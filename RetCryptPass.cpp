#include "RetCryptPass.h"

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Analysis/DomTreeUpdater.h"
#include "llvm/IR/Attributes.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Operator.h"
#include "llvm/IR/User.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/ValueMapper.h"

#include <cstdint>
#include <cstring>
#include <utility>

using namespace llvm;

llvm::cl::opt<bool> RetCryptEnable("obfretcrypt", llvm::cl::init(true), llvm::cl::desc("Master Toggle"));

static constexpr unsigned CloneXrefCap = 10;
static constexpr unsigned CloneSizeBudget = 4096;
static constexpr bool EnableCloneTier = true;
static constexpr bool EnableGarbleTier = true;
static constexpr bool EncConsts = true;
static constexpr bool EncStrings = true;
static constexpr bool EncGVPtrs = true;
static constexpr bool IndirectCallsEnabled = true;
static constexpr bool IndirectBranchesEnabled = true;
static constexpr uint64_t RATolerance = 64;
static constexpr uint64_t GarblePoison = 0x100000;

static constexpr uint64_t FNV1a64(const char* s)
{
    uint64_t h = 0xcbf29ce484222325ULL;
    while (*s)
    {
        h ^= (uint8_t)(*s);
        h *= 0x100000001b3ULL;
        ++s;
    }
    return h;
}

static uint64_t FNV1a64Range(StringRef s)
{
    uint64_t h = 0xcbf29ce484222325ULL;
    for (char c : s)
    {
        h ^= (uint8_t)c;
        h *= 0x100000001b3ULL;
    }
    return h;
}

static bool IsCRTSpecial(StringRef n)
{
    if (n.starts_with("_tls_callback")) return true;
    switch (FNV1a64Range(n))
    {
        case FNV1a64("DllMain"):
        case FNV1a64("_DllMainCRTStartup"):
        case FNV1a64("DllMainCRTStartup"):
        case FNV1a64("mainCRTStartup"):
        case FNV1a64("wmainCRTStartup"):
        case FNV1a64("WinMainCRTStartup"):
        case FNV1a64("wWinMainCRTStartup"):
        case FNV1a64("_CRT_INIT"):
        case FNV1a64("__scrt_common_main"):
        case FNV1a64("__scrt_common_main_seh"):
        case FNV1a64("__scrt_dllmain_before_initialize_c"):
        case FNV1a64("__scrt_dllmain_after_initialize_c"):
            return true;
    }
    return false;
}

static bool IsMSVCHelperCallee(StringRef n)
{
    if (n.starts_with("__imp_")) return true;
    if (n.starts_with("__delayLoadHelper")) return true;
    switch (FNV1a64Range(n))
    {
        case FNV1a64("__chkstk"):
        case FNV1a64("_alloca_probe"):
        case FNV1a64("__security_check_cookie"):
        case FNV1a64("__security_init_cookie"):
        case FNV1a64("__GSHandlerCheck"):
        case FNV1a64("__GSHandlerCheck_SEH"):
        case FNV1a64("__GSHandlerCheck_EH"):
        case FNV1a64("__CxxFrameHandler3"):
        case FNV1a64("__CxxFrameHandler4"):
        case FNV1a64("__C_specific_handler"):
        case FNV1a64("_setjmp"):
        case FNV1a64("_setjmp3"):
        case FNV1a64("longjmp"):
            return true;
    }
    return false;
}

static bool IsVTableGV(StringRef n)
{
    if (n.starts_with("??_7")) return true;
    if (n.starts_with("??_R4")) return true;
    if (n.starts_with("_ZTV")) return true;
    if (n.starts_with("_ZTC")) return true;
    if (n.starts_with("_ZTT")) return true;
    return false;
}

static void CollectGlobalCtorDtorFuncs(Module& m, DenseSet<Function*>& out)
{
    const StringRef tables[] = {"llvm.global_ctors", "llvm.global_dtors"};
    for (StringRef tn : tables)
    {
        GlobalVariable* gv = m.getNamedGlobal(tn);
        if (!gv || !gv->hasInitializer()) continue;
        auto* ca = dyn_cast<ConstantArray>(gv->getInitializer());
        if (!ca) continue;
        for (unsigned i = 0; i < ca->getNumOperands(); ++i)
        {
            auto* cs = dyn_cast<ConstantStruct>(ca->getOperand(i));
            if (!cs || cs->getNumOperands() < 2) continue;
            Value* v = cs->getOperand(1)->stripPointerCasts();
            if (auto* f = dyn_cast<Function>(v)) out.insert(f);
        }
    }
}

static void CollectFunctionsFromConstant(Constant* c, DenseSet<Function*>& out, DenseSet<Constant*>& visited)
{
    if (!c) return;
    if (!visited.insert(c).second) return;
    if (auto* f = dyn_cast<Function>(c)) { out.insert(f); return; }
    for (unsigned i = 0, n = c->getNumOperands(); i < n; ++i)
        if (auto* sub = dyn_cast<Constant>(c->getOperand(i)))
            CollectFunctionsFromConstant(sub, out, visited);
}

static void CollectVTableFuncs(Module& m, DenseSet<Function*>& out)
{
    DenseSet<Constant*> visited;
    for (GlobalVariable& gv : m.globals())
    {
        if (!gv.hasInitializer()) continue;
        if (!IsVTableGV(gv.getName())) continue;
        CollectFunctionsFromConstant(gv.getInitializer(), out, visited);
    }
}

static bool UserLeadsOnlyToMetadataGlobals(User* u, DenseSet<User*>& visited)
{
    if (!visited.insert(u).second) return true;
    if (auto* gv = dyn_cast<GlobalVariable>(u))
    {
        StringRef n = gv->getName();
        switch (FNV1a64Range(n))
        {
            case FNV1a64("llvm.global.annotations"):
            case FNV1a64("llvm.used"):
            case FNV1a64("llvm.compiler.used"):
            case FNV1a64("llvm.metadata"):
                return true;
        }
        return false;
    }
    if (isa<Instruction>(u)) return false;
    if (u->user_empty()) return false;
    for (User* uu : u->users())
        if (!UserLeadsOnlyToMetadataGlobals(uu, visited))
            return false;
    return true;
}

static bool DetectAddressTaken(Function& f)
{
    for (User* u : f.users())
    {
        if (auto* cb = dyn_cast<CallBase>(u))
        {
            if (cb->getCalledOperand() != &f) return true;
            continue;
        }
        DenseSet<User*> visited;
        if (!UserLeadsOnlyToMetadataGlobals(u, visited)) return true;
    }
    return false;
}

static bool DetectMustTailReceiver(Function& f)
{
    for (User* u : f.users())
    {
        if (auto* cb = dyn_cast<CallBase>(u))
        {
            if (cb->getCalledOperand() != &f) continue;
            if (auto* ci = dyn_cast<CallInst>(cb))
                if (ci->isMustTailCall()) return true;
        }
    }
    return false;
}

static bool HasFuncletOrEH(Function& f)
{
    for (BasicBlock& bb : f)
    {
        for (Instruction& i : bb)
        {
            if (isa<FuncletPadInst>(&i)) return true;
            if (isa<CatchReturnInst>(&i)) return true;
            if (isa<CleanupReturnInst>(&i)) return true;
        }
    }
    return false;
}

static bool HasAnnotationTag(Function& f, const char* tag)
{
    Module* m = f.getParent();
    GlobalVariable* ga = m->getGlobalVariable("llvm.global.annotations");
    if (!ga || !ga->hasInitializer()) return false;
    auto* ca = dyn_cast<ConstantArray>(ga->getOperand(0));
    if (!ca) return false;
    for (unsigned i = 0; i < ca->getNumOperands(); ++i)
    {
        auto* cs = dyn_cast<ConstantStruct>(ca->getOperand(i));
        if (!cs || cs->getNumOperands() < 2) continue;
        if (cs->getOperand(0)->stripPointerCasts() != &f) continue;
        auto* annogv = dyn_cast<GlobalVariable>(cs->getOperand(1)->stripPointerCasts());
        if (!annogv || !annogv->hasInitializer()) continue;
        auto* cds = dyn_cast<ConstantDataSequential>(annogv->getInitializer());
        if (!cds || !cds->isString()) continue;
        StringRef s = cds->getAsString();
        if (s.starts_with(tag) && s.size() == strlen(tag) + 1) return true;
    }
    return false;
}

static bool HasRetCryptAnnotation(Function& f)
{
    if (f.hasFnAttribute("retcrypt")) return true;
    return HasAnnotationTag(f, "retcrypt");
}

static bool HasNoRetCryptAnnotation(Function& f)
{
    return HasAnnotationTag(f, "noretcrypt");
}

struct ClassifyResult
{
    enum Tier { Skip, Clone, Garble } tier = Skip;
    unsigned directxrefs = 0;
    unsigned sizeinstrs = 0;
    bool addresstaken = false;
    bool recursive = false;
    bool toomanyxrefs = false;
    bool oversizebudget = false;
};

static ClassifyResult ClassifyFunction(Function& f, const DenseSet<Function*>& ctordtorset, const DenseSet<Function*>& vtableset)
{
    ClassifyResult r;
    if (f.isDeclaration()) return r;
    if (f.getName().starts_with("__retcrypt_")) return r;
    if (HasNoRetCryptAnnotation(f)) return r;
    if (f.hasFnAttribute(Attribute::Naked)) return r;
    if (HasFuncletOrEH(f)) return r;
    if (f.hasDLLExportStorageClass()) return r;
    if (IsCRTSpecial(f.getName())) return r;
    if (ctordtorset.contains(&f)) return r;
    if (vtableset.contains(&f)) return r;
    if (DetectMustTailReceiver(f)) return r;
    for (User* u : f.users())
    {
        auto* cb = dyn_cast<CallBase>(u);
        if (!cb || cb->getCalledOperand() != &f) continue;
        if (auto* ci = dyn_cast<CallInst>(cb))
            if (ci->isMustTailCall()) continue;
        Function* caller = cb->getFunction();
        if (!caller || caller->isDeclaration()) continue;
        if (caller == &f) r.recursive = true;
        ++r.directxrefs;
    }
    if (r.directxrefs == 0) return r;
    r.addresstaken = DetectAddressTaken(f);
    for (Instruction& i : instructions(f))
    {
        (void)i;
        ++r.sizeinstrs;
    }
    r.toomanyxrefs = (r.directxrefs > CloneXrefCap);
    r.oversizebudget = (r.sizeinstrs > CloneSizeBudget);
    bool cloneok = !r.toomanyxrefs && !r.oversizebudget && !r.addresstaken && !r.recursive;
    r.tier = cloneok ? ClassifyResult::Clone : ClassifyResult::Garble;
    return r;
}

static uint64_t NextMask()
{
    static uint64_t state = 0xA5A5A5A5DEADBEEFULL;
    state += 0x9E3779B97F4A7C15ULL;
    uint64_t x = state;
    x ^= x >> 30; x *= 0xBF58476D1CE4E5B9ULL;
    x ^= x >> 27; x *= 0x94D049BB133111EBULL;
    x ^= x >> 31;
    return x | 1;
}

static uint64_t NextGarbleKey()
{
    static uint64_t state = 0xCBF29CE484222325ULL;
    state += 0x9E3779B97F4A7C15ULL;
    uint64_t x = state;
    x ^= x >> 33; x *= 0xFF51AFD7ED558CCDULL;
    x ^= x >> 33; x *= 0xC4CEB9FE1A85EC53ULL;
    x ^= x >> 33;
    return x | 1;
}

struct EncryptContext
{
    Value* ra64 = nullptr;
    Value* ra32 = nullptr;
    Value* ra16 = nullptr;
    Value* ra8 = nullptr;
    Constant* ba64 = nullptr;
    Constant* ba32 = nullptr;
    Constant* ba16 = nullptr;
    Constant* ba8 = nullptr;
    Value* keydiff = nullptr;
    DenseSet<Instruction*> own;
};

static Value* RAForWidth(const EncryptContext& c, unsigned w)
{
    switch (w)
    {
        case 8: return c.ra8;
        case 16: return c.ra16;
        case 32: return c.ra32;
        case 64: return c.ra64;
    }
    return nullptr;
}

static Constant* BAForWidth(const EncryptContext& c, unsigned w)
{
    switch (w)
    {
        case 8: return c.ba8;
        case 16: return c.ba16;
        case 32: return c.ba32;
        case 64: return c.ba64;
    }
    return nullptr;
}

static bool OperandSlotAcceptsNonConstant(Instruction* i, unsigned idx)
{
    if (isa<SwitchInst>(i)) return idx == 0;
    if (isa<GetElementPtrInst>(i)) return false;
    if (isa<AllocaInst>(i)) return idx == 0;
    if (isa<AtomicRMWInst>(i)) return false;
    if (isa<AtomicCmpXchgInst>(i)) return false;
    if (isa<FenceInst>(i)) return false;
    if (isa<CallBrInst>(i)) return false;
    if (isa<InvokeInst>(i)) return false;
    if (isa<PHINode>(i)) return false;
    if (isa<IntrinsicInst>(i)) return false;
    if (auto* cb = dyn_cast<CallBase>(i))
        if (idx == cb->getCalledOperandUse().getOperandNo()) return false;
    return true;
}

static void EmitCloneEncryptContext(Function& f, Constant* ba, EncryptContext& ctx)
{
    LLVMContext& c = f.getContext();
    Module* m = f.getParent();
    Type* i64 = Type::getInt64Ty(c);
    Type* i32 = Type::getInt32Ty(c);
    Type* i16 = Type::getInt16Ty(c);
    Type* i8 = Type::getInt8Ty(c);
    BasicBlock& entry = f.getEntryBlock();
    IRBuilder<> b(&entry, entry.getFirstInsertionPt());
    Function* rafn = Intrinsic::getDeclaration(m, Intrinsic::returnaddress);
    Value* ra = b.CreateCall(rafn, {b.getInt32(0)}, "RA");
    ctx.ra64 = b.CreatePtrToInt(ra, i64, "RA64");
    ctx.ra32 = b.CreateTrunc(ctx.ra64, i32, "RA32");
    ctx.ra16 = b.CreateTrunc(ctx.ra64, i16, "RA16");
    ctx.ra8 = b.CreateTrunc(ctx.ra64, i8, "RA8");
    ctx.ba64 = ConstantExpr::getPtrToInt(ba, i64);
    ctx.ba32 = ConstantExpr::getTrunc(ctx.ba64, i32);
    ctx.ba16 = ConstantExpr::getTrunc(ctx.ba64, i16);
    ctx.ba8 = ConstantExpr::getTrunc(ctx.ba64, i8);
    // codegen inserts return value spills and other setup between the CALL and the labelled block, shifting real retaddr a few bytes off; absorb that with a +/-TOLERANCE unsigned compare window, branchless, so legit callers decrypt and hostile ones (off by megabytes) still fail
    Value* ba64rt = b.CreatePtrToInt(ba, i64, "BA64RT");
    Value* rawdiff = b.CreateSub(ctx.ra64, ba64rt, "RawDiff");
    Value* biased = b.CreateAdd(rawdiff, ConstantInt::get(i64, RATolerance), "DiffBias");
    Value* issmall = b.CreateICmpULT(biased, ConstantInt::get(i64, 2 * RATolerance), "DiffSmall");
    ctx.keydiff = b.CreateSelect(issmall, ConstantInt::get(i64, 0), rawdiff, "KeyDiff");
    if (auto* i = dyn_cast<Instruction>(ra)) ctx.own.insert(i);
    if (auto* i = dyn_cast<Instruction>(ctx.ra64)) ctx.own.insert(i);
    if (auto* i = dyn_cast<Instruction>(ctx.ra32)) ctx.own.insert(i);
    if (auto* i = dyn_cast<Instruction>(ctx.ra16)) ctx.own.insert(i);
    if (auto* i = dyn_cast<Instruction>(ctx.ra8)) ctx.own.insert(i);
    if (auto* i = dyn_cast<Instruction>(ba64rt)) ctx.own.insert(i);
    if (auto* i = dyn_cast<Instruction>(rawdiff)) ctx.own.insert(i);
    if (auto* i = dyn_cast<Instruction>(biased)) ctx.own.insert(i);
    if (auto* i = dyn_cast<Instruction>(issmall)) ctx.own.insert(i);
    if (auto* i = dyn_cast<Instruction>(ctx.keydiff)) ctx.own.insert(i);
}

static void EmitGarbleEncryptContext(Function& f, GlobalVariable* batable, unsigned n, uint64_t fkey, EncryptContext& ctx)
{
    LLVMContext& c = f.getContext();
    Module* m = f.getParent();
    Type* i64 = Type::getInt64Ty(c);
    Type* i32 = Type::getInt32Ty(c);
    Type* i16 = Type::getInt16Ty(c);
    Type* i8 = Type::getInt8Ty(c);
    BasicBlock& entry = f.getEntryBlock();
    IRBuilder<> b(&entry, entry.getFirstInsertionPt());
    Function* rafn = Intrinsic::getDeclaration(m, Intrinsic::returnaddress);
    Value* ra = b.CreateCall(rafn, {b.getInt32(0)}, "GRA");
    Value* raint = b.CreatePtrToInt(ra, i64, "GRA64RT");
    ArrayType* at = ArrayType::get(i64, n);
    Constant* zero32 = ConstantInt::get(i32, 0);
    Constant* tol = ConstantInt::get(i64, RATolerance);
    Constant* tol2 = ConstantInt::get(i64, 2 * RATolerance);
    Constant* neg1 = ConstantInt::get(i64, (uint64_t)-1);
    Constant* zero64 = ConstantInt::get(i64, 0);
    // linear scan all entries branchless; a conditional per entry would create misprediction penalties on big tables and leak timing info about which entry matched
    Value* matched = zero64;
    for (unsigned i = 0; i < n; ++i)
    {
        Constant* idx = ConstantInt::get(i32, i);
        Value* gep = b.CreateGEP(at, batable, {zero32, idx}, "GGep");
        Value* bart = b.CreateLoad(i64, gep, "GBAEntry");
        Value* diff = b.CreateSub(raint, bart, "GEntryDiff");
        Value* biased = b.CreateAdd(diff, tol, "GEntryBias");
        Value* within = b.CreateICmpULT(biased, tol2, "GWithin");
        Value* signmask = b.CreateSelect(within, neg1, zero64, "GSignMask");
        matched = b.CreateOr(matched, signmask, "GMatched");
        if (auto* ii = dyn_cast<Instruction>(gep)) ctx.own.insert(ii);
        if (auto* ii = dyn_cast<Instruction>(bart)) ctx.own.insert(ii);
        if (auto* ii = dyn_cast<Instruction>(diff)) ctx.own.insert(ii);
        if (auto* ii = dyn_cast<Instruction>(biased)) ctx.own.insert(ii);
        if (auto* ii = dyn_cast<Instruction>(within)) ctx.own.insert(ii);
        if (auto* ii = dyn_cast<Instruction>(signmask)) ctx.own.insert(ii);
        if (auto* ii = dyn_cast<Instruction>(matched)) ctx.own.insert(ii);
    }
    Constant* fkeyc = ConstantInt::get(i64, fkey);
    ctx.ba64 = fkeyc;
    ctx.ba32 = ConstantExpr::getTrunc(ctx.ba64, i32);
    ctx.ba16 = ConstantExpr::getTrunc(ctx.ba64, i16);
    ctx.ba8 = ConstantExpr::getTrunc(ctx.ba64, i8);
    ctx.ra64 = b.CreateAnd(fkeyc, matched, "GRTRA64");
    ctx.ra32 = b.CreateTrunc(ctx.ra64, i32, "GRTRA32");
    ctx.ra16 = b.CreateTrunc(ctx.ra64, i16, "GRTRA16");
    ctx.ra8 = b.CreateTrunc(ctx.ra64, i8, "GRTRA8");
    Constant* poison = ConstantInt::get(i64, GarblePoison);
    Value* notmatched = b.CreateXor(matched, neg1, "GNotMatched");
    ctx.keydiff = b.CreateAnd(notmatched, poison, "GKeyDiff");
    if (auto* i = dyn_cast<Instruction>(ra)) ctx.own.insert(i);
    if (auto* i = dyn_cast<Instruction>(raint)) ctx.own.insert(i);
    if (auto* i = dyn_cast<Instruction>(ctx.ra64)) ctx.own.insert(i);
    if (auto* i = dyn_cast<Instruction>(ctx.ra32)) ctx.own.insert(i);
    if (auto* i = dyn_cast<Instruction>(ctx.ra16)) ctx.own.insert(i);
    if (auto* i = dyn_cast<Instruction>(ctx.ra8)) ctx.own.insert(i);
    if (auto* i = dyn_cast<Instruction>(notmatched)) ctx.own.insert(i);
    if (auto* i = dyn_cast<Instruction>(ctx.keydiff)) ctx.own.insert(i);
}

static void EncryptConstants(Function& f, EncryptContext& ctx)
{
    struct Repl { Instruction* ins; unsigned idx; ConstantInt* cop; };
    SmallVector<Repl, 64> work;
    for (BasicBlock& bb : f)
    {
        for (Instruction& i : bb)
        {
            if (ctx.own.contains(&i)) continue;
            for (unsigned oi = 0, n = i.getNumOperands(); oi < n; ++oi)
            {
                auto* cop = dyn_cast<ConstantInt>(i.getOperand(oi));
                if (!cop) continue;
                unsigned w = cop->getBitWidth();
                if (w != 8 && w != 16 && w != 32 && w != 64) continue;
                if (!OperandSlotAcceptsNonConstant(&i, oi)) continue;
                work.push_back({&i, oi, cop});
            }
        }
    }
    for (const Repl& r : work)
    {
        unsigned w = r.cop->getBitWidth();
        Constant* ct = ConstantExpr::getXor(r.cop, BAForWidth(ctx, w));
        IRBuilder<> b(r.ins);
        Value* dec = b.CreateXor(ct, RAForWidth(ctx, w), "Dec");
        if (auto* di = dyn_cast<Instruction>(dec)) ctx.own.insert(di);
        r.ins->setOperand(r.idx, dec);
    }
}

static void EncryptStrings(Function& f, EncryptContext& ctx)
{
    DenseSet<GlobalVariable*> seen;
    SmallVector<GlobalVariable*, 16> entries;
    for (BasicBlock& bb : f)
    {
        for (Instruction& i : bb)
        {
            if (ctx.own.contains(&i)) continue;
            for (unsigned oi = 0, oe = i.getNumOperands(); oi < oe; ++oi)
            {
                Value* op = i.getOperand(oi);
                Value* stripped = op;
                while (auto* gep = dyn_cast<GEPOperator>(stripped))
                    stripped = gep->getPointerOperand();
                auto* gv = dyn_cast<GlobalVariable>(stripped);
                if (!gv || !gv->isConstant() || !gv->hasInitializer()) continue;
                auto* arrt = dyn_cast<ArrayType>(gv->getValueType());
                if (!arrt) continue;
                Type* elemt = arrt->getElementType();
                if (!elemt->isIntegerTy(8) && !elemt->isIntegerTy(16)) continue;
                auto* init = dyn_cast<ConstantDataSequential>(gv->getInitializer());
                if (!init) continue;
                if (!seen.insert(gv).second) continue;
                entries.push_back(gv);
            }
        }
    }
    if (entries.empty()) return;
    LLVMContext& c = f.getContext();
    Type* i64 = Type::getInt64Ty(c);
    for (GlobalVariable* gv : entries)
    {
        auto* init = cast<ConstantDataSequential>(gv->getInitializer());
        auto* arrt = cast<ArrayType>(gv->getValueType());
        unsigned ebits = arrt->getElementType()->getIntegerBitWidth();
        unsigned esize = ebits / 8;
        unsigned nelems = init->getNumElements();
        unsigned total = nelems * esize;
        unsigned padded = ((total + 7) / 8) * 8;
        unsigned nchunks = padded / 8;
        unsigned elemsperchunk = 8 / esize;
        IRBuilder<> be(&f.getEntryBlock(), f.getEntryBlock().begin());
        AllocaInst* slot = be.CreateAlloca(i64, ConstantInt::get(i64, nchunks), "StrBuf");
        ctx.own.insert(slot);
        Instruction* insertafter = cast<Instruction>(ctx.keydiff);
        IRBuilder<> bd(insertafter->getParent(), std::next(insertafter->getIterator()));
        for (unsigned chunkidx = 0; chunkidx < nchunks; ++chunkidx)
        {
            uint64_t plain = 0;
            for (unsigned k = 0; k < elemsperchunk; ++k)
            {
                unsigned elemidx = chunkidx * elemsperchunk + k;
                if (elemidx >= nelems) break;
                uint64_t v = init->getElementAsInteger(elemidx);
                plain |= v << (k * ebits);
            }
            // cipher must be a plain integer not a reloc XOR, since PE has no XOR relocation and LLVM would materialize the plaintext as a visible immediate at codegen; ADD with an integer per chunk mask is PE-safe
            uint64_t mask = NextMask();
            uint64_t cipherct = plain + mask;
            Constant* cipherc = ConstantInt::get(i64, cipherct);
            Constant* maskc = ConstantInt::get(i64, mask);
            Value* effmask = bd.CreateAdd(maskc, ctx.keydiff, "StrEMask");
            Value* dec = bd.CreateSub(cipherc, effmask, "StrDec");
            Value* dst = bd.CreateGEP(i64, slot, ConstantInt::get(i64, chunkidx), "StrDst");
            Value* st = bd.CreateStore(dec, dst);
            if (auto* di = dyn_cast<Instruction>(effmask)) ctx.own.insert(di);
            if (auto* di = dyn_cast<Instruction>(dec)) ctx.own.insert(di);
            if (auto* di = dyn_cast<Instruction>(dst)) ctx.own.insert(di);
            if (auto* di = dyn_cast<Instruction>(st)) ctx.own.insert(di);
        }
        SmallVector<Use*, 8> toreplace;
        for (Use& u : gv->uses())
        {
            auto* useri = dyn_cast<Instruction>(u.getUser());
            if (!useri) continue;
            if (useri->getFunction() != &f) continue;
            if (ctx.own.contains(useri)) continue;
            toreplace.push_back(&u);
        }
        for (Use* u : toreplace) u->set(slot);
    }
}

static bool ShouldEncryptGVOperand(GlobalVariable* gv)
{
    if (!gv) return false;
    if (gv->getName().starts_with("llvm.")) return false;
    if (gv->getName().starts_with("__retcrypt_")) return false;
    if (gv->isThreadLocal()) return false;
    if (gv->isConstant() && gv->hasInitializer())
    {
        if (auto* arrt = dyn_cast<ArrayType>(gv->getValueType()))
        {
            Type* elemt = arrt->getElementType();
            if ((elemt->isIntegerTy(8) || elemt->isIntegerTy(16)) && isa<ConstantDataSequential>(gv->getInitializer()))
                return false;
        }
    }
    return true;
}

static void EncryptGVPtrs(Function& f, EncryptContext& ctx)
{
    LLVMContext& c = f.getContext();
    Module* m = f.getParent();
    Type* i64 = Type::getInt64Ty(c);
    PointerType* ptrty = PointerType::getUnqual(c);
    DenseSet<GlobalVariable*> seen;
    SmallVector<GlobalVariable*, 16> gvs;
    for (BasicBlock& bb : f)
    {
        for (Instruction& i : bb)
        {
            if (ctx.own.contains(&i)) continue;
            for (unsigned oi = 0, oe = i.getNumOperands(); oi < oe; ++oi)
            {
                auto* gv = dyn_cast<GlobalVariable>(i.getOperand(oi));
                if (!ShouldEncryptGVOperand(gv)) continue;
                if (!seen.insert(gv).second) continue;
                gvs.push_back(gv);
            }
        }
    }
    if (gvs.empty()) return;
    Instruction* insertafter = cast<Instruction>(ctx.keydiff);
    for (GlobalVariable* gv : gvs)
    {
        uint64_t mask = NextMask();
        Constant* addr = ConstantExpr::getPtrToInt(gv, i64);
        Constant* maskc = ConstantInt::get(i64, mask);
        Constant* enc = ConstantExpr::getAdd(addr, maskc);
        auto* holder = new GlobalVariable(*m, i64, false, GlobalValue::PrivateLinkage, enc, "__retcrypt_gv_ref");
        holder->setUnnamedAddr(GlobalValue::UnnamedAddr::Global);
        IRBuilder<> b(insertafter->getParent(), std::next(insertafter->getIterator()));
        Value* loaded = b.CreateLoad(i64, holder, "GVLoad");
        Value* effmask = b.CreateAdd(maskc, ctx.keydiff, "GVEMask");
        Value* dec = b.CreateSub(loaded, effmask, "GVDec");
        Value* ptr = b.CreateIntToPtr(dec, ptrty, "GVP");
        if (auto* di = dyn_cast<Instruction>(loaded)) ctx.own.insert(di);
        if (auto* di = dyn_cast<Instruction>(effmask)) ctx.own.insert(di);
        if (auto* di = dyn_cast<Instruction>(dec)) ctx.own.insert(di);
        if (auto* di = dyn_cast<Instruction>(ptr)) ctx.own.insert(di);
        SmallVector<Use*, 8> toreplace;
        for (Use& u : gv->uses())
        {
            auto* useri = dyn_cast<Instruction>(u.getUser());
            if (!useri) continue;
            if (useri->getFunction() != &f) continue;
            if (ctx.own.contains(useri)) continue;
            toreplace.push_back(&u);
        }
        for (Use* u : toreplace) u->set(ptr);
        insertafter = cast<Instruction>(ptr);
    }
}

static void IndirectCalls(Function& f, EncryptContext& ctx)
{
    LLVMContext& c = f.getContext();
    Module* m = f.getParent();
    Type* i64 = Type::getInt64Ty(c);
    PointerType* ptrty = PointerType::getUnqual(c);
    SmallVector<CallBase*, 32> toindirect;
    for (BasicBlock& bb : f)
    {
        for (Instruction& i : bb)
        {
            if (ctx.own.contains(&i)) continue;
            auto* call = dyn_cast<CallBase>(&i);
            if (!call) continue;
            if (isa<CallBrInst>(call)) continue;
            if (call->isInlineAsm()) continue;
            if (auto* ci = dyn_cast<CallInst>(call))
                if (ci->isMustTailCall()) continue;
            Function* callee = call->getCalledFunction();
            if (!callee) continue;
            if (callee->isIntrinsic()) continue;
            if (callee->isVarArg()) continue;
            if (callee->getName().starts_with("__retcrypt_")) continue;
            if (IsMSVCHelperCallee(callee->getName())) continue;
            toindirect.push_back(call);
        }
    }
    for (CallBase* call : toindirect)
    {
        Function* callee = call->getCalledFunction();
        uint64_t mask = NextMask();
        Constant* addr = ConstantExpr::getPtrToInt(callee, i64);
        Constant* maskc = ConstantInt::get(i64, mask);
        Constant* enc = ConstantExpr::getAdd(addr, maskc);
        // holder GV MUST be mutable (isConstant=false) even though nothing writes it; constant propagation on a constant GV would fold a load back through the initializer and collapse the whole thing to a LEA at the call site
        auto* gv = new GlobalVariable(*m, i64, false, GlobalValue::PrivateLinkage, enc, "__retcrypt_ind_call");
        gv->setUnnamedAddr(GlobalValue::UnnamedAddr::Global);
        IRBuilder<> b(call);
        Value* loaded = b.CreateLoad(i64, gv, "CeeLoad");
        Value* effmask = b.CreateAdd(maskc, ctx.keydiff, "CeeEMask");
        Value* dec = b.CreateSub(loaded, effmask, "CeeDec");
        Value* fn = b.CreateIntToPtr(dec, ptrty, "CeeP");
        if (auto* di = dyn_cast<Instruction>(loaded)) ctx.own.insert(di);
        if (auto* di = dyn_cast<Instruction>(effmask)) ctx.own.insert(di);
        if (auto* di = dyn_cast<Instruction>(dec)) ctx.own.insert(di);
        if (auto* di = dyn_cast<Instruction>(fn)) ctx.own.insert(di);
        call->setCalledOperand(fn);
    }
}

static void IndirectBranches(Function& f, EncryptContext& ctx)
{
    LLVMContext& c = f.getContext();
    Module* m = f.getParent();
    Type* i64 = Type::getInt64Ty(c);
    Type* i32 = Type::getInt32Ty(c);
    PointerType* ptrty = PointerType::getUnqual(c);
    SmallVector<BranchInst*, 32> toindirect;
    DenseMap<BasicBlock*, unsigned> tgtidx;
    SmallVector<BasicBlock*, 32> tgtordered;
    for (BasicBlock& bb : f)
    {
        auto* br = dyn_cast<BranchInst>(bb.getTerminator());
        if (!br) continue;
        if (ctx.own.contains(br)) continue;
        bool hasehsucc = false;
        for (BasicBlock* succ : br->successors())
            if (succ && succ->isEHPad()) { hasehsucc = true; break; }
        if (hasehsucc) continue;
        toindirect.push_back(br);
        for (BasicBlock* succ : br->successors())
            if (tgtidx.insert({succ, (unsigned)tgtordered.size()}).second)
                tgtordered.push_back(succ);
    }
    if (toindirect.empty()) return;
    unsigned n = tgtordered.size();
    ArrayType* at = ArrayType::get(i64, n);
    SmallVector<Constant*, 32> addrentries(n);
    SmallVector<Constant*, 32> maskentries(n);
    for (unsigned i = 0; i < n; ++i)
    {
        uint64_t mask = NextMask();
        Constant* ba = BlockAddress::get(&f, tgtordered[i]);
        Constant* baint = ConstantExpr::getPtrToInt(ba, i64);
        Constant* maskc = ConstantInt::get(i64, mask);
        addrentries[i] = ConstantExpr::getAdd(baint, maskc);
        maskentries[i] = maskc;
    }
    auto* addrtable = new GlobalVariable(*m, at, false, GlobalValue::PrivateLinkage, ConstantArray::get(at, addrentries), "__retcrypt_ind_br_addrtbl");
    addrtable->setUnnamedAddr(GlobalValue::UnnamedAddr::Global);
    auto* masktable = new GlobalVariable(*m, at, false, GlobalValue::PrivateLinkage, ConstantArray::get(at, maskentries), "__retcrypt_ind_br_masktbl");
    masktable->setUnnamedAddr(GlobalValue::UnnamedAddr::Global);
    Constant* zero32 = ConstantInt::get(i32, 0);
    for (BranchInst* br : toindirect)
    {
        IRBuilder<> b(br);
        Value* idx;
        if (br->isConditional())
        {
            Constant* idxt = ConstantInt::get(i32, tgtidx[br->getSuccessor(0)]);
            Constant* idxf = ConstantInt::get(i32, tgtidx[br->getSuccessor(1)]);
            idx = b.CreateSelect(br->getCondition(), idxt, idxf, "BrIdx");
        }
        else
        {
            idx = ConstantInt::get(i32, tgtidx[br->getSuccessor(0)]);
        }
        Value* agep = b.CreateGEP(at, addrtable, {zero32, idx}, "BrAGep");
        Value* mgep = b.CreateGEP(at, masktable, {zero32, idx}, "BrMGep");
        Value* loaded = b.CreateLoad(i64, agep, "BrLoad");
        Value* mask = b.CreateLoad(i64, mgep, "BrMask");
        Value* effmask = b.CreateAdd(mask, ctx.keydiff, "BrEMask");
        Value* dec = b.CreateSub(loaded, effmask, "BrDec");
        Value* tgt = b.CreateIntToPtr(dec, ptrty, "BrP");
        if (auto* di = dyn_cast<Instruction>(idx)) ctx.own.insert(di);
        if (auto* di = dyn_cast<Instruction>(agep)) ctx.own.insert(di);
        if (auto* di = dyn_cast<Instruction>(mgep)) ctx.own.insert(di);
        if (auto* di = dyn_cast<Instruction>(loaded)) ctx.own.insert(di);
        if (auto* di = dyn_cast<Instruction>(mask)) ctx.own.insert(di);
        if (auto* di = dyn_cast<Instruction>(effmask)) ctx.own.insert(di);
        if (auto* di = dyn_cast<Instruction>(dec)) ctx.own.insert(di);
        if (auto* di = dyn_cast<Instruction>(tgt)) ctx.own.insert(di);
        SmallVector<BasicBlock*, 2> succs;
        for (BasicBlock* sc : br->successors()) succs.push_back(sc);
        auto* ibr = IndirectBrInst::Create(tgt, succs.size(), br);
        for (BasicBlock* sc : succs) ibr->addDestination(sc);
        ibr->copyMetadata(*br);
        ctx.own.insert(ibr);
        br->eraseFromParent();
    }
}

static void ApplyRetaddrPreservingAttrs(Function& f)
{
    f.removeFnAttr(Attribute::AlwaysInline);
    f.removeFnAttr(Attribute::InlineHint);
    f.addFnAttr(Attribute::NoInline);
    f.addFnAttr(Attribute::NoMerge);
    f.addFnAttr("disable-tail-calls", "true");
}

static Constant* SplitCallsiteAndGetBA(CallBase* cb)
{
    Function* caller = cb->getFunction();
    BasicBlock* rcafter = nullptr;
    if (auto* ci = dyn_cast<CallInst>(cb))
    {
        BasicBlock* callerbb = ci->getParent();
        Instruction* splitat = ci->getNextNode();
        rcafter = SplitBlock(callerbb, splitat, (DomTreeUpdater*)nullptr, nullptr, nullptr, "RCAfter");
        ci->setTailCallKind(CallInst::TCK_NoTail);
    }
    else if (auto* ii = dyn_cast<InvokeInst>(cb))
    {
        rcafter = SplitEdge(ii->getParent(), ii->getNormalDest(), nullptr, nullptr, nullptr);
        rcafter->setName("RCAfter");
    }
    return BlockAddress::get(caller, rcafter);
}

static void EncryptFunctionWithBA(Function& f, Constant* ba)
{
    EncryptContext ctx;
    EmitCloneEncryptContext(f, ba, ctx);
    if (EncConsts) EncryptConstants(f, ctx);
    if (EncStrings) EncryptStrings(f, ctx);
    if (EncGVPtrs) EncryptGVPtrs(f, ctx);
    if (IndirectCallsEnabled) IndirectCalls(f, ctx);
    if (IndirectBranchesEnabled) IndirectBranches(f, ctx);
}

static void EncryptFunctionAsGarble(Function& f, GlobalVariable* batable, unsigned n, uint64_t fkey)
{
    EncryptContext ctx;
    EmitGarbleEncryptContext(f, batable, n, fkey, ctx);
    if (EncConsts) EncryptConstants(f, ctx);
    if (EncStrings) EncryptStrings(f, ctx);
    if (EncGVPtrs) EncryptGVPtrs(f, ctx);
    if (IndirectCallsEnabled) IndirectCalls(f, ctx);
    if (IndirectBranchesEnabled) IndirectBranches(f, ctx);
}

static void EncryptSingleCaller(Function& f, CallBase* ci)
{
    Constant* ba = SplitCallsiteAndGetBA(ci);
    ApplyRetaddrPreservingAttrs(f);
    EncryptFunctionWithBA(f, ba);
}

static void EncryptMultiCallerViaCloning(Function& f, ArrayRef<CallBase*> callsites)
{
    unsigned idx = 0;
    for (CallBase* ci : callsites)
    {
        // clone from F's original body BEFORE encrypting F or any earlier clone, otherwise later clones inherit the earlier encryption chain
        ValueToValueMapTy vmap;
        Function* fclone = CloneFunction(&f, vmap);
        fclone->setName(f.getName() + ".rc" + Twine(idx++));
        fclone->setLinkage(GlobalValue::PrivateLinkage);
        fclone->setDLLStorageClass(GlobalValue::DefaultStorageClass);
        fclone->setVisibility(GlobalValue::DefaultVisibility);
        ci->setCalledFunction(fclone);
        Constant* ba = SplitCallsiteAndGetBA(ci);
        ApplyRetaddrPreservingAttrs(*fclone);
        EncryptFunctionWithBA(*fclone, ba);
    }
}

static bool TransformCloneTier(Function& f)
{
    SmallVector<CallBase*, 8> callsites;
    for (User* u : f.users())
    {
        auto* cb = dyn_cast<CallBase>(u);
        if (!cb || cb->getCalledOperand() != &f) continue;
        if (isa<CallBrInst>(cb)) return false;
        if (auto* ci = dyn_cast<CallInst>(cb))
        {
            if (ci->isMustTailCall()) return false;
            if (!ci->getNextNode()) return false;
        }
        else if (auto* ii = dyn_cast<InvokeInst>(cb))
        {
            if (ii->getNormalDest()->isEHPad()) return false;
        }
        if (cb->getParent()->isEHPad()) return false;
        Function* caller = cb->getFunction();
        if (!caller || caller->isDeclaration()) continue;
        callsites.push_back(cb);
    }
    if (callsites.empty()) return false;
    if (callsites.size() == 1)
        EncryptSingleCaller(f, callsites[0]);
    else
        EncryptMultiCallerViaCloning(f, callsites);
    return true;
}

static bool TransformGarbleTier(Function& f)
{
    if (DetectAddressTaken(f)) return false;
    SmallVector<CallBase*, 32> callsites;
    for (User* u : f.users())
    {
        auto* cb = dyn_cast<CallBase>(u);
        if (!cb || cb->getCalledOperand() != &f) continue;
        if (isa<CallBrInst>(cb)) return false;
        if (auto* ci = dyn_cast<CallInst>(cb))
        {
            if (ci->isMustTailCall()) return false;
            if (!ci->getNextNode()) return false;
        }
        else if (auto* ii = dyn_cast<InvokeInst>(cb))
        {
            if (ii->getNormalDest()->isEHPad()) return false;
        }
        if (cb->getParent()->isEHPad()) return false;
        Function* caller = cb->getFunction();
        if (!caller || caller->isDeclaration()) continue;
        callsites.push_back(cb);
    }
    if (callsites.size() < 2) return false;
    SmallVector<Constant*, 32> bas;
    bas.reserve(callsites.size());
    for (CallBase* ci : callsites)
        bas.push_back(SplitCallsiteAndGetBA(ci));
    LLVMContext& c = f.getContext();
    Module* m = f.getParent();
    Type* i64 = Type::getInt64Ty(c);
    unsigned n = (unsigned)bas.size();
    ArrayType* at = ArrayType::get(i64, n);
    SmallVector<Constant*, 32> entries(n);
    for (unsigned i = 0; i < n; ++i)
        entries[i] = ConstantExpr::getPtrToInt(bas[i], i64);
    // table GV must be mutable (isConstant=false) for the same const prop reason as the single call holder. A load through a constant GV would fold back to the initializer and leak the plaintext retaddr set
    auto* batable = new GlobalVariable(*m, at, false, GlobalValue::PrivateLinkage, ConstantArray::get(at, entries), "__retcrypt_garble_batbl");
    batable->setUnnamedAddr(GlobalValue::UnnamedAddr::Global);
    uint64_t fkey = NextGarbleKey();
    ApplyRetaddrPreservingAttrs(f);
    EncryptFunctionAsGarble(f, batable, n, fkey);
    return true;
}

bool RunRetCrypt(Module& m)
{
    if (!RetCryptEnable) return false;
    DenseSet<Function*> ctordtorset;
    CollectGlobalCtorDtorFuncs(m, ctordtorset);
    DenseSet<Function*> vtableset;
    CollectVTableFuncs(m, vtableset);
    SmallVector<Function*, 32> clonecandidates;
    SmallVector<Function*, 32> garblecandidates;
    for (Function& f : m)
    {
        if (!HasRetCryptAnnotation(f)) continue;
        ClassifyResult r = ClassifyFunction(f, ctordtorset, vtableset);
        if (r.tier == ClassifyResult::Clone)
            clonecandidates.push_back(&f);
        else if (r.tier == ClassifyResult::Garble && r.toomanyxrefs && !r.addresstaken && !r.recursive && !r.oversizebudget)
            garblecandidates.push_back(&f);
    }
    bool mutated = false;
    if (EnableCloneTier)
    {
        for (Function* f : clonecandidates)
            if (TransformCloneTier(*f)) mutated = true;
    }
    if (EnableGarbleTier)
    {
        for (Function* f : garblecandidates)
            if (TransformGarbleTier(*f)) mutated = true;
    }
    return mutated;
}

PreservedAnalyses RetCryptPass::run(Module& m, ModuleAnalysisManager&)
{
    bool mutated = RunRetCrypt(m);
    return mutated ? PreservedAnalyses::none() : PreservedAnalyses::all();
}