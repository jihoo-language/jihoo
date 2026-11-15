import Jihoo.NativeLendGhostRule

/-! Loan-indexed extension of the same complete native typing rules. Saved
loan depths follow the actual native reader stack. Code borrowing requires an
active named owner; dependent readers enter its frame and continuations use the
outer stack again. Ghost specialization admits arbitrary owners, so later ghost
substitution need not preserve the source checker's conservative variable gate.
The default kernel/admission alias has not yet been switched to this judgment. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping

mutual
  /-- A domain must actually infer a sort; arbitrary annotations are not assumed
  to be types. This definition is independent of the executable checker. -/
  inductive Binder (env : Environment) : Loans.Stack → Context → Bool → Term → SortTag → Prop where
    | intro : HasType env loans ctx true A s.term → binderAllowed env e A s → Binder env loans ctx e A s

  inductive HasType (env : Environment) : Loans.Stack → Context → Bool → Term → Term → Prop where
    | var : lookup ctx x = some b → (ghost = true ∨ b.erased = false) →
        HasType env loans ctx ghost (.var x) b.ty
    | univ : n < 32 → HasType env loans ctx ghost (.univ n) (.univ (n + 1))
    | prop : HasType env loans ctx ghost .prop (.univ 0)
    | u64 : HasType env loans ctx ghost .u64 (.univ 0)
    | i64 : HasType env loans ctx ghost .i64 (.univ 0)
    | natural : n < 2^64 → HasType env loans ctx ghost (.natural n) .u64
    | integer : -(2^63 : Int) ≤ n → n < (2^63 : Int) → HasType env loans ctx ghost (.integer n) .i64
    | array : HasType env loans ctx true n .u64 → HasType env loans ctx ghost (.array n) (.univ 0)
    | lt : HasType env loans ctx true a .u64 → HasType env loans ctx true b .u64 → HasType env loans ctx ghost (.lt a b) .prop
    | eq : HasType env loans ctx true a .u64 → HasType env loans ctx true b .u64 → HasType env loans ctx ghost (.eq a b) .prop
    | pi : Binder env loans ctx e A s → HasType env loans (⟨A, e⟩ :: ctx) true B r.term →
        HasType env loans ctx ghost (.pi e A B) (s.pi r).term
    | lam : Binder env loans ctx e A s → HasType env loans (⟨A, e⟩ :: ctx) ghost b B →
        HasType env loans ctx ghost (.lam e A b) (.pi e A B)
    | app : HasType env loans ctx ghost f (.pi e A B) → HasType env loans ctx (ghost || e) a A →
        applicationAllowed env ghost A a →
        HasType env loans ctx ghost (.app f a) (B.subst (fun | 0 => a | n + 1 => .var n))
    | uadd : HasType env loans ctx ghost a .u64 → HasType env loans ctx ghost b .u64 →
        HasType env loans ctx ghost (.uadd a b) .u64
    | usub : HasType env loans ctx ghost a .u64 → HasType env loans ctx ghost b .u64 →
        HasType env loans ctx true p (.lt b (.uadd a (.natural 1))) → HasType env loans ctx ghost (.usub a b p) .u64
    | refl : HasType env loans ctx true a .u64 → HasType env loans ctx ghost (.refl a) (.eq a a)
    | zeroLe : HasType env loans ctx true a .u64 →
        HasType env loans ctx ghost (.zeroLe a) (.lt (.natural 0) (.uadd a (.natural 1)))
    | decide : a < 2^64 → b < 2^64 → a < b →
        HasType env loans ctx ghost (.decide (.natural a) (.natural b)) (.lt (.natural a) (.natural b))
    | decideConverted : HasType env loans ctx true a .u64 → HasType env loans ctx true b .u64 →
        Conversion.Conv env a (.natural m) → Conversion.Conv env b (.natural n) →
        m < 2^64 → n < 2^64 → m < n →
        HasType env loans ctx ghost (.decide a b) (.lt a b)
    | elements : xs.length = n → xs.length < 2^64 →
        (∀ x ∈ xs, HasType env loans ctx ghost x .i64) →
        HasType env loans ctx ghost (.elements n xs) (.array (.natural xs.length))
    | index : HasType env loans ctx ghost a (.array n) → HasType env loans ctx ghost i .u64 →
        HasType env loans ctx true p (.lt i n) → HasType env loans ctx ghost (.index a i p) .i64
    | arith : HasType env loans ctx ghost a .i64 → HasType env loans ctx ghost b .i64 →
        HasType env loans ctx ghost (.arith op a b) .i64
    | strict : HasType env loans ctx ghost a A → HasType env loans ctx ghost b B → HasType env loans ctx ghost (.strict a b) B
    | ltAdd : HasType env loans ctx true a .u64 → HasType env loans ctx true b .u64 → HasType env loans ctx true c .u64 →
        HasType env loans ctx true p (.lt a b) → HasType env loans ctx ghost (.ltAdd a b c p) (.lt (.uadd a c) (.uadd b c))
    | ltCancel : HasType env loans ctx true a .u64 → HasType env loans ctx true b .u64 → HasType env loans ctx true c .u64 →
        HasType env loans ctx true p (.lt (.uadd a c) (.uadd b c)) → HasType env loans ctx ghost (.ltCancel a b c p) (.lt a b)
    | ltLe : HasType env loans ctx true a .u64 → HasType env loans ctx true b .u64 → HasType env loans ctx true c .u64 →
        HasType env loans ctx true p (.lt a b) → HasType env loans ctx true q (.lt b (.uadd c (.natural 1))) →
        HasType env loans ctx ghost (.ltLe a b c p q) (.lt a c)
    | transport : HasType env loans ctx true f (.pi false .u64 .prop) → HasType env loans ctx true e (.eq a b) →
        HasType env loans ctx true p (.app f a) → HasType env loans ctx ghost (.transport f e p) (.app f b)
    | refine : HasType env loans ctx true p (.pi false .u64 .prop) → HasType env loans ctx ghost (.refine p) (.univ 0)
    | pack : HasType env loans ctx true p (.pi false .u64 .prop) → HasType env loans ctx ghost a .u64 →
        HasType env loans ctx true q (.app p a) → HasType env loans ctx ghost (.pack p a q) (.refine p)
    | witness : HasType env loans ctx ghost s (.refine p) → HasType env loans ctx ghost (.witness s) .u64
    | proof : HasType env loans ctx true s (.refine p) → HasType env loans ctx ghost (.proof s) (.app p (.witness s))
    | ifLt : HasType env loans ctx ghost a .u64 → HasType env loans ctx ghost b .u64 →
        HasType env loans (⟨.lt a b, true⟩ :: ctx) ghost yes (B.rename Nat.succ) →
        HasType env loans ctx ghost no B → HasType env loans ctx ghost (.ifLt a b yes no) B
    | ifEq : HasType env loans ctx ghost a .u64 → HasType env loans ctx ghost b .u64 →
        HasType env loans (⟨.eq a b, true⟩ :: ctx) ghost yes (B.rename Nat.succ) →
        HasType env loans ctx ghost no B → HasType env loans ctx ghost (.ifEq a b yes no) B
    | absurd {s : SortTag} : HasType env loans ctx true T s.term → HasType env loans ctx true p (.lt i (.natural 0)) →
        absurdAllowed env ghost T → HasType env loans ctx ghost (.absurd T p) T
    | foldI64 : HasType env loans ctx ghost n .u64 → HasType env loans ctx ghost init .i64 →
        HasType env loans ctx ghost body (foldBodyType n) → IterationBodyAllowed env ghost body →
        HasType env loans ctx ghost (.fold n init body) .i64
    | foldOwned : HasType env loans ctx ghost n .u64 → HasType env loans ctx ghost init accumulator →
        Owned env accumulator → HasType env loans ctx ghost body (foldAccumulatorBodyType n accumulator) →
        IterationBodyAllowed env ghost body →
        HasType env loans ctx ghost (.fold n init body) accumulator
    | loop : HasType env loans ctx true motive (.pi false .u64 (loopSortTerm proof)) →
        IterationMotiveAllowed env ghost proof motive →
        HasType env loans ctx (ghost || proof) n .u64 →
        HasType env loans ctx (ghost || proof) init (.app motive (.natural 0)) →
        HasType env loans ctx (ghost || proof) body (loopBodyType n motive proof) →
        IterationBodyAllowed env (ghost || proof) body →
        HasType env loans ctx ghost (.loop n motive init body) (.app motive n)
    | global : env.globals[g]? = some declaration →
        HasType env loans ctx ghost (.node (.global g) [])
          (declaration.type.rename (fun x => x + ctx.length))
    | ind : env.families[f]? = some entry → count = entry.declaration.arity →
        xs.length = count → (∀ x ∈ xs, HasType env loans ctx true x .u64) →
        HasType env loans ctx ghost (.node (.ind f count) xs)
          (if entry.declaration.data then .univ 0 else .prop)
    | con : env.families[f]? = some entry → entry.signatures[k]? = some signature →
        count = xs.length →
        Arguments env loans ctx ghost entry.declaration.data
          ((signatureTerm f signature).rename (fun x => x + ctx.length)) xs
          (.node (.ind f arity) indices) →
        HasType env loans ctx ghost (.node (.con f k count) xs) (.node (.ind f arity) indices)
    | propElim : env.families[f]? = some entry → entry.declaration.data = false →
        HasType env loans ctx true motive (propMotiveType entry.declaration.arity) →
        Cases env loans ctx motive entry.signatures cases →
        HasType env loans ctx true scrutinee (.node (.ind f entry.declaration.arity) indices) →
        HasType env loans ctx ghost (.node (.elim f cases.length) (motive :: (cases ++ [scrutinee])))
          (applications motive indices)
    | buffer : HasType env loans ctx true n .u64 → HasType env loans ctx ghost (.buffer n) (.univ 0)
    | alloc : HasType env loans ctx ghost n .u64 → HasType env loans ctx ghost value .i64 →
        HasType env loans ctx ghost (.alloc n value) (.buffer n)
    | store : HasType env loans ctx ghost buffer (.buffer n) → HasType env loans ctx ghost index .u64 →
        HasType env loans ctx ghost value .i64 → HasType env loans ctx true proof (.lt index n) →
        HasType env loans ctx ghost (.store buffer index value proof) (.buffer n)
    | load : HasType env loans ctx ghost buffer (.buffer n) → HasType env loans ctx ghost index .u64 →
        HasType env loans ctx true proof (.lt index n) →
        HasType env loans ctx ghost continuation (.pi false valueDomain (.pi false ownerDomain result)) →
        Conversion.Conv env valueDomain .i64 → Conversion.Conv env ownerDomain (.buffer (n.rename Nat.succ)) →
        Conversion.Conv env result normal → PartialRenaming.shift (-2) 0 normal = some outside →
        continuationAllowed env ghost outside → HasType env loans ctx ghost (.load buffer index proof continuation) outside
    | free : HasType env loans ctx ghost buffer (.buffer n) → HasType env loans ctx ghost rest T →
        HasType env loans ctx ghost (.free buffer rest) T
    | refBuffer : HasType env loans ctx true n .u64 →
        HasType env loans ctx ghost (.ref (.buffer n)) (.univ 0)
    | ghostBorrow : HasType env loans ctx true buffer (.buffer n) →
        HasType env loans ctx true (.borrow buffer) (.ref (.buffer n))
    | ghostDeref : HasType env loans ctx true reference (.ref (.buffer n)) →
        HasType env loans ctx true (.deref reference) (.buffer n)
    | borrowedIndex : HasType env loans ctx ghost reference (.ref (.buffer n)) →
        HasType env loans ctx ghost index .u64 → HasType env loans ctx true proof (.lt index n) →
        HasType env loans ctx ghost (.index reference index proof) .i64
    | back : HasType env loans ctx true owner (.univ 0) → Owned env owner →
        HasType env loans ctx true motive (.pi false owner (loopSortTerm erased)) →
        BackRepresentation env ghost erased motive →
        HasType env loans ctx ghost (.back erased owner motive) (.univ 0)
    | give : HasType env loans ctx ghost owner T → Owned env T →
        HasType env loans ctx true motive (.pi false T (loopSortTerm erased)) →
        BackRepresentation env ghost erased motive →
        HasType env loans ctx (ghost || erased) result (.app motive owner) →
        HasType env loans ctx ghost (.give erased motive owner result) (.back erased T motive)
    | take : HasType env loans ctx ghost value (.back erased owner motive) →
        HasType env loans ctx ghost (.lam false declaredOwner (.lam erased declaredResult body))
          (.pi false inferredOwner (.pi inferredErased inferredResult result)) →
        Conversion.Conv env declaredOwner owner → Conversion.Conv env declaredResult (takeResultType motive) →
        Conversion.Conv env result normal → PartialRenaming.shift (-2) 0 normal = some outside →
        continuationAllowed env ghost outside →
        HasType env loans ctx ghost (.take value (.lam false declaredOwner (.lam erased declaredResult body))) outside
    | dataElim : env.families[family]? = some entry → entry.declaration.data = true →
        (analysis = true → entry.boxed = true) →
        indices.length = entry.declaration.arity →
        HasType env loans ctx true motive (dataMotiveType family entry.declaration.params
          entry.declaration.arity (indices.take entry.declaration.params) proof) →
        HasType env loans ctx (ghost || proof) scrutinee
          (.node (.ind family entry.declaration.arity) indices) →
        dataCaseTypes family entry.declaration.params ctx.length entry.signatures
          (indices.take entry.declaration.params) motive (entry.boxed && !analysis) proof = some types →
        BranchTypes env loans ctx (ghost || proof) types cases →
        continuationAllowed env (ghost || proof)
          (.app (applications motive (indices.drop entry.declaration.params)) scrutinee) →
        HasType env loans ctx ghost
          (.node (if analysis then .caseOf family cases.length else .elim family cases.length)
            (motive :: (cases ++ [scrutinee])))
          (.app (applications motive (indices.drop entry.declaration.params)) scrutinee)
    | drop : env.families[family]? = some entry → entry.boxed = true →
        HasType env loans ctx ghost owner (.node (.ind family count) indices) →
        HasType env loans ctx ghost rest T →
        HasType env loans ctx ghost (.node (.drop family) [owner, rest]) T
    | refOwned : HasType env loans ctx true owner (.univ 0) → Owned env owner →
        HasType env loans ctx ghost (.ref owner) (.univ 0)
    | ghostBorrowOwned : HasType env loans ctx true owner T → Owned env T →
        HasType env loans ctx true (.borrow owner) (.ref T)
    | ghostDerefOwned : HasType env loans ctx true reference (.ref T) →
        HasType env loans ctx true (.deref reference) T
    | view : env.families[family]? = some entry → entry.declaration.data = true → entry.boxed = true →
        entry.declaration.arity = entry.declaration.params → indices.length = entry.declaration.params →
        HasType env loans ctx ghost scrutinee (.ref (.node (.ind family entry.declaration.arity) indices)) →
        HasType env loans ctx true motive
          (viewMotiveType dependent (.node (.ind family entry.declaration.arity) indices)) →
        ViewMotiveAllowed env ghost dependent motive →
        viewCaseTypes env family entry.declaration.params ctx.length entry.signatures indices motive recursion dependent = some types →
        BranchTypes env loans ctx ghost types cases →
        HasType env loans ctx ghost (.node (.view recursion family cases.length) (motive :: (cases ++ [scrutinee])))
          (viewResult dependent motive scrutinee)
    | codeBorrowOwned : HasType env loans ctx true (.var owner) T → Owned env T →
        Loans.active ctx.length loans owner = true →
        HasType env loans ctx false (.borrow (.var owner)) (.ref T)
    | lendGeneric : HasType env loans ctx ghost owner T → Owned env T → Lending.Outlived env A →
        HasType env loans ctx ghost reader (.pi false (.ref T) (A.rename Nat.succ)) →
        HasType env loans ctx ghost continuation
          (.pi false A ((Term.pi false T (result.rename Nat.succ)).rename Nat.succ)) →
        continuationAllowed env ghost result →
        HasType env loans ctx ghost (.lend owner reader continuation) result
    | lendDependentCode : HasType env loans ctx false (.var owner) T → Owned env T →
        Binder env loans ctx false domain sort → Conversion.Conv env domain (.ref T) →
        HasType env (Loans.enter ctx.length owner loans) ctx false (Lending.read (.var owner) readerBody) A →
        Lending.Outlived env A → Conversion.Conv env first A →
        Conversion.Conv env again (T.rename Nat.succ) →
        HasType env loans ctx false (Lending.restore (.var owner) first body) (.pi false first result) →
        Conversion.Conv env result normal → PartialRenaming.shift (-1) 0 normal = some outside →
        continuationAllowed env false outside →
        HasType env loans ctx false
          (.lend (.var owner) (.lam false domain readerBody) (.lam false first (.lam false again body))) outside
    | lendDependentGhost : HasType env loans ctx true owner T → Owned env T →
        Binder env loans ctx false domain sort → Conversion.Conv env domain (.ref T) →
        HasType env loans ctx true (Lending.read owner readerBody) A →
        Lending.Outlived env A → Conversion.Conv env first A →
        Conversion.Conv env again (T.rename Nat.succ) →
        HasType env loans ctx true (Lending.restore owner first body) (.pi false first result) →
        Conversion.Conv env result normal → PartialRenaming.shift (-1) 0 normal = some outside →
        HasType env loans ctx true
          (.lend owner (.lam false domain readerBody) (.lam false first (.lam false again body))) outside
    | convert : HasType env loans ctx ghost t A → Conversion.Conv env A B → HasType env loans ctx ghost t B

  /-- Constructor fields instantiate an actual dependent Pi telescope. -/
  inductive Arguments (env : Environment) : Loans.Stack → Context → Bool → Bool →
      Term → List Term → Term → Prop where
    | nil : Conversion.Conv env telescope result → Arguments env loans ctx ghost data telescope [] result
    | cons : Conversion.Conv env telescope (.pi erased domain rest) →
        HasType env loans ctx (ghost || !(data && !erased)) argument domain →
        Arguments env loans ctx ghost data
          (rest.subst (fun | 0 => argument | n + 1 => .var n)) arguments result →
        Arguments env loans ctx ghost data telescope (argument :: arguments) result

  /-- There is exactly one checked branch for each checked constructor signature. -/
  inductive Cases (env : Environment) : Loans.Stack → Context → Term →
      List Signature → List Term → Prop where
    | nil : Cases env loans ctx motive [] []
    | cons : HasType env loans ctx true branch (propCaseType signature motive) →
        Cases env loans ctx motive signatures branches →
        Cases env loans ctx motive (signature :: signatures) (branch :: branches)
  /-- Branch terms are checked against the concrete generated telescope list. -/
  inductive BranchTypes (env : Environment) : Loans.Stack → Context → Bool → List Term → List Term → Prop where
    | nil : BranchTypes env loans ctx ghost [] []
    | cons : HasType env loans ctx ghost branch type → BranchTypes env loans ctx ghost types branches →
        BranchTypes env loans ctx ghost (type :: types) (branch :: branches)

end

end Jihoo.NativeKernel.Environment.LoanTyping
