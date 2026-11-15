import Jihoo.NativeFamilyIotaParallelConversion

/-! Exact raw observing-root inversion for the enlarged quotient parallel
calculus. Family roots retain every real lookup/length guard and explicit
syntactic result; no output typing or reduction oracle is a premise. -/
namespace Jihoo.NativeKernel.Environment.FamilyIota.Extended.Quotient
open NativeKernel.Conversion (ListRel)
open ACU
variable {env : Environment}
local notation "QPar" => Parallel env
local notation "QAtom" => Atom env
set_option linter.unusedSimpArgs false

inductive ParallelRoot (env : Environment) : Term → Term → Prop where
  | beta (e : Bool) (A body : Term) : Arithmetic f (.lam e A body) →
      (Parallel env) body body' → (Parallel env) a a' → ParallelRoot env (.app f a) (body'.subst (single a'))
  | sub (m n : Nat) (p : Term) : Arithmetic a (.natural m) → Arithmetic b (.natural n) →
      n ≤ m → m < 2^64 → ParallelRoot env (.usub a b p) (.natural (m-n))
  | read (count : Nat) (k : Nat) (p : Term) : Arithmetic a (.elements count xs) →
      Arithmetic index (.natural k) → ListRel (Parallel env) xs ys → ys[k]? = some v →
      ParallelRoot env (.index a index p) v
  | witnessPack (p a q : Term) : Arithmetic t (.pack p a q) → (Parallel env) a a' → ParallelRoot env (.witness t) a'
  | proofPack (p a q : Term) : Arithmetic t (.pack p a q) → (Parallel env) q q' → ParallelRoot env (.proof t) q'
  | derefBorrow (a : Term) : Arithmetic t (.node .borrow [a]) → (Parallel env) a a' →
      ParallelRoot env (.node .deref [t]) a'
  | borrowDeref (a : Term) : Arithmetic t (.node .deref [a]) → (Parallel env) a a' →
      ParallelRoot env (.node .borrow [t]) a'
  | transportRefl (a : Term) : Arithmetic eq (.refl a) → (Parallel env) p p' →
      ParallelRoot env (.transport f eq p) p'
  | ifLtTrue (m n : Nat) (no : Term) : Arithmetic a (.natural m) → Arithmetic b (.natural n) →
      m < n → (Parallel env) yes yes' →
      ParallelRoot env (.ifLt a b yes no) (yes'.subst (single (.decide (.natural m) (.natural n))))
  | ifLtFalse (m n : Nat) (yes : Term) : Arithmetic a (.natural m) → Arithmetic b (.natural n) →
      n ≤ m → (Parallel env) no no' → ParallelRoot env (.ifLt a b yes no) no'
  | ifEqTrue (n : Nat) (no : Term) : Arithmetic a (.natural n) → Arithmetic b (.natural n) →
      (Parallel env) yes yes' → ParallelRoot env (.ifEq a b yes no) (yes'.subst (single (.refl (.natural n))))
  | ifEqFalse (m n : Nat) (yes : Term) : Arithmetic a (.natural m) → Arithmetic b (.natural n) →
      m ≠ n → (Parallel env) no no' → ParallelRoot env (.ifEq a b yes no) no'

  | elim (family constructor : Nat) (entry : CheckedFamily) (signature : Signature)
        (motive : Term) (cases : List Term) (scrutinee : Term) :
        env.families[family]? = some entry → entry.signatures[constructor]? = some signature →
        cases.length = entry.signatures.length → values.length = signature.fields.length →
        Arithmetic scrutinee (.node (.con family constructor values.length) values) →
        (Parallel env) motive motive' → ListRel ((Parallel env)) cases cases' → ListRel ((Parallel env)) values values' →
        cases'[constructor]? = some branch' →
        ParallelRoot env (elimTerm family motive cases scrutinee) (elimBody entry signature family motive' branch' cases' values')
  | caseOf (family constructor : Nat) (entry : CheckedFamily) (signature : Signature)
        (motive : Term) (cases : List Term) (scrutinee : Term) :
        env.families[family]? = some entry → entry.declaration.data = true → entry.signatures[constructor]? = some signature →
        cases.length = entry.signatures.length → values.length = signature.fields.length →
        Arithmetic scrutinee (.node (.con family constructor values.length) values) →
        ListRel ((Parallel env)) cases cases' → ListRel ((Parallel env)) values values' → cases'[constructor]? = some branch' →
        ParallelRoot env (caseTerm family motive cases scrutinee) (applications branch' (values'.drop entry.declaration.params))
  | view (recursion : Bool) (family constructor : Nat) (entry : CheckedFamily) (signature : Signature)
        (motive : Term) (cases : List Term) (scrutinee : Term) :
        env.families[family]? = some entry → entry.boxed = true → entry.signatures[constructor]? = some signature →
        cases.length = entry.signatures.length → values.length = signature.fields.length →
        entry.declaration.params ≤ signature.fields.length →
        viewPlan env family (signature.fields.drop entry.declaration.params) = some plans →
        Arithmetic scrutinee (.borrow (.node (.con family constructor values.length) values)) →
        (Parallel env) motive motive' → ListRel ((Parallel env)) cases cases' → ListRel ((Parallel env)) values values' →
        cases'[constructor]? = some branch' →
        ParallelRoot env (viewTerm recursion family motive cases scrutinee)
          (viewBody recursion family entry.declaration.params motive' branch' cases' values' plans)
  | drop (family : Nat) (owner rest : Term) : (Parallel env) rest rest' →
        ParallelRoot env (.node (.drop family) [owner,rest]) rest'

local notation "RootP" => ParallelRoot env

theorem ParallelRoot.atom (h : RootP a b) : QAtom a b := by
  cases h <;> constructor <;> assumption

theorem ParallelRoot.parallel (h : RootP a b) : QPar a b := by
  apply Parallel.ofAtom h.atom
  cases h <;> simp only [arithmeticFlatten,elimTerm,caseTerm,viewTerm]

theorem Atom.inspect (h : QAtom t u) :
    (∃ x, t = .var x ∧ u = .var x) ∨
    (∃ op xs ys, t = .node op xs ∧ u = .node op ys ∧ ListRel QPar xs ys) ∨ RootP t u := by
  cases h with
  | var x => exact .inl ⟨x,rfl,rfl⟩
  | node op hs => exact .inr (.inl ⟨op,_,_,rfl,rfl,hs⟩)
  | _ => exact .inr (.inr (by constructor <;> assumption))

def FamilyInputs (env : Environment) : Term → Term → Prop
  | .node (.elim family count) args,output =>
      ∃ entry constructor signature motive cases scrutinee values motiveOut casesOut valuesOut branch,
        count = cases.length ∧ args = motive :: (cases ++ [scrutinee]) ∧
        env.families[family]? = some entry ∧ entry.signatures[constructor]? = some signature ∧
        cases.length = entry.signatures.length ∧ values.length = signature.fields.length ∧
        Arithmetic scrutinee (.node (.con family constructor values.length) values) ∧
        Parallel env motive motiveOut ∧ ListRel (Parallel env) cases casesOut ∧ ListRel (Parallel env) values valuesOut ∧
        casesOut[constructor]? = some branch ∧ output = elimBody entry signature family motiveOut branch casesOut valuesOut
  | .node (.caseOf family count) args,output =>
      ∃ entry constructor signature motive cases scrutinee values casesOut valuesOut branch,
        count = cases.length ∧ args = motive :: (cases ++ [scrutinee]) ∧
        env.families[family]? = some entry ∧ entry.declaration.data = true ∧ entry.signatures[constructor]? = some signature ∧
        cases.length = entry.signatures.length ∧ values.length = signature.fields.length ∧
        Arithmetic scrutinee (.node (.con family constructor values.length) values) ∧
        ListRel (Parallel env) cases casesOut ∧ ListRel (Parallel env) values valuesOut ∧
        casesOut[constructor]? = some branch ∧ output = applications branch (valuesOut.drop entry.declaration.params)
  | .node (.view recursion family count) args,output =>
      ∃ entry constructor signature motive cases scrutinee values plans motiveOut casesOut valuesOut branch,
        count = cases.length ∧ args = motive :: (cases ++ [scrutinee]) ∧
        env.families[family]? = some entry ∧ entry.boxed = true ∧ entry.signatures[constructor]? = some signature ∧
        cases.length = entry.signatures.length ∧ values.length = signature.fields.length ∧
        entry.declaration.params ≤ signature.fields.length ∧
        viewPlan env family (signature.fields.drop entry.declaration.params) = some plans ∧
        Arithmetic scrutinee (.borrow (.node (.con family constructor values.length) values)) ∧
        Parallel env motive motiveOut ∧ ListRel (Parallel env) cases casesOut ∧ ListRel (Parallel env) values valuesOut ∧
        casesOut[constructor]? = some branch ∧ output = viewBody recursion family entry.declaration.params motiveOut branch casesOut valuesOut plans
  | .node (.drop _) args,output => ∃ owner rest result,args = [owner,rest] ∧ Parallel env rest result ∧ output = result
  | _,_ => True

/-- Actual observing-root inversion, before any dependent matching of the
source's encoded branch count/layout. -/
theorem ParallelRoot.family_inputs (step : RootP term result) : FamilyInputs env term result := by
  cases step
  all_goals first | trivial | skip
  case elim found sigFound count fields view motiveStep caseSteps valueSteps selected =>
    exact ⟨_,_,_,_,_,_,_,_,_,_,_,rfl,rfl,found,sigFound,count,fields,view,motiveStep,caseSteps,valueSteps,selected,rfl⟩
  case caseOf found data sigFound count fields view caseSteps valueSteps selected =>
    exact ⟨_,_,_,_,_,_,_,_,_,_,rfl,rfl,found,data,sigFound,count,fields,view,caseSteps,valueSteps,selected,rfl⟩
  case view found boxed sigFound count fields bound planned view motiveStep caseSteps valueSteps selected =>
    exact ⟨_,_,_,_,_,_,_,_,_,_,_,_,rfl,rfl,found,boxed,sigFound,count,fields,bound,planned,view,motiveStep,caseSteps,valueSteps,selected,rfl⟩
  case drop step => exact ⟨_,_,_,rfl,step,rfl⟩

end Jihoo.NativeKernel.Environment.FamilyIota.Extended.Quotient
