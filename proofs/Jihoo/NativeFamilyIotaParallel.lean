import Jihoo.NativeFamilyIotaDelta

/-! Actual environment-indexed family/legacy parallel computation on the finite
arithmetic quotient. Every family constructor has genuine raw lookup guards;
all parallel premises refer only to original motive/case/field subterms. -/
namespace Jihoo.NativeKernel.Environment.FamilyIota.Extended.Quotient
open NativeKernel.Conversion (ListRel)
open ACU
set_option linter.unusedSimpArgs false

private theorem listRel_perm_left (p : xs.Perm zs) (h : ListRel R xs ys) :
    ∃ ws, ys.Perm ws ∧ ListRel R zs ws := by
  induction p generalizing ys with
  | nil => cases h; exact ⟨[],.nil,.nil⟩
  | cons x p ih =>
      cases h with
      | cons hx hs =>
          obtain ⟨ws,hp,hr⟩ := ih hs
          exact ⟨_::ws,hp.cons _,.cons hx hr⟩
  | swap x y xs =>
      cases h with
      | cons hx hs => cases hs with
        | cons hy hs => exact ⟨_,List.Perm.swap _ _ _,.cons hy (.cons hx hs)⟩
  | trans p q ip iq =>
      obtain ⟨ws,hp,hr⟩ := ip h
      obtain ⟨vs,hq,hs⟩ := iq hr
      exact ⟨vs,hp.trans hq,hs⟩

private theorem listRel_append (h : ListRel R xs ys) (k : ListRel R us vs) :
    ListRel R (xs ++ us) (ys ++ vs) := by
  induction h with
  | nil => exact k
  | cons ha hs ih => exact .cons ha ih

private theorem listRel_length (h : ListRel R xs ys) : xs.length = ys.length := by
  induction h <;> simp_all

mutual
  /-- Each displayed additive atom performs one parallel native computation;
  arbitrary arithmetic changes before and after it are retained explicitly. -/
  inductive Parallel (env : Environment) : Term → Term → Prop where
    | intro : (arithmeticFlatten a).Perm xs → ListRel (Atom env) xs ys →
        Arithmetic b (sumTerms ys) → Parallel env a b

  /-- Native parallel roots inspect constructors modulo proved Arithmetic.
  The node case follows every child, including binder and proof fields. -/
  inductive Atom (env : Environment) : Term → Term → Prop where
    | var (x : Nat) : Atom env (.var x) (.var x)
    | node (op : Op) : ListRel (Parallel env) xs ys → Atom env (.node op xs) (.node op ys)
    | beta (e : Bool) (A body : Term) : Arithmetic f (.lam e A body) →
        Parallel env body body' → Parallel env a a' → Atom env (.app f a) (body'.subst (single a'))
    | sub (m n : Nat) (p : Term) : Arithmetic a (.natural m) → Arithmetic b (.natural n) →
        n ≤ m → m < 2^64 → Atom env (.usub a b p) (.natural (m-n))
    | read (count : Nat) (k : Nat) (p : Term) : Arithmetic a (.elements count xs) →
        Arithmetic index (.natural k) → ListRel (Parallel env) xs ys → ys[k]? = some v →
        Atom env (.index a index p) v
    | witnessPack (p a q : Term) : Arithmetic t (.pack p a q) → Parallel env a a' → Atom env (.witness t) a'
    | proofPack (p a q : Term) : Arithmetic t (.pack p a q) → Parallel env q q' → Atom env (.proof t) q'
    | derefBorrow (a : Term) : Arithmetic t (.node .borrow [a]) → Parallel env a a' →
        Atom env (.node .deref [t]) a'
    | borrowDeref (a : Term) : Arithmetic t (.node .deref [a]) → Parallel env a a' →
        Atom env (.node .borrow [t]) a'
    | transportRefl (a : Term) : Arithmetic eq (.refl a) → Parallel env p p' →
        Atom env (.transport f eq p) p'
    | ifLtTrue (m n : Nat) (no : Term) : Arithmetic a (.natural m) → Arithmetic b (.natural n) →
        m < n → Parallel env yes yes' →
        Atom env (.ifLt a b yes no) (yes'.subst (single (.decide (.natural m) (.natural n))))
    | ifLtFalse (m n : Nat) (yes : Term) : Arithmetic a (.natural m) → Arithmetic b (.natural n) →
        n ≤ m → Parallel env no no' → Atom env (.ifLt a b yes no) no'
    | ifEqTrue (n : Nat) (no : Term) : Arithmetic a (.natural n) → Arithmetic b (.natural n) →
        Parallel env yes yes' → Atom env (.ifEq a b yes no) (yes'.subst (single (.refl (.natural n))))
    | ifEqFalse (m n : Nat) (yes : Term) : Arithmetic a (.natural m) → Arithmetic b (.natural n) →
        m ≠ n → Parallel env no no' → Atom env (.ifEq a b yes no) no'
    | elim (family constructor : Nat) (entry : CheckedFamily) (signature : Signature)
        (motive : Term) (cases : List Term) (scrutinee : Term) :
        env.families[family]? = some entry → entry.signatures[constructor]? = some signature →
        cases.length = entry.signatures.length → values.length = signature.fields.length →
        Arithmetic scrutinee (.node (.con family constructor values.length) values) →
        Parallel env motive motive' → ListRel (Parallel env) cases cases' → ListRel (Parallel env) values values' →
        cases'[constructor]? = some branch' →
        Atom env (elimTerm family motive cases scrutinee) (elimBody entry signature family motive' branch' cases' values')
    | caseOf (family constructor : Nat) (entry : CheckedFamily) (signature : Signature)
        (motive : Term) (cases : List Term) (scrutinee : Term) :
        env.families[family]? = some entry → entry.declaration.data = true → entry.signatures[constructor]? = some signature →
        cases.length = entry.signatures.length → values.length = signature.fields.length →
        Arithmetic scrutinee (.node (.con family constructor values.length) values) →
        ListRel (Parallel env) cases cases' → ListRel (Parallel env) values values' → cases'[constructor]? = some branch' →
        Atom env (caseTerm family motive cases scrutinee) (applications branch' (values'.drop entry.declaration.params))
    | view (recursion : Bool) (family constructor : Nat) (entry : CheckedFamily) (signature : Signature)
        (motive : Term) (cases : List Term) (scrutinee : Term) :
        env.families[family]? = some entry → entry.boxed = true → entry.signatures[constructor]? = some signature →
        cases.length = entry.signatures.length → values.length = signature.fields.length →
        entry.declaration.params ≤ signature.fields.length →
        viewPlan env family (signature.fields.drop entry.declaration.params) = some plans →
        Arithmetic scrutinee (.borrow (.node (.con family constructor values.length) values)) →
        Parallel env motive motive' → ListRel (Parallel env) cases cases' → ListRel (Parallel env) values values' →
        cases'[constructor]? = some branch' →
        Atom env (viewTerm recursion family motive cases scrutinee)
          (viewBody recursion family entry.declaration.params motive' branch' cases' values' plans)
    | drop (family : Nat) (owner rest : Term) : Parallel env rest rest' →
        Atom env (.node (.drop family) [owner,rest]) rest'
end

variable {env : Environment}
local notation "QPar" => Parallel env
local notation "QAtom" => Atom env


private theorem listQAtom_replicate_one (n : Nat) :
    ListRel QAtom (List.replicate n (.natural 1)) (List.replicate n (.natural 1)) := by
  induction n with
  | zero => exact .nil
  | succ n ih => exact .cons (.node _ .nil) ih

private theorem listQPar_refl_nil : ListRel QPar [] [] := .nil

theorem Parallel.output (h : QPar a b) (eqv : Arithmetic b b') : QPar a b' := by
  cases h with
  | intro p hs out => exact .intro p hs (eqv.symm.trans out)

/-- Parallel reduction follows the binary additive constructor by concatenating
its finite atom derivations; no uniqueness of a bag ordering is assumed. -/
theorem Parallel.addCong (ha : QPar a a') (hb : QPar b b') : QPar (.uadd a b) (.uadd a' b') := by
  cases ha with
  | intro pa hsa ea => cases hb with
    | intro pb hsb eb =>
        exact .intro (by simpa only [Term.uadd,arithmeticFlatten] using pa.append pb) (listRel_append hsa hsb)
          ((Arithmetic.addCong ea eb).trans (Arithmetic.sumTerms_append _ _))

/-- Parallel node congruence includes malformed arities without treating a
literal carrying children as a scalar value. -/
theorem Parallel.node (op : Op) (h : ListRel QPar xs ys) : QPar (.node op xs) (.node op ys) := by
  have atom := Atom.node op h
  have single : ListRel QAtom [.node op xs] [.node op ys] := .cons atom .nil
  have output : Arithmetic (.node op ys) (sumTerms [.node op ys]) := (Arithmetic.zero _).symm
  cases op <;> try (exact .intro (by simp only [arithmeticFlatten]; exact .refl _) single output)
  case uadd =>
    cases h with
    | nil => exact .intro (by simp only [arithmeticFlatten]; exact .refl _) single output
    | cons ha hs => cases hs with
      | nil => exact .intro (by simp only [arithmeticFlatten]; exact .refl _) single output
      | cons hb hs => cases hs with
        | nil => exact ha.addCong hb
        | cons hc hs => exact .intro (by simp only [arithmeticFlatten]; exact .refl _) single output
  case natural n =>
    cases h with
    | nil =>
        by_cases bound : n < AffineSum.wordLimit
        · exact .intro (.refl _) (by simpa only [arithmeticFlatten,bound,↓reduceIte] using listQAtom_replicate_one n)
            (Arithmetic.flatten _)
        · exact .intro (.refl _) (by simpa only [arithmeticFlatten,bound,↓reduceIte] using single)
            (Arithmetic.flatten _)
    | cons ha hs => exact .intro (by simp only [arithmeticFlatten]; exact .refl _) single output

theorem Parallel.refl (t : Term) : QPar t t := by
  induction t using Term.rec (motive_2 := fun xs => ListRel QPar xs xs) with
  | var x => exact .intro (by simp only [arithmeticFlatten]; exact .refl _) (.cons (Atom.var x) .nil) (Arithmetic.zero _).symm
  | node op xs ih => exact .node op ih
  | nil => exact .nil
  | cons x xs ix is => exact .cons ix is

theorem Parallel.arithmetic (h : Arithmetic a b) : QPar a b := (Parallel.refl a).output h


theorem Parallel.ofAtom (step : QAtom a b) (atomic : arithmeticFlatten a = [a]) : QPar a b :=
  .intro (by rw [atomic]) (.cons step .nil) (Arithmetic.zero _).symm

private theorem list_refl (terms : List Term) : ListRel QPar terms terms := by
  induction terms with
  | nil => exact .nil
  | cons term terms ih => exact .cons (Parallel.refl term) ih

/-- Every actual raw family contraction is a parallel quotient computation.
This includes forged/untyped tables and every real metadata/arity guard. -/
theorem Parallel.ofRoot (step : Root env a b) : QPar a b := by
  cases step with
  | @elim family entry constructor signature cases branch motive values found sigFound selected count fields =>
    exact Parallel.ofAtom (.elim family constructor entry signature motive cases _ found sigFound count fields
      (.refl _) (Parallel.refl motive) (list_refl cases) (list_refl values) selected)
      (by simp only [elimTerm,arithmeticFlatten])
  | @caseOf family entry constructor signature cases branch motive values found data sigFound selected count fields =>
    exact Parallel.ofAtom (.caseOf family constructor entry signature motive cases _ found data sigFound count fields
      (.refl _) (list_refl cases) (list_refl values) selected)
      (by simp only [caseTerm,arithmeticFlatten])
  | @view family entry constructor signature cases branch plans recursion motive values found boxed sigFound selected count fields bound planned =>
    exact Parallel.ofAtom (.view recursion family constructor entry signature motive cases _ found boxed sigFound count fields bound planned
      (.refl _) (Parallel.refl motive) (list_refl cases) (list_refl values) selected)
      (by simp only [viewTerm,arithmeticFlatten])
  | drop => exact Parallel.ofAtom (.drop _ _ _ (Parallel.refl _)) (by simp only [arithmeticFlatten])

end Jihoo.NativeKernel.Environment.FamilyIota.Extended.Quotient
