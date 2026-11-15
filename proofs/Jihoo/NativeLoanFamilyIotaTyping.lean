import Jihoo.NativeFamilyIotaSoundness
import Jihoo.NativeLoanPrincipalInversion

/-! Original-type preservation for pure Drop and genuinely generated nullary
View cases. Generic dependent recursive iota preservation is not assumed. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.FamilyIota
open _root_.Jihoo.NativeKernel.Environment.FamilyIota
open _root_.Jihoo.NativeKernel.Environment.LoanTyping.Conversion
set_option linter.unusedSimpArgs false

/-- Pure Drop returns its independently typed continuation at the exact
original type, with every surrounding conversion retained. -/
theorem drop_preserves (typed : HasType env [] ctx true (.node (.drop family) [owner,rest]) type) :
    HasType env [] ctx true rest type := by
  obtain ⟨result,continuation,converted⟩ := typed.principalView
  exact .convert continuation converted

private theorem mapM_get {α β : Type} {xs : List α} {ys : List β} {f : α → Option β} {index : Nat} {x : α}
    (generated : xs.mapM f = some ys) (found : xs[index]? = some x) :
    ∃ y,ys[index]? = some y ∧ f x = some y := by
  induction xs generalizing ys index with
  | nil => simp at found
  | cons head tail ih =>
    simp only [List.mapM_cons] at generated
    cases first : f head with
    | none => simp [first] at generated
    | some value =>
      simp only [first,Bind.bind,Option.bind] at generated
      cases rest : tail.mapM f with
      | none => simp [rest] at generated
      | some values =>
        simp only [rest,Bind.bind,Option.bind,pure,Option.some.injEq] at generated
        subst ys
        cases index with
        | zero =>
          simp only [List.getElem?_cons_zero,Option.some.injEq] at found
          subst x
          exact ⟨value,rfl,first⟩
        | succ index =>
          simp only [List.getElem?_cons_succ] at found ⊢
          exact ih rest found

/-- A successful generated telescope really supplies the selected case's type. -/
theorem viewCaseTypes_get
    (generated : viewCaseTypes env family params depth signatures ps motive recursion dependent = some types)
    (found : signatures[constructor]? = some signature) :
    ∃ type,types[constructor]? = some type ∧
      viewCaseType env family constructor params depth signature ps motive recursion dependent = some type := by
  apply mapM_get (index := constructor) (x := (signature,constructor)) generated
  simp only [List.getElem?_zipIdx,found,Option.map_some,Nat.zero_add]

theorem dataCaseTypes_get
    (generated : dataCaseTypes family params depth signatures ps motive recursion proof = some types)
    {constructor : Nat} (found : signatures[constructor]? = some signature) :
    ∃ type,types[constructor]? = some type ∧
      dataCaseType family constructor params depth signature ps motive recursion proof = some type := by
  apply mapM_get (index := constructor) (x := (signature,constructor)) generated
  simp only [List.getElem?_zipIdx,found,Option.map_some,Nat.zero_add]

/-- Retrieve a real derivation from the same mutual branch judgment. -/
theorem branch_get {index : Nat} (typed : BranchTypes env [] ctx mode types branches)
    (typeFound : types[index]? = some type) (branchFound : branches[index]? = some branch) :
    HasType env [] ctx mode branch type := by
  induction index generalizing types branches with
  | zero =>
    cases typed with
    | nil => simp at typeFound
    | cons head tail =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at typeFound branchFound
      subst type
      subst branch
      exact head
  | succ index ih =>
    cases typed with
    | nil => simp at typeFound
    | cons head tail => exact ih tail typeFound branchFound

theorem viewCaseType_nullary (family constructor depth : Nat) (indices : List Term)
    (motive : Term) (recursion dependent : Bool) :
    viewCaseType env family constructor 0 depth ⟨[],indices⟩ [] motive recursion dependent =
      some (viewResult dependent motive (.borrow (.node (.con family constructor 0) []))) := by
  cases recursion <;> cases dependent <;>
    simp [viewCaseType,viewPlan,viewPositions,viewInstFields,viewHypothesisTelescope,
      viewCaseResult,viewResult,closeDataFields]
  all_goals exact Term.rename_id motive

private def ViewInputs (env : Environment) (ctx : Context) : Term → Term → Prop
  | .node (.view recursion family count) args, type =>
      ∃ entry motive cases scrutinee indices dependent types,
        count = cases.length ∧ args = motive :: (cases ++ [scrutinee]) ∧
        env.families[family]? = some entry ∧ indices.length = entry.declaration.params ∧
        viewCaseTypes env family entry.declaration.params ctx.length entry.signatures indices motive recursion dependent = some types ∧
        BranchTypes env [] ctx true types cases ∧ Conversion.Conv env (viewResult dependent motive scrutinee) type
  | _,_ => True

private theorem ViewInputs.convert (inputs : ViewInputs env ctx term A) (converted : Conversion.Conv env A B) :
    ViewInputs env ctx term B := by
  fun_cases ViewInputs env ctx term A <;> simp only [ViewInputs] at inputs ⊢
  · obtain ⟨entry,motive,cases,scrutinee,indices,dependent,types,count,layout,found,size,generated,branches,result⟩ := inputs
    exact ⟨entry,motive,cases,scrutinee,indices,dependent,types,count,layout,found,size,generated,branches,.trans result converted⟩

private theorem view_inputs (typed : HasType env [] ctx true term type) : ViewInputs env ctx term type := by
  have stronger : ∀ stack mode,HasType env stack ctx mode term type → stack = [] → mode = true → ViewInputs env ctx term type := by
    intro stack mode h
    apply HasType.rec (t := h)
      (motive_1 := fun _ _ _ _ _ _ => True)
      (motive_2 := fun stack ctx mode term type _ => stack = [] → mode = true → ViewInputs env ctx term type)
      (motive_3 := fun _ _ _ _ _ _ _ _ => True)
      (motive_4 := fun _ _ _ _ _ _ => True) (motive_5 := fun _ _ _ _ _ _ => True)
    all_goals intros
    all_goals first | trivial | skip
    case dataElim => split <;> trivial
    case view found data boxed arity size scrutinee motive allowed generated branches _ _ _ emptyStack trueMode =>
      cases emptyStack
      subst trueMode
      exact ⟨_,_,_,_,_,_,_,rfl,rfl,found,size,generated,branches,.refl _⟩
    case convert typed converted ih emptyStack trueMode => exact (ih emptyStack trueMode).convert converted
  exact stronger [] true typed rfl rfl

/-- A known nullary view returns the selected, independently typed branch.
This applies to dependent motives and arbitrary surrounding type conversions. -/
theorem nullary_view_preserves
    (found : env.families[family]? = some entry)
    (signature : entry.signatures[constructor]? = some ⟨[],indices⟩)
    (params : entry.declaration.params = 0) (selected : cases[constructor]? = some branch)
    (typed : HasType env [] ctx true
      (viewTerm recursion family motive cases (.borrow (.node (.con family constructor 0) []))) type) :
    HasType env [] ctx true branch type := by
  obtain ⟨entry',motive',cases',scrutinee',ps,dependent,types,count,layout,found',size,generated,branches,result⟩ := view_inputs typed
  have same := Option.some.inj (found.symm.trans found')
  subst entry'
  have outer := List.cons.inj layout
  have motives := outer.1
  subst motive'
  have parts := List.append_inj' outer.2 (by simp)
  obtain ⟨rfl,scrutineeEq⟩ := parts
  have scrutineeEq := (List.cons.inj scrutineeEq).1
  subst scrutinee'
  have noParameters : ps = [] := List.length_eq_zero_iff.mp (size.trans params)
  subst ps
  rw [params] at generated
  obtain ⟨expected,typeFound,built⟩ := viewCaseTypes_get generated signature
  have expectedEq := Option.some.inj ((viewCaseType_nullary family constructor ctx.length indices motive recursion dependent).symm.trans built)
  subst expected
  exact .convert (branch_get branches typeFound selected) result

end Jihoo.NativeKernel.Environment.LoanTyping.FamilyIota
