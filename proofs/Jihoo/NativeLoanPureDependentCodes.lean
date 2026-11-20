import Jihoo.NativeLoanPureTypeUniqueness
import Jihoo.NativeLoanPureMixedAdmission
import Jihoo.NativeLoanPureHypothesisObservation
import Jihoo.NativeMultiUniverseClosure
import Jihoo.NativeAdministrativeUniverseValues

set_option maxUniverseOffset 40

/-! Type codes occur as source values in the finite universe model. A
dependent product ranges over actual decoded argument codes; a type-level
application extends the same assignment with its computed argument. -/
namespace Jihoo.NativeKernel.Environment.Semantics.MultiUniverse.DependentCodes

open Finite (LevelSort Universe Carrier)
open AffineSum (Expr)
open LoanTyping.PureHypothesisObservation (ScalarExpr)

abbrev inputSort (level : Fin 32) : LevelSort := .type ⟨level.val,by omega⟩
abbrev universeSort (level : Fin 32) : LevelSort := .type ⟨level.val+1,by omega⟩
abbrev smallSort : LevelSort := .type ⟨0,by decide⟩

inductive Code : List (Fin 32) → LevelSort → Type where
  | parameter (index : Fin levels.length) : Code levels (inputSort (levels.get index))
  | natural : Code levels smallSort
  | proposition : Code levels smallSort
  | universeCode (level : Fin 32) : Code levels (universeSort level)
  | less : ScalarExpr [] left → ScalarExpr [] right → Code levels .proposition
  | equal : ScalarExpr [] left → ScalarExpr [] right → Code levels .proposition
  | arrow (erased : Bool) (allowed : if erased then domainSort.native = .prop else domainSort.native ≠ .prop) :
      Code levels domainSort → Code levels resultSort → Code levels (domainSort.pi resultSort)
  | abstract (level : Fin 32) : Code (level :: levels) resultSort → Code levels ((universeSort level).pi resultSort)
  | apply (level : Fin 32) : Code (level :: levels) resultSort → Code levels (inputSort level) → Code levels resultSort

def Code.syntax : Code levels sort → Term
  | .parameter index => .var index.val
  | .natural => .u64
  | .proposition => .prop
  | .universeCode level => .univ level.val
  | .less (left := left) (right := right) _ _ => .lt left.toTerm right.toTerm
  | .equal (left := left) (right := right) _ _ => .eq left.toTerm right.toTerm
  | .arrow erased _ domain codomain => .pi erased domain.syntax (codomain.syntax.rename Nat.succ)
  | .abstract level codomain => .pi false (.univ level.val) codomain.syntax
  | .apply level body argument => .app (.lam false (.univ level.val) body.syntax) argument.syntax

def Code.meaning : (code : Code levels sort) → Assignment levels.get → Universe sort
  | .parameter index, assignment => assignment.codes index
  | .natural, _ => Finite.natural
  | .proposition, _ => Finite.propositionUniverse
  | .universeCode level, _ => Finite.Values.codeUniverse level
  | .less (left := left) (right := right) _ _, _ => .proposition (left.eval (fun _ => 0) < right.eval (fun _ => 0))
  | .equal (left := left) (right := right) _ _, _ => .proposition (left.eval (fun _ => 0) = right.eval (fun _ => 0))
  | .arrow _ (resultSort := resultSort) _ domain codomain, assignment =>
      Finite.pi (domain.meaning assignment) resultSort (fun _ => codomain.meaning assignment)
  | .abstract (resultSort := resultSort) level codomain, assignment =>
      Finite.pi (Finite.Values.codeUniverse level) resultSort
        (fun parameter => codomain.meaning (assignment.extend level (Finite.Values.decode level parameter)))
  | .apply level body argument, assignment => body.meaning (assignment.extend level (argument.meaning assignment))

private theorem universeBinder (level : Fin 32) :
    LoanTyping.Binder env [] ctx false (.univ level.val) (universeSort level).native :=
  .intro (.univ level.isLt) (Or.inl (by intro different; cases different))

private theorem purePolicy {sort : SortTag} (allowed : if erased then sort = .prop else sort ≠ .prop) :
    LoanTyping.binderAllowed env erased domain sort := by
  cases erased with
  | false => exact .inl allowed
  | true => exact .inl (.inl allowed)

private theorem closedArithmetic (valid : ScalarExpr [] expr) :
    LoanTyping.HasType env [] ctx true expr.toTerm .u64 := by
  induction valid with
  | var slot => cases slot
  | literal bound => exact .natural bound
  | add _ _ first second => exact .uadd first second

/-- The semantic sort of a reconstructed code is justified by native
formation, with the actual code binder in the dependent codomain. -/
theorem Code.formed (wf : UnifiedProgram.EnvWellFormed env) (code : Code levels sort) :
    LoanTyping.HasType env [] (parameterContext levels) true code.syntax sort.native.term := by
  induction code with
  | @parameter levels index =>
      have found := universe_lookup levels.get index
      rw [universeContext_list] at found
      exact .var found (Or.inl rfl)
  | natural => exact .u64
  | proposition => exact .prop
  | universeCode level => exact .univ level.isLt
  | less left right => exact .lt (closedArithmetic left) (closedArithmetic right)
  | equal left right => exact .eq (closedArithmetic left) (closedArithmetic right)
  | @arrow domainSort levels resultSort erased allowed domain codomain domainTyped codomainTyped =>
      rw [Code.syntax,Finite.LevelSort.pi_native]
      exact .pi (.intro domainTyped (purePolicy allowed))
        (by simpa only [SortTag.rename_term] using codomainTyped.ghostWeaken wf domain.syntax erased)
  | abstract level codomain formed =>
      rw [Code.syntax,Finite.LevelSort.pi_native]
      exact .pi (universeBinder level) formed
  | @apply levels resultSort level body argument bodyTyped argumentTyped =>
      rw [Code.syntax,← SortTag.subst_term resultSort.native (single argument.syntax)]
      exact .app (.lam (universeBinder level) bodyTyped) argumentTyped (Or.inl rfl)

/-- The executable pure checker's chosen annotation agrees with the
reconstructed semantic sort by full RawValue conversion. -/
theorem Code.typing_agrees (wf : UnifiedProgram.EnvWellFormed env) (code : Code levels sort)
    (typed : LoanTyping.PureTyping.HasType env (parameterContext levels) code.syntax requested) :
    RawValue.Conv env sort.native.term requested :=
  (LoanTyping.PureTyping.HasType.native (code.formed wf)).unique wf typed

def Recognized (levels : List (Fin 32)) (term : Term) : Prop :=
  ∃ sort, ∃ code : Code levels sort, code.syntax = term

def NativeSort : LevelSort → Prop
  | .proposition => True
  | .type level => level.val < 33

private theorem piSort_native (left : NativeSort domainSort) (right : NativeSort resultSort) :
    NativeSort (domainSort.pi resultSort) := by
  cases domainSort <;> cases resultSort <;> simp_all [NativeSort,LevelSort.pi]
  omega

theorem Code.native_sort (code : Code levels sort) : NativeSort sort := by
  induction code with
  | parameter index => exact Nat.lt_trans (List.get _ index).isLt (by decide)
  | natural | proposition => exact (by decide : 0 < 33)
  | universeCode level => exact Nat.succ_lt_succ level.isLt
  | less | equal => trivial
  | arrow _ _ _ _ left right => exact piSort_native left right
  | abstract level _ result => exact piSort_native (Nat.succ_lt_succ level.isLt) result
  | apply _ _ _ result _ => exact result

/-- A proposition is represented by a value of Prop in Type0, while a
type code is represented at the successor of its exact native level. -/
def Reflected : {sort : LevelSort} → Universe sort → Prop
  | .proposition, code => ∃ value : Carrier Finite.propositionUniverse, .proposition value.down = code
  | .type level, code => ∃ native : Fin 33, native.val = level.val ∧
      ∃ value : Carrier (Finite.AdministrativeValues.codeUniverse native),
        HEq (Finite.AdministrativeValues.decode native value) code

private theorem reflect (native : NativeSort sort) (code : Universe sort) : Reflected code := by
  cases sort with
  | proposition =>
      cases code with
      | proposition truth => exact ⟨⟨truth⟩,rfl⟩
  | type level =>
      cases level with
      | mk level range =>
          let exactLevel : Fin 33 := ⟨level,native⟩
          exact ⟨exactLevel,rfl,Finite.AdministrativeValues.encode exactLevel code,
            heq_of_eq (Finite.AdministrativeValues.decode_encode exactLevel code)⟩

theorem Code.reflected (code : Code levels sort) (assignment : Assignment levels.get) :
    Reflected (code.meaning assignment) := reflect code.native_sort _

/-- Code formation and actual ghost typing yield a concrete semantic family
at the stored annotation. For a dependent Pi the family varies with its
decoded universe argument. -/
theorem fundamental (wf : UnifiedProgram.EnvWellFormed env)
    (typed : LoanTyping.PureTyping.HasType env (parameterContext levels) term requested) (recognized : Recognized levels term) :
    ∃ sort, ∃ code : Code levels sort, code.syntax = term ∧ RawValue.Conv env sort.native.term requested ∧
      ∀ assignment : Assignment levels.get, Reflected (code.meaning assignment) := by
  obtain ⟨sort,code,rfl⟩ := recognized
  exact ⟨sort,code,rfl,code.typing_agrees wf typed,code.reflected⟩

/-- The annotation is recovered from exactly the admitted version-6
declaration. No semantic typing or interpretation of the slot is supplied. -/
theorem checked_global_code {declaration : GlobalDeclaration} {index : Nat}
    (accepted : LoanTyping.PureMixedAdmission.checkBytes limits bytes = some env)
    (found : env.globals[index]? = some declaration) (recognized : Recognized [] declaration.value) :
    ∃ sort, ∃ code : Code [] sort, code.syntax = declaration.value ∧ RawValue.Conv env sort.native.term declaration.type ∧
      ∀ assignment : Assignment (List.get ([] : List (Fin 32))), Reflected (code.meaning assignment) := by
  obtain ⟨_,_,_,_,_,history,wf,_⟩ := LoanTyping.PureMixedAdmission.checkBytes_sound accepted
  exact fundamental wf (history.global_value_and_reference found).1 recognized

/-- A native code of any recognized type level, including a code whose sort
is administrative Type32, can be lifted to a value and decoded exactly. -/
theorem typed_code_value (wf : UnifiedProgram.EnvWellFormed env) (level : Fin 33)
    (code : Code levels (.type ⟨level.val,by omega⟩))
    (typed : LoanTyping.PureTyping.HasType env (parameterContext levels) code.syntax requested)
    (assignment : Assignment levels.get) :
    RawValue.Conv env (.univ level.val) requested ∧
      ∃ value : Carrier (Finite.AdministrativeValues.codeUniverse level),
        Finite.AdministrativeValues.decode level value = code.meaning assignment :=
  ⟨code.typing_agrees wf typed,Finite.AdministrativeValues.encode level (code.meaning assignment),
    Finite.AdministrativeValues.decode_encode level (code.meaning assignment)⟩

/-- Instantiating a semantic dependent product uses the same code as the
source type-level application, with no assumption about the argument code. -/
theorem Code.application_meaning (level : Fin 32) (body : Code (level :: levels) resultSort)
    (argument : Code levels (inputSort level)) (assignment : Assignment levels.get) :
    (Code.apply level body argument).meaning assignment =
      body.meaning (assignment.extend level (Finite.Values.decode level
        (Finite.Values.encode level (argument.meaning assignment)))) := by
  rw [Finite.Values.decode_encode]
  rfl

theorem Code.application_beta (wf : UnifiedProgram.EnvWellFormed env) (level : Fin 32)
    (body : Code (level :: levels) resultSort) (argument : Code levels (inputSort level)) :
    RawValue.Conv env (Code.apply level body argument).syntax (body.syntax.subst (single argument.syntax)) ∧
      LoanTyping.HasType env [] (parameterContext levels) true
        (body.syntax.subst (single argument.syntax)) resultSort.native.term := by
  refine ⟨.old (.old (.legacy (.beta false _ _ _))),?_⟩
  have formed := (body.formed wf).ghostInstantiate wf (argument.formed wf)
  simpa only [SortTag.subst_term] using formed

def bottom (level : Fin 32) : Code [] ((universeSort level).pi (inputSort level)) :=
  .abstract level (.parameter ⟨0,by simp⟩)

/-- The family of a genuinely dependent product can select an empty
carrier. In this model `∀ X : Type u, X` has no inhabitant at every native
input level, including the one whose product lies in administrative Type32. -/
theorem bottom_uninhabited (level : Fin 32) (assignment : Assignment (List.get ([] : List (Fin 32)))) :
    ¬ Nonempty (Carrier ((bottom level).meaning assignment)) := by
  intro inhabited
  let domain := Finite.Values.codeUniverse level
  let family := Finite.Values.decode level
  change Nonempty (Carrier (Finite.pi domain (inputSort level) family)) at inhabited
  obtain ⟨function⟩ := inhabited
  have applied := (Finite.piMeaning domain (inputSort level) family).app function
    (Finite.Values.encode level (Finite.Values.empty level))
  change Carrier (Finite.Values.decode level (Finite.Values.encode level (Finite.Values.empty level))) at applied
  rw [Finite.Values.decode_encode] at applied
  exact Finite.Values.empty_uninhabited level ⟨applied⟩

def quantifiedFalse {outer : List (Fin 32)} : List (Fin 32) → Code outer .proposition
  | [] => .less (left := .literal 0) (right := .literal 0) (.literal (by decide)) (.literal (by decide))
  | level :: levels => .abstract level (quantifiedFalse levels)

/-- Any number of mixed-level universe binders leaves a closed false
arithmetic proposition uninhabited. Each classifier supplies an actual
argument code, so universal quantification cannot hide the contradiction. -/
theorem quantified_false_uninhabited {outer : List (Fin 32)} (levels : List (Fin 32))
    (assignment : Assignment outer.get) :
    ¬ Nonempty (Carrier ((quantifiedFalse levels).meaning assignment)) := by
  induction levels generalizing outer with
  | nil =>
      intro inhabited
      change Nonempty (Carrier (.proposition (0 < 0))) at inhabited
      obtain ⟨value⟩ := inhabited
      exact Nat.lt_irrefl _ value.down.down
  | cons level levels ih =>
      intro inhabited
      let domain := Finite.Values.codeUniverse level
      let family := fun value => (quantifiedFalse (outer := level :: outer) levels).meaning
        (assignment.extend level (Finite.Values.decode level value))
      change Nonempty (Carrier (Finite.pi domain .proposition family)) at inhabited
      obtain ⟨function⟩ := inhabited
      let witness := Finite.Values.encode level (Finite.Values.empty level)
      exact ih (assignment.extend level (Finite.Values.decode level witness))
        ⟨(Finite.piMeaning domain .proposition family).app function witness⟩

/-- Exact byte admission of the proposition as a code recovers its original
Prop annotation and the empty carrier of the code it denotes. -/
theorem checked_global_quantified_false_code {declaration : GlobalDeclaration} {index : Nat}
    (accepted : LoanTyping.PureMixedAdmission.checkBytes limits bytes = some env)
    (found : env.globals[index]? = some declaration) (levels : List (Fin 32))
    (source : declaration.value = (quantifiedFalse (outer := []) levels).syntax) :
    RawValue.Conv env .prop declaration.type ∧
      ∀ assignment : Assignment (List.get ([] : List (Fin 32))),
        ¬ Nonempty (Carrier ((quantifiedFalse levels).meaning assignment)) := by
  obtain ⟨_,_,_,_,_,history,wf,_⟩ := LoanTyping.PureMixedAdmission.checkBytes_sound accepted
  have original := (history.global_value_and_reference found).1
  rw [source] at original
  exact ⟨(quantifiedFalse (outer := []) levels).typing_agrees wf original,quantified_false_uninhabited levels⟩

end Jihoo.NativeKernel.Environment.Semantics.MultiUniverse.DependentCodes
