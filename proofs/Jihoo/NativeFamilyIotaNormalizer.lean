import Jihoo.NativeFamilyIotaConversion
import Jihoo.NativeEnvironmentConversionNormalizer
import Jihoo.NativeFamilyIotaComputationSoundness

/-! Bounded executable search using genuine old delta/ACU forward reductions
and actual raw family contractions. Every success has a finite forward witness;
no confluence or normal-form completeness is presumed. -/
namespace Jihoo.NativeKernel.Environment.FamilyIota.Extended
set_option linter.unusedSimpArgs false

/-- Finite search. The explicit size guard also precedes contraction so raw
large metadata/branch duplication cannot enter an unbounded contraction pass. -/
def normalize? (env : Environment) (budget : Nat) : Nat → Term → Option Term
  | 0,_ => none
  | fuel+1,term => do
    if NativeKernel.Conversion.treeSize term > budget then none else
    let prior ← EnvironmentDelta.Basis.normalize? env (fuel+1) term
    let rebuilt ← match prior with
      | .var x => some (.var x)
      | .node op children => do
        let next ← children.mapM (normalize? env budget fuel)
        some (.node op next)
    let folded ← EnvironmentDelta.Basis.normalize? env (fuel+1) rebuilt
    if folded != rebuilt then normalize? env budget fuel folded else
    if 4*(NativeKernel.Conversion.treeSize folded+1)^2 > budget then none else
    match contract env folded with
    | none => some folded
    | some result => normalize? env budget fuel result

private theorem mapM_forward (normalizer : Term → Option Term)
    (sound : ∀ term result,normalizer term = some result → Forward env term result)
    (accepted : children.mapM normalizer = some results) :
    NativeKernel.Conversion.ListRel (Forward env) children results := by
  induction children generalizing results with
  | nil => simp only [List.mapM_nil,pure,Option.some.injEq] at accepted;subst results;exact .nil
  | cons child children ih =>
    simp only [List.mapM_cons] at accepted
    cases head : normalizer child with
    | none => simp [head] at accepted
    | some result =>
      simp only [head,Bind.bind,Option.bind] at accepted
      cases tail : children.mapM normalizer with
      | none => simp [tail] at accepted
      | some rest =>
        simp only [tail,Bind.bind,Option.bind,pure,Option.some.injEq] at accepted
        subst results
        exact .cons (sound _ _ head) (ih tail)

/-- All successful enlarged executable search produces actual finite forward
computation, including reductions beneath arbitrary binder/type syntax. -/
theorem normalize?_forward (accepted : normalize? env budget fuel term = some result) :
    Forward env term result := by
  induction fuel generalizing term result with
  | zero => simp [normalize?] at accepted
  | succ fuel ih =>
    unfold normalize? at accepted
    split at accepted
    · contradiction
    · cases priorFound : EnvironmentDelta.Basis.normalize? env (fuel+1) term with
      | none => simp [priorFound] at accepted
      | some prior =>
        simp only [priorFound,Bind.bind,Option.bind] at accepted
        have original : Forward env term prior := .old (EnvironmentDelta.Basis.normalize?_forward priorFound)
        have finish : ∀ rebuilt,
            (do
              let folded ← EnvironmentDelta.Basis.normalize? env (fuel+1) rebuilt
              if folded != rebuilt then normalize? env budget fuel folded else
              if 4*(NativeKernel.Conversion.treeSize folded+1)^2 > budget then none else
              match contract env folded with
              | none => some folded
              | some next => normalize? env budget fuel next) = some result → Forward env rebuilt result := by
          intro rebuilt finished
          cases foldedFound : EnvironmentDelta.Basis.normalize? env (fuel+1) rebuilt with
          | none => simp [foldedFound] at finished
          | some folded =>
            simp only [foldedFound,Bind.bind,Option.bind] at finished
            have foldedPath : Forward env rebuilt folded := .old (EnvironmentDelta.Basis.normalize?_forward foldedFound)
            split at finished
            · exact foldedPath.trans (ih finished)
            · split at finished
              · contradiction
              · cases contracted : contract env folded with
                | none => simp only [contracted,Option.some.injEq] at finished;subst result;exact foldedPath
                | some next =>
                  simp only [contracted] at finished
                  exact foldedPath.trans ((Forward.iota (contract_sound contracted)).trans (ih finished))
        cases prior with
        | var x =>
          simp only [Bind.bind,Option.bind] at accepted
          exact original.trans (finish _ accepted)
        | node op children =>
          cases childrenFound : children.mapM (normalize? env budget fuel) with
          | none => simp [childrenFound] at accepted
          | some next =>
            simp only [childrenFound,Bind.bind,Option.bind] at accepted
            exact original.trans ((Forward.node op (mapM_forward _ (fun _ _ found => ih found) childrenFound)).trans
              (finish _ accepted))

theorem normalize?_sound (accepted : normalize? env budget fuel term = some result) : Conv env term result :=
  (normalize?_forward accepted).toConv

def equal (env : Environment) (budget fuel : Nat) (first second : Term) : Bool :=
  match normalize? env budget fuel first,normalize? env budget fuel second with
  | some left,some right => left == right
  | _,_ => false

theorem equal_common_reduct (accepted : equal env budget fuel first second = true) :
    ∃ common,Forward env first common ∧ Forward env second common := by
  unfold equal at accepted
  cases left : normalize? env budget fuel first with
  | none => simp [left] at accepted
  | some firstResult =>
    cases right : normalize? env budget fuel second with
    | none => simp [left,right] at accepted
    | some secondResult =>
      simp only [left,right,beq_iff_eq] at accepted
      subst secondResult
      exact ⟨firstResult,normalize?_forward left,normalize?_forward right⟩

theorem equal_sound (accepted : equal env budget fuel first second = true) : Conv env first second := by
  obtain ⟨common,left,right⟩ := equal_common_reduct accepted
  exact Conv.ofForwardJoin left right

end Jihoo.NativeKernel.Environment.FamilyIota.Extended
