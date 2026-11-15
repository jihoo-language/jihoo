import Jihoo.NativeFamilyIotaResiduals

/-! Every actual family redex survives arithmetic quotient exposure with an
actual forward arithmetic path and a genuine residual root. Raw metadata is
unrestricted; additive zero wrappers and permutations are handled explicitly. -/
namespace Jihoo.NativeKernel.Environment.FamilyIota.Extended
open NativeKernel.Conversion (ListRel)

private theorem related_length (related : ListRel R xs ys) : xs.length = ys.length := by
  induction related with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

private theorem split_append (related : ListRel R (xs ++ rest) ys) :
    ∃ frontTerms suffix,ys = frontTerms ++ suffix ∧ ListRel R xs frontTerms ∧ ListRel R rest suffix := by
  induction xs generalizing ys with
  | nil => exact ⟨[],ys,rfl,.nil,related⟩
  | cons x xs ih => cases related with
    | cons head tail =>
      obtain ⟨frontTerms,suffix,rfl,front,last⟩ := ih tail
      exact ⟨_::frontTerms,suffix,rfl,.cons head front,last⟩

private theorem one (related : ListRel R [term] terms) :
    ∃ result,terms = [result] ∧ R term result := by
  cases related with
  | cons head tail => cases tail;exact ⟨_,rfl,head⟩

private theorem layout (related : ListRel R (motive :: (cases ++ [scrutinee])) children) :
    ∃ motive' cases' scrutinee',children = motive' :: (cases' ++ [scrutinee']) ∧
      R motive motive' ∧ ListRel R cases cases' ∧ R scrutinee scrutinee' := by
  cases related with
  | cons head tail =>
    obtain ⟨frontTerms,suffix,rfl,front,last⟩ := split_append tail
    obtain ⟨scrutinee',rfl,scrut⟩ := one last
    exact ⟨_,frontTerms,scrutinee',rfl,head,front,scrut⟩

private theorem arithmetic_congruence : Congruence ACU.ArithmeticRed :=
  ⟨by intro op ordinary xs ys related;exact .node op related⟩

/-- Arithmetic may add/remove outer additive wrappers around a redex. The
conclusion gives an actual forward path exposing the residual and an actual
forward path on the contracted result, with no equality/normalization oracle. -/
theorem arithmetic_root_residual (step : Root env term result) (arithmetic : ACU.Arithmetic term other) :
    ∃ exposed result',ACU.ArithmeticRed other exposed ∧ Root env exposed result' ∧ ACU.ArithmeticRed result result' := by
  cases step with
  | @elim family entry constructor signature cases branch motive values found sigFound selected count fields =>
    obtain ⟨children,exposure,changes⟩ := arithmetic.forward_node (by rfl)
    obtain ⟨motive',cases',scrutinee',rfl,motiveRelated,casesRelated,scrutineeRelated⟩ := layout changes
    obtain ⟨values',rfl,valuesRelated⟩ := scrutineeRelated.rigid_shape (by rfl) rfl
    have exposed : ACU.ArithmeticRed other
        (elimTerm family motive' cases' (.node (.con family constructor values'.length) values')) := by
      simpa only [elimTerm,related_length casesRelated,related_length valuesRelated] using exposure
    obtain ⟨branch',selected',root,output⟩ := elim_residual arithmetic_congruence found sigFound selected count fields
      motiveRelated casesRelated valuesRelated
    exact ⟨_,_,exposed,root,output⟩
  | @caseOf family entry constructor signature cases branch motive values found data sigFound selected count fields =>
    obtain ⟨children,exposure,changes⟩ := arithmetic.forward_node (by rfl)
    obtain ⟨motive',cases',scrutinee',rfl,motiveRelated,casesRelated,scrutineeRelated⟩ := layout changes
    obtain ⟨values',rfl,valuesRelated⟩ := scrutineeRelated.rigid_shape (by rfl) rfl
    have exposed : ACU.ArithmeticRed other
        (caseTerm family motive' cases' (.node (.con family constructor values'.length) values')) := by
      simpa only [caseTerm,related_length casesRelated,related_length valuesRelated] using exposure
    obtain ⟨branch',selected',root,output⟩ := case_residual (motive' := motive') arithmetic_congruence found data sigFound selected count fields
      casesRelated valuesRelated
    exact ⟨_,_,exposed,root,output⟩
  | @view family entry constructor signature cases branch plans recursion motive values found boxed sigFound selected count fields bound planned =>
    obtain ⟨children,exposure,changes⟩ := arithmetic.forward_node (by rfl)
    obtain ⟨motive',cases',scrutinee',rfl,motiveRelated,casesRelated,scrutineeRelated⟩ := layout changes
    obtain ⟨borrowed,rfl,borrowRelated⟩ := scrutineeRelated.rigid_shape (by rfl) rfl
    obtain ⟨constructor',rfl,constructorRelated⟩ := one borrowRelated
    obtain ⟨values',rfl,valuesRelated⟩ := constructorRelated.rigid_shape (by rfl) rfl
    have exposed : ACU.ArithmeticRed other
        (viewTerm recursion family motive' cases' (.borrow (.node (.con family constructor values'.length) values'))) := by
      simpa only [viewTerm,related_length casesRelated,related_length valuesRelated] using exposure
    obtain ⟨branch',selected',root,output⟩ := view_residual arithmetic_congruence found boxed sigFound selected count fields bound planned
      motiveRelated casesRelated valuesRelated
    exact ⟨_,_,exposed,root,output⟩
  | drop family owner rest =>
    obtain ⟨children,exposure,changes⟩ := arithmetic.forward_node (by rfl)
    cases changes with
    | cons ownerRelated tail => cases tail with
      | cons restRelated tail => cases tail;exact ⟨_,_,exposure,.drop _ _ _,restRelated⟩

end Jihoo.NativeKernel.Environment.FamilyIota.Extended
