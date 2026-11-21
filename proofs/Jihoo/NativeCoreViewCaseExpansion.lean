import Jihoo.NativeCoreViewCaseType

/-! Transparency commutes with every part of the View case result.
The original motive is weakened, and the result keeps the constructor
fields in their original de Bruijn order. -/
namespace Jihoo.NativeKernel.NativeCoreViewCaseExpansion

open Environment
open EnvironmentDelta (expand expandArgs)

private theorem expanded_shifted (admissible : EnvironmentDelta.Admissible env) (σ : Nat → Nat)
    (terms : List Term) : expandArgs env (terms.map (Term.rename σ)) = (expandArgs env terms).map (Term.rename σ) := by
  simp only [EnvironmentDelta.expandArgs_map,List.map_map]
  apply List.map_congr_left
  intro term _
  exact EnvironmentDelta.expand_renaming admissible term σ

private def fieldArguments (fields hypotheses : Nat) (borrowed : List Bool) : List Term :=
  (List.range fields).map (fun j =>
    let field := Term.var (fields-1-j+hypotheses)
    if borrowed[j]?.getD false then Term.deref field else field)

private theorem fieldArguments_expanded (fields hypotheses : Nat) (borrowed : List Bool) :
    expandArgs env (fieldArguments fields hypotheses borrowed) = fieldArguments fields hypotheses borrowed := by
  simp only [fieldArguments,EnvironmentDelta.expandArgs_map,List.map_map]
  apply List.map_congr_left
  intro index _
  cases flag : borrowed[index]?.getD false <;> simp [flag,expand,expandArgs,Term.deref]

theorem viewCaseResult_expand (admissible : EnvironmentDelta.Admissible env) (ps : List Term) (motive : Term) :
    expand env (viewCaseResult family constructor fields hypotheses ps motive borrowed dependent) =
      viewCaseResult family constructor fields hypotheses (expandArgs env ps) (expand env motive) borrowed dependent := by
  let σ := fun x => x+fields+hypotheses
  let args := ps.map (Term.rename σ) ++ fieldArguments fields hypotheses borrowed
  let newArgs := (expandArgs env ps).map (Term.rename σ) ++ fieldArguments fields hypotheses borrowed
  have argsExpanded : expandArgs env args = newArgs := by
    have append_expanded (xs ys : List Term) :
        expandArgs env (xs ++ ys) = expandArgs env xs ++ expandArgs env ys := by
      simp only [EnvironmentDelta.expandArgs_map,List.map_append]
    simp only [args,newArgs,append_expanded,expanded_shifted admissible σ,fieldArguments_expanded]
  have arity : args.length = newArgs.length := by
    rw [←argsExpanded,EnvironmentDelta.expandArgs_map,List.length_map]
  cases dependent
  · exact EnvironmentDelta.expand_renaming admissible motive σ
  · change expand env (.app (motive.rename σ) (.borrow (.node (.con family constructor args.length) args))) =
      .app ((expand env motive).rename σ) (.borrow (.node (.con family constructor newArgs.length) newArgs))
    simp only [Term.app,Term.borrow,EnvironmentDelta.expand_node_cons,expandArgs]
    have conExpanded : expand env (.node (.con family constructor args.length) args) =
        .node (.con family constructor args.length) (expandArgs env args) := by
      cases args <;> simp only [expand,expandArgs,EnvironmentDelta.expand_node_cons]
    rw [EnvironmentDelta.expand_renaming admissible,conExpanded,argsExpanded,arity]

private theorem viewHypothesisType_expand (admissible : EnvironmentDelta.Admissible env) (motive : Term) :
    expand env (viewHypothesisType fields motive dependent position offset) =
      viewHypothesisType fields (expand env motive) dependent position offset := by
  cases dependent <;>
    simp only [viewHypothesisType,Bool.false_eq_true,ite_false,ite_true,Term.app,EnvironmentDelta.expand_node_cons,expandArgs,
      EnvironmentDelta.expand_renaming admissible,expand]

theorem viewHypothesisTelescope_expand (admissible : EnvironmentDelta.Admissible env) (positions : List Nat)
    (motive result : Term) :
    expand env (viewHypothesisTelescope fields offset positions motive dependent result) =
      viewHypothesisTelescope fields offset positions (expand env motive) dependent (expand env result) := by
  induction positions generalizing offset with
  | nil => rfl
  | cons position tail ih =>
    change expand env (.pi false (viewHypothesisType fields motive dependent position offset)
        (viewHypothesisTelescope fields (offset+1) tail motive dependent result)) =
      .pi false (viewHypothesisType fields (expand env motive) dependent position offset)
        (viewHypothesisTelescope fields (offset+1) tail (expand env motive) dependent (expand env result))
    have piExpanded : expand env (.pi false (viewHypothesisType fields motive dependent position offset)
          (viewHypothesisTelescope fields (offset+1) tail motive dependent result)) =
        .pi false (expand env (viewHypothesisType fields motive dependent position offset))
          (expand env (viewHypothesisTelescope fields (offset+1) tail motive dependent result)) := by
      simp only [Term.pi,EnvironmentDelta.expand_node_cons,expandArgs]
    rw [piExpanded,viewHypothesisType_expand admissible,ih]


end Jihoo.NativeKernel.NativeCoreViewCaseExpansion
