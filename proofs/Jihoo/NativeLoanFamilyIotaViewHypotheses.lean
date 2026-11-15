import Jihoo.NativeLoanFamilyIotaViewRecursiveTyping

/-! Actual recursive hypothesis applications consume the generated telescope
with exact binder instantiation, preserving the dependent constructor result. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.FamilyIota
open _root_.Jihoo.NativeKernel.Environment.FamilyIota
open _root_.Jihoo.NativeKernel.Environment.LoanTyping.Conversion
set_option linter.unusedSimpArgs false

private theorem fieldSubstitution_singleton (value : Term) : fieldSubstitution [value] = single value := by
  funext x
  simp only [fieldSubstitution,List.length_nil,liftSub,Term.subst_id]

theorem fieldSubstitution_snoc (values : List Term) (value : Term) :
    fieldSubstitution (values ++ [value]) = extendField (fieldSubstitution values) value := by
  rw [fieldSubstitution_append,fieldSubstitution_singleton]
  exact lift_single_extend _ _

private theorem liftSub_offset (locals : Nat) (σ : Nat → Term) (x : Nat) :
    liftSub locals σ (x+locals) = (σ x).rename (fun i => i+locals) := by
  induction locals with
  | zero => change σ x = (σ x).rename id;exact (Term.rename_id _).symm
  | succ locals ih =>
    change (liftSub locals σ (x+locals)).rename Nat.succ = (σ x).rename (fun i => i+(locals+1))
    rw [ih,Term.rename_comp]
    rfl

theorem fieldSubstitution_append_shift (fields hypotheses : List Term) :
    (fun x => fieldSubstitution (fields ++ hypotheses) (x+hypotheses.length)) = fieldSubstitution fields := by
  funext x
  rw [fieldSubstitution_append]
  simp only
  rw [liftSub_offset,fieldSubstitution_shift]

/-- The generated IH domain reduces to the motive at the actual selected
borrowed field, independently of all earlier recursive results. -/
theorem viewHypothesisType_instantiation (found : fields[position]? = some argument) (previous : List Term) :
    (viewHypothesisType fields.length motive dependent position previous.length).subst
      (fieldSubstitution (fields ++ previous)) = viewResult dependent motive argument := by
  have shift := fieldSubstitution_shift (fields ++ previous) motive
  simp only [List.length_append] at shift
  have selected : (fields ++ previous)[position]? = some argument := by
    have bound := (List.getElem?_eq_some_iff.mp found).1
    simp only [List.getElem?_append,bound,↓reduceIte,found]
  have selectedValue := fieldSubstitution_selected selected
  simp only [List.length_append] at selectedValue
  unfold viewHypothesisType viewResult
  cases dependent with
  | false => simpa only [Bool.false_eq_true,ite_false,Nat.add_assoc] using shift
  | true =>
    simp only [ite_true,Term.subst,substArgs,Op.binders,liftSub,Nat.add_assoc,shift,selectedValue]

def hypothesisArguments (positions : List Nat) (fields : List Term) (make : Term → Term) : List Term :=
  positions.filterMap fun position => fields[position]?.map make

/-- Each premise is an independently typed actual recursive call. There is no
premise about the selected branch's output type or about iota preservation. -/
theorem apply_view_hypotheses (positions : List Nat) (previous fields : List Term) (make : Term → Term)
    (hypotheses : ∀ position ∈ positions,∃ argument,fields[position]? = some argument ∧
      HasType env [] ctx true (make argument) (viewResult dependent motive argument))
    (typed : HasType env [] ctx true function
      ((viewHypothesisTelescope fields.length previous.length positions motive dependent body).subst
        (fieldSubstitution (fields ++ previous)))) :
    HasType env [] ctx true (applications function (hypothesisArguments positions fields make))
      (body.subst (fieldSubstitution (fields ++ (previous ++ hypothesisArguments positions fields make)))) := by
  induction positions generalizing previous function with
  | nil => simpa only [hypothesisArguments,List.filterMap_nil,List.append_nil,viewHypothesisTelescope,
      List.zipIdx_nil,List.foldr_nil,applications,List.foldl_nil] using typed
  | cons position positions ih =>
    obtain ⟨argument,found,hypothesis⟩ := hypotheses position (by simp)
    have tailHypotheses : ∀ p ∈ positions,∃ arg,fields[p]? = some arg ∧
        HasType env [] ctx true (make arg) (viewResult dependent motive arg) :=
      fun p hp => hypotheses p (by simp [hp])
    simp only [viewHypothesisTelescope,List.zipIdx_cons,List.foldr_cons,Term.subst,substArgs,Op.binders,liftSub] at typed
    have applied := HasType.app typed
      (by simpa only [Bool.true_or,viewHypothesisType_instantiation found previous] using hypothesis) (Or.inl rfl)
    rw [Term.subst_comp] at applied
    change HasType env [] ctx true _
      ((viewHypothesisTelescope fields.length (previous.length+1) positions motive dependent body).subst
        (fun x => (liftSubOne (fieldSubstitution (fields ++ previous)) x).subst (single (make argument)))) at applied
    rw [lift_single_extend,← fieldSubstitution_snoc,List.append_assoc] at applied
    have next := ih (previous ++ [make argument]) tailHypotheses
      (by simpa only [List.length_append,List.length_singleton] using applied)
    simpa only [hypothesisArguments,List.filterMap_cons,found,Option.map_some,
      List.append_assoc,List.singleton_append,applications,List.foldl_cons] using next

/-- Recursive-result binders shift every occurrence in the final View result. -/
theorem viewCaseResult_hypotheses_shift (family constructor fields q : Nat) (ps : List Term)
    (motive : Term) (borrowed : List Bool) (dependent : Bool) :
    viewCaseResult family constructor fields q ps motive borrowed dependent =
      (viewCaseResult family constructor fields 0 ps motive borrowed dependent).rename (fun x => x+q) := by
  unfold viewCaseResult
  cases dependent with
  | false => simp only [Bool.false_eq_true,ite_false,Nat.add_zero,Term.rename_comp,Nat.add_assoc]
  | true =>
    simp only [ite_true,Nat.add_zero,Term.rename,renameArgs,Op.binders,liftRenaming,renameArgs_con,
      List.map_append,List.map_map,Term.rename_comp,Function.comp_def,Nat.add_assoc,
      List.length_append,List.length_map,List.length_range]
    congr 3
    apply congrArg (List.append (ps.map (Term.rename (fun x => x+(fields+q)))))
    apply List.map_congr_left
    intro j member
    split <;> simp only [Term.rename,renameArgs,Op.binders,liftRenaming]

/-- Recursive IH values disappear from the final constructor result by proved
binder cancellation, while the actual fields retain Deref/Borrow conversion. -/
theorem viewCaseResult_recursive_instantiation (closed : Conversion.Closed env)
    (size : values.length = plans.length) (hypotheses : List Term) :
    Conversion.Conv env
      ((viewCaseResult family constructor plans.length hypotheses.length ps motive
        (plans.map ViewFieldPlan.borrowed) dependent).subst
        (fieldSubstitution (viewArguments plans values ++ hypotheses)))
      (viewResult dependent motive (.borrow (.node (.con family constructor (ps ++ values).length) (ps ++ values)))) := by
  rw [viewCaseResult_hypotheses_shift,Term.subst_rename,fieldSubstitution_append_shift]
  exact viewCaseResult_instantiation closed size

end Jihoo.NativeKernel.Environment.LoanTyping.FamilyIota
