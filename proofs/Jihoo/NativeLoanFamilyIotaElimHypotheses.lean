import Jihoo.NativeLoanFamilyIotaElimTyping
import Jihoo.NativeLoanFamilyIotaViewHypotheses

/-! Exact original indexed IH instantiation and actual branch application. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.FamilyIota
open _root_.Jihoo.NativeKernel.Environment.FamilyIota
open _root_.Jihoo.NativeKernel.Environment.LoanTyping.Conversion
set_option linter.unusedSimpArgs false

theorem fieldSubstitution_prefix_shift (bound : position ≤ fields.length) (previous : List Term) (term : Term) :
    (term.rename (fun x => x+(fields.length+previous.length-position))).subst
      (fieldSubstitution (fields ++ previous)) = term.subst (fieldSubstitution (fields.take position)) := by
  have arranged : fields ++ previous = fields.take position ++ (fields.drop position ++ previous) := by
    rw [← List.append_assoc,List.take_append_drop]
  have count : fields.length+previous.length-position = (fields.drop position ++ previous).length := by
    simp only [List.length_append,List.length_drop]
    omega
  rw [arranged,count,Term.subst_rename,fieldSubstitution_append_shift]

theorem dataHypothesisType_instantiation {pair : Nat × List Term}
    (found : fields[pair.1]? = some argument) (previous : List Term) :
    (dataHypothesisType params fields.length motive pair previous.length).subst
      (fieldSubstitution (fields ++ previous)) =
      .app (applications motive ((pair.2.map (Term.subst (fieldSubstitution (fields.take pair.1)))).drop params)) argument := by
  have bound := (List.getElem?_eq_some_iff.mp found).1
  have shift := fieldSubstitution_shift (fields ++ previous) motive
  simp only [List.length_append] at shift
  have selected : (fields ++ previous)[pair.1]? = some argument := by
    simp only [List.getElem?_append,bound,↓reduceIte,found]
  have selectedValue := fieldSubstitution_selected selected
  simp only [List.length_append] at selectedValue
  have indexEq : fields.length-1-pair.1+previous.length = fields.length+previous.length-1-pair.1 := by omega
  unfold dataHypothesisType
  simp only [Term.subst,substArgs,Op.binders,liftSub,applications_subst,Nat.add_assoc,shift,indexEq,selectedValue]
  congr 2
  rw [← List.map_drop,List.map_map]
  apply congrArg (applications motive)
  apply List.map_congr_left
  intro term member
  exact fieldSubstitution_prefix_shift (Nat.le_of_lt bound) previous term

def dataHypothesisArguments (recursive : List (Nat × List Term)) (fields : List Term) (make : Term → Term) : List Term :=
  recursive.filterMap fun pair => fields[pair.1]?.map make

/-- Actual indexed recursive calls consume exactly the authentic generated IH
binder types, without any output-typing or normalization premise. -/
theorem apply_data_hypotheses (recursive : List (Nat × List Term)) (previous fields : List Term) (make : Term → Term)
    (hypotheses : ∀ pair ∈ recursive,∃ argument,fields[pair.1]? = some argument ∧
      HasType env [] ctx true (make argument)
        (.app (applications motive ((pair.2.map (Term.subst (fieldSubstitution (fields.take pair.1)))).drop params)) argument))
    (typed : HasType env [] ctx true function
      ((dataHypothesisTelescope params fields.length previous.length recursive proof motive body).subst
        (fieldSubstitution (fields ++ previous)))) :
    HasType env [] ctx true (applications function (dataHypothesisArguments recursive fields make))
      (body.subst (fieldSubstitution (fields ++ (previous ++ dataHypothesisArguments recursive fields make)))) := by
  induction recursive generalizing previous function with
  | nil => simpa only [dataHypothesisArguments,List.filterMap_nil,List.append_nil,dataHypothesisTelescope,
      List.zipIdx_nil,List.foldr_nil,applications,List.foldl_nil] using typed
  | cons pair recursive ih =>
    obtain ⟨argument,found,hypothesis⟩ := hypotheses pair (by simp)
    have tailHypotheses : ∀ p ∈ recursive,∃ arg,fields[p.1]? = some arg ∧
        HasType env [] ctx true (make arg)
          (.app (applications motive ((p.2.map (Term.subst (fieldSubstitution (fields.take p.1)))).drop params)) arg) :=
      fun p hp => hypotheses p (by simp [hp])
    simp only [dataHypothesisTelescope,List.zipIdx_cons,List.foldr_cons,Term.subst,substArgs,Op.binders,liftSub] at typed
    have applied := HasType.app typed
      (by simpa only [Bool.true_or,dataHypothesisType_instantiation found previous] using hypothesis) (Or.inl rfl)
    rw [Term.subst_comp] at applied
    change HasType env [] ctx true _
      ((dataHypothesisTelescope params fields.length (previous.length+1) recursive proof motive body).subst
        (fun x => (liftSubOne (fieldSubstitution (fields ++ previous)) x).subst (single (make argument)))) at applied
    rw [lift_single_extend,← fieldSubstitution_snoc,List.append_assoc] at applied
    have next := ih (previous ++ [make argument]) tailHypotheses
      (by simpa only [List.length_append,List.length_singleton] using applied)
    simpa only [dataHypothesisArguments,List.filterMap_cons,found,Option.map_some,
      List.append_assoc,List.singleton_append,applications,List.foldl_cons] using next

theorem dataHypothesisArguments_length
    (bounds : ∀ pair ∈ recursive,∃ argument,fields[pair.1]? = some argument) :
    (dataHypothesisArguments recursive fields make).length = recursive.length := by
  induction recursive with
  | nil => rfl
  | cons pair recursive ih =>
    obtain ⟨argument,found⟩ := bounds pair (by simp)
    have tailBounds : ∀ p ∈ recursive,∃ a,fields[p.1]? = some a := fun p hp => bounds p (by simp [hp])
    simp only [dataHypothesisArguments,List.filterMap_cons,found,Option.map_some,List.length_cons]
    exact congrArg Nat.succ (ih tailBounds)

/-- IH-result binders only shift the final constructor result. -/
theorem dataCaseResult_hypotheses_shift (family constructor params fields q : Nat) (ps : List Term)
    (motive : Term) (indices : List Term) :
    dataCaseResult family constructor params fields q ps motive indices =
      (dataCaseResult family constructor params fields 0 ps motive indices).rename (fun x => x+q) := by
  unfold dataCaseResult
  simp only [Nat.add_zero,Term.rename,renameArgs,Op.binders,liftRenaming,renameArgs_con,
    List.map_append,List.map_map,Term.rename_comp,Function.comp_def,Nat.add_assoc,
    List.length_append,List.length_map,List.length_range,applications_rename]

end Jihoo.NativeKernel.Environment.LoanTyping.FamilyIota
