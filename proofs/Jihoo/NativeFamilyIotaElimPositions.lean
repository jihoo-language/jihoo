import Jihoo.NativeFamilyIotaElimInstantiation

/-! The generated recursive telescope and executable Elim calls have the same
ordered actual fields, including elimination of nonrecursive leading parameters. -/
namespace Jihoo.NativeKernel.Environment.FamilyIota
set_option linter.unusedSimpArgs false

private theorem filterMap_congr (xs : List α) (same : ∀ x ∈ xs,f x = g x) : xs.filterMap f = xs.filterMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filterMap_cons,same x (by simp)]
    rw [ih (fun y hy => same y (by simp [hy]))]

private theorem zip_indexed {values : List Term} {fields : List Field} (size : values.length = fields.length) :
    fields.zip values = fields.zipIdx.map (fun (field,j) => (field,(values[j]?).getD (Term.natural 0))) := by
  apply List.ext_getElem
  · simp only [List.length_zip,size,Nat.min_self,List.length_map,List.length_zipIdx]
  · intro j leftBound rightBound
    have fieldBound : j < fields.length := by simpa only [List.length_map,List.length_zipIdx] using rightBound
    have valueBound : j < values.length := by omega
    simp only [List.getElem_zip,List.getElem_map,List.getElem_zipIdx,Nat.zero_add,
      List.getElem?_eq_getElem valueBound,Option.getD_some]

theorem instantiatedRecursive_selected (member : pair ∈ instantiatedRecursive depth ps fields) :
    ∃ position indices field,pair = (position,indices.map (Term.subst (parameterAt depth position ps))) ∧
      fields[position]? = some field ∧ field.recursive = some indices := by
  obtain ⟨⟨position,indices⟩,inRecursive,chosen⟩ := List.mem_map.mp member
  obtain ⟨⟨field,j⟩,inFields,selected⟩ := List.mem_filterMap.mp inRecursive
  have found := List.mk_mem_zipIdx_iff_getElem?.mp inFields
  cases recursive : field.recursive with
  | none => simp only [recursive,Option.map_none] at selected;contradiction
  | some recursiveIndices =>
    simp only [recursive,Option.map_some,Option.some.injEq,Prod.mk.injEq] at selected
    obtain ⟨rfl,rfl⟩ := selected
    exact ⟨j,recursiveIndices,field,chosen.symm,found,recursive⟩

theorem elimHypotheses_positions (size : values.length = fields.length) :
    dataHypothesisArguments (instantiatedRecursive depth ps fields) values (elimTerm family motive cases) =
      elimHypotheses family motive cases fields values := by
  unfold dataHypothesisArguments instantiatedRecursive recursiveFields elimHypotheses
  simp only [List.filterMap_map,List.filterMap_filterMap]
  rw [zip_indexed size,List.filterMap_map]
  apply filterMap_congr
  intro pair member
  rcases pair with ⟨field,j⟩
  have fieldFound := List.mk_mem_zipIdx_iff_getElem?.mp member
  have fieldBound := (List.getElem?_eq_some_iff.mp fieldFound).1
  have valueBound : j < values.length := by omega
  have valueFound := List.getElem?_eq_getElem valueBound
  cases recursive : field.recursive with
  | none => simp only [recursive,Option.map_none,Option.bind_none,Option.isSome_none,Bool.false_eq_true,ite_false,Function.comp_apply]
  | some indices => simp only [recursive,Option.map_some,Option.bind_some,Option.isSome_some,ite_true,
      Function.comp_apply,valueFound,Option.getD_some]

theorem elimHypotheses_drop_parameters {fields : List Field} {values : List Term}
    (size : values.length = fields.length)
    (parameters : ∀ j < params,∀ field,fields[j]? = some field → field.recursive = none) :
    elimHypotheses family motive cases fields values =
      elimHypotheses family motive cases (fields.drop params) (values.drop params) := by
  induction params generalizing fields values with
  | zero => rfl
  | succ params ih =>
    cases fields with
    | nil => have empty : values = [] := List.length_eq_zero_iff.mp size;subst values;rfl
    | cons field fields => cases values with
      | nil => simp at size
      | cons value values =>
        have head := parameters 0 (by omega) field rfl
        have tail : ∀ j < params,∀ selected,fields[j]? = some selected → selected.recursive = none := by
          intro j inside selected found
          exact parameters (j+1) (by omega) selected found
        simpa only [elimHypotheses,List.zip_cons_cons,List.filterMap_cons,head,Option.isSome_none,
          Bool.false_eq_true,ite_false,List.drop_succ_cons] using ih (Nat.succ.inj size) tail

end Jihoo.NativeKernel.Environment.FamilyIota
