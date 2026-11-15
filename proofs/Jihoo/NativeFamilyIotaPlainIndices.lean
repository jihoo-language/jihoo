import Jihoo.NativePlainIndexForward

/-! Genuine family contraction preserves representation with independently
typed U64 holes. Metadata selects fields; every output term comes from source
motive, cases and constructor values. -/
namespace Jihoo.NativeKernel.Environment.Representation
open FamilyIota
set_option linter.unusedSimpArgs false

private theorem application_plain (function : PlainIndices env ctx f) (argument : PlainIndices env ctx a) :
    PlainIndices env ctx (.app f a) := by
  apply PlainIndices.node rfl
  intro term member
  rcases List.mem_cons.mp member with rfl | member
  · exact function
  · have same := List.mem_singleton.mp member
    exact same ▸ argument

private theorem applications_plain (head : PlainIndices env ctx function)
    (args : ∀ value ∈ values,PlainIndices env ctx value) :
    PlainIndices env ctx (applications function values) := by
  induction values generalizing function with
  | nil => exact head
  | cons value values ih =>
      exact ih (application_plain head (args value (by simp))) (fun term member => args term (by simp [member]))

private theorem elimTerm_plain (motivePlain : PlainIndices env ctx motive)
    (casesPlain : ∀ branch ∈ cases,PlainIndices env ctx branch)
    (scrutineePlain : PlainIndices env ctx scrutinee) :
    PlainIndices env ctx (elimTerm family motive cases scrutinee) := by
  apply PlainIndices.node rfl
  intro term member
  rcases List.mem_cons.mp member with rfl | member
  · exact motivePlain
  · rcases List.mem_append.mp member with member | member
    · exact casesPlain term member
    · have same := List.mem_singleton.mp member; exact same ▸ scrutineePlain

private theorem viewTerm_plain (motivePlain : PlainIndices env ctx motive)
    (casesPlain : ∀ branch ∈ cases,PlainIndices env ctx branch)
    (scrutineePlain : PlainIndices env ctx scrutinee) :
    PlainIndices env ctx (viewTerm recursion family motive cases scrutinee) := by
  apply PlainIndices.node rfl
  intro term member
  rcases List.mem_cons.mp member with rfl | member
  · exact motivePlain
  · rcases List.mem_append.mp member with member | member
    · exact casesPlain term member
    · have same := List.mem_singleton.mp member; exact same ▸ scrutineePlain

private theorem borrow_plain (plain : PlainIndices env ctx value) : PlainIndices env ctx (.borrow value) :=
  .node rfl (by intro term member; have same := List.mem_singleton.mp member; exact same ▸ plain)

private theorem elimHypotheses_plain (motivePlain : PlainIndices env ctx motive)
    (casesPlain : ∀ branch ∈ cases,PlainIndices env ctx branch)
    (valuesPlain : ∀ value ∈ values,PlainIndices env ctx value) (fields : List Field) :
    ∀ term ∈ elimHypotheses family motive cases fields values,PlainIndices env ctx term := by
  induction fields generalizing values with
  | nil => simp [elimHypotheses]
  | cons field fields ih =>
      cases values with
      | nil => simp [elimHypotheses]
      | cons value values =>
          have head := valuesPlain value (by simp)
          have tail : ∀ t ∈ values,PlainIndices env ctx t := fun t member => valuesPlain t (by simp [member])
          simp only [elimHypotheses,List.zip_cons_cons,List.filterMap_cons]
          by_cases recursive : field.recursive.isSome = true
          · simp only [recursive,ite_true,List.mem_cons,forall_eq_or_imp]
            exact ⟨elimTerm_plain motivePlain casesPlain head,ih tail⟩
          · simpa only [recursive,Bool.false_eq_true,ite_false,elimHypotheses] using ih tail

private theorem viewArguments_plain (valuesPlain : ∀ value ∈ values,PlainIndices env ctx value)
    (plans : List ViewFieldPlan) :
    ∀ term ∈ viewArguments plans values,PlainIndices env ctx term := by
  induction plans generalizing values with
  | nil => simp [viewArguments]
  | cons plan plans ih =>
      cases values with
      | nil => simp [viewArguments]
      | cons value values =>
          simp only [viewArguments,List.zip_cons_cons,List.map_cons,List.mem_cons,forall_eq_or_imp]
          refine ⟨?_,ih (fun t member => valuesPlain t (by simp [member]))⟩
          split
          · exact borrow_plain (valuesPlain value (by simp))
          · exact valuesPlain value (by simp)

private theorem viewHypotheses_plain (motivePlain : PlainIndices env ctx motive)
    (casesPlain : ∀ branch ∈ cases,PlainIndices env ctx branch)
    (valuesPlain : ∀ value ∈ values,PlainIndices env ctx value) (plans : List ViewFieldPlan) :
    ∀ term ∈ viewHypotheses recursion family motive cases plans values,PlainIndices env ctx term := by
  cases recursion with
  | false => simp [viewHypotheses]
  | true =>
      induction plans generalizing values with
      | nil => simp [viewHypotheses]
      | cons plan plans ih =>
          cases values with
          | nil => simp [viewHypotheses]
          | cons value values =>
              have tail : ∀ t ∈ values,PlainIndices env ctx t := fun t member => valuesPlain t (by simp [member])
              simp only [viewHypotheses,List.zip_cons_cons,List.filterMap_cons,ite_true]
              by_cases recursive : plan.self = true
              · simp only [recursive,ite_true,List.mem_cons,forall_eq_or_imp]
                exact ⟨viewTerm_plain motivePlain casesPlain (borrow_plain (valuesPlain value (by simp))),ih tail⟩
              · simpa only [recursive,Bool.false_eq_true,ite_false,viewHypotheses,ite_true] using ih tail

/-- Every actual family root, with authentic source typing, preserves the
representation predicate at its original context. -/
theorem family_root_plain_transform (history : UnifiedProgram.UnifiedProgramChecked definitions declarations env)
    (root : Root env input output) : PlainTransform env input output := by
  refine ⟨.iota root,?_⟩
  intro ctx mode type typed plain
  cases plain with
  | index indexTyped => exact .index (indexTyped.ghostFamilyForward history (.iota root))
  | var => cases root
  | lam => cases root
  | ifLt => cases root
  | ifEq => cases root
  | node head children =>
      cases root with
      | @elim family entry constructor signature cases branch motive values found sigFound selected count fields =>
          have motivePlain := children motive (by simp [elimTerm])
          have casesPlain : ∀ t ∈ cases,PlainIndices env ctx t := fun t member => children t (by simp [elimTerm,member])
          have constructorPlain := children (.node (.con family constructor values.length) values) (by simp [elimTerm])
          have valuesPlain : ∀ t ∈ values,PlainIndices env ctx t := by
            cases constructorPlain with
            | node _ children => exact children
            | index indexTyped =>
                obtain ⟨_,_,_,_,_,_,_,converted⟩ := indexTyped.principalView
                exact False.elim (FamilyIota.Extended.Conv.full_rigid_disjoint (op := .ind family _) (op' := .u64) rfl rfl (by intro same;cases same) converted history.wellFormed.admissible)
          exact applications_plain (applications_plain (casesPlain branch (List.mem_of_getElem? selected))
            (fun t member => valuesPlain t (List.mem_of_mem_drop member)))
            (elimHypotheses_plain motivePlain casesPlain valuesPlain _)
      | @caseOf family entry constructor signature cases branch motive values found data sigFound selected count fields =>
          have casesPlain : ∀ t ∈ cases,PlainIndices env ctx t := fun t member => children t (by simp [caseTerm,member])
          have constructorPlain := children (.node (.con family constructor values.length) values) (by simp [caseTerm])
          have valuesPlain : ∀ t ∈ values,PlainIndices env ctx t := by
            cases constructorPlain with
            | node _ children => exact children
            | index indexTyped =>
                obtain ⟨_,_,_,_,_,_,_,converted⟩ := indexTyped.principalView
                exact False.elim (FamilyIota.Extended.Conv.full_rigid_disjoint (op := .ind family _) (op' := .u64) rfl rfl (by intro same;cases same) converted history.wellFormed.admissible)
          exact applications_plain (casesPlain branch (List.mem_of_getElem? selected))
            (fun t member => valuesPlain t (List.mem_of_mem_drop member))
      | @view family entry constructor signature cases branch plans recursion motive values found boxed sigFound selected count fields bound planned =>
          have motivePlain := children motive (by simp [viewTerm])
          have casesPlain : ∀ t ∈ cases,PlainIndices env ctx t := fun t member => children t (by simp [viewTerm,member])
          have borrowedPlain := children (.borrow (.node (.con family constructor values.length) values)) (by simp [viewTerm])
          have valuesPlain : ∀ t ∈ values,PlainIndices env ctx t := by
            cases borrowedPlain with
            | node _ children =>
                have constructorPlain := children (.node (.con family constructor values.length) values) (by simp)
                cases constructorPlain with
                | node _ children => exact children
                | index indexTyped =>
                    obtain ⟨_,_,_,_,_,_,_,converted⟩ := indexTyped.principalView
                    exact False.elim (FamilyIota.Extended.Conv.full_rigid_disjoint (op := .ind family _) (op' := .u64) rfl rfl (by intro same;cases same) converted history.wellFormed.admissible)
            | index indexTyped =>
                obtain ⟨_,_,converted⟩ := indexTyped.borrowView
                exact False.elim (FamilyIota.Extended.Conv.full_rigid_disjoint (op := .ref) (op' := .u64) rfl rfl (by intro same;cases same) converted history.wellFormed.admissible)
          have dropped : ∀ t ∈ values.drop entry.declaration.params,PlainIndices env ctx t :=
            fun t member => valuesPlain t (List.mem_of_mem_drop member)
          exact applications_plain (applications_plain (casesPlain branch (List.mem_of_getElem? selected))
            (viewArguments_plain dropped _)) (viewHypotheses_plain motivePlain casesPlain dropped _)
      | drop => exact children output (by simp)

end Jihoo.NativeKernel.Environment.Representation
