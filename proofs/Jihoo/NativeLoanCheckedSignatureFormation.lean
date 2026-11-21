import Jihoo.NativeLoanFamilyIotaConstructor
import Jihoo.NativeLoanEnvironmentExtension
import Jihoo.NativeLoanContextConversion

/-! Written and stored constructor signatures form types once their
family is visible. The earlier declaration checked each ordinary binder
and recursive index in its dependent prefix. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.CheckedSignatureFormation

open UnifiedProgram.Families

private def familySort (data : Bool) : SortTag := if data then .type 0 else .prop

private theorem indices_typed
    (extension : Environment.Extends before env)
    (checked : IndicesChecked before self ctx source indices) :
    ∀ term ∈ indices, HasType env [] ctx true term .u64 :=
  fun term member => (LoanTyping.ofEnvironment (checked.normal_typed term member)).extend extension

private theorem family_result (found : env.families[family]? = some entry)
    (width : indices.length = entry.declaration.arity)
    (typed : ∀ term ∈ indices, HasType env [] ctx true term .u64) :
    HasType env [] ctx true (.node (.ind family indices.length) indices) (familySort entry.declaration.data).term := by
  have formed := HasType.ind (ghost := true) found width rfl typed
  cases truth : entry.declaration.data <;>
    simpa [familySort,truth,SortTag.term] using formed

private theorem stored_binder
    (extension : Environment.Extends before env)
    (found : env.families[self]? = some entry) (family : entry.declaration = declaration)
    (field : FieldChecked before self declaration ctx erased original stored) :
    ∃ sort : SortTag, Binder env [] ctx stored.erased stored.domain sort := by
  cases field with
  | ordinary _ _ _ _ checked _ => exact ⟨_,LoanTyping.binder_ofEnvironment (checked.extend extension)⟩
  | recursive countWidth sourceWidth indices erasedKind parameters =>
    rename_i count written normal
    have width := indices.length.symm.trans sourceWidth
    have known : normal.length = entry.declaration.arity := width.trans (congrArg FamilyDeclaration.arity family).symm
    have typed := family_result found known (indices_typed extension indices)
    have same : normal.length = count := width.trans countWidth.symm
    rw [same,family] at typed
    cases data : declaration.data
    · simp only [data,Bool.not_false] at erasedKind
      cases erasedKind
      exact ⟨.prop,.intro (by simpa only [familySort,data,Bool.false_eq_true,ite_false] using typed) (Or.inl (Or.inl rfl))⟩
    · simp only [data,Bool.not_true] at erasedKind
      cases erasedKind
      exact ⟨.type 0,.intro (by simpa only [familySort,data,ite_true] using typed) (Or.inl (by simp [pureBinderAllowed]))⟩

private theorem checked_suffix
    (extension : Environment.Extends before env)
    (found : env.families[self]? = some entry) (family : entry.declaration = declaration)
    (checked : TelescopeChecked before self declaration preceding original signature) :
    ∃ remaining, signature.fields = preceding ++ remaining ∧ ∃ sort : SortTag,
      HasType env [] (fieldContext preceding) true
        (closeDataFields (remaining.map fun field => (field.erased,field.domain))
          (.node (.ind self signature.result.length) signature.result)) sort.term := by
  induction checked with
  | field first rest ih =>
    rename_i preceding erased domain stored unprocessed signature
    obtain ⟨remaining,fields,bodySort,body⟩ := ih
    obtain ⟨domainSort,binder⟩ := stored_binder extension found family first
    have nextContext : fieldContext (preceding ++ [stored]) = ⟨stored.domain,stored.erased⟩ :: fieldContext preceding := by
      simp [FamilyEnvironment.fieldContext]
    rw [nextContext] at body
    refine ⟨stored :: remaining,by simpa only [List.append_assoc,List.singleton_append] using fields,domainSort.pi bodySort,?_⟩
    exact .pi binder body
  | result _ sourceWidth indices _ =>
    have width := indices.length.symm.trans sourceWidth
    have known : _ = entry.declaration.arity := width.trans (congrArg FamilyDeclaration.arity family).symm
    exact ⟨[],by simp,_,family_result found known (indices_typed extension indices)⟩

/-- All binders of the authenticated stored signature form a type in the
current environment, including recursively indexed fields. -/
theorem signature_formed
    (history : ScopedProgram.History definitions declarations env) {constructor : Nat}
    (found : env.families[family]? = some entry) (signature : entry.signatures[constructor]? = some stored) :
    ∃ sort : SortTag, HasType env [] ctx true (signatureTerm family stored) sort.term := by
  obtain ⟨_,_,before,source,_,index,checked,extension⟩ := history.family_prefix found
  obtain ⟨_,_,telescope⟩ := checked.signatures.right signature
  subst family
  obtain ⟨remaining,fields,sort,typed⟩ := checked_suffix extension found checked.declaration telescope
  have closed : HasType env [] [] true (signatureTerm before.families.size stored) sort.term := by
    rw [LoanTyping.FamilyIota.signatureTerm_close_fields,fields]
    exact typed
  have lifted := closed.ghostRenaming history.wellFormed (Δ := ctx) (ρ := id)
    (by intro index binding present; cases present)
  exact ⟨sort,by simpa only [Term.rename_id,SortTag.rename_term] using lifted⟩

private theorem expansion_retained (extension : Environment.Extends before env)
    (observed : GlobalEnvironment.Expansion before.globals source expanded) :
    GlobalEnvironment.Expansion env.globals source expanded := by
  induction observed using GlobalEnvironment.Expansion.rec
    (motive_2 := fun xs ys _ => NativeKernel.Conversion.ListRel (GlobalEnvironment.Expansion env.globals) xs ys) with
  | var x => exact .var x
  | global found => exact .global (extension.globals _ _ found)
  | node op ordinary _ ih => exact .node op ordinary ih
  | nil => exact .nil
  | cons _ _ head tail => exact .cons head tail

private theorem expanded_indices (extension : Environment.Extends before env)
    (checked : IndicesChecked before self ctx source normal) :
    (∀ term ∈ source.map (EnvironmentDelta.expand env), HasType env [] ctx true term .u64) ∧
      NativeKernel.Conversion.ListRel (Conversion.Conv env) (source.map (EnvironmentDelta.expand env)) normal := by
  induction checked with
  | nil => exact ⟨by simp,.nil⟩
  | cons first _ ih =>
    obtain ⟨_,expanded,observed,typed,converted,_⟩ := first
    have interpreted := EnvironmentDelta.expansion_eq_expand (expansion_retained extension observed)
    simp only [List.map_cons,interpreted]
    refine ⟨?_,.cons (.old (converted.extend extension)) ih.2⟩
    intro term member
    rcases List.mem_cons.mp member with rfl | later
    · exact (LoanTyping.ofEnvironment typed).extend extension
    · exact ih.1 term later

private theorem expanded_family_result (extension : Environment.Extends before env)
    (found : env.families[self]? = some entry) (family : entry.declaration = declaration)
    (width : count = declaration.arity) (indicesWidth : source.length = declaration.arity)
    (indices : IndicesChecked before self ctx source normal) :
    HasType env [] ctx true (EnvironmentDelta.expand env (.node (.ind self count) source))
      (familySort declaration.data).term ∧
      Conversion.Conv env (EnvironmentDelta.expand env (.node (.ind self count) source)) (.node (.ind self count) normal) := by
  obtain ⟨typed,converted⟩ := expanded_indices extension indices
  have length : (source.map (EnvironmentDelta.expand env)).length = count := by
    simpa only [List.length_map] using indicesWidth.trans width.symm
  have actual : (source.map (EnvironmentDelta.expand env)).length = entry.declaration.arity :=
    (length.trans width).trans (congrArg FamilyDeclaration.arity family).symm
  have formed := family_result found actual typed
  rw [length,family] at formed
  rw [EnvironmentDelta.expand_ordinary (by rfl),EnvironmentDelta.expandArgs_map]
  exact ⟨formed,.node _ converted⟩

private theorem expanded_binder (extension : Environment.Extends before env)
    (found : env.families[self]? = some entry) (family : entry.declaration = declaration)
    (checked : FieldChecked before self declaration ctx erased source stored) :
    ∃ sort : SortTag, Binder env [] ctx erased (EnvironmentDelta.expand env source) sort ∧
      Conversion.Conv env (EnvironmentDelta.expand env source) stored.domain := by
  cases checked with
  | ordinary _ observed binder converted _ _ =>
    rw [EnvironmentDelta.expansion_eq_expand (expansion_retained extension observed)]
    exact ⟨_,LoanTyping.binder_ofEnvironment (binder.extend extension),.old (converted.extend extension)⟩
  | recursive width sourceWidth indices erasedKind _ =>
    obtain ⟨formed,converted⟩ := expanded_family_result extension found family width sourceWidth indices
    cases data : declaration.data
    · simp only [data,Bool.not_false] at erasedKind
      cases erasedKind
      exact ⟨.prop,.intro (by simpa only [familySort,data,Bool.false_eq_true,ite_false] using formed) (Or.inl (Or.inl rfl)),converted⟩
    · simp only [data,Bool.not_true] at erasedKind
      cases erasedKind
      exact ⟨.type 0,.intro (by simpa only [familySort,data,ite_true] using formed) (Or.inl (by simp [pureBinderAllowed])),converted⟩

private theorem expanded_telescope (wf : UnifiedProgram.EnvWellFormed env)
    (extension : Environment.Extends before env)
    (found : env.families[self]? = some entry) (family : entry.declaration = declaration)
    (checked : TelescopeChecked before self declaration preceding source signature) :
    ∃ sort : SortTag, HasType env [] (fieldContext preceding) true (EnvironmentDelta.expand env source) sort.term := by
  induction checked with
  | field first rest ih =>
    rename_i preceding erased domain stored source signature
    obtain ⟨bodySort,body⟩ := ih
    obtain ⟨domainSort,binder,converted⟩ := expanded_binder extension found family first
    have nextContext : fieldContext (preceding ++ [stored]) = ⟨stored.domain,stored.erased⟩ :: fieldContext preceding := by
      simp [FamilyEnvironment.fieldContext]
    have sameErased : stored.erased = erased := by cases first <;> rfl
    rw [nextContext,sameErased] at body
    have related := (Ghost.ContextConversion.refl env (fieldContext preceding)).extend converted.symm erased wf.admissible.closed
    refine ⟨domainSort.pi bodySort,?_⟩
    simpa only [Term.pi,EnvironmentDelta.expand_node_cons,EnvironmentDelta.expandArgs] using
      HasType.pi binder (body.ghostContext wf related)
  | result width sourceWidth indices _ =>
    exact ⟨_,(expanded_family_result extension found family width sourceWidth indices).1⟩

/-- A constructor selected from the written declaration already has a formed
annotation before any argument is compared. Each expanded recursive index
is checked in the prefix where it appeared. -/
theorem source_signature_formed
    (history : ScopedProgram.History definitions declarations env)
    {family constructor : Nat} {entry : CheckedFamily} {stored : Signature}
    (found : env.families[family]? = some entry)
    (selected : entry.signatures[constructor]? = some stored) :
    ∃ source sort, entry.declaration.constructors[constructor]? = some source ∧
      HasType env [] ctx true (EnvironmentDelta.expand env source) (SortTag.term sort) := by
  obtain ⟨_,_,before,declaration,_,index,checked,extension⟩ := history.family_prefix found
  obtain ⟨source,written,telescope⟩ := checked.signatures.right selected
  subst family
  obtain ⟨sort,typed⟩ := expanded_telescope history.wellFormed extension found checked.declaration telescope
  have lifted := typed.ghostRenaming history.wellFormed (Δ := ctx) (ρ := id)
    (by intro index binding present; cases present)
  refine ⟨source,sort,?_ ,by simpa only [Term.rename_id,SortTag.rename_term] using lifted⟩
  simpa only [checked.declaration] using written

end Jihoo.NativeKernel.Environment.LoanTyping.CheckedSignatureFormation
