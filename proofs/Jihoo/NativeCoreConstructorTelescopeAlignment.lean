import Jihoo.NativeScopedProgramHistory
import Jihoo.NativeEnvironmentDeltaBounded
import Jihoo.NativeLoanEnvironmentExtension

/-! The raw constructor root used by native inference denotes the same
dependent telescope stored by the pure declaration checker. Field flags
are retained, and each normalized field and index has an authentic
conversion from its written earlier-prefix type. -/
namespace Jihoo.NativeKernel.NativeCoreConstructorTelescopeAlignment

open Environment UnifiedProgram
open EnvironmentDelta (expand expandArgs)
open NativeKernel.Conversion (ListRel)

private theorem indices_convert (checked : Families.IndicesChecked env self ctx written normal) :
    ListRel (RawLend.Conv env) (expandArgs env written) normal := by
  induction checked with
  | nil => simp only [expandArgs]; exact .nil
  | cons head tail ih =>
    obtain ⟨_,expanded,expansion,_,converted,_⟩ := head
    simp only [expandArgs]
    exact .cons ((EnvironmentDelta.expansion_eq_expand (env := env) expansion).symm ▸ RawLend.Conv.old converted) ih

private theorem field_convert (checked : Families.FieldChecked env self declaration ctx erased written field) :
    field.erased = erased ∧ RawLend.Conv env (expand env written) field.domain := by
  cases checked with
  | ordinary _ expansion _ converted _ _ =>
    exact ⟨rfl,(EnvironmentDelta.expansion_eq_expand (env := env) expansion).symm ▸ RawLend.Conv.old converted⟩
  | recursive _ _ indices _ _ =>
    refine ⟨rfl,?_⟩
    simp only [expand]
    exact .node _ (indices_convert indices)

private theorem expanded_suffix (checked : Families.TelescopeChecked env self declaration earlierFields written signature) :
    ∃ suffix, signature.fields = earlierFields ++ suffix ∧ RawLend.Conv env (expand env written)
      (suffix.foldr (fun field rest => .pi field.erased field.domain rest)
        (.node (.ind self signature.result.length) signature.result)) := by
  induction checked with
  | field checked next ih =>
    obtain ⟨remaining,length,tail⟩ := ih
    obtain ⟨flag,written⟩ := field_convert checked
    refine ⟨_ :: remaining,by simpa only [List.append_assoc,List.singleton_append] using length,?_⟩
    simp only [List.foldr_cons,flag,Term.pi,EnvironmentDelta.expand_node_cons,expandArgs]
    exact .node _ (.cons written (.cons tail .nil))
  | result arity length checked _ =>
    refine ⟨[],(List.append_nil _).symm,?_⟩
    have resultArity := length.symm.trans (FamilyEnvironment.RelList.length checked)
    have same : _ = _ := arity.trans resultArity
    simp only [List.foldr_nil,expand]
    rw [same]
    exact .node _ (indices_convert checked)

/-- Actual signature checking relates the written closed telescope to the
dependent telescope assembled from its checked fields and result indices. -/
theorem checked_signature_conversion (checked : Families.TelescopeChecked env family declaration [] written signature) :
    RawLend.Conv env (expand env written) (signatureTerm family signature) := by
  obtain ⟨suffix,fields,converted⟩ := expanded_suffix checked
  simpa only [signatureTerm,fields,List.nil_append] using converted

private theorem matching_entry {α β : Type} {P : α → β → Prop} {xs : List α} {ys : List β}
    {index : Nat} {x : α} {y : β} (related : FamilyEnvironment.RelList P xs ys)
    (left : xs[index]? = some x) (right : ys[index]? = some y) : P x y := by
  induction related generalizing index with
  | nil => cases left
  | cons checked tail ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at left right
      cases left
      cases right
      exact checked
    | succ index => exact ih left right

/-- The actual mixed history authenticates the native written constructor
root even when the caller comes after additional declarations. -/
theorem admitted_constructor_signature_conversion
    {family constructor : Nat} {entry : CheckedFamily} {written : Term} {signature : Signature}
    (history : ScopedProgram.History definitions declarations env)
    (familyFound : env.families[family]? = some entry)
    (writtenFound : entry.declaration.constructors[constructor]? = some written)
    (signatureFound : entry.signatures[constructor]? = some signature) :
    RawLend.Conv env (expand env written) (signatureTerm family signature) := by
  obtain ⟨_,_,prior,source,historyPrefix,index,checked,extension⟩ := history.family_prefix familyFound
  rw [checked.declaration] at writtenFound
  have telescope := matching_entry checked.signatures writtenFound signatureFound
  rw [index] at telescope
  have aligns := checked_signature_conversion telescope
  have earlier : RawLend.Conv prior written (expand prior written) :=
    (RawLend.Forward.old (.old (EnvironmentDelta.expand_forward prior written))).toConv
  have later : RawLend.Conv env written (expand env written) :=
    (RawLend.Forward.old (.old (EnvironmentDelta.expand_forward env written))).toConv
  exact later.symm.trans ((earlier.trans aligns).extend extension)

/-- The written family head survives every substitution through the
telescope, even when field values change all of its instantiated indices. -/
inductive EndsInFamily (family : Nat) : Term → Prop where
  | result (arity : Nat) (indices : List Term) : EndsInFamily family (.node (.ind family arity) indices)
  | binder : EndsInFamily family body → EndsInFamily family (.pi erased domain body)

theorem EndsInFamily.substitution (head : EndsInFamily family type) (values : Nat → Term) :
    EndsInFamily family (type.subst values) := by
  induction head generalizing values with
  | result arity indices =>
    simp only [Term.subst]
    exact .result arity _
  | binder head ih =>
    simp only [Term.pi,Term.subst,substArgs,Op.binders,liftSub]
    exact .binder (ih _)

theorem EndsInFamily.renaming (head : EndsInFamily family type) (rename : Nat → Nat) :
    EndsInFamily family (type.rename rename) := by
  induction head generalizing rename with
  | result arity indices =>
    simp only [Term.rename]
    exact .result arity _
  | binder head ih =>
    simp only [Term.pi,Term.rename,renameArgs,Op.binders,liftRenaming]
    exact .binder (ih _)

theorem signature_ends_in_family (family : Nat) (signature : Signature) :
    EndsInFamily family (signatureTerm family signature) := by
  unfold signatureTerm
  generalize signature.fields = fields
  induction fields with
  | nil => exact .result _ _
  | cons field rest ih => exact .binder ih

/-- The live field replay cannot end in a different inductive family from
the checked signature. This also covers conversion at every visited Pi
and each instantiated dependent index. -/
theorem replay_retains_declared_family (wf : UnifiedProgram.EnvWellFormed env)
    (replayed : LoanTyping.Arguments env loans ctx ghost data telescope fields output)
    (head : EndsInFamily family declared) (checked : RawLend.Conv env telescope declared)
    (result : output = .node (.ind actual arity) indices) : actual = family := by
  suffices claim : ∀ candidate, EndsInFamily family candidate → RawLend.Conv env telescope candidate →
      output = .node (.ind actual arity) indices → actual = family from claim declared head checked result
  apply LoanTyping.Arguments.rec (t := replayed)
    (motive_1 := fun _ _ _ _ _ _ => True) (motive_2 := fun _ _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ telescope _ output _ => ∀ candidate,
      EndsInFamily family candidate → RawLend.Conv env telescope candidate →
        output = .node (.ind actual arity) indices → actual = family)
    (motive_4 := fun _ _ _ _ _ _ => True) (motive_5 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | skip
  case nil =>
    rename_i telescope output stack ctx mode data converted candidate head aligned selected
    subst output
    cases head with
    | result count values =>
      exact ((aligned.symm.trans converted).ind_injective wf.admissible).1.symm
    | binder =>
      exact False.elim (RawLend.Conv.full_rigid_disjoint (op := .pi _) (op' := .ind actual arity)
        rfl rfl (by intro impossible; cases impossible) (aligned.symm.trans converted) wf.admissible)
  case cons =>
    rename_i telescope erased domain rest stack ctx mode data argument arguments output converted typed tail _ ih
      candidate head aligned selected
    cases head with
    | result count values =>
      exact False.elim (RawLend.Conv.full_rigid_disjoint (op := .ind family count) (op' := .pi _)
        rfl rfl (by intro impossible; cases impossible) (aligned.symm.trans converted) wf.admissible)
    | binder remaining =>
      have compared := (converted.symm.trans aligned).pi_injective wf.admissible
      exact ih _ (remaining.substitution (single argument)) (compared.2.2.substitution _ wf.closed) selected

end Jihoo.NativeKernel.NativeCoreConstructorTelescopeAlignment
