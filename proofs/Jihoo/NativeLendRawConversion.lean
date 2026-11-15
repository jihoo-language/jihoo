import Jihoo.NativeLendRawProjection

/-! A genuine unconditional raw Lend extension of the proved family theory.
Its raw forward paths are not assumed to preserve dependent source LoanTyping;
the source-specialized typed evaluator is a distinct obligation. -/
namespace Jihoo.NativeKernel.Environment.RawLend
open NativeKernel.Conversion (ListRel)

inductive Conv (env : Environment) : Term → Term → Prop where
  | old : FamilyIota.Extended.Conv env a b → Conv env a b
  | lend (owner reader continuation : Term) : Conv env (lendTerm owner reader continuation) (desugar owner reader continuation)
  | refl (term : Term) : Conv env term term
  | symm : Conv env a b → Conv env b a
  | trans : Conv env a b → Conv env b c → Conv env a c
  | node (op : Op) : ListRel (Conv env) xs ys → Conv env (.node op xs) (.node op ys)

inductive Forward (env : Environment) : Term → Term → Prop where
  | old : FamilyIota.Extended.Forward env a b → Forward env a b
  | lend (owner reader continuation : Term) : Forward env (lendTerm owner reader continuation) (desugar owner reader continuation)
  | refl : Forward env term term
  | trans : Forward env a b → Forward env b c → Forward env a c
  | node (op : Op) : ListRel (Forward env) xs ys → Forward env (.node op xs) (.node op ys)

theorem Forward.toConv (forward : Forward env a b) : Conv env a b := by
  induction forward using Forward.rec (motive_2 := fun xs ys _ => ListRel (Conv env) xs ys) with
  | old original => exact .old original.toConv
  | lend owner reader continuation => exact .lend owner reader continuation
  | refl => exact .refl _
  | trans _ _ first second => exact .trans first second
  | node op _ ih => exact .node op ih
  | nil => exact .nil
  | cons _ _ first rest => exact .cons first rest

private theorem rebuild_forward (op : Op) (children : List Term) :
    Forward env (.node op children) (rebuild op children) := by
  by_cases head : op = .lend
  · subst op
    cases children with
    | nil => simpa only [rebuild] using (Forward.refl (env := env) (term := .node .lend []))
    | cons owner rest => cases rest with
      | nil => simpa only [rebuild] using (Forward.refl (env := env) (term := .node .lend [owner]))
      | cons reader rest => cases rest with
        | nil => simpa only [rebuild] using (Forward.refl (env := env) (term := .node .lend [owner,reader]))
        | cons continuation rest => cases rest with
          | nil => simpa only [lendTerm,rebuild] using Forward.lend (env := env) owner reader continuation
          | cons extra rest => simpa only [rebuild] using
              (Forward.refl (env := env) (term := .node .lend (owner::reader::continuation::extra::rest)))
  · rw [rebuild_other head]
    exact .refl

/-- Total finite macro expansion follows actual raw forward equations, even
under malformed arities, binder annotations and arbitrary type syntax. -/
theorem unlend_forward (env : Environment) (term : Term) : Forward env term (unlend term) := by
  induction term using Term.rec (motive_2 := fun children => ListRel (Forward env) children (unlendArgs children)) with
  | var => simpa only [unlend] using (Forward.refl (env := env))
  | node op children ih =>
      simpa only [unlend] using (Forward.node op ih).trans (rebuild_forward op (unlendArgs children))
  | nil => simp only [unlendArgs];exact .nil
  | cons _ _ first rest => simpa only [unlendArgs] using ListRel.cons first rest

/-- Actual global expansion followed by actual finite Lend contraction reaches
the projection in the original environment. No erased world is fabricated. -/
theorem project_forward (env : Environment) (term : Term) : Forward env term (project env term) :=
  (Forward.old (.old (EnvironmentDelta.expand_forward env term))).trans (unlend_forward env _)

/-- Every enlarged raw equation has a proved equation in the established
family theory after its explicit projection. This handles all overlaps rather
than assuming Church-Rosser for the larger relation. -/
theorem Conv.projected (converted : Conv env a b) (admissible : EnvironmentDelta.Admissible env) :
    FamilyIota.Extended.Conv env (project env a) (project env b) := by
  induction converted using Conv.rec
    (motive_2 := fun xs ys _ => ListRel (FamilyIota.Extended.Conv env)
      (unlendArgs (EnvironmentDelta.expandArgs env xs)) (unlendArgs (EnvironmentDelta.expandArgs env ys))) with
  | old original => exact family_conversion admissible original
  | lend owner reader continuation => rw [project_lend,project_desugar];exact .refl _
  | refl => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ first second => exact .trans first second
  | node op related ih =>
      cases related with
      | nil => exact .refl _
      | cons head tail =>
          simpa only [project_node_nonempty,EnvironmentDelta.expandArgs] using rebuild_family_congruence op ih
  | nil => simp only [EnvironmentDelta.expandArgs,unlendArgs];exact .nil
  | cons _ _ first rest => simpa only [project,EnvironmentDelta.expandArgs,unlendArgs] using ListRel.cons first rest

/-- Genuine raw Lend/family/delta/ACU Church-Rosser yields actual finite common
reducts for arbitrary family metadata. Only the original global admissibility
invariant is needed; no typing, callback or enlarged confluence oracle occurs. -/
theorem Conv.church_rosser (converted : Conv env a b) (admissible : EnvironmentDelta.Admissible env) :
    ∃ common,Forward env a common ∧ Forward env b common := by
  obtain ⟨common,left,right⟩ := (converted.projected admissible).church_rosser admissible
  exact ⟨common,(project_forward env a).trans (.old left),(project_forward env b).trans (.old right)⟩

theorem Forward.confluence (left : Forward env a b) (right : Forward env a c)
    (admissible : EnvironmentDelta.Admissible env) :
    ∃ common,Forward env b common ∧ Forward env c common :=
  (left.toConv.symm.trans right.toConv).church_rosser admissible

theorem conv_iff_forward_join (admissible : EnvironmentDelta.Admissible env) :
    Conv env a b ↔ ∃ common,Forward env a common ∧ Forward env b common := by
  constructor
  · intro converted;exact converted.church_rosser admissible
  · rintro ⟨common,left,right⟩;exact left.toConv.trans right.toConv.symm

/-- The owner is duplicated by the real macro. Arbitrary simultaneous owner,
reader and continuation changes still join its actual root contraction. -/
theorem lend_children_join (ownerStep : Forward env owner owner')
    (readerStep : Forward env reader reader') (continuationStep : Forward env continuation continuation')
    (admissible : EnvironmentDelta.Admissible env) :
    ∃ common,Forward env (desugar owner reader continuation) common ∧
      Forward env (lendTerm owner' reader' continuation') common := by
  exact (Forward.lend owner reader continuation).confluence
    (.node .lend (.cons ownerStep (.cons readerStep (.cons continuationStep .nil)))) admissible

end Jihoo.NativeKernel.Environment.RawLend
