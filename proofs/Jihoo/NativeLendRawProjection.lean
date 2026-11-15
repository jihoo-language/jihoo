import Jihoo.NativeLendRawSyntax
import Jihoo.NativeFamilyIotaChurchRosser

/-! Raw macro projection into the proved family/delta/ACU theory. Global
expansion happens in the genuine admitted environment before macro projection;
no fabricated environment or external conversion oracle is used. -/
namespace Jihoo.NativeKernel.Environment.RawLend
open NativeKernel.Conversion (ListRel)
set_option linter.unusedSimpArgs false

private theorem acu_desugar_congr (owners : ACU.Conv owner owner') (readers : ACU.Conv reader reader')
    (continuations : ACU.Conv continuation continuation') :
    ACU.Conv (desugar owner reader continuation) (desugar owner' reader' continuation') :=
  .node .app (.cons (.node .app (.cons continuations (.cons
    (.node .app (.cons readers (.cons (.node .borrow (.cons owners .nil)) .nil))) .nil))) (.cons owners .nil))

private theorem rebuild_congruence (op : Op) (related : ListRel ACU.Conv first second) :
    ACU.Conv (rebuild op first) (rebuild op second) := by
  by_cases head : op = .lend
  · subst op
    cases related with
    | nil => exact .refl _
    | cons owner rest => cases rest with
      | nil => simpa only [rebuild] using ACU.Conv.node .lend (.cons owner .nil)
      | cons reader rest => cases rest with
        | nil => simpa only [rebuild] using ACU.Conv.node .lend (.cons owner (.cons reader .nil))
        | cons continuation rest => cases rest with
          | nil => exact acu_desugar_congr owner reader continuation
          | cons extra rest =>
              simpa only [rebuild] using ACU.Conv.node .lend (.cons owner (.cons reader (.cons continuation (.cons extra rest))))
  · rw [rebuild_other head,rebuild_other head]
    exact .node op related

theorem legacy_conversion (converted : NativeKernel.Conversion.Conv first second) : ACU.Conv (unlend first) (unlend second) := by
  induction converted using NativeKernel.Conversion.Conv.rec
    (motive_2 := fun first second _ => Conversion.ListRel ACU.Conv (unlendArgs first) (unlendArgs second)) with
  | refl => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ first second => exact .trans first second
  | node op children ih => simpa only [unlend] using rebuild_congruence op ih
  | beta unlendd domain body argument =>
    simpa only [unlend,unlendArgs,rebuild,unlend_instantiate] using
      (ACU.Conv.legacy (.beta unlendd (unlend domain) (unlend body) (unlend argument)))
  | add first second bound =>
    simpa only [unlend,unlendArgs,rebuild] using (ACU.Conv.legacy (.add first second bound))
  | sub first second proof ordered bound =>
    simpa only [unlend,unlendArgs,rebuild] using (ACU.Conv.legacy (.sub first second (unlend proof) ordered bound))
  | read count elements index proof value selected =>
    simpa only [unlend,unlendArgs,rebuild] using
      (ACU.Conv.legacy (.read count (unlendArgs elements) index (unlend proof) (unlend value)
        (by rw [unlendArgs_map,List.getElem?_map,selected]; rfl)))
  | witnessPack predicate value proof =>
    simpa only [unlend,unlendArgs,rebuild] using
      (ACU.Conv.legacy (.witnessPack (unlend predicate) (unlend value) (unlend proof)))
  | proofPack predicate value proof =>
    simpa only [unlend,unlendArgs,rebuild] using
      (ACU.Conv.legacy (.proofPack (unlend predicate) (unlend value) (unlend proof)))
  | derefBorrow value => simpa only [unlend,unlendArgs,rebuild] using (ACU.Conv.legacy (.derefBorrow (unlend value)))
  | borrowDeref value => simpa only [unlend,unlendArgs,rebuild] using (ACU.Conv.legacy (.borrowDeref (unlend value)))
  | transportRefl family value proof =>
    simpa only [unlend,unlendArgs,rebuild] using (ACU.Conv.legacy (.transportRefl (unlend family) (unlend value) (unlend proof)))
  | ifLtTrue first second yes no bound =>
    simpa only [unlend,unlendArgs,rebuild,unlend_instantiate] using
      (ACU.Conv.legacy (.ifLtTrue first second (unlend yes) (unlend no) bound))
  | ifLtFalse first second yes no bound =>
    simpa only [unlend,unlendArgs,rebuild] using (ACU.Conv.legacy (.ifLtFalse first second (unlend yes) (unlend no) bound))
  | ifEqTrue value yes no =>
    simpa only [unlend,unlendArgs,rebuild,unlend_instantiate] using (ACU.Conv.legacy (.ifEqTrue value (unlend yes) (unlend no)))
  | ifEqFalse first second yes no different =>
    simpa only [unlend,unlendArgs,rebuild] using (ACU.Conv.legacy (.ifEqFalse first second (unlend yes) (unlend no) different))
  | nil => simp only [unlendArgs]; exact .nil
  | cons first rest ihfirst ihrest => simpa only [unlendArgs] using Conversion.ListRel.cons ihfirst ihrest

theorem acu_conversion (converted : ACU.Conv first second) : ACU.Conv (unlend first) (unlend second) := by
  induction converted using ACU.Conv.rec
    (motive_2 := fun first second _ => Conversion.ListRel ACU.Conv (unlendArgs first) (unlendArgs second)) with
  | legacy converted => exact legacy_conversion converted
  | refl => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ first second => exact .trans first second
  | node op children ih => simpa only [unlend] using rebuild_congruence op ih
  | assoc first second third => simpa only [unlend,unlendArgs,rebuild] using ACU.Conv.assoc (unlend first) (unlend second) (unlend third)
  | comm first second => simpa only [unlend,unlendArgs,rebuild] using ACU.Conv.comm (unlend first) (unlend second)
  | zero first => simpa only [unlend,unlendArgs,rebuild] using ACU.Conv.zero (unlend first)
  | nil => simp only [unlendArgs]; exact .nil
  | cons first rest ihfirst ihrest => simpa only [unlendArgs] using Conversion.ListRel.cons ihfirst ihrest


/-- Eliminate globals first using the actual checked prefix, then expand raw
Lend macros. Stored declarations are never replaced by an assumed erased world. -/
def project (env : Environment) (term : Term) : Term := unlend (EnvironmentDelta.expand env term)

theorem project_renaming (admissible : EnvironmentDelta.Admissible env) (term : Term) (ρ : Nat → Nat) :
    project env (term.rename ρ) = (project env term).rename ρ := by
  rw [project,EnvironmentDelta.expand_renaming admissible,unlend_rename]
  rfl

theorem project_substitution (admissible : EnvironmentDelta.Admissible env) (term : Term) (σ : Nat → Term) :
    project env (term.subst σ) = (project env term).subst (fun index => project env (σ index)) := by
  rw [project,EnvironmentDelta.expand_substitution admissible,unlend_subst]
  rfl

theorem project_node_nonempty (op : Op) (term : Term) (terms : List Term) :
    project env (.node op (term::terms)) = rebuild op (unlendArgs (EnvironmentDelta.expandArgs env (term::terms))) := by
  rw [project,EnvironmentDelta.expand_node_cons,unlend]
  simp only [EnvironmentDelta.expandArgs]

theorem project_root (root : FamilyIota.Root env term result) :
    FamilyIota.Root env (project env term) (project env result) :=
  unlend_root (FamilyIota.Extended.root_expansion root)

private theorem family_desugar_congr (owners : FamilyIota.Extended.Conv env owner owner') (readers : FamilyIota.Extended.Conv env reader reader')
    (continuations : FamilyIota.Extended.Conv env continuation continuation') :
    FamilyIota.Extended.Conv env (desugar owner reader continuation) (desugar owner' reader' continuation') :=
  .node .app (.cons (.node .app (.cons continuations (.cons
    (.node .app (.cons readers (.cons (.node .borrow (.cons owners .nil)) .nil))) .nil))) (.cons owners .nil))

theorem rebuild_family_congruence (op : Op) (related : ListRel (FamilyIota.Extended.Conv env) first second) :
    FamilyIota.Extended.Conv env (rebuild op first) (rebuild op second) := by
  by_cases head : op = .lend
  · subst op
    cases related with
    | nil => exact .refl _
    | cons owner rest => cases rest with
      | nil => simpa only [rebuild] using FamilyIota.Extended.Conv.node (env := env) .lend (.cons owner .nil)
      | cons reader rest => cases rest with
        | nil => simpa only [rebuild] using FamilyIota.Extended.Conv.node (env := env) .lend (.cons owner (.cons reader .nil))
        | cons continuation rest => cases rest with
          | nil => exact family_desugar_congr owner reader continuation
          | cons extra rest =>
              simpa only [rebuild] using FamilyIota.Extended.Conv.node (env := env) .lend (.cons owner (.cons reader (.cons continuation (.cons extra rest))))
  · rw [rebuild_other head,rebuild_other head]
    exact .node op related


/-- Every equation of the already installed family theory survives raw Lend
macro expansion after genuine global expansion. -/
theorem family_conversion (admissible : EnvironmentDelta.Admissible env)
    (converted : FamilyIota.Extended.Conv env first second) :
    FamilyIota.Extended.Conv env (project env first) (project env second) := by
  induction converted using FamilyIota.Extended.Conv.rec
    (motive_2 := fun xs ys _ => ListRel (FamilyIota.Extended.Conv env)
      (unlendArgs (EnvironmentDelta.expandArgs env xs)) (unlendArgs (EnvironmentDelta.expandArgs env ys))) with
  | old original => exact .old (.acu (acu_conversion (original.toProjected admissible)))
  | iota root => exact .iota (project_root root)
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

theorem project_ordinary (ordinary : GlobalEnvironment.ordinary op = true) (children : List Term) :
    project env (.node op children) = rebuild op (children.map (project env)) := by
  rw [project,EnvironmentDelta.expand_ordinary ordinary,unlend,unlendArgs_map,EnvironmentDelta.expandArgs_map,List.map_map]
  rfl

theorem project_lend (env : Environment) (owner reader continuation : Term) :
    project env (lendTerm owner reader continuation) = desugar (project env owner) (project env reader) (project env continuation) := by
  rw [lendTerm,project_ordinary (by rfl)]
  rfl

theorem project_desugar (env : Environment) (owner reader continuation : Term) :
    project env (desugar owner reader continuation) = desugar (project env owner) (project env reader) (project env continuation) := by
  simp only [desugar,Term.app,Term.borrow,project_ordinary (op := .app) (by rfl),
    project_ordinary (op := .borrow) (by rfl),List.map_cons,List.map_nil,rebuild]


end Jihoo.NativeKernel.Environment.RawLend
