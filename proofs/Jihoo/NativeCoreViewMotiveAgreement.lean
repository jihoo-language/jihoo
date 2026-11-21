import Jihoo.NativeCoreViewMotiveGate
import Jihoo.NativeLendNeutralHead

/-! A motive may retain a free type-family head after normalization.
Its application spine determines the same View mode at each successful
normalization visit with a rigid or free neutral result. -/
namespace Jihoo.NativeKernel.NativeCoreViewMotiveAgreement

open NativeArena Environment
open NativeCorePureComputationNormal (ExpandedNormalization)
open EnvironmentDelta (expand)

inductive Head : Term → Prop where
  | rigid : RawLend.rigid op = true → Head (.node op arguments)
  | neutral : Head (neutralSpine name arguments)

private theorem raw_expansion (env : Environment) (term : Term) :
    RawLend.Conv env term (expand env term) :=
  (RawLend.Forward.old (.old (EnvironmentDelta.expand_forward env term))).toConv

private theorem neutral_mode (head : Nat) (arguments : List Term) :
    LoanTyping.Checker.viewDependent (neutralSpine head arguments) = false := by
  cases arguments <;> rfl

private theorem neutral_to_rigid (admissible : EnvironmentDelta.Admissible env)
    (rigid : RawLend.rigid op = true)
    (converted : RawLend.Conv env (neutralSpine name arguments) (.node op terms)) :
    LoanTyping.Checker.viewDependent (.node op terms) = false := by
  cases op <;> try rfl
  case lam erased =>
    exact False.elim (RawLend.Conv.neutralSpine_node_separate admissible
      (by intro same; cases same) rigid converted)

/-- Real motive visits that expose either rigid nodes or free neutral
applications agree about the dependent mode, including open annotations. -/
theorem normalized_motive_modes_agree (admissible : EnvironmentDelta.Admissible env)
    (first : Represents before left A) (second : Represents after right B)
    (firstChange : ExpandedNormalization env M A) (secondChange : ExpandedNormalization env M B)
    (firstHead : Head A) (secondHead : Head B) :
    LoanTyping.Checker.viewDependent A = LoanTyping.Checker.viewDependent B := by
  have connected : RawLend.Conv env A B := (raw_expansion env A).trans
    (firstChange.converted.symm.trans (secondChange.converted.trans (raw_expansion env B).symm))
  cases firstHead with
  | rigid leftRigid =>
    cases secondHead with
    | rigid rightRigid =>
      exact NativeCoreViewMotiveGate.rigid_normal_motive_agrees admissible first second
        firstChange secondChange leftRigid rightRigid
    | neutral =>
      rw [neutral_mode]
      exact neutral_to_rigid admissible leftRigid connected.symm
  | neutral =>
    cases secondHead with
    | rigid rightRigid =>
      rw [neutral_mode]
      exact (neutral_to_rigid admissible rightRigid connected).symm
    | neutral => rw [neutral_mode,neutral_mode]

end Jihoo.NativeKernel.NativeCoreViewMotiveAgreement
