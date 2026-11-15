import Jihoo.NativeContextualUniverseModel
import Jihoo.NativeLendRawConversion
import Jihoo.NativeEnvironmentTyping
set_option maxUniverseOffset 40

/-! A dependent gluing relation over the concrete finite CwF. Pi fibers may
depend on arbitrary semantic values, with any finite sort, rather than on a
fixed source-code grammar. The raw conversion includes genuine Lend macros;
this does not assert source LoanTyping preservation of macro intermediates. -/
namespace Jihoo.NativeKernel.Environment.Semantics.DependentRelation
open Contextual

structure Ty (env : Environment) (Γ : Contextual.Context) (sort : Finite.LevelSort) where
  code : Contextual.Ty Γ sort
  realizes : (point : Γ) → Term → Finite.Carrier (code point) → Prop
  conversion : ∀ point {term replacement value},RawLend.Conv env term replacement →
    (realizes point term value ↔ realizes point replacement value)

def Ty.substitution (A : Ty env Δ sort) (σ : Contextual.Sub Γ Δ) : Ty env Γ sort where
  code := Contextual.typeSubst A.code σ
  realizes point term value := A.realizes (σ point) term value
  conversion := by
    intro point term replacement value converted
    exact A.conversion (σ point) converted

def pi (A : Ty env Γ domainSort) (B : Ty env (Contextual.extend Γ A.code) bodySort) :
    Ty env Γ (domainSort.pi bodySort) where
  code := Contextual.pi A.code B.code
  realizes point function value := ∀ argument argumentValue,A.realizes point argument argumentValue →
    B.realizes ⟨point,argumentValue⟩ (.app function argument)
      ((Finite.piMeaning (A.code point) bodySort (fun value => B.code ⟨point,value⟩)).app value argumentValue)
  conversion := by
    intro point term replacement value converted
    constructor <;> intro realized argument argumentValue admitted
    · exact (B.conversion ⟨point,argumentValue⟩
        (.node .app (.cons converted (.cons (.refl _) .nil)))).mp (realized argument argumentValue admitted)
    · exact (B.conversion ⟨point,argumentValue⟩
        (.node .app (.cons converted (.cons (.refl _) .nil)))).mpr (realized argument argumentValue admitted)

theorem pi_application (A : Ty env Γ domainSort) (B : Ty env (Contextual.extend Γ A.code) bodySort)
    {point : Γ} {function argument : Term}
    {functionValue : Finite.Carrier ((pi A B).code point)} {argumentValue : Finite.Carrier (A.code point)}
    (realized : (pi A B).realizes point function functionValue)
    (argumentRealized : A.realizes point argument argumentValue) :
    B.realizes ⟨point,argumentValue⟩ (.app function argument)
      ((Finite.piMeaning (A.code point) bodySort (fun value => B.code ⟨point,value⟩)).app functionValue argumentValue) :=
  realized _ _ argumentRealized

theorem pi_substitution (A : Ty env Δ domainSort) (B : Ty env (Contextual.extend Δ A.code) bodySort)
    (σ : Contextual.Sub Γ Δ) :
    (pi A B).substitution σ = pi (A.substitution σ) (B.substitution (Contextual.lift σ)) := rfl

/-- A mathematical natural has a valid additive source tree at any size.
This definition is symbolic; no unary expansion is executed during checking. -/
def numeralTree (value : Nat) : Term := ACU.compact (List.replicate value (.natural 1))

theorem numeralTree_typed (value : Nat) : HasType env ctx mode (numeralTree value) .u64 := by
  induction value with
  | zero => exact .natural (by decide)
  | succ value ih =>
    cases value with
    | zero => exact .natural (by decide)
    | succ value => exact .uadd (.natural (by decide)) ih

def natural (env : Environment) (Γ : Contextual.Context) : Ty env Γ (.type ⟨0,by decide⟩) where
  code := Contextual.natural
  realizes _ term value := RawLend.Conv env term (numeralTree value.down)
  conversion := by
    intro point term replacement value converted
    exact ⟨fun realized => converted.symm.trans realized,fun realized => converted.trans realized⟩

theorem natural_literal (value : Nat) (bound : value < 2^64) :
    (natural env Γ).realizes point (.natural value) ⟨value⟩ :=
  .old (.old (.acu ((ACU.ArithmeticRed.literalSplit value bound).toArithmetic.toConv)))

theorem natural_add (first : (natural env Γ).realizes point a firstValue)
    (second : (natural env Γ).realizes point b secondValue) :
    (natural env Γ).realizes point (.uadd a b) ⟨firstValue.down+secondValue.down⟩ := by
  have related : RawLend.Conv env (.uadd a b) (.uadd (numeralTree firstValue.down) (numeralTree secondValue.down)) :=
    .node .uadd (.cons first (.cons second .nil))
  have combined := ACU.ArithmeticRed.compact_append (List.replicate firstValue.down (.natural 1))
    (List.replicate secondValue.down (.natural 1))
  have combinedConversion : RawLend.Conv env (.uadd (numeralTree firstValue.down) (numeralTree secondValue.down))
      (numeralTree (firstValue.down+secondValue.down)) := by
    simpa only [numeralTree,List.replicate_append_replicate] using
      (RawLend.Conv.old (FamilyIota.Extended.Conv.old (EnvironmentDelta.Basis.Conv.acu combined.toArithmetic.toConv)))
  exact related.trans combinedConversion

/-- Empty propositions use the actual concrete Prop carrier, not a supplied
normalization or proof-irrelevance axiom. -/
def proposition (env : Environment) (Γ : Contextual.Context) (truth : Γ → Prop) :
    Ty env Γ .proposition where
  code point := .proposition (truth point)
  realizes _ _ _ := True
  conversion := by intros; exact Iff.rfl

theorem false_unrealizable (point : Γ) (term : Term) :
    ¬ ∃ value,(proposition env Γ (fun _ => False)).realizes point term value := by
  rintro ⟨value,_⟩
  exact value.down.down

end Jihoo.NativeKernel.Environment.Semantics.DependentRelation
