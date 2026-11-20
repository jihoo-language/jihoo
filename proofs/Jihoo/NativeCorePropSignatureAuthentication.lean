import Jihoo.NativeCorePropSignatureConversion
import Jihoo.NativeCoreConstructorTelescopeAlignment

/-! The recursive markers come from the written constructor telescope.
Its two independently normalized signatures may differ in representation
while agreeing on every field, result index and recursive position. -/
namespace Jihoo.NativeKernel.NativeCorePropSignatureAuthentication

open Environment UnifiedProgram
open FamilyEnvironment (RelList)
open NativeKernel.Conversion (ListRel)
open EnvironmentDelta (expand expandArgs)

inductive ObservedField (env : Environment) (family : Nat) : Bool → Term → Field → Prop where
  | ordinary : Families.selfFree family source = true →
      RawLend.Conv env (expand env source) (expand env domain) →
      ObservedField env family erased source ⟨erased,domain,none⟩
  | recursive : RawLend.Conv env (expand env (.node (.ind family count) source)) (expand env domain) →
      ListRel (RawLend.Conv env) (expandArgs env source) (expandArgs env indices) →
      ObservedField env family erased (.node (.ind family count) source) ⟨erased,domain,some indices⟩

inductive ObservedTelescope (env : Environment) (family : Nat) : List Field → Term → Signature → Prop where
  | field : ObservedField env family erased domain field →
      ObservedTelescope env family (fields ++ [field]) tail signature →
      ObservedTelescope env family fields (.pi erased domain tail) signature
  | result : ListRel (RawLend.Conv env) (expandArgs env source) (expandArgs env indices) →
      ObservedTelescope env family fields (.node (.ind family count) source) ⟨fields,indices⟩

private theorem across_prefix (extension : prior.Extends env)
    (expanded : GlobalEnvironment.Expansion prior.globals source concrete)
    (checked : Environment.Conversion.Conv prior concrete normal) :
    RawLend.Conv env (expand env source) normal := by
  have before : RawLend.Conv prior source (expand prior source) :=
    (RawLend.Forward.old (.old (EnvironmentDelta.expand_forward prior source))).toConv
  have after : RawLend.Conv env source (expand env source) :=
    (RawLend.Forward.old (.old (EnvironmentDelta.expand_forward env source))).toConv
  have checkedHere : RawLend.Conv prior (expand prior source) normal :=
    (EnvironmentDelta.expansion_eq_expand (env := prior) expanded).symm ▸ RawLend.Conv.old checked
  exact after.symm.trans ((before.trans checkedHere).extend extension)

private theorem common_indices (first : ListRel (RawLend.Conv env) source xs)
    (second : ListRel (RawLend.Conv env) source ys) : ListRel (RawLend.Conv env) xs ys := by
  induction first generalizing ys with
  | nil => cases second; exact .nil
  | cons head tail ih =>
    cases second with
    | cons next rest => exact .cons (head.symm.trans next) (ih rest)

private theorem checked_indices (extension : prior.Extends env)
    (checked : Families.IndicesChecked prior family ctx written normal) :
    ListRel (RawLend.Conv env) (expandArgs env written) normal := by
  induction checked with
  | nil => simp only [expandArgs]; exact .nil
  | cons head _ tail =>
    obtain ⟨_,_,expansion,_,converted,_⟩ := head
    simp only [expandArgs]
    exact .cons (across_prefix extension expansion converted) tail

private def unfoldField (env : Environment) (field : Field) : Field :=
  ⟨field.erased,expand env field.domain,field.recursive.map (expandArgs env)⟩

private theorem checked_field (extension : prior.Extends env)
    (observed : ObservedField env family erased domain field)
    (checked : Families.FieldChecked prior family declaration ctx erased domain trusted) :
    FieldConversion env (unfoldField env field) trusted := by
  cases observed with
  | ordinary absent ordinary =>
    cases checked with
    | ordinary _ expansion _ converted _ _ =>
      exact ⟨rfl,ordinary.symm.trans (across_prefix extension expansion converted),.none⟩
    | recursive _ _ _ _ _ =>
      simp [Families.selfFree] at absent
  | recursive domainConverted stored =>
    cases checked with
    | ordinary absent _ _ _ _ _ => simp [Families.selfFree] at absent
    | recursive _ _ indices _ _ =>
      have arguments := checked_indices extension indices
      simp only [expand] at domainConverted
      exact ⟨rfl,domainConverted.symm.trans (.node _ arguments),.some (common_indices stored arguments)⟩

private theorem related_snoc (prior : RelList R first second) (last : R a b) :
    RelList R (first ++ [a]) (second ++ [b]) := by
  induction prior with
  | nil => exact .cons last .nil
  | cons head tail ih => exact .cons head ih

/-- The native observation and the pure checked telescope refer to the same
written constructor. Only raw conversions and recorded recursive positions
are used, so later declarations may extend the checking prefix. -/
theorem checked_telescope (extension : prior.Extends env)
    (observed : ObservedTelescope env family observedPrefix written seen)
    (checked : Families.TelescopeChecked prior family declaration checkedPrefix written stored)
    (alignedPrefix : RelList (FieldConversion env) (observedPrefix.map (unfoldField env)) checkedPrefix) :
    SignatureConversion env (expandSignature env seen) stored := by
  induction checked generalizing observedPrefix seen with
  | field first tail ih =>
    cases observed with
    | field head rest =>
      exact ih rest (by simpa only [List.map_append,List.map_cons,List.map_nil]
        using related_snoc alignedPrefix (checked_field extension head first))
  | result _ _ indices _ =>
    cases observed with
    | result observedIndices => exact ⟨alignedPrefix,common_indices observedIndices (checked_indices extension indices)⟩

/-- Every observed native field becomes a case-type field at the authentic
signature in the mixed history, including each remembered recursive marker. -/
theorem from_history {family constructor : Nat}
    (history : ScopedProgram.History definitions declarations env)
    (found : env.families[family]? = some entry)
    (written : entry.declaration.constructors[constructor]? = some source)
    (selected : entry.signatures[constructor]? = some stored)
    (observed : ObservedTelescope env family [] source seen) :
    SignatureConversion env (expandSignature env seen) stored := by
  obtain ⟨_,_,prior,actual,earlier,place,checked,extension⟩ := history.family_prefix found
  rw [checked.declaration] at written
  obtain ⟨matching,read,related⟩ := checked.signatures.left written
  rw [selected] at read
  cases read
  rw [place] at related
  exact checked_telescope extension observed related .nil

end Jihoo.NativeKernel.NativeCorePropSignatureAuthentication
