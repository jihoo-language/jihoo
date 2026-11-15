import Jihoo.NativeFamilyIotaConversion

/-! Compatibility embeddings for the legacy forward fragment of the installed
family, delta and ACU forward relation. -/
namespace Jihoo.NativeKernel.Environment.FamilyIota.Extended

theorem Forward.acu (step : ACU.MixedRed a b) : Forward env a b := .old (.acu step)
theorem Forward.delta (found : env.globals[index]? = some declaration) :
    Forward env (.node (.global index) []) declaration.value := .old (.delta found)

private theorem old_forward_extend (step : EnvironmentDelta.Forward before a b)
    (extension : Extends before after) : EnvironmentDelta.Forward after a b := by
  induction step using EnvironmentDelta.Forward.rec
    (motive_2 := fun xs ys _ => NativeKernel.Conversion.ListRel (EnvironmentDelta.Forward after) xs ys) with
  | refl => exact .refl
  | trans _ _ first second => exact .trans first second
  | node op _ ih => exact .node op ih
  | acu original => exact .acu original
  | delta found => exact .delta (extension.globals _ _ found)
  | nil => exact .nil
  | cons _ _ first rest => exact .cons first rest

theorem Forward.extend (step : Forward before a b) (extension : Extends before after) : Forward after a b := by
  induction step using Forward.rec
    (motive_2 := fun xs ys _ => NativeKernel.Conversion.ListRel (Forward after) xs ys) with
  | old original => exact .old (old_forward_extend original extension)
  | iota root => exact .iota (root.extend extension)
  | refl => exact .refl
  | trans _ _ first second => exact .trans first second
  | node op _ ih => exact .node op ih
  | nil => exact .nil
  | cons _ _ first rest => exact .cons first rest

end Jihoo.NativeKernel.Environment.FamilyIota.Extended
