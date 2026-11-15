import Jihoo.NativeLendRawPolicies

/-! Explicit embeddings for clients of the unconditional raw Lend theory.
Installing it as a source typing/evaluator alias remains a separate task. -/
namespace Jihoo.NativeKernel.Environment.RawLend

theorem Conv.legacy (converted : NativeKernel.Conversion.Conv a b) : Conv env a b := .old (.legacy converted)
theorem Conv.acu (converted : ACU.Conv a b) : Conv env a b := .old (.acu converted)
theorem Conv.delta (found : env.globals[index]? = some declaration) :
    Conv env (.node (.global index) []) declaration.value := .old (.delta found)
theorem Conv.iota (root : FamilyIota.Root env a b) : Conv env a b := .old (.iota root)

theorem Forward.acu (step : ACU.MixedRed a b) : Forward env a b := .old (.old (.acu step))
theorem Forward.delta (found : env.globals[index]? = some declaration) :
    Forward env (.node (.global index) []) declaration.value := .old (.old (.delta found))
theorem Forward.iota (root : FamilyIota.Root env a b) : Forward env a b := .old (.iota root)

theorem Conv.ofForwardJoin (left : Forward env a common) (right : Forward env b common) : Conv env a b :=
  left.toConv.trans right.toConv.symm

theorem Conv.ofProjected (converted : FamilyIota.Extended.Conv env (project env a) (project env b)) : Conv env a b :=
  (project_forward env a).toConv.trans ((Conv.old converted).trans (project_forward env b).toConv.symm)

theorem conv_iff_projection (admissible : EnvironmentDelta.Admissible env) :
    Conv env a b ↔ FamilyIota.Extended.Conv env (project env a) (project env b) :=
  ⟨fun converted => converted.projected admissible,Conv.ofProjected⟩

end Jihoo.NativeKernel.Environment.RawLend
