import Jihoo.NativeCoreGhostSpineInference

/-! The recursive ghost visitor follows all four combinations of a
constant or dependent motive and one-level or recursive borrowed View. -/
namespace Jihoo.NativeKernel.NativeCoreGhostViewInference.Examples

open NativeArena NativeFamilyWire Environment
open NativeCoreGhostSpineInference (Inferred)

private def owner : Term := .node (.ind 0 0) []
private def declaration : FamilyDeclaration := ⟨true,0,0,[owner,.pi false owner owner],0⟩
private def entry : CheckedFamily := ⟨declaration,[⟨[],[]⟩,⟨[⟨false,owner,some []⟩],[]⟩],true⟩
private def env : Environment := ⟨#[],#[entry]⟩
private def row : FamilyRoots := ⟨true,0,0,0,[1,2]⟩

private def initial (dependent recursive : Bool) : Arena := #[
  .node .u64 [],.node (.ind 0 0) [],.node (.pi false) [1,1],.node .ref [1],.node (.lam false) [3,0],
  .node (.natural 0) [],.node (.lam false) [0,5],.node (.lam false) [3,5],.node (.lam false) [3,6],
  .node (.con 0 0 0) [],.node .borrow [9],
  .node (.view recursive 0 2) [if dependent then 4 else 0,5,if recursive then 8 else 7,10],
  .node (.universe 0) [],.node (.universe 0) [],.node (.universe 0) []]

private def constructors (family constructor : Nat) : Option Nat :=
  if family = 0 then row.constructors[constructor]? else none

private def visibleFamily (family : Nat) : Option NativeCoreGhostFamilyElimination.VisibleFamily :=
  if family = 0 then some ⟨row,true,[]⟩ else none

private def observe (limit : Nat) (dependent recursive : Bool) :=
  let normal := NativeCoreExpandedFamilies.run env [row] [] 0 limit
  let inferred := NativeCoreGhostSpineInference.runWithFamilyViews normal env [] 0 limit
    (fun id => id == 0) (fun id => id == 0) (fun id => if id = 0 then some (0,true) else none)
    constructors visibleFamily 16 [] ⟨initial dependent recursive,0⟩ 11
  (inferred.state.steps,inferred.state.arena.size,inferred.result.map Inferred.typeRoot,
    match inferred.result with
    | .ok answer => inferred.state.arena[answer.typeRoot]?
    | .error _ => none)

/-- Both constant motives return the original type root, and both dependent
results point to the application of the written motive to the original
borrow. The checker consumes the same budget as native for each result. -/
theorem recursive_ghost_view_matches_native :
    observe 41 false false = (41,27,.ok 0,some (.node .u64 [])) ∧
    observe 51 false true = (51,30,.ok 0,some (.node .u64 [])) ∧
    observe 94 true false = (94,41,.ok 40,some (.node .app [4,10])) ∧
    observe 114 true true = (114,47,.ok 46,some (.node .app [4,10])) := by cbv

end Jihoo.NativeKernel.NativeCoreGhostViewInference.Examples
