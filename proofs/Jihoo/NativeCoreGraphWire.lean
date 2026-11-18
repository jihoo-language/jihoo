import Jihoo.NativeCoreGraph
import Jihoo.NativeWireMachine

/-! The reference vector emitted by `core_native_snapshot.write_node` comes
from the same `Core.children` call used by `Core.extend`. Given the words
passed to that writer, the canonical snapshot parser and the reference scan
agree exactly, including the identity and order of each reference. The tag
and scalar fields are supplied by the production constructor match. -/
namespace Jihoo.NativeKernel.NativeCoreGraph
open GraphCertificates.Canonical NativeArena

structure NodeWords where
  tag : UInt64
  fields : List UInt64
  children : List UInt32

def NodeWords.fits (node : NodeWords) : Prop :=
  node.fields.length < 2^64 ∧ node.children.length < 2^64

def NodeWords.encode (node : NodeWords) : Bytes :=
  NativeWire.writeNodeWords [] node.tag node.fields node.children

def NodeWords.toNode (node : NodeWords) : Option Node :=
  let fields := node.fields.map UInt64.toNat
  let refs := node.children.map UInt32.toNat
  if node.tag.toNat = 0 then
    match fields, refs with
    | [index], [] => some (.var index)
    | _, _ => none
  else (NativeSchema.ofCode node.tag.toNat fields).map (fun op => .node op refs)

theorem parseNodeWords (words : NodeWords) (fits : words.fits) (rest : Bytes) :
    NativeWire.parseNode (words.encode ++ rest) = words.toNode.map (fun node => (node, rest)) := by
  rw [NodeWords.encode, NativeWire.writeNodeWords_refines _ _ _ _ fits.1 fits.2]
  simp only [List.nil_append, List.append_assoc, NativeWire.parseNode, parseNat_encode,
    parseList_encode encodeNat parseNat parseNat_encode, bind, Option.bind]
  change (words.toNode.bind fun node => some (node, rest)) = _
  cases words.toNode <;> rfl

theorem NodeWords.toNode_references {words : NodeWords} (parsed : words.toNode = some node) :
    node.references = words.children.map UInt32.toNat := by
  unfold NodeWords.toNode at parsed
  split at parsed
  · dsimp only at parsed
    split at parsed
    · next index fields children =>
        cases parsed
        simp [Node.references, children]
    · contradiction
  · cases code : NativeSchema.ofCode words.tag.toNat (words.fields.map UInt64.toNat) <;>
      simp [code] at parsed
    subst node
    rfl

private theorem parseManyWords (words : List NodeWords) (fits : ∀ n ∈ words, n.fits) (rest : Bytes) :
    parseMany NativeWire.parseNode words.length (encodeMany NodeWords.encode words ++ rest) =
      (words.mapM NodeWords.toNode).map (fun nodes => (nodes, rest)) := by
  induction words with
  | nil => rfl
  | cons node words ih =>
      have head := parseNodeWords node (fits _ (by simp)) (encodeMany NodeWords.encode words ++ rest)
      have tail := ih (fun n member => fits n (List.mem_cons_of_mem _ member))
      cases h₁ : node.toNode <;> cases h₂ : words.mapM NodeWords.toNode <;>
        simp [encodeMany, parseMany, List.append_assoc, head, tail, h₁, h₂, List.mapM_cons]

def encodeObservedProgram (definitions : List NativeProgramWire.Roots)
    (families : List NativeFamilyWire.FamilyRoots) (words : List NodeWords) : Bytes :=
  encodeNat 6 ++ encodeList NativeProgramWire.encodeRoots definitions ++
    encodeList NativeFamilyWire.encodeFamily families ++ encodeList NodeWords.encode words

theorem parseObservedProgram (definitions : List NativeProgramWire.Roots)
    (families : List NativeFamilyWire.FamilyRoots) (words : List NodeWords)
    (fits : ∀ n ∈ words, n.fits) (rest : Bytes) :
    NativeFamilyWire.parseSnapshot (encodeObservedProgram definitions families words ++ rest) =
      (words.mapM NodeWords.toNode).map (fun nodes =>
        (⟨definitions, families, nodes.toArray⟩, rest)) := by
  have parsed : parseList NativeWire.parseNode (encodeList NodeWords.encode words ++ rest) =
      (words.mapM NodeWords.toNode).map (fun nodes => (nodes, rest)) := by
    simpa [parseList, encodeList, List.append_assoc, parseNat_encode] using parseManyWords words fits rest
  cases nodes : words.mapM NodeWords.toNode <;>
    simp [NativeFamilyWire.parseSnapshot, encodeObservedProgram, List.append_assoc, parseNat_encode,
      parseList_encode _ _ NativeProgramWire.parseRoots_encode,
      parseList_encode _ _ NativeFamilyWire.parseFamily_encode, parsed, nodes]

private theorem mapM_references {words : List NodeWords} {nodes : List Node}
    (parsed : words.mapM NodeWords.toNode = some nodes) :
    nodes.map Node.references = words.map (fun word => word.children.map UInt32.toNat) := by
  induction words generalizing nodes with
  | nil => simp at parsed; subst nodes; rfl
  | cons word words ih =>
      cases h₁ : word.toNode <;> cases h₂ : words.mapM NodeWords.toNode <;>
        simp [List.mapM_cons, h₁, h₂] at parsed
      subst nodes
      simp only [List.map_cons, NodeWords.toNode_references h₁, ih h₂]

private def observedArena (words : List NodeWords) : Arena :=
  (words.map (fun word => Node.node .u64 (word.children.map UInt32.toNat))).toArray

/-- Run the graph check over just the native validator's observed references. -/
def checkObservedGraph (words : List NodeWords) (checkedNodes : Nat) : Except Error Unit :=
  checkGraph (observedArena words) checkedNodes

/-- For every checked prefix index, parsing the observed native writer bytes
gives exactly the same graph result as scanning the ordered native words. -/
theorem checkObservedGraph_parse (fits : ∀ n ∈ words, n.fits)
    (parsed : NativeFamilyWire.parseSnapshot (encodeObservedProgram definitions families words ++ rest) =
      some (snapshot, tail)) (checkedNodes : Nat) :
    checkObservedGraph words checkedNodes = checkGraph snapshot.arena checkedNodes := by
  rw [parseObservedProgram _ _ _ fits] at parsed
  cases decoded : words.mapM NodeWords.toNode with
  | none => simp [decoded] at parsed
  | some nodes =>
      simp [decoded] at parsed
      obtain ⟨rfl, rfl⟩ := parsed
      apply checkGraph_references
      rw [← Array.toList_inj]
      simp [observedArena, List.map_map, Node.references, mapM_references decoded]

/-- Loan64 acceptance of the observed version-6 writer bytes implies that the
native graph phase passes over the emitted ordered reference words. -/
theorem checkBytes_observedGraph (fits : ∀ n ∈ words, n.fits)
    (accepted : NativeLoanMixedAdmission.checkBytes fuel quantityFuel
      (encodeObservedProgram definitions families words).toByteArray = true) :
    checkObservedGraph words 0 = .ok () := by
  obtain ⟨snapshot, _, _, _, exactBytes, valid, backward, _⟩ :=
    NativeLoanMixedAdmission.checkBytes_sound accepted
  have encoded : NativeFamilyWire.encodeSnapshotList snapshot = encodeObservedProgram definitions families words := by
    have same := congrArg (fun bytes : ByteArray => bytes.data.toList) exactBytes
    simpa only [NativeFamilyWire.encodeSnapshot, List.toList_data_toByteArray] using same
  have parsed := NativeFamilyWire.parseSnapshot_encode snapshot []
  rw [encoded] at parsed
  rw [checkObservedGraph_parse fits parsed 0]
  have capacity := NativeWire.graphValid_size valid
  exact (checkGraph_full _).mpr ⟨by unfold entryLimit; omega, backward⟩

end Jihoo.NativeKernel.NativeCoreGraph
