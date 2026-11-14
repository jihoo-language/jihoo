import Jihoo.NativeContextualUniverseCodes
set_option maxUniverseOffset 40

/-! Generic finite-level Tarski code values for every native input universe.
The level-indexed operations reduce to the concrete previously verified
host universes; no semantic membership or normalization is an input. -/
namespace Jihoo.NativeKernel.Environment.Semantics.Finite.Values

def codeUniverse (level : Fin 32) : Universe (.type ⟨level.val+1,by omega⟩) :=
  match level with
  | ⟨0,_⟩ => Finite.universe0
  | ⟨1,_⟩ => Finite.universe1
  | ⟨2,_⟩ => Finite.universe2
  | ⟨3,_⟩ => Finite.universe3
  | ⟨4,_⟩ => Finite.universe4
  | ⟨5,_⟩ => Finite.universe5
  | ⟨6,_⟩ => Finite.universe6
  | ⟨7,_⟩ => Finite.universe7
  | ⟨8,_⟩ => Finite.universe8
  | ⟨9,_⟩ => Finite.universe9
  | ⟨10,_⟩ => Finite.universe10
  | ⟨11,_⟩ => Finite.universe11
  | ⟨12,_⟩ => Finite.universe12
  | ⟨13,_⟩ => Finite.universe13
  | ⟨14,_⟩ => Finite.universe14
  | ⟨15,_⟩ => Finite.universe15
  | ⟨16,_⟩ => Finite.universe16
  | ⟨17,_⟩ => Finite.universe17
  | ⟨18,_⟩ => Finite.universe18
  | ⟨19,_⟩ => Finite.universe19
  | ⟨20,_⟩ => Finite.universe20
  | ⟨21,_⟩ => Finite.universe21
  | ⟨22,_⟩ => Finite.universe22
  | ⟨23,_⟩ => Finite.universe23
  | ⟨24,_⟩ => Finite.universe24
  | ⟨25,_⟩ => Finite.universe25
  | ⟨26,_⟩ => Finite.universe26
  | ⟨27,_⟩ => Finite.universe27
  | ⟨28,_⟩ => Finite.universe28
  | ⟨29,_⟩ => Finite.universe29
  | ⟨30,_⟩ => Finite.universe30
  | ⟨31,_⟩ => Finite.universe31
  | ⟨n+32,bound⟩ => False.elim (by omega)

def decode (level : Fin 32) : Carrier (codeUniverse level) → Universe (.type ⟨level.val,by omega⟩) :=
  match level with
  | ⟨0,_⟩ => fun value => .type0 value.down
  | ⟨1,_⟩ => fun value => .type1 value.down
  | ⟨2,_⟩ => fun value => .type2 value.down
  | ⟨3,_⟩ => fun value => .type3 value.down
  | ⟨4,_⟩ => fun value => .type4 value.down
  | ⟨5,_⟩ => fun value => .type5 value.down
  | ⟨6,_⟩ => fun value => .type6 value.down
  | ⟨7,_⟩ => fun value => .type7 value.down
  | ⟨8,_⟩ => fun value => .type8 value.down
  | ⟨9,_⟩ => fun value => .type9 value.down
  | ⟨10,_⟩ => fun value => .type10 value.down
  | ⟨11,_⟩ => fun value => .type11 value.down
  | ⟨12,_⟩ => fun value => .type12 value.down
  | ⟨13,_⟩ => fun value => .type13 value.down
  | ⟨14,_⟩ => fun value => .type14 value.down
  | ⟨15,_⟩ => fun value => .type15 value.down
  | ⟨16,_⟩ => fun value => .type16 value.down
  | ⟨17,_⟩ => fun value => .type17 value.down
  | ⟨18,_⟩ => fun value => .type18 value.down
  | ⟨19,_⟩ => fun value => .type19 value.down
  | ⟨20,_⟩ => fun value => .type20 value.down
  | ⟨21,_⟩ => fun value => .type21 value.down
  | ⟨22,_⟩ => fun value => .type22 value.down
  | ⟨23,_⟩ => fun value => .type23 value.down
  | ⟨24,_⟩ => fun value => .type24 value.down
  | ⟨25,_⟩ => fun value => .type25 value.down
  | ⟨26,_⟩ => fun value => .type26 value.down
  | ⟨27,_⟩ => fun value => .type27 value.down
  | ⟨28,_⟩ => fun value => .type28 value.down
  | ⟨29,_⟩ => fun value => .type29 value.down
  | ⟨30,_⟩ => fun value => .type30 value.down
  | ⟨31,_⟩ => fun value => .type31 value.down
  | ⟨n+32,bound⟩ => False.elim (by omega)

def encode (level : Fin 32) : Universe (.type ⟨level.val,by omega⟩) → Carrier (codeUniverse level) :=
  match level with
  | ⟨0,_⟩ => fun code => ⟨Finite.decode0 code⟩
  | ⟨1,_⟩ => fun code => ⟨Finite.decode1 code⟩
  | ⟨2,_⟩ => fun code => ⟨Finite.decode2 code⟩
  | ⟨3,_⟩ => fun code => ⟨Finite.decode3 code⟩
  | ⟨4,_⟩ => fun code => ⟨Finite.decode4 code⟩
  | ⟨5,_⟩ => fun code => ⟨Finite.decode5 code⟩
  | ⟨6,_⟩ => fun code => ⟨Finite.decode6 code⟩
  | ⟨7,_⟩ => fun code => ⟨Finite.decode7 code⟩
  | ⟨8,_⟩ => fun code => ⟨Finite.decode8 code⟩
  | ⟨9,_⟩ => fun code => ⟨Finite.decode9 code⟩
  | ⟨10,_⟩ => fun code => ⟨Finite.decode10 code⟩
  | ⟨11,_⟩ => fun code => ⟨Finite.decode11 code⟩
  | ⟨12,_⟩ => fun code => ⟨Finite.decode12 code⟩
  | ⟨13,_⟩ => fun code => ⟨Finite.decode13 code⟩
  | ⟨14,_⟩ => fun code => ⟨Finite.decode14 code⟩
  | ⟨15,_⟩ => fun code => ⟨Finite.decode15 code⟩
  | ⟨16,_⟩ => fun code => ⟨Finite.decode16 code⟩
  | ⟨17,_⟩ => fun code => ⟨Finite.decode17 code⟩
  | ⟨18,_⟩ => fun code => ⟨Finite.decode18 code⟩
  | ⟨19,_⟩ => fun code => ⟨Finite.decode19 code⟩
  | ⟨20,_⟩ => fun code => ⟨Finite.decode20 code⟩
  | ⟨21,_⟩ => fun code => ⟨Finite.decode21 code⟩
  | ⟨22,_⟩ => fun code => ⟨Finite.decode22 code⟩
  | ⟨23,_⟩ => fun code => ⟨Finite.decode23 code⟩
  | ⟨24,_⟩ => fun code => ⟨Finite.decode24 code⟩
  | ⟨25,_⟩ => fun code => ⟨Finite.decode25 code⟩
  | ⟨26,_⟩ => fun code => ⟨Finite.decode26 code⟩
  | ⟨27,_⟩ => fun code => ⟨Finite.decode27 code⟩
  | ⟨28,_⟩ => fun code => ⟨Finite.decode28 code⟩
  | ⟨29,_⟩ => fun code => ⟨Finite.decode29 code⟩
  | ⟨30,_⟩ => fun code => ⟨Finite.decode30 code⟩
  | ⟨31,_⟩ => fun code => ⟨Finite.decode31 code⟩
  | ⟨n+32,bound⟩ => False.elim (by omega)

theorem decode_encode (level : Fin 32) (code : Universe (.type ⟨level.val,by omega⟩)) :
    decode level (encode level code) = code := by
  rcases level with ⟨n,bound⟩
  have possibilities : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 ∨ n = 16 ∨ n = 17 ∨ n = 18 ∨ n = 19 ∨ n = 20 ∨ n = 21 ∨ n = 22 ∨ n = 23 ∨ n = 24 ∨ n = 25 ∨ n = 26 ∨ n = 27 ∨ n = 28 ∨ n = 29 ∨ n = 30 ∨ n = 31 := by omega
  rcases possibilities with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31
  all_goals subst n; cases code; rfl

theorem encode_decode (level : Fin 32) (value : Carrier (codeUniverse level)) :
    encode level (decode level value) = value := by
  rcases level with ⟨n,bound⟩
  have possibilities : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 ∨ n = 16 ∨ n = 17 ∨ n = 18 ∨ n = 19 ∨ n = 20 ∨ n = 21 ∨ n = 22 ∨ n = 23 ∨ n = 24 ∨ n = 25 ∨ n = 26 ∨ n = 27 ∨ n = 28 ∨ n = 29 ∨ n = 30 ∨ n = 31 := by omega
  rcases possibilities with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31
  all_goals subst n; cases value; rfl

theorem native_level (level : Fin 32) :
    (LevelSort.type ⟨level.val,by omega⟩).native = SortTag.type level.val := rfl

theorem universe_native_sort (level : Fin 32) :
    (LevelSort.type ⟨level.val+1,by omega⟩).native = SortTag.type (level.val+1) := rfl

theorem universe_input_bound (level : Fin 32) : level.val < 32 := level.isLt


def empty (level : Fin 32) : Universe (.type ⟨level.val,by omega⟩) :=
  match level with
  | ⟨0,_⟩ => .type0 (ULift.{0} Empty)
  | ⟨1,_⟩ => .type1 (ULift.{1} Empty)
  | ⟨2,_⟩ => .type2 (ULift.{2} Empty)
  | ⟨3,_⟩ => .type3 (ULift.{3} Empty)
  | ⟨4,_⟩ => .type4 (ULift.{4} Empty)
  | ⟨5,_⟩ => .type5 (ULift.{5} Empty)
  | ⟨6,_⟩ => .type6 (ULift.{6} Empty)
  | ⟨7,_⟩ => .type7 (ULift.{7} Empty)
  | ⟨8,_⟩ => .type8 (ULift.{8} Empty)
  | ⟨9,_⟩ => .type9 (ULift.{9} Empty)
  | ⟨10,_⟩ => .type10 (ULift.{10} Empty)
  | ⟨11,_⟩ => .type11 (ULift.{11} Empty)
  | ⟨12,_⟩ => .type12 (ULift.{12} Empty)
  | ⟨13,_⟩ => .type13 (ULift.{13} Empty)
  | ⟨14,_⟩ => .type14 (ULift.{14} Empty)
  | ⟨15,_⟩ => .type15 (ULift.{15} Empty)
  | ⟨16,_⟩ => .type16 (ULift.{16} Empty)
  | ⟨17,_⟩ => .type17 (ULift.{17} Empty)
  | ⟨18,_⟩ => .type18 (ULift.{18} Empty)
  | ⟨19,_⟩ => .type19 (ULift.{19} Empty)
  | ⟨20,_⟩ => .type20 (ULift.{20} Empty)
  | ⟨21,_⟩ => .type21 (ULift.{21} Empty)
  | ⟨22,_⟩ => .type22 (ULift.{22} Empty)
  | ⟨23,_⟩ => .type23 (ULift.{23} Empty)
  | ⟨24,_⟩ => .type24 (ULift.{24} Empty)
  | ⟨25,_⟩ => .type25 (ULift.{25} Empty)
  | ⟨26,_⟩ => .type26 (ULift.{26} Empty)
  | ⟨27,_⟩ => .type27 (ULift.{27} Empty)
  | ⟨28,_⟩ => .type28 (ULift.{28} Empty)
  | ⟨29,_⟩ => .type29 (ULift.{29} Empty)
  | ⟨30,_⟩ => .type30 (ULift.{30} Empty)
  | ⟨31,_⟩ => .type31 (ULift.{31} Empty)
  | ⟨n+32,bound⟩ => False.elim (by omega)

theorem empty_uninhabited (level : Fin 32) : ¬ Nonempty (Carrier (empty level)) := by
  rcases level with ⟨n,bound⟩
  have possibilities : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 ∨ n = 16 ∨ n = 17 ∨ n = 18 ∨ n = 19 ∨ n = 20 ∨ n = 21 ∨ n = 22 ∨ n = 23 ∨ n = 24 ∨ n = 25 ∨ n = 26 ∨ n = 27 ∨ n = 28 ∨ n = 29 ∨ n = 30 ∨ n = 31 := by omega
  rcases possibilities with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31
  all_goals subst n; intro inhabited; obtain ⟨value⟩ := inhabited; exact value.down.down.elim

end Jihoo.NativeKernel.Environment.Semantics.Finite.Values
