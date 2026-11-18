import Jihoo.NativeWire

/-! The word-level serialization primitives in `compiler/core_native_snapshot.jh`.
The buffer is a sequence of bytes, and append models the writer's `String.push`
of ASCII bytes. The proofs cover every u64 token and i64 literal payload. -/
namespace Jihoo.NativeKernel.NativeWire
open GraphCertificates.Canonical

private theorem half_lt (value : UInt64) (nonzero : value ≠ 0) :
    (value / 2).toNat < value.toNat := by
  have positive : 0 < value.toNat := by
    simpa [Nat.pos_iff_ne_zero, ← UInt64.toNat_inj] using nonzero
  simpa [UInt64.toNat_div] using Nat.div_lt_self positive (by decide : 1 < 2)

def pushToken (out : Bytes) (value : UInt64) : Bytes :=
  if h : value = 0 then out ++ [59]
  else pushToken (out ++ [if value % 2 = 0 then 48 else 49]) (value / 2)
termination_by value.toNat
decreasing_by exact half_lt value h

theorem pushToken_refines (out : Bytes) (value : UInt64) :
    pushToken out value = out ++ encodeNat value.toNat := by
  rw [pushToken, encodeNat]
  by_cases zero : value = 0
  · simp [zero]
  · have nonzero : value.toNat ≠ 0 := by simpa [← UInt64.toNat_inj] using zero
    have parity : (value % 2 = 0) = (value.toNat % 2 = 0) := by
      simp [← UInt64.toNat_inj, UInt64.toNat_mod]
    simp only [zero, nonzero, dite_false, parity]
    rw [pushToken_refines]
    simp [UInt64.toNat_div, List.append_assoc]
termination_by value.toNat
decreasing_by exact half_lt value zero

def pushTokens (out : Bytes) (values : List UInt64) : Bytes := values.foldl pushToken out

theorem pushTokens_refines (out : Bytes) (values : List UInt64) :
    pushTokens out values = out ++ encodeMany encodeNat (values.map UInt64.toNat) := by
  induction values generalizing out with
  | nil => simp [pushTokens, encodeMany]
  | cons value values ih =>
      change pushTokens (pushToken out value) values = _
      simp [ih, pushToken_refines, encodeMany, List.append_assoc]

def writeNodeWords (out : Bytes) (tag : UInt64) (fields : List UInt64)
    (refs : List UInt32) : Bytes :=
  pushTokens out ([tag, UInt64.ofNat fields.length] ++ fields ++
    (UInt64.ofNat refs.length :: refs.map UInt32.toUInt64))

private theorem encodeMany_append (fields more : List Nat) :
    encodeMany encodeNat (fields ++ more) =
      encodeMany encodeNat fields ++ encodeMany encodeNat more := by
  induction fields with
  | nil => simp [encodeMany]
  | cons field fields ih => simp [encodeMany, ih, List.append_assoc]

/-- The `node` helper writes a tag followed by length-prefixed payload and
reference words. The two length casts must fit u64. -/
theorem writeNodeWords_refines (out : Bytes) (tag : UInt64) (fields : List UInt64)
    (refs : List UInt32) (fieldCount : fields.length < 2 ^ 64) (refCount : refs.length < 2 ^ 64) :
    writeNodeWords out tag fields refs = out ++ (encodeNat tag.toNat ++
      encodeList encodeNat (fields.map UInt64.toNat) ++ encodeList encodeNat (refs.map UInt32.toNat)) := by
  simp [writeNodeWords, pushTokens_refines, encodeMany_append, encodeMany, encodeList,
    Nat.mod_eq_of_lt fieldCount, Nat.mod_eq_of_lt refCount, List.map_map,
    Function.comp_def, UInt32.toNat_toUInt64, List.append_assoc]

/-- `0 -% value` is wrapping signed subtraction. Casting its word to u64
recovers the magnitude even when the signed result is `Int64.minValue`. -/
def integerPayloadWords (value : Int64) : List UInt64 :=
  if value < 0 then [1, (0 - value).toUInt64] else [0, value.toUInt64]

theorem integerPayloadWords_refines (value : Int64) :
    (integerPayloadWords value).map UInt64.toNat = NativeSchema.payload (.integer value.toInt) := by
  cases meaning : value.toInt with
  | ofNat magnitude =>
      have nonnegative : 0 ≤ value := by simp [Int64.le_iff_toInt_le, meaning]
      have notNegative : ¬ value < 0 := by simp [Int64.lt_iff_toInt_lt, meaning]
      have exactMagnitude : value.toUInt64.toNat = magnitude := by
        rw [Int64.toNat_toUInt64_of_le nonnegative, ← Int64.toNat_toInt, meaning]
        rfl
      change _ = [0, magnitude]
      simp only [integerPayloadWords, ite_eq_right notNegative, List.map_cons, List.map_nil,
        UInt64.toNat_zero, exactMagnitude]
  | negSucc magnitude =>
      have negative : value < 0 := by simp [Int64.lt_iff_toInt_lt, meaning]
      have magnitudeFits : magnitude + 1 < 2 ^ 64 := by
        have lower := value.le_toInt
        rw [meaning] at lower
        omega
      have wrapping : (0 - value).toUInt64 = UInt64.ofNat (magnitude + 1) := by
        rw [Int64.zero_sub, ← Int64.ofInt_toInt value, ← Int64.ofInt_neg, meaning]
        exact Int64.toUInt64_ofNat'
      change _ = [1, magnitude + 1]
      simp only [integerPayloadWords, ite_eq_left negative, List.map_cons, List.map_nil,
        UInt64.toNat_one, wrapping, UInt64.toNat_ofNat', Nat.mod_eq_of_lt magnitudeFits]

/-- The actual literal-node fields in the writer, including tag, lengths,
sign, and magnitude, produce the canonical version-4/5/6 node bytes. -/
theorem writeInteger_refines (out : Bytes) (value : Int64) :
    writeNodeWords out 48 (integerPayloadWords value) [] =
      out ++ encodeNode (.node (.integer value.toInt) []) := by
  have length : (integerPayloadWords value).length = 2 := by
    unfold integerPayloadWords
    split <;> rfl
  rw [writeNodeWords_refines _ _ _ _ (by rw [length]; decide) (by decide), integerPayloadWords_refines]
  rfl

theorem parseWrittenInteger (value : Int64) (rest : Bytes) :
    parseNode (writeNodeWords [] 48 (integerPayloadWords value) [] ++ rest) =
      some (.node (.integer value.toInt) [], rest) := by
  simpa only [writeInteger_refines, List.nil_append] using
    parseNode_encode (.node (.integer value.toInt) []) rest

end Jihoo.NativeKernel.NativeWire
