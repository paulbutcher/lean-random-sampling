/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSampling.Nat

/-! The uniform draw builds its float from the bit pattern rather than by dividing, so its value is exact
and the same on every platform, and its bounds follow from Lean's own model of `Float`. -/

namespace RandomSampling

open Float.Model UnpackedFloat

/-- The bits of the binary64 float `n * 2^-53`, for `n` in `1..2^53-1`. The exponent field is clamped to
`970..1022` so every `n` gives a positive normal float below 1. -/
def unitBits (n : Nat) : UInt64 :=
  let e := min n.log2 52
  ((e + 970) * 2 ^ 52 + n * 2 ^ (52 - e) % 2 ^ 52).toUInt64

theorem unitBits_toNat (n : Nat) :
    (unitBits n).toNat = (min n.log2 52 + 970) * 2 ^ 52 + n * 2 ^ (52 - min n.log2 52) % 2 ^ 52 := by
  simp only [unitBits, Nat.toUInt64, UInt64.toNat_ofNat']
  have := Nat.mod_lt (n * 2 ^ (52 - min n.log2 52)) (show 0 < 2 ^ 52 by decide)
  generalize n * 2 ^ (52 - min n.log2 52) % 2 ^ 52 = t at *
  omega

theorem unitBits_exponent (n : Nat) : (unitBits n).toNat / 2 ^ 52 = min n.log2 52 + 970 := by
  rw [unitBits_toNat]
  have := Nat.mod_lt (n * 2 ^ (52 - min n.log2 52)) (show 0 < 2 ^ 52 by decide)
  generalize n * 2 ^ (52 - min n.log2 52) % 2 ^ 52 = t at *
  omega

private theorem exponent_toNat (b : UInt64) :
    (unpackExponent (spec := Format.binary64) b.toBitVec).toNat = b.toNat / 2 ^ 52 % 2 ^ 11 := by
  simp [unpackExponent, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

private theorem mantissa_toNat (b : UInt64) :
    (1#1 ++ unpackMantissa (spec := Format.binary64) b.toBitVec).toNat = 2 ^ 52 + b.toNat % 2 ^ 52 := by
  have := Nat.two_pow_add_eq_or_of_lt (i := 52) (Nat.mod_lt b.toNat (by decide)) 1
  have hm : (unpackMantissa (spec := Format.binary64) b.toBitVec).toNat = b.toNat % 2 ^ 52 := by
    simp [unpackMantissa, BitVec.extractLsb'_toNat]
  rw [BitVec.toNat_append, hm]
  show 1 <<< 52 ||| _ = _
  rw [Nat.shiftLeft_eq, Nat.one_mul, ← Nat.mul_one (2 ^ 52), ← this]

private theorem valid_of_exponent (b : UInt64) (h : b.toNat / 2 ^ 52 < 1023) :
    Format.binary64.Valid b.toBitVec :=
  ⟨fun he _ => by have := congrArg BitVec.toNat he; simp [exponent_toNat] at this; omega⟩

/-- The float of `unitBits n`, which is `n * 2^-53` for `n` in `1..2^53-1`. -/
def unitFloat (n : Nat) : Float :=
  .ofModel ⟨unitBits n, valid_of_exponent _ (by rw [unitBits_exponent]; omega)⟩

private theorem unpack_normal (b : UInt64) (hv : Format.binary64.Valid b.toBitVec)
    (h0 : 0 < b.toNat / 2 ^ 52) (h1 : b.toNat / 2 ^ 52 < 1023) :
    ∃ h, (Float.Model.mk b hv).unpack =
      .finite .positive (2 ^ 52 + b.toNat % 2 ^ 52) ((b.toNat / 2 ^ 52 : Nat) - 1075) h := by
  have hne1 : unpackExponent (spec := Format.binary64) b.toBitVec ≠ -1#_ := by
    intro h; have := congrArg BitVec.toNat h; simp [exponent_toNat] at this; omega
  have hne0 : unpackExponent (spec := Format.binary64) b.toBitVec ≠ 0#_ := by
    intro h; have := congrArg BitVec.toNat h; simp [exponent_toNat] at this; omega
  have hs : unpackSign (spec := Format.binary64) b.toBitVec = 0#1 :=
    BitVec.eq_of_toNat_eq (by
      have := b.toNat_lt
      simp [unpackSign, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]; omega)
  refine ⟨by omega, ?_⟩
  simp only [Float.Model.unpack, UnpackedFloat.unpack, hne1, hne0, hs, ite_false,
    show Sign.ofBitVec 0#1 = .positive from rfl]
  congr 1
  · exact mantissa_toNat b
  · simp [exponent_toNat, Format.exponentBias]; omega

/-- The model's unpacked value of `unitFloat n` is `n * 2^(52 - e)` times `2^(e - 105)`, where `e` is
`n.log2`: that is `n * 2^-53` exactly. -/
theorem unitFloat_unpack (n : Nat) (h1 : 1 ≤ n) (h2 : n < 2 ^ 53) :
    ∃ h, (unitFloat n).toModel.unpack = .finite .positive (n * 2 ^ (52 - n.log2)) (n.log2 - 105) h := by
  have hn : n ≠ 0 := by omega
  have he : n.log2 < 53 := (Nat.log2_lt hn).2 h2
  have hlo : 2 ^ 52 ≤ n * 2 ^ (52 - n.log2) := by
    have := Nat.mul_le_mul_right (2 ^ (52 - n.log2)) (Nat.log2_self_le hn)
    rwa [← Nat.pow_add, show n.log2 + (52 - n.log2) = 52 by omega] at this
  have hhi : n * 2 ^ (52 - n.log2) < 2 ^ 53 := by
    have := Nat.mul_lt_mul_of_pos_right (Nat.lt_log2_self (n := n)) (Nat.two_pow_pos (52 - n.log2))
    rwa [← Nat.pow_add, show n.log2 + 1 + (52 - n.log2) = 53 by omega] at this
  have hb := unitBits_toNat n
  rw [show min n.log2 52 = n.log2 by omega] at hb
  obtain ⟨_, hu⟩ := unpack_normal (unitBits n) _ (by omega) (by omega)
  refine ⟨by omega, ?_⟩
  show (Float.Model.mk (unitBits n) _).unpack = _
  rw [hu]
  congr 1 <;> generalize n * 2 ^ (52 - n.log2) = t at * <;> omega

private theorem unitFloat_unpack_lt (n : Nat) :
    ∃ m e h, (unitFloat n).toModel.unpack = .finite .positive m e h ∧ e < -52 := by
  have hb := unitBits_exponent n
  obtain ⟨h, hu⟩ := unpack_normal (unitBits n) _ (by omega) (by omega)
  exact ⟨_, _, h, hu, by omega⟩

theorem unitFloat_pos (n : Nat) : 0 < unitFloat n := by
  obtain ⟨m, e, h, hu, _⟩ := unitFloat_unpack_lt n
  show Float.Model.lt _ _ = true
  simp only [Float.Model.lt, hu, show (0 : Float).toModel.unpack = .zero .positive from rfl]
  rfl

theorem unitFloat_lt_one (n : Nat) : unitFloat n < 1 := by
  obtain ⟨m, e, h, hu, he⟩ := unitFloat_unpack_lt n
  show Float.Model.lt _ _ = true
  simp only [Float.Model.lt, hu,
    show (1 : Float).toModel.unpack = .finite .positive (2 ^ 52) (-52) (by decide) from rfl]
  simp [UnpackedFloat.lt, UnpackedFloat.compare, compare, compareOfLessAndEq, he]

/-- A float drawn uniformly from the `2^53 - 1` values `n * 2^-53` for `n` in `1..2^53-1`, so strictly
inside (0, 1). -/
def uniform {γ : Type} [RandomGen γ] (g : γ) : Float × γ :=
  let (n, g) := nat g 1 (2 ^ 53 - 1)
  (unitFloat n, g)

theorem uniform_eq {γ : Type} [RandomGen γ] (g : γ) :
    uniform g = (unitFloat (nat g 1 (2 ^ 53 - 1)).1, (nat g 1 (2 ^ 53 - 1)).2) := rfl

theorem uniform_pos {γ : Type} [RandomGen γ] (g : γ) : 0 < (uniform g).1 := unitFloat_pos _

theorem uniform_lt_one {γ : Type} [RandomGen γ] (g : γ) : (uniform g).1 < 1 := unitFloat_lt_one _

/-- The result is exactly `n * 2^-53` for an `n` in `1..2^53-1`, as `unitFloat_unpack` states. -/
theorem uniform_resolution {γ : Type} [RandomGen γ] (g : γ) :
    ∃ n, 1 ≤ n ∧ n < 2 ^ 53 ∧ (uniform g).1 = unitFloat n := by
  have := nat_mem g 1 (2 ^ 53 - 1) (by decide)
  exact ⟨_, this.1, by omega, rfl⟩

end RandomSampling
