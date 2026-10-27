/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.RationalGcdReduction

/-! # Canonical fraction components and positive integer-pair reconstruction -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- For a natural numerator and positive natural denominator, the raw fraction components
are a common positive natural multiple of its canonical numerator absolute value and denominator.
Extract the integer normalization factor and take absolute values; the numerator may be zero. -/
theorem fraction_scale_of_den_pos {a b : ℕ} (hb : 0 < b) :
    ∃ c : ℕ, 0 < c ∧ a = c * ((a : ℚ) / b).num.natAbs ∧ b = c * ((a : ℚ) / b).den := by
  have he : (a : ℚ) / b = Rat.divInt a b := by
    rw [Rat.divInt_eq_div, Int.cast_natCast, Int.cast_natCast]
  obtain ⟨c, hn, hd⟩ := Rat.num_den_mk (Int.natCast_ne_zero.mpr (ne_of_gt hb)) he
  have hc : c ≠ 0 := by
    intro hc
    rw [hc, zero_mul] at hd
    exact (Int.natCast_ne_zero.mpr (ne_of_gt hb)) hd
  have hn' := congrArg Int.natAbs hn
  have hd' := congrArg Int.natAbs hd
  simp only [Int.natAbs_natCast, Int.natAbs_mul] at hn' hd'
  exact ⟨c.natAbs, Int.natAbs_pos.mpr hc, hn', hd'⟩

/-- For a natural fraction with positive denominator, its canonical numerator divides the
raw numerator and its canonical denominator divides the raw denominator.
Use the common natural scaling factor; this supports exact integer-pair multiplicity counts. -/
theorem fraction_component_dvd_of_den_pos {a b : ℕ} (hb : 0 < b) :
    ((a : ℚ) / b).num.natAbs ∣ a ∧ ((a : ℚ) / b).den ∣ b := by
  obtain ⟨c, hc, hn, hd⟩ := fraction_scale_of_den_pos (a := a) hb
  exact ⟨⟨c, hn.trans (Nat.mul_comm _ _)⟩, ⟨c, hd.trans (Nat.mul_comm _ _)⟩⟩

/-- Two positive-denominator natural pairs with the same positive second coordinate and
rational ratio are equal. Cross multiply and cancel the positive second coordinate. -/
theorem nat_pair_eq_of_ratio_and_second {a b : ℕ × ℕ} (ha : 0 < a.1) (hb : 0 < b.1) (hy : 0 < a.2)
    (he : (a.2 : ℚ) / a.1 = (b.2 : ℚ) / b.1) (he2 : a.2 = b.2) : a = b := by
  apply Prod.ext
  · have hc :=
      (div_eq_div_iff (Nat.cast_ne_zero.mpr (ne_of_gt ha)) (Nat.cast_ne_zero.mpr (ne_of_gt hb))).mp
        he
    rw [← he2] at hc
    have hx := mul_left_cancel₀ (Nat.cast_ne_zero.mpr (ne_of_gt hy)) hc
    exact (Nat.cast_inj.mp hx).symm
  · exact he2

/-- Positive rationals with identical canonical numerator absolute values and denominators
are equal. Reconstruct each from its positive canonical fraction. -/
theorem positive_rat_eq_of_num_den {q t : ℚ} (hq : 0 < q) (ht : 0 < t)
    (hn : q.num.natAbs = t.num.natAbs) (hd : q.den = t.den) : q = t := by
  calc
    q = (q.num.natAbs : ℚ) / q.den := positive_rat_nat_fraction hq
    _ = (t.num.natAbs : ℚ) / t.den := by rw [hn, hd]
    _ = t := (positive_rat_nat_fraction ht).symm

end PseudoPrime.NumberTheory.Heilbronn
