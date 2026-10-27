/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.HeightLayerRationalScales
public import PseudoPrime.NumberTheory.Heilbronn.RationalHeilbronnSmoothSupply

/-! # Fermat quotient witnesses at every logarithmic exponent above 116/63 -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- For every A>116/63, choose a rational scale between that lower endpoint
and min(A,2). Expose the positive natural denominator and numerator to fix
the layer parameters and thresholds before the prime varies. -/
theorem exists_rational_scale_above_height_layers {A : ℝ} (hA : (116 / 63 : ℝ) < A) :
    ∃ a t : ℕ, 0 < a ∧ 116 * a < 63 * t ∧ t < 2 * a ∧ (t : ℝ) / a < A := by
  have hint : (116 / 63 : ℝ) < min A 2 := lt_min hA (by norm_num only)
  obtain ⟨q, hlo, hhi⟩ := exists_rat_btwn hint
  have hq0 : (0 : ℝ) ≤ q := (lt_trans (by norm_num only : (0 : ℝ) < 116 / 63) hlo).le
  have hn : 0 ≤ q.num := Rat.num_nonneg.mpr (Rat.cast_nonneg.mp hq0)
  have he : (q.num.natAbs : ℝ) = (q.num : ℝ) := by
    simpa only [Int.cast_natCast] using
      congrArg (fun z : ℤ ↦ (z : ℝ)) ((Int.natCast_natAbs q.num).trans (abs_of_nonneg hn))
  rw [Rat.cast_def, ← he] at hlo hhi
  have haR : (0 : ℝ) < q.den := Nat.cast_pos.mpr q.pos
  have hgapR : (116 : ℝ) * q.den < 63 * q.num.natAbs := by
    have h := (lt_div_iff₀ haR).mp hlo
    nlinarith only [h]
  have hsmallR : (q.num.natAbs : ℝ) < 2 * q.den :=
    (div_lt_iff₀ haR).mp (hhi.trans_le (min_le_right A 2))
  refine ⟨q.den, q.num.natAbs, q.pos, ?_, ?_, hhi.trans_le (min_le_left A 2)⟩
  · apply Nat.cast_lt (α := ℝ).mp
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hgapR
  · apply Nat.cast_lt (α := ℝ).mp
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hsmallR

/-- For every fixed A>116/63, sufficiently large odd primes p have a prime
q<=log(p)^A with q^(p-1) nontrivial modulo p². Fix a rational scale below A,
combine its proved interval and smooth-count bounds, and extract a prime factor.
The threshold depends only on A; GRH and external Fermat estimates are absent. -/
theorem eventually_exists_prime_nontrivial_power_of_height_layers {A : ℝ}
    (hA : (116 / 63 : ℝ) < A) :
    Filter.Eventually
      (fun p : ℕ ↦
        p.Prime →
          p ≠ 2 → ∃ q : ℕ, q.Prime ∧ (q : ℝ) ≤ (Real.log p) ^ A ∧ (q : ZMod (p ^ 2)) ^ (p - 1) ≠ 1)
      Filter.atTop := by
  obtain ⟨a, t, ha, hgap, hsmall, hscale⟩ := exists_rational_scale_above_height_layers hA
  have hat : a < t := by nlinarith only [hgap, ha]
  have hκ : 1 < (t : ℝ) / a := (one_lt_div (Nat.cast_pos.mpr ha)).mpr (Nat.cast_lt.mpr hat)
  obtain ⟨P, hP⟩ := exists_uniform_height_layer_heilbronn_interval_bound ha hgap hsmall
  filter_upwards [eventually_smooth_count_at_rational_cutoff ha hκ hscale,
    Filter.eventually_ge_atTop P] with p hsm hlarge hp hp2
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk, hkp, hlo, hhi, hcount⟩ := hP p (hp.odd_of_ne_two hp2) hlarge
  obtain ⟨q, hq, hqB, hpow⟩ :=
    exists_prime_nontrivial_power_of_interval_and_smooth hcount (hsm k hk hlo hhi)
  have hB := Nat.lt_add_one_iff.mp hqB
  have hle : (q : ℝ) ≤ (Real.log p) ^ A :=
    (Nat.cast_le.mpr hB).trans
      (Nat.floor_le (Real.rpow_nonneg (Real.log_nonneg (Nat.one_le_cast.mpr hp.one_lt.le)) _))
  exact ⟨q, hq, hle, hpow⟩

end PseudoPrime.NumberTheory.Heilbronn
