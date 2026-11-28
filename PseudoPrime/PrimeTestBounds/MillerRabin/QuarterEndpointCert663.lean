/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPowerGain663
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.TruncatedEulerCertificates3
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterProfile663

/-! # Rational certificates for the section 137 endpoint comparison -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem exp_upper (x u : ℚ) (hx : |x| ≤ 11) (hu : profileExpTaylor x + 1 / 10 ^ 16 ≤ u) :
    Real.exp (x : ℝ) ≤ (u : ℝ) := by
  have ht := profile_exp_error x (by exact_mod_cast hx)
  have h := (Rat.cast_le (K := ℝ)).mpr hu
  simp only [Rat.cast_add, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] at h
  linarith only [h, (abs_le.mp ht).2]

private theorem support_exp_upper : Real.exp (21 / 8 : ℝ) ≤ 13.80457418606710 := by
  have h := exp_upper (21 / 8) 13.80457418606710 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] using h

private theorem normalization_exp_upper :
    Real.exp (-(11 / 10 : ℝ) * (21 / 8)) ≤ 0.05571532696350 := by
  have h := exp_upper (-(231 / 80)) 0.05571532696350 (by decide +kernel) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
  exact h

/-- An upper support index follows from a rational bound on the exponential
of the kernel shift. The inequality is strict before taking the floor. -/
theorem quarter_support_floor_663 (N B : ℕ) (h : ((N : ℚ) + 1) * 13.80457418606710 < (B : ℚ) + 1) :
    ⌊((N : ℝ) + 1) * Real.exp (21 / 8)⌋₊ ≤ B := by
  have hR := (Rat.cast_lt (K := ℝ)).mpr h
  simp only [Rat.cast_mul, Rat.cast_add, Rat.cast_natCast, Rat.cast_one,
    Rat.cast_ofScientific] at hR
  have hN : 0 ≤ (N : ℝ) + 1 := by positivity
  have ht := (mul_le_mul_of_nonneg_left support_exp_upper hN).trans_lt hR
  exact
    Nat.lt_succ_iff.mp
      ((Nat.floor_lt (mul_nonneg hN (Real.exp_pos _).le)).mpr
        (by simpa only [Nat.cast_succ] using ht))

/-- Use an upper enclosure for the negative rational power of the endpoint
to obtain an upper normalization for the five-degree kernel weight. -/
theorem quarter_endpoint_norm_663 (N : ℕ) {p : ℚ}
    (hp :
      AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck ((N : ℚ) + 1) 0 p 11 10 = true) :
    (11 / 10 : ℝ) ^ 5 / 120 * Real.exp (-(11 / 10) * (21 / 8)) * ((N : ℝ) + 1) ^ (-(11 / 10) : ℝ) ≤
      (((11 / 10 : ℚ) ^ 5 / 120 * 0.05571532696350 * p : ℚ) : ℝ) := by
  have h := (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound hp).2
  simp only [Rat.cast_add, Rat.cast_natCast, Rat.cast_one, Nat.cast_ofNat, neg_div] at h
  simp only [Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_ofScientific]
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left normalization_exp_upper (by norm_num only)
  · exact h
  · positivity
  · positivity

/-- A rational inequality for the two endpoint square roots and the
weighted sum implies the required real endpoint comparison. -/
theorem quarter_endpoint_compare_663 {N : ℕ} {A lo hi : ℚ} (hlo : 0 ≤ lo) (hhi : 0 ≤ hi)
    (hs₁ : lo ^ 2 ≤ (N : ℚ)) (hs₂ : (N : ℚ) + 1 ≤ hi ^ 2)
    (h :
      4 * (A - lo * 0.088044185448) ≤
        0.055701529 + 0.0219746789 * (663 / 2 - hi) + (if 108736 ≤ N then 0.004377 else 0)) :
    4 * ((A : ℝ) - Real.sqrt N * 0.088044185448) ≤
      0.055701529 + 0.0219746789 * (663 / 2 - Real.sqrt ((N : ℝ) + 1)) +
        (if 108736 ≤ N then 0.004377 else 0) := by
  have hl := Real.sqrt_le_sqrt (by exact_mod_cast hs₁ : (lo : ℝ) ^ 2 ≤ N)
  have hu := Real.sqrt_le_sqrt (by exact_mod_cast hs₂ : (N : ℝ) + 1 ≤ (hi : ℝ) ^ 2)
  rw [Real.sqrt_sq (Rat.cast_nonneg.mpr hlo)] at hl
  rw [Real.sqrt_sq (Rat.cast_nonneg.mpr hhi)] at hu
  have hR := (Rat.cast_le (K := ℝ)).mpr h
  simp only [Rat.cast_sub, Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat,
    Rat.cast_ofScientific] at hR
  by_cases hf : 108736 ≤ N
  · simp only [ite_eq_left hf, Rat.cast_ofScientific] at hR ⊢
    linarith only [hR, hl, hu]
  · simp only [ite_eq_right hf, Rat.cast_zero] at hR ⊢
    linarith only [hR, hl, hu]

/-- Verifying the scalar enclosures and the six cumulative moment differences
at one integer endpoint suffices for its part of the real-radius comparison. -/
theorem quarter_endpoint_certified_663 (N B jB : ℕ) (hNB : N ≤ B) {z p lo hi : ℚ} (hz : 0 ≤ z)
    (hsupport : ((N : ℚ) + 1) * 13.80457418606710 < (B : ℚ) + 1)
    (hu : Analysis.rationalLogIntervalCheck ((N : ℚ) + 1) 17 22 0 (z + 12 - 21 / 8) = true)
    (hB : Analysis.rationalLogIntervalCheck (B : ℚ) jB 22 0 (z + 12) = true)
    (hp : AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck ((N : ℚ) + 1) 0 p 11 10 = true)
    (hlo : 0 ≤ lo) (hhi : 0 ≤ hi) (hs₁ : lo ^ 2 ≤ (N : ℚ)) (hs₂ : (N : ℚ) + 1 ≤ hi ^ 2) (M : ℕ → ℚ)
    (hM :
      ∀ j ∈ Finset.range 6, quarterMangoldtPrefix663 B j - quarterMangoldtPrefix663 N j ≤ (M j : ℝ))
    (h :
      let A :=
        ((11 / 10 : ℚ) ^ 5 / 120 * 0.05571532696350 * p) *
          ∑ j ∈ Finset.range 6, (Nat.choose 5 j : ℚ) * z ^ (5 - j) * M j
      4 * (A - lo * 0.088044185448) ≤
        0.055701529 + 0.0219746789 * (663 / 2 - hi) + (if 108736 ≤ N then 0.004377 else 0)) :
    let u := (N : ℝ) + 1
    4 *
        ((∑ n ∈ Finset.Ioc N ⌊u * Real.exp (21 / 8)⌋₊,
            ArithmeticFunction.vonMangoldt n * quarterWeight656 u n) -
          Real.sqrt N * 0.088044185448) ≤
      0.055701529 + 0.0219746789 * (663 / 2 - Real.sqrt u) +
        (if 108736 ≤ N then 0.004377 else 0) := by
  intro u
  have hu₀ : 0 < u := by
    dsimp only [u]; positivity
  have hlog := (Analysis.rationalLogIntervalCheck_sound hu).2
  have hlogB := (Analysis.rationalLogIntervalCheck_sound hB).2
  simp only [Rat.cast_add, Rat.cast_sub, Rat.cast_div, Rat.cast_natCast,
    Rat.cast_ofNat] at hlog hlogB
  have hB₀ : 0 < (B : ℝ) := by
    have hq := (of_decide_eq_true hB).1
    exact_mod_cast hq
  have hsum :=
    quarter_endpoint_rational_le_663 hu₀ hNB (quarter_support_floor_663 N B hsupport) hz
      (by
        dsimp only [u]; linarith only [hlog])
      (quarter_endpoint_norm_663 N hp) ((Real.log_le_iff_le_exp hB₀).mp hlogB) M hM
  exact
    (mul_le_mul_of_nonneg_left (sub_le_sub_right hsum _) (by norm_num only : (0 : ℝ) ≤ 4)).trans
      (quarter_endpoint_compare_663 hlo hhi hs₁ hs₂ h)

end PseudoPrime.PrimeTestBounds.MillerRabin
