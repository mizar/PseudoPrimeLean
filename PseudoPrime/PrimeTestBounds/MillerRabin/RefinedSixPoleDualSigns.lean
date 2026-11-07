/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleDualEuler
public import PseudoPrime.Analysis.LogDirichletNumericalBounds

/-! # Nonnegative inverse-scale arithmetic weights -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The nonnegative Mangoldt weight in the inverse-scale sixth-pole series.
At zero the square-root denominator makes the weight zero. -/
noncomputable def refinedDualWeight (x : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n / Real.sqrt n *
    Analysis.rationalPoleProfile 3 (25 / 54) (21 / 16) (((n : ℝ) * x)⁻¹)

/-- On the interval `(0, 1]`, the sixth-pole profile is its explicit power
and logarithm expression. The factor `(27/25)^5` records the normalization
of the kernel used in this development. -/
theorem refined_profile_explicit {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    Analysis.rationalPoleProfile 3 (25 / 54) (21 / 16) u =
      ((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8))) * u ^ (27 / 25 : ℝ) *
        ((21 / 8 : ℝ) - Real.log u) ^ 5 := by
  have hl : Real.log u ≤ 0 := Real.log_nonpos hu.le hu1
  have hcut : Real.log u ≤ 2 * (21 / 16 : ℝ) := by linarith only [hl]
  unfold Analysis.rationalPoleProfile
  rw [ite_eq_left ⟨hu, hcut⟩]
  norm_num only [show 2 * 3 - 1 = 5 by decide, Nat.factorial]
  have he :
    -(((21 / 8 : ℝ) - Real.log u) / (25 / 27)) = -(567 / 200 : ℝ) + (27 / 25 : ℝ) * Real.log u := by
    ring
  rw [he, Real.exp_add, Real.rpow_def_of_pos hu]
  rw [mul_comm (Real.log u) (27 / 25 : ℝ)]
  ring

/-- The conductor profile at inverse scale has the explicit sixth-pole
formula. This keeps the normalized scale factor and logarithmic fifth power. -/
theorem refined_conductor_profile {x : ℝ} (hx : 1 ≤ x) :
    Analysis.rationalPoleProfile 3 (25 / 54) (21 / 16) x⁻¹ =
      ((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8))) * x ^ (-(27 / 25 : ℝ)) *
        ((21 / 8 : ℝ) + Real.log x) ^ 5 := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  rw [refined_profile_explicit (inv_pos.mpr hx0) ((inv_le_one₀ hx0).mpr hx), Real.log_inv,
    Real.inv_rpow hx0.le, ← Real.rpow_neg hx0.le]
  congr 1
  ring

/-- For `x ≥ 1` and `n ≥ 1`, the inverse-scale weight has the explicit
logarithmic form used in the scalar majorant. The kernel normalization is
retained exactly, and no estimate on the Mangoldt function is used. -/
theorem refined_dual_weight_explicit {x : ℝ} (hx : 1 ≤ x) {n : ℕ} (hn : 1 ≤ n) :
    refinedDualWeight x n =
      ArithmeticFunction.vonMangoldt n / Real.sqrt n *
        (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8))) *
          (((n : ℝ) * x)⁻¹) ^ (27 / 25 : ℝ) *
          ((21 / 8 : ℝ) + Real.log x + Real.log n) ^ 5) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnx : (1 : ℝ) ≤ (n : ℝ) * x := one_le_mul_of_one_le_of_one_le hn' hx
  have hpos : 0 < (n : ℝ) * x := lt_of_lt_of_le zero_lt_one hnx
  have hu : 0 < ((n : ℝ) * x)⁻¹ := inv_pos.mpr hpos
  have hu1 : ((n : ℝ) * x)⁻¹ ≤ 1 := (inv_le_one₀ hpos).mpr hnx
  unfold refinedDualWeight
  rw [refined_profile_explicit hu hu1, Real.log_inv, Real.log_mul (by positivity) (by positivity)]
  congr 2
  ring

/-- The explicit inverse-scale weight is bounded by the logarithmic majorant
from the sixth-pole profile. The zero index is included, and the inequality
uses the standard bound of von Mangoldt by the logarithm. -/
theorem refined_dual_weight_log_bound {x : ℝ} (hx : 1 ≤ x) (n : ℕ) :
    refinedDualWeight x n ≤
      (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8)))) *
        (((21 / 8 : ℝ) + Real.log x + Real.log n) ^ 5 *
          ((Real.log n / Real.sqrt n) * (((n : ℝ) * x)⁻¹) ^ (27 / 25 : ℝ))) := by
  by_cases hn : n = 0
  · subst n
    simp only [refinedDualWeight, ArithmeticFunction.map_zero, Nat.cast_zero, Real.sqrt_zero,
      div_zero, zero_mul, Real.log_zero, mul_zero, le_refl]
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    rw [refined_dual_weight_explicit hx hn1]
    have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
    have hlogn : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    have hbase : 0 ≤ (21 / 8 : ℝ) + Real.log x + Real.log n := by linarith only [hlogx, hlogn]
    have hc : 0 ≤ ((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8))) := by
      positivity
    have hr : 0 ≤ (((n : ℝ) * x)⁻¹) ^ (27 / 25 : ℝ) := Real.rpow_nonneg (by positivity) _
    have hm :=
      div_le_div_of_nonneg_right (ArithmeticFunction.vonMangoldt_le_log (n := n))
        (Real.sqrt_nonneg n)
    have h := mul_le_mul_of_nonneg_right hm (mul_nonneg (mul_nonneg hc hr) (pow_nonneg hbase 5))
    nlinarith only [h]

/-- The inverse-scale arithmetic weight is nonnegative for all real scales and
natural indices, by nonnegativity of Mangoldt, the square root and the profile. -/
theorem refined_dual_weight_nonneg (x : ℝ) (n : ℕ) : 0 ≤ refinedDualWeight x n := by
  exact
    mul_nonneg (div_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n)) (Real.sqrt_nonneg _))
      (refined_six_pole_profile_nonneg _)

/-- The real reflected Dirichlet term factors into the real character value
and the nonnegative inverse-scale weight, including the zero index. -/
theorem refined_dual_factor {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) (n : ℕ) :
    (refinedDualTerm (fun n ↦ χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) x n).re =
      (χ n).re * refinedDualWeight x n := by
  by_cases hn : n = 0
  · subst n
    simp only [refinedDualTerm, ite_true, Complex.zero_re, refinedDualWeight, Nat.cast_zero,
      Real.sqrt_zero, div_zero, zero_mul, mul_zero]
  · have hp : (n : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt (n : ℝ) : ℂ) := by
      rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (Nat.cast_nonneg n)]
      push_cast
      rfl
    rw [refinedDualTerm, ite_eq_right hn, hp]
    simp only [div_eq_mul_inv, ← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero, refinedDualWeight]
    ring

/-- For positive scale, the real character-weighted inverse-scale series is
absolutely summable. Apply the real-part map to the reflected Dirichlet series. -/
theorem refined_dual_signed_summable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) : Summable (fun n : ℕ ↦ (χ n).re * refinedDualWeight x n) := by
  have hs :
    LSeriesSummable (fun n ↦ χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) (((17 / 16 : ℝ) : ℂ)) :=
    χ.LSeriesSummable_twist_vonMangoldt
      (show (1 : ℝ) < (((17 / 16 : ℝ) : ℂ)).re by norm_num only [Complex.ofReal_re])
  have h := Complex.reCLM.summable (refined_dual_summable hx hs)
  change
    Summable
      (fun n ↦ (refinedDualTerm (fun n ↦ χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) x n).re) at h
  exact h.congr (fun n ↦ refined_dual_factor χ x n)

/-- The principal inverse-scale weight is summable at positive scales. Apply
the signed summability theorem to the unique character modulo one. -/
theorem refined_dual_weight_summable {x : ℝ} (hx : 0 < x) : Summable (refinedDualWeight x) := by
  have h := refined_dual_signed_summable (1 : DirichletCharacter ℂ 1) hx
  apply h.congr
  intro n
  simp only [MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1)), Complex.one_re, one_mul]

/-- When three character real parts sum to at least minus one at every index,
the negative sum of their inverse-scale series is bounded by one principal
series. Nonnegativity and summability allow the pointwise comparison to be summed. -/
theorem refined_dual_three_lower {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) {x : ℝ}
    (hx : 0 < x) (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re) :
    -((∑' n : ℕ, (a n).re * refinedDualWeight x n) + (∑' n : ℕ, (b n).re * refinedDualWeight x n) +
          (∑' n : ℕ, (c n).re * refinedDualWeight x n)) ≤
      ∑' n : ℕ, refinedDualWeight x n := by
  have hA := refined_dual_signed_summable a hx
  have hB := refined_dual_signed_summable b hx
  have hC := refined_dual_signed_summable c hx
  have hW := refined_dual_weight_summable hx
  have hnonneg :
    0 ≤
      ∑' n : ℕ,
        (refinedDualWeight x n + (a n).re * refinedDualWeight x n +
          (b n).re * refinedDualWeight x n +
          (c n).re * refinedDualWeight x n) := by
    apply tsum_nonneg
    intro n
    have h := mul_le_mul_of_nonneg_right (ht n) (refined_dual_weight_nonneg x n)
    nlinarith only [h]
  rw [Summable.tsum_add ((hW.add hA).add hB) hC, Summable.tsum_add (hW.add hA) hB,
    Summable.tsum_add hW hA] at hnonneg
  linarith only [hnonneg]

/-- The real reflected ordinary-logarithmic-derivative integral at a positive
scale equals the character-weighted inverse-scale arithmetic series. -/
theorem refined_reflected_logDeriv_real {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            -logDeriv χ.LFunction (1 / 2 - (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) *
              (refinedSixPoleKernel.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
                (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)))).re =
      ∑' n : ℕ, (χ n).re * refinedDualWeight x n := by
  have hs :
    LSeriesSummable (fun n ↦ χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) (((17 / 16 : ℝ) : ℂ)) :=
    χ.LSeriesSummable_twist_vonMangoldt
      (show (1 : ℝ) < (((17 / 16 : ℝ) : ℂ)).re by norm_num only [Complex.ofReal_re])
  rw [refined_reflected_logDeriv_integral χ hx, Complex.re_tsum (refined_dual_summable hx hs)]
  exact tsum_congr (fun n ↦ refined_dual_factor χ x n)

/-- The real reflected ordinary-logarithmic-derivative integral. This is the
inverse-scale Euler term entering the asymmetric two-scale contour formula. -/
noncomputable def refinedReflectedEuler {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) :
    ℝ :=
  (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ,
        -logDeriv χ.LFunction (1 / 2 - (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) *
          (refinedSixPoleKernel.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
            (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)))).re

/-- The principal reflected Euler integral equals the nonnegative inverse-scale
arithmetic series at a positive scale. This identifies the quantity that must be
bounded explicitly in the refined witness estimate. -/
theorem refined_reflected_principal_eq {x : ℝ} (hx : 0 < x) :
    refinedReflectedEuler (1 : DirichletCharacter ℂ 1) x = ∑' n : ℕ, refinedDualWeight x n := by
  unfold refinedReflectedEuler
  rw [refined_reflected_logDeriv_real (1 : DirichletCharacter ℂ 1) hx]
  apply tsum_congr
  intro n
  simp only [MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1)), Complex.one_re, one_mul]

/-- The principal reflected Euler term is nonnegative at positive scales, since
all of its arithmetic weights are nonnegative. -/
theorem refined_reflected_principal_nonneg {x : ℝ} (hx : 0 < x) :
    0 ≤ refinedReflectedEuler (1 : DirichletCharacter ℂ 1) x := by
  rw [refined_reflected_principal_eq hx]
  exact tsum_nonneg (refined_dual_weight_nonneg x)

/-- A summable pointwise majorant bounds the principal reflected Euler term.
This isolates the scalar series estimate needed for an explicit numerical bound. -/
theorem refined_reflected_principal_le {x : ℝ} (hx : 0 < x) (majorant : ℕ → ℝ)
    (hm : Summable majorant) (hb : ∀ n, refinedDualWeight x n ≤ majorant n) :
    refinedReflectedEuler (1 : DirichletCharacter ℂ 1) x ≤ ∑' n, majorant n := by
  rw [refined_reflected_principal_eq hx]
  exact Summable.tsum_le_tsum hb (refined_dual_weight_summable hx) hm

/-- Split a fifth-power majorant for the principal reflected Euler term into two
summable scalar series. The factor sixteen is the convexity bound for the fifth
power; explicit estimates for the two scalar series remain to be supplied. -/
theorem refined_reflected_principal_split {x z C : ℝ} (hx : 0 < x) (hz : 0 ≤ z) (hC : 0 ≤ C)
    (w v : ℕ → ℝ) (hw : Summable w) (hv : Summable v) (hwn : ∀ n, 0 ≤ w n)
    (hvw : ∀ n, v n = (Real.log n) ^ 5 * w n)
    (hb : ∀ n, refinedDualWeight x n ≤ C * ((z + Real.log n) ^ 5 * w n)) :
    refinedReflectedEuler (1 : DirichletCharacter ℂ 1) x ≤
      C * 16 * (z ^ 5 * (∑' n, w n) + ∑' n, v n) := by
  have hsum := (hw.mul_left (z ^ 5)).add hv
  have hmaj := hsum.mul_left (C * 16)
  have hpoint : ∀ n, refinedDualWeight x n ≤ C * 16 * (z ^ 5 * w n + v n) := by
    intro n
    have hp : (z + Real.log n) ^ 5 ≤ 16 * (z ^ 5 + (Real.log n) ^ 5) := by
      simpa only [show 5 - 1 = 4 by decide, show (2 : ℝ) ^ 4 = 16 by norm_num only] using
        add_pow_le hz (Real.log_natCast_nonneg n) 5
    have h := mul_le_mul_of_nonneg_right hp (hwn n)
    have h' := mul_le_mul_of_nonneg_left h hC
    rw [hvw n]
    nlinarith only [hb n, h']
  apply (refined_reflected_principal_le hx _ hmaj hpoint).trans_eq
  rw [Summable.tsum_mul_left, Summable.tsum_add (hw.mul_left _) hv, Summable.tsum_mul_left]
  · exact hw
  · exact hsum

/-- The first logarithmic summand has the rational uniform bound `50/79`.
The logarithm is bounded by a positive real power and the powers cancel. -/
theorem refined_log_one_point_bound (n : ℕ) :
    Real.log n * (n : ℝ) ^ (-(79 / 50 : ℝ)) ≤ (50 / 79 : ℝ) := by
  by_cases hn : n = 0
  · subst n
    simp only [Nat.cast_zero, Real.log_zero, zero_mul]
    norm_num only
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hlog := Real.log_natCast_le_rpow_div n (show (0 : ℝ) < 79 / 50 by norm_num only)
    have hr : 0 ≤ (n : ℝ) ^ (-(79 / 50 : ℝ)) := Real.rpow_nonneg hnpos.le _
    have h := mul_le_mul_of_nonneg_right hlog hr
    have hcancel : (n : ℝ) ^ (79 / 50 : ℝ) * (n : ℝ) ^ (-(79 / 50 : ℝ)) = 1 := by
      rw [← Real.rpow_add hnpos]
      norm_num only [add_neg_cancel, Real.rpow_zero]
    have heq :
      (n : ℝ) ^ (79 / 50 : ℝ) / (79 / 50 : ℝ) * (n : ℝ) ^ (-(79 / 50 : ℝ)) = (50 / 79 : ℝ) := by
      rw [div_eq_mul_inv]
      calc
        _ = ((n : ℝ) ^ (79 / 50 : ℝ) * (n : ℝ) ^ (-(79 / 50 : ℝ))) * ((79 / 50 : ℝ))⁻¹ := by ring
        _ = _ := by
          rw [hcancel]; norm_num only
    exact h.trans_eq heq

/-- The sixth logarithmic summand has the rational uniform bound `(300/79)^6`.
Raise the elementary logarithm bound to the sixth power and cancel real powers. -/
theorem refined_log_six_point_bound (n : ℕ) :
    (Real.log n) ^ 6 * (n : ℝ) ^ (-(79 / 50 : ℝ)) ≤ (300 / 79 : ℝ) ^ 6 := by
  by_cases hn : n = 0
  · subst n
    simp only [Nat.cast_zero, Real.log_zero, zero_pow (by decide : 6 ≠ 0), zero_mul]
    positivity
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hlog := Real.log_natCast_le_rpow_div n (show (0 : ℝ) < 79 / 300 by norm_num only)
    have hpow := pow_le_pow_left₀ (Real.log_natCast_nonneg n) hlog 6
    have hr : (n : ℝ) ^ (-(79 / 50 : ℝ)) ≥ 0 := Real.rpow_nonneg hnpos.le _
    have h := mul_le_mul_of_nonneg_right hpow hr
    have hp : ((n : ℝ) ^ (79 / 300 : ℝ)) ^ 6 = (n : ℝ) ^ (79 / 50 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
      norm_num only
    have hcancel : (n : ℝ) ^ (79 / 50 : ℝ) * (n : ℝ) ^ (-(79 / 50 : ℝ)) = 1 := by
      rw [← Real.rpow_add hnpos]
      norm_num only [add_neg_cancel, Real.rpow_zero]
    rw [div_pow, hp] at h
    have heq :
      (n : ℝ) ^ (79 / 50 : ℝ) / (79 / 300 : ℝ) ^ 6 * (n : ℝ) ^ (-(79 / 50 : ℝ)) =
        (300 / 79 : ℝ) ^ 6 := by
      rw [div_eq_mul_inv]
      calc
        _ = ((n : ℝ) ^ (79 / 50 : ℝ) * (n : ℝ) ^ (-(79 / 50 : ℝ))) * ((79 / 300 : ℝ) ^ 6)⁻¹ := by
          ring
        _ = _ := by
          rw [hcancel]; norm_num only
    exact h.trans_eq heq

/-- The first fixed logarithmic Dirichlet series is bounded by the explicit
integral and maximum allowance at exponent `79/50`. Specialize the established
logarithmic integral comparison to `r = 29/50`. -/
theorem refined_log_one_tsum_bound :
    (∑' n : ℕ, Real.log n * (n : ℝ) ^ (-(79 / 50 : ℝ))) ≤ (50 / 29 : ℝ) ^ 2 + 50 / 79 := by
  have h := Analysis.tsum_logPower_le (r := 29 / 50) (by norm_num only)
  norm_num only [show -(29 / 50 : ℝ) - 1 = -(79 / 50 : ℝ) by norm_num only,
    show (29 / 50 : ℝ)⁻¹ = 50 / 29 by norm_num only,
    show (29 / 50 : ℝ) + 1 = 79 / 50 by norm_num only,
    show (79 / 50 : ℝ)⁻¹ = 50 / 79 by norm_num only] at h ⊢
  exact h

/-- The sixth logarithmic summand is bounded by a rational multiple of a
first logarithmic summand with exponent `129/100`. Five logarithmic factors
are dominated by a small positive real power. -/
theorem refined_log_six_reduction (n : ℕ) :
    (Real.log n) ^ 6 * (n : ℝ) ^ (-(79 / 50 : ℝ)) ≤
      (500 / 29 : ℝ) ^ 5 * (Real.log n * (n : ℝ) ^ (-(129 / 100 : ℝ))) := by
  by_cases hn : n = 0
  · subst n
    simp only [Nat.cast_zero, Real.log_zero, zero_pow (by decide : 6 ≠ 0), zero_mul, mul_zero,
      le_refl]
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    have hb := Real.log_natCast_le_rpow_div n (show (0 : ℝ) < 29 / 500 by norm_num only)
    have hp := pow_le_pow_left₀ hlog hb 5
    have hnneg : 0 ≤ (n : ℝ) ^ (-(79 / 50 : ℝ)) := Real.rpow_nonneg hnpos.le _
    have h := mul_le_mul_of_nonneg_right hp (mul_nonneg hlog hnneg)
    have hscale :
      ((n : ℝ) ^ (29 / 500 : ℝ)) ^ 5 * (n : ℝ) ^ (-(79 / 50 : ℝ)) =
        (n : ℝ) ^ (-(129 / 100 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le, ← Real.rpow_add hnpos]
      congr 1
      norm_num only
    have heq :
      ((n : ℝ) ^ (29 / 500 : ℝ) / (29 / 500 : ℝ)) ^ 5 * (Real.log n * (n : ℝ) ^ (-(79 / 50 : ℝ))) =
        (500 / 29 : ℝ) ^ 5 * (Real.log n * (n : ℝ) ^ (-(129 / 100 : ℝ))) := by
      rw [div_pow, div_eq_mul_inv, ← hscale]
      norm_num only
      ring
    rw [heq] at h
    convert h using 1
    ring

/-- Every nonnegative integral power of the logarithm is summable against
`n^(-79/50)`. Iterated logarithmic weights preserve the abscissa of convergence
of the constant-coefficient Dirichlet series. -/
theorem refined_log_power_summable (k : ℕ) :
    Summable (fun n : ℕ ↦ (Real.log n) ^ k * (n : ℝ) ^ (-(79 / 50 : ℝ))) := by
  have hc : ∀ (k n : ℕ), (LSeries.logMul^[k] (fun _ : ℕ ↦ (1 : ℂ))) n = (Complex.log n) ^ k := by
    intro k n
    induction k with
    | zero => simp only [Function.iterate_zero, id_eq, pow_zero]
    | succ k ih =>
      simp only [Function.iterate_succ_apply', LSeries.logMul, ih, pow_succ]
      ring
  have hbound : LSeries.abscissaOfAbsConv (fun _ : ℕ ↦ (1 : ℂ)) ≤ 1 :=
    LSeries.abscissaOfAbsConv_le_of_le_const ⟨1, fun _ _ ↦ by rw [norm_one]⟩
  have ha :
    LSeries.abscissaOfAbsConv (LSeries.logMul^[k] (fun _ : ℕ ↦ (1 : ℂ))) <
      (((79 / 50 : ℝ) : ℂ)).re := by
    rw [LSeries.abscissaOfAbsConv_logPowMul]
    apply hbound.trans_lt
    simpa only [Complex.ofReal_re, ← EReal.coe_one, EReal.coe_lt_coe_iff] using
      (show (1 : ℝ) < 79 / 50 by norm_num only)
  have hs := (LSeriesSummable_of_abscissaOfAbsConv_lt_re ha).norm
  apply hs.congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [LSeries.term_zero, norm_zero, Nat.cast_zero, Real.log_zero,
      Real.zero_rpow (by norm_num only : -(79 / 50 : ℝ) ≠ 0), mul_zero]
  · rw [LSeries.term_def, ite_eq_right hn, hc, norm_div, norm_pow,
      Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), ← Complex.ofReal_natCast, ←
      Complex.ofReal_log (Nat.cast_nonneg _), Complex.norm_of_nonneg (Real.log_natCast_nonneg n),
      Complex.ofReal_re, Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv]

/-- The sixth logarithmic fixed series has an explicit rational upper bound.
Reduce it termwise to an integrable first logarithmic series at exponent `129/100`. -/
theorem refined_log_six_tsum_bound :
    (∑' n : ℕ, (Real.log n) ^ 6 * (n : ℝ) ^ (-(79 / 50 : ℝ))) ≤
      (500 / 29 : ℝ) ^ 5 * ((100 / 29 : ℝ) ^ 2 + 100 / 129) := by
  have he := Analysis.summable_logPower_envelope (r := 29 / 100) (by norm_num only)
  have he' : Summable (fun n : ℕ ↦ (Real.log n + 1) * (n : ℝ) ^ (-(129 / 100 : ℝ))) := by
    convert he using 1
    norm_num only
  have hs : Summable (fun n : ℕ ↦ Real.log n * (n : ℝ) ^ (-(129 / 100 : ℝ))) := by
    refine Summable.of_nonneg_of_le ?_ ?_ he'
    · intro n
      exact mul_nonneg (Real.log_natCast_nonneg n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    · intro n
      exact
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
          (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have ht :=
    (refined_log_power_summable 6).tsum_le_tsum refined_log_six_reduction
      (hs.mul_left ((500 / 29 : ℝ) ^ 5))
  have hb := Analysis.tsum_logPower_le (r := 29 / 100) (by norm_num only)
  have hb' :
    (∑' n : ℕ, Real.log n * (n : ℝ) ^ (-(129 / 100 : ℝ))) ≤ (100 / 29 : ℝ) ^ 2 + 100 / 129 := by
    norm_num only [show -(29 / 100 : ℝ) - 1 = -(129 / 100 : ℝ) by norm_num only,
      show (29 / 100 : ℝ)⁻¹ = 100 / 29 by norm_num only,
      show (29 / 100 : ℝ) + 1 = 129 / 100 by norm_num only,
      show (129 / 100 : ℝ)⁻¹ = 100 / 129 by norm_num only] at hb ⊢
    exact hb
  rw [tsum_mul_left] at ht
  exact ht.trans (mul_le_mul_of_nonneg_left hb' (by positivity))

/-- Bound the sixth logarithmic summand by a first logarithmic summand at
exponent `59/50`, choosing the power `2/25` to improve the scalar budget. -/
theorem refined_log_six_reduction_improved (n : ℕ) :
    (Real.log n) ^ 6 * (n : ℝ) ^ (-(79 / 50 : ℝ)) ≤
      (25 / 2 : ℝ) ^ 5 * (Real.log n * (n : ℝ) ^ (-(59 / 50 : ℝ))) := by
  by_cases hn : n = 0
  · subst n
    simp only [Nat.cast_zero, Real.log_zero, zero_pow (by decide : 6 ≠ 0), zero_mul, mul_zero,
      le_refl]
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    have hb := Real.log_natCast_le_rpow_div n (show (0 : ℝ) < 2 / 25 by norm_num only)
    have hp := pow_le_pow_left₀ hlog hb 5
    have hnneg : 0 ≤ (n : ℝ) ^ (-(79 / 50 : ℝ)) := Real.rpow_nonneg hnpos.le _
    have h := mul_le_mul_of_nonneg_right hp (mul_nonneg hlog hnneg)
    have hscale :
      ((n : ℝ) ^ (2 / 25 : ℝ)) ^ 5 * (n : ℝ) ^ (-(79 / 50 : ℝ)) = (n : ℝ) ^ (-(59 / 50 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le, ← Real.rpow_add hnpos]
      congr 1
      norm_num only
    have heq :
      ((n : ℝ) ^ (2 / 25 : ℝ) / (2 / 25 : ℝ)) ^ 5 * (Real.log n * (n : ℝ) ^ (-(79 / 50 : ℝ))) =
        (25 / 2 : ℝ) ^ 5 * (Real.log n * (n : ℝ) ^ (-(59 / 50 : ℝ))) := by
      rw [div_pow, div_eq_mul_inv, ← hscale]
      norm_num only
      ring
    rw [heq] at h
    convert h using 1
    ring

/-- The sixth logarithmic series has a rational upper bound using the exponent
`59/50`. Summability and the existing first-logarithm integral bound justify the comparison. -/
theorem refined_log_six_tsum_improved :
    (∑' n : ℕ, (Real.log n) ^ 6 * (n : ℝ) ^ (-(79 / 50 : ℝ))) ≤
      (25 / 2 : ℝ) ^ 5 * ((50 / 9 : ℝ) ^ 2 + 50 / 59) := by
  have he := Analysis.summable_logPower_envelope (r := 9 / 50) (by norm_num only)
  have he' : Summable (fun n : ℕ ↦ (Real.log n + 1) * (n : ℝ) ^ (-(59 / 50 : ℝ))) := by
    convert he using 1
    norm_num only
  have hs : Summable (fun n : ℕ ↦ Real.log n * (n : ℝ) ^ (-(59 / 50 : ℝ))) := by
    refine Summable.of_nonneg_of_le ?_ ?_ he'
    · intro n
      exact mul_nonneg (Real.log_natCast_nonneg n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    · intro n
      exact
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
          (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have ht :=
    (refined_log_power_summable 6).tsum_le_tsum refined_log_six_reduction_improved
      (hs.mul_left ((25 / 2 : ℝ) ^ 5))
  have hb := Analysis.tsum_logPower_le (r := 9 / 50) (by norm_num only)
  have hb' : (∑' n : ℕ, Real.log n * (n : ℝ) ^ (-(59 / 50 : ℝ))) ≤ (50 / 9 : ℝ) ^ 2 + 50 / 59 := by
    norm_num only [show -(9 / 50 : ℝ) - 1 = -(59 / 50 : ℝ) by norm_num only,
      show (9 / 50 : ℝ)⁻¹ = 50 / 9 by norm_num only,
      show (9 / 50 : ℝ) + 1 = 59 / 50 by norm_num only,
      show (59 / 50 : ℝ)⁻¹ = 50 / 59 by norm_num only] at hb ⊢
    exact hb
  rw [tsum_mul_left] at ht
  exact ht.trans (mul_le_mul_of_nonneg_left hb' (by positivity))

/-- At a positive scale, every logarithmic power in the inverse-scale
majorant is summable. The combined decay exponent is `79/50`. -/
theorem refined_scaled_log_summable {x : ℝ} (hx : 0 < x) (k : ℕ) :
    Summable (fun n : ℕ ↦ (Real.log n) ^ k / Real.sqrt n * (((n : ℝ) * x)⁻¹) ^ (27 / 25 : ℝ)) := by
  apply ((refined_log_power_summable k).mul_left (x ^ (-(27 / 25 : ℝ)))).congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [Nat.cast_zero, Real.log_zero, Real.sqrt_zero, div_zero, zero_mul, mul_zero,
      Real.zero_rpow (by norm_num only : -(79 / 50 : ℝ) ≠ 0)]
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hpow :
      (n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(27 / 25 : ℝ)) = (n : ℝ) ^ (-(79 / 50 : ℝ)) := by
      rw [← Real.rpow_add hnpos]
      congr 1
      norm_num only
    rw [Real.sqrt_eq_rpow, Real.inv_rpow (mul_nonneg hnpos.le hx.le), Real.mul_rpow hnpos.le hx.le]
    simp only [div_eq_mul_inv, mul_inv_rev, ← Real.rpow_neg hnpos.le, ← Real.rpow_neg hx.le]
    simp only [div_eq_mul_inv] at hpow
    rw [← hpow]
    ring

/-- The inverse-scale logarithmic series factors into a power of the scale and
a fixed series with exponent `79/50`. This isolates the two numerical constants
needed for the principal reflected Euler estimate. -/
theorem refined_scaled_log_tsum {x : ℝ} (hx : 0 < x) (k : ℕ) :
    (∑' n : ℕ, (Real.log n) ^ k / Real.sqrt n * (((n : ℝ) * x)⁻¹) ^ (27 / 25 : ℝ)) =
      x ^ (-(27 / 25 : ℝ)) * ∑' n : ℕ, (Real.log n) ^ k * (n : ℝ) ^ (-(79 / 50 : ℝ)) := by
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [Nat.cast_zero, Real.log_zero, Real.sqrt_zero, div_zero, zero_mul, mul_zero,
      Real.zero_rpow (by norm_num only : -(79 / 50 : ℝ) ≠ 0)]
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hpow :
      (n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(27 / 25 : ℝ)) = (n : ℝ) ^ (-(79 / 50 : ℝ)) := by
      rw [← Real.rpow_add hnpos]
      congr 1
      norm_num only
    rw [Real.sqrt_eq_rpow, Real.inv_rpow (mul_nonneg hnpos.le hx.le), Real.mul_rpow hnpos.le hx.le]
    simp only [div_eq_mul_inv, mul_inv_rev, ← Real.rpow_neg hnpos.le, ← Real.rpow_neg hx.le]
    simp only [div_eq_mul_inv] at hpow
    rw [← hpow]
    ring

/-- The principal reflected term is bounded by two logarithmic scalar series
once their convergence is known. The remaining numerical bounds for those series
are separate from the profile and Mangoldt comparisons. -/
theorem refined_reflected_log_split {x : ℝ} (hx : 1 ≤ x)
    (h1 : Summable (fun n : ℕ ↦ Real.log n / Real.sqrt n * (((n : ℝ) * x)⁻¹) ^ (27 / 25 : ℝ)))
    (h6 :
      Summable
        (fun n : ℕ ↦
          (Real.log n) ^ 5 * (Real.log n / Real.sqrt n * (((n : ℝ) * x)⁻¹) ^ (27 / 25 : ℝ)))) :
    refinedReflectedEuler (1 : DirichletCharacter ℂ 1) x ≤
      (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8)))) * 16 *
        (((21 / 8 : ℝ) + Real.log x) ^ 5 *
            (∑' n : ℕ, Real.log n / Real.sqrt n * (((n : ℝ) * x)⁻¹) ^ (27 / 25 : ℝ)) +
          ∑' n : ℕ,
            (Real.log n) ^ 5 * (Real.log n / Real.sqrt n * (((n : ℝ) * x)⁻¹) ^ (27 / 25 : ℝ))) := by
  refine refined_reflected_principal_split (lt_of_lt_of_le zero_lt_one hx) ?_ ?_ _ _ h1 h6 ?_ ?_ ?_
  · have hl := Real.log_nonneg hx
    linarith only [hl]
  · positivity
  · intro n
    exact
      mul_nonneg (div_nonneg (Real.log_natCast_nonneg n) (Real.sqrt_nonneg n))
        (Real.rpow_nonneg (by positivity) _)
  · intro n
    rfl
  · intro n
    exact refined_dual_weight_log_bound hx n

/-- At scales at least one, the principal reflected Euler term is bounded by
the two convergent logarithmic majorant series. Their subsequent numerical
estimates are not assumed here. -/
theorem refined_reflected_log_bound {x : ℝ} (hx : 1 ≤ x) :
    refinedReflectedEuler (1 : DirichletCharacter ℂ 1) x ≤
      (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8)))) * 16 *
        (((21 / 8 : ℝ) + Real.log x) ^ 5 *
            (∑' n : ℕ, Real.log n / Real.sqrt n * (((n : ℝ) * x)⁻¹) ^ (27 / 25 : ℝ)) +
          ∑' n : ℕ,
            (Real.log n) ^ 5 * (Real.log n / Real.sqrt n * (((n : ℝ) * x)⁻¹) ^ (27 / 25 : ℝ))) := by
  have hx' : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have h1 := refined_scaled_log_summable hx' 1
  have h6 := refined_scaled_log_summable hx' 6
  apply refined_reflected_log_split hx
  · simpa only [pow_one] using h1
  · apply h6.congr
    intro n
    rw [show 6 = 5 + 1 by decide, pow_add, pow_one]
    ring

/-- The principal reflected Euler term is bounded using two fixed convergent
logarithmic series and the exact scale factor `x^(-27/25)`. This is the analytic
form preceding the explicit numerical evaluation of those two series. -/
theorem refined_reflected_fixed_bound {x : ℝ} (hx : 1 ≤ x) :
    refinedReflectedEuler (1 : DirichletCharacter ℂ 1) x ≤
      (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8)))) * 16 *
        x ^ (-(27 / 25 : ℝ)) *
        (((21 / 8 : ℝ) + Real.log x) ^ 5 * (∑' n : ℕ, Real.log n * (n : ℝ) ^ (-(79 / 50 : ℝ))) +
          ∑' n : ℕ, (Real.log n) ^ 6 * (n : ℝ) ^ (-(79 / 50 : ℝ))) := by
  have hx' : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have h1 := refined_scaled_log_tsum hx' 1
  have h6 := refined_scaled_log_tsum hx' 6
  simp only [pow_one] at h1
  have h6' :
    (∑' n : ℕ, (Real.log n) ^ 5 * (Real.log n / Real.sqrt n * (((n : ℝ) * x)⁻¹) ^ (27 / 25 : ℝ))) =
      x ^ (-(27 / 25 : ℝ)) * ∑' n : ℕ, (Real.log n) ^ 6 * (n : ℝ) ^ (-(79 / 50 : ℝ)) := by
    rw [← h6]
    apply tsum_congr
    intro n
    rw [show 6 = 5 + 1 by decide, pow_add, pow_one]
    ring
  have h := refined_reflected_log_bound hx
  rw [h1, h6'] at h
  convert h using 1
  ring

/-- The principal reflected term has an explicit rational bound for the
first scalar series, leaving only the sixth logarithmic moment to estimate. -/
theorem refined_reflected_one_explicit {x : ℝ} (hx : 1 ≤ x) :
    refinedReflectedEuler (1 : DirichletCharacter ℂ 1) x ≤
      (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8)))) * 16 *
        x ^ (-(27 / 25 : ℝ)) *
        (((21 / 8 : ℝ) + Real.log x) ^ 5 * ((50 / 29 : ℝ) ^ 2 + 50 / 79) +
          ∑' n : ℕ, (Real.log n) ^ 6 * (n : ℝ) ^ (-(79 / 50 : ℝ))) := by
  apply (refined_reflected_fixed_bound hx).trans
  apply mul_le_mul_of_nonneg_left
  · apply add_le_add (mul_le_mul_of_nonneg_left refined_log_one_tsum_bound ?_) le_rfl
    exact
      pow_nonneg
        (by
          have h := Real.log_nonneg hx; linarith only [h])
        _
  · positivity

/-- The principal reflected Euler term has a fully explicit rational-series
majorant at scales at least one. The sixth-moment bound is deliberately coarse;
sharper estimates are needed for the paper's final numerical certificate. -/
theorem refined_reflected_explicit_bound {x : ℝ} (hx : 1 ≤ x) :
    refinedReflectedEuler (1 : DirichletCharacter ℂ 1) x ≤
      (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8)))) * 16 *
        x ^ (-(27 / 25 : ℝ)) *
        (((21 / 8 : ℝ) + Real.log x) ^ 5 * ((50 / 29 : ℝ) ^ 2 + 50 / 79) +
          (500 / 29 : ℝ) ^ 5 * ((100 / 29 : ℝ) ^ 2 + 100 / 129)) := by
  apply (refined_reflected_one_explicit hx).trans
  apply mul_le_mul_of_nonneg_left
  · exact add_le_add le_rfl refined_log_six_tsum_bound
  · positivity

/-- The principal reflected term with the improved sixth-moment bound.
The estimate retains the exact scale dependence and requires no series assumptions. -/
theorem refined_reflected_improved_bound {x : ℝ} (hx : 1 ≤ x) :
    refinedReflectedEuler (1 : DirichletCharacter ℂ 1) x ≤
      (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8)))) * 16 *
        x ^ (-(27 / 25 : ℝ)) *
        (((21 / 8 : ℝ) + Real.log x) ^ 5 * ((50 / 29 : ℝ) ^ 2 + 50 / 79) +
          (25 / 2 : ℝ) ^ 5 * ((50 / 9 : ℝ) ^ 2 + 50 / 59)) := by
  apply (refined_reflected_one_explicit hx).trans
  apply mul_le_mul_of_nonneg_left
  · exact add_le_add le_rfl refined_log_six_tsum_improved
  · positivity

/-- Three reflected Euler integrals satisfy the common principal bound when
their character real parts sum to at least minus one at every index. -/
theorem refined_reflected_three_lower {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) {x : ℝ}
    (hx : 0 < x) (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re) :
    -(refinedReflectedEuler a x + refinedReflectedEuler b x + refinedReflectedEuler c x) ≤
      refinedReflectedEuler (1 : DirichletCharacter ℂ 1) x := by
  unfold refinedReflectedEuler
  rw [refined_reflected_logDeriv_real a hx, refined_reflected_logDeriv_real b hx,
    refined_reflected_logDeriv_real c hx,
    refined_reflected_logDeriv_real (1 : DirichletCharacter ℂ 1) hx]
  have h := refined_dual_three_lower a b c hx ht
  apply h.trans_eq
  apply tsum_congr
  intro n
  simp only [MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1)), Complex.one_re, one_mul]

/-- The ordinary reflected logarithmic derivative against the sixth-pole
left-line weight is integrable at every positive scale. Sum the integrable
Dirichlet terms using the absolute integrated-norm bound. -/
theorem refined_reflected_ordinary_integrable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 0 < x) :
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        -logDeriv χ.LFunction (((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)) *
          (refinedSixPoleKernel.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
            (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) := by
  let W := fun t : ℝ ↦
    refinedSixPoleKernel.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
      (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)
  have hd : refinedSixPoleKernel.delta = (1 / 8 : ℝ) := by
    norm_num only [refinedSixPoleKernel, LLS.PaperStatements.rationalPoleMellinKernel]
    apply min_eq_right
    norm_num only
  have hiW : MeasureTheory.Integrable W := by
    have h :=
      LLS.PaperStatements.MellinKernel.integrable_inverse_in_strip refinedSixPoleKernel (c :=
        (-9 / 16 : ℝ)) (u := x⁻¹)
        (by
          rw [hd]; norm_num only)
        (by
          rw [hd]; norm_num only)
        (by norm_num only) (inv_pos.mpr hx)
    simp only [Complex.ofReal_inv, Complex.cpow_neg, Complex.inv_cpow_ofReal_nonneg hx.le,
      inv_inv] at h
    exact h
  let f := fun n : ℕ ↦ χ n * (ArithmeticFunction.vonMangoldt n : ℂ)
  let F := fun (n : ℕ) (t : ℝ) ↦ LSeries.term f (((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)) n * W t
  have hs : LSeriesSummable f (((17 / 16 : ℝ) : ℂ)) :=
    χ.LSeriesSummable_twist_vonMangoldt
      (show (1 : ℝ) < (((17 / 16 : ℝ) : ℂ)).re by norm_num only [Complex.ofReal_re])
  have hi :=
    Analysis.integrable_tsum_of_summable_integral_norm F
      (fun n ↦
        AnalyticNumberTheory.General.integrable_LSeries_term_mul_weight f (17 / 16) n
          (fun t : ℝ ↦ -t) continuous_neg W hiW)
      (AnalyticNumberTheory.General.summable_integral_norm_LSeries_term_mul_weight hs
        (fun t : ℝ ↦ -t) W)
  apply hi.congr
  apply MeasureTheory.ae_of_all
  intro t
  dsimp only [F]
  rw [tsum_mul_right]
  change LSeries f _ * _ = _
  rw [AnalyticNumberTheory.DirichletLFunction.LSeries_mangoldt_eq_neg_logDeriv χ
      (show (1 : ℝ) < ((((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ))).re
        by
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
        norm_num only)]
  dsimp only [W]
  simp only [logDeriv, Pi.div_apply, neg_div]

/-- The reflected completed-minus-ordinary logarithmic derivative integral.
This isolates the archimedean term on the inverse scale. -/
noncomputable def refinedReflectedArchimedean {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (x : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    (∫ t : ℝ,
      (logDeriv χ.completedLFunction (((17 / 16 : ℝ) : ℂ) - Complex.I * t) -
          logDeriv χ.LFunction (((17 / 16 : ℝ) : ℂ) - Complex.I * t)) *
        (refinedSixPoleKernel.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
          (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)))

/-- On the reflected line, the completed-minus-ordinary logarithmic derivative
is exactly the Gamma-factor logarithmic derivative. Nonvanishing in the right
half-plane justifies this identity inside the integral. -/
theorem refined_reflected_arch_eq_gamma {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) (x : ℝ) :
    refinedReflectedArchimedean χ x =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          logDeriv χ.gammaFactor (((17 / 16 : ℝ) : ℂ) - Complex.I * t) *
            (refinedSixPoleKernel.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
              (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) := by
  unfold refinedReflectedArchimedean
  congr 1
  apply MeasureTheory.integral_congr_ae
  apply MeasureTheory.ae_of_all
  intro t
  let z : ℂ := (((17 / 16 : ℝ) : ℂ) - Complex.I * t)
  have hr : 1 ≤ z.re := by
    simp only [z, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
    norm_num only
  have hp : 0 < z.re := zero_lt_one.trans_le hr
  have he :=
    AnalyticNumberTheory.DirichletLFunction.L_logDeriv_sub_gamma_of_regular hne
      (AnalyticNumberTheory.DirichletLFunction.completed_ne_zero_of_one_le_re hne hr)
      (AnalyticNumberTheory.DirichletLFunction.gammaFactor_ne_zero_of_re_pos χ hp)
      (AnalyticNumberTheory.DirichletLFunction.analyticAt_gammaFactor_of_re_pos χ
          hp).differentiableAt
  change (logDeriv χ.completedLFunction z - logDeriv χ.LFunction z) * _ = _
  rw [he]
  ring

/-- The reflected archimedean integral is the same for any two even
nonprincipal characters. Their Gamma factors are the same real Gamma factor. -/
theorem refined_reflected_arch_even_eq {p q : ℕ} [NeZero p] [NeZero q] (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (ha : a ≠ 1) (hb : b ≠ 1) (hea : a.Even) (heb : b.Even) (x : ℝ) :
    refinedReflectedArchimedean a x = refinedReflectedArchimedean b x := by
  rw [refined_reflected_arch_eq_gamma a ha x, refined_reflected_arch_eq_gamma b hb x]
  have hγ : a.gammaFactor = b.gammaFactor := by
    funext z
    rw [hea.gammaFactor_def, heb.gammaFactor_def]
  rw [hγ]

/-- Split the primitive completed left contour into the exact conductor term,
the inverse character's ordinary Euler integral, and its archimedean remainder. -/
theorem refined_left_euler_split {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
            (refinedSixPoleKernel.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
              (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) =
      Complex.log q * (Analysis.rationalPoleProfile 3 (25 / 54) (21 / 16) x⁻¹ : ℂ) +
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv χ⁻¹.LFunction (((17 / 16 : ℝ) : ℂ) - Complex.I * t) *
              (refinedSixPoleKernel.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
                (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) +
        refinedReflectedArchimedean χ⁻¹ x := by
  let K := refinedSixPoleKernel
  let W := fun t : ℝ ↦
    K.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
      (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)
  let F := fun t : ℝ ↦
    -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) * W t
  let C := fun t : ℝ ↦ Complex.log q * W t
  let R := fun t : ℝ ↦ logDeriv χ⁻¹.completedLFunction (((17 / 16 : ℝ) : ℂ) - Complex.I * t) * W t
  have hd : K.delta = (1 / 8 : ℝ) := by
    norm_num only [K, refinedSixPoleKernel, LLS.PaperStatements.rationalPoleMellinKernel]
    apply min_eq_right
    norm_num only
  have hF :=
    LLS.PaperStatements.MellinKernel.integrable_completed_left_line K hp hne hinv (c := -9 / 16)
      (x := x)
      (by
        rw [hd]; norm_num only)
      (by norm_num only) (by norm_num only) hx
  have hC :=
    LLS.PaperStatements.MellinKernel.integrable_logWeighted_power_line K (c := -9 / 16) (x := x)
      (F := fun _ : ℝ ↦ Complex.log q) (A := ‖Complex.log q‖)
      (by
        rw [hd]; norm_num only)
      (by
        rw [hd]; norm_num only)
      (by norm_num only) hx MeasureTheory.aestronglyMeasurable_const
      (fun t ↦ by
        have hlog : 0 ≤ Real.log (4 + |t|) := Real.log_nonneg (by linarith only [abs_nonneg t])
        nlinarith only [hlog, norm_nonneg (Complex.log (q : ℂ))])
  simp only [mul_assoc] at hC
  change MeasureTheory.Integrable F at hF
  change MeasureTheory.Integrable C at hC
  have he (t : ℝ) : F t = C t + R t := by
    dsimp only [F, C, R, W, K]
    rw [LLS.PaperStatements.triangular18_completed_left_reflection hp hne hinv t, add_mul]
  have hR : MeasureTheory.Integrable R :=
    (hF.sub hC).congr
      (MeasureTheory.ae_of_all _ (fun t ↦ by rw [Pi.sub_apply, he, add_sub_cancel_left]))
  have hO :
    MeasureTheory.Integrable
      (fun t : ℝ ↦ logDeriv χ⁻¹.LFunction (((17 / 16 : ℝ) : ℂ) - Complex.I * t) * W t) := by
    apply (refined_reflected_ordinary_integrable χ⁻¹ hx).neg.congr
    apply MeasureTheory.ae_of_all
    intro t
    simp only [Pi.neg_apply, neg_mul, neg_neg, Complex.ofReal_neg, mul_neg, sub_eq_add_neg, W, K]
  rw [refined_left_reflection hp hne hinv hx]
  dsimp only [refinedReflectedArchimedean]
  simp only [sub_mul]
  rw [MeasureTheory.integral_sub hR hO]
  ring

/-- The real ordinary term in the reflected completed contour is the negative
of the reflected Euler integral used in the three-character comparison. -/
theorem refined_ordinary_re {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv χ.LFunction (((17 / 16 : ℝ) : ℂ) - Complex.I * t) *
              (refinedSixPoleKernel.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
                (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)))).re =
      -refinedReflectedEuler χ x := by
  have he (t : ℝ) :
    1 / 2 - (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) = (((17 / 16 : ℝ) : ℂ) - Complex.I * t) := by
    push_cast
    ring
  unfold refinedReflectedEuler
  simp only [he, neg_mul, MeasureTheory.integral_neg, mul_neg, Complex.neg_re, neg_neg]

/-- The right-line Gamma integral in the refined contour remainder. -/
noncomputable def refinedRightGamma {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    (∫ t : ℝ,
      logDeriv χ.gammaFactor ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
        (refinedSixPoleKernel.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t) *
          (x : ℂ) ^ (((9 / 16 : ℝ) : ℂ) + Complex.I * t)))

/-- For even characters, the sum of the two Gamma contour integrals is
independent of the modulus. This combines parity invariance under inversion with
the common even Gamma factor on both vertical lines. -/
theorem refined_even_gamma_cost_eq {p q : ℕ} [NeZero p] [NeZero q] (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (ha : a⁻¹ ≠ 1) (hb : b⁻¹ ≠ 1) (hea : a.Even) (heb : b.Even)
    (x : ℝ) :
    refinedReflectedArchimedean a⁻¹ x + refinedRightGamma a x =
      refinedReflectedArchimedean b⁻¹ x + refinedRightGamma b x := by
  have heA : a⁻¹.Even := AnalyticNumberTheory.DirichletLFunction.character_even_inv_iff.mpr hea
  have heB : b⁻¹.Even := AnalyticNumberTheory.DirichletLFunction.character_even_inv_iff.mpr heb
  rw [refined_reflected_arch_even_eq a⁻¹ b⁻¹ ha hb heA heB x]
  unfold refinedRightGamma
  have hγ : a.gammaFactor = b.gammaFactor := by
    funext z
    rw [hea.gammaFactor_def, heb.gammaFactor_def]
  rw [hγ]

/-- The conductor and Gamma terms remaining after the reflected Euler term is
separated from the refined contour remainder. -/
noncomputable def refinedContourNonEuler {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) :
    ℝ :=
  (Complex.log q * (Analysis.rationalPoleProfile 3 (25 / 54) (21 / 16) x⁻¹ : ℂ)).re +
    (refinedReflectedArchimedean χ⁻¹ x).re +
    (refinedRightGamma χ x).re

/-- The three complex conductor terms equal the sum of the three real
logarithms times the common real profile. Natural moduli are nonnegative. -/
theorem refined_conductor_sum (p q r : ℕ) (x : ℝ) :
    (Complex.log p * (Analysis.rationalPoleProfile 3 (25 / 54) (21 / 16) x⁻¹ : ℂ)).re +
        (Complex.log q * (Analysis.rationalPoleProfile 3 (25 / 54) (21 / 16) x⁻¹ : ℂ)).re +
        (Complex.log r * (Analysis.rationalPoleProfile 3 (25 / 54) (21 / 16) x⁻¹ : ℂ)).re =
      (Real.log p + Real.log q + Real.log r) *
        Analysis.rationalPoleProfile 3 (25 / 54) (21 / 16) x⁻¹ := by
  simp only [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg _),
    ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

/-- Three even-character non-Euler terms consist of their conductor terms
and three copies of one common Gamma cost. The identity prepares the numerical
Gamma bound without replacing any of the actual contour integrals. -/
theorem refined_three_nonEuler_even {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r)
    (ha : a⁻¹ ≠ 1) (hb : b⁻¹ ≠ 1) (hc : c⁻¹ ≠ 1) (hea : a.Even) (heb : b.Even) (hec : c.Even)
    (x : ℝ) :
    refinedContourNonEuler a x + refinedContourNonEuler b x + refinedContourNonEuler c x =
      (Complex.log p * (Analysis.rationalPoleProfile 3 (25 / 54) (21 / 16) x⁻¹ : ℂ)).re +
        (Complex.log q * (Analysis.rationalPoleProfile 3 (25 / 54) (21 / 16) x⁻¹ : ℂ)).re +
        (Complex.log r * (Analysis.rationalPoleProfile 3 (25 / 54) (21 / 16) x⁻¹ : ℂ)).re +
        3 * (refinedReflectedArchimedean a⁻¹ x + refinedRightGamma a x).re := by
  have hb' := congrArg Complex.re (refined_even_gamma_cost_eq a b ha hb hea heb x)
  have hc' := congrArg Complex.re (refined_even_gamma_cost_eq a c ha hc hea hec x)
  simp only [Complex.add_re] at hb' hc' ⊢
  unfold refinedContourNonEuler
  linarith only [hb', hc']

/-- For a primitive nonprincipal character and positive scale, the real
contour remainder is its non-Euler part minus the reflected Euler contribution. -/
theorem refined_contour_split_real {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) :
    (refinedContourRemainder χ x).re =
      refinedContourNonEuler χ x - refinedReflectedEuler χ⁻¹ x := by
  rw [refined_contour_no_residue χ x, refined_left_euler_split hp hne hinv hx]
  simp only [Complex.add_re, refined_ordinary_re]
  unfold refinedContourNonEuler refinedRightGamma
  ring

/-- The three actual contour remainders are bounded by their conductor and
Gamma terms plus one principal reflected Euler integral. The inverse characters
must satisfy the common lower sign bound at every index. -/
theorem refined_three_contour_upper {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r)
    (hpA : a.IsPrimitive) (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1)
    (hnC : c ≠ 1) (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x)
    (ht : ∀ n : ℕ, -1 ≤ (a⁻¹ n).re + (b⁻¹ n).re + (c⁻¹ n).re) :
    (refinedContourRemainder a x).re + (refinedContourRemainder b x).re +
        (refinedContourRemainder c x).re ≤
      refinedContourNonEuler a x + refinedContourNonEuler b x + refinedContourNonEuler c x +
        refinedReflectedEuler (1 : DirichletCharacter ℂ 1) x := by
  have hA := refined_contour_split_real hpA hnA hiA hx
  have hB := refined_contour_split_real hpB hnB hiB hx
  have hC := refined_contour_split_real hpC hnC hiC hx
  have h := refined_reflected_three_lower a⁻¹ b⁻¹ c⁻¹ hx ht
  linarith only [hA, hB, hC, h]

/-- Inversion of a complex Dirichlet character preserves the real part of
its value. Character inversion is complex conjugation at every residue. -/
theorem refined_inv_char_re {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (n : ℕ) :
    (χ⁻¹ n).re = (χ n).re := by
  rw [← MulChar.star_apply']
  rfl

/-- Under GRH and the three prime-prefix conditions, the principal deficit
is bounded by the separated conductor and Gamma terms, one reflected principal
Euler integral, and the certified zero-mass correction. -/
theorem refined_cutoff_dual_upper {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hpA : a.IsPrimitive) (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1)
    (hnC : c ≠ 1) (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) (heA : a.Even) (heB : b.Even)
    (heC : c.Even) {X : ℝ} (hX : 1000 ≤ X) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) :
    4 *
          (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
            (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X n).re) -
        (∑' n : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X n).re <
      refinedContourNonEuler a X + refinedContourNonEuler b X + refinedContourNonEuler c X +
          refinedReflectedEuler (1 : DirichletCharacter ℂ 1) X +
          (3 / 16 : ℝ) * (Real.log p + Real.log q + Real.log r) -
        (6366 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 5 := by
  have htInv : ∀ k : ℕ, -1 ≤ (a⁻¹ k).re + (b⁻¹ k).re + (c⁻¹ k).re := by
    intro k
    simpa only [refined_inv_char_re] using ht k
  have hc :=
    refined_cutoff_prefix_upper hGRH a b c hP hQ hR hpA hpB hpC hnA hnB hnC hiA hiB hiC heA heB heC
      hX ht hA hB hC
  have hd :=
    refined_three_contour_upper a b c hpA hpB hpC hnA hnB hnC hiA hiB hiC (by linarith only [hX])
      htInv
  linarith only [hc, hd]

/-- The all-pass cutoff inequality for even characters, with the non-Euler
contour split into three conductor terms and one shared Gamma integral. -/
theorem refined_cutoff_gamma_upper {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hpA : a.IsPrimitive) (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1)
    (hnC : c ≠ 1) (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) (heA : a.Even) (heB : b.Even)
    (heC : c.Even) {X : ℝ} (hX : 1000 ≤ X) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) :
    4 *
          (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
            (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X n).re) -
        (∑' n : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X n).re <
      (Complex.log p * (Analysis.rationalPoleProfile 3 (25 / 54) (21 / 16) X⁻¹ : ℂ)).re +
          (Complex.log q * (Analysis.rationalPoleProfile 3 (25 / 54) (21 / 16) X⁻¹ : ℂ)).re +
          (Complex.log r * (Analysis.rationalPoleProfile 3 (25 / 54) (21 / 16) X⁻¹ : ℂ)).re +
          3 * (refinedReflectedArchimedean a⁻¹ X + refinedRightGamma a X).re +
          refinedReflectedEuler (1 : DirichletCharacter ℂ 1) X +
          (3 / 16 : ℝ) * (Real.log p + Real.log q + Real.log r) -
        (6366 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 5 := by
  have h :=
    refined_cutoff_dual_upper hGRH a b c hP hQ hR hpA hpB hpC hnA hnB hnC hiA hiB hiC heA heB heC hX
      ht hA hB hC
  rw [refined_three_nonEuler_even a b c hiA hiB hiC heA heB heC X] at h
  exact h

/-- For three even characters, bound the cutoff deficit using the real
conductor sum, the common Gamma integral and an explicit reflected Euler term. -/
theorem refined_cutoff_explicit_gamma {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hpA : a.IsPrimitive) (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1)
    (hnC : c ≠ 1) (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) (heA : a.Even) (heB : b.Even)
    (heC : c.Even) {X : ℝ} (hX : 1000 ≤ X) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) :
    4 *
          (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
            (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X n).re) -
        (∑' n : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X n).re <
      (Real.log p + Real.log q + Real.log r) *
            Analysis.rationalPoleProfile 3 (25 / 54) (21 / 16) X⁻¹ +
          3 * (refinedReflectedArchimedean a⁻¹ X + refinedRightGamma a X).re +
          (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8)))) * 16 *
            X ^ (-(27 / 25 : ℝ)) *
            (((21 / 8 : ℝ) + Real.log X) ^ 5 * ((50 / 29 : ℝ) ^ 2 + 50 / 79) +
              (25 / 2 : ℝ) ^ 5 * ((50 / 9 : ℝ) ^ 2 + 50 / 59)) +
          (3 / 16 : ℝ) * (Real.log p + Real.log q + Real.log r) -
        (6366 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 5 := by
  have h :=
    refined_cutoff_gamma_upper hGRH a b c hP hQ hR hpA hpB hpC hnA hnB hnC hiA hiB hiC heA heB heC
      hX ht hA hB hC
  rw [refined_conductor_sum p q r X] at h
  have hX1 : (1 : ℝ) ≤ X := (by norm_num only : (1 : ℝ) ≤ 1000).trans hX
  have hb := refined_reflected_improved_bound hX1
  linarith only [h, hb]

/-- The cutoff inequality with explicit conductor and inverse-scale Euler
costs, leaving only the common Gamma integral and the principal sum to bound. -/
theorem refined_cutoff_explicit_costs {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hpA : a.IsPrimitive) (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1)
    (hnC : c ≠ 1) (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) (heA : a.Even) (heB : b.Even)
    (heC : c.Even) {X : ℝ} (hX : 1000 ≤ X) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) :
    4 *
          (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
            (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X n).re) -
        (∑' n : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X n).re <
      (Real.log p + Real.log q + Real.log r) *
            (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8))) *
              X ^ (-(27 / 25 : ℝ)) *
              ((21 / 8 : ℝ) + Real.log X) ^ 5) +
          3 * (refinedReflectedArchimedean a⁻¹ X + refinedRightGamma a X).re +
          (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8)))) * 16 *
            X ^ (-(27 / 25 : ℝ)) *
            (((21 / 8 : ℝ) + Real.log X) ^ 5 * ((50 / 29 : ℝ) ^ 2 + 50 / 79) +
              (25 / 2 : ℝ) ^ 5 * ((50 / 9 : ℝ) ^ 2 + 50 / 59)) +
          (3 / 16 : ℝ) * (Real.log p + Real.log q + Real.log r) -
        (6366 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 5 := by
  have h :=
    refined_cutoff_explicit_gamma hGRH a b c hP hQ hR hpA hpB hpC hnA hnB hnC hiA hiB hiC heA heB
      heC hX ht hA hB hC
  have hx1 : (1 : ℝ) ≤ X := (by norm_num only : (1 : ℝ) ≤ 1000).trans hX
  rw [refined_conductor_profile hx1] at h
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
