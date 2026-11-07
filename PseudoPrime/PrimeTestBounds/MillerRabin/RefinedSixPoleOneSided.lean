/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPolePsiRelative

/-! # One-sided cutoff principal bound for the refined kernel -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The principal weight at the unit cutoff is nonnegative. Evaluate the explicit
expression and use positivity of the exponential. -/
theorem refined_unit_weight_nonneg : 0 ≤ refinedWeight 1 := by
  norm_num only [refinedWeight, refinedCoord, Real.log_one, Real.sqrt_one, mul_zero, sub_zero,
    mul_one]
  positivity

/-- The principal weight derivative at the unit cutoff is nonpositive. Evaluate its
explicit expression and use positivity of the exponential. -/
theorem refined_unit_deriv_nonpos : refinedWeightDeriv 1 ≤ 0 := by
  norm_num only [refinedWeightDeriv, refinedCoord, Real.log_one, Real.sqrt_one, mul_zero, sub_zero,
    mul_one]
  have he := Real.exp_pos (-(567 / 200 : ℝ))
  nlinarith only [he]

/-- Under RH, positive relative width and a scale at least one, the unit-cutoff
principal sum is bounded below by its kernel main term minus explicit integral, Mangoldt
and one-sided Chebyshev errors. Keep the signed derivative and positive boundary weight. -/
theorem refined_unit_one_sided (hRH : RiemannHypothesis) {x h H : ℝ} (hx : 1 ≤ x) (hh : 0 < h)
    (hhH : h ≤ H) (hH : H ≤ 1 / 2) :
    Real.sqrt x * (∫ u : ℝ in (0 : ℝ)..1, (refinedSixPoleKernel.transform u).re / Real.sqrt u) -
        ((231 / 5000 : ℝ) * (6889 / 2700) +
          ((1839 / 1000 : ℝ) * (Real.log x + 21 / 8) + 2) *
              ((918330048 / 17682025 : ℝ) * Real.exp (-(21 / 16 : ℝ))) /
            Real.sqrt x) -
        |refinedWeightDeriv 1| *
            ((231 / 5000 : ℝ) * Real.sqrt x + (1839 / 1000 : ℝ) * Real.log x + 2) /
          Real.sqrt x -
        refinedWeight 1 *
            (h / (2 - H) * x + (231 / 2500 : ℝ) / h * Real.sqrt x + (231 / 2500 : ℝ) / h +
              1839 / 1000) /
          Real.sqrt x ≤
      ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) x n).re := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hb : (1 : ℝ) ≤ Real.exp (21 / 8 : ℝ) := Real.one_le_exp_iff.mpr (by norm_num only)
  have heq := refined_principal_error_identity hx0 zero_le_one hb
  rw [refined_unit_main_eq] at heq
  simp only [mul_one, one_mul] at heq
  have hi := (abs_le.mp (refined_sharp_integral_explicit hRH hx zero_le_one hb)).1
  have hw := refined_log_mangoldt_error hRH hx0
  rw [max_eq_right hx] at hw
  have hw' := (abs_le.mp hw).1
  have hp := refined_psi_relative hRH hh hhH hH hx0.le
  have hmulW := mul_le_mul_of_nonneg_left hw' (neg_nonneg.mpr refined_unit_deriv_nonpos)
  have hmulP := mul_le_mul_of_nonneg_left hp refined_unit_weight_nonneg
  have hneg : |refinedWeightDeriv 1| = -refinedWeightDeriv 1 :=
    abs_of_nonpos refined_unit_deriv_nonpos
  rw [hneg]
  have heq' := (eq_div_iff hs.ne').mp heq
  have hnum :
    -((231 / 5000 : ℝ) * Real.sqrt x * (6889 / 2700) +
            ((1839 / 1000 : ℝ) * (Real.log x + 21 / 8) + 2) *
              ((918330048 / 17682025 : ℝ) * Real.exp (-(21 / 16 : ℝ)))) -
        (-refinedWeightDeriv 1) *
          ((231 / 5000 : ℝ) * Real.sqrt x + (1839 / 1000 : ℝ) * Real.log x + 2) -
        refinedWeight 1 *
          (h / (2 - H) * x + (231 / 2500 : ℝ) / h * Real.sqrt x + (231 / 2500 : ℝ) / h +
            1839 / 1000) ≤
      ((∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
            (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) x n).re) -
          Real.sqrt x *
            (∫ u : ℝ in (0 : ℝ)..1, (refinedSixPoleKernel.transform u).re / Real.sqrt u)) *
        Real.sqrt x := by
    rw [heq']
    ring_nf at hi hmulW hmulP ⊢
    linarith only [hi, hmulW, hmulP]
  have hdiv := div_le_div_of_nonneg_right hnum hs.le
  rw [mul_div_cancel_right₀ _ hs.ne'] at hdiv
  have hr :
    (-((231 / 5000 : ℝ) * Real.sqrt x * (6889 / 2700) +
              ((1839 / 1000 : ℝ) * (Real.log x + 21 / 8) + 2) *
                ((918330048 / 17682025 : ℝ) * Real.exp (-(21 / 16 : ℝ)))) -
          (-refinedWeightDeriv 1) *
            ((231 / 5000 : ℝ) * Real.sqrt x + (1839 / 1000 : ℝ) * Real.log x + 2) -
          refinedWeight 1 *
            (h / (2 - H) * x + (231 / 2500 : ℝ) / h * Real.sqrt x + (231 / 2500 : ℝ) / h +
              1839 / 1000)) /
        Real.sqrt x =
      -((231 / 5000 : ℝ) * (6889 / 2700) +
            ((1839 / 1000 : ℝ) * (Real.log x + 21 / 8) + 2) *
                ((918330048 / 17682025 : ℝ) * Real.exp (-(21 / 16 : ℝ))) /
              Real.sqrt x) -
        (-refinedWeightDeriv 1) *
            ((231 / 5000 : ℝ) * Real.sqrt x + (1839 / 1000 : ℝ) * Real.log x + 2) /
          Real.sqrt x -
        refinedWeight 1 *
            (h / (2 - H) * x + (231 / 2500 : ℝ) / h * Real.sqrt x + (231 / 2500 : ℝ) / h +
              1839 / 1000) /
          Real.sqrt x := by
    field_simp (disch :=
      first
      | exact hs.ne'
      | norm_num only)
  rw [hr] at hdiv
  linarith only [hdiv]

/-- Under RH and `r ≥ 522`, the unit-cutoff principal sum at `r²` satisfies the
explicit one-sided estimate at width `3/(7 sqrt r)` and maximum width `1/32`.
Specialize the relative Chebyshev bound and simplify its boundary costs. -/
theorem refined_unit_paper_scale (hRH : RiemannHypothesis) {r : ℝ} (hr : 522 ≤ r) :
    r * (∫ u : ℝ in (0 : ℝ)..1, (refinedSixPoleKernel.transform u).re / Real.sqrt u) -
        ((231 / 5000 : ℝ) * (6889 / 2700) +
          ((1839 / 1000 : ℝ) * (2 * Real.log r + 21 / 8) + 2) *
              ((918330048 / 17682025 : ℝ) * Real.exp (-(21 / 16 : ℝ))) /
            r) -
        |refinedWeightDeriv 1| * ((231 / 5000 : ℝ) * r + (1839 / 1000 : ℝ) * (2 * Real.log r) + 2) /
          r -
        refinedWeight 1 *
          (((32 / 63 : ℝ) * (3 / 7) + (231 / 2500 : ℝ) * (7 / 3)) * Real.sqrt r +
            (231 / 2500 : ℝ) * (7 / 3) / Real.sqrt r +
            (1839 / 1000 : ℝ) / r) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) n).re := by
  have hr0 : 0 < r := (by norm_num only : (0 : ℝ) < 522).trans_le hr
  have hs : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr0
  have hs20 : (20 : ℝ) ≤ Real.sqrt r :=
    (Real.le_sqrt (by norm_num only) hr0.le).mpr (by nlinarith only [hr])
  have hwidth : (3 / 7 : ℝ) / Real.sqrt r ≤ 1 / 32 := by
    apply (div_le_iff₀ hs).mpr
    linarith only [hs20]
  have hx : (1 : ℝ) ≤ r ^ 2 := by nlinarith only [hr]
  have hh : 0 < (3 / 7 : ℝ) / Real.sqrt r := div_pos (by norm_num only) hs
  have hp := refined_unit_one_sided hRH hx hh hwidth (by norm_num only : (1 / 32 : ℝ) ≤ 1 / 2)
  rw [Real.sqrt_sq hr0.le, Real.log_pow] at hp
  norm_num only [Nat.cast_ofNat] at hp
  have hid :
    ((3 / 7 : ℝ) / Real.sqrt r / (63 / 32) * r ^ 2 +
          (231 / 2500 : ℝ) / ((3 / 7 : ℝ) / Real.sqrt r) * r +
          (231 / 2500 : ℝ) / ((3 / 7 : ℝ) / Real.sqrt r) +
          1839 / 1000) /
        r =
      ((32 / 63 : ℝ) * (3 / 7) + (231 / 2500 : ℝ) * (7 / 3)) * Real.sqrt r +
        (231 / 2500 : ℝ) * (7 / 3) / Real.sqrt r +
        (1839 / 1000 : ℝ) / r := by
    field_simp (disch :=
      first
      | exact hs.ne'
      | exact hr0.ne'
      | norm_num only)
    rw [Real.sq_sqrt hr0.le]
    ring
  have hmul :
    refinedWeight 1 *
          ((3 / 7 : ℝ) / Real.sqrt r / (63 / 32) * r ^ 2 +
            (231 / 2500 : ℝ) / ((3 / 7 : ℝ) / Real.sqrt r) * r +
            (231 / 2500 : ℝ) / ((3 / 7 : ℝ) / Real.sqrt r) +
            1839 / 1000) /
        r =
      refinedWeight 1 *
        (((32 / 63 : ℝ) * (3 / 7) + (231 / 2500 : ℝ) * (7 / 3)) * Real.sqrt r +
          (231 / 2500 : ℝ) * (7 / 3) / Real.sqrt r +
          (1839 / 1000 : ℝ) / r) := by
    rw [mul_div_assoc, hid]
  rw [hmul] at hp
  norm_num only at hp ⊢
  exact hp

/-- Under RH and `r ≥ 522`, the cutoff-minus-full principal gap at scale `r²`
has the displayed one-sided lower bound. Combine the paper-width unit estimate with
the sharp full-series estimate at the same scale. -/
theorem refined_paper_gap_lower (hRH : RiemannHypothesis) {r : ℝ} (hr : 522 ≤ r) :
    r *
          (4 * (∫ u : ℝ in (0 : ℝ)..1, (refinedSixPoleKernel.transform u).re / Real.sqrt u) -
            (refinedSixPoleKernel.function (1 / 2)).re) -
        5 *
          ((231 / 5000 : ℝ) * (6889 / 2700) +
            ((1839 / 1000 : ℝ) * (2 * Real.log r + 21 / 8) + 2) *
                ((918330048 / 17682025 : ℝ) * Real.exp (-(21 / 16 : ℝ))) /
              r) -
        4 * |refinedWeightDeriv 1| *
            ((231 / 5000 : ℝ) * r + (1839 / 1000 : ℝ) * (2 * Real.log r) + 2) /
          r -
        4 * refinedWeight 1 *
          (((32 / 63 : ℝ) * (3 / 7) + (231 / 2500 : ℝ) * (7 / 3)) * Real.sqrt r +
            (231 / 2500 : ℝ) * (7 / 3) / Real.sqrt r +
            (1839 / 1000 : ℝ) / r) ≤
      4 *
          (∑ n ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊,
            (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) n).re) -
        (∑' n : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) n).re := by
  have hr0 : 0 < r := (by norm_num only : (0 : ℝ) < 522).trans_le hr
  have hx : (1 : ℝ) ≤ r ^ 2 := by nlinarith only [hr]
  have hf := refined_unit_paper_scale hRH hr
  have ht := (abs_le.mp (refined_full_sharp_error hRH hx)).2
  rw [Real.sqrt_sq hr0.le, Real.log_pow] at ht
  norm_num only [Nat.cast_ofNat] at ht
  ring_nf at hf ht ⊢
  linarith only [hf, ht]

end PseudoPrime.PrimeTestBounds.MillerRabin
