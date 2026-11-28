/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSixPoleCoordinate
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalLimit656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentIntegral656
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSpectralBudget
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Forward
import Mathlib.Tactic

/-! # Principal Abel zero terms for the shared six-pole Gaussian kernel -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem six_pole_cpow_div {t : ℝ} (ht : 0 < t) (c ρ : ℂ) :
    (c * (t : ℂ) ^ (ρ - 1)).re = (c * (t : ℂ) ^ ρ).re / t := by
  rw [Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr ht.ne'), Complex.cpow_one, ← mul_div_assoc,
    Complex.div_ofReal_re]

/-- The lower physical endpoint contribution, including the boundary from the
integration by parts at one. -/
@[expose]
public noncomputable def gaussianSixPoleRemainder (X : ℝ) (ρ : ℂ) : ℝ :=
  let a : ℝ := 11 / 10
  let b : ℝ := 21 / 8
  let C : ℝ := a ^ 5 * Real.exp (-(a * b)) / 120
  let s := (a : ℂ) + (ρ.im : ℂ) * Complex.I
  let z := b + Real.log X
  let m := (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ)
  let p := m * Complex.exp (((ρ.im * Real.log X : ℝ) : ℂ) * Complex.I)
  3 *
    ((p * (C : ℂ) * Complex.exp (s * ((b : ℂ) - (z : ℂ))) * gaussianSixPoleAnti s (z : ℂ)).re +
      (-m / ρ).re * quarterWeight656 X 1)

/-- Under RH's real-part condition and at nonzero ordinate, the physical Abel
zero term is the shared spectral coefficient plus its lower endpoint correction. -/
public theorem gaussian_six_pole_abel_zero {y : ℝ} (hy : 1 ≤ y ^ 2) {ρ : ℂ} (hre : ρ.re = 1 / 2)
    (him : ρ.im ≠ 0) :
    quarterZeroIntegral656 (y ^ 2) ρ =
      gaussianSpectralContribution y ρ + gaussianSixPoleRemainder (y ^ 2) ρ := by
  let X := y ^ 2
  let U := X * Real.exp (21 / 8)
  let m := (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ)
  have hX : 0 < X := zero_lt_one.trans_le hy
  have hU : X ≤ U := le_mul_of_one_le_right hX.le (Real.one_le_exp (by norm_num only))
  have hρ : ((1 / 2 : ℝ) : ℂ) + (ρ.im : ℂ) * Complex.I = ρ := by rw [← hre, Complex.re_add_im]
  let f := fun t : ℝ ↦ quarterWeight656 X t * ((m * (t : ℂ) ^ ρ).re / t)
  have hf {l r : ℝ} (hl : 0 < l) (hlr : l ≤ r) :
    (∫ t in l..r, (-m * (t : ℂ) ^ (ρ - 1)).re * quarterWeight656 X t) = -(∫ t in l..r, f t) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    have hp : 0 < t := hl.trans_le (Set.uIcc_of_le hlr ▸ ht).1
    change (-m * (t : ℂ) ^ (ρ - 1)).re * quarterWeight656 X t = -f t
    rw [six_pole_cpow_div hp, neg_mul, Complex.neg_re, neg_div, neg_mul, mul_comm]
  have hi {l r : ℝ} (hl : 0 < l) (hlr : l ≤ r) : IntervalIntegrable f MeasureTheory.volume l r := by
    apply ContinuousOn.intervalIntegrable
    have hsub : Set.uIcc l r ⊆ Set.Ioi (0 : ℝ) := fun _ ht ↦ hl.trans_le (Set.uIcc_of_le hlr ▸ ht).1
    apply ((weight_smooth_656 hX).continuousOn.mono hsub).mul
    have hh : ContinuousOn (fun t : ℝ ↦ (m * (t : ℂ) ^ ρ).re) (Set.uIcc l r) :=
      Complex.continuous_re.comp_continuousOn
        (continuousOn_const.mul
          (fun t ht ↦
            (Complex.continuousAt_ofReal_cpow_const t ρ
                (Or.inr (show 0 < t from hsub ht).ne')).continuousWithinAt))
    exact hh.div continuousOn_id (fun t ht ↦ (show 0 < t from hsub ht).ne')
  have he := gaussian_six_pole_physical_integrals hy m him
  have hc := gaussian_six_pole_zero_cutoff hX m ρ.im
  dsimp only at he hc
  rw [hρ] at he hc
  rw [← hc] at he
  change quarterZeroIntegral656 X ρ = _
  unfold quarterZeroIntegral656
  dsimp only
  change
    4 * (∫ t in (1 : ℝ)..X, (-m * (t : ℂ) ^ (ρ - 1)).re * quarterWeight656 X t) -
          (∫ t in (1 : ℝ)..U, (-m * (t : ℂ) ^ (ρ - 1)).re * quarterWeight656 X t) -
          4 * (-m / ρ * (X : ℂ) ^ ρ).re * quarterWeight656 X X +
        3 * (-m / ρ).re * quarterWeight656 X 1 =
      _
  rw [hf zero_lt_one hy, hf zero_lt_one (hy.trans hU), ←
    intervalIntegral.integral_add_adjacent_intervals (hi zero_lt_one hy) (hi hX hU)]
  simp only [neg_div, neg_mul, Complex.neg_re]
  unfold gaussianSpectralContribution gaussianSixPoleRemainder
  dsimp only
  have hm (w : ℂ) :
    (m * w).re = (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) * w.re := by
    simp only [m, ← Complex.ofReal_natCast, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
  rw [← hm, ← mul_assoc m]
  simp only [neg_div, Complex.neg_re]
  change
    4 * quarterWeight656 X X * (m / ρ * (X : ℂ) ^ ρ).re - 3 * (∫ t in (1 : ℝ)..X, f t) +
        (∫ t in X..U, f t) =
      _ at he
  linarith only [he]

/-- The explicit-formula rectangles converge to the full Abel zero
contribution when each summand is written in shared six-pole form. -/
public theorem gaussian_six_pole_abel_limit (hRH : RiemannHypothesis) {y : ℝ} (hy : 1 ≤ y ^ 2) :
    Filter.Tendsto
      (fun k : ℕ ↦
        ∑ ρ ∈ k131ZeroRect k,
          (gaussianSpectralContribution y ρ + gaussianSixPoleRemainder (y ^ 2) ρ))
      Filter.atTop
      (nhds
        (quarterAbelAction656 (y ^ 2)
          (fun t ↦
            (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re))) := by
  apply (quarter_zero_integral_limit_656 hy).congr'
  filter_upwards with k
  apply Finset.sum_congr rfl
  intro ρ hρ
  have hm := Finset.mem_filter.mp hρ
  have hz := (AnalyticNumberTheory.RiemannZeta.mem_riemannZetaZerosInAnyRectangle_iff.mp hm.1).2
  have hr : 0 ≤ ρ.re := not_lt.mp hm.2
  have hre := AnalyticNumberTheory.RiemannZeta.zeta_zero_re_eq_half_of_riemannHypothesis hRH hz hr
  have hh := AnalyticNumberTheory.RiemannZeta.zero_height_gt_two_pi hRH hz hr
  have him := abs_pos.mp ((mul_pos (by norm_num only) Real.pi_pos).trans hh)
  exact gaussian_six_pole_abel_zero hy hre him

end PseudoPrime.PrimeTestBounds.MillerRabin
