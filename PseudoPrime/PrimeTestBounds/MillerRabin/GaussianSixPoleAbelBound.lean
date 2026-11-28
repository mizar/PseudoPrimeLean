/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSixPoleRemainder
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalTrivial656
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSpectralBudget
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Forward
import Mathlib.Analysis.Complex.ExponentialBounds
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterKernel656
import Mathlib.Tactic

/-! # Bounds for the full shared Gaussian Abel zero term -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem gaussian_ordinate_mass_le (hRH : RiemannHypothesis) (S : Finset ℂ)
    (hz : ∀ ρ ∈ S, riemannZeta ρ = 0) (hr : ∀ ρ ∈ S, 0 ≤ ρ.re) :
    (∑ ρ ∈ S, (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| ^ 2) ≤
      1 / 10 := by
  have hm := AnalyticNumberTheory.RiemannZeta.sum_zetaZeroMultiplicity_invNormSq_le hRH S hz hr
  simp only [← Complex.sq_norm] at hm
  have hh (ρ : ℂ) (hρ : ρ ∈ S) : 1 ≤ |ρ.im| := by
    have h := AnalyticNumberTheory.RiemannZeta.zero_height_gt_two_pi hRH (hz ρ hρ) (hr ρ hρ)
    linarith only [h, Real.pi_gt_three]
  have hc (ρ : ℂ) (hρ : ρ ∈ S) : ‖ρ‖ ^ 2 ≤ 2 * |ρ.im| ^ 2 := by
    have he :=
      AnalyticNumberTheory.RiemannZeta.zeta_zero_re_eq_half_of_riemannHypothesis hRH (hz ρ hρ)
        (hr ρ hρ)
    rw [Complex.sq_norm, Complex.normSq_apply, he, sq_abs]
    have hp := pow_le_pow_left₀ zero_le_one (hh ρ hρ) 2
    rw [sq_abs] at hp
    nlinarith only [hp]
  have hsum :
    (∑ ρ ∈ S, (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| ^ 2) ≤
      2 *
        ∑ ρ ∈ S,
          (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) / ‖ρ‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ρ hρ
    have hp : 0 < ‖ρ‖ := zero_lt_one.trans_le ((hh ρ hρ).trans (Complex.abs_im_le_norm _))
    rw [← mul_div_assoc,
      div_le_div_iff₀ (pow_pos (zero_lt_one.trans_le (hh ρ hρ)) 2) (pow_pos hp 2)]
    calc
      _ ≤ (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) * (2 * |ρ.im| ^ 2) :=
        mul_le_mul_of_nonneg_left (hc ρ hρ) (Nat.cast_nonneg _)
      _ = _ := by ring
  linarith only [hsum, hm, AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_231_div_10000]

/-- Under RH, the full principal Abel zero term is bounded by the common
spectral allowance and an exponentially decreasing lower endpoint cost. -/
public theorem gaussian_six_pole_abel_bound (hRH : RiemannHypothesis) {y : ℝ} (hy : 1 ≤ y ^ 2)
    (hzmin : 10 ≤ (21 / 8 : ℝ) + Real.log (y ^ 2)) :
    let a : ℝ := 11 / 10
    let z := (21 / 8 : ℝ) + Real.log (y ^ 2)
    |quarterAbelAction656 (y ^ 2)
          (fun t ↦ (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re)| ≤
      1 / 40 + (3 * (a ^ 5 * Real.exp (-(a * z)) / 120) * (2 * z ^ 5)) / 10 := by
  intro a z
  let D := 3 * (a ^ 5 * Real.exp (-(a * z)) / 120) * (2 * z ^ 5)
  have hz0 : 0 ≤ z := add_nonneg (by norm_num only) (Real.log_nonneg hy)
  have hD : 0 ≤ D :=
    mul_nonneg
      (mul_nonneg (by norm_num only)
        (div_nonneg (mul_nonneg (pow_nonneg (by norm_num only [a]) _) (Real.exp_pos _).le)
          (by norm_num only)))
      (mul_nonneg (by norm_num only) (pow_nonneg hz0 _))
  apply le_of_tendsto (gaussian_six_pole_abel_limit hRH hy).abs
  filter_upwards with k
  let S := k131ZeroRect k
  have hz (ρ : ℂ) (hρ : ρ ∈ S) : riemannZeta ρ = 0 :=
    (AnalyticNumberTheory.RiemannZeta.mem_riemannZetaZerosInAnyRectangle_iff.mp
        (Finset.mem_filter.mp hρ).1).2
  have hr (ρ : ℂ) (hρ : ρ ∈ S) : 0 ≤ ρ.re := not_lt.mp (Finset.mem_filter.mp hρ).2
  have hphase :=
    gaussian_spectral_finite_lt hRH S (gaussianSpectralContribution y) hz hr
      (fun ρ hρ ↦ gaussian_spectral_contribution_le hRH (hz ρ hρ) (hr ρ hρ))
  have hrem : |∑ ρ ∈ S, gaussianSixPoleRemainder (y ^ 2) ρ| ≤ D / 10 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      _ ≤
          ∑ ρ ∈ S,
            D *
              ((AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| ^ 2) :=
        by
        apply Finset.sum_le_sum
        intro ρ hρ
        have he :=
          AnalyticNumberTheory.RiemannZeta.zeta_zero_re_eq_half_of_riemannHypothesis hRH (hz ρ hρ)
            (hr ρ hρ)
        have hh := AnalyticNumberTheory.RiemannZeta.zero_height_gt_two_pi hRH (hz ρ hρ) (hr ρ hρ)
        exact gaussian_six_pole_remainder_bound hzmin he (by linarith only [hh, Real.pi_gt_three])
      _ ≤ _ := by
        rw [← Finset.mul_sum, ← mul_one_div]
        exact mul_le_mul_of_nonneg_left (gaussian_ordinate_mass_le hRH S hz hr) hD
  change
    |∑ ρ ∈ S, (gaussianSpectralContribution y ρ + gaussianSixPoleRemainder (y ^ 2) ρ)| ≤
      1 / 40 + D / 10
  rw [Finset.sum_add_distrib]
  exact (abs_add_le _ _).trans (add_le_add hphase.le hrem)

private theorem six_pole_coord_ge_fourteen {y : ℝ} (hy : 331 ≤ y) :
    (14 : ℝ) ≤ 21 / 8 + Real.log (y ^ 2) := by
  have hE : Real.exp 1 ≤ (68 / 25 : ℝ) := Real.exp_one_lt_d9.le.trans (by norm_num only)
  have he : Real.exp (23 : ℝ) ≤ (331 : ℝ) ^ 4 := by
    rw [show (23 : ℝ) = (23 : ℕ) * (1 : ℝ) by norm_num only, Real.exp_natCast_mul]
    exact (pow_le_pow_left₀ (Real.exp_pos _).le hE _).trans (by norm_num only)
  have hd : Real.exp (23 / 2 : ℝ) ≤ (331 : ℝ) ^ 2 := by
    apply le_of_pow_le_pow_left₀ (n := 2) (by decide) (by norm_num only)
    rw [← Real.exp_natCast_mul, show (2 : ℕ) * (23 / 2 : ℝ) = 23 by norm_num only, ← pow_mul]
    exact he
  have hl : (23 / 2 : ℝ) ≤ Real.log (y ^ 2) := by
    apply (Real.le_log_iff_exp_le (pow_pos (lt_of_lt_of_le (by norm_num only) hy) 2)).mpr
    exact hd.trans (pow_le_pow_left₀ (by norm_num only) hy 2)
  linarith only [hl]

private theorem six_pole_endpoint_budget {z : ℝ} (hz : 14 ≤ z) :
    (3 * ((11 / 10 : ℝ) ^ 5 * Real.exp (-((11 / 10 : ℝ) * z)) / 120) * (2 * z ^ 5)) / 10 ≤
      1 / 1000 := by
  have hq : z / 14 ≤ Real.exp ((z - 14) / 14) := by
    have h := Real.add_one_le_exp ((z - 14) / 14)
    linarith only [h]
  have ht : (z / 14) ^ 5 ≤ Real.exp ((11 / 10 : ℝ) * (z - 14)) := by
    refine
      (pow_le_pow_left₀ (div_nonneg ((by norm_num only : (0 : ℝ) ≤ 14).trans hz) (by norm_num only))
            hq 5).trans
        ?_
    rw [← Real.exp_natCast_mul]
    apply Real.exp_le_exp.mpr
    norm_num only [Nat.cast_ofNat]
    linarith only [hz]
  have hprod : z ^ 5 * Real.exp (-((11 / 10 : ℝ) * z)) ≤ 14 ^ 5 * Real.exp (-(77 / 5 : ℝ)) := by
    rw [div_pow, div_le_iff₀ (by norm_num only : (0 : ℝ) < 14 ^ 5)] at ht
    refine (mul_le_mul_of_nonneg_right ht (Real.exp_pos _).le).trans_eq ?_
    rw [mul_comm (Real.exp _) (14 ^ 5), mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hE : (271 / 100 : ℝ) ≤ Real.exp 1 :=
    (by norm_num only : (271 / 100 : ℝ) ≤ 2.7182818283).trans Real.exp_one_gt_d9.le
  have he : (271 / 100 : ℝ) ^ 15 * (7 / 5) ≤ Real.exp (77 / 5 : ℝ) := by
    rw [show (77 / 5 : ℝ) = (15 : ℕ) * (1 : ℝ) + 2 / 5 by norm_num only, Real.exp_add,
      Real.exp_natCast_mul]
    apply
      mul_le_mul (pow_le_pow_left₀ (by norm_num only) hE _) _ (by norm_num only)
        (pow_nonneg (Real.exp_pos _).le _)
    exact (by norm_num only : (7 / 5 : ℝ) ≤ 2 / 5 + 1).trans (Real.add_one_le_exp _)
  have hb : Real.exp (-(77 / 5 : ℝ)) ≤ ((271 / 100 : ℝ) ^ 15 * (7 / 5))⁻¹ := by
    rw [Real.exp_neg]
    exact (inv_le_inv₀ (Real.exp_pos _) (by norm_num only)).mpr he
  have hh :=
    mul_le_mul_of_nonneg_left
      (hprod.trans (mul_le_mul_of_nonneg_left hb (by norm_num only : (0 : ℝ) ≤ 14 ^ 5)))
      (by norm_num only : (0 : ℝ) ≤ (11 / 10 : ℝ) ^ 5 / 200)
  calc
    _ = ((11 / 10 : ℝ) ^ 5 / 200) * (z ^ 5 * Real.exp (-((11 / 10 : ℝ) * z))) := by ring
    _ ≤ _ := hh.trans (by norm_num only)

/-- The shared principal Abel zero contribution costs at most 0.026 on the
physical-radius range of the compressed K137 and K197 cells. -/
public theorem gaussian_six_pole_abel_bound_of_331 (hRH : RiemannHypothesis) {y : ℝ}
    (hy : 331 ≤ y) :
    |quarterAbelAction656 (y ^ 2)
          (fun t ↦ (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re)| ≤
      26 / 1000 := by
  have hz := six_pole_coord_ge_fourteen hy
  have hy1 : (1 : ℝ) ≤ y ^ 2 := one_le_pow₀ ((by norm_num only : (1 : ℝ) ≤ 331).trans hy)
  have h := gaussian_six_pole_abel_bound hRH hy1 ((by norm_num only : (10 : ℝ) ≤ 14).trans hz)
  exact h.trans (by linarith only [six_pole_endpoint_budget hz])

/-- In the compressed-cell range, the principal arithmetic prefix minus
the full kernel sum admits the explicit-formula lower bound with zero cost 0.026. -/
public theorem gaussian_six_pole_principal_lower (hRH : RiemannHypothesis) {y : ℝ} (hy : 331 ≤ y) :
    let X := y ^ 2
    let B := X * Real.exp (21 / 8)
    let S := fun n : ℕ ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) X n).re
    let W := quarterWeight656 X
    4 * (∫ t in (1 : ℝ)..X, W t) - (∫ t in (1 : ℝ)..B, W t) +
          4 * W X * (Chebyshev.psi X - X + Real.log (2 * Real.pi)) +
          3 * (1 - Real.log (2 * Real.pi)) * W 1 -
        26 / 1000 -
        quarterAbelAction656 X AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries ≤
      4 * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, S n) - (∑' n : ℕ, S n) := by
  intro X B S W
  have hX : 1 ≤ X := one_le_pow₀ ((by norm_num only : (1 : ℝ) ≤ 331).trans hy)
  have hZ := neg_le_of_abs_le (gaussian_six_pole_abel_bound_of_331 hRH hy)
  have he := quarter_principal_explicit_656 hX
  dsimp only at he
  change _ ≤ 4 * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, S n) - (∑' n : ℕ, S n)
  rw [he]
  dsimp only [B, W]
  linarith only [hZ]

/-- On the compressed-cell radius range, bound the principal arithmetic
difference with both nontrivial and trivial zero costs included. -/
public theorem gaussian_six_pole_principal_bound (hRH : RiemannHypothesis) {y : ℝ} (hy : 331 ≤ y) :
    let X := y ^ 2
    let B := X * Real.exp (21 / 8)
    let S := fun n : ℕ ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) X n).re
    let W := quarterWeight656 X
    4 * (∫ t in (1 : ℝ)..X, W t) - (∫ t in (1 : ℝ)..B, W t) +
          4 * W X * (Chebyshev.psi X - X + Real.log (2 * Real.pi)) +
          (1.7875 - 3 * Real.log (2 * Real.pi)) * W 1 -
        0.026012 ≤
      4 * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, S n) - (∑' n : ℕ, S n) := by
  intro X B S W
  have ht :=
    quarter_trivial_bound_656_from_coord ((by norm_num only : (322 : ℝ) ≤ 331).trans hy)
      (six_pole_coord_ge_fourteen hy)
  have h := gaussian_six_pole_principal_lower hRH hy
  dsimp only [X, B, S, W] at *
  linarith only [h, ht]

/-- Replace the weighted integrals in the principal comparison by the
Mellin mass and the omitted mass at one. The signed psi boundary is retained
for each compressed cell's certified prefix bound. -/
public theorem gaussian_six_pole_principal_mass (hRH : RiemannHypothesis) {y : ℝ} (hy : 331 ≤ y) :
    let X := y ^ 2
    let S := fun n : ℕ ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) X n).re
    let W := quarterWeight656 X
    0.71780481 * y + 4 * W X * (Chebyshev.psi X - X + Real.log (2 * Real.pi)) -
        (100 / 31 - 1.7875 + 3 * Real.log (2 * Real.pi)) * W 1 -
        0.026012 <
      4 * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, S n) - (∑' n : ℕ, S n) := by
  intro X S W
  have hp : 0 ≤ y := (by norm_num only : (0 : ℝ) ≤ 331).trans hy
  have hX : 1 ≤ X := one_le_pow₀ ((by norm_num only : (1 : ℝ) ≤ 331).trans hy)
  have hi := quarter_integral_difference_656 ((by norm_num only : (322 : ℝ) ≤ 331).trans hy)
  have hm := quarter_missing_mass_ratio_656 hX (six_pole_coord_ge_fourteen hy)
  change Real.sqrt (y ^ 2) * _ ≤ _ at hm
  rw [Real.sqrt_sq hp] at hm
  have hb := gaussian_six_pole_principal_bound hRH hy
  dsimp only [X, S, W] at hi hm hb ⊢
  linarith only [hi, hm, hb]

/-- On a positive radius interval, a signed psi lower bound uses the left
radius for a negative numerator and the right radius otherwise. -/
public theorem gaussian_six_pole_psi_box {l y u e : ℝ} (hl : 0 < l) (hly : l ≤ y) (hyu : y ≤ u)
    (he : e ≤ Chebyshev.psi (y ^ 2) - y ^ 2) :
    let w := (quarterKernel656.transform 1).re
    4 * w * (if e ≤ 0 then e / l else e / u) ≤
      4 * quarterWeight656 (y ^ 2) (y ^ 2) * (Chebyshev.psi (y ^ 2) - y ^ 2) := by
  intro w
  have hy := hl.trans_le hly
  have hu := hy.trans_le hyu
  have hw : 0 ≤ w := quarterKernel656.mellin_nonneg 1 zero_lt_one
  have hcut : quarterWeight656 (y ^ 2) (y ^ 2) = w / y := by
    rw [quarter_cutoff_weight_656 (pow_pos hy 2), Real.sqrt_sq hy.le]
  have hd : (if e ≤ 0 then e / l else e / u) ≤ e / y := by
    split
    · rename_i hn
      rw [div_le_div_iff₀ hl hy]
      exact mul_le_mul_of_nonpos_left hly hn
    · rename_i hp
      rw [div_le_div_iff₀ hu hy]
      exact mul_le_mul_of_nonneg_left hyu (le_of_not_ge hp)
  have hb :=
    mul_le_mul_of_nonneg_left (hd.trans (div_le_div_of_nonneg_right he hy.le))
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4) hw)
  rw [hcut]
  convert hb using 1
  ring

/-- The compressed-cell principal bound takes a signed psi floor and an
upper bound on the weight at one. The positive logarithmic term uses the
right endpoint, independently of the sign of the psi floor. -/
public theorem gaussian_six_pole_principal_box (hRH : RiemannHypothesis) {l y u e H : ℝ}
    (hl : 331 ≤ l) (hly : l ≤ y) (hyu : y ≤ u) (he : e ≤ Chebyshev.psi (y ^ 2) - y ^ 2)
    (hH : quarterWeight656 (y ^ 2) 1 ≤ H) :
    let X := y ^ 2
    let w := (quarterKernel656.transform 1).re
    let c := Real.log (2 * Real.pi)
    let S := fun n : ℕ ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) X n).re
    0.71780481 * y + 4 * w * ((if e ≤ 0 then e / l else e / u) + c / u) -
        (100 / 31 - 1.7875 + 3 * c) * H -
        0.026012 <
      4 * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, S n) - (∑' n : ℕ, S n) := by
  intro X w c S
  have hl0 : 0 < l := (by norm_num only : (0 : ℝ) < 331).trans_le hl
  have hy0 := hl0.trans_le hly
  have hu0 := hy0.trans_le hyu
  have hw : 0 ≤ w := quarterKernel656.mellin_nonneg 1 zero_lt_one
  have hc : 0 ≤ c := Real.log_nonneg (by linarith only [Real.pi_gt_three])
  have hcut : quarterWeight656 X X = w / y := by
    rw [quarter_cutoff_weight_656 (pow_pos hy0 2), Real.sqrt_sq hy0.le]
  have hP := gaussian_six_pole_psi_box hl0 hly hyu he
  have hlog : 4 * w * (c / u) ≤ 4 * quarterWeight656 X X * c := by
    have hd : c / u ≤ c / y := by
      rw [div_le_div_iff₀ hu0 hy0]
      exact mul_le_mul_of_nonneg_left hyu hc
    have h := mul_le_mul_of_nonneg_left hd (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4) hw)
    rw [hcut]
    convert h using 1
    ring
  have hlo : 0 ≤ (100 / 31 - 1.7875 + 3 * c : ℝ) := by linarith only [hc]
  have hW := mul_le_mul_of_nonneg_left hH hlo
  have hm := gaussian_six_pole_principal_mass hRH (hl.trans hly)
  change _ < 4 * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, S n) - (∑' n : ℕ, S n)
  dsimp only [X, S, w, c] at *
  linarith only [hP, hlog, hW, hm]

/-- On the compressed Gaussian range the lower-end weight is uniformly
at most 1/600. This follows from the same exponential estimate as the
lower-end correction to the zero sum. -/
public theorem gaussian_six_pole_endpoint_weight {y : ℝ} (hy : 331 ≤ y) :
    quarterWeight656 (y ^ 2) 1 ≤ 1 / 600 := by
  have he := six_pole_endpoint_budget (six_pole_coord_ge_fourteen hy)
  rw [quarterWeight656, one_div, Real.log_inv, sub_neg_eq_add, Real.sqrt_one, div_one, one_mul]
  have h := mul_le_mul_of_nonneg_left he (by norm_num only : (0 : ℝ) ≤ 5 / 3)
  convert h using 1 <;> ring

end PseudoPrime.PrimeTestBounds.MillerRabin
