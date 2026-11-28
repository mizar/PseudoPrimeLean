/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianCenteredTail
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPrincipalLowZeros
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Midpoint variation from centered finite Mellin moments -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A reciprocal pole on the positive half-line is bounded by the inverse left endpoint. -/
private theorem high_pole_inv_norm_le (a : ℝ) {l t : ℝ} (hl : 0 < l) (ht : l ≤ t) :
    ‖highPoleInv a t‖ ≤ l⁻¹ := by
  have h := Complex.abs_im_le_norm ((a : ℂ) + Complex.I * (t : ℂ))
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, zero_mul, one_mul, zero_add] at h
  rw [highPoleInv, norm_inv]
  exact
    (inv_le_inv₀ (hl.trans_le (ht.trans ((le_abs_self t).trans h))) hl).mpr
      (ht.trans ((le_abs_self t).trans h))

/-- The derivative of a product of inverse powers uses the sum of their exponents. -/
private theorem high_inverse_term_deriv (a b : ℝ) {l t : ℝ} (ha : 0 < a) (hb : 0 < b) (hl : 0 < l)
    (ht : l ≤ t) (j : ℕ) :
    ∃ z : ℂ,
      HasDerivAt (fun x ↦ highPoleInv a x ^ (j + 1) * highPoleInv b x) z t ∧
        ‖z‖ ≤ (j + 2 : ℕ) / l ^ (j + 3) := by
  have h := ((high_pole_inv_deriv ha t).pow (j + 1)).mul (high_pole_inv_deriv hb t)
  refine ⟨_, h, (norm_add_le _ _).trans ?_⟩
  let u := ‖highPoleInv a t‖
  let v := ‖highPoleInv b t‖
  let R := l⁻¹
  have hu : u ≤ R := high_pole_inv_norm_le a hl ht
  have hv : v ≤ R := high_pole_inv_norm_le b hl ht
  have hR : 0 ≤ R := inv_nonneg.mpr hl.le
  have hu₀ : 0 ≤ u := norm_nonneg _
  have hv₀ : 0 ≤ v := norm_nonneg _
  have hup (n : ℕ) : u ^ n ≤ R ^ n := pow_le_pow_left₀ hu₀ hu n
  have h₁ :=
    mul_le_mul
      (mul_le_mul (mul_le_mul_of_nonneg_left (hup j) (Nat.cast_nonneg (α := ℝ) (j + 1))) (hup 2)
        (sq_nonneg u) (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hR _)))
      hv hv₀ (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hR _)) (sq_nonneg R))
  have h₂ := mul_le_mul (hup (j + 1)) (pow_le_pow_left₀ hv₀ hv 2) (sq_nonneg v) (pow_nonneg hR _)
  simp only [norm_mul, norm_pow, norm_neg, Complex.norm_I, Complex.norm_natCast, one_mul,
    Nat.add_sub_cancel, Pi.pow_apply]
  change ((j + 1 : ℕ) : ℝ) * u ^ j * u ^ 2 * v + u ^ (j + 1) * v ^ 2 ≤ _
  refine (add_le_add h₁ h₂).trans_eq ?_
  have e₁ : R ^ j * R ^ 2 * R = R ^ (j + 3) := by rw [← pow_add, ← pow_succ]
  have e₂ : R ^ (j + 1) * R ^ 2 = R ^ (j + 3) := by rw [← pow_add]
  rw [mul_assoc (((j + 1 : ℕ) : ℝ)), mul_assoc (((j + 1 : ℕ) : ℝ)), e₁, e₂]
  simp only [R, inv_pow, div_eq_mul_inv, Nat.cast_add, Nat.cast_ofNat]
  ring

/-- Differentiate the grouped finite sum with a common left endpoint for both poles. -/
private theorem high_inverse_sum_deriv (a b : ℝ) (J : Finset ℕ) (c : ℕ → ℝ) {l t : ℝ} (ha : 0 < a)
    (hb : 0 < b) (hl : 0 < l) (ht : l ≤ t) :
    ∃ z : ℂ,
      HasDerivAt (fun x ↦ ∑ j ∈ J, (c j : ℂ) * (highPoleInv a x ^ (j + 1) * highPoleInv b x)) z t ∧
        ‖z‖ ≤ ∑ j ∈ J, |c j| * ((j + 2 : ℕ) : ℝ) / l ^ (j + 3) := by
  choose z hdz hz using fun j : ℕ ↦ high_inverse_term_deriv a b ha hb hl ht j
  refine ⟨_, HasDerivAt.fun_sum (fun j _ ↦ (hdz j).const_mul (c j : ℂ)), ?_⟩
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ ↦ ?_))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (hz j) (abs_nonneg _)

/-- The centered finite moment is expressed using powers of the reciprocal poles. -/
private theorem high_centered_inverse_eq (K : HighGaussianKernel) (t : ℝ) :
    let P := highCenteredProfile K
    let a := (K.pole : ℝ)
    highPrincipalMultiplier K t =
      highHeightKernel K t +
        (4 * Complex.exp (-(5 * (K.pole : ℂ)))) *
          ∑ j ∈ Finset.range (P.natDegree + 1),
            ((principalMomentCoeff P 5 j * (j.factorial : ℝ) : ℝ) : ℂ) *
              (highPoleInv a t ^ (j + 1) * highPoleInv (1 / 2) t) := by
  intro P a
  rw [high_principal_multiplier_centered]
  change
    highHeightKernel K t +
        (4 * Complex.exp (-(5 * (K.pole : ℂ)))) * (complexLogPolyMoment P 5 _ / _) =
      _
  congr 2
  rw [principal_moment_by_power, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  have hhalf : ((1 / 2 : ℝ) : ℂ) = 1 / 2 := by
    simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  simp only [highPoleInv, a, Complex.ofReal_ratCast, hhalf, Complex.ofReal_mul,
    Complex.ofReal_natCast, add_comm (K.pole : ℂ) (Complex.I * (t : ℂ))]
  simp only [div_eq_mul_inv, inv_pow]
  ring

/-- The derivative cap for the centered representation at a positive left endpoint. -/
@[expose]
public noncomputable def highCenteredDerivCap (K : HighGaussianKernel) (l : ℝ) : ℝ :=
  let P := highCenteredProfile K
  let a := (K.pole : ℝ)
  let M₀ := highCompactMass K
  let M₁ := highCompactSlope K
  (K.normalization : ℝ) * (5 * M₀ ^ 2 / l ^ 4 + 4 * M₀ ^ 2 / l ^ 5 + 4 * a * M₀ * M₁ / l ^ 6) +
    4 * Real.exp (-(5 * a)) *
      ∑ j ∈ Finset.range (P.natDegree + 1),
        |principalMomentCoeff P 5 j * (j.factorial : ℝ)| * ((j + 2 : ℕ) : ℝ) / l ^ (j + 3)

/-- The finite centered representation gives the derivative bound without an integral estimate. -/
public theorem high_centered_deriv_le (K : HighGaussianKernel) {l t : ℝ} (hl : 0 < l) (ht : l ≤ t) :
    DifferentiableAt ℝ (highPrincipalMultiplier K) t ∧
      ‖deriv (highPrincipalMultiplier K) t‖ ≤ highCenteredDerivCap K l := by
  let P := highCenteredProfile K
  let a := (K.pole : ℝ)
  let M₀ := highCompactMass K
  let M₁ := highCompactSlope K
  have ha : 0 < a := (by norm_num only : (0 : ℝ) < 1 / 2).trans (high_gaussian_pole_gt K)
  have hκ : 0 ≤ (K.normalization : ℝ) := Rat.cast_nonneg.mpr (high_gaussian_normalization_pos K).le
  have hM₁ : 0 ≤ M₁ := Finset.sum_nonneg (fun _ _ ↦ mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))
  have hM₀ : 0 ≤ M₀ := Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
  have hdiv (c : ℝ) (hc : 0 ≤ c) (n : ℕ) : c / t ^ n ≤ c / l ^ n :=
    div_le_div_of_nonneg_left hc (pow_pos hl _) (pow_le_pow_left₀ hl.le ht _)
  have hsq :=
    (high_height_kernel_deriv_bound K (hl.trans_le ht)).trans
      (mul_le_mul_of_nonneg_left
        (add_le_add
          (add_le_add (hdiv _ (mul_nonneg (by norm_num only) (sq_nonneg _)) 4)
            (hdiv _ (mul_nonneg (by norm_num only) (sq_nonneg _)) 5))
          (hdiv _ (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num only) ha.le) hM₀) hM₁) 6))
        hκ)
  obtain ⟨z, hz, hn⟩ :=
    high_inverse_sum_deriv a (1 / 2) (Finset.range (P.natDegree + 1))
      (fun j ↦ principalMomentCoeff P 5 j * (j.factorial : ℝ)) ha (by norm_num only) hl ht
  have h :=
    ((high_height_kernel_differentiable K t).hasDerivAt).add
      (hz.const_mul (4 * Complex.exp (-(5 * (K.pole : ℂ)))))
  have he : ‖Complex.exp (-(5 * (K.pole : ℂ)))‖ = Real.exp (-(5 * a)) := by
    rw [← Complex.ofReal_ratCast, ← Complex.ofReal_ofNat (n := 5), ← Complex.ofReal_mul, ←
      Complex.ofReal_neg, Complex.norm_exp, Complex.ofReal_re]
  have hh := h.congr_of_eventuallyEq (Filter.Eventually.of_forall (high_centered_inverse_eq K))
  refine ⟨hh.differentiableAt, ?_⟩
  rw [hh.deriv, highCenteredDerivCap]
  refine (norm_add_le _ _).trans (add_le_add hsq ?_)
  rw [norm_mul, norm_mul, Complex.norm_ofNat, he]
  exact mul_le_mul_of_nonneg_left hn (mul_nonneg (by norm_num only) (Real.exp_pos _).le)

/-- A positive bracket can be evaluated at its midpoint with the centered derivative cap. -/
public theorem high_centered_midpoint_le (K : HighGaussianKernel) {l r t : ℝ} (hl : 0 < l)
    (ht : t ∈ Set.Icc l r) :
    ‖highPrincipalMultiplier K t‖ ≤
      ‖highPrincipalMultiplier K ((l + r) / 2)‖ + highCenteredDerivCap K l * ((r - l) / 2) := by
  let m := (l + r) / 2
  have hm : m ∈ Set.Icc l r := by
    have h := ht.1.trans ht.2
    exact
      ⟨by
        dsimp only [m]; linarith only [h], by
        dsimp only [m]; linarith only [h]⟩
  have hr : |t - m| ≤ (r - l) / 2 :=
    abs_le.mpr
      ⟨by
        dsimp only [m]; linarith only [ht.1], by
        dsimp only [m]; linarith only [ht.2]⟩
  have hd (x : ℝ) (hx : x ∈ Set.Icc l r) := high_centered_deriv_le K hl hx.1
  have hv :=
    Convex.norm_image_sub_le_of_norm_deriv_le (fun x hx ↦ (hd x hx).1) (fun x hx ↦ (hd x hx).2)
      (convex_Icc l r) hm ht
  have hcap := (norm_nonneg _).trans (hd t ht).2
  have hv' :
    ‖highPrincipalMultiplier K t - highPrincipalMultiplier K m‖ ≤
      highCenteredDerivCap K l * |t - m| := by
    simpa only [Real.norm_eq_abs] using hv
  calc
    _ =
        ‖highPrincipalMultiplier K m +
            (highPrincipalMultiplier K t - highPrincipalMultiplier K m)‖ :=
      by rw [add_sub_cancel]
    _ ≤ _ :=
      (norm_add_le _ _).trans (add_le_add le_rfl (hv'.trans (mul_le_mul_of_nonneg_left hr hcap)))

/-- The centered cap multiplied by the half-width of a certified positive zero bracket. -/
public noncomputable def highCenteredBracketError (K : HighGaussianKernel) (i : Fin 29) : ℝ :=
  highCenteredDerivCap K (AnalyticNumberTheory.RiemannZeta.lowZero100Lower i : ℝ) / 200

/-- Evaluate the certified positive zero brackets without a separate head-integral cap. -/
public theorem high_centered_low_midpoint (K : HighGaussianKernel) (g : Fin 29 → ℝ)
    (hlo : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g)
    (hhi : AnalyticNumberTheory.RiemannZeta.LowZero100UpperBounds g) (i : Fin 29) :
    ‖highPrincipalMultiplier K (g i)‖ ≤
      ‖highPrincipalMultiplier K (highZeroBracketMid i : ℝ)‖ + highCenteredBracketError K i := by
  let l := AnalyticNumberTheory.RiemannZeta.lowZero100Lower i
  have h :=
    high_centered_midpoint_le K (l := (l : ℝ)) (r := (l : ℝ) + 1 / 100)
      (Rat.cast_pos.mpr (high_zero_left_pos i)) ⟨hlo i, hhi i⟩
  have hm (x : ℝ) : (x + (x + 1 / 100)) / 2 = x + 1 / 200 := by ring
  have hw (x : ℝ) : (x + 1 / 100 - x) / 2 = 1 / 200 := by ring
  simpa only [hm, hw, highZeroBracketMid, highCenteredBracketError, Rat.cast_add, Rat.cast_div,
    Rat.cast_one, Rat.cast_ofNat, mul_one_div, l] using h

/-- Summing the centered errors controls the entire family of 29 positive brackets. -/
public theorem high_centered_low_sum_le (K : HighGaussianKernel) (g : Fin 29 → ℝ)
    (hlo : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g)
    (hhi : AnalyticNumberTheory.RiemannZeta.LowZero100UpperBounds g) :
    (∑ i, ‖highPrincipalMultiplier K (g i)‖) ≤
      (∑ i, ‖highPrincipalMultiplier K (highZeroBracketMid i : ℝ)‖) +
        ∑ i, highCenteredBracketError K i := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ ↦ high_centered_low_midpoint K g hlo hhi i

end PseudoPrime.PrimeTestBounds.MillerRabin
