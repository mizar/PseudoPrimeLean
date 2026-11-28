/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighKernelHeight
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPrincipalHeadDeriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! # Height variation of the complete principal zero coefficient -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The middle value in H25 with the physical scaling included. -/
@[expose]
public noncomputable def highPrincipalEdge (K : HighGaussianKernel) : ℝ :=
  Real.exp (-5 * (K.pole : ℝ)) * K.realProfile.eval 5

/-- The principal multiplier in H25, before multiplying by the zero multiplicity. -/
@[expose]
public noncomputable def highPrincipalMultiplier (K : HighGaussianKernel) (t : ℝ) : ℂ :=
  -3 * highHeightKernel K t + 4 * highPrincipalHead K t +
    4 * ((highPrincipalEdge K : ℂ) / ((1 / 2 : ℂ) + Complex.I * t))

/-- The sum of the three derivative charges in H26 for positive height. -/
@[expose]
public noncomputable def highPrincipalDerivCap (K : HighGaussianKernel) (t : ℝ) : ℝ :=
  let a := (K.pole : ℝ)
  let M₀ := highCompactMass K
  let M₁ := highCompactSlope K
  3 * (K.normalization : ℝ) * (5 * M₀ ^ 2 / t ^ 4 + 4 * M₀ ^ 2 / t ^ 5 + 4 * a * M₀ * M₁ / t ^ 6) +
    4 * highPrincipalHeadCap K / t ^ 2 +
    4 * |highPrincipalEdge K| / (t ^ 2 + 1 / 4)

private theorem high_head_differentiable (K : HighGaussianKernel) (t : ℝ) :
    DifferentiableAt ℝ (highPrincipalHead K) t := by
  have he :
    highPrincipalHead K = fun x ↦
      ∫ v in (0 : ℝ)..5, principalHeadIntegrand K.realProfile K.pole 5 x v := by
    funext x
    simpa only [highPrincipalHead, Complex.ofReal_ofNat] using
      (principal_head_integral_eq K.realProfile K.pole 5 x).symm
  rw [he]
  exact (principal_head_height_deriv K.realProfile K.pole 5 t).differentiableAt

private theorem high_edge_differentiable (w t : ℝ) :
    DifferentiableAt ℝ (fun u : ℝ ↦ (w : ℂ) / ((1 / 2 : ℂ) + Complex.I * u)) t := by
  refine (hasDerivAt_const t (w : ℂ)).differentiableAt.div ?_ ?_
  · fun_prop
  · intro h
    have he := congrArg Complex.re h
    norm_num only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero, Complex.zero_re, Complex.div_re,
      Complex.one_re, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat,
      Complex.normSq_ofNat] at he

/-- The complete principal multiplier is differentiable on the height line. -/
public theorem high_principal_multiplier_deriv (K : HighGaussianKernel) (t : ℝ) :
    HasDerivAt (highPrincipalMultiplier K)
      (-3 * deriv (highHeightKernel K) t + 4 * deriv (highPrincipalHead K) t +
        4 * deriv (fun u : ℝ ↦ (highPrincipalEdge K : ℂ) / ((1 / 2 : ℂ) + Complex.I * u)) t)
      t := by
  exact
    ((((high_height_kernel_differentiable K t).hasDerivAt.const_mul (-3 : ℂ)).add
          ((high_head_differentiable K t).hasDerivAt.const_mul (4 : ℂ))).add
      ((high_edge_differentiable (highPrincipalEdge K) t).hasDerivAt.const_mul (4 : ℂ)))

/-- The complete derivative satisfies the H26 bound at every positive height. -/
public theorem high_principal_multiplier_deriv_bound (K : HighGaussianKernel) {t : ℝ} (ht : 0 < t) :
    ‖deriv (highPrincipalMultiplier K) t‖ ≤ highPrincipalDerivCap K t := by
  rw [(high_principal_multiplier_deriv K t).deriv]
  refine (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl) |>.trans ?_
  simp only [norm_mul, norm_neg, Complex.norm_ofNat, principal_edge_deriv_norm]
  have hk := high_height_kernel_deriv_bound K ht
  have hh := high_principal_head_deriv_bound K ht.ne'
  change _ ≤ highPrincipalHeadCap K / t ^ 2 at hh
  refine
    (add_le_add
          (add_le_add (mul_le_mul_of_nonneg_left hk (by norm_num only))
            (mul_le_mul_of_nonneg_left hh (by norm_num only)))
          le_rfl).trans_eq
      ?_
  unfold highPrincipalDerivCap
  ring

/-- The H26 cap decreases as the positive height increases. -/
public theorem high_principal_deriv_cap_antitone (K : HighGaussianKernel) {x y : ℝ} (hx : 0 < x)
    (hxy : x ≤ y) : highPrincipalDerivCap K y ≤ highPrincipalDerivCap K x := by
  have ha : 0 < (K.pole : ℝ) := (by norm_num only : (0 : ℝ) < 1 / 2).trans (high_gaussian_pole_gt K)
  have hκ : 0 ≤ (K.normalization : ℝ) := (Rat.cast_pos.mpr (high_gaussian_normalization_pos K)).le
  have hM₀ : 0 ≤ highCompactMass K := Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
  have hM₁ : 0 ≤ highCompactSlope K :=
    Finset.sum_nonneg (fun _ _ ↦ mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))
  have hdiv (c : ℝ) (hc : 0 ≤ c) (i : ℕ) : c / y ^ i ≤ c / x ^ i :=
    div_le_div_of_nonneg_left hc (pow_pos hx _) (pow_le_pow_left₀ hx.le hxy _)
  have hedge :
    4 * |highPrincipalEdge K| / (y ^ 2 + 1 / 4) ≤ 4 * |highPrincipalEdge K| / (x ^ 2 + 1 / 4) :=
    div_le_div_of_nonneg_left (mul_nonneg (by norm_num only) (abs_nonneg _))
      (add_pos (sq_pos_of_pos hx) (by norm_num only))
      (add_le_add (pow_le_pow_left₀ hx.le hxy 2) le_rfl)
  unfold highPrincipalDerivCap
  dsimp only
  exact
    add_le_add
      (add_le_add
        (mul_le_mul_of_nonneg_left
          (add_le_add
            (add_le_add (hdiv _ (mul_nonneg (by norm_num only) (sq_nonneg _)) 4)
              (hdiv _ (mul_nonneg (by norm_num only) (sq_nonneg _)) 5))
            (hdiv _ (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num only) ha.le) hM₀) hM₁) 6))
          (mul_nonneg (by norm_num only) hκ))
        (hdiv _ (mul_nonneg (by norm_num only) (high_principal_head_cap_nonneg K)) 2))
      hedge

/-- H26 controls the error of replacing a zero height by a point in its positive bracket. -/
public theorem high_principal_multiplier_interval (K : HighGaussianKernel) {l r x y : ℝ}
    (hl : 0 < l) (hx : x ∈ Set.Icc l r) (hy : y ∈ Set.Icc l r) :
    ‖highPrincipalMultiplier K y - highPrincipalMultiplier K x‖ ≤
      highPrincipalDerivCap K l * |y - x| := by
  have hd (t : ℝ) (ht : t ∈ Set.Icc l r) :
    ‖deriv (highPrincipalMultiplier K) t‖ ≤ highPrincipalDerivCap K l :=
    (high_principal_multiplier_deriv_bound K (hl.trans_le ht.1)).trans
      (high_principal_deriv_cap_antitone K hl ht.1)
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_deriv_le
      (fun t _ ↦ (high_principal_multiplier_deriv K t).differentiableAt) hd (convex_Icc l r) hx hy

/-- Multiplying the H25 height multiplier by the zero multiplicity gives the actual coefficient. -/
public theorem high_principal_multiplier_eq (K : HighGaussianKernel) (hRH : RiemannHypothesis)
    {ρ : ℂ} (hz : riemannZeta ρ = 0 ∧ 0 ≤ ρ.re) :
    Complex.exp (-(5 * (K.pole : ℂ))) * highPrincipalFiniteCoeff K ρ =
      (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ) *
        highPrincipalMultiplier K ρ.im := by
  have h := high_principal_coeff_at_height K hRH hz
  have hxi := AnalyticNumberTheory.RiemannXi.xi_zero_of_zeta_zero_of_re_nonneg hz.1 hz.2
  have hr := AnalyticNumberTheory.RiemannXi.xi_zero_re_eq_half_of_riemannHypothesis hRH hxi
  have hρ : (1 / 2 : ℂ) + Complex.I * (ρ.im : ℂ) = ρ := by
    have he := Complex.re_add_im ρ
    rw [hr] at he
    simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at he
    rw [mul_comm Complex.I]
    exact he
  unfold highPrincipalMultiplier highPrincipalEdge
  rw [high_height_kernel_eq, hρ]
  simp only [Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_ofNat,
    Complex.ofReal_ratCast, neg_mul]
  dsimp only at h
  rw [← neg_mul] at h
  simpa only [add_comm (Complex.I * (ρ.im : ℂ)), mul_assoc, neg_mul, mul_div_assoc] using h

/-- A midpoint value and the H26 endpoint cap control the multiplier throughout a bracket. -/
public theorem high_principal_multiplier_midpoint (K : HighGaussianKernel) {l r t : ℝ} (hl : 0 < l)
    (ht : t ∈ Set.Icc l r) :
    ‖highPrincipalMultiplier K t‖ ≤
      ‖highPrincipalMultiplier K ((l + r) / 2)‖ + highPrincipalDerivCap K l * ((r - l) / 2) := by
  let m := (l + r) / 2
  have hm : m ∈ Set.Icc l r := by
    have h := ht.1.trans ht.2
    exact
      ⟨by
        dsimp only [m]; linarith only [h], by
        dsimp only [m]; linarith only [h]⟩
  have hr : |t - m| ≤ (r - l) / 2 := by
    exact
      abs_le.mpr
        ⟨by
          dsimp only [m]; linarith only [ht.1], by
          dsimp only [m]; linarith only [ht.2]⟩
  have hc := (norm_nonneg _).trans (high_principal_multiplier_deriv_bound K hl)
  have hv := (high_principal_multiplier_interval K hl hm ht).trans (mul_le_mul_of_nonneg_left hr hc)
  calc
    _ =
        ‖highPrincipalMultiplier K m +
            (highPrincipalMultiplier K t - highPrincipalMultiplier K m)‖ :=
      by rw [add_sub_cancel]
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add le_rfl hv)

end PseudoPrime.PrimeTestBounds.MillerRabin
