/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TriangularSignedGammaBounds

/-! # Signed dual-scale triangular explicit formula

Reflect the completed left integral before taking norms. The inverse-scale arithmetic
sum is retained, and the left contour is replaced by the exact triangular profile.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For a nonprincipal character and positive scale, the completed right integral
is the negative arithmetic sum plus the Gamma integral. Split the ordinary and Gamma
logarithmic derivatives using their integrability. This also applies at inverse scales. -/
theorem triangular18_completed_rightIntegral_eq_scaled_arithmetic_add_gamma {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hne : χ ≠ 1) {x : ℝ} (hx : 0 < x) :
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          logDeriv χ.completedLFunction ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
            (K.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t) *
              (x : ℂ) ^ (((9 / 16 : ℝ) : ℂ) + Complex.I * t))) =
      -(∑' n : ℕ, K.summand χ x n) +
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv χ.gammaFactor ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
              (K.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t) *
                (x : ℂ) ^ (((9 / 16 : ℝ) : ℂ) + Complex.I * t))) := by
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  let w := fun t : ℝ ↦
    K.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t) * (x : ℂ) ^ (((9 / 16 : ℝ) : ℂ) + Complex.I * t)
  let A := fun t : ℝ ↦ -logDeriv χ.LFunction ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) * w t
  let G := fun t : ℝ ↦ logDeriv χ.gammaFactor ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) * w t
  have ha :=
    MellinKernel.integrable_arithmeticMellin_logDeriv K χ (c := 9 / 16) hx (by norm_num only)
      (by
        change (9 / 16 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
  have hg :=
    MellinKernel.integrable_gammaFactor_power_line K χ (c := 9 / 16) (x := x) (by norm_num only)
      (by
        change (9 / 16 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
      (by norm_num only) hx
  change MeasureTheory.Integrable A at ha
  simp only [mul_assoc] at hg
  change MeasureTheory.Integrable G at hg
  have he (t : ℝ) :
    logDeriv χ.completedLFunction ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) * w t =
      -A t + G t := by
    have hr : 1 ≤ ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2).re := by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero, Complex.div_ofNat_re,
        Complex.one_re]
      norm_num only
    have h := MellinKernel.arithmetic_logDeriv_eq_completed_add_gamma hne hr (w t)
    dsimp only [A, G]
    linear_combination h
  have hs :=
    MellinKernel.tsum_summand_eq_integral_logDeriv K χ (x := x) (c := 9 / 16) hx (by norm_num only)
      (by
        change (9 / 16 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
  change
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * _ =
      -(∑' n : ℕ, K.summand χ x n) + ((1 / (2 * Real.pi) : ℝ) : ℂ) * _
  rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ he),
    MeasureTheory.integral_add (f := fun t : ℝ ↦ -A t) (g := G) ha.neg hg,
    MeasureTheory.integral_neg, mul_add]
  rw [hs]
  exact congrArg (fun z : ℂ ↦ z + ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, G t)) (mul_neg _ _)

/-- For any complex function and positive scale, the reflected weighted integral
equals the right integral at inverse scale. Substitute the negative height, use the even
triangular kernel, and invert the real-base complex power. No integrability input is needed. -/
theorem triangular18_reflected_scaledIntegral_eq_inverse_scale_right (f : ℂ → ℂ) {x : ℝ}
    (hx : 0 < x) :
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    (∫ t : ℝ,
        f (((17 / 16 : ℝ) : ℂ) - Complex.I * t) *
          (K.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
            (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) =
      (∫ t : ℝ,
        f ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
          (K.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t) *
            ((x⁻¹ : ℝ) : ℂ) ^ (((9 / 16 : ℝ) : ℂ) + Complex.I * t))) := by
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  let F := fun t : ℝ ↦
    f ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
      (K.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t) *
        ((x⁻¹ : ℝ) : ℂ) ^ (((9 / 16 : ℝ) : ℂ) + Complex.I * t))
  have he (t : ℝ) :
    f (((17 / 16 : ℝ) : ℂ) - Complex.I * t) *
        (K.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
          (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) =
      F (-t) := by
    have hz : (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) = -(((9 / 16 : ℝ) : ℂ) + Complex.I * (-t)) := by
      simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat]
      ring
    have hw :
      (((17 / 16 : ℝ) : ℂ) - Complex.I * t) = (((9 / 16 : ℝ) : ℂ) + Complex.I * (-t)) + 1 / 2 := by
      simp only [Complex.ofReal_div, Complex.ofReal_ofNat]
      ring
    dsimp only [F]
    rw [hz, hw]
    change f _ * (Analysis.triangularMellinFunction 18 (-_) * _) = _
    rw [Analysis.triangularMellinFunction_neg (by norm_num only : (18 : ℝ) ≠ 0), Complex.cpow_neg,
      Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg hx.le]
    simp only [Complex.ofReal_neg]
    rfl
  change (∫ t : ℝ, _) = ∫ t : ℝ, F t
  rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ he)]
  exact MeasureTheory.integral_neg_eq_self F MeasureTheory.volume

/-- For primitive nonprincipal data with nonprincipal inverse and positive scale,
the completed left integral equals its conductor contribution minus the inverse-scale
arithmetic sum plus the inverse-character Gamma integral. Apply the functional equation,
split integrable terms, and reflect before taking norms. This preserves the dual sum. -/
theorem triangular18_left_completedIntegral_eq_dual_arithmetic_add_gamma {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ}
    (hx : 0 < x) :
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
            (K.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
              (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
            (∫ t : ℝ,
              Complex.log q *
                (K.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
                  (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) -
          (∑' n : ℕ, K.summand χ⁻¹ x⁻¹ n) +
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv χ⁻¹.gammaFactor ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
              (K.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t) *
                ((x⁻¹ : ℝ) : ℂ) ^ (((9 / 16 : ℝ) : ℂ) + Complex.I * t))) := by
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  let w := fun t : ℝ ↦
    K.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
      (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)
  let F := fun t : ℝ ↦
    -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) * w t
  let C := fun t : ℝ ↦ Complex.log q * w t
  let R := fun t : ℝ ↦ logDeriv χ⁻¹.completedLFunction (((17 / 16 : ℝ) : ℂ) - Complex.I * t) * w t
  have hF :=
    MellinKernel.integrable_completed_left_line K hp hne hinv (c := -9 / 16) (x := x)
      (by
        change (-1 / 2 - 1 / 8 : ℝ) < -9 / 16; norm_num only)
      (by norm_num only) (by norm_num only) hx
  have hC :=
    MellinKernel.integrable_logWeighted_power_line K (c := -9 / 16) (x := x) (F := fun _ : ℝ ↦
      Complex.log q) (A := ‖Complex.log q‖)
      (by
        change (-1 / 2 - 1 / 8 : ℝ) < -9 / 16; norm_num only)
      (by
        change (-9 / 16 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
      (by norm_num only) hx MeasureTheory.aestronglyMeasurable_const
      (fun t ↦ by
        have hlog : 0 ≤ Real.log (4 + |t|) := Real.log_nonneg (by linarith only [abs_nonneg t])
        nlinarith only [hlog, norm_nonneg (Complex.log (q : ℂ))])
  simp only [mul_assoc] at hC
  change MeasureTheory.Integrable F at hF
  change MeasureTheory.Integrable C at hC
  have he (t : ℝ) : F t = C t + R t := by
    dsimp only [F, C, R]
    rw [triangular18_completed_left_reflection hp hne hinv t, add_mul]
  have hR : MeasureTheory.Integrable R :=
    (hF.sub hC).congr
      (MeasureTheory.ae_of_all _ (fun t ↦ by rw [Pi.sub_apply, he, add_sub_cancel_left]))
  have hi : (∫ t : ℝ, F t) = (∫ t : ℝ, C t) + ∫ t : ℝ, R t := by
    rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ he),
      MeasureTheory.integral_add hC hR]
  have hreflect :=
    triangular18_reflected_scaledIntegral_eq_inverse_scale_right (logDeriv χ⁻¹.completedLFunction)
      hx
  have hright :=
    triangular18_completed_rightIntegral_eq_scaled_arithmetic_add_gamma hinv (inv_pos.mpr hx)
  change ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, F t) = _
  rw [hi, mul_add]
  dsimp only [R, w] at *
  rw [hreflect, hright]
  ring

/-- For positive scale, the normalized left-line triangular kernel integral
is its real triangular profile at that scale. Apply inverse Mellin inversion at inverse
scale and the evenness of the absolute logarithm. This evaluates the conductor term. -/
theorem triangular18_left_scaledKernelIntegral {x : ℝ} (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          Analysis.triangularMellinFunction 18 (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
            (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) =
      (triangularKernelProfile 18 x : ℂ) := by
  have h :=
    inverseMellin_triangular (a := 18) (c := -9 / 16) (u := x⁻¹) (by norm_num only)
      (by norm_num only [abs_neg]) (inv_pos.mpr hx)
  unfold inverseMellin at h
  simp only [Complex.ofReal_inv, Complex.cpow_neg, Complex.inv_cpow_ofReal_nonneg hx.le,
    inv_inv] at h
  rw [h]
  unfold triangularKernelProfile
  rw [Real.log_inv, abs_neg]

/-- For primitive nonprincipal GRH data of modulus at least two, nonprincipal
inverse and scale at least one, the scale and inverse-scale arithmetic sums plus the
oscillating zero sum equal the conductor times the triangular profile plus two Gamma
integrals. Insert the reflected left formula into the completed contour identity.
This removes the estimated left-contour remainder while retaining the dual arithmetic sum. -/
theorem triangular18_dual_scale_signed_formula {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    let G := fun (ψ : DirichletCharacter ℂ q) (y : ℝ) ↦
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          logDeriv ψ.gammaFactor ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
            (K.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t) *
              (y : ℂ) ^ (((9 / 16 : ℝ) : ℂ) + Complex.I * t)))
    (∑' n : ℕ, K.summand χ x n) + (∑' n : ℕ, K.summand χ⁻¹ x⁻¹ n) +
        (∑' ρ : ℂ, K.oscillatingZeroTerm χ x ρ) =
      Complex.log q * (triangularKernelProfile 18 x : ℂ) + G χ x + G χ⁻¹ x⁻¹ := by
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  have hx0 := zero_lt_one.trans_le hx
  have he :=
    MellinKernel.tsum_summand_eq_completed_residue_formula K hq hGRH hp hne hinv (a := -9 / 16)
      (b := 9 / 16) (x := x) (by norm_num only)
      (by
        change (-1 / 2 - 1 / 8 : ℝ) < -9 / 16; norm_num only)
      (by
        change (9 / 16 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
      (by norm_num only) (by norm_num only) hx (by norm_num only) (by norm_num only)
  dsimp only at he
  rw [triangular_weightedResidue_pole_eq_zero, zero_sub] at he
  rw [triangular18_left_completedIntegral_eq_dual_arithmetic_add_gamma hp hne hinv hx0] at he
  rw [MeasureTheory.integral_const_mul] at he
  have hk := triangular18_left_scaledKernelIntegral hx0
  have hc :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (Complex.log q *
          (∫ t : ℝ,
            K.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
              (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) =
      Complex.log q * (triangularKernelProfile 18 x : ℂ) := by
    calc
      _ =
          Complex.log q *
            (((1 / (2 * Real.pi) : ℝ) : ℂ) *
              (∫ t : ℝ,
                K.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
                  (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) :=
        by ring
      _ = _ := congrArg (fun z : ℂ ↦ Complex.log q * z) hk
  rw [hc] at he
  dsimp only
  linear_combination he

/-- For a finite family of primitive nonprincipal characters with nonprincipal inverses,
possibly of different conductors at least two, sum the real dual-scale formula under GRH.
The common triangular profile multiplies the sum of conductor logarithms; Gamma integrals
and both arithmetic scales retain their signs. This supplies a finite-family interface
for subgroup averages without introducing an estimated left-contour remainder. -/
theorem triangular18_dual_scale_signed_family_formula {ι : Type*} (s : Finset ι) (q : ι → ℕ)
    [∀ i, NeZero (q i)] (χ : ∀ i, DirichletCharacter ℂ (q i))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hq : ∀ i ∈ s, 2 ≤ q i)
    (hp : ∀ i ∈ s, (χ i).IsPrimitive) (hne : ∀ i ∈ s, χ i ≠ 1) (hinv : ∀ i ∈ s, (χ i)⁻¹ ≠ 1) {x : ℝ}
    (hx : 1 ≤ x) :
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    let G := fun (i : ι) (ψ : DirichletCharacter ℂ (q i)) (y : ℝ) ↦
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          logDeriv ψ.gammaFactor ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
            (K.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t) *
              (y : ℂ) ^ (((9 / 16 : ℝ) : ℂ) + Complex.I * t)))
    (∑ i ∈ s,
        ((∑' n : ℕ, K.summand (χ i) x n) + (∑' n : ℕ, K.summand (χ i)⁻¹ x⁻¹ n) +
            (∑' ρ : ℂ, K.oscillatingZeroTerm (χ i) x ρ)).re) =
      triangularKernelProfile 18 x * (∑ i ∈ s, Real.log (q i)) +
        ∑ i ∈ s, (G i (χ i) x + G i (χ i)⁻¹ x⁻¹).re := by
  dsimp only
  have he (i : ι) (hi : i ∈ s) :=
    congrArg Complex.re
      (triangular18_dual_scale_signed_formula (hq i hi) hGRH (hp i hi) (hne i hi) (hinv i hi) hx)
  simp only [Complex.add_re, ← Complex.natCast_log, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero] at he
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have h := he i hi
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  linear_combination h

end PseudoPrime.LLS.PaperStatements
