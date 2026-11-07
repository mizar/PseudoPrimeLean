/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.TriangularDualScaleFormula
public import PseudoPrime.LLS.PaperStatements.TriangularGammaPositiveScale
public import PseudoPrime.LLS.PaperStatements.TriangularScaleOneCredit

/-! # Parameterized triangular dual-scale formula -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For a positive triangular parameter and positive scale, the completed right
integral equals the negative arithmetic sum plus the Gamma integral. Split the
completed logarithmic derivative into its arithmetic and Gamma parts; this
parameterized identity supplies the width-24 dual-scale formula. -/
theorem triangular_right_arithmetic_gamma {a : ℝ} (ha : 0 < a) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hne : χ ≠ 1) {x : ℝ} (hx : 0 < x) :
    let K := triangularMellinKernel ha
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
  let K := triangularMellinKernel ha
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

/-- For every positive triangular parameter and positive scale, reflect the
integral to the inverse scale. Evenness of the kernel and the negative-variable
substitution preserve the exact inverse-scale arithmetic term. -/
theorem triangular_reflected_inverse {a : ℝ} (ha : 0 < a) (f : ℂ → ℂ) {x : ℝ} (hx : 0 < x) :
    let K := triangularMellinKernel ha
    (∫ t : ℝ,
        f (((17 / 16 : ℝ) : ℂ) - Complex.I * t) *
          (K.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
            (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) =
      (∫ t : ℝ,
        f ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
          (K.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t) *
            ((x⁻¹ : ℝ) : ℂ) ^ (((9 / 16 : ℝ) : ℂ) + Complex.I * t))) := by
  let K := triangularMellinKernel ha
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
    change f _ * (Analysis.triangularMellinFunction a (-_) * _) = _
    rw [Analysis.triangularMellinFunction_neg ha.ne', Complex.cpow_neg, Complex.ofReal_inv,
      Complex.inv_cpow_ofReal_nonneg hx.le]
    simp only [Complex.ofReal_neg]
    rfl
  change (∫ t : ℝ, _) = ∫ t : ℝ, F t
  rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ he)]
  exact MeasureTheory.integral_neg_eq_self F MeasureTheory.volume

/-- For a positive triangular parameter and primitive nonprincipal character,
reflect the completed left integral to inverse scale. The conductor term and
inverse-character arithmetic and Gamma terms remain exact and signed. -/
theorem triangular_left_dual_arithmetic {a : ℝ} (ha : 0 < a) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ}
    (hx : 0 < x) :
    let K := triangularMellinKernel ha
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
  let K := triangularMellinKernel ha
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
  have hreflect := triangular_reflected_inverse ha (logDeriv χ⁻¹.completedLFunction) hx
  have hright := triangular_right_arithmetic_gamma ha hinv (inv_pos.mpr hx)
  change ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, F t) = _
  rw [hi, mul_add]
  dsimp only [R, w] at *
  rw [hreflect, hright]
  ring

/-- For positive triangular parameter and positive scale, the normalized left
contour kernel integral is the triangular profile. Inverse Mellin inversion at
the reciprocal scale evaluates the conductor term exactly. -/
theorem triangular_left_scaled_integral {a : ℝ} (ha : 0 < a) {x : ℝ} (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          Analysis.triangularMellinFunction a (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
            (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) =
      (triangularKernelProfile a x : ℂ) := by
  have h :=
    inverseMellin_triangular (a := a) (c := -9 / 16) (u := x⁻¹) ha (by norm_num only [abs_neg])
      (inv_pos.mpr hx)
  unfold Analysis.inverseMellin at h
  simp only [Complex.ofReal_inv, Complex.cpow_neg, Complex.inv_cpow_ofReal_nonneg hx.le,
    inv_inv] at h
  rw [h]
  unfold triangularKernelProfile
  rw [Real.log_inv, abs_neg]

/-- For a positive triangular parameter, primitive nonprincipal GRH data and
scale at least one, the two arithmetic scales and oscillating zero sum satisfy
the exact signed formula. The reflected left integral gives the conductor and
inverse-scale terms without a contour remainder estimate. -/
theorem triangular_dual_signed_formula {a : ℝ} (ha : 0 < a) {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    let K := triangularMellinKernel ha
    let G := fun (ψ : DirichletCharacter ℂ q) (y : ℝ) ↦
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          logDeriv ψ.gammaFactor ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
            (K.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t) *
              (y : ℂ) ^ (((9 / 16 : ℝ) : ℂ) + Complex.I * t)))
    (∑' n : ℕ, K.summand χ x n) + (∑' n : ℕ, K.summand χ⁻¹ x⁻¹ n) +
        (∑' ρ : ℂ, K.oscillatingZeroTerm χ x ρ) =
      Complex.log q * (triangularKernelProfile a x : ℂ) + G χ x + G χ⁻¹ x⁻¹ := by
  let K := triangularMellinKernel ha
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
  rw [triangular_left_dual_arithmetic ha hp hne hinv hx0] at he
  rw [MeasureTheory.integral_const_mul] at he
  have hk := triangular_left_scaled_integral ha hx0
  have hc :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (Complex.log q *
          (∫ t : ℝ,
            K.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
              (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) =
      Complex.log q * (triangularKernelProfile a x : ℂ) := by
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

/-- For a finite family of primitive nonprincipal characters and a positive
triangular parameter, sum the real signed dual-scale formulas under GRH.
The shared profile multiplies the conductor-log sum while the two arithmetic
scales and Gamma terms retain their signs for subgroup averaging. -/
theorem triangular_dual_signed_family {a : ℝ} (ha : 0 < a) {ι : Type*} (s : Finset ι) (q : ι → ℕ)
    [∀ i, NeZero (q i)] (χ : ∀ i, DirichletCharacter ℂ (q i))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hq : ∀ i ∈ s, 2 ≤ q i)
    (hp : ∀ i ∈ s, (χ i).IsPrimitive) (hne : ∀ i ∈ s, χ i ≠ 1) (hinv : ∀ i ∈ s, (χ i)⁻¹ ≠ 1) {x : ℝ}
    (hx : 1 ≤ x) :
    let K := triangularMellinKernel ha
    let G := fun (i : ι) (ψ : DirichletCharacter ℂ (q i)) (y : ℝ) ↦
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          logDeriv ψ.gammaFactor ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
            (K.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t) *
              (y : ℂ) ^ (((9 / 16 : ℝ) : ℂ) + Complex.I * t)))
    (∑ i ∈ s,
        ((∑' n : ℕ, K.summand (χ i) x n) + (∑' n : ℕ, K.summand (χ i)⁻¹ x⁻¹ n) +
            (∑' ρ : ℂ, K.oscillatingZeroTerm (χ i) x ρ)).re) =
      triangularKernelProfile a x * (∑ i ∈ s, Real.log (q i)) +
        ∑ i ∈ s, (G i (χ i) x + G i (χ i)⁻¹ x⁻¹).re := by
  dsimp only
  have he (i : ι) (hi : i ∈ s) :=
    congrArg Complex.re
      (triangular_dual_signed_formula ha (hq i hi) hGRH (hp i hi) (hne i hi) (hinv i hi) hx)
  simp only [Complex.add_re, ← Complex.natCast_log, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero] at he
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have h := he i hi
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  linear_combination h

/-- For a positive triangular parameter and primitive nonprincipal GRH data,
move both Gamma terms of the signed dual-scale identity to the central line.
The positive-scale line shift works at both the scale and its reciprocal. -/
theorem triangular_dual_signed_central {a : ℝ} (ha : 0 < a) {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    let K := triangularMellinKernel ha
    let G := fun (ψ : DirichletCharacter ℂ q) (y : ℝ) ↦
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          logDeriv ψ.gammaFactor (Complex.I * t + 1 / 2) *
            (K.function (Complex.I * t) * (y : ℂ) ^ (Complex.I * t)))
    (∑' n : ℕ, K.summand χ x n) + (∑' n : ℕ, K.summand χ⁻¹ x⁻¹ n) +
        (∑' ρ : ℂ, K.oscillatingZeroTerm χ x ρ) =
      Complex.log q * (triangularKernelProfile a x : ℂ) + G χ x + G χ⁻¹ x⁻¹ := by
  let K := triangularMellinKernel ha
  have hx0 := zero_lt_one.trans_le hx
  have h := triangular_dual_signed_formula ha hq hGRH hp hne hinv hx
  dsimp only at h ⊢
  have hshift (ψ : DirichletCharacter ℂ q) {y : ℝ} (hy : 0 < y) :=
    MellinKernel.gammaIntegral_eq_central_of_pos K ψ (b := 9 / 16) (by norm_num only)
      (by
        change (9 / 16 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
      (by norm_num only) hy
  rw [hshift χ hx0, hshift χ⁻¹ (inv_pos.mpr hx0)] at h
  exact h

/-- For any admissible Mellin kernel, if all primes through the cutoff are
coprime to the modulus and lie in the subgroup, the finite level-one sum gives
twice its contribution to the primitive scale-one arithmetic average. This
retains the signed arithmetic credit independently of the chosen kernel. -/
theorem MellinKernel.scaleOne_pair_lower (K : MellinKernel) {q : ℕ} [NeZero q]
    (H : Subgroup (ZMod q)ˣ) {X : ℝ} (hX : 0 ≤ X) (hlarge : ∀ p : ℕ, p.Prime → p ∣ q → X < (p : ℝ))
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ X → NumberTheory.residueInSubgroup q H p) :
    letI := Classical.propDecidable
    (2 : ℝ) * (H.index : ℝ) *
          (∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (K.summand (1 : DirichletCharacter ℂ 1) 1 n).re) -
        2 * (∑' n : ℕ, K.summand (1 : DirichletCharacter ℂ 1) 1 n).re ≤
      ∑ χ ∈ Finset.univ.erase (1 : NumberTheory.subgroupAnnihilator H),
        ((∑' n : ℕ, K.summand χ.val.primitiveCharacter 1 n).re +
          (∑' n : ℕ, K.summand (χ.val.primitiveCharacter)⁻¹ 1 n).re) := by
  classical
  let _ := Classical.propDecidable
  let A := NumberTheory.subgroupAnnihilator H
  let F := fun χ : A ↦ (∑' n : ℕ, K.summand χ.val.primitiveCharacter 1 n).re
  have hd : ∀ p : ℕ, p.Prime → p ∣ q → ⌊X⌋₊ < p := by
    intro p hp hpq
    exact (Nat.floor_lt hX).mpr (hlarge p hp hpq)
  have heq := MellinKernel.principal_sum_level_one_of_no_divisor K (q := q) 1 hd
  have hI : Finset.Ioc 0 ⌊X⌋₊ = Finset.Icc 1 ⌊X⌋₊ := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc, Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero]
  have heq' :
    (∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (K.summand (1 : DirichletCharacter ℂ q) 1 n).re) =
      ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (K.summand (1 : DirichletCharacter ℂ 1) 1 n).re := by
    have h := congrArg Complex.re heq
    simpa only [hI, Complex.re_sum] using h
  have hc :=
    MellinKernel.principal_sum_le_primitive_of_noSmall K H (x := 1) (by norm_num only) hsmall
  rw [heq'] at hc
  have he := Finset.sum_erase_add (s := Finset.univ) F (Finset.mem_univ (1 : A))
  have hp : F (1 : A) = (∑' n : ℕ, K.summand (1 : DirichletCharacter ℂ 1) 1 n).re :=
    congrArg Complex.re (tsum_congr (MellinKernel.principal_primitive_summand_eq_level_one K 1))
  have hr (χ : A) : (∑' n : ℕ, K.summand (χ.val.primitiveCharacter)⁻¹ 1 n).re = F χ := by
    let : NeZero χ.val.conductor := ⟨χ.val.conductor_ne_zero⟩
    exact MellinKernel.tsum_summand_inv_re_eq K χ.val.primitiveCharacter (by norm_num only)
  have hs :=
    Finset.sum_congr (s₁ := Finset.univ.erase (1 : A)) rfl
      (fun χ _ ↦ congrArg (fun y : ℝ ↦ F χ + y) (hr χ))
  change (2 : ℝ) * _ * _ - 2 * _ ≤ _
  rw [hs, Finset.sum_add_distrib]
  rw [hp] at he
  change (H.index : ℝ) * _ ≤ ∑ χ : A, F χ at hc
  linarith only [hc, he]

/-- For a positive triangular parameter and primitive nonprincipal GRH data,
the exact signed dual-scale formula has two explicit convergent Gamma weight
series. Evaluate both central Gamma terms at the scale and its reciprocal. -/
theorem triangular_dual_weightSeries_GRH {a : ℝ} (ha : 0 < a) {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    ∃ β γ : ℝ,
      1 / 4 ≤ β ∧
        β ≤ 1 ∧
          1 / 4 ≤ γ ∧
            γ ≤ 1 ∧
              let K := triangularMellinKernel ha
              (∑' n : ℕ, K.summand χ x n) + (∑' n : ℕ, K.summand χ⁻¹ x⁻¹ n) +
                  (∑' ρ : ℂ, K.oscillatingZeroTerm χ x ρ) =
                Complex.log q * (triangularKernelProfile a x : ℂ) +
                  (((-Complex.log Real.pi + Complex.digamma (β : ℂ)) / 2) *
                      (triangularKernelProfile a x : ℂ) +
                    (1 / 2 : ℂ) * ∑' n : ℕ, triangularGammaReciprocalTerm a (β + n) x) +
                  (((-Complex.log Real.pi + Complex.digamma (γ : ℂ)) / 2) *
                      (triangularKernelProfile a x⁻¹ : ℂ) +
                    (1 / 2 : ℂ) * ∑' n : ℕ, triangularGammaReciprocalTerm a (γ + n) x⁻¹) := by
  obtain ⟨β, hβ, hβ1, hg⟩ := triangular_gamma_eq_weightSeries χ
  obtain ⟨γ, hγ, hγ1, hgi⟩ := triangular_gamma_eq_weightSeries χ⁻¹
  refine ⟨β, γ, hβ, hβ1, hγ, hγ1, ?_⟩
  have h := triangular_dual_signed_central ha hq hGRH hp hne hinv hx
  dsimp only at h ⊢
  simp only [triangularMellinKernel] at h
  rw [hg a x ha (zero_lt_one.trans_le hx),
    hgi a x⁻¹ ha (inv_pos.mpr (zero_lt_one.trans_le hx))] at h
  exact h

end PseudoPrime.LLS.PaperStatements
