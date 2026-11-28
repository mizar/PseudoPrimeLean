/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighMassPoleShift
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighMassPoleShift
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighMassProfileContour
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTwoShiftZeta
import PseudoPrime.LLS.PaperStatements.MellinKernelArithmeticMellin
import PseudoPrime.LLS.PaperStatements.MellinKernelVerticalIntegrability
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-! # Exact even-character and Xi mass comparison for the high Gaussian kernels -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Integrability of the balanced components transfers to the combined contour mass. -/
private theorem integrable_mass_weight (K : HighGaussianKernel) (b : ℝ) (g : ℝ → ℂ) (hb₁ : -1 ≤ b)
    (hb₂ : b ≤ 1)
    (h :
      ∀ j : ℕ,
        MeasureTheory.Integrable
          (fun t : ℝ ↦
            g t *
              (balancedPoleKernel K.pole (high_gaussian_pole_ge_two K) (K.degree + 1 - j)).function
                ((b : ℂ) + Complex.I * (t : ℂ)))) :
    MeasureTheory.Integrable (fun t : ℝ ↦ g t * K.massExtension ((b : ℂ) + Complex.I * t)) := by
  let r := fun t : ℝ ↦ (b : ℂ) + Complex.I * (t : ℂ)
  let B := fun j ↦ balancedPoleKernel K.pole (high_gaussian_pole_ge_two K) (K.degree + 1 - j)
  let c := fun j ↦ (K.normalization : ℂ) * ((normSqPolynomial K.pole K.polynomial).coeff j : ℂ)
  have ha := high_gaussian_pole_ge_two K
  have hre (t : ℝ) : (r t).re = b := by
    simp only [r, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  have hh (j : ℕ) : MeasureTheory.Integrable (fun t : ℝ ↦ c j * (g t * (B j).function (r t))) :=
    (h j).const_mul _
  apply (MeasureTheory.integrable_finsetSum (Finset.range (K.degree + 1)) (fun j _ ↦ hh j)).congr
  exact
    Filter.Eventually.of_forall fun t ↦
      mass_integrand K
        (by
          rw [hre]; linarith only [ha, hb₁])
        (by
          rw [hre]; linarith only [ha, hb₂])
        (g t)

/-- The reflected ordinary logarithmic derivative is integrable against the high mass. -/
private theorem integrable_mass_reflected (K : HighGaussianKernel) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    MeasureTheory.Integrable
      (fun t : ℝ ↦ -logDeriv χ.LFunction (-(l t) + 1 / 2) * K.massExtension (l t)) := by
  intro l
  let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
  have h :=
    integrable_mass_weight K (9 / 16) (fun t ↦ -logDeriv χ.LFunction (r t + 1 / 2))
      (by norm_num only) (by norm_num only) fun j ↦ by
      let B := balancedPoleKernel K.pole (high_gaussian_pole_ge_two K) (K.degree + 1 - j)
      have hb : (9 / 16 : ℝ) ≤ 1 / 2 + B.delta := by
        rw [show B.delta = 1 / 8 from balanced_pole_delta _ _ _]
        norm_num only
      simpa only [r, Complex.ofReal_one, Complex.one_cpow, mul_one] using
        B.integrable_arithmeticMellin_logDeriv χ (x := 1) zero_lt_one (by norm_num only) hb
  apply h.comp_neg.congr
  apply Filter.Eventually.of_forall
  intro t
  change -logDeriv χ.LFunction (r (-t) + 1 / 2) * K.massExtension (r (-t)) = _
  have hr : r (-t) = -(l t) := by
    dsimp only [r, l]
    simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat, mul_neg, neg_add_rev]
    ring
  rw [hr, high_gaussian_mass_even]

/-- The left contour difference is the conductor term, the reflected Euler
difference, and the two left simple-pole integrals. -/
public theorem high_gaussian_mass_left_split (K : HighGaussianKernel) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hi : χ⁻¹ = χ) (he : χ.Even) :
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let d := ((1 / (2 * Real.pi) : ℝ) : ℂ)
    d *
        ((∫ t : ℝ, -logDeriv χ.completedLFunction (l t + 1 / 2) * K.massExtension (l t)) -
          ∫ t : ℝ,
            -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (l t + 1 / 2) *
              K.massExtension (l t)) =
      Complex.log (q : ℂ) * ((3 / 16 : ℝ) : ℂ) +
        ((∑' n : ℕ,
            ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
              (1 : DirichletCharacter ℂ 1) n *
              (K.massProfile n : ℂ)) -
          (∑' n : ℕ,
            ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * χ n *
              (K.massProfile n : ℂ))) +
        highMassPoleIntegral K (-9 / 16) (1 / 2) +
        highMassPoleIntegral K (-9 / 16) (-1 / 2) := by
  intro l d
  let F := fun t ↦ -logDeriv χ.completedLFunction (l t + 1 / 2)
  let Z := fun t ↦ -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (l t + 1 / 2)
  let C := fun t ↦ Complex.log (q : ℂ) * K.massExtension (l t)
  let A {m : ℕ} [NeZero m] (ψ : DirichletCharacter ℂ m) (t : ℝ) : ℂ :=
    -logDeriv ψ.LFunction (-(l t) + 1 / 2) * K.massExtension (l t)
  let P := fun (p : ℝ) t ↦ 1 / (l t - (p : ℂ)) * K.massExtension (l t)
  let B := fun j ↦ balancedPoleKernel K.pole (high_gaussian_pole_ge_two K) (K.degree + 1 - j)
  have hd (j : ℕ) : (B j).delta = 1 / 8 := balanced_pole_delta _ _ _
  have hb (j : ℕ) : -1 / 2 - (B j).delta < (-9 / 16 : ℝ) := by
    rw [hd]; norm_num only
  have hF :=
    integrable_mass_weight K (-9 / 16) F (by norm_num only) (by norm_num only) fun j ↦ by
      simpa only [F, l, Complex.ofReal_one, Complex.one_cpow, mul_one] using
        (B j).integrable_completed_left_line hp hne (inv_ne_one.mpr hne) (x := 1) (hb j)
          (by norm_num only) (by norm_num only) zero_lt_one
  have hZ :=
    integrable_mass_weight K (-9 / 16) Z (by norm_num only) (by norm_num only) fun j ↦ by
      simpa only [Z, l, Complex.ofReal_one, Complex.one_cpow, mul_one] using
        (B j).integrable_xi_left_line (x := 1) (hb j) (by norm_num only) (by norm_num only)
          zero_lt_one
  have ha := high_gaussian_pole_ge_two K
  have hC : MeasureTheory.Integrable C := by
    have h :=
      high_gaussian_mass_vertical K (c := -9 / 16) (by linarith only [ha]) (by linarith only [ha])
    unfold Complex.VerticalIntegrable at h
    simpa only [C, l, mul_comm Complex.I] using h.const_mul (Complex.log q)
  have hA : MeasureTheory.Integrable (fun t ↦ A (1 : DirichletCharacter ℂ 1) t - A χ t) :=
    (integrable_mass_reflected K (1 : DirichletCharacter ℂ 1)).sub (integrable_mass_reflected K χ)
  have hP (p : ℝ) (hn : (-9 / 16 : ℝ) ≠ p) : MeasureTheory.Integrable (P p) := by
    apply
      integrable_mass_weight K (-9 / 16) (fun t ↦ 1 / (l t - (p : ℂ))) (by norm_num only)
        (by norm_num only)
    intro j
    simpa only [l, Complex.ofReal_one, Complex.one_cpow, mul_one] using
      (B j).integrable_pole_power_line (x := 1) (hb j)
        (by
          rw [hd]; norm_num only)
        (by norm_num only) hn zero_lt_one
  have hPp := hP (1 / 2) (by norm_num only)
  have hPm := hP (-1 / 2) (by norm_num only)
  have hpoint (t : ℝ) :
    F t * K.massExtension (l t) - Z t * K.massExtension (l t) =
      C t + (A (1 : DirichletCharacter ℂ 1) t - A χ t) + P (1 / 2) t + P (-1 / 2) t := by
    have h := twoShift_left_log_difference hp hne hi he t
    have hw : ((17 / 16 : ℝ) : ℂ) - Complex.I * t = -(l t) + 1 / 2 := by
      dsimp only [l]
      simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat]
      ring
    dsimp only at h
    rw [hw] at h
    have H :=
      twoShift_left_pole_split (l t) (K.massExtension (l t)) (Complex.log q)
        (logDeriv χ.LFunction (-(l t) + 1 / 2)) (logDeriv riemannZeta (-(l t) + 1 / 2))
    dsimp only at H
    simpa only [F, Z, C, A, P, l, ← sub_mul, sub_neg_eq_add, DirichletCharacter.LFunction_modOne_eq,
      h] using H
  change d * ((∫ t : ℝ, F t * K.massExtension (l t)) - ∫ t : ℝ, Z t * K.massExtension (l t)) = _
  have hAdd := MeasureTheory.integral_add ((hC.add hA).add hPp) hPm
  have hAdd' := MeasureTheory.integral_add (hC.add hA) hPp
  have hSub :=
    MeasureTheory.integral_sub
      (show MeasureTheory.Integrable (A (1 : DirichletCharacter ℂ 1)) from
        integrable_mass_reflected K (1 : DirichletCharacter ℂ 1))
      (show MeasureTheory.Integrable (A χ) from integrable_mass_reflected K χ)
  simp only [Pi.add_apply] at hAdd hAdd'
  rw [← MeasureTheory.integral_sub hF hZ,
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint), hAdd, hAdd',
    MeasureTheory.integral_add hC hA, hSub]
  simp only [mul_add, mul_sub]
  rw [show d * (∫ t : ℝ, C t) = _ from high_gaussian_mass_conductor K q,
    show d * (∫ t : ℝ, A (1 : DirichletCharacter ℂ 1) t) = _ from
      high_gaussian_reflected_euler K (1 : DirichletCharacter ℂ 1),
    show d * (∫ t : ℝ, A χ t) = _ from high_gaussian_reflected_euler K χ]
  rfl

/-- Subtracting the Xi mass leaves the conductor term, the two pole residues,
and twice the difference of the signed level-one and character Euler sums. -/
public theorem high_gaussian_mass_even_difference (K : HighGaussianKernel) {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hRH : RiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hi : χ⁻¹ = χ) (he : χ.Even) {x : ℝ} (hx : 0 < x) :
    ((∑' ρ : ℂ, ‖K.zeroTerm χ x ρ‖ : ℝ) : ℂ) - K.xiMass =
      Complex.log (q : ℂ) * ((3 / 16 : ℝ) : ℂ) - 2 * (K.massPole : ℂ) +
        2 *
          ((∑' n : ℕ,
              ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
                (1 : DirichletCharacter ℂ 1) n *
                (K.massProfile n : ℂ)) -
            (∑' n : ℕ,
              ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * χ n *
                (K.massProfile n : ℂ))) := by
  have h := high_gaussian_mass_gamma_cancel K hq hg hRH hp hne he hx
  have hl := high_gaussian_mass_left_split K hp hne hi he
  have hP := high_gaussian_mass_two_poles K
  dsimp only at h hl
  simp only [highMassPoleIntegral, mul_sub] at h hl hP
  linear_combination h + hl - hP

/-- The signed unit-scale Mangoldt series converges absolutely for every character. -/
public theorem high_gaussian_mass_series_summable (K : HighGaussianKernel) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    Summable
      (fun n : ℕ ↦
        ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * χ n *
          (K.massProfile n : ℂ)) := by
  let B := fun j ↦ balancedPoleKernel K.pole (high_gaussian_pole_ge_two K) (K.degree + 1 - j)
  let c := fun j ↦ (K.normalization : ℂ) * ((normSqPolynomial K.pole K.polynomial).coeff j : ℂ)
  have hs (s : Finset ℕ) : Summable (fun n : ℕ ↦ ∑ j ∈ s, c j * (B j).summand χ 1 n) := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact summable_zero
    | @insert j s hj ih =>
      simp only [Finset.sum_insert hj]
      exact (((B j).summable_summand χ zero_lt_one).mul_left (c j)).add ih
  exact (hs (Finset.range (K.degree + 1))).congr (mass_arithmetic K χ)

/-- Taking real parts converts the signed Mangoldt sum to the real character trace weight. -/
public theorem high_gaussian_mass_series_re (K : HighGaussianKernel) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    let W := fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n / Real.sqrt n * K.massProfile n
    HasSum (fun n : ℕ ↦ (χ n).re * W n)
      ((∑' n : ℕ,
          ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * χ n *
            (K.massProfile n : ℂ)).re) := by
  intro W
  apply (Complex.hasSum_re (high_gaussian_mass_series_summable K χ).hasSum).congr_fun
  intro n
  simp only [W, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero]
  ac_rfl

/-- The real zero-mass difference is the conductor and pole contribution plus
twice the signed Euler deficit series. -/
public theorem high_gaussian_mass_even_real (K : HighGaussianKernel) {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hRH : RiemannHypothesis) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hi : χ⁻¹ = χ) (he : χ.Even)
    {x : ℝ} (hx : 0 < x) :
    let W := fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n / Real.sqrt n * K.massProfile n
    (∑' ρ : ℂ, ‖K.zeroTerm χ x ρ‖) - K.xiMass.re =
      3 / 16 * Real.log q - 2 * (K.massPole : ℝ) + 2 * ∑' n : ℕ, (1 - (χ n).re) * W n := by
  intro W
  have ha := high_gaussian_mass_series_re K (1 : DirichletCharacter ℂ 1)
  have hb := high_gaussian_mass_series_re K χ
  dsimp only at ha hb
  simp only [MulChar.one_apply (isUnit_of_subsingleton (_ : ZMod 1)), Complex.one_re, one_mul] at ha
  have hh : HasSum (fun n : ℕ ↦ (1 - (χ n).re) * W n) _ :=
    (ha.sub hb).congr_fun (fun n ↦ by rw [sub_mul, one_mul])
  have hr := congrArg Complex.re (high_gaussian_mass_even_difference K hq hg hRH hp hne hi he hx)
  have hc : Complex.log (q : ℂ) = (Real.log (q : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (Nat.cast_nonneg q), Complex.ofReal_natCast]
  rw [hc] at hr
  have htwo (z : ℂ) : (2 * z).re = 2 * z.re := by
    have h : ((2 : ℝ) : ℂ) = 2 := Complex.ofReal_ofNat 2
    rw [← h, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  simp only [Complex.sub_re, Complex.add_re, ← Complex.ofReal_mul, htwo, ← Complex.ofReal_ratCast,
    Complex.ofReal_re, MulChar.one_apply (isUnit_of_subsingleton (_ : ZMod 1))] at hr
  rw [hh.tsum_eq]
  linarith only [hr]

end PseudoPrime.PrimeTestBounds.MillerRabin
