/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighMassPole
public import PseudoPrime.LLS.PaperStatements.MellinKernelZeros
import all PseudoPrime.LLS.PaperStatements.ShiftedPoleKernel

/-! # Absolute zero weights for the high Gaussian shifted-pole kernels -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The high Gaussian zero summand combines the shifted poles with their signed
numerator coefficients before taking the absolute value. -/
public noncomputable def HighGaussianKernel.zeroTerm (K : HighGaussianKernel) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (x : ℝ) (ρ : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (2 * K.degree + 1),
    (K.expandedCoeff j : ℂ) *
      (LLS.PaperStatements.shiftedPoleKernel (K.logPower j) K.pole 5
            (Nat.le_of_succ_le_succ ((by decide : 2 ≤ 4).trans (high_gaussian_order_ge_four K j)))
            (high_gaussian_pole_gt K)).oscillatingZeroTerm
        χ x ρ

/-- At positive cutoff the absolute value of the combined shifted-pole zero
summand is the rational mass times the nonnegative completed-L multiplicity. -/
public theorem high_gaussian_zero_term_norm (K : HighGaussianKernel) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hne : χ ≠ 1) {x : ℝ} (hx : 0 < x) (ρ : ℂ) :
    ‖K.zeroTerm χ x ρ‖ =
      (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
        (K.massExtension (Complex.I * (ρ.im : ℂ))).re := by
  have ha : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := fun z _ ↦
    (DirichletCharacter.differentiable_completedLFunction hne).analyticAt z
  have hd : (0 : ℝ) ≤ (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) := by
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg ha ρ
  unfold HighGaussianKernel.zeroTerm
  simp only [LLS.PaperStatements.MellinKernel.oscillatingZeroTerm,
    LLS.PaperStatements.MellinKernel.kernelZeroTerm]
  let d := (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℂ)
  let z := Complex.I * (ρ.im : ℂ)
  have he (j : ℕ) :
    (K.expandedCoeff j : ℂ) *
        (d *
          (LLS.PaperStatements.shiftedPoleKernel (K.logPower j) K.pole 5
                (Nat.le_of_succ_le_succ
                  ((by decide : 2 ≤ 4).trans (high_gaussian_order_ge_four K j)))
                (high_gaussian_pole_gt K)).function
            z *
          (x : ℂ) ^ z) =
      d *
        ((K.expandedCoeff j : ℂ) * Complex.exp (5 * z) / (z + (K.pole : ℂ)) ^ (K.logPower j + 1)) *
        (x : ℂ) ^ z := by
    change _ * (d * (Complex.exp ((↑(5 : ℝ) : ℂ) * z) / _) * (x : ℂ) ^ z) = _
    simp only [Complex.ofReal_ofNat, Complex.ofReal_ratCast, div_eq_mul_inv]
    ac_rfl
  simp only [he, ← Finset.mul_sum, ← Finset.sum_mul, norm_mul, d, z, Complex.norm_intCast,
    abs_of_nonneg hd, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.mul_re, Complex.I_re,
    Complex.ofReal_im, zero_mul, mul_zero, sub_zero, Real.rpow_zero, mul_one,
    high_gaussian_mass_extension_line, Complex.ofReal_re]

/-- Under GRH, the combined zero series for primitive nonprincipal data is absolutely summable. -/
public theorem high_gaussian_zero_summable (K : HighGaussianKernel) {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) {x : ℝ} (hx : 0 < x) : Summable (K.zeroTerm χ x) := by
  unfold HighGaussianKernel.zeroTerm
  generalize Finset.range (2 * K.degree + 1) = s
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]; exact summable_zero
  | @insert j s hjs ih =>
    simp only [Finset.sum_insert hjs]
    exact
      ((LLS.PaperStatements.shiftedPoleKernel (K.logPower j) K.pole 5
                  (Nat.le_of_succ_le_succ
                    ((by decide : 2 ≤ 4).trans (high_gaussian_order_ge_four K j)))
                  (high_gaussian_pole_gt K)).summable_oscillatingZeroTerm
              hq hGRH hp hne (inv_ne_one.mpr hne) hx |>.mul_left
            (K.expandedCoeff j : ℂ)).add
        ih

/-- Summing the exact pointwise mass bounds the combined oscillatory zero sum. -/
public theorem high_gaussian_zero_sum_le (K : HighGaussianKernel) {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) {x : ℝ} (hx : 0 < x) :
    ‖∑' ρ : ℂ, K.zeroTerm χ x ρ‖ ≤
      ∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          (K.massExtension (Complex.I * (ρ.im : ℂ))).re := by
  simp only [← high_gaussian_zero_term_norm K hne hx]
  exact norm_tsum_le_tsum_norm (high_gaussian_zero_summable K hq hGRH hp hne hx).norm

end PseudoPrime.PrimeTestBounds.MillerRabin
