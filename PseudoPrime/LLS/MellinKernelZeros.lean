/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.MellinKernelBounds
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveFunctionalEquation
public import PseudoPrime.LLS.RiemannExplicitFormula

/-!
# General Mellin-kernel zero sums for the LLS paper

Under GRH, quadratic kernel decay gives absolute convergence of the multiplicity-weighted
zero sum and a Hadamard zero-mass bound. The oscillatory sum has a bounded theta representation.
Lemma 6.1's sharp conductor coefficient and contour error estimates remain separate.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements.MellinKernel

/-- The kernel hypotheses give a positive uniform quadratic decay constant on the imaginary
axis. Its distance from the possible pole is at least one half. This majorizes zero sums. -/
theorem exists_vertical_decay_bound (K : MellinKernel) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, ‖K.function (Complex.I * t)‖ ≤ C / (1 + t ^ 2) := by
  obtain ⟨C, hC, hb⟩ := K.decay (1 / 2) (by norm_num only)
  refine ⟨C, hC, ?_⟩
  intro t
  have hr : Complex.I * (t : ℂ) ∈ K.region := by
    apply K.strip_subset
    simp only [Set.mem_ofPred_eq, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
    constructor
    · linarith only [K.delta_pos]
    · linarith only [K.delta_pos]
  have hn : (1 / 2 : ℝ) ≤ ‖Complex.I * (t : ℂ) + 1 / 2‖ := by
    have hh := Complex.abs_re_le_norm (Complex.I * (t : ℂ) + 1 / 2)
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) from (Complex.ofReal_div 1 2).symm] at hh ⊢
    simpa only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, zero_add,
      abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 1 / 2)] using hh
  have h := hb (Complex.I * (t : ℂ)) hr hn
  simpa only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul, sq_abs] using
    h

/-- On the critical line, the vertical decay bound is at most `C / normSq ρ`.
Compare the positive denominators using `Re ρ = 1/2`; this matches the zero-mass series. -/
theorem norm_kernel_le_inv_normSq (K : MellinKernel) {C : ℝ} (hC : 0 < C)
    (hb : ∀ t : ℝ, ‖K.function (Complex.I * t)‖ ≤ C / (1 + t ^ 2)) {ρ : ℂ} (hre : ρ.re = 1 / 2) :
    ‖K.function (Complex.I * ρ.im)‖ ≤ C / Complex.normSq ρ := by
  have hn : 0 < Complex.normSq ρ := by
    rw [Complex.normSq_apply, hre]
    nlinarith only [sq_nonneg ρ.im]
  have hd : Complex.normSq ρ ≤ 1 + ρ.im ^ 2 := by
    rw [Complex.normSq_apply, hre]
    nlinarith only [sq_nonneg ρ.im]
  exact (hb ρ.im).trans (div_le_div_of_nonneg_left hC.le hn hd)

/-- The completed L-function's meromorphic divisor at ρ, cast to a complex number,
multiplied by the kernel value at `i Im ρ`. This is defined for every character and point.
For nonprincipal characters the completion is entire, so the divisor is the nonnegative
zero multiplicity and vanishes away from zeros. In that setting this is the unmodulated
zero term used in the Mellin formula. -/
noncomputable def kernelZeroTerm (K : MellinKernel) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (ρ : ℂ) : ℂ :=
  (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℂ) *
    K.function (Complex.I * ρ.im)

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- Under GRH, for a primitive character with χ ≠ 1 and χ⁻¹ ≠ 1, assume C > 0
and the bound `norm (K.function (i t)) ≤ C / (1 + t²)` for all real t.
The norm of each divisor-weighted kernel value is at most `C Dρ / normSq ρ`.
A nonzero divisor gives a critical-line zero; analyticity makes Dρ nonnegative.
This pointwise comparison supplies the majorant for the kernel zero series. -/
theorem norm_kernelZeroTerm_le (K : MellinKernel) {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {C : ℝ} (hC : 0 < C)
    (hb : ∀ t : ℝ, ‖K.function (Complex.I * t)‖ ≤ C / (1 + t ^ 2)) (ρ : ℂ) :
    ‖K.kernelZeroTerm χ ρ‖ ≤
      C *
        ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℝ) /
          Complex.normSq ρ) := by
  let D := MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ
  by_cases hD : D = 0
  · simp only [kernelZeroTerm,
      ←
        show D = MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ from
          rfl,
      hD, Int.cast_zero, zero_mul, norm_zero, zero_div, mul_zero, le_refl]
  · have hz := dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero hne hD
    have hr := completedLFunction_zero_re_eq_half hGRH hp hne hinv hz
    have hnD : (0 : ℝ) ≤ D := by
      have ha : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) Set.univ := fun z _ ↦
        (DirichletCharacter.differentiable_completedLFunction hne).analyticAt z
      exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg ha ρ
    have hk := norm_kernel_le_inv_normSq K hC hb hr
    change ‖(D : ℂ) * K.function (Complex.I * ρ.im)‖ ≤ C * ((D : ℝ) / Complex.normSq ρ)
    rw [norm_mul, Complex.norm_intCast, abs_of_nonneg hnD]
    calc
      _ ≤ (D : ℝ) * (C / Complex.normSq ρ) := mul_le_mul_of_nonneg_left hk hnD
      _ = _ := by ring

/-- For q ≥ 2 and a primitive character with χ ≠ 1 and χ⁻¹ ≠ 1, GRH implies
absolute summability of the divisor-weighted kernel values over the complex plane.
Extract a positive imaginary-axis decay constant from the kernel hypotheses and compare
with the summable inverse-norm-square divisor family. This validates the zero tsum
used in the general Mellin-kernel formula. -/
theorem summable_kernelZeroTerm (K : MellinKernel) {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) : Summable (K.kernelZeroTerm χ) := by
  obtain ⟨C, hC, hb⟩ := exists_vertical_decay_bound K
  have hs := AnalyticNumberTheory.DirichletLFunction.summable_divisor_div_normSq hq hGRH hp hne hinv
  exact (hs.mul_left C).of_norm_bounded (norm_kernelZeroTerm_le K hGRH hp hne hinv hC hb)

/-- Under GRH, let q ≥ 2 and let χ be primitive with χ ≠ 1 and χ⁻¹ ≠ 1.
A positive constant C bounding the imaginary-axis kernel by `C / (1 + t²)` bounds
the total sum of term norms by C times the inverse-norm-square divisor sum.
Sum the pointwise inequality using the two absolute convergence results.
This retains the chosen decay constant in the quantitative zero estimate. -/
theorem tsum_norm_kernelZeroTerm_le (K : MellinKernel) {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {C : ℝ} (hC : 0 < C)
    (hb : ∀ t : ℝ, ‖K.function (Complex.I * t)‖ ≤ C / (1 + t ^ 2)) :
    ∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖ ≤
      C *
        ∑' ρ : ℂ,
          (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℝ) /
            Complex.normSq ρ := by
  have hs := AnalyticNumberTheory.DirichletLFunction.summable_divisor_div_normSq hq hGRH hp hne hinv
  have ht :=
    Summable.tsum_le_tsum (norm_kernelZeroTerm_le K hGRH hp hne hinv hC hb)
      (summable_kernelZeroTerm K hq hGRH hp hne hinv).norm (hs.mul_left C)
  simpa only [tsum_mul_left] using ht

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- Under GRH, for q ≥ 2 and a primitive χ with χ ≠ 1 and χ⁻¹ ≠ 1, a positive
imaginary-axis decay constant C gives absolute kernel zero mass at most
`2 C abs (primitiveBRe χ)`. Apply the divisor-mass comparison and rewrite the
inverse-norm-square sum by the Hadamard identity. This gives the zero estimate
in terms of the character's Hadamard constant. -/
theorem tsum_norm_kernelZeroTerm_le_BRe (K : MellinKernel) {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {C : ℝ} (hC : 0 < C)
    (hb : ∀ t : ℝ, ‖K.function (Complex.I * t)‖ ≤ C / (1 + t ^ 2)) :
    ∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖ ≤ C * (2 * |primitiveBRe χ|) := by
  have h := tsum_norm_kernelZeroTerm_le K hq hGRH hp hne hinv hC hb
  rw [tsum_divisor_inv_normSq_eq_two_mul_abs_BRe hq hGRH hp hne hinv] at h
  exact h

/-- The divisor-weighted kernel value at `i Im ρ`, multiplied by the phase `x^(i Im ρ)`.
It is defined for every real x, character of nonzero modulus, and complex point.
For x > 0 the phase has norm one; for nonprincipal characters the divisor weights
are zero multiplicities. This is the oscillatory zero term in the Mellin formula. -/
noncomputable def oscillatingZeroTerm (K : MellinKernel) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (x : ℝ) (ρ : ℂ) : ℂ :=
  K.kernelZeroTerm χ ρ * (x : ℂ) ^ (Complex.I * ρ.im)

/-- At positive `x`, the oscillatory and unmodulated zero terms have equal norms.
The real part of the phase exponent is zero, so the complex power has unit norm.
This transfers absolute convergence and mass bounds to the contour zero sum. -/
theorem norm_oscillatingZeroTerm (K : MellinKernel) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 0 < x) (ρ : ℂ) : ‖K.oscillatingZeroTerm χ x ρ‖ = ‖K.kernelZeroTerm χ ρ‖ := by
  rw [oscillatingZeroTerm, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero, Real.rpow_zero, mul_one]

/-- For q ≥ 2, a primitive χ with χ ≠ 1 and χ⁻¹ ≠ 1, and x > 0, GRH implies
absolute summability of the oscillatory kernel zero series. The phase has norm one,
so the unmodulated kernel zero majorant also bounds these terms.
This justifies taking the real part of the contour zero tsum. -/
theorem summable_oscillatingZeroTerm (K : MellinKernel) {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) :
    Summable (K.oscillatingZeroTerm χ x) := by
  exact
    (summable_kernelZeroTerm K hq hGRH hp hne hinv).norm.of_norm_bounded
      (fun ρ ↦ (norm_oscillatingZeroTerm K χ hx ρ).le)

/-- Under GRH, for q ≥ 2, a primitive χ with χ ≠ 1 and χ⁻¹ ≠ 1, and x > 0,
the real part of the oscillatory zero sum is θ times the unmodulated absolute
kernel zero mass, with abs θ ≤ 1. Absolute convergence and the
triangle inequality bound its real part; the bounded-coefficient construction
also covers zero mass. This supplies the zero-term coefficient in the Mellin formula. -/
theorem exists_theta_zero_sum (K : MellinKernel) {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) :
    ∃ θ : ℝ,
      |θ| ≤ 1 ∧
        (∑' ρ : ℂ, K.oscillatingZeroTerm χ x ρ).re = θ * ∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖ := by
  apply LLS.exists_theta_mul_of_abs_le
  calc
    _ ≤ ‖∑' ρ : ℂ, K.oscillatingZeroTerm χ x ρ‖ := Complex.abs_re_le_norm _
    _ ≤ ∑' ρ : ℂ, ‖K.oscillatingZeroTerm χ x ρ‖ :=
      norm_tsum_le_tsum_norm (summable_oscillatingZeroTerm K hq hGRH hp hne hinv hx).norm
    _ = _ := tsum_congr (norm_oscillatingZeroTerm K χ hx)

end PseudoPrime.LLS.PaperStatements.MellinKernel
