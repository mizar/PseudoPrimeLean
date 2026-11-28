/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTriple644
public import PseudoPrime.LLS.PaperStatements.MellinKernelZeros
public import PseudoPrime.LLS.PaperStatements.MellinKernelExplicitFormula
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTriple644
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterZeroThreeFrequency

/-! # Three-frequency square completion for section 122 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For a nonprincipal character, the zero-term norm is its nonnegative multiplicity
times the kernel norm. -/
private theorem kernel_zero_norm {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hne : χ ≠ 1)
    (ρ : ℂ) :
    ‖quarterKernel644.kernelZeroTerm χ ρ‖ =
      (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
        ‖quarterKernel644.function (Complex.I * ρ.im)‖ := by
  have ha : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := fun z _ ↦
    (DirichletCharacter.differentiable_completedLFunction hne).analyticAt z
  have hd : (0 : ℝ) ≤ (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) := by
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg ha ρ
  unfold LLS.PaperStatements.MellinKernel.kernelZeroTerm
  rw [norm_mul, Complex.norm_intCast, abs_of_nonneg hd]

/-- Multiplication of the scale by exp(-s) rotates each zero term by
minus s times its ordinate, including terms of zero multiplicity. -/
private theorem zero_term_shift {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x)
    (s : ℝ) (ρ : ℂ) :
    quarterKernel644.oscillatingZeroTerm χ (x * Real.exp (-s)) ρ =
      quarterKernel644.oscillatingZeroTerm χ x ρ * Complex.exp ((-(s * ρ.im) : ℝ) * Complex.I) := by
  unfold LLS.PaperStatements.MellinKernel.oscillatingZeroTerm
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (mul_pos hx (Real.exp_pos _)).ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'), ←
    Complex.ofReal_log (mul_pos hx (Real.exp_pos _)).le, ← Complex.ofReal_log hx.le,
    Real.log_mul hx.ne' (Real.exp_pos _).ne', Real.log_exp, mul_assoc, ← Complex.exp_add]
  push_cast
  ring_nf

/-- The shifted phase cosine sum is exactly the real oscillating zero sum
at the rescaled cutoff. Absolute convergence at the positive new cutoff
justifies taking the real part term by term. -/
private theorem shifted_phase_eq {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hn : χ ≠ 1)
    (hi : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) (s : ℝ) :
    let Z := quarterKernel644.oscillatingZeroTerm χ x
    (∑' ρ : ℂ, ‖Z ρ‖ * Real.cos ((Z ρ).arg - s * ρ.im)) =
      (∑' ρ : ℂ, quarterKernel644.oscillatingZeroTerm χ (x * Real.exp (-s)) ρ).re := by
  intro Z
  rw [Complex.re_tsum
      (LLS.PaperStatements.MellinKernel.summable_oscillatingZeroTerm quarterKernel644 hq hG hp hn hi
        (mul_pos hx (Real.exp_pos _)))]
  apply tsum_congr
  intro ρ
  rw [zero_term_shift χ hx, Complex.mul_re, Complex.exp_re, Complex.exp_im, Real.cos_sub]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, mul_one, add_zero, Real.exp_zero, one_mul, Real.cos_neg,
    Real.sin_neg]
  change ‖Z ρ‖ * _ = (Z ρ).re * _ - (Z ρ).im * _
  rw [mul_add, ← mul_assoc, Complex.norm_mul_cos_arg, ← mul_assoc, Complex.norm_mul_sin_arg]
  ring

/-- Under GRH the three-frequency phase inequality applies to the oscillating
zero series of a primitive nonprincipal character. -/
private theorem zero_three_frequency {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hn : χ ≠ 1)
    (hi : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) (a b c p v s : ℝ) :
    let Z := quarterKernel644.oscillatingZeroTerm χ x
    let W := fun t : ℝ ↦ ∑' ρ : ℂ, ‖Z ρ‖ * Real.cos (t * ρ.im)
    let T := fun t : ℝ ↦ (∑' ρ : ℂ, quarterKernel644.oscillatingZeroTerm χ (x * Real.exp (-t)) ρ).re
    p * (W a + T a) + v * (W b + T b) + s * (W c + T c) -
        ((p ^ 2 + v ^ 2 + s ^ 2) / 2) * quarterMass644 χ -
        p * v * W (a - b) -
        p * s * W (a - c) -
        v * s * W (b - c) ≤
      quarterMass644 χ + (∑' ρ : ℂ, Z ρ).re := by
  intro Z W T
  have hs :=
    LLS.PaperStatements.MellinKernel.summable_oscillatingZeroTerm quarterKernel644 hq hG hp hn hi hx
  have hm : (∑' ρ : ℂ, ‖Z ρ‖) = quarterMass644 χ := by
    apply tsum_congr
    intro ρ
    exact
      (LLS.PaperStatements.MellinKernel.norm_oscillatingZeroTerm quarterKernel644 χ hx ρ).trans
        (kernel_zero_norm hn ρ)
  have hr : (∑' ρ : ℂ, ‖Z ρ‖ * Real.cos (Z ρ).arg) = (∑' ρ : ℂ, Z ρ).re := by
    rw [Complex.re_tsum hs]
    exact tsum_congr (fun ρ ↦ Complex.norm_mul_cos_arg (Z ρ))
  have h :=
    three_frequency_weighted_tsum (fun ρ ↦ ‖Z ρ‖) (fun ρ ↦ (Z ρ).arg) Complex.im
      (fun ρ ↦ norm_nonneg (Z ρ)) hs.norm a b c p v s
  dsimp only at h
  rw [hm, hr, shifted_phase_eq hq hG hp hn hi hx a, shifted_phase_eq hq hG hp hn hi hx b,
    shifted_phase_eq hq hG hp hn hi hx c] at h
  exact h

/-- Under GRH the section 122 oscillating zero sums satisfy the
three-frequency lower bound for a primitive nonprincipal character.
All three mixed cosine terms appear with their signed coefficients. -/
theorem quarter_three_frequency_644 {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hn : χ ≠ 1)
    {X : ℝ} (hX : 0 < X) :
    let Z := quarterKernel644.oscillatingZeroTerm χ X
    let W := fun t : ℝ ↦ ∑' ρ : ℂ, ‖Z ρ‖ * Real.cos (t * ρ.im)
    let T := fun t : ℝ ↦ (∑' ρ : ℂ, quarterKernel644.oscillatingZeroTerm χ (X * Real.exp (-t)) ρ).re
    1.54 * (W (2687 / 1000) + T (2687 / 1000)) - 1.508 * (W (2707 / 1000) + T (2707 / 1000)) -
            0.0917 * (W (3787 / 1000) + T (3787 / 1000)) -
            ((1.54 ^ 2 + 1.508 ^ 2 + 0.0917 ^ 2) / 2) * quarterMass644 χ +
          1.54 * 1.508 * W (1 / 50) +
          1.54 * 0.0917 * W (11 / 10) -
        1.508 * 0.0917 * W (27 / 25) ≤
      quarterMass644 χ + (∑' ρ, Z ρ).re := by
  intro Z W T
  have h :=
    zero_three_frequency hq hG hp hn (inv_ne_one.mpr hn) hX (3787 / 1000) (2707 / 1000)
      (2687 / 1000) (-0.0917) (-1.508) 1.54
  dsimp only at h
  rw [show (3787 / 1000 : ℝ) - 2707 / 1000 = 27 / 25 by norm_num only,
    show (3787 / 1000 : ℝ) - 2687 / 1000 = 11 / 10 by norm_num only,
    show (2707 / 1000 : ℝ) - 2687 / 1000 = 1 / 50 by norm_num only] at h
  dsimp only [Z, W, T]
  linarith only [h]

/-- The pole residue and the two contour integrals on the fixed lines ±9/16. -/
noncomputable def contourRemainder644 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  let W := fun s : ℂ ↦ quarterKernel644.function s * (x : ℂ) ^ s
  LLS.PaperStatements.MellinKernel.weightedResidue quarterKernel644
      (fun z : ℂ ↦ χ.completedLFunction (z + 1 / 2)) x (-1 / 2) +
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ,
        -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
          W (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) +
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ,
        logDeriv χ.gammaFactor ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
          W (((9 / 16 : ℝ) : ℂ) + Complex.I * t))

/-- Under GRH, the refined arithmetic sum equals the contour remainder minus its zero sum. -/
theorem contour_formula_644 {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    (∑' n : ℕ, quarterKernel644.summand χ x n) =
      contourRemainder644 χ x - ∑' ρ : ℂ, quarterKernel644.oscillatingZeroTerm χ x ρ := by
  have hd : quarterKernel644.delta = (1 / 8 : ℝ) := by
    norm_num only [quarterKernel644, LLS.PaperStatements.rationalPoleMellinKernel]
    apply min_eq_right
    norm_num only
  have h :=
    LLS.PaperStatements.MellinKernel.tsum_summand_eq_completed_residue_formula quarterKernel644 hq
      hGRH hp hne hinv (a := (-9 / 16 : ℝ)) (b := 9 / 16) (by norm_num only)
      (by
        rw [hd]; norm_num only)
      (by
        rw [hd]; norm_num only)
      (by norm_num only) (by norm_num only) hx (by norm_num only) (by norm_num only)
  dsimp only [contourRemainder644] at *
  linear_combination h

/-- The refined kernel has no residue at the regularization point minus one half. -/
theorem pole_residue_zero_644 (F : ℂ → ℂ) (x : ℝ) :
    LLS.PaperStatements.MellinKernel.weightedResidue quarterKernel644 F x (-1 / 2) = 0 := by
  simp only [LLS.PaperStatements.MellinKernel.weightedResidue]
  change
    -logDeriv F (-1 / 2) *
        (((-1 / 2 : ℂ) + 1 / 2) * quarterKernel644.function (-1 / 2) * (x : ℂ) ^ (-1 / 2)) =
      0
  rw [neg_div, neg_add_cancel, zero_mul, zero_mul, mul_zero]

/-- The refined contour remainder consists exactly of its two vertical integrals. -/
theorem contour_no_residue_644 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) :
    contourRemainder644 χ x =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
              (quarterKernel644.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
                (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) +
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv χ.gammaFactor ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
              (quarterKernel644.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t) *
                (x : ℂ) ^ (((9 / 16 : ℝ) : ℂ) + Complex.I * t))) := by
  simp only [contourRemainder644, pole_residue_zero_644, zero_add]

private theorem zero_re_eq_contour {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hn : χ ≠ 1)
    {x : ℝ} (hx : 1 ≤ x) :
    (∑' ρ, quarterKernel644.oscillatingZeroTerm χ x ρ).re =
      (contourRemainder644 χ x).re - (∑' n, quarterKernel644.summand χ x n).re := by
  have h := congrArg Complex.re (contour_formula_644 hq hG hp hn (inv_ne_one.mpr hn) hx)
  rw [Complex.sub_re] at h
  linarith only [h]

/-- At frequency s ≥ 14/5 the forward sixth-pole prime sum at the shifted
cutoff equals its level-one sum if the character is trivial at primes through X. -/
theorem quarter_shifted_forward_644 {q : ℕ} (χ : DirichletCharacter ℂ q) {X s : ℝ} (hX : 0 < X)
    (hs : 2687 / 1000 ≤ s) (hp : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ X → χ p = 1) :
    (∑' n : ℕ, quarterKernel644.summand χ (X * Real.exp (-s)) n) =
      ∑' n : ℕ, quarterKernel644.summand (1 : DirichletCharacter ℂ 1) (X * Real.exp (-s)) n := by
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · simp only [hn, LLS.PaperStatements.MellinKernel.summand, ite_true]
  simp only [LLS.PaperStatements.MellinKernel.summand, ite_eq_right hn,
    MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1)), mul_one]
  by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
  · simp only [hΛ, zero_div, Complex.ofReal_zero, zero_mul]
  by_cases hcut : (n : ℝ) ≤ X
  · rw [AnalyticNumberTheory.Arithmetic.character_apply_one_of_mangoldt_ne_zero χ hp hcut hΛ,
      mul_one]
  have hx := mul_pos hX (Real.exp_pos (-s))
  have he : Real.exp ((2687 / 1000 : ℝ)) * (X * Real.exp (-s)) ≤ X := by
    have h := Real.exp_le_one_iff.mpr (show (2687 / 1000 : ℝ) + -s ≤ 0 by linarith only [hs])
    rw [Real.exp_add] at h
    linarith only [mul_le_mul_of_nonneg_left h hX.le]
  have hu := (lt_div_iff₀ hx).mpr (he.trans_lt (lt_of_not_ge hcut))
  have hzero :=
    Analysis.rationalPoleProfile_eq_zero 3 (50 / 107) (2687 / 2000)
      (by
        rw [show (2 * (2687 / 2000) : ℝ) = 2687 / 1000 by norm_num only]
        exact hu)
  rw [quarterKernel644,
    LLS.PaperStatements.rationalPole_transform _ _ _ _ ((Real.exp_pos _).trans hu), hzero,
    Complex.ofReal_zero, mul_zero, mul_zero]

/-- The three-frequency lower bound on the zero side gives an upper bound
for the forward prime sum. The shifted oscillating sums are replaced
by the contour remainders minus level-one forward sums, using agreement
on all primes through the cutoff. -/
theorem quarter_three_prime_upper_644 {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hn : χ ≠ 1)
    {X : ℝ} (hX : 1 ≤ X) (hcut : 1 ≤ X * Real.exp (-(3787 / 1000)))
    (hpass : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ X → χ p = 1) :
    let W := fun t : ℝ ↦
      ∑' ρ : ℂ, ‖quarterKernel644.oscillatingZeroTerm χ X ρ‖ * Real.cos (t * ρ.im)
    let C := fun y ↦ (contourRemainder644 χ y).re
    let S := fun y ↦ (∑' n, quarterKernel644.summand χ y n).re
    let T := fun t : ℝ ↦
      C (X * Real.exp (-t)) -
        (∑' n, quarterKernel644.summand (1 : DirichletCharacter ℂ 1) (X * Real.exp (-t)) n).re
    S X +
        (1.54 * (W (2687 / 1000) + T (2687 / 1000)) - 1.508 * (W (2707 / 1000) + T (2707 / 1000)) -
              0.0917 * (W (3787 / 1000) + T (3787 / 1000)) -
              ((1.54 ^ 2 + 1.508 ^ 2 + 0.0917 ^ 2) / 2) * quarterMass644 χ +
            1.54 * 1.508 * W (1 / 50) +
            1.54 * 0.0917 * W (11 / 10) -
          1.508 * 0.0917 * W (27 / 25)) ≤
      quarterMass644 χ + C X := by
  intro W C S T
  have hx := zero_lt_one.trans_le hX
  have cut {t : ℝ} (ht : t ≤ 3787 / 1000) : 1 ≤ X * Real.exp (-t) :=
    hcut.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg ht)) hx.le)
  have h := quarter_three_frequency_644 hq hG hp hn hx
  dsimp only at h
  rw [zero_re_eq_contour hq hG hp hn hX,
    zero_re_eq_contour hq hG hp hn (cut (by norm_num only : (2687 / 1000 : ℝ) ≤ 3787 / 1000)),
    zero_re_eq_contour hq hG hp hn (cut (by norm_num only : (2707 / 1000 : ℝ) ≤ 3787 / 1000)),
    zero_re_eq_contour hq hG hp hn hcut,
    quarter_shifted_forward_644 χ hx (le_refl (2687 / 1000 : ℝ)) hpass,
    quarter_shifted_forward_644 χ hx (by norm_num only : (2687 / 1000 : ℝ) ≤ 2707 / 1000) hpass,
    quarter_shifted_forward_644 χ hx (by norm_num only : (2687 / 1000 : ℝ) ≤ 3787 / 1000)
      hpass] at h
  dsimp only [W, C, S, T]
  linarith only [h]

end PseudoPrime.PrimeTestBounds.MillerRabin
