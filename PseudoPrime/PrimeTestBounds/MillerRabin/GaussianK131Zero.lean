/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Kernel
public import PseudoPrime.LLS.PaperStatements.MellinKernelZeta
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Kernel
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Polynomials
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Polynomials
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Exponential
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAuxiliary656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosinePoles644
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTwoShiftZeta
import PseudoPrime.LLS.PaperStatements.MellinKernelGammaPositiveScale
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosinePoles644
import PseudoPrime.AnalyticNumberTheory.Arithmetic.CharacterFullTriviality
import PseudoPrime.AnalyticNumberTheory.RiemannXi.FinerLLSConstants2
import PseudoPrime.AnalyticNumberTheory.RiemannXi.ZeroMellin
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZeroExclusion

/-! # Gram comparison for the K131 oscillatory zero sum -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Multiplication of the scale by exp(-s) rotates each zero term by
minus s times its ordinate, including terms of zero multiplicity. -/
private theorem k131_zero_term_shift {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) (s : ℝ) (ρ : ℂ) :
    k131MellinKernel.oscillatingZeroTerm χ (x * Real.exp (-s)) ρ =
      k131MellinKernel.oscillatingZeroTerm χ x ρ * Complex.exp ((-(s * ρ.im) : ℝ) * Complex.I) := by
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
theorem k131_shifted_zero_eq {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hn : χ ≠ 1)
    (hi : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) (s : ℝ) :
    let Z := k131MellinKernel.oscillatingZeroTerm χ x
    (∑' ρ : ℂ, ‖Z ρ‖ * Real.cos ((Z ρ).arg - s * ρ.im)) =
      (∑' ρ : ℂ, k131MellinKernel.oscillatingZeroTerm χ (x * Real.exp (-s)) ρ).re := by
  intro Z
  rw [Complex.re_tsum
      (LLS.PaperStatements.MellinKernel.summable_oscillatingZeroTerm k131MellinKernel hq hG hp hn hi
        (mul_pos hx (Real.exp_pos _)))]
  apply tsum_congr
  intro ρ
  rw [k131_zero_term_shift χ hx, Complex.mul_re, Complex.exp_re, Complex.exp_im, Real.cos_sub]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, mul_one, add_zero, Real.exp_zero, one_mul, Real.cos_neg,
    Real.sin_neg]
  change ‖Z ρ‖ * _ = (Z ρ).re * _ - (Z ρ).im * _
  rw [mul_add, ← mul_assoc, Complex.norm_mul_cos_arg, ← mul_assoc, Complex.norm_mul_sin_arg]
  ring

/-- Under GRH, the four auxiliary frequencies give a lower bound for
the K131 zero sum plus its absolute mass. The shifted cosine terms are
the actual oscillating zero sums at positive shifted scales. -/
theorem k131_gram_zero_lower {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hn : χ ≠ 1)
    (hi : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) (s c : Fin 4 → ℝ) :
    let Z := k131MellinKernel.oscillatingZeroTerm χ x
    let B := fun v : ℝ ↦ ∑' ρ : ℂ, ‖Z ρ‖ * Real.cos (v * ρ.im)
    (∑ i,
          c i *
            (B (s i) +
              (∑' ρ : ℂ, k131MellinKernel.oscillatingZeroTerm χ (x * Real.exp (-(s i))) ρ).re)) -
        (∑ i, ∑ j, c i * c j * B (s i - s j)) / 2 ≤
      (∑' ρ : ℂ, ‖Z ρ‖) + (∑' ρ : ℂ, Z ρ).re := by
  intro Z B
  have hZ :=
    LLS.PaperStatements.MellinKernel.summable_oscillatingZeroTerm k131MellinKernel hq hG hp hn hi hx
  have h :=
    finite_frequency_weighted_le (fun ρ ↦ ‖Z ρ‖) (fun ρ ↦ (Z ρ).arg) Complex.im
      (fun ρ ↦ norm_nonneg (Z ρ)) hZ.norm s c
  dsimp only at h
  have hp' (v : ℝ) :
    (∑' ρ : ℂ, ‖Z ρ‖ * Real.cos ((Z ρ).arg - v * ρ.im)) =
      (∑' ρ : ℂ, k131MellinKernel.oscillatingZeroTerm χ (x * Real.exp (-v)) ρ).re :=
    k131_shifted_zero_eq hq hG hp hn hi hx v
  have he : (∑' ρ : ℂ, ‖Z ρ‖ * Real.cos (Z ρ).arg) = (∑' ρ : ℂ, Z ρ).re := by
    rw [Complex.re_tsum hZ]
    exact tsum_congr (fun ρ ↦ Complex.norm_mul_cos_arg (Z ρ))
  simp only [he, hp', B] at h ⊢
  exact h

/-- Each auxiliary scale lies above one throughout the K131 cell, so
the finite forward Euler formula applies to its shifted zero sum. -/
theorem k131_gram_shifted_scale {L : ℝ} (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000) (i : Fin 4) :
    1 ≤ gaussianBridgeScale L ^ 2 * Real.exp (-(k131GramFreq i)) := by
  have hy :=
    (by norm_num only : (0 : ℝ) < 465644807 / 400000).trans_le (gaussian_bridge_scale_mem hL).1
  have hl := (k131_radius_log_mem hL).1
  change 14 ≤ 2 * Real.log (gaussianBridgeScale L) at hl
  have hf := (k131_gram_freq_mem i).2
  have he : Real.exp (k131GramFreq i) ≤ gaussianBridgeScale L ^ 2 := by
    rw [← Real.exp_log (pow_pos hy 2), Real.log_pow]
    apply Real.exp_le_exp.mpr
    norm_num only [Nat.cast_ofNat]
    linarith only [hf, hl]
  rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _), one_mul]
  exact he

/-- The actual four-frequency K131 Gram inequality, specialized to the
bridge scale and the coefficients used in its scalar comparison. -/
theorem k131_bridge_gram_lower {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hn : χ ≠ 1)
    (hi : χ⁻¹ ≠ 1) {L : ℝ} (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000) :
    let x := gaussianBridgeScale L ^ 2
    let Z := k131MellinKernel.oscillatingZeroTerm χ x
    let B := fun v : ℝ ↦ ∑' ρ : ℂ, ‖Z ρ‖ * Real.cos (v * ρ.im)
    let s := k131GramFreq
    let c := k131GramCoeff
    (∑ i,
          c i *
            (B (s i) +
              (∑' ρ : ℂ, k131MellinKernel.oscillatingZeroTerm χ (x * Real.exp (-(s i))) ρ).re)) -
        (∑ i, ∑ j, c i * c j * B (s i - s j)) / 2 ≤
      (∑' ρ : ℂ, ‖Z ρ‖) + (∑' ρ : ℂ, Z ρ).re := by
  have hy :=
    (by norm_num only : (0 : ℝ) < 465644807 / 400000).trans_le (gaussian_bridge_scale_mem hL).1
  exact k131_gram_zero_lower hq hG hp hn hi (pow_pos hy 2) k131GramFreq k131GramCoeff

/-- A shifted zero term in the K131 Gram inequality equals the
conductor and contour contributions minus the corresponding finite Euler sum. -/
theorem k131_shifted_zero_euler {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hn : χ ≠ 1)
    (hi : χ⁻¹ ≠ 1) {L : ℝ} (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000) (i : Fin 4) :
    let x := gaussianBridgeScale L ^ 2 * Real.exp (-(k131GramFreq i))
    (∑' ρ : ℂ, k131MellinKernel.oscillatingZeroTerm χ x ρ).re =
      (Complex.log q * (k131MellinProfile x⁻¹ : ℂ)).re + (k131ReflectedIntegral χ x).re +
          (k131GammaIntegral χ x).re -
        ∑ n ∈ Finset.Icc 0 ⌊x * Real.exp (9 / 4)⌋₊,
          (χ n).re * (k131ForwardWeight (Real.sqrt x) n * ArithmeticFunction.vonMangoldt n) := by
  intro x
  have hx : 1 ≤ x := k131_gram_shifted_scale hL i
  have hy : 1 ≤ Real.sqrt x := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hx
  have h := k131_euler_reflected hq hG hp hn hi hy
  rw [Real.sq_sqrt (zero_le_one.trans hx)] at h
  linarith only [h]

private theorem k131_gram_support_le {L : ℝ} (i : Fin 4) :
    gaussianBridgeScale L ^ 2 * Real.exp (-(k131GramFreq i)) * Real.exp (9 / 4) ≤
      gaussianBridgeScale L ^ 2 := by
  rw [mul_assoc, ← Real.exp_add]
  have h := (k131_gram_freq_mem i).1
  exact mul_le_of_le_one_right (sq_nonneg _) (Real.exp_le_one_iff.mpr (by linarith only [h]))

/-- The shifted contour contribution minus the unsigned Euler sum,
at the i-th auxiliary frequency and the prescribed bridge scale. -/
noncomputable def k131ShiftedDifference {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (L : ℝ)
    (i : Fin 4) : ℝ :=
  let x := gaussianBridgeScale L ^ 2 * Real.exp (-(k131GramFreq i))
  (Complex.log q * (k131MellinProfile x⁻¹ : ℂ)).re + (k131ReflectedIntegral χ x).re +
      (k131GammaIntegral χ x).re -
    ∑ n ∈ Finset.Icc 0 ⌊x * Real.exp (9 / 4)⌋₊,
      k131ForwardWeight (Real.sqrt x) n * ArithmeticFunction.vonMangoldt n

/-- At each auxiliary scale the entire forward support lies below
the main cutoff, so full prime triviality removes the character from the Euler sum. -/
theorem k131_shifted_zero_main {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hn : χ ≠ 1)
    (hi : χ⁻¹ ≠ 1) {L : ℝ} (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000)
    (hsmall : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ gaussianBridgeScale L ^ 2 → χ l = 1) (i : Fin 4) :
    (∑' ρ : ℂ,
          k131MellinKernel.oscillatingZeroTerm χ
            (gaussianBridgeScale L ^ 2 * Real.exp (-(k131GramFreq i))) ρ).re =
      k131ShiftedDifference χ L i := by
  let x := gaussianBridgeScale L ^ 2 * Real.exp (-(k131GramFreq i))
  have hx := zero_lt_one.trans_le (k131_gram_shifted_scale hL i)
  have hx' : 0 ≤ x * Real.exp (9 / 4) := (mul_pos hx (Real.exp_pos _)).le
  have hb (n : ℕ) (hn' : n ∈ Finset.Icc 0 ⌊x * Real.exp (9 / 4)⌋₊) :
    (n : ℝ) ≤ gaussianBridgeScale L ^ 2 :=
    ((Nat.le_floor_iff hx').mp (Finset.mem_Icc.mp hn').2).trans (k131_gram_support_le i)
  have hsum :=
    AnalyticNumberTheory.Arithmetic.weighted_sum_re_eq_of_full_prime_trivial χ hsmall
      (Finset.Icc 0 ⌊x * Real.exp (9 / 4)⌋₊) hb (fun n ↦ k131ForwardWeight (Real.sqrt x) n)
  have h := k131_shifted_zero_euler hq hG hp hn hi hL i
  dsimp only at h
  unfold k131ShiftedDifference
  convert h using 2
  simpa only [mul_comm, mul_left_comm, mul_assoc, x] using hsum.symm

/-- The four-frequency Gram lower bound with the shifted forward terms
already reduced to unsigned prime sums. The remaining moments are cosine moments. -/
theorem k131_bridge_gram_main {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hn : χ ≠ 1)
    (hi : χ⁻¹ ≠ 1) {L : ℝ} (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000)
    (hsmall : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ gaussianBridgeScale L ^ 2 → χ l = 1) :
    let Z := k131MellinKernel.oscillatingZeroTerm χ (gaussianBridgeScale L ^ 2)
    let B := fun v : ℝ ↦ ∑' ρ : ℂ, ‖Z ρ‖ * Real.cos (v * ρ.im)
    let s := k131GramFreq
    let c := k131GramCoeff
    (∑ i, c i * (B (s i) + k131ShiftedDifference χ L i)) -
        (∑ i, ∑ j, c i * c j * B (s i - s j)) / 2 ≤
      (∑' ρ : ℂ, ‖Z ρ‖) + (∑' ρ : ℂ, Z ρ).re := by
  have h := k131_bridge_gram_lower hq hG hp hn hi hL
  dsimp only at h ⊢
  simpa only [k131_shifted_zero_main hq hG hp hn hi hL hsmall] using h

/-- At a nonnegative frequency the real symmetric-kernel zero sum equals the two
vertical integrals less the forward arithmetic sum. The regularization residue
vanishes because the symmetric kernel is holomorphic at minus one half. -/
private theorem k131_mass_contour {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hn : χ ≠ 1)
    {b : ℝ} (hb : 0 ≤ b) :
    let x := Real.exp b
    let W := fun s : ℂ ↦ k131MassFn s * (x : ℂ) ^ s
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
    let d := ((1 / (2 * Real.pi) : ℝ) : ℂ)
    (∑' ρ, k131MassKernel.oscillatingZeroTerm χ x ρ).re =
      (d * ∫ t : ℝ, -logDeriv χ.completedLFunction (l t + 1 / 2) * W (l t)).re +
          (d * ∫ t : ℝ, logDeriv χ.gammaFactor (r t + 1 / 2) * W (r t)).re -
        (∑' n, k131MassKernel.summand χ x n).re := by
  intro x W l r d
  have h :=
    LLS.PaperStatements.MellinKernel.tsum_summand_eq_completed_residue_formula k131MassKernel hq hG
      hp hn (inv_ne_one.mpr hn) (a := (-9 / 16 : ℝ)) (b := 9 / 16) (by norm_num only)
      (by
        change -1 / 2 - (1 / 8 : ℝ) < -9 / 16; norm_num only)
      (by
        change (9 / 16 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
      (by norm_num only) (by norm_num only) (Real.one_le_exp hb) (by norm_num only)
      (by norm_num only)
  have hz (F : ℂ → ℂ) : k131MassKernel.weightedResidue F x (-1 / 2) = 0 := by
    simp only [LLS.PaperStatements.MellinKernel.weightedResidue, ite_true]
    change -logDeriv F (-1 / 2) * (((-1 / 2 : ℂ) + 1 / 2) * _ * _) = 0
    rw [neg_div, neg_add_cancel, zero_mul, zero_mul, mul_zero]
  change
    (∑' n, k131MassKernel.summand χ x n) =
      k131MassKernel.weightedResidue _ x (-1 / 2) -
          (∑' ρ, k131MassKernel.oscillatingZeroTerm χ x ρ) +
        d * (∫ t : ℝ, -logDeriv χ.completedLFunction (l t + 1 / 2) * W (l t)) +
        d * (∫ t : ℝ, logDeriv χ.gammaFactor (r t + 1 / 2) * W (r t)) at h
  rw [hz, zero_sub] at h
  have he := congrArg Complex.re h
  simp only [Complex.add_re, Complex.neg_re] at he
  linarith only [he]

/-- The contour expression for a single frequency: the completed left integral
and the right gamma integral, less the forward symmetric-profile arithmetic sum. -/
noncomputable def k131CosineContour {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (b : ℝ) : ℝ :=
  let x := Real.exp b
  let W := fun s : ℂ ↦ k131MassFn s * (x : ℂ) ^ s
  let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
  let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
  let d := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  (d * ∫ t : ℝ, -logDeriv χ.completedLFunction (l t + 1 / 2) * W (l t)).re +
      (d * ∫ t : ℝ, logDeriv χ.gammaFactor (r t + 1 / 2) * W (r t)).re -
    (∑' n, k131MassKernel.summand χ x n).re

private theorem k131_mass_zero_re {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (b : ℝ) (ρ : ℂ) :
    (k131MassKernel.oscillatingZeroTerm χ (Real.exp b) ρ).re =
      (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
        ‖k131MellinFn (Complex.I * ρ.im)‖ *
        Real.cos (b * ρ.im) := by
  unfold LLS.PaperStatements.MellinKernel.oscillatingZeroTerm
    LLS.PaperStatements.MellinKernel.kernelZeroTerm
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'), ←
    Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp]
  change
    (((MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℤ) : ℂ) *
          k131MassFn (Complex.I * ρ.im) *
          _).re =
      _
  rw [k131_mass_central, ← Complex.ofReal_intCast, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
  simp only [Complex.exp_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, zero_add, add_zero, one_mul,
    Real.exp_zero]

/-- The K131 cosine-weighted zero mass is exactly the symmetric
completed-L contour at the absolute value of the frequency. -/
theorem k131_cosine_contour {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hn : χ ≠ 1)
    {X : ℝ} (hx : 0 < X) (b : ℝ) :
    (∑' ρ : ℂ, ‖k131MellinKernel.oscillatingZeroTerm χ X ρ‖ * Real.cos (b * ρ.im)) =
      k131CosineContour χ |b| := by
  unfold k131CosineContour
  rw [← k131_mass_contour hq hG hp hn (abs_nonneg b),
    Complex.re_tsum
      (LLS.PaperStatements.MellinKernel.summable_oscillatingZeroTerm k131MassKernel hq hG hp hn
        (inv_ne_one.mpr hn) (Real.exp_pos |b|))]
  apply tsum_congr
  intro ρ
  rw [k131_mass_zero_re, k131_zero_mass_term hn hx, k131_mass_central, Complex.ofReal_re]
  rcases le_total 0 b with hb | hb
  · rw [abs_of_nonneg hb]
  · rw [abs_of_nonpos hb, neg_mul, Real.cos_neg]

/-- The K131 Gram comparison with both the cosine moments and the
shifted zero sums replaced by their actual contour expressions. -/
theorem k131_gram_contour_lower {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hn : χ ≠ 1)
    {L : ℝ} (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000)
    (hsmall : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ gaussianBridgeScale L ^ 2 → χ l = 1) :
    let Z := k131MellinKernel.oscillatingZeroTerm χ (gaussianBridgeScale L ^ 2)
    let s := k131GramFreq
    let c := k131GramCoeff
    (∑ i, c i * (k131CosineContour χ |s i| + k131ShiftedDifference χ L i)) -
        (∑ i, ∑ j, c i * c j * k131CosineContour χ |s i - s j|) / 2 ≤
      k131CosineContour χ 0 + (∑' ρ : ℂ, Z ρ).re := by
  have hy :=
    (by norm_num only : (0 : ℝ) < 465644807 / 400000).trans_le (gaussian_bridge_scale_mem hL).1
  have hB := k131_cosine_contour hq hG hp hn (pow_pos hy 2)
  have h0 := hB 0
  simp only [zero_mul, Real.cos_zero, mul_one, abs_zero] at h0
  have h := k131_bridge_gram_main hq hG hp hn (inv_ne_one.mpr hn) hL hsmall
  dsimp only at h ⊢
  simpa only [hB, h0] using h

private theorem k131_mass_even (z : ℂ) : k131MassFn (-z) = k131MassFn z := by
  simp only [k131MassFn, neg_sq]

/-- Reflection interchanges the two lines of real parts ±9/16 and inverts the
scale in the power weight. Evenness preserves the symmetric kernel itself. -/
theorem k131_mass_reflect_line (H : ℂ → ℂ) {x : ℝ} (hx : 0 < x) :
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
    (∫ t : ℝ, H (-(l t)) * (k131MassFn (l t) * (x : ℂ) ^ l t)) =
      ∫ t : ℝ, H (r t) * (k131MassFn (r t) * ((x⁻¹ : ℝ) : ℂ) ^ r t) := by
  intro l r
  let F := fun t : ℝ ↦ H (r t) * (k131MassFn (r t) * ((x⁻¹ : ℝ) : ℂ) ^ r t)
  have hr (t : ℝ) : r (-t) = -(l t) := by
    dsimp only [r, l]
    push_cast
    ring
  have he (t : ℝ) : H (-(l t)) * (k131MassFn (l t) * (x : ℂ) ^ l t) = F (-t) := by
    simp only [F, hr, k131_mass_even, Complex.ofReal_inv, Complex.cpow_neg,
      Complex.inv_cpow_ofReal_nonneg hx.le, inv_inv]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall he)]
  exact MeasureTheory.integral_neg_eq_self F MeasureTheory.volume

/-- The reflected ordinary logarithmic derivative for the symmetric kernel has
the exact forward arithmetic sum at reciprocal scale, with its minus sign. -/
theorem k131_mass_dual_sum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x) :
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ, -logDeriv χ.LFunction (-(l t) + 1 / 2) * (k131MassFn (l t) * (x : ℂ) ^ l t)) =
      ∑' n, k131MassKernel.summand χ x⁻¹ n := by
  intro l
  have h := k131_mass_reflect_line (fun s ↦ -logDeriv χ.LFunction (s + 1 / 2)) hx
  dsimp only at h
  dsimp only [l]
  rw [h]
  exact
    (LLS.PaperStatements.MellinKernel.tsum_summand_eq_integral_logDeriv k131MassKernel χ
        (inv_pos.mpr hx) (by norm_num only)
        (by
          change (9 / 16 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)).symm

/-- The constant logarithmic conductor integrates on the left line to the
continuous symmetric profile at the reciprocal scale. -/
theorem k131_mass_left_conductor (q : ℕ) {x : ℝ} (hx : 0 < x) :
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, Complex.log q * (k131MassFn (l t) * (x : ℂ) ^ l t)) =
      Complex.log q * (k131MassProfile x⁻¹ : ℂ) := by
  intro l
  have h :=
    k131_mass_inversion (c := -9 / 16) (by norm_num only) (by norm_num only) (inv_pos.mpr hx)
  unfold Analysis.inverseMellin at h
  simp only [Complex.ofReal_inv, Complex.cpow_neg, Complex.inv_cpow_ofReal_nonneg hx.le,
    inv_inv] at h
  rw [MeasureTheory.integral_const_mul, mul_left_comm, ← h]

/-- The real symmetric arithmetic summand at any positive scale, also at n = 0
where the von Mangoldt factor vanishes. -/
theorem k131_mass_summand_re {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x) (n : ℕ) :
    (k131MassKernel.summand χ x n).re =
      (χ n).re * (ArithmeticFunction.vonMangoldt n / Real.sqrt n * k131MassProfile (n / x)) := by
  by_cases hn : n = 0
  · subst n
    simp only [LLS.PaperStatements.MellinKernel.summand, ite_true, Complex.zero_re,
      ArithmeticFunction.map_zero, zero_div, zero_mul, mul_zero]
  · have hy := div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) hx
    have ht : k131MassKernel.transform (n / x) = (k131MassProfile (n / x) : ℂ) :=
      k131_mass_inversion (c := 0) (by norm_num only) (by norm_num only) hy
    rw [LLS.PaperStatements.MellinKernel.summand, ite_eq_right hn, ht, mul_comm _ (χ n)]
    rw [mul_assoc, ← Complex.ofReal_mul, Complex.mul_re]
    simp only [Complex.ofReal_im, Complex.ofReal_re, mul_zero, sub_zero]

/-- The real reflected logarithmic derivative is the von Mangoldt series at
reciprocal scale. Its profile argument is n times the original scale. -/
theorem k131_mass_dual_euler {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x) :
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            -logDeriv χ.LFunction (-(l t) + 1 / 2) * (k131MassFn (l t) * (x : ℂ) ^ l t))).re =
      ∑' n : ℕ,
        (χ n).re * (ArithmeticFunction.vonMangoldt n / Real.sqrt n * k131MassProfile (n * x)) := by
  intro l
  rw [k131_mass_dual_sum χ hx,
    Complex.re_tsum
      (LLS.PaperStatements.MellinKernel.summable_summand k131MassKernel χ (inv_pos.mpr hx))]
  apply tsum_congr
  intro n
  simpa only [div_inv_eq_mul] using (k131_mass_summand_re χ (inv_pos.mpr hx) n)

/-- Absolute integrability on the reflected line permits subtraction of the
character and zeta logarithmic derivatives before taking real parts. -/
theorem k131_mass_dual_int {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x) :
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        -logDeriv χ.LFunction (-(l t) + 1 / 2) * (k131MassFn (l t) * (x : ℂ) ^ l t)) := by
  intro l
  let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
  have h :=
    LLS.PaperStatements.MellinKernel.integrable_arithmeticMellin_logDeriv k131MassKernel χ
      (inv_pos.mpr hx) (c := 9 / 16) (by norm_num only)
      (by
        change (9 / 16 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
  apply h.comp_neg.congr
  apply Filter.Eventually.of_forall
  intro t
  change
    -logDeriv χ.LFunction (r (-t) + 1 / 2) * (k131MassFn (r (-t)) * ((x⁻¹ : ℝ) : ℂ) ^ r (-t)) = _
  have hr : r (-t) = -(l t) := by
    dsimp only [r, l]
    push_cast
    ring
  simp only [hr, k131_mass_even, Complex.ofReal_inv, Complex.cpow_neg,
    Complex.inv_cpow_ofReal_nonneg hx.le, inv_inv]

/-- The reflected difference of ordinary logarithmic derivatives contributes
the principal Euler series minus the character Euler series. -/
theorem k131_mass_dual_difference {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) :
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let A := fun {m : ℕ} [NeZero m] (ψ : DirichletCharacter ℂ m) (t : ℝ) ↦
      -logDeriv ψ.LFunction (-(l t) + 1 / 2) * (k131MassFn (l t) * (x : ℂ) ^ l t)
    let S := fun {m : ℕ} (ψ : DirichletCharacter ℂ m) ↦
      ∑' n : ℕ,
        (ψ n).re * (ArithmeticFunction.vonMangoldt n / Real.sqrt n * k131MassProfile (n * x))
    let ψ := (1 : DirichletCharacter ℂ 1)
    (((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, A ψ t - A χ t)).re = S ψ - S χ := by
  intro l A S ψ
  rw [MeasureTheory.integral_sub (k131_mass_dual_int ψ hx) (k131_mass_dual_int χ hx), mul_sub,
    Complex.sub_re]
  exact congrArg₂ (· - ·) (k131_mass_dual_euler ψ hx) (k131_mass_dual_euler χ hx)

/-- The ordinary Euler sum for the symmetric profile at positive scale y. -/
noncomputable def k131MassSum {q : ℕ} (χ : DirichletCharacter ℂ q) (y : ℝ) : ℝ :=
  ∑' n : ℕ, (χ n).re * (ArithmeticFunction.vonMangoldt n / Real.sqrt n * k131MassProfile (n / y))

/-- The cosine kernel has no poles in the comparison strip, so moving a
simple xi pole between the vertical lines adds its weighted residue. -/
theorem k131_cosine_residue {x p : ℝ} (hx : 1 ≤ x) (hlP : -9 / 16 < p) (huP : p < 9 / 16) :
    quarterCosinePole k131MassKernel (9 / 16) p x - quarterCosinePole k131MassKernel (-9 / 16) p x =
      k131MassFn (p : ℂ) * (x : ℂ) ^ (p : ℂ) := by
  refine quarter_cosine_pole_diff k131MassKernel rfl ?_ hx hlP huP
  let U := Complex.re ⁻¹' Set.Ioo (-(3 / 4 : ℝ)) (3 / 4)
  have hU : IsOpen U := isOpen_Ioo.preimage Complex.continuous_re
  have hD : DifferentiableOn ℂ k131MassFn U := fun z hz ↦
    (k131_mass_differentiable hz.1.le hz.2.le).differentiableWithinAt
  exact fun z hl hu ↦ (hD.analyticOnNhd hU) z ⟨by linarith only [hl], by linarith only [hu]⟩

/-- At scale at least one, shifting both xi poles from the right comparison
line to the left contributes the sum of their two weighted residues. -/
theorem k131_cosine_xi_poles {x : ℝ} (hx : 1 ≤ x) :
    let P := quarterCosinePole k131MassKernel
    P (9 / 16) (1 / 2) x + P (9 / 16) (-1 / 2) x -
        (P (-9 / 16) (1 / 2) x + P (-9 / 16) (-1 / 2) x) =
      k131MassFn ((1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ ((1 / 2 : ℝ) : ℂ) +
        k131MassFn ((-1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ ((-1 / 2 : ℝ) : ℂ) := by
  dsimp only
  rw [add_sub_add_comm, k131_cosine_residue hx (by norm_num only) (by norm_num only),
    k131_cosine_residue hx (by norm_num only) (by norm_num only)]

/-- The left comparison integral splits into the conductor, the reflected
Euler difference, and the two simple-pole integrals at positive scale. -/
theorem k131_cosine_left_split {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) :
    let s := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let w := fun t : ℝ ↦ -(s t) + 1 / 2
    let W := fun t : ℝ ↦ k131MassFn (s t) * (x : ℂ) ^ s t
    let C := fun t : ℝ ↦ Complex.log q * W t
    let A := fun {m : ℕ} [NeZero m] (ψ : DirichletCharacter ℂ m) (t : ℝ) ↦
      -logDeriv ψ.LFunction (w t) * W t
    let P := fun (p t : ℝ) ↦ (1 / (s t - (p : ℂ))) * W t
    (∫ t : ℝ,
        (Complex.log q + logDeriv χ.LFunction (w t) - logDeriv riemannZeta (w t) - 1 / w t -
            1 / (w t - 1)) *
          W t) =
      (∫ t : ℝ, C t) + (∫ t : ℝ, A (1 : DirichletCharacter ℂ 1) t - A χ t) +
        (∫ t : ℝ, P (1 / 2) t) +
        ∫ t : ℝ, P (-1 / 2) t := by
  intro s w W C A P
  have hW := k131_mass_line_int (c := -9 / 16) (by norm_num only) (by norm_num only)
  have hc : Continuous (fun t : ℝ ↦ (x : ℂ) ^ s t) :=
    (continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
  have hi : MeasureTheory.Integrable W := by
    apply hW.mul_bdd (c := x ^ (-9 / 16 : ℝ)) hc.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro t
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, line_re]
  have hC : MeasureTheory.Integrable C := hi.const_mul _
  have hA := (k131_mass_dual_int (1 : DirichletCharacter ℂ 1) hx).sub (k131_mass_dual_int χ hx)
  have hP (p : ℝ) (hne : (-9 / 16 : ℝ) ≠ p) : MeasureTheory.Integrable (P p) := by
    simpa only [P, W, s, mul_assoc, k131MassKernel] using
      LLS.PaperStatements.MellinKernel.integrable_pole_power_line k131MassKernel
        (by
          change -1 / 2 - (1 / 8 : ℝ) < -9 / 16; norm_num only)
        (by
          change (-9 / 16 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
        (by norm_num only) hne hx
  have hp := hP (1 / 2) (by norm_num only)
  have hm := hP (-1 / 2) (by norm_num only)
  let B := fun t : ℝ ↦ A (1 : DirichletCharacter ℂ 1) t - A χ t
  change MeasureTheory.Integrable B at hA
  have he (t : ℝ) :=
    twoShift_left_pole_split (s t) (W t) (Complex.log q) (logDeriv χ.LFunction (w t))
      (logDeriv riemannZeta (w t))
  calc
    _ = ∫ t : ℝ, ((C + B) + P (1 / 2) + P (-1 / 2)) t := by
      apply MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t ↦ ?_)
      simpa only [C, B, A, P, Pi.add_apply, DirichletCharacter.LFunction_modOne_eq] using he t
    _ = _ := by
      calc
        _ = _ := MeasureTheory.integral_add ((hC.add hA).add hp) hm
        _ = _ := congrArg (· + _) (MeasureTheory.integral_add (hC.add hA) hp)
        _ = _ := congrArg (fun z ↦ z + _ + _) (MeasureTheory.integral_add hC hA)

/-- The single-frequency difference after both gamma cancellations. The reflected
ordinary logarithmic derivatives are evaluated to the right of one, so their
Dirichlet series converge absolutely. -/
noncomputable def k131CosineEvenDiff {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (b : ℝ) : ℝ :=
  let W := fun s : ℂ ↦ k131MassFn s * ((Real.exp b : ℝ) : ℂ) ^ s
  let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
  let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
  let w := fun t : ℝ ↦ ((17 / 16 : ℝ) : ℂ) - Complex.I * t
  let d := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  (d *
            ∫ t : ℝ,
              (Complex.log q + logDeriv χ.LFunction (w t) - logDeriv riemannZeta (w t) - 1 / w t -
                  1 / (w t - 1)) *
                W (l t)).re -
        (d * ∫ t : ℝ, (1 / (r t - ((-1 / 2 : ℝ) : ℂ))) * W (r t)).re -
        (d * ∫ t : ℝ, (1 / (r t - ((1 / 2 : ℝ) : ℂ))) * W (r t)).re +
      (∑' n, k131MassKernel.summand (1 : DirichletCharacter ℂ 1) (Real.exp b) n).re -
    (∑' n, k131MassKernel.summand χ (Real.exp b) n).re

/-- For a nonnegative frequency the two right-line pole terms in the even
comparison move to the left line, each subtracting its weighted residue. -/
theorem k131_cosine_even_left {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {b : ℝ} (hb : 0 ≤ b) :
    let x := Real.exp b
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let w := fun t : ℝ ↦ ((17 / 16 : ℝ) : ℂ) - Complex.I * t
    let H := fun s : ℂ ↦ k131MassFn s * (x : ℂ) ^ s
    let S := fun {m : ℕ} (ψ : DirichletCharacter ℂ m) ↦ (∑' n, k131MassKernel.summand ψ x n).re
    k131CosineEvenDiff χ b =
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
                ∫ t : ℝ,
                  (Complex.log q + logDeriv χ.LFunction (w t) - logDeriv riemannZeta (w t) -
                      1 / w t -
                      1 / (w t - 1)) *
                    H (l t)).re -
            (quarterCosinePole k131MassKernel (-9 / 16) (-1 / 2) x).re -
            (quarterCosinePole k131MassKernel (-9 / 16) (1 / 2) x).re -
            (H ((-1 / 2 : ℝ) : ℂ)).re -
            (H ((1 / 2 : ℝ) : ℂ)).re +
          S (1 : DirichletCharacter ℂ 1) -
        S χ := by
  intro x l w H S
  have hx : 1 ≤ x := Real.one_le_exp hb
  have hp (p : ℝ) (hl : -9 / 16 < p) (hu : p < 9 / 16) :=
    congrArg Complex.re (k131_cosine_residue hx hl hu)
  have hm := hp (-1 / 2) (by norm_num only) (by norm_num only)
  have hpos := hp (1 / 2) (by norm_num only) (by norm_num only)
  simp only [Complex.sub_re] at hm hpos
  unfold k131CosineEvenDiff
  dsimp only
  have hfun : k131MassKernel.function = k131MassFn := rfl
  simp only [quarterCosinePole, hfun] at hm hpos ⊢
  dsimp only [H, S, w, l, x] at *
  linarith only [hm, hpos]

/-- For a nonnegative frequency the contour comparison consists of the conductor,
the reflected and forward Euler differences, and the two weighted residues. -/
theorem k131_cosine_even_euler {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {b : ℝ}
    (hb : 0 ≤ b) :
    let x := Real.exp b
    let H := fun p : ℝ ↦ (k131MassFn (p : ℂ) * (x : ℂ) ^ (p : ℂ)).re
    let R := fun {m : ℕ} (ψ : DirichletCharacter ℂ m) ↦
      ∑' n : ℕ,
        (ψ n).re * (ArithmeticFunction.vonMangoldt n / Real.sqrt n * k131MassProfile (n * x))
    let S := fun {m : ℕ} (ψ : DirichletCharacter ℂ m) ↦ (∑' n, k131MassKernel.summand ψ x n).re
    let ψ := (1 : DirichletCharacter ℂ 1)
    k131CosineEvenDiff χ b =
      (Complex.log q * (k131MassProfile x⁻¹ : ℂ)).re + (R ψ - R χ) - H (-1 / 2) - H (1 / 2) + S ψ -
        S χ := by
  intro x H R S ψ
  have hx : 0 < x := Real.exp_pos b
  have hw (t : ℝ) :
    ((17 / 16 : ℝ) : ℂ) - Complex.I * t = -(((-9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2 := by
    push_cast
    ring
  have h := k131_cosine_even_left χ hb
  dsimp only at h
  simp_rw [hw] at h
  have hs := k131_cosine_left_split χ hx
  dsimp only at hs
  rw [hs] at h
  simp only [mul_add, Complex.add_re] at h
  have hc := k131_mass_left_conductor q hx
  have ha := k131_mass_dual_difference χ hx
  dsimp only at hc ha
  rw [hc, ha] at h
  unfold quarterCosinePole at h
  dsimp only [k131MassKernel] at h
  dsimp only [x, H, R, S, ψ, k131MassKernel] at *
  linarith only [h]

/-- The real normalized xi contour difference at frequency b, on the same
left and right lines used for the three pair characters. -/
noncomputable def k131CosineXi (b : ℝ) : ℝ :=
  let F := fun s : ℂ ↦
    -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (s + 1 / 2) *
      (k131MassFn s * ((Real.exp b : ℝ) : ℂ) ^ s)
  (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ((∫ t : ℝ, F (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) -
        ∫ t : ℝ, F (((9 / 16 : ℝ) : ℂ) + Complex.I * t))).re

/-- The left character-minus-xi integrals and the two right simple-pole
integrals remaining after cancellation of the common even gamma factor. -/
noncomputable def k131CosineLeftDiff {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (b : ℝ) : ℝ :=
  let W := fun s : ℂ ↦ k131MassFn s * ((Real.exp b : ℝ) : ℂ) ^ s
  let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
  let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
  let d := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  (d * ∫ t : ℝ, -logDeriv χ.completedLFunction (l t + 1 / 2) * W (l t)).re -
    (d * ∫ t : ℝ, -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (l t + 1 / 2) * W (l t)).re -
    (d * ∫ t : ℝ, (1 / (r t - ((-1 / 2 : ℝ) : ℂ))) * W (r t)).re -
    (d * ∫ t : ℝ, (1 / (r t - ((1 / 2 : ℝ) : ℂ))) * W (r t)).re

/-- For an even character at any real frequency the right gamma integral cancels
in the character-minus-xi contour difference. The arithmetic contribution is the
principal forward sum less the character forward sum. -/
theorem k131_cosine_gamma_cancel {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (he : χ.Even)
    (b : ℝ) :
    k131CosineContour χ b - k131CosineXi b =
      k131CosineLeftDiff χ b +
          (∑' n, k131MassKernel.summand (1 : DirichletCharacter ℂ 1) (Real.exp b) n).re -
        (∑' n, k131MassKernel.summand χ (Real.exp b) n).re := by
  have hg : χ.gammaFactor = (1 : DirichletCharacter ℂ 1).gammaFactor := by
    funext z
    rw [he.gammaFactor_def,
      AnalyticNumberTheory.DirichletLFunction.principal_modulus_one_even.gammaFactor_def]
  have h := twoShift_level_one_forward k131MassKernel rfl (Real.exp_pos b)
  dsimp only at h
  have hk : k131MassKernel.function = k131MassFn := rfl
  rw [show k131MassKernel.function = k131MassFn from hk] at h
  unfold k131CosineContour k131CosineXi k131CosineLeftDiff
  dsimp only
  rw [hg, h]
  simp only [mul_sub, mul_add, Complex.sub_re, Complex.add_re]
  ring

/-- For even self-inverse primitive nonprincipal characters, the complete contour
difference at any frequency is the ordinary Euler, conductor and pole expression. -/
theorem k131_cosine_even_diff {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive)
    (hn : χ ≠ 1) (hi : χ⁻¹ = χ) (he : χ.Even) (b : ℝ) :
    k131CosineContour χ b - k131CosineXi b = k131CosineEvenDiff χ b := by
  have hF :=
    LLS.PaperStatements.MellinKernel.integrable_completed_left_line k131MassKernel hp hn
      (inv_ne_one.mpr hn) (c := -9 / 16) (x := Real.exp b)
      (by
        change -1 / 2 - (1 / 8 : ℝ) < -9 / 16; norm_num only)
      (by norm_num only) (by norm_num only) (Real.exp_pos b)
  have hG :=
    LLS.PaperStatements.MellinKernel.integrable_xi_left_line k131MassKernel (c := -9 / 16) (x :=
      Real.exp b)
      (by
        change -1 / 2 - (1 / 8 : ℝ) < -9 / 16; norm_num only)
      (by norm_num only) (by norm_num only) (Real.exp_pos b)
  let W := fun t : ℝ ↦
    k131MassFn (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
      ((Real.exp b : ℝ) : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)
  let s := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2
  let w := fun t : ℝ ↦ ((17 / 16 : ℝ) : ℂ) - Complex.I * t
  change MeasureTheory.Integrable (fun t : ℝ ↦ -logDeriv χ.completedLFunction (s t) * W t) at hF
  change
    MeasureTheory.Integrable
      (fun t : ℝ ↦ -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (s t) * W t) at hG
  have h := MeasureTheory.integral_sub hF hG
  have ht (t : ℝ) := congrArg (fun z : ℂ ↦ z * W t) (twoShift_left_log_difference hp hn hi he t)
  have h' :
    (∫ t : ℝ,
        (Complex.log q + logDeriv χ.LFunction (w t) - logDeriv riemannZeta (w t) - 1 / w t -
            1 / (w t - 1)) *
          W t) =
      _ :=
    Eq.trans
      (MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall fun t ↦ by
          simpa only [s, w, add_mul, neg_mul, sub_neg_eq_add] using (ht t).symm))
      h
  rw [k131_cosine_gamma_cancel χ he b]
  unfold k131CosineLeftDiff k131CosineEvenDiff
  dsimp only
  rw [h', mul_sub, Complex.sub_re]

/-- The paired Euler contribution is the difference between the principal
and character sums at the two reciprocal scales. -/
noncomputable def k131PairedEuler {q : ℕ} (χ : DirichletCharacter ℂ q) (b : ℝ) : ℝ :=
  let y := Real.exp b
  (k131MassSum (1 : DirichletCharacter ℂ 1) y - k131MassSum χ y) +
    (k131MassSum (1 : DirichletCharacter ℂ 1) y⁻¹ - k131MassSum χ y⁻¹)

/-- For an even primitive self-inverse nonprincipal character, the cosine
contour is the common xi contour plus its conductor and paired Euler difference,
minus the two weighted residues. -/
theorem k131_cosine_decompose {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive)
    (hn : χ ≠ 1) (hi : χ⁻¹ = χ) (he : χ.Even) {b : ℝ} (hb : 0 ≤ b) :
    let H := fun p : ℝ ↦ (k131MassFn (p : ℂ) * (Real.exp b : ℂ) ^ (p : ℂ)).re
    k131CosineContour χ b =
      k131CosineXi b + Real.log q * k131MassProfile (Real.exp b)⁻¹ + k131PairedEuler χ b -
        H (-1 / 2) -
        H (1 / 2) := by
  intro H
  have hs {m : ℕ} [NeZero m] (ψ : DirichletCharacter ℂ m) :
    (∑' n, k131MassKernel.summand ψ (Real.exp b) n).re = k131MassSum ψ (Real.exp b) := by
    rw [Complex.re_tsum
        (LLS.PaperStatements.MellinKernel.summable_summand k131MassKernel ψ (Real.exp_pos b))]
    exact tsum_congr (k131_mass_summand_re ψ (Real.exp_pos b))
  have h := k131_cosine_even_euler χ hb
  dsimp only at h
  rw [hs, hs, ← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg q), ←
    Complex.ofReal_mul, Complex.ofReal_re] at h
  have hd := k131_cosine_even_diff hp hn hi he b
  simp only [k131PairedEuler, k131MassSum, div_inv_eq_mul, H] at h ⊢
  linarith only [h, hd]

/-- When the character is one on primes through X, its symmetric Euler deficit
is supported above floor X at every positive scale. -/
theorem k131_mass_sum_tail {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {X y : ℝ} (hX : 0 ≤ X)
    (hy : 0 < y) (hp : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ X → χ p = 1) :
    k131MassSum (1 : DirichletCharacter ℂ 1) y - k131MassSum χ y =
      ∑' n : { n : ℕ // ⌊X⌋₊ < n },
        (1 - (χ n.val).re) *
          (ArithmeticFunction.vonMangoldt n.val / Real.sqrt n.val *
            k131MassProfile (n.val / y)) := by
  let W := fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n / Real.sqrt n * k131MassProfile (n / y)
  have hs {m : ℕ} [NeZero m] (ψ : DirichletCharacter ℂ m) :
    Summable (fun n : ℕ ↦ (ψ n).re * W n) := by
    have h := LLS.PaperStatements.MellinKernel.summable_summand k131MassKernel ψ hy
    exact
      ((Complex.hasSum_re h.hasSum).congr_fun (fun n ↦ (k131_mass_summand_re ψ hy n).symm)).summable
  unfold k131MassSum
  rw [← (hs (1 : DirichletCharacter ℂ 1)).tsum_sub (hs χ)]
  let F := fun n : ℕ ↦ (1 - (χ n).re) * W n
  have he (n : ℕ) : ((1 : DirichletCharacter ℂ 1) n).re * W n - (χ n).re * W n = F n := by
    simp only [F, MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1)), Complex.one_re, sub_mul]
  rw [tsum_congr he]
  symm
  apply tsum_subtype_eq_of_support_subset (f := F) (s := {n : ℕ | ⌊X⌋₊ < n})
  intro n hn
  by_contra hno
  have hcut := (Nat.le_floor_iff hX).mp (le_of_not_gt hno)
  apply hn
  by_cases hm : ArithmeticFunction.vonMangoldt n = 0
  · simp only [F, W, hm, zero_div, zero_mul, mul_zero]
  simp only [F,
    AnalyticNumberTheory.Arithmetic.character_apply_one_of_mangoldt_ne_zero χ hp hcut hm,
    Complex.one_re, sub_self, zero_mul]

/-- At one positive scale the three absolutely convergent character tails
combine into one series weighted by three minus the trace. -/
theorem k131_trace_tail_hasSum {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (X : ℝ)
    {y : ℝ} (hy : 0 < y) :
    let W := fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n / Real.sqrt n * k131MassProfile (n / y)
    let E := fun {m : ℕ} (χ : DirichletCharacter ℂ m) ↦
      ∑' k : { k : ℕ // ⌊X⌋₊ < k }, (1 - (χ k.val).re) * W k.val
    HasSum
      (fun k : { k : ℕ // ⌊X⌋₊ < k } ↦ (3 - ((a k.val).re + (b k.val).re + (c k.val).re)) * W k.val)
      (E a + E b + E c) := by
  intro W E
  have hs {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) :
    Summable (fun n : ℕ ↦ (χ n).re * W n) := by
    have h := LLS.PaperStatements.MellinKernel.summable_summand k131MassKernel χ hy
    exact
      ((Complex.hasSum_re h.hasSum).congr_fun (fun n ↦ (k131_mass_summand_re χ hy n).symm)).summable
  have hW : Summable W := by
    apply (hs (1 : DirichletCharacter ℂ 1)).congr
    intro n
    simp only [MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1)), Complex.one_re, one_mul]
  have hE {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) :
    Summable (fun k : { k : ℕ // ⌊X⌋₊ < k } ↦ (1 - (χ k.val).re) * W k.val) := by
    apply ((hW.sub (hs χ)).subtype _).congr
    intro k
    change W k.val - (χ k.val).re * W k.val = _
    rw [sub_mul, one_mul]
  dsimp only [E]
  apply (((hE a).hasSum.add (hE b).hasSum).add (hE c).hasSum).congr_fun
  intro k
  ring

/-- Summing the trace-weighted series recovers the three individual tails. -/
theorem k131_trace_tail_eq {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r] (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (X : ℝ) {y : ℝ} (hy : 0 < y) :
    let W := fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n / Real.sqrt n * k131MassProfile (n / y)
    let E := fun {m : ℕ} (χ : DirichletCharacter ℂ m) ↦
      ∑' k : { k : ℕ // ⌊X⌋₊ < k }, (1 - (χ k.val).re) * W k.val
    E a + E b + E c =
      ∑' k : { k : ℕ // ⌊X⌋₊ < k },
        (3 - ((a k.val).re + (b k.val).re + (c k.val).re)) * W k.val := by
  exact (k131_trace_tail_hasSum a b c X hy).tsum_eq.symm

/-- The trace-weighted Euler tail for a signed frequency uses both reciprocal
scales and only those integers beyond the tested cutoff. -/
noncomputable def k131CosineTail {p q r : ℕ} (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (X s : ℝ) : ℝ :=
  ∑' n : { n : ℕ // ⌊X⌋₊ < n },
    (3 - ((a n.val).re + (b n.val).re + (c n.val).re)) *
      (ArithmeticFunction.vonMangoldt n.val / Real.sqrt n.val *
        (k131MassProfile (n.val / Real.exp |s|) + k131MassProfile (n.val / (Real.exp |s|)⁻¹)))

/-- The paired Euler deficit equals the six principal-versus-character
deficits at the two reciprocal scales. This is the Euler part of the
three-character cosine contour after the completed functional equation. -/
theorem k131_cosine_tail_deficits {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) {X : ℝ}
    (hX : 0 ≤ X) (s : ℝ) (ha : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ X → a n = 1)
    (hb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ X → b n = 1)
    (hc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ X → c n = 1) :
    let E := fun {m : ℕ} (χ : DirichletCharacter ℂ m) y ↦
      k131MassSum (1 : DirichletCharacter ℂ 1) y - k131MassSum χ y
    let y := Real.exp |s|
    k131CosineTail a b c X s = (E a y + E b y + E c y) + (E a y⁻¹ + E b y⁻¹ + E c y⁻¹) := by
  intro E y
  have hy : 0 < y := Real.exp_pos _
  have hy' := inv_pos.mpr hy
  have h₁ := k131_trace_tail_hasSum a b c X hy
  have h₂ := k131_trace_tail_hasSum a b c X hy'
  have hs :=
    (h₁.add h₂).congr_fun (g := fun n : { n : ℕ // ⌊X⌋₊ < n } ↦
      (3 - ((a n.val).re + (b n.val).re + (c n.val).re)) *
        (ArithmeticFunction.vonMangoldt n.val / Real.sqrt n.val *
          (k131MassProfile (n.val / y) + k131MassProfile (n.val / y⁻¹))))
      (fun n ↦ by
        dsimp only; simp only [mul_add])
  dsimp only [E]
  rw [k131_mass_sum_tail a hX hy ha, k131_mass_sum_tail b hX hy hb, k131_mass_sum_tail c hX hy hc,
    k131_mass_sum_tail a hX hy' ha, k131_mass_sum_tail b hX hy' hb, k131_mass_sum_tail c hX hy' hc]
  exact hs.tsum_eq

/-- At a signed frequency, the part of the three cosine contours independent
of the Euler trace is the common xi term, both residues and the conductor. -/
noncomputable def k131CosineCore (L t : ℝ) : ℝ :=
  let y := Real.exp |t|
  let H := fun u : ℝ ↦ (k131MassFn (u : ℂ) * (y : ℂ) ^ (u : ℂ)).re
  3 * (k131CosineXi |t| - H (-1 / 2) - H (1 / 2)) + L * k131MassProfile y⁻¹

/-- Three even primitive self-inverse characters with prime agreement
have a single paired Euler tail in the decomposition at each frequency. -/
theorem k131_three_cosine_split {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ r}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) {X : ℝ} (hX : 0 ≤ X) (t : ℝ)
    (hpa : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ X → a n = 1)
    (hpb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ X → b n = 1)
    (hpc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ X → c n = 1) :
    k131CosineContour a |t| + k131CosineContour b |t| + k131CosineContour c |t| =
      k131CosineCore (Real.log p + Real.log q + Real.log r) t + k131CosineTail a b c X t := by
  rw [k131_cosine_decompose ha.1 ha.2.1 ha.2.2.1 ha.2.2.2 (abs_nonneg t),
    k131_cosine_decompose hb.1 hb.2.1 hb.2.2.1 hb.2.2.2 (abs_nonneg t),
    k131_cosine_decompose hc.1 hc.2.1 hc.2.2.1 hc.2.2.2 (abs_nonneg t)]
  have h := k131_cosine_tail_deficits a b c hX t hpa hpb hpc
  dsimp only [k131CosineCore, k131PairedEuler] at h ⊢
  linear_combination -h

/-- Beyond the two reciprocal scales, the paired K131 profile is an
exponential times the two translates of the Fourier polynomial. -/
theorem k131_paired_mass_profile {v s : ℝ} (hv : |s| ≤ v) :
    k131MassProfile (Real.exp v / Real.exp |s|) + k131MassProfile (Real.exp v / (Real.exp |s|)⁻¹) =
      Real.exp (-(27 / 16 : ℝ) * v) *
        ((Real.exp ((27 / 16 : ℝ) * |s|) * gaussianK131Fourier.eval (v - |s|) +
            Real.exp (-(27 / 16 : ℝ) * |s|) * gaussianK131Fourier.eval (v + |s|)) /
          2) := by
  have hv₀ := (abs_nonneg s).trans hv
  rw [k131_mass_profile_fourier, k131_mass_profile_fourier,
    Real.log_div (Real.exp_pos _).ne' (Real.exp_pos _).ne',
    Real.log_div (Real.exp_pos _).ne' (inv_ne_zero (Real.exp_pos _).ne'), Real.log_inv,
    Real.log_exp, Real.log_exp, sub_neg_eq_add, abs_of_nonneg (sub_nonneg.mpr hv),
    abs_of_nonneg (add_nonneg hv₀ (abs_nonneg s))]
  have hm :
    Real.exp (-(27 / 16 : ℝ) * (v - |s|)) =
      Real.exp (-(27 / 16 : ℝ) * v) * Real.exp ((27 / 16 : ℝ) * |s|) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hp :
    Real.exp (-(27 / 16 : ℝ) * (v + |s|)) =
      Real.exp (-(27 / 16 : ℝ) * v) * Real.exp (-(27 / 16 : ℝ) * |s|) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hm, hp]
  ring

/-- The signed four-frequency functional that enters the upper bound
for the negative oscillating zero sum. -/
noncomputable def k131GramMix (F : ℝ → ℝ) : ℝ :=
  (∑ i, ∑ j, k131GramCoeff i * k131GramCoeff j * F (k131GramFreq i - k131GramFreq j)) / 2 -
    ∑ i, k131GramCoeff i * F (k131GramFreq i)

/-- The polynomial weight of the signed auxiliary Euler tail, using the
same coefficients as the scalar gap. -/
noncomputable def k131GramEulerPoly : Polynomial ℝ :=
  gramFourier

private theorem k131_gram_mix_tsum {ι : Type*} (F : ℝ → ι → ℝ) (hf : ∀ s, Summable (F s)) :
    Summable (fun n ↦ k131GramMix (fun s ↦ F s n)) ∧
      k131GramMix (fun s ↦ ∑' n, F s n) = ∑' n, k131GramMix (fun s ↦ F s n) := by
  let f := fun i ↦ F (k131GramFreq i)
  let g := fun i j ↦ F (k131GramFreq i - k131GramFreq j)
  let c := k131GramCoeff
  have hp (i j : Fin 4) : Summable (fun n ↦ c i * c j * g i j n) := (hf _).mul_left _
  have hrow (i : Fin 4) : Summable (fun n ↦ ∑ j, c i * c j * g i j n) :=
    summable_sum (fun j _ ↦ hp i j)
  have hP : Summable (fun n ↦ ∑ i, ∑ j, c i * c j * g i j n) := summable_sum (fun i _ ↦ hrow i)
  have hS (i : Fin 4) : Summable (fun n ↦ c i * f i n) := (hf _).mul_left _
  have hSS : Summable (fun n ↦ ∑ i, c i * f i n) := summable_sum (fun i _ ↦ hS i)
  refine ⟨(hP.div_const 2).sub hSS, ?_⟩
  have h := Summable.tsum_sub (hP.div_const 2) hSS
  rw [tsum_div_const, Summable.tsum_finsetSum (fun i _ ↦ hrow i),
    Summable.tsum_finsetSum (fun i _ ↦ hS i)] at h
  simpa only [k131GramMix, f, g, c, Summable.tsum_finsetSum (fun j _ ↦ hp _ j), tsum_mul_left] using
    h.symm

private theorem k131_gram_poly_eval (v : ℝ) :
    k131GramEulerPoly.eval v =
      k131GramMix
        (fun s ↦
          (Real.exp ((27 / 16 : ℝ) * |s|) * gaussianK131Fourier.eval (v - |s|) +
              Real.exp (-(27 / 16 : ℝ) * |s|) * gaussianK131Fourier.eval (v + |s|)) /
            2) := by
  have hd (i j : Fin 4) : k131GramFreq i - k131GramFreq j = offsets i - offsets j := by
    unfold k131GramFreq
    ring
  simp only [k131GramMix, hd]
  simp only [k131GramEulerPoly, gramFourier, shiftedFourier, shiftPoly, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_comp,
    Polynomial.eval_X, k131GramCoeff, k131GramFreq, sub_eq_add_neg, ← neg_mul, Finset.sum_div,
    ← Finset.sum_neg_distrib]
  rw [add_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  · apply Finset.sum_congr rfl
    intro i _
    ring

/-- Beyond `exp 7`, the Euler tail for the mass and Gram terms converges
with the common trace deficit and combined Fourier polynomial. -/
theorem k131_combined_tail_hasSum {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) {X : ℝ}
    (hX : Real.exp 7 ≤ X) :
    HasSum
      (fun n : { n : ℕ // ⌊X⌋₊ < n } ↦
        (3 - ((a n.val).re + (b n.val).re + (c n.val).re)) *
          (ArithmeticFunction.vonMangoldt n.val / (n.val : ℝ) ^ (35 / 16 : ℝ)) *
          (gaussianK131Fourier + k131GramEulerPoly).eval (Real.log n.val))
      (k131CosineTail a b c X 0 + k131GramMix (k131CosineTail a b c X)) := by
  let N := { n : ℕ // ⌊X⌋₊ < n }
  let D := fun n : N ↦ 3 - ((a n.val).re + (b n.val).re + (c n.val).re)
  let F := fun s : ℝ ↦ fun n : N ↦
    D n *
      (ArithmeticFunction.vonMangoldt n.val / Real.sqrt n.val *
        (k131MassProfile (n.val / Real.exp |s|) + k131MassProfile (n.val / (Real.exp |s|)⁻¹)))
  have hF (s : ℝ) : Summable (F s) := by
    have hy := Real.exp_pos |s|
    have h₁ := (k131_trace_tail_hasSum a b c X hy).summable
    have h₂ := (k131_trace_tail_hasSum a b c X (inv_pos.mpr hy)).summable
    dsimp only at h₁ h₂
    exact (h₁.add h₂).congr (fun n ↦ by simp only [F, D, mul_add])
  change HasSum _ ((∑' n, F 0 n) + k131GramMix (fun s ↦ ∑' n, F s n))
  obtain ⟨hs, heq⟩ := k131_gram_mix_tsum F hF
  rw [heq]
  refine ((hF 0).hasSum.add hs.hasSum).congr ?_
  refine fun s ↦ Finset.sum_congr rfl (fun n _ ↦ ?_)
  have hn := (Nat.floor_lt ((Real.exp_pos 7).le.trans hX)).mp n.property
  have hn₀ : (0 : ℝ) < n.val := ((Real.exp_pos 7).trans_le hX).trans hn
  have hl : 7 ≤ Real.log n.val := (Real.le_log_iff_exp_le hn₀).mpr (hX.trans hn.le)
  have hscale :
    Real.exp (-(27 / 16 : ℝ) * Real.log n.val) / Real.sqrt n.val =
      ((n.val : ℝ) ^ (35 / 16 : ℝ))⁻¹ := by
    rw [mul_comm (-(27 / 16 : ℝ)), ← Real.rpow_def_of_pos hn₀, Real.sqrt_eq_rpow, ←
      Real.rpow_sub hn₀, show -(27 / 16 : ℝ) - 1 / 2 = -(35 / 16) by norm_num only,
      Real.rpow_neg hn₀.le]
  let K := D n * (ArithmeticFunction.vonMangoldt n.val / (n.val : ℝ) ^ (35 / 16 : ℝ))
  let P := fun s : ℝ ↦
    (Real.exp ((27 / 16 : ℝ) * |s|) * gaussianK131Fourier.eval (Real.log n.val - |s|) +
        Real.exp (-(27 / 16 : ℝ) * |s|) * gaussianK131Fourier.eval (Real.log n.val + |s|)) /
      2
  have he (s : ℝ) (hs : |s| ≤ 7) : F s n = K * P s := by
    have h := k131_paired_mass_profile (v := Real.log n.val) (s := s) (hs.trans hl)
    rw [Real.exp_log hn₀] at h
    dsimp only [F, K, P]
    rw [h]
    change
      D n *
          (ArithmeticFunction.vonMangoldt n.val / Real.sqrt n.val *
            (Real.exp (-(27 / 16 : ℝ) * Real.log n.val) * P s)) =
        _
    linear_combination (D n * ArithmeticFunction.vonMangoldt n.val * P s) * hscale
  have hf (i : Fin 4) : |k131GramFreq i| ≤ 7 := by
    rw [abs_of_nonneg ((by norm_num only : (0 : ℝ) ≤ 9 / 4).trans (k131_gram_freq_mem i).1)]
    exact (k131_gram_freq_mem i).2
  have hd (i j : Fin 4) : |k131GramFreq i - k131GramFreq j| ≤ 7 := by
    obtain ⟨hi, hi'⟩ := k131_gram_freq_mem i
    obtain ⟨hj, hj'⟩ := k131_gram_freq_mem j
    exact abs_le.mpr ⟨by linarith only [hi, hj'], by linarith only [hi', hj]⟩
  have hm : k131GramMix (fun s ↦ F s n) = K * k131GramMix P := by
    simp only [k131GramMix, he _ (hf _), he _ (hd _ _), mul_sub]
    simp only [Finset.mul_sum, Finset.sum_mul, div_eq_mul_inv]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    · apply Finset.sum_congr rfl
      intro i _
      ring
  change
    F 0 n + k131GramMix (fun s ↦ F s n) =
      K * (gaussianK131Fourier + k131GramEulerPoly).eval (Real.log n.val)
  rw [hm, he 0 (by norm_num only [abs_zero]), Polynomial.eval_add, k131_gram_poly_eval, mul_add]
  have hzero : P 0 = gaussianK131Fourier.eval (Real.log n.val) := by
    simp only [P, abs_zero, mul_zero, Real.exp_zero, one_mul, sub_zero, add_zero]
    ring
  rw [hzero]

/-- The mass and Gram terms together have one trace deficit and the
combined Fourier polynomial used by the scalar gap. -/
theorem k131_combined_euler_tail {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) {X : ℝ}
    (hX : Real.exp 7 ≤ X) :
    k131CosineTail a b c X 0 + k131GramMix (k131CosineTail a b c X) =
      ∑' n : { n : ℕ // ⌊X⌋₊ < n },
        (3 - ((a n.val).re + (b n.val).re + (c n.val).re)) *
          (ArithmeticFunction.vonMangoldt n.val / (n.val : ℝ) ^ (35 / 16 : ℝ)) *
          (gaussianK131Fourier + k131GramEulerPoly).eval (Real.log n.val) := by
  exact (k131_combined_tail_hasSum a b c hX).tsum_eq.symm

/-- A convergent termwise majorant bounds the combined mass and Gram Euler tail. -/
theorem k131_combined_tail_le {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) {X M : ℝ}
    (hX : Real.exp 7 ≤ X) {G : { n : ℕ // ⌊X⌋₊ < n } → ℝ} (hG : HasSum G M)
    (hle :
      ∀ n,
        (3 - ((a n.val).re + (b n.val).re + (c n.val).re)) *
            (ArithmeticFunction.vonMangoldt n.val / (n.val : ℝ) ^ (35 / 16 : ℝ)) *
            (gaussianK131Fourier + k131GramEulerPoly).eval (Real.log n.val) ≤
          G n) :
    k131CosineTail a b c X 0 + k131GramMix (k131CosineTail a b c X) ≤ M := by
  have h := k131_combined_tail_hasSum a b c hX
  rw [← h.tsum_eq, ← hG.tsum_eq]
  exact h.summable.tsum_le_tsum hle hG.summable

/-- When the three real character values sum to at least minus one,
four times the nonnegative part of the weighted kernel bounds the Euler tail. -/
theorem k131_tail_le_four {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r] (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) {X M : ℝ} (hX : Real.exp 7 ≤ X)
    (htrace : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (hM :
      HasSum
        (fun n : { n : ℕ // ⌊X⌋₊ < n } ↦
          4 *
            max 0
              ((ArithmeticFunction.vonMangoldt n.val / (n.val : ℝ) ^ (35 / 16 : ℝ)) *
                (gaussianK131Fourier + k131GramEulerPoly).eval (Real.log n.val)))
        M) :
    k131CosineTail a b c X 0 + k131GramMix (k131CosineTail a b c X) ≤ M := by
  refine k131_combined_tail_le a b c hX hM (fun n ↦ ?_)
  have ha := (Complex.re_le_norm (a n.val)).trans (a.norm_le_one n.val)
  have hb := (Complex.re_le_norm (b n.val)).trans (b.norm_le_one n.val)
  have hc := (Complex.re_le_norm (c n.val)).trans (c.norm_le_one n.val)
  have h₀ : 0 ≤ 3 - ((a n.val).re + (b n.val).re + (c n.val).re) := by linarith only [ha, hb, hc]
  have h₄ : 3 - ((a n.val).re + (b n.val).re + (c n.val).re) ≤ 4 := by linarith only [htrace n.val]
  rw [mul_assoc]
  exact
    (mul_le_mul_of_nonneg_left (le_max_right _ _) h₀).trans
      (mul_le_mul_of_nonneg_right h₄ (le_max_left _ _))

private theorem k131_gram_mix_add (F G : ℝ → ℝ) :
    k131GramMix (fun s ↦ F s + G s) = k131GramMix F + k131GramMix G := by
  simp only [k131GramMix, mul_add, Finset.sum_add_distrib]
  ring

/-- The Gram correction at the four shifted scales, summed with the
signed coefficients from the K131 comparison. -/
noncomputable def k131ShiftedGram {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (L : ℝ) : ℝ :=
  ∑ i, k131GramCoeff i * k131ShiftedDifference χ L i

private theorem k131_gram_upper_one {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hn : χ ≠ 1)
    {L : ℝ} (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000)
    (hsmall : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ gaussianBridgeScale L ^ 2 → χ l = 1) :
    -(∑' ρ : ℂ, k131MellinKernel.oscillatingZeroTerm χ (gaussianBridgeScale L ^ 2) ρ).re ≤
      k131CosineContour χ 0 + k131GramMix (fun t ↦ k131CosineContour χ |t|) -
        k131ShiftedGram χ L := by
  have h := k131_gram_contour_lower hq hG hp hn hL hsmall
  simp only [mul_add, Finset.sum_add_distrib] at h
  unfold k131GramMix k131ShiftedGram
  linarith only [h]

/-- The three oscillatory K131 zero sums are bounded by a common core,
one Euler tail and the four shifted contour differences. -/
theorem k131_three_gram_upper {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ r}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hr : 2 ≤ r)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L : ℝ}
    (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000)
    (hpa : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ gaussianBridgeScale L ^ 2 → a l = 1)
    (hpb : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ gaussianBridgeScale L ^ 2 → b l = 1)
    (hpc : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ gaussianBridgeScale L ^ 2 → c l = 1) :
    let X := gaussianBridgeScale L ^ 2
    let B := k131CosineCore (Real.log p + Real.log q + Real.log r)
    let T :=
      ∑' n : { n : ℕ // ⌊X⌋₊ < n },
        ((3 - ((a n.val).re + (b n.val).re + (c n.val).re)) *
          (ArithmeticFunction.vonMangoldt n.val / (n.val : ℝ) ^ (35 / 16 : ℝ)) *
          (gaussianK131Fourier + k131GramEulerPoly).eval (Real.log n.val));
    -(∑' ρ : ℂ, k131MellinKernel.oscillatingZeroTerm a X ρ).re -
        (∑' ρ : ℂ, k131MellinKernel.oscillatingZeroTerm b X ρ).re -
        (∑' ρ : ℂ, k131MellinKernel.oscillatingZeroTerm c X ρ).re ≤
      B 0 + k131GramMix B + T -
        (k131ShiftedGram a L + k131ShiftedGram b L + k131ShiftedGram c L) := by
  intro X B T
  let S := k131CosineTail a b c X
  have h (t : ℝ) :
    k131CosineContour a |t| + k131CosineContour b |t| + k131CosineContour c |t| = B t + S t :=
    k131_three_cosine_split ha hb hc (sq_nonneg _) t hpa hpb hpc
  have h0 := h 0
  rw [abs_zero] at h0
  have he := congrArg k131GramMix (funext h)
  simp only [k131_gram_mix_add] at he
  have h₁ := k131_gram_upper_one hp hG ha.1 ha.2.1 hL hpa
  have h₂ := k131_gram_upper_one hq hG hb.1 hb.2.1 hL hpb
  have h₃ := k131_gram_upper_one hr hG hc.1 hc.2.1 hL hpc
  have hlog := (k131_radius_log_mem hL).1
  have hy : 0 < gaussianBridgeScale L :=
    (by norm_num only : (0 : ℝ) < 465644807 / 400000).trans_le (gaussian_bridge_scale_mem hL).1
  have hX : Real.exp 7 ≤ X := by
    change Real.exp 7 ≤ gaussianBridgeScale L ^ 2
    rw [← Real.exp_log (pow_pos hy 2), Real.log_pow]
    apply Real.exp_le_exp.mpr
    norm_num only [Nat.cast_ofNat]
    linarith only [hlog]
  have hT : S 0 + k131GramMix S = T := k131_combined_euler_tail a b c hX
  linarith only [h₁, h₂, h₃, h0, he, hT]

/-- Under RH, the oscillating xi zero series for the symmetric kernel equals
the normalized difference of the two vertical xi integrals at scale `exp b`.
The kernel is regular at the half-unit point. -/
theorem k131_symmetric_xi (hRH : RiemannHypothesis) {b : ℝ} (hb : 0 ≤ b) :
    let x := Real.exp b
    let F := fun s : ℂ ↦
      -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (s + 1 / 2) * (k131MassFn s * (x : ℂ) ^ s)
    (∑' ρ, k131MassKernel.zetaOscillatingZeroTerm x ρ) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ((∫ t : ℝ, F (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) -
          ∫ t : ℝ, F (((9 / 16 : ℝ) : ℂ) + Complex.I * t)) := by
  intro x F
  have h :=
    LLS.PaperStatements.MellinKernel.xiContourIdentity k131MassKernel hRH (a := (-9 / 16 : ℝ)) (b :=
      9 / 16)
      (by
        change -1 / 2 - (1 / 8 : ℝ) < -9 / 16; norm_num only)
      (by
        change (9 / 16 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (Real.one_le_exp hb)
  have hz (G : ℂ → ℂ) : k131MassKernel.weightedResidue G x (-1 / 2) = 0 := by
    simp only [LLS.PaperStatements.MellinKernel.weightedResidue, ite_true]
    change -logDeriv G (-1 / 2) * (((-1 / 2 : ℂ) + 1 / 2) * _ * _) = 0
    rw [neg_div, neg_add_cancel, zero_mul, zero_mul, mul_zero]
  change
    Complex.I *
        ((∫ t : ℝ, F (((9 / 16 : ℝ) : ℂ) + t * Complex.I)) -
          ∫ t : ℝ, F (((-9 / 16 : ℝ) : ℂ) + t * Complex.I)) =
      (2 * Real.pi * Complex.I) *
        (k131MassKernel.weightedResidue _ x (-1 / 2) -
          ∑' ρ, k131MassKernel.zetaOscillatingZeroTerm x ρ) at h
  rw [hz, zero_sub, mul_comm (2 * (Real.pi : ℂ)) Complex.I, mul_assoc] at h
  have he := mul_left_cancel₀ Complex.I_ne_zero h
  rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat, one_div]
  simp only [mul_comm Complex.I]
  rw [eq_inv_mul_iff_mul_eq₀ (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))]
  linear_combination he

/-- Under RH and at nonnegative frequency, the real xi contour equals the
real part of the symmetric kernel's oscillating xi zero series. -/
theorem k131_xi_cosine (hRH : RiemannHypothesis) {b : ℝ} (hb : 0 ≤ b) :
    k131CosineXi b = ∑' ρ, (k131MassKernel.zetaOscillatingZeroTerm (Real.exp b) ρ).re := by
  rw [←
    Complex.re_tsum
      (LLS.PaperStatements.MellinKernel.summable_zetaOscillatingZeroTerm k131MassKernel hRH
        (Real.exp_pos b))]
  exact (congrArg Complex.re (k131_symmetric_xi hRH hb)).symm

/-- Every K131 xi cosine moment is bounded in absolute value by the
nonnegative mass at frequency zero. -/
theorem k131_xi_cosine_abs_le (hRH : RiemannHypothesis) {b : ℝ} (hb : 0 ≤ b) :
    |k131CosineXi b| ≤ k131CosineXi 0 := by
  let K := k131MassKernel
  have hs :=
    LLS.PaperStatements.MellinKernel.summable_zetaOscillatingZeroTerm K hRH (Real.exp_pos b)
  have he (ρ : AnalyticNumberTheory.RiemannXi.Zero) :
    ‖K.zetaOscillatingZeroTerm (Real.exp b) ρ‖ = (K.zetaOscillatingZeroTerm (Real.exp 0) ρ).re := by
    rw [LLS.PaperStatements.MellinKernel.norm_zetaOscillatingZeroTerm K (Real.exp_pos b)]
    simp only [LLS.PaperStatements.MellinKernel.zetaOscillatingZeroTerm, Real.exp_zero,
      Complex.ofReal_one, Complex.one_cpow, mul_one]
    unfold LLS.PaperStatements.MellinKernel.zetaKernelZeroTerm
    change ‖_ * k131MassFn (Complex.I * (ρ : ℂ).im)‖ = (_ * k131MassFn (Complex.I * (ρ : ℂ).im)).re
    simp only [k131_mass_central, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _), ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
      Complex.ofReal_re,
      abs_of_nonneg
          (Nat.cast_nonneg (α := ℝ) (AnalyticNumberTheory.RiemannXi.riemannXiZeroMultiplicity ρ))]
  rw [k131_xi_cosine hRH hb, ← Complex.re_tsum hs, k131_xi_cosine hRH le_rfl]
  exact (Complex.abs_re_le_norm _).trans ((norm_tsum_le_tsum_norm hs.norm).trans_eq (tsum_congr he))

/-- Under RH, the K131 xi contribution is at most 231/500000
in absolute value, uniformly in the nonnegative frequency. -/
theorem k131_xi_cosine_cap (hRH : RiemannHypothesis) {b : ℝ} (hb : 0 ≤ b) :
    |k131CosineXi b| ≤ (231 / 500000 : ℝ) := by
  let K := k131MassKernel
  let W := fun ρ : AnalyticNumberTheory.RiemannXi.Zero ↦
    (AnalyticNumberTheory.RiemannXi.riemannXiZeroMultiplicity ρ : ℝ) / ‖(ρ : ℂ)‖ ^ 2
  have hs :=
    LLS.PaperStatements.MellinKernel.summable_zetaOscillatingZeroTerm K hRH (Real.exp_pos b)
  have hW : Summable W := by
    have h := AnalyticNumberTheory.RiemannXi.summable_zeroMultiplicityInvNormSq_RH hRH
    apply (h.subtype _).congr
    intro ρ
    simp only [W, Function.comp_apply, ite_eq_left ρ.property, Complex.normSq_eq_norm_sq]
  have he (ρ : AnalyticNumberTheory.RiemannXi.Zero) :
    ‖K.zetaOscillatingZeroTerm (Real.exp b) ρ‖ ≤ (1 / 100 : ℝ) * W ρ := by
    have hr := AnalyticNumberTheory.RiemannXi.xi_zero_re_eq_half_of_riemannHypothesis hRH ρ.property
    have hz := AnalyticNumberTheory.RiemannXi.riemannZeta_zero_of_riemannXi_zero ρ.property
    have ht :=
      AnalyticNumberTheory.RiemannZeta.zero_height_gt_two_pi hRH hz
        (by
          rw [hr]; norm_num only)
    have ht' : 6 ≤ |(ρ : ℂ).im| := by linarith only [ht, Real.pi_gt_three]
    have hnorm : ‖(ρ : ℂ)‖ ^ 2 = (ρ : ℂ).im ^ 2 + 1 / 4 := by
      rw [Complex.sq_norm, Complex.normSq_apply, hr]
      ring
    rw [LLS.PaperStatements.MellinKernel.norm_zetaOscillatingZeroTerm K (Real.exp_pos b)]
    unfold LLS.PaperStatements.MellinKernel.zetaKernelZeroTerm
    rw [norm_mul, Complex.norm_natCast]
    change _ * ‖k131MassFn (Complex.I * (ρ : ℂ).im)‖ ≤ _
    have h :=
      mul_le_mul_of_nonneg_left (k131_mass_axis_cap ht')
        (Nat.cast_nonneg (α := ℝ) (AnalyticNumberTheory.RiemannXi.riemannXiZeroMultiplicity ρ))
    dsimp only [W]
    rw [hnorm]
    exact
      h.trans_eq
        (by
          simp only [div_eq_mul_inv, mul_inv]; ring)
  have h := hs.norm.tsum_le_tsum he (hW.mul_left (1 / 100 : ℝ))
  rw [tsum_mul_left] at h
  change _ ≤ (1 / 100 : ℝ) * (∑' ρ, W ρ) at h
  dsimp only [W] at h
  rw [AnalyticNumberTheory.RiemannXi.tsum_zeroInvSq_eq_two_mass_RH hRH] at h
  rw [k131_xi_cosine hRH hb, ← Complex.re_tsum hs]
  refine (Complex.abs_re_le_norm _).trans ((norm_tsum_le_tsum_norm hs.norm).trans ?_)
  exact h.trans (by linarith only [AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_231_div_10000])

private theorem k131_gram_abs_sum : (∑ i : Fin 4, |k131GramCoeff i|) = (2003 / 5000 : ℝ) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change
    |(1831 / 10000 : ℝ)| + (|(-973 / 5000 : ℝ)| + (|(1 / 80 : ℝ)| + (|(-13 / 1250 : ℝ)| + 0))) = _
  norm_num only [abs_div, abs_neg, abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 1831),
    abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 973),
    abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 13), abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 1),
    abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 10000),
    abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 5000),
    abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 80),
    abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 1250)]

private theorem k131_gram_mix_abs_le (F : ℝ → ℝ) {M : ℝ} (_hM : 0 ≤ M) (hF : ∀ s, |F s| ≤ M) :
    |k131GramMix F| ≤ ((2003 / 5000 : ℝ) ^ 2 / 2 + 2003 / 5000) * M := by
  let c := k131GramCoeff
  let D := ∑ i : Fin 4, |c i|
  have hD : D = 2003 / 5000 := k131_gram_abs_sum
  let A := ∑ i : Fin 4, ∑ j : Fin 4, c i * c j * F (k131GramFreq i - k131GramFreq j)
  let B := ∑ i : Fin 4, c i * F (k131GramFreq i)
  have hB : |B| ≤ D * M := by
    dsimp only [B, D]
    rw [Finset.sum_mul]
    exact
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum
          (fun i _ ↦ by
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (hF _) (abs_nonneg _)))
  have hA : |A| ≤ D ^ 2 * M := by
    dsimp only [A, D]
    rw [pow_two, Finset.sum_mul, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ ↦ ?_))
    rw [Finset.mul_sum, Finset.sum_mul]
    exact
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum
          (fun j _ ↦ by
            rw [abs_mul, abs_mul]
            exact mul_le_mul_of_nonneg_left (hF _) (mul_nonneg (abs_nonneg _) (abs_nonneg _))))
  change |A / 2 - B| ≤ _
  have h := abs_add_le (A / 2) (-B)
  simp only [← sub_eq_add_neg, abs_neg, abs_div,
    abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 2)] at h
  rw [← hD]
  nlinarith only [h, hA, hB]

/-- The full three-character xi contribution, including the mass
at zero and the Gram correction, has absolute size at most 21/10000. -/
theorem k131_xi_gram_cap (hRH : RiemannHypothesis) :
    |3 * (k131CosineXi 0 + k131GramMix (fun s ↦ k131CosineXi |s|))| ≤ (21 / 10000 : ℝ) := by
  have h₀ := k131_xi_cosine_cap hRH (b := 0) le_rfl
  have h₁ :=
    k131_gram_mix_abs_le (fun s ↦ k131CosineXi |s|) (by norm_num only : (0 : ℝ) ≤ 231 / 500000)
      (fun s ↦ k131_xi_cosine_cap hRH (abs_nonneg s))
  rw [abs_mul, abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 3)]
  have h := abs_add_le (k131CosineXi 0) (k131GramMix (fun s ↦ k131CosineXi |s|))
  nlinarith only [h₀, h₁, h]

/-- Under RH, the oscillating principal zero sum for the nonsymmetric
K131 kernel is the normalized difference of its two vertical xi integrals. -/
theorem k131_forward_xi_contour (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    let F := fun s : ℂ ↦
      -logDeriv (AnalyticNumberTheory.RiemannXi.riemannXi) (s + 1 / 2) *
        (k131MellinFn s * (x : ℂ) ^ s)
    (∑' ρ, k131MellinKernel.zetaOscillatingZeroTerm x ρ) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ((∫ t : ℝ, F (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) -
          ∫ t : ℝ, F (((9 / 16 : ℝ) : ℂ) + Complex.I * t)) := by
  intro F
  have h :=
    LLS.PaperStatements.MellinKernel.xiContourIdentity k131MellinKernel hRH (a := (-9 / 16 : ℝ))
      (b := 9 / 16)
      (by
        rw [k131_kernel_delta]; norm_num only)
      (by
        rw [k131_kernel_delta]; norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only) hx
  change
    Complex.I *
        ((∫ t : ℝ, F (((9 / 16 : ℝ) : ℂ) + t * Complex.I)) -
          ∫ t : ℝ, F (((-9 / 16 : ℝ) : ℂ) + t * Complex.I)) =
      (2 * Real.pi * Complex.I) *
        (k131MellinKernel.weightedResidue _ x (-1 / 2) -
          ∑' ρ, k131MellinKernel.zetaOscillatingZeroTerm x ρ) at h
  rw [k131_zero_residue, zero_sub, mul_comm (2 * (Real.pi : ℂ)) Complex.I, mul_assoc] at h
  have he := mul_left_cancel₀ Complex.I_ne_zero h
  rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat, one_div]
  simp only [mul_comm Complex.I]
  rw [eq_inv_mul_iff_mul_eq₀ (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))]
  linear_combination he

/-- The shifted K131 principal zero sum is uniformly bounded in absolute
value by the same zero mass as the zero-frequency symmetric kernel. -/
theorem k131_forward_xi_cap (hRH : RiemannHypothesis) {x : ℝ} (hx : 0 < x) :
    |(∑' ρ, k131MellinKernel.zetaOscillatingZeroTerm x ρ).re| ≤ (231 / 500000 : ℝ) := by
  let K := k131MellinKernel
  let S := k131MassKernel
  have hs := LLS.PaperStatements.MellinKernel.summable_zetaOscillatingZeroTerm K hRH hx
  have he (ρ : AnalyticNumberTheory.RiemannXi.Zero) :
    ‖K.zetaOscillatingZeroTerm x ρ‖ = (S.zetaOscillatingZeroTerm (Real.exp 0) ρ).re := by
    rw [LLS.PaperStatements.MellinKernel.norm_zetaOscillatingZeroTerm K hx]
    simp only [LLS.PaperStatements.MellinKernel.zetaOscillatingZeroTerm, Real.exp_zero,
      Complex.ofReal_one, Complex.one_cpow, mul_one]
    unfold LLS.PaperStatements.MellinKernel.zetaKernelZeroTerm
    change
      ‖_ * k131MellinFn (Complex.I * (ρ : ℂ).im)‖ = (_ * k131MassFn (Complex.I * (ρ : ℂ).im)).re
    simp only [k131_mass_central, norm_mul, ← Complex.ofReal_natCast, Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_nonneg
          (Nat.cast_nonneg (α := ℝ) (AnalyticNumberTheory.RiemannXi.riemannXiZeroMultiplicity ρ)),
      ← Complex.ofReal_mul, Complex.ofReal_re]
  change |(∑' ρ, K.zetaOscillatingZeroTerm x ρ).re| ≤ _
  refine (Complex.abs_re_le_norm _).trans ((norm_tsum_le_tsum_norm hs.norm).trans ?_)
  rw [tsum_congr he, ← k131_xi_cosine hRH le_rfl]
  exact (le_abs_self _).trans (k131_xi_cosine_cap hRH le_rfl)

/-- The four shifted principal xi sums, counted for all three pair
characters, cost at most `3/5000` on the K131 bridge under RH. -/
theorem k131_shift_xi_cap (hRH : RiemannHypothesis) {L : ℝ} (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000) :
    let X := gaussianBridgeScale L ^ 2
    |3 *
          (∑ j : Fin 4,
            k131GramCoeff j *
              (∑' ρ,
                  k131MellinKernel.zetaOscillatingZeroTerm (X * Real.exp (-(k131GramFreq j)))
                    ρ).re)| ≤
      (3 / 5000 : ℝ) := by
  intro X
  let F := fun j : Fin 4 ↦
    (∑' ρ, k131MellinKernel.zetaOscillatingZeroTerm (X * Real.exp (-(k131GramFreq j))) ρ).re
  have hcap (j : Fin 4) : |F j| ≤ (231 / 500000 : ℝ) :=
    k131_forward_xi_cap hRH (zero_lt_one.trans_le (k131_gram_shifted_scale hL j))
  have hs : |∑ j : Fin 4, k131GramCoeff j * F j| ≤ (2003 / 5000 : ℝ) * (231 / 500000) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [← k131_gram_abs_sum, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hcap j) (abs_nonneg _)
  change |3 * ∑ j : Fin 4, k131GramCoeff j * F j| ≤ _
  rw [abs_mul, abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 3)]
  linarith only [hs]

/-- The common symmetric xi terms and all shifted principal terms together
cost at most `27/10000` on the affine K131 bridge. -/
theorem k131_total_xi_cap (hRH : RiemannHypothesis) {L : ℝ} (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000) :
    let X := gaussianBridgeScale L ^ 2
    |3 * (k131CosineXi 0 + k131GramMix (fun s ↦ k131CosineXi |s|)) -
          3 *
            (∑ j : Fin 4,
              k131GramCoeff j *
                (∑' ρ,
                    k131MellinKernel.zetaOscillatingZeroTerm (X * Real.exp (-(k131GramFreq j)))
                      ρ).re)| ≤
      (27 / 10000 : ℝ) := by
  intro X
  let A := 3 * (k131CosineXi 0 + k131GramMix (fun s ↦ k131CosineXi |s|))
  let B :=
    3 *
      (∑ j : Fin 4,
        k131GramCoeff j *
          (∑' ρ, k131MellinKernel.zetaOscillatingZeroTerm (X * Real.exp (-(k131GramFreq j))) ρ).re)
  have h := abs_add_le A (-B)
  simp only [← sub_eq_add_neg, abs_neg] at h
  have hs := k131_shift_xi_cap hRH hL
  dsimp only at hs
  change |A - B| ≤ _
  have ha : |A| ≤ 21 / 10000 := k131_xi_gram_cap hRH
  have hb : |B| ≤ 3 / 5000 := hs
  linarith only [ha, hb, h]

/-- The right-line principal xi term and its two pole integrals for K131. -/
noncomputable def k131RightXiPoles (x : ℝ) : ℂ :=
  let s := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
  let W := fun t : ℝ ↦ k131MellinFn (s t) * (x : ℂ) ^ s t
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    ((∫ t : ℝ, -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (s t + 1 / 2) * W t) +
      (∫ t : ℝ, (1 / (s t - ((-1 / 2 : ℝ) : ℂ))) * W t) +
      ∫ t : ℝ, (1 / (s t - ((1 / 2 : ℝ) : ℂ))) * W t)

/-- At positive scale the unsigned forward Mangoldt sum equals the principal
xi and pole terms plus the central gamma integral of any even character. -/
theorem k131_principal_forward_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (he : χ.Even)
    {y : ℝ} (hy : 0 < y) :
    (∑ n ∈ Finset.Icc 0 ⌊y ^ 2 * Real.exp (9 / 4)⌋₊,
        k131ForwardWeight y n * ArithmeticFunction.vonMangoldt n) =
      (k131RightXiPoles (y ^ 2)).re + (k131GammaIntegral χ (y ^ 2)).re := by
  have hr := twoShift_level_one_forward k131MellinKernel k131_kernel_delta (pow_pos hy 2)
  dsimp only at hr
  rw [LLS.PaperStatements.MellinKernel.gammaIntegral_eq_central_of_pos k131MellinKernel
      (1 : DirichletCharacter ℂ 1) (by norm_num only : (0 : ℝ) ≤ 9 / 16)
      (by
        rw [k131_kernel_delta]; norm_num only)
      (by norm_num only) (pow_pos hy 2)] at hr
  rw [k131_kernel_tsum_eq hy] at hr
  have hgamma : χ.gammaFactor = (1 : DirichletCharacter ℂ 1).gammaFactor := by
    funext z
    rw [he.gammaFactor_def,
      AnalyticNumberTheory.DirichletLFunction.principal_modulus_one_even.gammaFactor_def]
  have h := congrArg Complex.re hr
  simp only [Complex.add_re, Complex.re_sum,
    MulChar.one_apply (isUnit_of_subsingleton (_ : ZMod 1)), mul_one, Complex.ofReal_re] at h
  unfold k131GammaIntegral
  rw [hgamma]
  exact h

/-- For each K131 Gram frequency the principal forward sum cancels the
central gamma contribution of an even character. -/
theorem k131_shifted_principal_cancel {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (he : χ.Even)
    {L : ℝ} (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000) (i : Fin 4) :
    let x := gaussianBridgeScale L ^ 2 * Real.exp (-(k131GramFreq i))
    k131ShiftedDifference χ L i =
      (Complex.log q * (k131MellinProfile x⁻¹ : ℂ)).re + (k131ReflectedIntegral χ x).re -
        (k131RightXiPoles x).re := by
  intro x
  have hx := zero_lt_one.trans_le (k131_gram_shifted_scale hL i)
  have h := k131_principal_forward_eq χ he (Real.sqrt_pos.2 hx)
  rw [Real.sq_sqrt hx.le] at h
  unfold k131ShiftedDifference
  dsimp only [x] at h ⊢
  linarith only [h]

/-- The K131 pole integral on a vertical line at real part `c`. -/
noncomputable def k131PoleIntegral (c p x : ℝ) : ℂ :=
  let s := fun t : ℝ ↦ (c : ℂ) + Complex.I * t
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ t : ℝ, (1 / (s t - (p : ℂ))) * (k131MellinFn (s t) * (x : ℂ) ^ s t)

/-- Moving a K131 pole integral across the comparison strip adds the
weighted residue at the interior pole. -/
theorem k131_pole_difference {x p : ℝ} (hx : 1 ≤ x) (hlP : -9 / 16 < p) (huP : p < 9 / 16) :
    k131PoleIntegral (9 / 16) p x - k131PoleIntegral (-9 / 16) p x =
      k131MellinFn (p : ℂ) * (x : ℂ) ^ (p : ℂ) := by
  let a : ℝ := -9 / 16
  let b : ℝ := 9 / 16
  let K := k131MellinKernel
  let F := fun s : ℂ ↦ (1 / (s - (p : ℂ))) * K.function s * (x : ℂ) ^ s
  let T := fun n : ℕ ↦ (n : ℝ) + 1
  have hd : K.delta = 1 / 8 := k131_kernel_delta
  have hl : -1 / 2 - K.delta < a := by
    rw [hd]; norm_num only [a]
  have hu : b ≤ 1 / 2 + K.delta := by
    rw [hd]; norm_num only [b]
  have ha : a ≤ b := by norm_num only [a, b]
  have hxp := zero_lt_one.trans_le hx
  have hi0 :=
    LLS.PaperStatements.MellinKernel.integrable_pole_power_line K (hl.trans_le ha) hu
      (by norm_num only [b]) (ne_of_gt huP) hxp
  have hia :=
    LLS.PaperStatements.MellinKernel.integrable_pole_power_line K hl (ha.trans hu)
      (by norm_num only [a, b]) (ne_of_lt hlP) hxp
  have ht := LLS.PaperStatements.MellinKernel.tendsto_pole_horizontalIntegral K ha hl hu hx p
  have hlim :=
    AnalyticNumberTheory.RectangleGeometry.tendsto_boundaryIntegral (K := F) (a := a) (b := b) T
      (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
      (by
        simpa only [F, T, neg_one_mul, Complex.ofReal_neg, neg_mul, sub_eq_add_neg, one_mul] using
          ht (-1) (Or.inr rfl))
      (by simpa only [F, T, one_mul] using ht 1 (Or.inl rfl))
      (by simpa only [F, mul_comm Complex.I, mul_assoc] using hia)
      (by simpa only [F, mul_comm Complex.I, mul_assoc] using hi0)
  let H := fun z : ℂ ↦ K.function z * (x : ℂ) ^ z
  have hH (z : ℂ) (hr : a ≤ z.re) (hs : z.re ≤ b) : AnalyticAt ℂ H z := by
    have hn : (1 : ℂ) + 2 * ((8 / 27 : ℝ) : ℂ) * z ≠ 0 := by
      intro h
      have hh := congrArg Complex.re h
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num only [Complex.ofReal_ofNat], ←
        Complex.ofReal_mul] at hh
      simp only [Complex.add_re, Complex.mul_re, Complex.zero_re, Complex.one_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero] at hh
      linarith only [hh, show (-9 / 16 : ℝ) ≤ z.re from hr]
    change AnalyticAt ℂ (fun u ↦ k131MellinFn u * (x : ℂ) ^ u) z
    simp only [k131MellinFn, k131Pole, LLS.PaperStatements.rationalPoleMellinKernel,
      Analysis.rationalPoleFunction]
    fun_prop (disch :=
      first
      | exact pow_ne_zero _ hn
      | exact Complex.ofReal_mem_slitPlane.mpr hxp)
  have hz (n : ℕ) :
    AnalyticNumberTheory.RectangleGeometry.rectangleBoundaryIntegral F ((a : ℂ) - T n * Complex.I)
        ((b : ℂ) + T n * Complex.I) =
      2 * Real.pi * Complex.I * H (p : ℂ) := by
    have htpos : 0 < T n := by
      dsimp only [T]; linarith only [Nat.cast_nonneg (α := ℝ) n]
    have ho :
      (p : ℂ) ∈
        AnalyticNumberTheory.RectangleGeometry.rectangleOpenBox ((a : ℂ) - T n * Complex.I)
          ((b : ℂ) + T n * Complex.I) := by
      change ((_ < _ ∧ _ < _) ∧ (_ < _ ∧ _ < _))
      simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_im, mul_zero, sub_zero, add_zero, Complex.sub_im,
        Complex.add_im, Complex.mul_im, mul_one, zero_add, zero_sub, min_eq_left ha,
        max_eq_right ha, min_eq_left (neg_le_self htpos.le), max_eq_right (neg_le_self htpos.le)]
      exact ⟨⟨hlP, huP⟩, neg_lt_zero.mpr htpos, htpos⟩
    apply
      AnalyticNumberTheory.RectangleGeometry.boundaryIntegral_simple_pole
        (by
          simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
            Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero]
          norm_num only [a, b])
        (by
          simpa only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
            Complex.I_im, Complex.I_re, Complex.ofReal_re, mul_one, mul_zero, add_zero, zero_add,
            zero_sub] using neg_lt_self htpos)
        ho
    · intro z hbox hne
      have hr := hbox.1
      change z.re ∈ Set.uIcc _ _ at hr
      simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero, Set.uIcc_of_le ha,
        Set.mem_Icc] at hr
      simp only [F, mul_assoc]
      exact
        ((differentiableAt_const (1 : ℂ)).div (differentiableAt_id.sub_const (p : ℂ))
              (sub_ne_zero.mpr hne)).mul
          (hH z hr.1 hr.2).differentiableAt
    · exact hH _ hlP.le huP.le
    · filter_upwards [self_mem_nhdsWithin] with z hz
      have hn : z ≠ (p : ℂ) := hz
      dsimp only [F, H]
      rw [← mul_assoc, ← mul_assoc, one_div, mul_inv_cancel₀ (sub_ne_zero.mpr hn), one_mul]
  have h := tendsto_nhds_unique hlim (tendsto_const_nhds.congr (fun n ↦ (hz n).symm))
  rw [mul_comm (2 * (Real.pi : ℂ)) Complex.I, mul_assoc] at h
  have he := mul_left_cancel₀ Complex.I_ne_zero h
  let d : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  have hi : d * (2 * (Real.pi : ℂ)) = 1 := by
    dsimp only [d]
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat, one_div,
      inv_mul_cancel₀ (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))]
  have hh := congrArg (fun u ↦ d * u) he
  rw [mul_sub, ← mul_assoc, hi, one_mul] at hh
  simpa only [k131PoleIntegral, F, K, H, a, b, d,
    show k131MellinKernel.function = k131MellinFn from rfl, mul_comm Complex.I, mul_assoc] using hh

/-- The left-line xi integral and both pole integrals for K131. -/
noncomputable def k131LeftXiPoles (x : ℝ) : ℂ :=
  let s := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
  let W := fun t : ℝ ↦ k131MellinFn (s t) * (x : ℂ) ^ s t
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    ((∫ t : ℝ, -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (s t + 1 / 2) * W t) +
      (∫ t : ℝ, (1 / (s t - ((-1 / 2 : ℝ) : ℂ))) * W t) +
      ∫ t : ℝ, (1 / (s t - ((1 / 2 : ℝ) : ℂ))) * W t)

/-- The difference of the right and left principal K131 contours is
the sum of both Mellin residues minus the oscillating zeta zero sum. -/
theorem k131_xi_poles_difference (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    k131RightXiPoles x - k131LeftXiPoles x =
      k131MellinFn ((-1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ ((-1 / 2 : ℝ) : ℂ) +
          k131MellinFn ((1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ ((1 / 2 : ℝ) : ℂ) -
        ∑' ρ, k131MellinKernel.zetaOscillatingZeroTerm x ρ := by
  have hl := k131_pole_difference hx (p := -1 / 2) (by norm_num only) (by norm_num only)
  have hr := k131_pole_difference hx (p := 1 / 2) (by norm_num only) (by norm_num only)
  have hz := k131_forward_xi_contour hRH hx
  dsimp only at hz
  simp only [k131RightXiPoles, k131LeftXiPoles, k131PoleIntegral, mul_add, mul_sub] at hl hr hz ⊢
  linear_combination hl + hr + hz

end PseudoPrime.PrimeTestBounds.MillerRabin
