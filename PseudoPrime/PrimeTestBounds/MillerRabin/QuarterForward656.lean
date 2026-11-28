/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAuxiliary656
public import PseudoPrime.LLS.PaperStatements.MellinKernelExplicitFormula
import PseudoPrime.AnalyticNumberTheory.Arithmetic.CharacterPrimeTriviality

/-! # Section 132 forward-sum comparison -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The pole residue and the two contour integrals on the fixed lines ±9/16. -/
noncomputable def contourRemainder656 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  let W := fun s : ℂ ↦ quarterKernel656.function s * (x : ℂ) ^ s
  LLS.PaperStatements.MellinKernel.weightedResidue quarterKernel656
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
theorem contour_formula_656 {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    (∑' n : ℕ, quarterKernel656.summand χ x n) =
      contourRemainder656 χ x - ∑' ρ : ℂ, quarterKernel656.oscillatingZeroTerm χ x ρ := by
  have hd : quarterKernel656.delta = (1 / 8 : ℝ) := by
    norm_num only [quarterKernel656, LLS.PaperStatements.rationalPoleMellinKernel]
    apply min_eq_right
    norm_num only
  have h :=
    LLS.PaperStatements.MellinKernel.tsum_summand_eq_completed_residue_formula quarterKernel656 hq
      hGRH hp hne hinv (a := (-9 / 16 : ℝ)) (b := 9 / 16) (by norm_num only)
      (by
        rw [hd]; norm_num only)
      (by
        rw [hd]; norm_num only)
      (by norm_num only) (by norm_num only) hx (by norm_num only) (by norm_num only)
  dsimp only [contourRemainder656] at *
  linear_combination h

/-- The refined kernel has no residue at the regularization point minus one half. -/
theorem pole_residue_zero_656 (F : ℂ → ℂ) (x : ℝ) :
    LLS.PaperStatements.MellinKernel.weightedResidue quarterKernel656 F x (-1 / 2) = 0 := by
  simp only [LLS.PaperStatements.MellinKernel.weightedResidue]
  change
    -logDeriv F (-1 / 2) *
        (((-1 / 2 : ℂ) + 1 / 2) * quarterKernel656.function (-1 / 2) * (x : ℂ) ^ (-1 / 2)) =
      0
  rw [neg_div, neg_add_cancel, zero_mul, zero_mul, mul_zero]

/-- The refined contour remainder consists exactly of its two vertical integrals. -/
theorem contour_no_residue_656 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) :
    contourRemainder656 χ x =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
              (quarterKernel656.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
                (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) +
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv χ.gammaFactor ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
              (quarterKernel656.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t) *
                (x : ℂ) ^ (((9 / 16 : ℝ) : ℂ) + Complex.I * t))) := by
  simp only [contourRemainder656, pole_residue_zero_656, zero_add]

private theorem zero_re_eq_contour {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hn : χ ≠ 1)
    {x : ℝ} (hx : 1 ≤ x) :
    (∑' ρ, quarterKernel656.oscillatingZeroTerm χ x ρ).re =
      (contourRemainder656 χ x).re - (∑' n, quarterKernel656.summand χ x n).re := by
  have h := congrArg Complex.re (contour_formula_656 hq hG hp hn (inv_ne_one.mpr hn) hx)
  rw [Complex.sub_re] at h
  linarith only [h]

/-- At frequency s ≥ 21/8 the forward sixth-pole prime sum at the shifted
cutoff equals its level-one sum if the character is trivial at primes through X. -/
theorem quarter_shifted_forward_656 {q : ℕ} (χ : DirichletCharacter ℂ q) {X s : ℝ} (hX : 0 < X)
    (hs : 21 / 8 ≤ s) (hp : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ X → χ p = 1) :
    (∑' n : ℕ, quarterKernel656.summand χ (X * Real.exp (-s)) n) =
      ∑' n : ℕ, quarterKernel656.summand (1 : DirichletCharacter ℂ 1) (X * Real.exp (-s)) n := by
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
  have he : Real.exp ((21 / 8 : ℝ)) * (X * Real.exp (-s)) ≤ X := by
    have h := Real.exp_le_one_iff.mpr (show (21 / 8 : ℝ) + -s ≤ 0 by linarith only [hs])
    rw [Real.exp_add] at h
    linarith only [mul_le_mul_of_nonneg_left h hX.le]
  have hu := (lt_div_iff₀ hx).mpr (he.trans_lt (lt_of_not_ge hcut))
  have hzero :=
    Analysis.rationalPoleProfile_eq_zero 3 (5 / 11) (21 / 16)
      (by
        rw [show (2 * (21 / 16) : ℝ) = 21 / 8 by norm_num only]
        exact hu)
  rw [quarterKernel656,
    LLS.PaperStatements.rationalPole_transform _ _ _ _ ((Real.exp_pos _).trans hu), hzero,
    Complex.ofReal_zero, mul_zero, mul_zero]

/-- The seven shifted scales have their forward support inside the main cutoff,
since every auxiliary displacement from the main shift is nonnegative. -/
theorem quarter_aux_frequency_ge_656 (i : Fin 7) : 21 / 8 ≤ quarterAuxFrequency656 i := by
  have h : ∀ j : Fin 7, 0 ≤ quarterAuxShift656 j := by decide +kernel
  exact le_add_of_nonneg_right (Rat.cast_nonneg.mpr (h i))

/-- Every shifted scale stays at least one once the main radius is 322.
This supplies the lower scale hypothesis for the explicit formula. -/
theorem quarter_aux_scale_ge_one_656 {X : ℝ} (hX : (322 : ℝ) ^ 2 ≤ X) (i : Fin 7) :
    1 ≤ X * Real.exp (-(quarterAuxFrequency656 i)) := by
  have h : ∀ j : Fin 7, quarterAuxShift656 j ≤ 64 / 10 := by decide +kernel
  have hs : quarterAuxFrequency656 i ≤ 10 := by
    have hi := (Rat.cast_le (K := ℝ)).mpr (h i)
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at hi
    unfold quarterAuxFrequency656
    linarith only [hi]
  have he : Real.exp 10 < (3 : ℝ) ^ 10 := by
    rw [show (10 : ℝ) = 1 * ((10 : ℕ) : ℝ) by norm_num only, Real.exp_mul_natCast]
    exact pow_lt_pow_left₀ Real.exp_one_lt_three (Real.exp_pos _).le (by decide)
  rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _), one_mul]
  exact
    (Real.exp_le_exp.mpr hs).trans
      (he.le.trans ((by norm_num only : (3 : ℝ) ^ 10 ≤ 322 ^ 2).trans hX))

/-- Under GRH, replace the seven shifted zero sums by their contour remainders
and level-one forward sums. The prime agreement hypothesis applies on the
whole shifted support, and the main absolute zero mass stays at scale X. -/
theorem quarter_seven_forward_656 {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hn : χ ≠ 1)
    {X : ℝ} (hX : (322 : ℝ) ^ 2 ≤ X) (hpass : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ X → χ p = 1) :
    let Z := quarterKernel656.oscillatingZeroTerm χ X
    let B := fun t : ℝ ↦ ∑' ρ : ℂ, ‖Z ρ‖ * Real.cos (t * ρ.im)
    let T := fun t : ℝ ↦
      (contourRemainder656 χ (X * Real.exp (-t))).re -
        (∑' n, quarterKernel656.summand (1 : DirichletCharacter ℂ 1) (X * Real.exp (-t)) n).re
    (∑' n, quarterKernel656.summand χ X n).re +
        ((∑ i,
            quarterAuxCoeff656 i * (B (quarterAuxFrequency656 i) + T (quarterAuxFrequency656 i))) -
          (∑ i,
              ∑ j,
                quarterAuxCoeff656 i * quarterAuxCoeff656 j *
                  B (quarterAuxFrequency656 i - quarterAuxFrequency656 j)) /
            2) ≤
      (∑' ρ : ℂ, ‖Z ρ‖) + (contourRemainder656 χ X).re := by
  intro Z B T
  have h₁ : 1 ≤ X := (by norm_num only : (1 : ℝ) ≤ 322 ^ 2).trans hX
  have hx := zero_lt_one.trans_le h₁
  have hf := quarter_seven_frequency_656 hq hG hp hn hx
  dsimp only at hf
  have hs (i : Fin 7) :
    (∑' ρ : ℂ,
          quarterKernel656.oscillatingZeroTerm χ (X * Real.exp (-(quarterAuxFrequency656 i)))
            ρ).re =
      T (quarterAuxFrequency656 i) := by
    rw [zero_re_eq_contour hq hG hp hn (quarter_aux_scale_ge_one_656 hX i),
      quarter_shifted_forward_656 χ hx (quarter_aux_frequency_ge_656 i) hpass]
  simp only [hs] at hf
  have hm := zero_re_eq_contour hq hG hp hn h₁
  dsimp only [Z, B] at *
  linarith only [hf, hm]

end PseudoPrime.PrimeTestBounds.MillerRabin
