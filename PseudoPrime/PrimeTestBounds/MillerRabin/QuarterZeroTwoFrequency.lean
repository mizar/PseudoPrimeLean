/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.CharacterPrimeTriviality

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTwoFrequency
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrimeContour570

/-! # Two-frequency bound for the completed-character zero sum -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For a primitive nonprincipal character under GRH, the two-shift cosine
comparison bounds its actual sixth-pole mass plus the real oscillating zero
sum. Each zero carries its divisor multiplicity in the oscillating term. -/
theorem quarter_zero_two_frequency {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hn : χ ≠ 1)
    (hi : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) (b t k : ℝ) :
    let Z := quarterKernel570.oscillatingZeroTerm χ x
    let W := fun (f : ℂ → ℝ) ↦ ∑' ρ : ℂ, ‖Z ρ‖ * Real.cos (f ρ)
    k *
          (W (fun ρ ↦ b * ρ.im) - W (fun ρ ↦ t * ρ.im) + W (fun ρ ↦ (Z ρ).arg - b * ρ.im) -
            W (fun ρ ↦ (Z ρ).arg - t * ρ.im)) -
        k ^ 2 * (quarterMass570 χ - W (fun ρ ↦ (t - b) * ρ.im)) ≤
      quarterMass570 χ + (∑' ρ : ℂ, Z ρ).re := by
  intro Z W
  have hs :=
    LLS.PaperStatements.MellinKernel.summable_oscillatingZeroTerm quarterKernel570 hq hG hp hn hi hx
  have hm : (∑' ρ : ℂ, ‖Z ρ‖) = quarterMass570 χ := by
    apply tsum_congr
    intro ρ
    exact
      (LLS.PaperStatements.MellinKernel.norm_oscillatingZeroTerm quarterKernel570 χ hx ρ).trans
        (kernel_zero_norm_570 hn ρ)
  have hr : W (fun ρ ↦ (Z ρ).arg) = (∑' ρ : ℂ, Z ρ).re := by
    rw [Complex.re_tsum hs]
    exact tsum_congr (fun ρ ↦ Complex.norm_mul_cos_arg (Z ρ))
  have h :=
    two_frequency_tsum_le (fun ρ ↦ ‖Z ρ‖) (fun ρ ↦ (Z ρ).arg) Complex.im (fun ρ ↦ norm_nonneg (Z ρ))
      hs.norm b t k
  dsimp only at h
  rw [← hm, ← hr]
  exact h

/-- Multiplication of the scale by exp(-s) rotates each zero term by
minus s times its ordinate, including terms of zero multiplicity. -/
private theorem zeroTerm_shift {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x)
    (s : ℝ) (ρ : ℂ) :
    quarterKernel570.oscillatingZeroTerm χ (x * Real.exp (-s)) ρ =
      quarterKernel570.oscillatingZeroTerm χ x ρ * Complex.exp ((-(s * ρ.im) : ℝ) * Complex.I) := by
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
theorem shifted_phase_eq_zero_sum {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hn : χ ≠ 1)
    (hi : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) (s : ℝ) :
    let Z := quarterKernel570.oscillatingZeroTerm χ x
    (∑' ρ : ℂ, ‖Z ρ‖ * Real.cos ((Z ρ).arg - s * ρ.im)) =
      (∑' ρ : ℂ, quarterKernel570.oscillatingZeroTerm χ (x * Real.exp (-s)) ρ).re := by
  intro Z
  rw [Complex.re_tsum
      (LLS.PaperStatements.MellinKernel.summable_oscillatingZeroTerm quarterKernel570 hq hG hp hn hi
        (mul_pos hx (Real.exp_pos _)))]
  apply tsum_congr
  intro ρ
  rw [zeroTerm_shift χ hx, Complex.mul_re, Complex.exp_re, Complex.exp_im, Real.cos_sub]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, mul_one, add_zero, Real.exp_zero, one_mul, Real.cos_neg,
    Real.sin_neg]
  change ‖Z ρ‖ * _ = (Z ρ).re * _ - (Z ρ).im * _
  rw [mul_add, ← mul_assoc, Complex.norm_mul_cos_arg, ← mul_assoc, Complex.norm_mul_sin_arg]
  ring

/-- The two-frequency comparison expressed with actual oscillating zero sums
at both shifted cutoffs, ready for the contour explicit formula. -/
theorem quarter_zero_shifted_lower {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hn : χ ≠ 1)
    (hi : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) (b t k : ℝ) :
    let Z := quarterKernel570.oscillatingZeroTerm χ x
    let W := fun (f : ℂ → ℝ) ↦ ∑' ρ : ℂ, ‖Z ρ‖ * Real.cos (f ρ)
    k *
          (W (fun ρ ↦ b * ρ.im) - W (fun ρ ↦ t * ρ.im) +
              (∑' ρ : ℂ, quarterKernel570.oscillatingZeroTerm χ (x * Real.exp (-b)) ρ).re -
            (∑' ρ : ℂ, quarterKernel570.oscillatingZeroTerm χ (x * Real.exp (-t)) ρ).re) -
        k ^ 2 * (quarterMass570 χ - W (fun ρ ↦ (t - b) * ρ.im)) ≤
      quarterMass570 χ + (∑' ρ : ℂ, Z ρ).re := by
  intro Z W
  have h := quarter_zero_two_frequency hq hG hp hn hi hx b t k
  dsimp only at h
  rw [← shifted_phase_eq_zero_sum hq hG hp hn hi hx b, ←
    shifted_phase_eq_zero_sum hq hG hp hn hi hx t]
  exact h

/-- The real oscillating zero sum at a cutoff at least one is the conductor
and Gamma contribution less the reflected integral and the arithmetic sum.
The contour identity retains the sign of the zero sum. -/
theorem zero_re_eq_contour_sub_prime {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hn : χ ≠ 1)
    (hi : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    (∑' ρ : ℂ, quarterKernel570.oscillatingZeroTerm χ x ρ).re =
      contourNonEuler570 χ x - reflectedIntegral570 χ x -
        (∑' n : ℕ, quarterKernel570.summand χ x n).re := by
  have hx0 := zero_lt_one.trans_le hx
  have he := congrArg Complex.re (contour_formula_570 hq hG hp hn hi hx)
  rw [contour_no_residue_570, left_euler_split_570 hp hn hi hx0] at he
  simp only [Complex.add_re, Complex.sub_re, ordinary_re_570, reflected_inv_570 _ hx0] at he
  unfold contourNonEuler570 rightGamma570
  linarith only [he]

/-- Applying the explicit formula at the main cutoff and both shifted cutoffs
bounds the arithmetic sum with the signed two-frequency correction. -/
theorem two_shift_arithmetic_upper {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hn : χ ≠ 1)
    (hi : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) (b t k : ℝ) (hb : 1 ≤ x * Real.exp (-b))
    (ht : 1 ≤ x * Real.exp (-t)) :
    let W := fun s : ℝ ↦
      ∑' ρ : ℂ, ‖quarterKernel570.oscillatingZeroTerm χ x ρ‖ * Real.cos (s * ρ.im)
    let C := fun y : ℝ ↦ contourNonEuler570 χ y - reflectedIntegral570 χ y
    let S := fun y : ℝ ↦ (∑' n : ℕ, quarterKernel570.summand χ y n).re
    S x ≤
      C x + quarterMass570 χ -
          k *
            (W b - W t + (C (x * Real.exp (-b)) - S (x * Real.exp (-b))) -
              (C (x * Real.exp (-t)) - S (x * Real.exp (-t)))) +
        k ^ 2 * (quarterMass570 χ - W (t - b)) := by
  intro W C S
  have h := quarter_zero_shifted_lower hq hG hp hn hi (zero_lt_one.trans_le hx) b t k
  dsimp only at h
  rw [zero_re_eq_contour_sub_prime hq hG hp hn hi hb,
    zero_re_eq_contour_sub_prime hq hG hp hn hi ht,
    zero_re_eq_contour_sub_prime hq hG hp hn hi hx] at h
  dsimp only [W, C, S]
  linarith only [h]

/-- At frequency s ≥ 14/5 the forward sixth-pole prime sum at the shifted
cutoff equals its level-one sum if the character is trivial at primes through X. -/
theorem twoShift_forward_eq_principal {q : ℕ} (χ : DirichletCharacter ℂ q) {X s : ℝ} (hX : 0 < X)
    (hs : 14 / 5 ≤ s) (hp : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ X → χ p = 1) :
    (∑' n : ℕ, quarterKernel570.summand χ (X * Real.exp (-s)) n) =
      ∑' n : ℕ, quarterKernel570.summand (1 : DirichletCharacter ℂ 1) (X * Real.exp (-s)) n := by
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
  have he : Real.exp (2 * (7 / 5 : ℝ)) * (X * Real.exp (-s)) ≤ X := by
    have h := Real.exp_le_one_iff.mpr (show 2 * (7 / 5 : ℝ) + -s ≤ 0 by linarith only [hs])
    rw [Real.exp_add] at h
    linarith only [mul_le_mul_of_nonneg_left h hX.le]
  have hu := (lt_div_iff₀ hx).mpr (he.trans_lt (lt_of_not_ge hcut))
  rw [quarterKernel570,
    LLS.PaperStatements.rationalPole_transform _ _ _ _ ((Real.exp_pos _).trans hu),
    Analysis.rationalPoleProfile_eq_zero _ _ _ hu, Complex.ofReal_zero, mul_zero, mul_zero]

/-- After subtracting the explicit formula at the two shifted cutoffs, both
forward sums are level-one sums. The original character remains only in the
conductor, Gamma and reflected contributions. -/
theorem twoShift_zero_difference {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hprim : χ.IsPrimitive)
    (hn : χ ≠ 1) (hi : χ⁻¹ ≠ 1) {X : ℝ} (hx : 0 < X) (hcut : 1 ≤ X * Real.exp (-3))
    (hp : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ X → χ p = 1) :
    let B := X * Real.exp (-(14 / 5))
    let T := X * Real.exp (-3)
    let Z := fun y : ℝ ↦ (∑' ρ : ℂ, quarterKernel570.oscillatingZeroTerm χ y ρ).re
    let S := fun y : ℝ ↦ (∑' n : ℕ, quarterKernel570.summand (1 : DirichletCharacter ℂ 1) y n).re
    Z B - Z T =
      (contourNonEuler570 χ B - reflectedIntegral570 χ B - S B) -
        (contourNonEuler570 χ T - reflectedIntegral570 χ T - S T) := by
  intro B T Z S
  have hb : 1 ≤ B :=
    hcut.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by norm_num only)) hx.le)
  dsimp only [Z, S, B, T]
  rw [zero_re_eq_contour_sub_prime hq hG hprim hn hi hb,
    zero_re_eq_contour_sub_prime hq hG hprim hn hi hcut,
    twoShift_forward_eq_principal χ hx (le_refl (14 / 5)) hp,
    twoShift_forward_eq_principal χ hx (by norm_num only : (14 / 5 : ℝ) ≤ 3) hp]

/-- For the fixed frequencies 14/5 and 3, the mass plus the real zero sum is bounded
below by the cosine and contour correction with a character-independent forward term. -/
theorem twoShift_zero_contour_lower {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hprim : χ.IsPrimitive)
    (hn : χ ≠ 1) (hi : χ⁻¹ ≠ 1) {X : ℝ} (hx : 0 < X) (hcut : 1 ≤ X * Real.exp (-3))
    (hp : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ X → χ p = 1) :
    let B := X * Real.exp (-(14 / 5))
    let T := X * Real.exp (-3)
    let Z := quarterKernel570.oscillatingZeroTerm χ X
    let W := fun s : ℝ ↦ ∑' ρ : ℂ, ‖Z ρ‖ * Real.cos (s * ρ.im)
    let C := fun y : ℝ ↦ contourNonEuler570 χ y - reflectedIntegral570 χ y
    let S := fun y : ℝ ↦ (∑' n : ℕ, quarterKernel570.summand (1 : DirichletCharacter ℂ 1) y n).re
    (W (14 / 5) - W 3 + (C B - C T) - (S B - S T)) / 2 - (quarterMass570 χ - W (1 / 5)) / 4 ≤
      quarterMass570 χ + (∑' ρ : ℂ, Z ρ).re := by
  intro B T Z W C S
  have ht := quarter_zero_shifted_lower hq hG hprim hn hi hx (14 / 5) 3 (1 / 2)
  have hd := twoShift_zero_difference hq hG hprim hn hi hx hcut hp
  dsimp only at ht hd
  rw [show (3 : ℝ) - 14 / 5 = 1 / 5 by norm_num only] at ht
  dsimp only [B, T, Z, W, C, S]
  linarith only [ht, hd]

/-- Under GRH, the weighted two-frequency comparison for a primitive nonprincipal
character retains both shifted oscillating zero sums and the mixed cosine term.
This supplies the zero-side inequality for section 101. -/
theorem quarter_zero_weighted_lower {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hn : χ ≠ 1)
    (hi : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) (b t u v : ℝ) :
    let Z := quarterKernel570.oscillatingZeroTerm χ x
    let W := fun (f : ℂ → ℝ) ↦ ∑' ρ : ℂ, ‖Z ρ‖ * Real.cos (f ρ)
    u *
            (W (fun ρ ↦ b * ρ.im) +
              (∑' ρ : ℂ, quarterKernel570.oscillatingZeroTerm χ (x * Real.exp (-b)) ρ).re) -
          v *
            (W (fun ρ ↦ t * ρ.im) +
              (∑' ρ : ℂ, quarterKernel570.oscillatingZeroTerm χ (x * Real.exp (-t)) ρ).re) -
          ((u ^ 2 + v ^ 2) / 2) * quarterMass570 χ +
        (u * v) * W (fun ρ ↦ (t - b) * ρ.im) ≤
      quarterMass570 χ + (∑' ρ : ℂ, Z ρ).re := by
  intro Z W
  have hs :=
    LLS.PaperStatements.MellinKernel.summable_oscillatingZeroTerm quarterKernel570 hq hG hp hn hi hx
  have hm : (∑' ρ : ℂ, ‖Z ρ‖) = quarterMass570 χ := by
    apply tsum_congr
    intro ρ
    exact
      (LLS.PaperStatements.MellinKernel.norm_oscillatingZeroTerm quarterKernel570 χ hx ρ).trans
        (kernel_zero_norm_570 hn ρ)
  have hr : W (fun ρ ↦ (Z ρ).arg) = (∑' ρ : ℂ, Z ρ).re := by
    rw [Complex.re_tsum hs]
    exact tsum_congr (fun ρ ↦ Complex.norm_mul_cos_arg (Z ρ))
  have h :=
    two_frequency_weighted_tsum (fun ρ ↦ ‖Z ρ‖) (fun ρ ↦ (Z ρ).arg) Complex.im
      (fun ρ ↦ norm_nonneg (Z ρ)) hs.norm b t u v
  dsimp only at h
  rw [← hm, ← hr]
  rw [← shifted_phase_eq_zero_sum hq hG hp hn hi hx b, ←
    shifted_phase_eq_zero_sum hq hG hp hn hi hx t]
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
