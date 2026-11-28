/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipal632
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPowerGrowth632
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPsiBoundary632
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipal600
import PseudoPrime.Analysis.NumericalLogBounds

/-! # Arithmetic lower bound for radii 313 through 316 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The positive cutoff-boundary term is bounded below on the full radius
interval by evaluating its reciprocal-radius factor at 316. -/
private theorem principal_log_boundary632 {r : ℝ} (hr : r ∈ Set.Icc 313 316) :
    0.002116 ≤ 4 * quarterWeight570 (r ^ 2) (r ^ 2) * Real.log (2 * Real.pi) := by
  have hp : 0 < r := by linarith only [hr.1]
  have hw : 0.09104 ≤ (quarterKernel570.transform 1).re := by
    linarith only [quarter_unit_weight_570.1]
  have h := mul_le_mul hw Analysis.log_two_mul_pi_gt.le (by norm_num only) (by linarith only [hw])
  rw [quarter_cutoff_weight_570 (sq_pos_of_pos hp), Real.sqrt_sq hp.le]
  rw [show
      4 * ((quarterKernel570.transform 1).re / r) * Real.log (2 * Real.pi) =
        (4 * (quarterKernel570.transform 1).re * Real.log (2 * Real.pi)) / r
      by ring]
  apply (le_div_iff₀ hp).mpr
  linarith only [h, hr.2]

/-- The signed principal boundary can be evaluated at the appropriate
endpoint of each of the five comparison intervals. -/
private theorem signed_boundary632 {r : ℝ} (hr : r ∈ Set.Icc 313 316) :
    (if r ≤ 1568 / 5 then 4 * 0.09105 * (-28.592) / 313
      else
        if r ≤ 314 then 4 * 0.09105 * (-20.120) / (1568 / 5)
        else
          if r ≤ 6289 / 20 then 4 * 0.09105 * (-23.6745) / 314
          else
            if r ≤ 315 then 4 * 0.09105 * (-9.170) / (6289 / 20) else 4 * 0.09104 * 10.585 / 316) ≤
      4 * quarterWeight570 (r ^ 2) (r ^ 2) * (Chebyshev.psi (r ^ 2) - r ^ 2) := by
  by_cases h₁ : r ≤ 1568 / 5
  · rw [ite_eq_left h₁]
    exact quarter_psi_boundary_3136 hr.1 h₁
  rw [ite_eq_right h₁]
  by_cases h₂ : r ≤ 314
  · rw [ite_eq_left h₂]
    exact quarter_psi_boundary_314 (le_of_not_ge h₁) h₂
  rw [ite_eq_right h₂]
  by_cases h₃ : r ≤ 6289 / 20
  · rw [ite_eq_left h₃]
    exact quarter_psi_boundary_31445 (le_of_not_ge h₂) h₃
  rw [ite_eq_right h₃]
  by_cases h₄ : r ≤ 315
  · rw [ite_eq_left h₄]
    exact quarter_psi_boundary_315 (le_of_not_ge h₃) h₄
  rw [ite_eq_right h₄]
  exact quarter_psi_boundary_316 (le_of_not_ge h₄) hr.2

/-- The radius-dependent additive arithmetic term, excluding the lower-end
logarithmic weight, includes the principal error, signed boundary, and
fixed prime-power gain. -/
@[expose]
noncomputable def quarterArithmeticTerm632 (r : ℝ) : ℝ :=
  0.002116 + 0.1448 +
    (if r ≤ 1568 / 5 then -0.008176 + 4 * 0.09105 * (-28.592) / 313
    else
      if r ≤ 314 then -0.007866 + 4 * 0.09105 * (-20.120) / (1568 / 5)
      else
        if r ≤ 6289 / 20 then -0.007706 + 4 * 0.09105 * (-23.6745) / 314
        else
          if r ≤ 315 then -0.007546 + 4 * 0.09105 * (-9.170) / (6289 / 20)
          else -0.007446 + 4 * 0.09104 * 10.585 / 316)

/-- The arithmetic comparison retains the extra radius-dependent prime-power recovery. -/
theorem quarter_arithmetic_growth_632 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    (hRH : RiemannHypothesis) (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q)
    (c : DirichletCharacter ℂ s) {r : ℝ} (hr : r ∈ Set.Icc 313 316)
    (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) :
    let X := r ^ 2
    0.717289 * r + quarterArithmeticTerm632 r + 0.1448 * 1.53 * ((r - 313) / 316) -
        3 * Real.log (2 * Real.pi) * quarterWeight570 X 1 <
      (∑' k : ℕ, quarterKernel570.summand a X k).re +
        (∑' k : ℕ, quarterKernel570.summand b X k).re +
        (∑' k : ℕ, quarterKernel570.summand c X k).re := by
  dsimp only
  have hx := one_le_pow₀ (show 1 ≤ r by linarith only [hr.1]) (n := 2)
  have h := quarter_centered_difference_570 hx
  have hi := integral_difference_exact ((by norm_num only : (292 : ℝ) ≤ 313).trans hr.1)
  have he := principal_error_lower_632 hRH hr
  have hp := signed_boundary632 hr
  have hf := fixed_arithmetic_lower_632 a b c hr ht hA hB hC
  have hlog := principal_log_boundary632 hr
  have hg := fixed_power_gain_growth_632 hr
  dsimp only at h hi hf
  unfold section99PrincipalError section99PrincipalRemainder at he
  rw [←
    Complex.re_tsum
      (quarterKernel570.summable_summand (1 : DirichletCharacter ℂ 1)
        (zero_lt_one.trans_le hx))] at h
  unfold quarterArithmeticTerm632
  split_ifs at he hp ⊢ <;> linarith only [h, hi, he, hp, hf, hlog, hg]

/-- Under RH, passing pair characters have the stated arithmetic lower
bound on radii 313 to 316. The selected prime powers are used once, and the
five principal and signed-boundary estimates are evaluated together. -/
theorem quarter_arithmetic_lower_632 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    (hRH : RiemannHypothesis) (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q)
    (c : DirichletCharacter ℂ s) {r : ℝ} (hr : r ∈ Set.Icc 313 316)
    (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) :
    let X := r ^ 2
    0.717289 * r + quarterArithmeticTerm632 r - 3 * Real.log (2 * Real.pi) * quarterWeight570 X 1 <
      (∑' k : ℕ, quarterKernel570.summand a X k).re +
        (∑' k : ℕ, quarterKernel570.summand b X k).re +
        (∑' k : ℕ, quarterKernel570.summand c X k).re := by
  have h := quarter_arithmetic_growth_632 hRH a b c hr ht hA hB hC
  dsimp only at h ⊢
  linarith only [h, hr.1]

end PseudoPrime.PrimeTestBounds.MillerRabin
