/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.QuadraticBudgetLinear

/-! # Finite reciprocal taper savings in negative-prime exclusion budgets -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The positive reciprocal mass multiplier in the equal-cutoff endpoint
weight. Inputs are totalized; positivity is proved at x>1. This coefficient
converts a retained Mangoldt contribution into an endpoint saving. -/
noncomputable def excludedReciprocalCoefficient (x : ℝ) : ℝ :=
  (2 + (Real.log x + 2) / Real.sqrt x) / (1 - 1 / Real.sqrt x) ^ 2

/-- The endpoint exclusion weight before reciprocal taper subtraction.
Replace Lambda(n)/n*(1-n/x) by Lambda(n)/n and keep the logarithmic term.
An upper estimate for this weight can retain the finite taper saving separately. -/
noncomputable def untaperedExcludedEndpointWeight (x : ℝ) (n : ℕ) : ℝ :=
  excludedReciprocalCoefficient x * (ArithmeticFunction.vonMangoldt n / n) +
    (1 / Real.sqrt x) * AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm x n

/-- At x>1 the reciprocal coefficient is positive. Its numerator is positive
and the square denominator is nonzero. This makes retained prime contributions
strictly improve the endpoint comparison. -/
theorem excludedReciprocalCoefficient_pos {x : ℝ} (hx : 1 < x) :
    0 < excludedReciprocalCoefficient x := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hs : 1 < Real.sqrt x := by nlinarith only [Real.sq_sqrt hx0.le, Real.sqrt_nonneg x, hx]
  have hd : 0 < 1 - 1 / Real.sqrt x :=
    sub_pos.mpr (by simpa only [one_div] using inv_lt_one_of_one_lt₀ hs)
  have hn : 0 < 2 + (Real.log x + 2) / Real.sqrt x :=
    lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 2)
      (le_add_of_nonneg_right
        (div_nonneg (by linarith only [Real.log_nonneg hx.le]) (Real.sqrt_nonneg x)))
  exact div_pos hn (sq_pos_of_pos hd)

/-- For positive n and arbitrary cutoff, the actual endpoint weight equals
its untapered weight minus coefficient/x times Lambda(n). Cancel the nonzero
natural index before collecting factors. This retains all excluded prime powers. -/
theorem excludedEndpointWeight_eq_untapered_sub (x : ℝ) {n : ℕ} (hn : 0 < n) :
    excludedEndpointWeight x n =
      untaperedExcludedEndpointWeight x n -
        (excludedReciprocalCoefficient x / x) * ArithmeticFunction.vonMangoldt n := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have he :
    ArithmeticFunction.vonMangoldt n / n * (1 - (n : ℝ) / x) =
      ArithmeticFunction.vonMangoldt n / n - ArithmeticFunction.vonMangoldt n / x := by
    rw [mul_sub, mul_one, ← mul_div_assoc, div_mul_cancel₀ _ hn0]
  dsimp only [excludedEndpointWeight, untaperedExcludedEndpointWeight,
    excludedReciprocalCoefficient, AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtTerm]
  rw [he]
  ring

open AnalyticNumberTheory.Arithmetic in
/-- For every level, exclusion modulus and cutoff, the structural endpoint
budget equals the untapered budget minus the same multiplier times its Mangoldt
budget. Apply weight linearity on positive indices. This identity keeps every
finite prime-power saving rather than only a uniform lower contribution. -/
theorem quadraticEndpointBudget_eq_untapered_sub (q N : ℕ) (x : ℝ) :
    quadraticExcludedBudget q N (Finset.Ioc 0 ⌊x⌋₊) (excludedEndpointWeight x) =
      quadraticExcludedBudget q N (Finset.Ioc 0 ⌊x⌋₊) (untaperedExcludedEndpointWeight x) -
        (excludedReciprocalCoefficient x / x) *
          quadraticExcludedBudget q N (Finset.Ioc 0 ⌊x⌋₊) ArithmeticFunction.vonMangoldt := by
  have he :
    quadraticExcludedBudget q N (Finset.Ioc 0 ⌊x⌋₊) (excludedEndpointWeight x) =
      quadraticExcludedBudget q N (Finset.Ioc 0 ⌊x⌋₊)
        (fun n ↦
          1 * untaperedExcludedEndpointWeight x n +
            (-(excludedReciprocalCoefficient x / x)) * ArithmeticFunction.vonMangoldt n) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [excludedEndpointWeight_eq_untapered_sub x (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).1]
    ring
  rw [he, quadraticExcludedBudget_linear_weight]
  ring

open AnalyticNumberTheory.Arithmetic in
/-- For even N and x>=2, an upper bound C on the untapered budget gives an
upper bound C-coefficient*log 2/x on the actual endpoint budget. Retain the
excluded prime two, whose structural Mangoldt contribution is at least log 2.
No character or finite input enumeration is needed in this arithmetic estimate. -/
theorem quadraticEndpointBudget_le_sub_log_two (q : ℕ) {N : ℕ} (hN2 : 2 ∣ N) {x C : ℝ} (hx : 2 ≤ x)
    (hC : quadraticExcludedBudget q N (Finset.Ioc 0 ⌊x⌋₊) (untaperedExcludedEndpointWeight x) ≤ C) :
    quadraticExcludedBudget q N (Finset.Ioc 0 ⌊x⌋₊) (excludedEndpointWeight x) ≤
      C - (excludedReciprocalCoefficient x / x) * Real.log 2 := by
  have hmem : 2 ∈ Finset.Ioc 0 ⌊x⌋₊ := Finset.mem_Ioc.mpr ⟨by norm_num only, Nat.le_floor hx⟩
  have hm := log_prime_le_quadraticExcludedBudget Nat.prime_two q N (Finset.Ioc 0 ⌊x⌋₊) hmem hN2
  have hk :=
    div_nonneg (excludedReciprocalCoefficient_pos (by linarith only [hx] : 1 < x)).le
      (by linarith only [hx] : 0 ≤ x)
  have hs := mul_le_mul_of_nonneg_left hm hk
  rw [quadraticEndpointBudget_eq_untapered_sub]
  linarith only [hs, hC]

/-- At x>1 the retained-taper scalar comparison is strictly smaller than
the comparison which only uses the untapered budget C. Positivity of the
coefficient and log two gives the strict saving at every such cutoff. -/
theorem finiteExcludedTaper_comparison_lt (q : ℕ) {x : ℝ} (hx : 1 < x) (C : ℝ) :
    oddEndpointTwoCostLimit q x x 0 0 + C - (excludedReciprocalCoefficient x / x) * Real.log 2 <
      oddEndpointTwoCostLimit q x x 0 0 + C := by
  exact
    sub_lt_self _
      (mul_pos (div_pos (excludedReciprocalCoefficient_pos hx) (zero_lt_one.trans hx))
        (Real.log_pos (by norm_num only : (1 : ℝ) < 2)))

open AnalyticNumberTheory.Arithmetic in
/-- Under primitive nonprincipal quadratic GRH data, q dividing even N and
x>=64, an untapered budget bound C and the improved scalar separation give
an odd N-coprime negative prime. Insert the retained-taper arithmetic bound
into the existing exact quadratic exclusion witness theorem. -/
theorem exists_prime_neg_one_of_finite_excluded_taper {q N : ℕ} [NeZero q] (hq : 2 ≤ q)
    (hqN : q ∣ N) (hN2 : 2 ∣ N) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hquad : χ.IsQuadratic) {x C : ℝ} (hx : 64 ≤ x)
    (hC : quadraticExcludedBudget q N (Finset.Ioc 0 ⌊x⌋₊) (untaperedExcludedEndpointWeight x) ≤ C)
    (hsep :
      oddEndpointTwoCostLimit q x x 0 0 + C - (excludedReciprocalCoefficient x / x) * Real.log 2 <
        0) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ x ∧ Nat.Coprime p N ∧ χ p = -1 := by
  have hb := quadraticEndpointBudget_le_sub_log_two q hN2 (by linarith only [hx] : 2 ≤ x) hC
  apply exists_odd_prime_neg_one_of_quadratic_excluded_budget hq hqN hN2 hGRH hp hne hquad hx
  linarith only [hb, hsep]

/-- Off prime powers, the untapered endpoint weight vanishes. Both Mangoldt
terms vanish. This supplies the support condition for the generic prime-factor
budget and keeps certification in the prime variable rather than in input moduli. -/
theorem untaperedExcludedEndpointWeight_eq_zero_of_not_primePow (x : ℝ) {n : ℕ}
    (hn : ¬IsPrimePow n) : untaperedExcludedEndpointWeight x n = 0 := by
  dsimp only [untaperedExcludedEndpointWeight]
  rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn,
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm_eq_zero_of_not_primePow hn]
  simp only [zero_div, mul_zero, add_zero]

open AnalyticNumberTheory.Arithmetic in
/-- For primitive nonprincipal quadratic GRH data, q dividing nonzero even N,
x>=64 and a nonnegative logarithmic tail rate, a prime-budget upper bound on
the untapered weight with the retained log-two saving yields an odd negative
N-coprime prime. Apply the generic prime-factor budget before subtracting the
finite taper contribution. Tail and exceptional costs remain explicit obligations. -/
theorem exists_prime_neg_one_of_finite_taper_prime_budget {q N : ℕ} [NeZero q] (hq : 2 ≤ q)
    (hN : N ≠ 0) (hqN : q ∣ N) (hN2 : 2 ∣ N) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hquad : χ.IsQuadratic) {x : ℝ} (hx : 64 ≤ x) (T : Finset ℕ) {a : ℝ} (ha : 0 ≤ a)
    (htail :
      ∀ p ∈ N.primeFactors,
        p ∉ T →
          quadraticExcludedPrimeCost q x (untaperedExcludedEndpointWeight x) p ≤ a * Real.log p)
    (hsep :
      oddEndpointTwoCostLimit q x x 0 0 + a * Real.log N +
            ∑ p ∈ T,
              max 0
                (quadraticExcludedPrimeCost q x (untaperedExcludedEndpointWeight x) p -
                  a * Real.log p) -
          (excludedReciprocalCoefficient x / x) * Real.log 2 <
        0) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ x ∧ Nat.Coprime p N ∧ χ p = -1 := by
  have hb :=
    quadraticExcludedBudget_le_primeBudget hN q (by linarith only [hx] : 0 ≤ x)
      (untaperedExcludedEndpointWeight x)
      (fun _ hn ↦ untaperedExcludedEndpointWeight_eq_zero_of_not_primePow x hn) T ha htail
  exact
    exists_prime_neg_one_of_finite_excluded_taper hq hqN hN2 hGRH hp hne hquad hx hb
      (by linarith only [hsep])

open AnalyticNumberTheory.Arithmetic in
/-- Under primitive nonprincipal quadratic GRH data and x>=64, an upper
untapered budget C and any lower structural Mangoldt budget m yield an odd
negative N-coprime prime when their retained-taper separation is negative.
Use the exact budget identity and coefficient positivity. Taking m equal to
the full Mangoldt budget retains every excluded prime-power contribution. -/
theorem exists_prime_neg_one_of_finite_taper_mangoldt_budget {q N : ℕ} [NeZero q] (hq : 2 ≤ q)
    (hqN : q ∣ N) (hN2 : 2 ∣ N) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hquad : χ.IsQuadratic) {x C m : ℝ} (hx : 64 ≤ x)
    (hC : quadraticExcludedBudget q N (Finset.Ioc 0 ⌊x⌋₊) (untaperedExcludedEndpointWeight x) ≤ C)
    (hm : m ≤ quadraticExcludedBudget q N (Finset.Ioc 0 ⌊x⌋₊) ArithmeticFunction.vonMangoldt)
    (hsep : oddEndpointTwoCostLimit q x x 0 0 + C - (excludedReciprocalCoefficient x / x) * m < 0) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ x ∧ Nat.Coprime p N ∧ χ p = -1 := by
  have hx1 : 1 < x := by linarith only [hx]
  have hs :=
    mul_le_mul_of_nonneg_left hm
      (div_nonneg (excludedReciprocalCoefficient_pos hx1).le (zero_lt_one.trans hx1).le)
  apply exists_odd_prime_neg_one_of_quadratic_excluded_budget hq hqN hN2 hGRH hp hne hquad hx
  rw [quadraticEndpointBudget_eq_untapered_sub]
  linarith only [hs, hC, hsep]

end PseudoPrime.LLS.PaperStatements
