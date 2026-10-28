/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.JacobiSquareFactorBudget
public import PseudoPrime.LLS.FiniteExcludedTaperSavings
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ConductorSquareFactorCost

/-! # Exclusion costs with coupled conductor and square-factor rates -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

open AnalyticNumberTheory.Arithmetic in
/-- For an odd nonsquare bridge, nonnegative rates a,b and finite excesses,
the untapered structural exclusion budget is at most its two-adic cost plus
b log n+(a-b)log d and excesses. Charge conductor primes at rate a and the
other input primes at rate 2b before using the exact square decomposition.
This retains different conductor and square-factor costs for witness separation. -/
theorem untaperedBudget_le_conductor_square_rates {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) {x a b : ℝ} (hx : 0 ≤ x)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (T : Finset ℕ) (e : ℕ → ℝ) (he : ∀ p ∈ T, 0 ≤ e p)
    (hR :
      ∀ p ∈ n.primeFactors,
        p ∣ (NumberTheory.complexQuadraticCharacter n hn).conductor →
          quadraticExcludedPrimeCost (NumberTheory.complexQuadraticCharacter n hn).conductor x
              (untaperedExcludedEndpointWeight x) p ≤
            a * Real.log p + if p ∈ T then e p else 0)
    (hE :
      ∀ p ∈ n.primeFactors,
        ¬p ∣ (NumberTheory.complexQuadraticCharacter n hn).conductor →
          quadraticExcludedPrimeCost (NumberTheory.complexQuadraticCharacter n hn).conductor x
              (untaperedExcludedEndpointWeight x) p ≤
            2 * b * Real.log p + if p ∈ T then e p else 0) :
    quadraticExcludedBudget (NumberTheory.complexQuadraticCharacter n hn).conductor (4 * n)
        (Finset.Ioc 0 ⌊x⌋₊) (untaperedExcludedEndpointWeight x) ≤
      quadraticExcludedPrimeCost (NumberTheory.complexQuadraticCharacter n hn).conductor x
          (untaperedExcludedEndpointWeight x) 2 +
        b * Real.log n +
        (a - b) * Real.log bridge.squarefreePart +
        ∑ p ∈ T, e p := by
  have hcost :=
    bridge.sum_prime_cost_le_conductor_square_budget
      (quadraticExcludedPrimeCost (NumberTheory.complexQuadraticCharacter n hn).conductor x
        (untaperedExcludedEndpointWeight x))
      ha hb T e he hR hE
  rw [quadraticExcludedBudget_four_mul_eq_two_add hn _ hx _
      (fun _ hm ↦ untaperedExcludedEndpointWeight_eq_zero_of_not_primePow x hm)]
  linarith only [hcost]

open AnalyticNumberTheory.Arithmetic in
/-- The coupled untapered exclusion bound for an odd nonsquare bridge:
the cost at two plus b log n+(a-b)log d and a finite excess sum. The real rates
and excess weights are arbitrary in this definition; the bound theorem requires
nonnegative rates and certified local costs. Used in negative-witness separation. -/
noncomputable def conductorSquareUntaperedBudget {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) (x a b : ℝ) (T : Finset ℕ)
    (e : ℕ → ℝ) : ℝ :=
  quadraticExcludedPrimeCost (NumberTheory.complexQuadraticCharacter n hn).conductor x
      (untaperedExcludedEndpointWeight x) 2 +
    b * Real.log n +
    (a - b) * Real.log bridge.squarefreePart +
    ∑ p ∈ T, e p

/-- The coefficient of log conductor in the equal-cutoff endpoint limit.
It is positive at x>1 and independent of the exclusion costs. This quantifies
the analytic gain from removing a square factor from the original input. -/
noncomputable def equalEndpointLevelCoefficient (x : ℝ) : ℝ :=
  (2 + (Real.log x + 2) / Real.sqrt x) * ((1 / 2 : ℝ) * (1 - 1 / x) / (1 - 1 / Real.sqrt x) ^ 2) +
    Real.log x / (2 * Real.sqrt x)

/-- For arbitrary levels and cutoff, the difference of zero-cost endpoint
limits equals the conductor-log difference times the explicit level coefficient.
Expand the affine mass cap and collect factors; totalized division causes no restriction. -/
theorem equalEndpoint_level_difference (q Q : ℕ) (x : ℝ) :
    oddEndpointTwoCostLimit q x x 0 0 - oddEndpointTwoCostLimit Q x x 0 0 =
      equalEndpointLevelCoefficient x * (Real.log q - Real.log Q) := by
  dsimp only [oddEndpointTwoCostLimit, oddEndpointCostLimit, reciprocalGapFullEndpointLimit,
    reciprocalGapReciprocalMassCap, equalEndpointLevelCoefficient]
  simp only [div_eq_mul_inv]
  ring

/-- At x>1 the equal-cutoff level coefficient is positive. Its first product
is positive and its remaining logarithmic term is nonnegative. This makes a
strict conductor reduction a strict improvement of endpoint separation. -/
theorem equalEndpointLevelCoefficient_pos {x : ℝ} (hx : 1 < x) :
    0 < equalEndpointLevelCoefficient x := by
  have he :
    equalEndpointLevelCoefficient x =
      excludedReciprocalCoefficient x * ((1 / 2 : ℝ) * (1 - 1 / x)) +
        Real.log x / (2 * Real.sqrt x) := by
    dsimp only [equalEndpointLevelCoefficient, excludedReciprocalCoefficient]
    ring
  rw [he]
  have hi : 0 < 1 - 1 / x := sub_pos.mpr (by simpa only [one_div] using inv_lt_one_of_one_lt₀ hx)
  exact
    add_pos_of_pos_of_nonneg
      (mul_pos (excludedReciprocalCoefficient_pos hx) (mul_pos (by norm_num only) hi))
      (div_nonneg (Real.log_nonneg hx.le) (mul_nonneg (by norm_num only) (Real.sqrt_nonneg x)))

/-- For n=s^2*d with nonzero factors, the zero-cost endpoint gain from level
4n to 4d is exactly twice the level coefficient times log s. Use the affine
level identity and the exact input logarithm decomposition. -/
theorem equalEndpoint_square_factor_gain {n d s : ℕ} (hd : d ≠ 0) (hs : s ≠ 0)
    (hdec : s ^ 2 * d = n) (x : ℝ) :
    oddEndpointTwoCostLimit (4 * n) x x 0 0 - oddEndpointTwoCostLimit (4 * d) x x 0 0 =
      2 * equalEndpointLevelCoefficient x * Real.log s := by
  have hn : n ≠ 0 := hdec ▸ Nat.mul_ne_zero (pow_ne_zero 2 hs) hd
  have h1 : Real.log (4 * n : ℕ) = Real.log (4 : ℝ) + Real.log n := by
    rw [Nat.cast_mul, Nat.cast_ofNat,
      Real.log_mul (by norm_num only : (4 : ℝ) ≠ 0) (Nat.cast_ne_zero.mpr hn)]
  have h2 : Real.log (4 * d : ℕ) = Real.log (4 : ℝ) + Real.log d := by
    rw [Nat.cast_mul, Nat.cast_ofNat,
      Real.log_mul (by norm_num only : (4 : ℝ) ≠ 0) (Nat.cast_ne_zero.mpr hd)]
  rw [equalEndpoint_level_difference, h1, h2,
    AnalyticNumberTheory.Arithmetic.log_square_factor_decomposition hd hs hdec]
  ring

open AnalyticNumberTheory.Arithmetic in
/-- The gain in the complete retained-taper comparison is exactly
2*(levelCoefficient+a-b)*log s. Compare the coupled 4d cost with the 4n
comparison charging every input prime at rate a. The two-adic cost, finite
excesses and taper saving are kept identical in both expressions. -/
theorem conductorSquare_comparison_gain {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) (x a b : ℝ) (T : Finset ℕ)
    (e : ℕ → ℝ) :
    (oddEndpointTwoCostLimit (4 * n) x x 0 0 +
            quadraticExcludedPrimeCost (NumberTheory.complexQuadraticCharacter n hn).conductor x
              (untaperedExcludedEndpointWeight x) 2 +
            a * Real.log n +
            ∑ p ∈ T, e p -
          (excludedReciprocalCoefficient x / x) * Real.log 2) -
        (oddEndpointTwoCostLimit (4 * bridge.squarefreePart) x x 0 0 +
            conductorSquareUntaperedBudget bridge x a b T e -
          (excludedReciprocalCoefficient x / x) * Real.log 2) =
      2 * (equalEndpointLevelCoefficient x + a - b) * Real.log bridge.squareFactor := by
  have hg :=
    equalEndpoint_square_factor_gain bridge.squarefreePart_pos.ne' bridge.squareFactor_pos.ne'
      bridge.squarefreePart_sq_mul x
  have hl :=
    log_square_factor_decomposition bridge.squarefreePart_pos.ne' bridge.squareFactor_pos.ne'
      bridge.squarefreePart_sq_mul
  dsimp only [conductorSquareUntaperedBudget]
  linear_combination hg + (a - b) * hl

open AnalyticNumberTheory.Arithmetic in
/-- For x>1, a>=b and square factor s>1, the coupled comparison is strictly
smaller than the 4n comparison with the same two-adic and excess costs at rate a.
The exact gain is positive. This comparison does not claim domination of all
published bounds or discharge the local cost-rate hypotheses. -/
theorem conductorSquare_comparison_lt {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) {x a b : ℝ} (hx : 1 < x)
    (hab : b ≤ a) (hs : 1 < bridge.squareFactor) (T : Finset ℕ) (e : ℕ → ℝ) :
    oddEndpointTwoCostLimit (4 * bridge.squarefreePart) x x 0 0 +
          conductorSquareUntaperedBudget bridge x a b T e -
        (excludedReciprocalCoefficient x / x) * Real.log 2 <
      oddEndpointTwoCostLimit (4 * n) x x 0 0 +
          quadraticExcludedPrimeCost (NumberTheory.complexQuadraticCharacter n hn).conductor x
            (untaperedExcludedEndpointWeight x) 2 +
          a * Real.log n +
          ∑ p ∈ T, e p -
        (excludedReciprocalCoefficient x / x) * Real.log 2 := by
  have hg := conductorSquare_comparison_gain bridge x a b T e
  have hk := equalEndpointLevelCoefficient_pos hx
  have hl : 0 < Real.log bridge.squareFactor := Real.log_pos (Nat.one_lt_cast.mpr hs)
  have hp : 0 < 2 * (equalEndpointLevelCoefficient x + a - b) * Real.log bridge.squareFactor :=
    mul_pos (mul_pos (by norm_num only) (by linarith only [hk, hab])) hl
  linarith only [hg, hp]

open AnalyticNumberTheory.Arithmetic in
/-- If a>=b, the coupled untapered budget is at most the uniform rate-a
input bound with the same cost at two and the same finite excesses. The exact
logarithm decomposition and log s>=0 prove this without an analytic hypothesis.
Thus the comparison baseline is also a valid upper bound under the local rates. -/
theorem conductorSquareUntaperedBudget_le_uniform {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) (x a b : ℝ) (hab : b ≤ a)
    (T : Finset ℕ) (e : ℕ → ℝ) :
    conductorSquareUntaperedBudget bridge x a b T e ≤
      quadraticExcludedPrimeCost (NumberTheory.complexQuadraticCharacter n hn).conductor x
          (untaperedExcludedEndpointWeight x) 2 +
        a * Real.log n +
        ∑ p ∈ T, e p := by
  have hl :=
    log_square_factor_decomposition bridge.squarefreePart_pos.ne' bridge.squareFactor_pos.ne'
      bridge.squarefreePart_sq_mul
  have hs : 0 ≤ Real.log bridge.squareFactor :=
    Real.log_nonneg (Nat.one_le_cast.mpr (Nat.succ_le_of_lt bridge.squareFactor_pos))
  have hm := mul_nonneg (sub_nonneg.mpr hab) hs
  dsimp only [conductorSquareUntaperedBudget]
  rw [hl]
  nlinarith only [hm]

end PseudoPrime.LLS.PaperStatements
