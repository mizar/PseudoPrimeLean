/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PreciseSavingTheorem11S1
public import PseudoPrime.LLS.PreciseSavingPrime31
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ElementaryOmegaFiniteCertificates

/-! # Factor-independent majorants for the selected precise-saving root

The first root uses only nonnegative reciprocal saving. The second retains that saving
through the certified cutoff-thirty-one prime-support bound. Both branches of each
nonnegative-part maximum are bounded explicitly; no activity condition is assumed.
The original-level factor-count estimate is supplied by its existing unconditional
arithmetic proof, which is imported directly rather than exposed as a new assumption.
-/

@[expose] public section

namespace PseudoPrime.LLS

/-- The factor-independent elementary root with the selected precise reciprocal constant.
Input: an original natural level. Output: log(q)+(24/5)loglog(q)+7031/5000.
Role: a cumulative majorant that improves the former additive constant two. -/
noncomputable def preciseElementaryRoot (q : ℕ) : ℝ :=
  Real.log q + (24 / 5 : ℝ) * Real.log (Real.log q) + 7031 / 5000

/-- The factor-independent root retaining the selected small-prime saving at cutoff thirty-one.
Input: an original natural level. Output: (33/31)log(q)+(4/5)loglog(q)+18327/2000.
Role: preserve saving without factorizing every input in a cumulative witness maximum. -/
noncomputable def prime31SavingRoot (q : ℕ) : ℝ :=
  (33 / 31 : ℝ) * Real.log q + (4 / 5 : ℝ) * Real.log (Real.log q) + 18327 / 2000

/-- The existing unconditional arithmetic theorem bounds the original-level factor-count cost.
Input: an odd input at least 750. Claim: the precise-saving count term is at most (14/5)loglog.
Proof: use the completed elementary omega proof and normalize its character modulus.
Role: pay the original level cost internally in both selected root majorants. -/
theorem preciseSaving_factor_cost {n : ℕ} (hn : Odd n) (hn750 : 750 ≤ n) :
    2 * (4 * n).primeFactors.card * Real.log (Real.log (4 * n : ℕ)) ^ 2 / Real.log (4 * n : ℕ) ≤
      (14 / 5 : ℝ) * Real.log (Real.log (4 * n : ℕ)) := by
  have hc :=
    AnalyticNumberTheory.Arithmetic.elementary_prime_count_term_le
      AnalyticNumberTheory.Arithmetic.elementaryOmegaStatement hn hn750
  norm_num only [NumberTheory.characterModulus,
    AnalyticNumberTheory.Arithmetic.elementaryOmegaConstant] at hc
  exact hc

/-- The certified cutoff-thirty-one constant bounds every nonzero level's reciprocal factor sum.
Input: a nonzero natural level. Claim: its factor sum is at most log(q)/31+2.3011.
Proof: apply the arbitrary-cutoff support theorem and the eleven-log numerical certificate.
Role: retain the reciprocal saving when deriving the selected factor-independent root. -/
theorem primeFactorLogSum_le_prime31 {q : ℕ} (hq : q ≠ 0) :
    AnalyticNumberTheory.Arithmetic.primeFactorLogSum q ≤
      Real.log q / 31 + (23011 / 10000 : ℝ) := by
  exact
    (NumberTheory.sum_primeFactor_log_div_le (P := 31) hq (by norm_num only : (1 : ℕ) < 31)).trans
      (add_le_add (le_refl _) prime31_log_constant_lt.le)

/-- The precise-saving root is bounded by the improved elementary root at quadratic levels.
Input: an odd input at least 750. Claim: the factor-independent majorant covers the actual cutoff.
Proof: use nonnegative saving and the unconditional count cost, including the zero max branch.
Role: derive the first uniform cumulative candidate without changing the actual-prime contract. -/
theorem preciseSavingRoot_le_elementary {n : ℕ} (hn : Odd n) (hn750 : 750 ≤ n) :
    preciseSavingRadiusRoot (4 * n) ≤ preciseElementaryRoot (4 * n) := by
  have hq : 3000 ≤ 4 * n := Nat.mul_le_mul_left 4 hn750
  have hy := (AnalyticNumberTheory.Arithmetic.log_log_pos_of_le hq).2
  have hw := preciseSaving_factor_cost hn hn750
  have ha : 0 ≤ preciseSavingAuxiliary (4 * n) := le_max_left _ _
  have hc :
    preciseSavingCorrectionTerm (4 * n) ≤
      (24 / 5 : ℝ) * Real.log (Real.log (4 * n : ℕ)) + 7031 / 5000 := by
    dsimp only [preciseSavingCorrectionTerm]
    exact max_le (by linarith only [hy]) (by linarith only [hw, ha])
  dsimp only [preciseSavingRadiusRoot, preciseElementaryRoot]
  linarith only [hc]

/-- The precise-saving root is also bounded by the root retaining the cutoff-thirty-one saving.
Input: an odd input at least 750. Claim: the second root covers the actual cutoff.
Proof: bound the auxiliary saving from below and the factor sum from above, then check
both branches of the outer maximum. Role: the selected R31 cumulative witness candidate. -/
theorem preciseSavingRoot_le_prime31 {n : ℕ} (hn : Odd n) (hn750 : 750 ≤ n) :
    preciseSavingRadiusRoot (4 * n) ≤ prime31SavingRoot (4 * n) := by
  have hq : 3000 ≤ 4 * n := Nat.mul_le_mul_left 4 hn750
  have hp := AnalyticNumberTheory.Arithmetic.log_log_pos_of_le hq
  have hw := preciseSaving_factor_cost hn hn750
  have hs :=
    primeFactorLogSum_le_prime31 (Nat.mul_ne_zero (by norm_num only : (4 : ℕ) ≠ 0) hn.pos.ne')
  have ha :=
    le_max_right (0 : ℝ)
      (2 * Real.log (Real.log (4 * n : ℕ)) - 31551 / 20000 -
        AnalyticNumberTheory.Arithmetic.primeFactorLogSum (4 * n))
  change _ ≤ preciseSavingAuxiliary (4 * n) at ha
  have hc :
    preciseSavingCorrectionTerm (4 * n) ≤
      (2 / 31 : ℝ) * Real.log (4 * n : ℕ) + (4 / 5 : ℝ) * Real.log (Real.log (4 * n : ℕ)) +
        18327 / 2000 := by
    dsimp only [preciseSavingCorrectionTerm]
    exact max_le (by linarith only [hp.1, hp.2]) (by linarith only [hw, hs, ha])
  dsimp only [preciseSavingRadiusRoot, prime31SavingRoot]
  linarith only [hc]

end PseudoPrime.LLS
