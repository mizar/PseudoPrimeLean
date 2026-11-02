/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.MarkedPrimeFactorLogMean

/-! # Small-prime tails for reciprocal logarithmic factor weights

For an arbitrary cutoff greater than one, split each reciprocal prime-factor weight
into a uniform logarithmic part and a signed excess. Large primes have nonpositive
excess, while the remaining contribution is bounded by the finite set of all small
primes. This applies to logarithmic level-change and prime-support budgets independently
of any selected analytic kernel. Concrete cutoff certificates belong to their consumers.
-/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- The excess of a reciprocal logarithmic prime weight above a uniform cutoff weight.
Input: a natural cutoff and a natural argument. Output: log(p) times the reciprocal difference.
Role: separate nonpositive large-prime tails from the finite small-prime contribution. -/
noncomputable def primeLogTailWeight (P p : ℕ) : ℝ :=
  Real.log p * (1 / ((p : ℝ) - 1) - 1 / (P : ℝ))

/-- The complete small-prime excess constant at an arbitrary cutoff.
Input: a natural cutoff. Output: the sum of excess weights over every prime at most the cutoff.
Role: bound arbitrary prime supports using a reusable finite logarithmic certificate. -/
noncomputable def smallPrimeLogConstant (P : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, primeLogTailWeight P p

/-- A prime at most the cutoff has nonnegative excess weight.
Input: a cutoff greater than one and a prime below it. Claim: its reciprocal difference is positive.
Proof: compare positive denominators. Role: enlarge a small prime support to all small primes. -/
theorem primeLogTailWeight_nonneg {P p : ℕ} (hp : p.Prime) (hpP : p ≤ P) :
    0 ≤ primeLogTailWeight P p := by
  have hp1 : (1 : ℝ) < p := Nat.one_lt_cast.mpr hp.one_lt
  have hden : (0 : ℝ) < (p : ℝ) - 1 := sub_pos.mpr hp1
  have hpcast : (p : ℝ) ≤ P := Nat.cast_le.mpr hpP
  have hi := one_div_le_one_div_of_le hden (show (p : ℝ) - 1 ≤ P by linarith only [hpcast])
  exact mul_nonneg (Real.log_natCast_nonneg p) (sub_nonneg.mpr hi)

/-- Every argument above a cutoff greater than one has nonpositive excess weight.
Input: the cutoff lower bound and an argument strictly above it. Claim: the excess is nonpositive.
Proof: compare denominators and use the nonnegative natural logarithm.
Role: discard the large-prime part of any finite prime support. -/
theorem primeLogTailWeight_nonpos {P p : ℕ} (hP : 1 < P) (hpP : P < p) :
    primeLogTailWeight P p ≤ 0 := by
  have hP0 : (0 : ℝ) < P := Nat.cast_pos.mpr ((by norm_num only : (0 : ℕ) < 1).trans hP)
  have hpcast : (P : ℝ) + 1 ≤ p := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (Nat.cast_le (α := ℝ)).mpr (Nat.add_one_le_iff.mpr hpP)
  have hi := one_div_le_one_div_of_le hP0 (show (P : ℝ) ≤ (p : ℝ) - 1 by linarith only [hpcast])
  exact mul_nonpos_of_nonneg_of_nonpos (Real.log_natCast_nonneg p) (sub_nonpos.mpr hi)

/-- A nonzero integer's reciprocal prime-factor logarithmic sum has a finite small-prime majorant.
Input: a nonzero natural number and any natural cutoff greater than one.
Claim: the sum is at most log(q)/P plus the complete small-prime excess constant.
Proof: split the uniform logarithmic term, discard the nonpositive tail, and use the
squarefree-product logarithmic bound. Role: kernel-independent prime-support and level budgets. -/
theorem sum_primeFactor_log_div_le {q P : ℕ} (hq : q ≠ 0) (hP : 1 < P) :
    (∑ p ∈ q.primeFactors, Real.log p / ((p : ℝ) - 1)) ≤
      Real.log q / (P : ℝ) + smallPrimeLogConstant P := by
  classical
  let S := q.primeFactors.filter (fun p ↦ p ≤ P)
  have hdrop :
    (∑ p ∈ q.primeFactors, primeLogTailWeight P p) ≤ ∑ p ∈ S, primeLogTailWeight P p := by
    apply Finset.sum_le_sum_of_subset_of_nonpos (Finset.filter_subset _ _)
    intro p hp hnot
    exact primeLogTailWeight_nonpos hP (lt_of_not_ge fun h ↦ hnot (Finset.mem_filter.mpr ⟨hp, h⟩))
  have hsmall : (∑ p ∈ S, primeLogTailWeight P p) ≤ smallPrimeLogConstant P := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      have hm := Finset.mem_filter.mp hp
      exact
        Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hm.2), Nat.prime_of_mem_primeFactors hm.1⟩
    · intro p hp _
      have hm := Finset.mem_filter.mp hp
      exact primeLogTailWeight_nonneg hm.2 (Nat.le_of_lt_succ (Finset.mem_range.mp hm.1))
  have he :
    (∑ p ∈ q.primeFactors, Real.log p / ((p : ℝ) - 1)) =
      (∑ p ∈ q.primeFactors, Real.log p) / (P : ℝ) +
        ∑ p ∈ q.primeFactors, primeLogTailWeight P p := by
    rw [Finset.sum_div, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    dsimp only [primeLogTailWeight]
    ring
  rw [he]
  exact
    add_le_add
      (div_le_div_of_nonneg_right (sum_log_primeFactors_le_log (Nat.pos_of_ne_zero hq))
        (Nat.cast_nonneg P))
      (hdrop.trans hsmall)

end PseudoPrime.NumberTheory
