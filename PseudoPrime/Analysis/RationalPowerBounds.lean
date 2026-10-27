/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Rational enclosures of negative rational real powers via integer powers -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For b>0, natural p and nonzero natural d, the d-th power of b^(-p/d),
multiplied by b^p, equals one. Cancel the rational exponent and use inverse powers.
This identity reduces real-power certification to integer-power inequalities. -/
theorem negRationalPower_mul_pow {b : ℝ} (hb : 0 < b) (p : ℕ) {d : ℕ} (hd : d ≠ 0) :
    (b ^ (-(p : ℝ) / (d : ℝ))) ^ d * b ^ p = 1 := by
  rw [← Real.rpow_mul_natCast hb.le, div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr hd),
    Real.rpow_neg hb.le, Real.rpow_natCast, inv_mul_cancel₀ (ne_of_gt (pow_pos hb p))]

/-- For b>0 and lo>=0, a natural-power product at most one certifies lo<=b^(-p/d).
Here p is natural and d is a nonzero natural. Cancel the positive factor b^p
and reflect the d-th power comparison. This supplies certified lower endpoints. -/
theorem le_negRationalPower_of_mul_pow_le {b lo : ℝ} (hb : 0 < b) (hlo : 0 ≤ lo) (p : ℕ) {d : ℕ}
    (hd : d ≠ 0) (h : lo ^ d * b ^ p ≤ 1) : lo ≤ b ^ (-(p : ℝ) / (d : ℝ)) := by
  have hp := pow_pos hb p
  have he := negRationalPower_mul_pow hb p hd
  have hpow : lo ^ d ≤ (b ^ (-(p : ℝ) / (d : ℝ))) ^ d := by
    exact (mul_le_mul_iff_left₀ hp).mp (h.trans_eq he.symm)
  exact (pow_le_pow_iff_left₀ hlo (Real.rpow_pos_of_pos hb _).le hd).mp hpow

/-- For b>0 and hi>=0, a natural-power product at least one certifies b^(-p/d)<=hi.
Here p is natural and d is a nonzero natural. Cancel the positive factor b^p
and reflect the d-th power comparison. This supplies certified upper endpoints. -/
theorem negRationalPower_le_of_one_le_mul_pow {b hi : ℝ} (hb : 0 < b) (hhi : 0 ≤ hi) (p : ℕ) {d : ℕ}
    (hd : d ≠ 0) (h : 1 ≤ hi ^ d * b ^ p) : b ^ (-(p : ℝ) / (d : ℝ)) ≤ hi := by
  have hp := pow_pos hb p
  have he := negRationalPower_mul_pow hb p hd
  have hpow : (b ^ (-(p : ℝ) / (d : ℝ))) ^ d ≤ hi ^ d := by
    exact (mul_le_mul_iff_left₀ hp).mp (he.trans_le h)
  exact (pow_le_pow_iff_left₀ (Real.rpow_pos_of_pos hb _).le hhi hd).mp hpow

/-- For positive b, nonnegative endpoints and natural p with nonzero natural d,
two integer-power product checks enclose b^(-p/d) in the closed interval.
Combine the endpoint lemmas. This supports finite Euler-prefix certificates. -/
theorem negRationalPower_mem_Icc {b lo hi : ℝ} (hb : 0 < b) (hlo : 0 ≤ lo) (hhi : 0 ≤ hi) (p : ℕ)
    {d : ℕ} (hd : d ≠ 0) (hl : lo ^ d * b ^ p ≤ 1) (hu : 1 ≤ hi ^ d * b ^ p) :
    b ^ (-(p : ℝ) / (d : ℝ)) ∈ Set.Icc lo hi := by
  exact
    ⟨le_negRationalPower_of_mul_pow_le hb hlo p hd hl,
      negRationalPower_le_of_one_le_mul_pow hb hhi p hd hu⟩

/-- For a finite set of bases at least one, upper log endpoints and nonnegative power
endpoints satisfying integer-power checks bound the logarithmic Dirichlet prefix.
Apply the scalar power upper bound termwise. This is the numerator certificate interface. -/
theorem sum_log_mul_negRationalPower_le {ι : Type*} (S : Finset ι) (b u ell : ι → ℝ) (p : ℕ) {d : ℕ}
    (hd : d ≠ 0) (hb : ∀ i ∈ S, 1 ≤ b i) (hu : ∀ i ∈ S, 0 ≤ u i)
    (hl : ∀ i ∈ S, Real.log (b i) ≤ ell i) (hc : ∀ i ∈ S, 1 ≤ (u i) ^ d * (b i) ^ p) :
    (∑ i ∈ S, Real.log (b i) * (b i) ^ (-(p : ℝ) / (d : ℝ))) ≤ ∑ i ∈ S, ell i * u i := by
  refine Finset.sum_le_sum (fun i hi ↦ ?_)
  have hbi := zero_lt_one.trans_le (hb i hi)
  have hpow := negRationalPower_le_of_one_le_mul_pow hbi (hu i hi) p hd (hc i hi)
  exact
    mul_le_mul (hl i hi) hpow (Real.rpow_pos_of_pos hbi _).le
      ((Real.log_nonneg (hb i hi)).trans (hl i hi))

/-- For positive bases and nonnegative lower endpoints on a finite set, integer-power
checks bound the Dirichlet prefix from below. The natural denominator d is nonzero.
Apply the scalar lower bound termwise. This is the denominator certificate interface. -/
theorem sum_lower_le_sum_negRationalPower {ι : Type*} (S : Finset ι) (b lo : ι → ℝ) (p : ℕ) {d : ℕ}
    (hd : d ≠ 0) (hb : ∀ i ∈ S, 0 < b i) (hlo : ∀ i ∈ S, 0 ≤ lo i)
    (hc : ∀ i ∈ S, (lo i) ^ d * (b i) ^ p ≤ 1) :
    (∑ i ∈ S, lo i) ≤ ∑ i ∈ S, (b i) ^ (-(p : ℝ) / (d : ℝ)) := by
  exact
    Finset.sum_le_sum
      (fun i hi ↦ le_negRationalPower_of_mul_pow_le (hb i hi) (hlo i hi) p hd (hc i hi))

end PseudoPrime.Analysis
