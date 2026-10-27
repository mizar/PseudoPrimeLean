module

public import PseudoPrime.PrimeTest.MillerRabin.OEISA006945Iff
public import PseudoPrime.AnalyticNumberTheory.GRH.Definition
public import PseudoPrime.PrimeTestBounds.MillerRabin.FromLLS

/-!
# OEIS A006945 https://oeis.org/A006945 Bounds
-/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/--
Under GRH, the n-th prime is at most the square of the logarithm of any
candidate for A006945(n).
-/
theorem a006945_candidate_prime_le_log_sq
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n a : ℕ}
    (ha : PrimeTest.A006945Candidate n a) : (Nat.nth Nat.Prime n : ℝ) ≤ (Real.log (a : ℝ)) ^ 2 := by
  obtain ⟨p, hp, hpBound, hreject⟩ :=
    exists_prime_strongMillerRabinWithBase_eq_false_le_log_sq hGRH ha.1 ha.2.1 ha.2.2.1
  by_contra hnot
  have hpn : p < Nat.nth Nat.Prime n := by exact_mod_cast lt_of_le_of_lt hpBound (lt_of_not_ge hnot)
  have hindex : Nat.count Nat.Prime p < n := by
    have hindex' := hpn
    rw [← Nat.nth_count hp] at hindex'
    exact (Nat.nth_lt_nth Nat.infinite_setOfPred_prime).mp hindex'
  have hpass := (PrimeTest.a006945Candidate_iff n a).mp ha
  have hpPass : PrimeTest.StrongMillerRabinPass a (p : ZMod a) := by
    simpa only [Nat.nth_count hp] using hpass.2.2.2 (Nat.count Nat.Prime p) hindex
  exact (PrimeTest.not_strongMillerRabinPass_iff.mpr hreject) hpPass

/--
Under GRH, any candidate for the n-th term of OEIS A006945 is at least
`exp(sqrt(p_n))`.
-/
theorem a006945_candidate_exp_sqrt_lower_bound
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n a : ℕ}
    (ha : PrimeTest.A006945Candidate n a) :
    Real.exp (Real.sqrt (Nat.nth Nat.Prime n : ℝ)) ≤ (a : ℝ) := by
  have hprime := a006945_candidate_prime_le_log_sq hGRH ha
  have hlog_nonneg : 0 ≤ Real.log (a : ℝ) := by exact Real.log_nonneg (by exact_mod_cast ha.1.le)
  have hsqrt : Real.sqrt (Nat.nth Nat.Prime n : ℝ) ≤ Real.log (a : ℝ) := by
    rw [Real.sqrt_le_iff]
    exact ⟨hlog_nonneg, hprime⟩
  calc
    Real.exp (Real.sqrt (Nat.nth Nat.Prime n : ℝ)) ≤ Real.exp (Real.log (a : ℝ)) :=
      Real.exp_le_exp.mpr hsqrt
    _ = (a : ℝ) := Real.exp_log (by exact_mod_cast Nat.zero_lt_of_lt ha.1)

/--
Under GRH, the n-th term `a` of OEIS A006945 (0-indexed)
satisfies `exp(sqrt(p_n)) ≤ a`, where `p_n` is the n-th prime
(0-indexed).

The predicate `IsA006945Term n a` states that `a` is the
least odd composite number passing the strong Miller-Rabin
test at the first `n` prime bases.

This follows from `a006945_candidate_exp_sqrt_lower_bound`,
since every term is a candidate and the lower bound does
not require minimality.
-/
theorem a006945_term_exp_sqrt_lower_bound
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n a : ℕ}
    (ha : PrimeTest.IsA006945Term n a) :
    Real.exp (Real.sqrt (Nat.nth Nat.Prime n : ℝ)) ≤ (a : ℝ) := by
  exact a006945_candidate_exp_sqrt_lower_bound hGRH ha.1

end PseudoPrime.PrimeTestBounds.MillerRabin
