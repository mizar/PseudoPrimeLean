/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.CountCandidateLogCheck
public import PseudoPrime.PrimeTestBounds.MillerRabin.IndexedPrimeSupplies
public import PseudoPrime.PrimeTestBounds.MillerRabin.SquareLocalCounting

/-! # Indexed repeated-product candidates and witnesses -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Check a candidate's logarithm bounds and its membership in the indexed prime supply
table. The Boolean also checks that the prime cutoff exceeds one. -/
def CandidateLogData.indexedCheck (d : CandidateLogData) : Bool :=
  d.check &&
    decide (1 < d.candidate.bound ∧ (d.candidate.bound, d.candidate.count) ∈ indexedSupplies)

/-- A successful indexed candidate check supplies the prime count and logarithm check.
The prime index table provides the count independently of the candidate's degree. -/
theorem CandidateLogData.indexed_sound (d : CandidateLogData) (h : d.indexedCheck = true) :
    d.check = true ∧
      1 < d.candidate.bound ∧ d.candidate.count ≤ d.candidate.bound.primeCounting := by
  have hc := Bool.and_eq_true_iff.mp h
  have hi : 1 < d.candidate.bound ∧ (d.candidate.bound, d.candidate.count) ∈ indexedSupplies :=
    of_decide_eq_true hc.2
  exact ⟨hc.1, hi.1, indexedSupplies_sound _ hi.2⟩

/-- Under GRH, a checked indexed candidate bounds a rejecting prime for an odd product
of distinct primes. The indexed supply and logarithm certificate discharge the hypotheses
of the local-or-counting witness theorem. -/
theorem CandidateLogData.indexed_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (d : CandidateLogData)
    (hcheck : d.indexedCheck = true) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ semiprimeCandidateBound d.candidate (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have h := d.indexed_sound hcheck
  exact
    exists_prime_reject_semiprime_candidate hn ho hp hq hpq hprod h.2.1 h.2.2 hGRH (d.sound h.1).1
      (d.sound h.1).2.le

/-- A checked indexed candidate bounds a rejecting prime for an odd prime square when
its logarithm lies in the candidate's size and count interval. The strict logarithm
certificate proves the multichoose inequality required by the square criterion. -/
theorem CandidateLogData.indexed_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpow : n = p ^ 2) (d : CandidateLogData) (hcheck : d.indexedCheck = true)
    (hlo : (d.candidate.upper : ℝ) < Real.log n) (hhi : Real.log n ≤ 2 * d.candidate.lower) :
    ∃ r : ℕ, r.Prime ∧ r ≤ d.candidate.bound ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have h := d.indexed_sound hcheck
  exact
    exists_prime_reject_square_candidate hn ho hp hp2 hpow h.2.1 h.2.2 (d.sound h.1).1 hlo hhi
      (d.sound h.1).2

end PseudoPrime.PrimeTestBounds.MillerRabin
