/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.IndexedCandidateWitness
public import PseudoPrime.PrimeTestBounds.MillerRabin.AnalyticPrimeSupplyData

/-! # Analytic repeated-product candidates and witnesses -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Check a candidate's logarithms, cutoff and membership in the analytic prime supply
table. Membership is determined by the square cutoff and count, independently of degree. -/
def CandidateLogData.analyticCheck (d : CandidateLogData) : Bool :=
  d.check && decide (1 < d.candidate.bound) &&
    analyticSupplies.any
      (fun s ↦ decide (s.root ^ 2 = d.candidate.bound ∧ s.count = d.candidate.count))

/-- Under RH, a successful analytic candidate check gives its prime supply and checked
logarithms. Locate the matching supply in the certified table and transfer its count. -/
theorem CandidateLogData.analytic_sound (hRH : RiemannHypothesis) (d : CandidateLogData)
    (h : d.analyticCheck = true) :
    d.check = true ∧
      1 < d.candidate.bound ∧ d.candidate.count ≤ d.candidate.bound.primeCounting := by
  have hparts := Bool.and_eq_true_iff.mp h
  have hleft := Bool.and_eq_true_iff.mp hparts.1
  have hB : 1 < d.candidate.bound := of_decide_eq_true hleft.2
  obtain ⟨s, hs, heq⟩ := List.any_eq_true.mp hparts.2
  have hs' : s.root ^ 2 = d.candidate.bound ∧ s.count = d.candidate.count := of_decide_eq_true heq
  have hpi := analyticSupplies_sound hRH s hs
  rw [hs'.1, hs'.2] at hpi
  exact ⟨hleft.1, hB, hpi⟩

/-- Under GRH, a checked analytic candidate bounds a rejecting prime for an odd product
of distinct primes. The RH supply and logarithm checks discharge the local-or-counting
witness theorem. -/
theorem CandidateLogData.analytic_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (d : CandidateLogData)
    (hcheck : d.analyticCheck = true) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ semiprimeCandidateBound d.candidate (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have h := d.analytic_sound hGRH.riemann hcheck
  exact
    exists_prime_reject_semiprime_candidate hn ho hp hq hpq hprod h.2.1 h.2.2 hGRH (d.sound h.1).1
      (d.sound h.1).2.le

/-- Under RH, a checked analytic candidate bounds a rejecting prime for an odd prime
square in its logarithmic interval. The strict multichoose bound provides the counting
inequality required by the square criterion. -/
theorem CandidateLogData.analytic_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (d : CandidateLogData)
    (hcheck : d.analyticCheck = true) (hlo : (d.candidate.upper : ℝ) < Real.log n)
    (hhi : Real.log n ≤ 2 * d.candidate.lower) :
    ∃ r : ℕ, r.Prime ∧ r ≤ d.candidate.bound ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have h := d.analytic_sound hRH hcheck
  exact
    exists_prime_reject_square_candidate hn ho hp hp2 hpow h.2.1 h.2.2 (d.sound h.1).1 hlo hhi
      (d.sound h.1).2

/-- Check the logarithms and cutoff of a candidate and find either an indexed or an RH
prime supply. The shared logarithm check is evaluated only once for either supply kind. -/
def CandidateLogData.certifiedCheck (d : CandidateLogData) : Bool :=
  d.check && decide (1 < d.candidate.bound) &&
    (decide ((d.candidate.bound, d.candidate.count) ∈ indexedSupplies) ||
      analyticSupplies.any
        (fun s ↦ decide (s.root ^ 2 = d.candidate.bound ∧ s.count = d.candidate.count)))

/-- Under RH, a successful combined check yields the logarithm check, valid cutoff and
prime supply. The proof selects the indexed or analytic table according to the check. -/
theorem CandidateLogData.certified_sound (hRH : RiemannHypothesis) (d : CandidateLogData)
    (h : d.certifiedCheck = true) :
    d.check = true ∧
      1 < d.candidate.bound ∧ d.candidate.count ≤ d.candidate.bound.primeCounting := by
  have hparts := Bool.and_eq_true_iff.mp h
  have hleft := Bool.and_eq_true_iff.mp hparts.1
  have hB : 1 < d.candidate.bound := of_decide_eq_true hleft.2
  have hpi : d.candidate.count ≤ d.candidate.bound.primeCounting := by
    rcases Bool.or_eq_true_iff.mp hparts.2 with hidx | hanalytic
    · have hi : (d.candidate.bound, d.candidate.count) ∈ indexedSupplies := of_decide_eq_true hidx
      exact indexedSupplies_sound _ hi
    · obtain ⟨s, hs, heq⟩ := List.any_eq_true.mp hanalytic
      have hs' : s.root ^ 2 = d.candidate.bound ∧ s.count = d.candidate.count :=
        of_decide_eq_true heq
      have hp := analyticSupplies_sound hRH s hs
      rw [hs'.1, hs'.2] at hp
      exact hp
  exact ⟨hleft.1, hB, hpi⟩

/-- Under GRH, a checked candidate with either kind of prime supply bounds a rejecting
prime for an odd product of distinct primes. The combined certificate discharges the
local-or-counting witness theorem. -/
theorem CandidateLogData.certified_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (d : CandidateLogData)
    (hcheck : d.certifiedCheck = true) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ semiprimeCandidateBound d.candidate (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have h := d.certified_sound hGRH.riemann hcheck
  exact
    exists_prime_reject_semiprime_candidate hn ho hp hq hpq hprod h.2.1 h.2.2 hGRH (d.sound h.1).1
      (d.sound h.1).2.le

/-- Under RH, a checked candidate with either kind of prime supply bounds a rejecting
prime for an odd prime square in its logarithmic interval. The certified strict logarithm
bound supplies the multichoose inequality. -/
theorem CandidateLogData.certified_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (d : CandidateLogData)
    (hcheck : d.certifiedCheck = true) (hlo : (d.candidate.upper : ℝ) < Real.log n)
    (hhi : Real.log n ≤ 2 * d.candidate.lower) :
    ∃ r : ℕ, r.Prime ∧ r ≤ d.candidate.bound ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have h := d.certified_sound hRH hcheck
  exact
    exists_prime_reject_square_candidate hn ho hp hp2 hpow h.2.1 h.2.2 (d.sound h.1).1 hlo hhi
      (d.sound h.1).2

end PseudoPrime.PrimeTestBounds.MillerRabin
