/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.AnalyticCandidateWitness

/-! # Witnesses from certified repeated-product candidate lists -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, every member of a checked list gives its semiprime witness bound. Extract
the member's certificate and apply the combined indexed-or-analytic witness theorem. -/
theorem candidateList_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (L : List CandidateLogData) (hL : L.all CandidateLogData.certifiedCheck = true)
    (d : CandidateLogData) (hd : d ∈ L) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ semiprimeCandidateBound d.candidate (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact d.certified_semiprime hn ho hp hq hpq hprod hGRH (List.all_eq_true.mp hL d hd)

/-- Under RH, a member of a checked list gives its square witness bound throughout its
logarithmic interval. Extract the member's certificate and apply the square criterion. -/
theorem candidateList_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (L : List CandidateLogData)
    (hL : L.all CandidateLogData.certifiedCheck = true) (d : CandidateLogData) (hd : d ∈ L)
    (hlo : (d.candidate.upper : ℝ) < Real.log n) (hhi : Real.log n ≤ 2 * d.candidate.lower) :
    ∃ r : ℕ, r.Prime ∧ r ≤ d.candidate.bound ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact d.certified_square hn ho hp hp2 hpow hRH (List.all_eq_true.mp hL d hd) hlo hhi

end PseudoPrime.PrimeTestBounds.MillerRabin
