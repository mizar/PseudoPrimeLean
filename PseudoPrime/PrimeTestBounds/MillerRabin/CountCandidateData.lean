/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.InitialCountCandidates
public import PseudoPrime.PrimeTestBounds.MillerRabin.CountCandidateData02
public import PseudoPrime.PrimeTestBounds.MillerRabin.CountCandidateData03
public import PseudoPrime.PrimeTestBounds.MillerRabin.CountCandidateData04
public import PseudoPrime.PrimeTestBounds.MillerRabin.CountCandidateData05
public import PseudoPrime.PrimeTestBounds.MillerRabin.CountCandidateData06
public import PseudoPrime.PrimeTestBounds.MillerRabin.CountCandidateData07

/-! # Certified candidate list for the repeated-product envelope

The candidate batches retain the selected endpoints while keeping their finite checks separate.
-/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The 956 selected repeated-product candidates, in the order used by the counting
coverage data. Their prime-supply and logarithm checks are certified in separate batches. -/
def allCountCandidates : List CandidateLogData :=
  initialCandidates ++ countCandidates02 ++ countCandidates03 ++ countCandidates04 ++
    countCandidates05 ++
    countCandidates06 ++
    countCandidates07 ++
    countCandidates08 ++
    countCandidates09 ++
    countCandidates10 ++
    countCandidates11 ++
    countCandidates12 ++
    countCandidates13 ++
    countCandidates14 ++
    countCandidates15 ++
    countCandidates16 ++
    countCandidates17 ++
    countCandidates18 ++
    countCandidates19 ++
    countCandidates20 ++
    countCandidates21 ++
    countCandidates22 ++
    countCandidates23 ++
    countCandidates24 ++
    countCandidates25 ++
    countCandidates26 ++
    countCandidates27 ++
    countCandidates28 ++
    countCandidates29 ++
    countCandidates30

/-- Every selected candidate passes its prime-supply and logarithm check. Combine the
individual batch certificates without repeating their finite reductions. -/
theorem allCountCandidates_checked :
    allCountCandidates.all CandidateLogData.certifiedCheck = true := by
  simp only [allCountCandidates, List.all_append, initialCandidates_checked,
    countCandidates02_checked, countCandidates03_checked, countCandidates04_checked,
    countCandidates05_checked, countCandidates06_checked, countCandidates07_checked,
    countCandidates08_checked, countCandidates09_checked, countCandidates10_checked,
    countCandidates11_checked, countCandidates12_checked, countCandidates13_checked,
    countCandidates14_checked, countCandidates15_checked, countCandidates16_checked,
    countCandidates17_checked, countCandidates18_checked, countCandidates19_checked,
    countCandidates20_checked, countCandidates21_checked, countCandidates22_checked,
    countCandidates23_checked, countCandidates24_checked, countCandidates25_checked,
    countCandidates26_checked, countCandidates27_checked, countCandidates28_checked,
    countCandidates29_checked, countCandidates30_checked, Bool.true_and]

/-- Under GRH, every selected candidate gives its bound for an odd product of distinct
primes. Extract the member certificate from the combined list and apply the witness theorem. -/
theorem allCountCandidates_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (d : CandidateLogData)
    (hd : d ∈ allCountCandidates) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ semiprimeCandidateBound d.candidate (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact
    candidateList_semiprime hn ho hp hq hpq hprod hGRH allCountCandidates allCountCandidates_checked
      d hd

/-- Under RH, every selected candidate gives a prime-square witness in its logarithmic
interval. Extract the member certificate and apply the strict repeated-product count. -/
theorem allCountCandidates_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (d : CandidateLogData)
    (hd : d ∈ allCountCandidates) (hlo : (d.candidate.upper : ℝ) < Real.log n)
    (hhi : Real.log n ≤ 2 * d.candidate.lower) :
    ∃ r : ℕ, r.Prime ∧ r ≤ d.candidate.bound ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact
    candidateList_square hn ho hp hp2 hpow hRH allCountCandidates allCountCandidates_checked d hd
      hlo hhi

end PseudoPrime.PrimeTestBounds.MillerRabin
