/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.AnalyticCandidateWitness

/-! # Initial repeated-product candidates for the counting envelope -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The first 32 selected repeated-product candidates, with their Taylor scales. Their
cutoffs, counts, degrees and endpoints are used by the early square and semiprime cells. -/
def initialCandidates : List CandidateLogData :=
  [⟨⟨11, 5, 2, 2397895272799 / 500000000000, 3044522437723 / 1000000000000⟩, 4, 5⟩,
    ⟨⟨11, 5, 3, 7193685818397 / 1000000000000, 805070338147 / 200000000000⟩, 4, 6⟩,
    ⟨⟨13, 6, 2, 1282474678731 / 250000000000, 133288180407 / 40000000000⟩, 4, 5⟩,
    ⟨⟨13, 6, 3, 3847424036193 / 500000000000, 4430816798843 / 1000000000000⟩, 4, 7⟩,
    ⟨⟨19, 8, 2, 2944438979167 / 500000000000, 380666248977 / 100000000000⟩, 5, 6⟩,
    ⟨⟨19, 8, 3, 8833316937501 / 1000000000000, 51059454739 / 10000000000⟩, 5, 8⟩,
    ⟨⟨19, 8, 4, 2944438979167 / 250000000000, 6204557762567 / 1000000000000⟩, 5, 9⟩,
    ⟨⟨29, 10, 2, 3367295829987 / 500000000000, 2094827371013 / 500000000000⟩, 5, 7⟩,
    ⟨⟨29, 10, 3, 10101887489961 / 1000000000000, 5655991810819 / 1000000000000⟩, 5, 9⟩,
    ⟨⟨31, 11, 2, 1716993602243 / 250000000000, 4356708826689 / 1000000000000⟩, 5, 7⟩,
    ⟨⟨31, 11, 3, 5150980806729 / 500000000000, 1179430773527 / 200000000000⟩, 5, 9⟩,
    ⟨⟨31, 11, 4, 1716993602243 / 125000000000, 7218909707617 / 1000000000000⟩, 5, 11⟩,
    ⟨⟨43, 14, 2, 1880600057847 / 250000000000, 4787491742781 / 1000000000000⟩, 6, 7⟩,
    ⟨⟨43, 14, 3, 5641800173541 / 500000000000, 652209279817 / 100000000000⟩, 6, 10⟩,
    ⟨⟨43, 14, 4, 1880600057847 / 125000000000, 7838056831 / 976562500⟩, 6, 12⟩,
    ⟨⟨53, 16, 2, 3970291913553 / 500000000000, 314402370087 / 62500000000⟩, 6, 8⟩,
    ⟨⟨53, 16, 3, 11910875740659 / 1000000000000, 687626461189 / 100000000000⟩, 6, 10⟩,
    ⟨⟨53, 16, 4, 3970291913553 / 250000000000, 2121425631081 / 250000000000⟩, 6, 13⟩,
    ⟨⟨67, 19, 2, 4204692619391 / 500000000000, 1336776882679 / 250000000000⟩, 7, 8⟩,
    ⟨⟨67, 19, 3, 12614077858173 / 1000000000000, 7339537695407 / 1000000000000⟩, 7, 11⟩,
    ⟨⟨67, 19, 4, 4204692619391 / 250000000000, 1136092193777 / 125000000000⟩, 7, 14⟩,
    ⟨⟨67, 19, 5, 4204692619391 / 200000000000, 5328676734063 / 500000000000⟩, 7, 16⟩,
    ⟨⟨71, 20, 2, 2131339938521 / 250000000000, 5442417710521 / 1000000000000⟩, 7, 8⟩,
    ⟨⟨71, 20, 3, 6394019815563 / 500000000000, 3739649818891 / 500000000000⟩, 7, 11⟩,
    ⟨⟨71, 20, 4, 2131339938521 / 125000000000, 144860298547 / 15625000000⟩, 7, 14⟩,
    ⟨⟨71, 20, 5, 2131339938521 / 100000000000, 10880497019441 / 1000000000000⟩, 7, 16⟩,
    ⟨⟨83, 23, 2, 4418840607797 / 500000000000, 178243202333 / 31250000000⟩, 7, 9⟩,
    ⟨⟨83, 23, 3, 13256521823391 / 1000000000000, 7863266724007 / 1000000000000⟩, 7, 12⟩,
    ⟨⟨83, 23, 4, 4418840607797 / 250000000000, 9772809228891 / 1000000000000⟩, 7, 15⟩,
    ⟨⟨83, 23, 5, 4418840607797 / 200000000000, 11495575826631 / 1000000000000⟩, 7, 17⟩,
    ⟨⟨89, 24, 2, 4488636369733 / 500000000000, 5783825182329 / 1000000000000⟩, 7, 9⟩,
    ⟨⟨89, 24, 3, 13465909109199 / 1000000000000, 1596209951933 / 200000000000⟩, 7, 12⟩]

set_option maxRecDepth 16384 in
/-- All initial candidates pass their logarithm and prime-supply checks by finite reduction. -/
theorem initialCandidates_checked :
    initialCandidates.all CandidateLogData.certifiedCheck = true := by decide +kernel

/-- Under GRH, each initial candidate bounds a rejecting prime for an odd product of
distinct primes. Select its checked certificate and apply the local-or-counting theorem. -/
theorem initialCandidates_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (d : CandidateLogData)
    (hd : d ∈ initialCandidates) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ semiprimeCandidateBound d.candidate (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact
    d.certified_semiprime hn ho hp hq hpq hprod hGRH
      (List.all_eq_true.mp initialCandidates_checked d hd)

/-- Under RH, an initial candidate bounds a rejecting prime for an odd prime square in
its logarithmic interval. Its checked strict count endpoint discharges the square criterion. -/
theorem initialCandidates_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (d : CandidateLogData) (hd : d ∈ initialCandidates)
    (hlo : (d.candidate.upper : ℝ) < Real.log n) (hhi : Real.log n ≤ 2 * d.candidate.lower) :
    ∃ r : ℕ, r.Prime ∧ r ≤ d.candidate.bound ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact
    d.certified_square hn ho hp hp2 hpow hRH (List.all_eq_true.mp initialCandidates_checked d hd)
      hlo hhi

end PseudoPrime.PrimeTestBounds.MillerRabin
