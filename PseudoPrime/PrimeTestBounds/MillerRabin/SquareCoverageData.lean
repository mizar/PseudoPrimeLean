/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.SquareCoverageChain

/-! # Certified coverage data for odd prime squares -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A square-witness coverage row. The prime cutoff applies through `target`; `seed` is
the initial logarithmic cap, `logScale` normalizes `log (bound + 1)`, and `chain` contains
indices of certified counting candidates that extend the initial cap. -/
structure SquareCoverageData where
  /-- Prime witness cutoff. -/
  bound : ℕ
  /-- Initial logarithmic coverage cap. -/
  seed : ℚ
  /-- Final logarithmic coverage cap. -/
  target : ℚ
  /-- Binary scale for the initial cap certificate. -/
  logScale : ℕ
  /-- Candidate indices used to extend coverage. -/
  chain : List ℕ

/-- Check the seed logarithm with a strict rational margin and check the candidate chain.
The latter uses the globally certified candidate list and verifies every overlap and cutoff. -/
def SquareCoverageData.check (d : SquareCoverageData) : Bool :=
  decide
    (Analysis.fineLogCheck (d.bound + 1 : ℕ) d.logScale 64 (d.seed / 2 + 1 / 1000000000000000000)
          (d.seed / 2 + 1) =
        true ∧
      squareChainCheck allCountCandidates d.bound d.seed d.target d.chain = true)

/-- Under RH, a checked coverage row gives a rejecting prime at most its cutoff for any
odd prime square whose logarithm is at most its target. The seed follows from the square's
prime factor, and the checked chain extends that seed with repeated-product candidates. -/
theorem SquareCoverageData.sound {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (d : SquareCoverageData) (hcheck : d.check = true)
    (hlog : Real.log n ≤ (d.target : ℝ)) :
    ∃ r : ℕ, r.Prime ∧ r ≤ d.bound ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hc :
    Analysis.fineLogCheck (d.bound + 1 : ℕ) d.logScale 64 (d.seed / 2 + 1 / 1000000000000000000)
          (d.seed / 2 + 1) =
        true ∧
      squareChainCheck allCountCandidates d.bound d.seed d.target d.chain = true :=
    of_decide_eq_true hcheck
  have hs := (Analysis.fineLogCheck_sound hc.1).1
  simp only [Rat.cast_add, Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_natCast,
    Nat.cast_add, Nat.cast_one] at hs
  have hseed : (d.seed : ℝ) < 2 * Real.log (d.bound + 1) := by linarith only [hs]
  apply
    squareChainCheck_sound hn ho hp hp2 hpow hRH allCountCandidates allCountCandidates_checked
      d.bound d.chain d.seed d.target hc.2
  · exact exists_prime_reject_square_seed hn ho hp hpow d.seed hseed
  · exact hlog

end PseudoPrime.PrimeTestBounds.MillerRabin
