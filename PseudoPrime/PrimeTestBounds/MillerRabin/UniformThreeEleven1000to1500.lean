/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.UniformKorseltTriple
public import PseudoPrime.AnalyticNumberTheory.GRH.Definition
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformNarrowCell
import PseudoPrime.Analysis.PreciseLogTaylorBounds
import PseudoPrime.AnalyticNumberTheory.Arithmetic.TruncatedEulerCertificates3

/-! # Uniform three-elevenths witness on a certified interval -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Exact logarithm and negative-power checks for this scale interval. -/
private theorem endpoint_checks :
    Analysis.preciseLogCheck (24545175561 / 40000) 20 32 (133271 / 10000) (16659 / 1250) = true ∧
      AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck (2727241729 / 10000) 0
          (421 / 312500000) 27 25 =
        true ∧
      AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck (2727241729 / 10000) 0
          (7035263 / 10000000000) 29 50 =
        true ∧
      AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck (2727241729 / 10000) 0
          (153929 / 5000000000) 83 100 =
        true := by
  decide +kernel

/-- Under GRH, a uniform Korselt triple on this logarithmic interval has a
rejecting prime with coefficient `3 / 11`. Exact endpoint certificates
establish the narrow centered budget. -/
theorem uniform_three_eleven_1000_1500 {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (1000 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ 1500) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (3 / 11 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hl := (Analysis.preciseLogCheck_sound endpoint_checks.1).2
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound endpoint_checks.2.1).2
  have hq :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound endpoint_checks.2.2.1).2
  have hv :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound endpoint_checks.2.2.2).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl hp hq hv
  apply
    uniform_narrow_cell hn ho hu hGRH (a := 1000) (b := 1500) (L := (16659 / 1250)) (P :=
      (421 / 312500000)) (Q := (7035263 / 10000000000)) (V := (153929 / 5000000000)) (R :=
      (1001 / 1000000)) (H := (2717 / 1000000)) (J := (25713 / 500000)) (s := (357068 / 15625))
      (t := (13994151 / 500000)) (by norm_num only) hlo hhi
  · norm_num only at hl ⊢
    exact hl
  · norm_num only at hp ⊢
    exact hp
  · norm_num only at hq ⊢
    exact hq
  · norm_num only at hv ⊢
    exact hv
  · norm_num only
  · norm_num only
  · norm_num only
  · norm_num only
  · norm_num only
  · norm_num only [quarterMomentPolynomial]
  · norm_num only [quarterEulerClosedUpper, quarterMomentClosedUpper, Analysis.logPowerTailPoly]
  · norm_num only

end PseudoPrime.PrimeTestBounds.MillerRabin
