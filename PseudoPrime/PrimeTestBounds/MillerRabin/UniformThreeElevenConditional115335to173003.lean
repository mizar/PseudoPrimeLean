/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
public import PseudoPrime.PrimeTestBounds.MillerRabin.UniformKorseltTriple
public import PseudoPrime.AnalyticNumberTheory.GRH.Definition
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformLogSquareCell
import PseudoPrime.Analysis.PreciseLogTaylorBounds
import PseudoPrime.AnalyticNumberTheory.Arithmetic.TruncatedEulerCertificates3

/-! # Uniform three-elevenths witness on a conditional certified interval -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Exact logarithm and negative-power checks for this scale interval. -/
private theorem endpoint_checks :
    Analysis.preciseLogCheck (81626448608700877561 / 10000000000) 33 32 (57057 / 2500)
          (228229 / 10000) =
        true ∧
      AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck (1451128476237899481 / 400000000) 0
          (1 / 10000000000) 27 25 =
        true ∧
      AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck (1451128476237899481 / 400000000) 0
          (28537 / 10000000000) 29 50 =
        true ∧
      AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck (1451128476237899481 / 400000000) 0
          (117 / 10000000000) 83 100 =
        true := by
  decide +kernel

/-- Under GRH and a Chebyshev lower bound at the chosen radius, the exact
endpoint certificates give a uniform three-elevenths witness on this interval. -/
theorem uniform_115335_173003_at {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hpsi :
      let r := (52223 / 100000 : ℝ) * Real.log n
      r ^ 2 - (1 / 12 : ℝ) * r * Real.log (r ^ 2) ^ 2 ≤ Chebyshev.psi (r ^ 2))
    (hlo : (115335 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ 173003) :
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
    uniform_log_square_cell_at hn ho hu hGRH hpsi (a := 115335) (b := 173003) (L :=
      (228229 / 10000)) (P := (1 / 10000000000)) (Q := (28537 / 10000000000)) (V :=
      (117 / 10000000000)) (R := (1 / 1000000)) (H := (1 / 500000)) (J := (489 / 1000000))
      (by norm_num only) hlo hhi
  · norm_num only at hl ⊢
    exact hl
  · norm_num only at hp ⊢
    exact hp
  · norm_num only at hq ⊢
    exact hq
  · norm_num only at hv ⊢
    exact hv
  · norm_num only
  · norm_num only [quarterMomentPolynomial]
  · norm_num only [quarterEulerClosedUpper, quarterMomentClosedUpper, Analysis.logPowerTailPoly]
  · norm_num only

/-- Under GRH, a uniform Korselt triple on this logarithmic interval has a
rejecting prime with coefficient `3 / 11`. The assumed Chebyshev bound and
exact endpoint certificates establish the centered budget. -/
theorem uniform_three_eleven_cond_115335_173003 {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hpsi :
      ∀ x : ℝ, 1000000 ≤ x → x - (1 / 12 : ℝ) * Real.sqrt x * Real.log x ^ 2 ≤ Chebyshev.psi x)
    (hlo : (115335 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ 173003) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (3 / 11 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let r : ℝ := (52223 / 100000 : ℝ) * Real.log n
  have hr : (1000 : ℝ) ≤ r := by
    dsimp only [r]; nlinarith only [hlo]
  have hX : (1000000 : ℝ) ≤ r ^ 2 := by nlinarith only [hr]
  have hp := hpsi (r ^ 2) hX
  rw [Real.sqrt_sq (by linarith only [hr] : 0 ≤ r)] at hp
  exact uniform_115335_173003_at hn ho hu hGRH hp hlo hhi

end PseudoPrime.PrimeTestBounds.MillerRabin
