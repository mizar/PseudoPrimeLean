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
    Analysis.preciseLogCheck (929782237677613301601 / 10000000000) 37 32 (63139 / 2500)
          (252557 / 10000) =
        true ∧
      AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck
          (103309137519734811289 / 2500000000) 0 (1 / 10000000000) 27 25 =
        true ∧
      AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck
          (103309137519734811289 / 2500000000) 0 (87 / 125000000) 29 50 =
        true ∧
      AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck
          (103309137519734811289 / 2500000000) 0 (1 / 625000000) 83 100 =
        true := by
  decide +kernel

/-- Under GRH and a Chebyshev lower bound at the chosen radius, the exact
endpoint certificates give a uniform three-elevenths witness on this interval. -/
theorem uniform_389258_583887_at {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hpsi :
      let r := (52223 / 100000 : ℝ) * Real.log n
      r ^ 2 - (1 / 12 : ℝ) * r * Real.log (r ^ 2) ^ 2 ≤ Chebyshev.psi (r ^ 2))
    (hlo : (389258 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ 583887) :
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
    uniform_log_square_cell_at hn ho hu hGRH hpsi (a := 389258) (b := 583887) (L :=
      (252557 / 10000)) (P := (1 / 10000000000)) (Q := (87 / 125000000)) (V := (1 / 625000000))
      (R := (1 / 500000)) (H := (3 / 1000000)) (J := (71 / 500000)) (by norm_num only) hlo hhi
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
theorem uniform_three_eleven_cond_389258_583887 {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hpsi :
      ∀ x : ℝ, 1000000 ≤ x → x - (1 / 12 : ℝ) * Real.sqrt x * Real.log x ^ 2 ≤ Chebyshev.psi x)
    (hlo : (389258 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ 583887) :
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
  exact uniform_389258_583887_at hn ho hu hGRH hp hlo hhi

end PseudoPrime.PrimeTestBounds.MillerRabin
