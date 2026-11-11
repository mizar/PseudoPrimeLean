/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.UniformKorseltTriple
public import PseudoPrime.AnalyticNumberTheory.GRH.Definition
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFiniteCell
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformFiniteBudget
import PseudoPrime.Analysis.LogTaylorBounds
import PseudoPrime.AnalyticNumberTheory.Arithmetic.TruncatedEulerCertificates3

/-! # Uniform quarter witness on an independently certified interval -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Exact logarithm and negative-power checks for this radius interval. -/
private theorem endpoint_checks :
    Analysis.rationalLogIntervalCheck 52900 16 32 0 (54381 / 5000) = true ∧
      AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 50625 0 (831 / 100000000) 27 25 =
        true ∧
      AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 50625 0 (4671 / 2500000) 29 50 =
        true ∧
      AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 50625 0 (1557 / 12500000) 83 100 =
        true := by
  decide +kernel

/-- Endpoint certificates imply the finite scalar budget throughout this radius interval. -/
private theorem scalar_budget {r : ℝ} (ha : (225 : ℝ) ≤ r) (hb : r ≤ 230) :
    (4 * r) * quarterReflectedScale r + (39 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 + quarterMomentScale r +
            (3 / 4 : ℝ) * r -
          (3117 / 400 : ℝ) * (27 / 25 : ℝ) ^ 5 +
        4 * quarterEulerClosedTailCap (r ^ 2) ≤
      (27 / 25 : ℝ) ^ 5 * ((24439 / 50000 : ℝ) * r - 7 / 200 - (29631 / 200 : ℝ) / r) -
        3 * Real.log (2 * Real.pi) * quarterReflectedScale r := by
  have hl := (Analysis.rationalLogIntervalCheck_sound endpoint_checks.1).2
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound endpoint_checks.2.1).2
  have hq :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound endpoint_checks.2.2.1).2
  have hv :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound endpoint_checks.2.2.2).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl hp hq hv
  apply
    quarter_finite_budget_cell (a := 225) (b := 230) (L := (54381 / 5000)) (P := (831 / 100000000))
      (Q := (4671 / 2500000)) (V := (1557 / 12500000)) (R := (2681 / 1000000)) (H :=
      (4233 / 500000)) (J := (102113 / 1000000)) (by norm_num only) ha hb
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

/-- Under GRH, a uniform Korselt triple in this logarithmic interval has a
rejecting prime bounded by one quarter of its squared logarithm. Exact endpoint
checks certify the finite scalar budget. -/
theorem quarter_uniform_450_460 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hlo : (450 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ 460) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let r : ℝ := Real.log n / 2
  have hr : (225 : ℝ) ≤ r := by
    dsimp only [r]; linarith only [hlo]
  have hrU : r ≤ (230 : ℝ) := by
    dsimp only [r]; linarith only [hhi]
  have hU : Real.log n ≤ 2 * r := by
    dsimp only [r]; linarith only
  have hcut : r ^ 2 ≤ (1 / 4 : ℝ) * Real.log n ^ 2 := by
    dsimp only [r]
    ring_nf
    exact le_rfl
  exact
    quarter_uniform_finite_budget hn ho hu hGRH (by linarith only [hr]) (by linarith only [hrU]) hU
      hcut (scalar_budget hr hrU)

end PseudoPrime.PrimeTestBounds.MillerRabin
