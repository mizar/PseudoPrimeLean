/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Cell05
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerCap292
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAbelEnvelope
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentIntegralCaps

/-! # Uniform triple cell at cutoff 292 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The numerical endpoint estimates and the six moment bounds control the
quarter-square budget at cutoff 292. -/
theorem quarter_uniform_budget292 (hm : QuarterMomentBounds) :
    quarterUniformBudget 292 37 (23453 / 10000) (quarterUniformAbel 292)
        (refinedReflectedEuler (1 : DirichletCharacter ℂ 1) 292) ≤
      4 * (2718 / 625 : ℝ) := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 292 8 32 0 (56769 / 10000) = true from by
          decide +kernel)).2
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 292 0 (217465 / 100000000) 27
              25 =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl hp
  have hlog : Real.log 292 ≤ (56769 / 10000 : ℝ) := by
    norm_num only at hl ⊢
    exact hl
  have hpow : (292 : ℝ) ^ (-(27 / 25 : ℝ)) ≤ (217465 / 100000000 : ℝ) := by
    norm_num only at hp ⊢
    exact hp
  have hs : (170880 / 10000 : ℝ) ≤ Real.sqrt 292 := Real.le_sqrt_of_sq_le (by norm_num only)
  have ht : Real.sqrt 292 ≤ (170881 / 10000 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  have hb :=
    quarter_abel_envelope (X := 292) (U := 37) (L := 56769 / 10000) (Q := 217465 / 100000000) (s :=
      170880 / 10000) (t := 170881 / 10000) (P := 23453 / 10000) (by norm_num only)
      (by norm_num only) hlog hpow (by norm_num only) hs ht hm
  apply hb.trans
  norm_num only [quarterAbelEnvelope, quarterMomentPolynomial]

/-- GRH supplies a quarter-square rejecting prime for a uniform Korselt triple
in the cell. Its principal and Euler lower bounds are checked independently. -/
theorem quarter_uniform_36_37 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hlo : (36 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ 37) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (292 : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 := by nlinarith only [hlo]
  exact
    quarter_uniform_of_abel hn ho hu hGRH (X := 292) (U := 37) (S := 2718 / 625) (P :=
      23453 / 10000) (H := refinedReflectedEuler (1 : DirichletCharacter ℂ 1) 292)
      (by norm_num only) le_rfl hhi hcut (le_of_lt target028_cell05_principal) quarter_euler_cap292
      (quarter_uniform_budget292
        (quarter_moment_bounds_of_integrals hGRH.riemann quarter_moment_integral_bounds))

end PseudoPrime.PrimeTestBounds.MillerRabin
