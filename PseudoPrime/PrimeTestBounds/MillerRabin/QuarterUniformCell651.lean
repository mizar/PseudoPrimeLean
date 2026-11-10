/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Cell15
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerCap651
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAbelEnvelope
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentIntegralCaps

/-! # Uniform triple cell at cutoff 651 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The numerical endpoint estimates and the six moment bounds control the
quarter-square budget at cutoff 651. -/
theorem quarter_uniform_budget651 (hm : QuarterMomentBounds) :
    quarterUniformBudget 651 (554 / 10) (25378 / 10000) (quarterUniformAbel 651)
        (refinedReflectedEuler (1 : DirichletCharacter ℂ 1) 651) ≤
      4 * (65353 / 10000 : ℝ) := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 651 9 32 0 (64788 / 10000) = true from by
          decide +kernel)).2
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 651 0 (91490 / 100000000) 27
              25 =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl hp
  have hlog : Real.log 651 ≤ (64788 / 10000 : ℝ) := by
    norm_num only at hl ⊢
    exact hl
  have hpow : (651 : ℝ) ^ (-(27 / 25 : ℝ)) ≤ (91490 / 100000000 : ℝ) := by
    norm_num only at hp ⊢
    exact hp
  have hs : (255147 / 10000 : ℝ) ≤ Real.sqrt 651 := Real.le_sqrt_of_sq_le (by norm_num only)
  have ht : Real.sqrt 651 ≤ (255148 / 10000 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  have hb :=
    quarter_abel_envelope (X := 651) (U := 554 / 10) (L := 64788 / 10000) (Q := 91490 / 100000000)
      (s := 255147 / 10000) (t := 255148 / 10000) (P := 25378 / 10000) (by norm_num only)
      (by norm_num only) hlog hpow (by norm_num only) hs ht hm
  apply hb.trans
  norm_num only [quarterAbelEnvelope, quarterMomentPolynomial]

/-- GRH supplies a quarter-square rejecting prime for a uniform Korselt triple
in the cell. Its principal and Euler lower bounds are checked independently. -/
theorem quarter_uniform_529_554 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (529 / 10 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ 554 / 10) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (651 : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 := by nlinarith only [hlo]
  exact
    quarter_uniform_of_abel hn ho hu hGRH (X := 651) (U := 554 / 10) (S := 65353 / 10000) (P :=
      25378 / 10000) (H := refinedReflectedEuler (1 : DirichletCharacter ℂ 1) 651)
      (by norm_num only) le_rfl hhi hcut (le_of_lt target028_cell15_principal) quarter_euler_cap651
      (quarter_uniform_budget651
        (quarter_moment_bounds_of_integrals hGRH.riemann quarter_moment_integral_bounds))

end PseudoPrime.PrimeTestBounds.MillerRabin
