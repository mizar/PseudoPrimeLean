/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Cell20
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerCap949
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAbelEnvelope
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentIntegralCaps

/-! # Uniform triple cell at cutoff 949 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The numerical endpoint estimates and the six moment bounds control the
quarter-square budget at cutoff 949. -/
theorem quarter_uniform_budget949 (hm : QuarterMomentBounds) :
    quarterUniformBudget 949 (659 / 10) (26115 / 10000) (quarterUniformAbel 949)
        (refinedReflectedEuler (1 : DirichletCharacter ℂ 1) 949) ≤
      4 * (78457 / 10000 : ℝ) := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 949 10 32 0 (68557 / 10000) = true from by
          decide +kernel)).2
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 949 0 (60899 / 100000000) 27
              25 =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl hp
  have hlog : Real.log 949 ≤ (68557 / 10000 : ℝ) := by
    norm_num only at hl ⊢
    exact hl
  have hpow : (949 : ℝ) ^ (-(27 / 25 : ℝ)) ≤ (60899 / 100000000 : ℝ) := by
    norm_num only at hp ⊢
    exact hp
  have hs : (308058 / 10000 : ℝ) ≤ Real.sqrt 949 := Real.le_sqrt_of_sq_le (by norm_num only)
  have ht : Real.sqrt 949 ≤ (308059 / 10000 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  have hb :=
    quarter_abel_envelope (X := 949) (U := 659 / 10) (L := 68557 / 10000) (Q := 60899 / 100000000)
      (s := 308058 / 10000) (t := 308059 / 10000) (P := 26115 / 10000) (by norm_num only)
      (by norm_num only) hlog hpow (by norm_num only) hs ht hm
  apply hb.trans
  norm_num only [quarterAbelEnvelope, quarterMomentPolynomial]

/-- GRH supplies a quarter-square rejecting prime for a uniform Korselt triple
in the cell. Its principal and Euler lower bounds are checked independently. -/
theorem quarter_uniform_643_659 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (643 / 10 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ 659 / 10) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (949 : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 := by nlinarith only [hlo]
  exact
    quarter_uniform_of_abel hn ho hu hGRH (X := 949) (U := 659 / 10) (S := 78457 / 10000) (P :=
      26115 / 10000) (H := refinedReflectedEuler (1 : DirichletCharacter ℂ 1) 949)
      (by norm_num only) le_rfl hhi hcut (le_of_lt target028_cell20_principal) quarter_euler_cap949
      (quarter_uniform_budget949
        (quarter_moment_bounds_of_integrals hGRH.riemann quarter_moment_integral_bounds))

end PseudoPrime.PrimeTestBounds.MillerRabin
