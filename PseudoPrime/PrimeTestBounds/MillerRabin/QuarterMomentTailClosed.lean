/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformTailCap
public import PseudoPrime.Analysis.LogPowerTailIntegral

/-! Closed logarithmic-power form of the variable Euler moment tail. -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At any cutoff at least one, the moment-tail integral is the sum of two explicit logarithmic
power tails. The formula allows exact interval certification of the Euler envelope. -/
theorem quarter_moment_integral_from (k : ℕ) {a : ℝ} (ha : 1 ≤ a) :
    (∫ t in Set.Ioi a, quarterMomentTailIntegrand k t) =
      a ^ (-(29 / 50 : ℝ)) * Analysis.logPowerTailPoly (29 / 50) k (Real.log a) +
        (3 / 4 : ℝ) *
          (a ^ (-(83 / 100 : ℝ)) * Analysis.logPowerTailPoly (83 / 100) k (Real.log a)) := by
  have hi1 := Analysis.log_power_tail_integrable (r := 29 / 50) (a := a) (by norm_num only) ha k
  have hi2 := Analysis.log_power_tail_integrable (r := 83 / 100) (a := a) (by norm_num only) ha k
  have he :
    ∀ t ∈ Set.Ioi a,
      quarterMomentTailIntegrand k t =
        Real.log t ^ k * t ^ (-(29 / 50 : ℝ) - 1) +
          (3 / 4 : ℝ) * (Real.log t ^ k * t ^ (-(83 / 100 : ℝ) - 1)) := by
    intro t ht
    have ht0 : 0 < t := (zero_lt_one.trans_le ha).trans ht
    have hp : t ^ (-(1 / 4 : ℝ)) * t ^ (-(79 / 50 : ℝ)) = t ^ (-(83 / 100 : ℝ) - 1) := by
      rw [← Real.rpow_add ht0]
      norm_num only
    have hp1 : (-(29 / 50 : ℝ) - 1) = -(79 / 50 : ℝ) := by norm_num only
    dsimp only [quarterMomentTailIntegrand, AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight]
    rw [hp1]
    calc
      _ =
          Real.log t ^ k * t ^ (-(79 / 50 : ℝ)) +
            (3 / 4 : ℝ) * (Real.log t ^ k * (t ^ (-(1 / 4 : ℝ)) * t ^ (-(79 / 50 : ℝ)))) :=
        by ring
      _ = _ := by rw [hp]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi he,
    MeasureTheory.integral_add hi1 (hi2.const_mul (3 / 4 : ℝ)), MeasureTheory.integral_const_mul,
    Analysis.log_power_tail_integral (r := 29 / 50) (a := a) (by norm_num only) ha,
    Analysis.log_power_tail_integral (r := 83 / 100) (a := a) (by norm_num only) ha]

/-- Closed form of one psi-free moment-tail envelope at cutoff `a`. It consists of the cutoff
correction and the two logarithmic-power tail polynomials. -/
noncomputable def quarterMomentClosedTail (k : ℕ) (a : ℝ) : ℝ :=
  2 * AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight (79 / 50) k a * a ^ (3 / 4 : ℝ) +
    a ^ (-(29 / 50 : ℝ)) * Analysis.logPowerTailPoly (29 / 50) k (Real.log a) +
    (3 / 4 : ℝ) * (a ^ (-(83 / 100 : ℝ)) * Analysis.logPowerTailPoly (83 / 100) k (Real.log a))

/-- At cutoffs at least one, the clean moment-tail envelope equals its explicit closed form.
The equality exposes the expression to rational interval estimates. -/
theorem quarter_moment_clean_eq (k : ℕ) {a : ℝ} (ha : 1 ≤ a) :
    quarterMomentCleanTail k a = quarterMomentClosedTail k a := by
  dsimp only [quarterMomentCleanTail, quarterMomentClosedTail]
  rw [quarter_moment_integral_from k ha]
  ring

/-- The closed three-moment Euler-tail envelope, with no improper integrals or Chebyshev
values. It can be evaluated using rational bounds on the logarithm and real powers. -/
noncomputable def quarterEulerClosedTailCap (a : ℝ) : ℝ :=
  (3 / 8 : ℝ) * quarterMomentClosedTail 0 a + (81 / 200 : ℝ) * quarterMomentClosedTail 1 a +
    (729 / 5000 : ℝ) * quarterMomentClosedTail 2 a

/-- For cutoffs at least one, the clean Euler envelope is its closed three-moment expression. -/
theorem quarter_euler_clean_closed_eq {a : ℝ} (ha : 1 ≤ a) :
    quarterEulerCleanTailCap a = quarterEulerClosedTailCap a := by
  dsimp only [quarterEulerCleanTailCap, quarterEulerClosedTailCap]
  rw [quarter_moment_clean_eq 0 ha, quarter_moment_clean_eq 1 ha, quarter_moment_clean_eq 2 ha]

/-- Under RH and prime-level triviality, the three-character zero mass is bounded by the sharp
Euler constant and the closed Euler-tail envelope for every real cutoff at least 625. -/
theorem quarter_uniform_mass_tail_closed {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hRH : RiemannHypothesis) (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q)
    (c : DirichletCharacter ℂ r) (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hRA : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis a)
    (hRB : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis b)
    (hRC : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis c) (hpA : a.IsPrimitive)
    (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1) (hnC : c ≠ 1)
    (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) (heA : a.Even) (heB : b.Even) (heC : c.Even)
    {X : ℝ} (hX : 625 ≤ X) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) :
    sixMass a + sixMass b + sixMass c <
      (3 / 16 : ℝ) * (Real.log p + Real.log q + Real.log r) +
        -(3117 / 400 : ℝ) * (27 / 25 : ℝ) ^ 5 +
        4 * quarterEulerClosedTailCap X := by
  have h :=
    quarter_uniform_mass_tail_clean hRH a b c hP hQ hR hRA hRB hRC hpA hpB hpC hnA hnB hnC hiA hiB
      hiC heA heB heC hX ht hA hB hC
  rw [quarter_euler_clean_closed_eq (by linarith only [hX])] at h
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
