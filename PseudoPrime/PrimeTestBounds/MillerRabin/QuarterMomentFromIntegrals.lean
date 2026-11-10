/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentInfiniteTail
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPsi2701
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentPrefixCap0
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentPrefixCap1
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentPrefixCap2
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentPrefixCap3
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentPrefixCap4
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentPrefixCap5

/-! # Moment caps from finite prefixes and tail integrals -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Explicit upper bounds for the six finite Mangoldt moment prefixes. -/
noncomputable def quarterMomentPrefixCap : ℕ → ℝ
  | 0 => 1223136 / 1000000
  | 1 => 2663413 / 1000000
  | 2 => 8499304 / 1000000
  | 3 => 35560865 / 1000000
  | 4 => 176805657 / 1000000
  | 5 => 981503921 / 1000000
  | _ => 0

/-- Outward rational upper endpoints for the six nonnegative tail integrals. -/
noncomputable def quarterMomentIntegralCap : ℕ → ℝ
  | 0 => 18914 / 1000000
  | 1 => 181384 / 1000000
  | 2 => 1794125 / 1000000
  | 3 => 18441302 / 1000000
  | 4 => 198774483 / 1000000
  | 5 => 2270274502 / 1000000
  | _ => 0

/-- The six explicit tail-integral estimates needed to complete the moment
caps. Their integrands are nonnegative and their convergence is already proved. -/
def QuarterMomentIntegralBounds : Prop :=
  ∀ k < 6, (∫ t in Set.Ioi (2701 : ℝ), quarterMomentTailIntegrand k t) ≤ quarterMomentIntegralCap k

/-- Rational upper envelope for the retained Chebyshev boundary correction. -/
noncomputable def quarterMomentBoundaryCap (k : ℕ) : ℝ :=
  (3786092 / 1000000000000 : ℝ) * (7901378 / 1000000 : ℝ) ^ k *
    (2701 + (519711459 / 10000000 : ℝ) * (72091017 / 10000000 : ℝ) - (2702944613 / 1000000 : ℝ))

/-- The six finite moment prefixes satisfy their independently checked caps. -/
theorem quarter_moment_prefix_cap {k : ℕ} (hk : k < 6) :
    (∑ n ∈ Finset.Ioc 0 2701, quarterMangoldtMoment k n) ≤ quarterMomentPrefixCap k := by
  interval_cases k
  · simpa only [quarterMomentPrefixCap] using quarter_moment_prefix2701_real0
  · simpa only [quarterMomentPrefixCap] using quarter_moment_prefix2701_real1
  · simpa only [quarterMomentPrefixCap] using quarter_moment_prefix2701_real2
  · simpa only [quarterMomentPrefixCap] using quarter_moment_prefix2701_real3
  · simpa only [quarterMomentPrefixCap] using quarter_moment_prefix2701_real4
  · simpa only [quarterMomentPrefixCap] using quarter_moment_prefix2701_real5

/-- The retained lower Chebyshev boundary, checked logarithm and checked
power endpoints give a uniform upper bound for each boundary correction. -/
theorem quarter_moment_boundary_upper (k : ℕ) :
    AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight (79 / 50) k 2701 *
        (2701 + (2701 : ℝ) ^ (3 / 4 : ℝ) - Chebyshev.psi 2701) ≤
      quarterMomentBoundaryCap k := by
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 2701 12 32 0 (7901378 / 1000000) = true from by
          decide +kernel)).2
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 2701 0
              (3786092 / 1000000000000) 79 50 =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog hp
  have hlog' : Real.log 2701 ≤ (7901378 / 1000000 : ℝ) := by
    norm_num only at hlog ⊢
    exact hlog
  have hp' : (2701 : ℝ) ^ (-(79 / 50 : ℝ)) ≤ (3786092 / 1000000000000 : ℝ) := by
    norm_num only at hp ⊢
    exact hp
  have hs : Real.sqrt 2701 ≤ (519711459 / 10000000 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  have hss : Real.sqrt (Real.sqrt 2701) ≤ (72091017 / 10000000 : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by norm_num only, hs.trans (by norm_num only)⟩
  have hroot :=
    mul_le_mul hs hss (Real.sqrt_nonneg _) (by norm_num only : (0 : ℝ) ≤ 519711459 / 10000000)
  have hpow0 : 0 ≤ (2701 : ℝ) ^ (-(79 / 50 : ℝ)) := Real.rpow_nonneg (by norm_num only) _
  have hlog0 : 0 ≤ Real.log 2701 := Real.log_nonneg (by norm_num only)
  have hw :=
    mul_le_mul hp' (pow_le_pow_left₀ hlog0 hlog' k) (pow_nonneg hlog0 k)
      (by norm_num only : (0 : ℝ) ≤ 3786092 / 1000000000000)
  have hw0 : 0 ≤ AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight (79 / 50) k 2701 := by
    dsimp only [AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight]
    positivity
  have hb :
    2701 + (2701 : ℝ) ^ (3 / 4 : ℝ) - Chebyshev.psi 2701 ≤
      2701 + (519711459 / 10000000 : ℝ) * (72091017 / 10000000 : ℝ) - 2702944613 / 1000000 := by
    rw [← quarter_sqrt_product (by norm_num only : (0 : ℝ) ≤ 2701)]
    linarith only [hroot, quarter_psi2701_lower]
  have hb0 :
    0 ≤ 2701 + (519711459 / 10000000 : ℝ) * (72091017 / 10000000 : ℝ) - 2702944613 / 1000000 := by
    norm_num only
  dsimp only [quarterMomentBoundaryCap]
  have h := mul_le_mul_of_nonneg_left hb hw0
  have hw' := mul_le_mul_of_nonneg_right hw hb0
  dsimp only [AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight] at h ⊢
  exact h.trans hw'

/-- The finite prefix, boundary and proposed integral caps fit within each
of the six target Mangoldt moment caps. -/
theorem quarter_moment_cap_arithmetic {k : ℕ} (hk : k < 6) :
    quarterMomentPrefixCap k + quarterMomentBoundaryCap k + quarterMomentIntegralCap k ≤
      quarterMomentCap k := by
  interval_cases k <;>
    norm_num only [quarterMomentPrefixCap, quarterMomentBoundaryCap, quarterMomentIntegralCap,
      quarterMomentCap]

/-- Under RH, the six tail-integral estimates imply all six Mangoldt moment
caps. Finite prefixes and the Chebyshev boundary are already kernel certified. -/
theorem quarter_moment_bounds_of_integrals (hRH : RiemannHypothesis)
    (hi : QuarterMomentIntegralBounds) : QuarterMomentBounds := by
  intro k hk
  have h := quarter_moment_infinite_upper hRH hk
  have hp := quarter_moment_prefix_cap hk
  have hb := quarter_moment_boundary_upper k
  have he := hi k hk
  have ha := quarter_moment_cap_arithmetic hk
  linarith only [h, hp, hb, he, ha]

end PseudoPrime.PrimeTestBounds.MillerRabin
