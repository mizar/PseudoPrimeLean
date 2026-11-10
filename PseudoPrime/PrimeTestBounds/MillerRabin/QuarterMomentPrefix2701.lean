/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentPower0
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentPower1
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentPower2
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentPower3
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentPower4
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentPower5
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentPower6
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentPower7
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentPower8
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentPower9
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentPower10
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentPower11
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentPower12
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentPower13
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentPower14
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentPower15
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentPower16
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentPower17
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentPower18

/-! # Combined moment-power certificates through 2701 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The upper power endpoints for the 428 prime powers through 2701. -/
def quarterMomentPowers2701 : List ℚ :=
  quarterMomentPower0 ++ quarterMomentPower1 ++ quarterMomentPower2 ++ quarterMomentPower3 ++
    quarterMomentPower4 ++
    quarterMomentPower5 ++
    quarterMomentPower6 ++
    quarterMomentPower7 ++
    quarterMomentPower8 ++
    quarterMomentPower9 ++
    quarterMomentPower10 ++
    quarterMomentPower11 ++
    quarterMomentPower12 ++
    quarterMomentPower13 ++
    quarterMomentPower14 ++
    quarterMomentPower15 ++
    quarterMomentPower16 ++
    quarterMomentPower17 ++
    quarterMomentPower18

-- The list equality unfolds the existing cutoff support, without repeating row checks.
set_option maxRecDepth 30000 in
-- The relation concatenates independently certified finite blocks.
/-- Every prime-power row through 2701 has its independently checked power endpoint. -/
theorem quarter_moment_powers2701_checked :
    List.Forall₂
      (fun r u ↦
        AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck (r.p ^ (r.k + 1) : ℕ) 0 u 79 50 =
          true)
      (centerRowsBelow 2701) quarterMomentPowers2701 := by
  have h0 := quarter_moment_power_check_sound quarter_moment_power0_check
  have h1 := quarter_moment_power_check_sound quarter_moment_power1_check
  have h2 := quarter_moment_power_check_sound quarter_moment_power2_check
  have h3 := quarter_moment_power_check_sound quarter_moment_power3_check
  have h4 := quarter_moment_power_check_sound quarter_moment_power4_check
  have h5 := quarter_moment_power_check_sound quarter_moment_power5_check
  have h6 := quarter_moment_power_check_sound quarter_moment_power6_check
  have h7 := quarter_moment_power_check_sound quarter_moment_power7_check
  have h8 := quarter_moment_power_check_sound quarter_moment_power8_check
  have h9 := quarter_moment_power_check_sound quarter_moment_power9_check
  have h10 := quarter_moment_power_check_sound quarter_moment_power10_check
  have h11 := quarter_moment_power_check_sound quarter_moment_power11_check
  have h12 := quarter_moment_power_check_sound quarter_moment_power12_check
  have h13 := quarter_moment_power_check_sound quarter_moment_power13_check
  have h14 := quarter_moment_power_check_sound quarter_moment_power14_check
  have h15 := quarter_moment_power_check_sound quarter_moment_power15_check
  have h16 := quarter_moment_power_check_sound quarter_moment_power16_check
  have h17 := quarter_moment_power_check_sound quarter_moment_power17_check
  have h18 := quarter_moment_power_check_sound quarter_moment_power18_check
  have h17s := List.rel_append h17 h18
  have h16s := List.rel_append h16 h17s
  have h15s := List.rel_append h15 h16s
  have h14s := List.rel_append h14 h15s
  have h13s := List.rel_append h13 h14s
  have h12s := List.rel_append h12 h13s
  have h11s := List.rel_append h11 h12s
  have h10s := List.rel_append h10 h11s
  have h9s := List.rel_append h9 h10s
  have h8s := List.rel_append h8 h9s
  have h7s := List.rel_append h7 h8s
  have h6s := List.rel_append h6 h7s
  have h5s := List.rel_append h5 h6s
  have h4s := List.rel_append h4 h5s
  have h3s := List.rel_append h3 h4s
  have h2s := List.rel_append h2 h3s
  have h1s := List.rel_append h1 h2s
  have h0s := List.rel_append h0 h1s
  exact h0s

/-- The finite prefix of any Mangoldt moment is bounded by the certified
rational endpoint sum. The result applies separately to all six degrees. -/
theorem quarter_moment_prefix2701_upper (k : ℕ) :
    (∑ n ∈ Finset.Ioc 0 2701, quarterMangoldtMoment k n) ≤
      (((List.zipWith (fun r u ↦ r.hi * (((r.k + 1 : ℕ) : ℚ) * r.hi) ^ k * u) (centerRowsBelow 2701)
              quarterMomentPowers2701).sum :
          ℚ) :
        ℝ) := by
  exact
    quarter_moment_prefix_upper (by decide) quarterMomentPowers2701 k
      quarter_moment_powers2701_checked

end PseudoPrime.PrimeTestBounds.MillerRabin
