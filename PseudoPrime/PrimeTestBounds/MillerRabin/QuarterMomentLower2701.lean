/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentLower0
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentLower1
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentLower2
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentLower3
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentLower4
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentLower5
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentLower6
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentLower7
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentLower8
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentLower9
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentLower10
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentLower11
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentLower12
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentLower13
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentLower14
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentLower15
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentLower16
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentLower17
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentLower18
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentPrefix2701

/-! # Reflected moment lower certificates through 2701 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The lower endpoints correspond to the previously certified upper
endpoints, shifted down by one unit in the final decimal place. -/
def quarterMomentLower2701 : List ℚ :=
  (quarterMomentPower0.map (fun u ↦ u - 1 / 1000000000000)) ++
    ((quarterMomentPower1.map (fun u ↦ u - 1 / 1000000000000)) ++
      ((quarterMomentPower2.map (fun u ↦ u - 1 / 1000000000000)) ++
        ((quarterMomentPower3.map (fun u ↦ u - 1 / 1000000000000)) ++
          ((quarterMomentPower4.map (fun u ↦ u - 1 / 1000000000000)) ++
            ((quarterMomentPower5.map (fun u ↦ u - 1 / 1000000000000)) ++
              ((quarterMomentPower6.map (fun u ↦ u - 1 / 1000000000000)) ++
                ((quarterMomentPower7.map (fun u ↦ u - 1 / 1000000000000)) ++
                  ((quarterMomentPower8.map (fun u ↦ u - 1 / 1000000000000)) ++
                    ((quarterMomentPower9.map (fun u ↦ u - 1 / 1000000000000)) ++
                      ((quarterMomentPower10.map (fun u ↦ u - 1 / 1000000000000)) ++
                        ((quarterMomentPower11.map (fun u ↦ u - 1 / 1000000000000)) ++
                          ((quarterMomentPower12.map (fun u ↦ u - 1 / 1000000000000)) ++
                            ((quarterMomentPower13.map (fun u ↦ u - 1 / 1000000000000)) ++
                              ((quarterMomentPower14.map (fun u ↦ u - 1 / 1000000000000)) ++
                                ((quarterMomentPower15.map (fun u ↦ u - 1 / 1000000000000)) ++
                                  ((quarterMomentPower16.map (fun u ↦ u - 1 / 1000000000000)) ++
                                    ((quarterMomentPower17.map (fun u ↦ u - 1 / 1000000000000)) ++
                                      ((quarterMomentPower18.map
                                        (fun u ↦ u - 1 / 1000000000000))))))))))))))))))))

-- Concatenate the independently checked finite blocks without repeating their checks.
set_option maxRecDepth 20000 in
-- Definitional reduction connects the 428 existing rows and endpoint blocks.
/-- Every prime-power row through 2701 has a checked lower inverse-power
endpoint. The independent finite block results are concatenated. -/
theorem quarter_moment_lower2701_checked :
    List.Forall₂
      (fun r u ↦
        0 ≤ r.lo ∧
          0 ≤ u ∧
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck (r.p ^ (r.k + 1) : ℕ) u 1 79
              50 =
            true)
      (centerRowsBelow 2701) quarterMomentLower2701 := by
  have h0 := quarter_moment_lower_check_sound quarter_moment_lower0_check
  have h1 := quarter_moment_lower_check_sound quarter_moment_lower1_check
  have h2 := quarter_moment_lower_check_sound quarter_moment_lower2_check
  have h3 := quarter_moment_lower_check_sound quarter_moment_lower3_check
  have h4 := quarter_moment_lower_check_sound quarter_moment_lower4_check
  have h5 := quarter_moment_lower_check_sound quarter_moment_lower5_check
  have h6 := quarter_moment_lower_check_sound quarter_moment_lower6_check
  have h7 := quarter_moment_lower_check_sound quarter_moment_lower7_check
  have h8 := quarter_moment_lower_check_sound quarter_moment_lower8_check
  have h9 := quarter_moment_lower_check_sound quarter_moment_lower9_check
  have h10 := quarter_moment_lower_check_sound quarter_moment_lower10_check
  have h11 := quarter_moment_lower_check_sound quarter_moment_lower11_check
  have h12 := quarter_moment_lower_check_sound quarter_moment_lower12_check
  have h13 := quarter_moment_lower_check_sound quarter_moment_lower13_check
  have h14 := quarter_moment_lower_check_sound quarter_moment_lower14_check
  have h15 := quarter_moment_lower_check_sound quarter_moment_lower15_check
  have h16 := quarter_moment_lower_check_sound quarter_moment_lower16_check
  have h17 := quarter_moment_lower_check_sound quarter_moment_lower17_check
  have h18 := quarter_moment_lower_check_sound quarter_moment_lower18_check
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

/-- The certified lower endpoints bound every nonnegative logarithmic
Mangoldt moment over the prime powers through 2701. -/
theorem quarter_moment_lower2701 (k : ℕ) :
    (((List.zipWith (fun r u ↦ r.lo * (((r.k + 1 : ℕ) : ℚ) * r.lo) ^ k * u) (centerRowsBelow 2701)
              quarterMomentLower2701).sum :
          ℚ) :
        ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 2701, quarterMangoldtMoment k n := by
  exact
    quarter_moment_prefix_lower (by decide) quarterMomentLower2701 k
      quarter_moment_lower2701_checked

end PseudoPrime.PrimeTestBounds.MillerRabin
