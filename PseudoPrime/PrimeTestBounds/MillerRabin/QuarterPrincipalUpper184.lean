/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalEulerUpper
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows184Block0
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows184Block1
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows184Block2
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows184Block3
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows184Block4
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows184Block5
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows184Block6
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows184Block7
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows184Block8
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows184Block9
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows184Block10
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows184Block11
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows184Block12
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows184Block13
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows184Block14
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows184Block15
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows184Block16

/-! # Principal upper bound at cutoff 184 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The combined independent upper-weight certificates at cutoff 184. -/
def quarterUpperRows184 : List QuarterUpperWeightRow :=
  quarterUpperRows184Block0 ++ quarterUpperRows184Block1 ++ quarterUpperRows184Block2 ++
    quarterUpperRows184Block3 ++
    quarterUpperRows184Block4 ++
    quarterUpperRows184Block5 ++
    quarterUpperRows184Block6 ++
    quarterUpperRows184Block7 ++
    quarterUpperRows184Block8 ++
    quarterUpperRows184Block9 ++
    quarterUpperRows184Block10 ++
    quarterUpperRows184Block11 ++
    quarterUpperRows184Block12 ++
    quarterUpperRows184Block13 ++
    quarterUpperRows184Block14 ++
    quarterUpperRows184Block15 ++
    quarterUpperRows184Block16

/-- Each upper-weight row is certified by its independent block check. -/
theorem quarter_upper_rows184_check :
    quarterUpperRows184.all QuarterUpperWeightRow.check = true := by
  simp only [quarterUpperRows184, List.all_append, quarter_upper_rows184_block0_check,
    quarter_upper_rows184_block1_check, quarter_upper_rows184_block2_check,
    quarter_upper_rows184_block3_check, quarter_upper_rows184_block4_check,
    quarter_upper_rows184_block5_check, quarter_upper_rows184_block6_check,
    quarter_upper_rows184_block7_check, quarter_upper_rows184_block8_check,
    quarter_upper_rows184_block9_check, quarter_upper_rows184_block10_check,
    quarter_upper_rows184_block11_check, quarter_upper_rows184_block12_check,
    quarter_upper_rows184_block13_check, quarter_upper_rows184_block14_check,
    quarter_upper_rows184_block15_check, quarter_upper_rows184_block16_check, Bool.and_self]

-- Reduction matches 410 index pairs against the existing prime-power support.
set_option maxRecDepth 30000 in
-- This checks only indices and cutoff, not the numerical row certificates.
/-- The upper weights align with the certified Euler rows through 2576. -/
theorem quarter_upper_rows184_align :
    quarterUpperAlignmentCheck 184 (centerRowsBelow 2576) quarterUpperRows184 = true := by
  decide +kernel

-- The kernel sums the rational products of existing log and weight endpoints.
set_option maxRecDepth 30000 in
-- Exact rational arithmetic checks the aggregate principal upper bound.
/-- The rational upper-row sum is at most 4.6485. -/
theorem quarter_upper_rows184_sum :
    (List.zipWith (fun r w ↦ r.hi * ((w.weight : ℚ) / 1000000)) (centerRowsBelow 2576)
          quarterUpperRows184).sum ≤
      (9297 / 2000 : ℚ) := by
  decide +kernel

/-- At cutoff 184 the full principal series is at most 4.6485. -/
theorem quarter_principal_upper184_explicit :
    (∑' n : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 184 n).re ≤
      (9297 / 2000 : ℝ) := by
  have h :=
    quarter_principal_euler_prefix_upper (X := 184) (B := 2576) (by norm_num only) (by decide)
      (by norm_num only [Nat.floor_ofNat]) quarterUpperRows184 quarter_upper_rows184_check
      (quarter_upper_alignment_sound quarter_upper_rows184_align)
  have hs := (Rat.cast_le (K := ℝ)).mpr quarter_upper_rows184_sum
  simp only [Rat.cast_div, Rat.cast_ofNat] at hs
  exact h.trans hs

end PseudoPrime.PrimeTestBounds.MillerRabin
