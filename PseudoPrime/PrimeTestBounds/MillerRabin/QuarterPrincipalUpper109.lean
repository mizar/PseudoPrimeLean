/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalEulerUpper
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows109Block0
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows109Block1
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows109Block2
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows109Block3
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows109Block4
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows109Block5
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows109Block6
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows109Block7
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows109Block8
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows109Block9
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows109Block10

/-! # Principal upper bound at cutoff 109 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The combined independent upper-weight certificates at cutoff 109. -/
def quarterUpperRows109 : List QuarterUpperWeightRow :=
  quarterUpperRows109Block0 ++ quarterUpperRows109Block1 ++ quarterUpperRows109Block2 ++
    quarterUpperRows109Block3 ++
    quarterUpperRows109Block4 ++
    quarterUpperRows109Block5 ++
    quarterUpperRows109Block6 ++
    quarterUpperRows109Block7 ++
    quarterUpperRows109Block8 ++
    quarterUpperRows109Block9 ++
    quarterUpperRows109Block10

/-- Each upper-weight row is certified by its independent block check. -/
theorem quarter_upper_rows109_check :
    quarterUpperRows109.all QuarterUpperWeightRow.check = true := by
  simp only [quarterUpperRows109, List.all_append, quarter_upper_rows109_block0_check,
    quarter_upper_rows109_block1_check, quarter_upper_rows109_block2_check,
    quarter_upper_rows109_block3_check, quarter_upper_rows109_block4_check,
    quarter_upper_rows109_block5_check, quarter_upper_rows109_block6_check,
    quarter_upper_rows109_block7_check, quarter_upper_rows109_block8_check,
    quarter_upper_rows109_block9_check, quarter_upper_rows109_block10_check, Bool.and_self]

-- Reduction matches 269 index pairs against the existing prime-power support.
set_option maxRecDepth 30000 in
-- This checks only indices and cutoff, not the numerical row certificates.
/-- The upper weights align with the certified Euler rows through 1526. -/
theorem quarter_upper_rows109_align :
    quarterUpperAlignmentCheck 109 (centerRowsBelow 1526) quarterUpperRows109 = true := by
  decide +kernel

-- The kernel sums the rational products of existing log and weight endpoints.
set_option maxRecDepth 30000 in
-- Exact rational arithmetic checks the aggregate principal upper bound.
/-- The rational upper-row sum is at most 3.5102. -/
theorem quarter_upper_rows109_sum :
    (List.zipWith (fun r w ↦ r.hi * ((w.weight : ℚ) / 1000000)) (centerRowsBelow 1526)
          quarterUpperRows109).sum ≤
      (35102 / 10000 : ℚ) := by
  decide +kernel

/-- At cutoff 109 the full principal series is at most 3.5102. -/
theorem quarter_principal_upper109_explicit :
    (∑' n : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 109 n).re ≤
      (35102 / 10000 : ℝ) := by
  have h :=
    quarter_principal_euler_prefix_upper (X := 109) (B := 1526) (by norm_num only) (by decide)
      (by norm_num only [Nat.floor_ofNat]) quarterUpperRows109 quarter_upper_rows109_check
      (quarter_upper_alignment_sound quarter_upper_rows109_align)
  have hs := (Rat.cast_le (K := ℝ)).mpr quarter_upper_rows109_sum
  simp only [Rat.cast_div, Rat.cast_ofNat] at hs
  exact h.trans hs

end PseudoPrime.PrimeTestBounds.MillerRabin
