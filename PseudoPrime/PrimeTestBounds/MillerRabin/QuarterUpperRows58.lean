/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows58Block0
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows58Block1
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows58Block2
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows58Block3
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows58Block4
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows58Block5
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows58Block6

/-! # Combined principal upper rows at cutoff 58 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- All checked principal-weight rows at cutoff 58, combined without repeating the checks. -/
def quarterUpperRows58 : List QuarterUpperWeightRow :=
  quarterUpperRows58Block0 ++ quarterUpperRows58Block1 ++ quarterUpperRows58Block2 ++
    quarterUpperRows58Block3 ++
    quarterUpperRows58Block4 ++
    quarterUpperRows58Block5 ++
    quarterUpperRows58Block6

/-- All upper rows satisfy their checks, by combining independent block results. -/
theorem quarter_upper_rows58_check : quarterUpperRows58.all QuarterUpperWeightRow.check = true := by
  simp only [quarterUpperRows58, List.all_append, quarter_upper_rows58_block0_check,
    quarter_upper_rows58_block1_check, quarter_upper_rows58_block2_check,
    quarter_upper_rows58_block3_check, quarter_upper_rows58_block4_check,
    quarter_upper_rows58_block5_check, quarter_upper_rows58_block6_check, Bool.and_self]

end PseudoPrime.PrimeTestBounds.MillerRabin
