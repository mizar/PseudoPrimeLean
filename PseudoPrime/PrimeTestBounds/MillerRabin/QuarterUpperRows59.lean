/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows59Block0
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows59Block1
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows59Block2
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows59Block3
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows59Block4
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows59Block5
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows59Block6

/-! # Combined principal upper rows at cutoff 59 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- All checked principal-weight rows at cutoff 59, combined without repeating the checks. -/
def quarterUpperRows59 : List QuarterUpperWeightRow :=
  quarterUpperRows59Block0 ++ quarterUpperRows59Block1 ++ quarterUpperRows59Block2 ++
    quarterUpperRows59Block3 ++
    quarterUpperRows59Block4 ++
    quarterUpperRows59Block5 ++
    quarterUpperRows59Block6

/-- All upper rows satisfy their checks, by combining independent block results. -/
theorem quarter_upper_rows59_check : quarterUpperRows59.all QuarterUpperWeightRow.check = true := by
  simp only [quarterUpperRows59, List.all_append, quarter_upper_rows59_block0_check,
    quarter_upper_rows59_block1_check, quarter_upper_rows59_block2_check,
    quarter_upper_rows59_block3_check, quarter_upper_rows59_block4_check,
    quarter_upper_rows59_block5_check, quarter_upper_rows59_block6_check, Bool.and_self]

end PseudoPrime.PrimeTestBounds.MillerRabin
