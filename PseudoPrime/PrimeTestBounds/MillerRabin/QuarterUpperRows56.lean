/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows56First
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows56Block1
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows56Block2
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows56Block3
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows56Block4
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows56Block5
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows56Block6
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows56Block7
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows56Block8
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows56Block9
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows56Block10
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows56Block11
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows56Block12
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows56Block13
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows56Block14
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows56Block15

/-! # Combined principal upper rows at cutoff 56 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- All checked principal-weight rows at cutoff 56, combined without repeating the checks. -/
def quarterUpperRows56 : List QuarterUpperWeightRow :=
  quarterUpperRows56First ++ quarterUpperRows56Block1 ++ quarterUpperRows56Block2 ++
    quarterUpperRows56Block3 ++
    quarterUpperRows56Block4 ++
    quarterUpperRows56Block5 ++
    quarterUpperRows56Block6 ++
    quarterUpperRows56Block7 ++
    quarterUpperRows56Block8 ++
    quarterUpperRows56Block9 ++
    quarterUpperRows56Block10 ++
    quarterUpperRows56Block11 ++
    quarterUpperRows56Block12 ++
    quarterUpperRows56Block13 ++
    quarterUpperRows56Block14 ++
    quarterUpperRows56Block15

/-- All upper rows satisfy their checks, by combining the independent block results. -/
theorem quarter_upper_rows56_check : quarterUpperRows56.all QuarterUpperWeightRow.check = true := by
  simp only [quarterUpperRows56, List.all_append, quarter_upper_rows56_first_check,
    quarter_upper_rows56_block1_check, quarter_upper_rows56_block2_check,
    quarter_upper_rows56_block3_check, quarter_upper_rows56_block4_check,
    quarter_upper_rows56_block5_check, quarter_upper_rows56_block6_check,
    quarter_upper_rows56_block7_check, quarter_upper_rows56_block8_check,
    quarter_upper_rows56_block9_check, quarter_upper_rows56_block10_check,
    quarter_upper_rows56_block11_check, quarter_upper_rows56_block12_check,
    quarter_upper_rows56_block13_check, quarter_upper_rows56_block14_check,
    quarter_upper_rows56_block15_check, Bool.and_self]

end PseudoPrime.PrimeTestBounds.MillerRabin
