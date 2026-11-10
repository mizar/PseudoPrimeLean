/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalEulerUpper
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows141Block0
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows141Block1
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows141Block2
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows141Block3
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows141Block4
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows141Block5
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows141Block6
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows141Block7
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows141Block8
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows141Block9
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows141Block10
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows141Block11
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows141Block12
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows141Block13

/-! # Principal upper bound at cutoff 141 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The combined independent upper-weight certificates at cutoff 141. -/
def quarterUpperRows141 : List QuarterUpperWeightRow :=
  quarterUpperRows141Block0 ++ quarterUpperRows141Block1 ++ quarterUpperRows141Block2 ++
    quarterUpperRows141Block3 ++
    quarterUpperRows141Block4 ++
    quarterUpperRows141Block5 ++
    quarterUpperRows141Block6 ++
    quarterUpperRows141Block7 ++
    quarterUpperRows141Block8 ++
    quarterUpperRows141Block9 ++
    quarterUpperRows141Block10 ++
    quarterUpperRows141Block11 ++
    quarterUpperRows141Block12 ++
    quarterUpperRows141Block13

/-- Each upper-weight row is certified by its independent block check. -/
theorem quarter_upper_rows141_check :
    quarterUpperRows141.all QuarterUpperWeightRow.check = true := by
  simp only [quarterUpperRows141, List.all_append, quarter_upper_rows141_block0_check,
    quarter_upper_rows141_block1_check, quarter_upper_rows141_block2_check,
    quarter_upper_rows141_block3_check, quarter_upper_rows141_block4_check,
    quarter_upper_rows141_block5_check, quarter_upper_rows141_block6_check,
    quarter_upper_rows141_block7_check, quarter_upper_rows141_block8_check,
    quarter_upper_rows141_block9_check, quarter_upper_rows141_block10_check,
    quarter_upper_rows141_block11_check, quarter_upper_rows141_block12_check,
    quarter_upper_rows141_block13_check, Bool.and_self]

-- Reduction matches 328 index pairs against the existing prime-power support.
set_option maxRecDepth 30000 in
-- This checks only indices and cutoff, not the numerical row certificates.
/-- The upper weights align with the certified Euler rows through 1974. -/
theorem quarter_upper_rows141_align :
    quarterUpperAlignmentCheck 141 (centerRowsBelow 1974) quarterUpperRows141 = true := by
  decide +kernel

-- The kernel sums the rational products of existing log and weight endpoints.
set_option maxRecDepth 30000 in
-- Exact rational arithmetic checks the aggregate principal upper bound.
/-- The rational upper-row sum is at most 4.0348. -/
theorem quarter_upper_rows141_sum :
    (List.zipWith (fun r w ↦ r.hi * ((w.weight : ℚ) / 1000000)) (centerRowsBelow 1974)
          quarterUpperRows141).sum ≤
      (10087 / 2500 : ℚ) := by
  decide +kernel

/-- At cutoff 141 the full principal series is at most 4.0348. -/
theorem quarter_principal_upper141_explicit :
    (∑' n : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 141 n).re ≤
      (10087 / 2500 : ℝ) := by
  have h :=
    quarter_principal_euler_prefix_upper (X := 141) (B := 1974) (by norm_num only) (by decide)
      (by norm_num only [Nat.floor_ofNat]) quarterUpperRows141 quarter_upper_rows141_check
      (quarter_upper_alignment_sound quarter_upper_rows141_align)
  have hs := (Rat.cast_le (K := ℝ)).mpr quarter_upper_rows141_sum
  simp only [Rat.cast_div, Rat.cast_ofNat] at hs
  exact h.trans hs

end PseudoPrime.PrimeTestBounds.MillerRabin
