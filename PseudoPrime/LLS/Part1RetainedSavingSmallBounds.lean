/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Part1SmallRadiusBounds
public import PseudoPrime.Analysis.LogTaylorBounds

/-! # Shared rational logarithm checks for finite Part 1 radius bounds -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Claim: rational intervals bound log(6), log(17917/10000) and log(5).
Proof: exact kernel arithmetic. Role: quantify the small-modulus retained-saving comparisons. -/
theorem retained_saving_small_log_checks :
    Analysis.rationalLogIntervalCheck 6 3 20 (17917 / 10000) 2 = true ∧
      Analysis.rationalLogIntervalCheck (17917 / 10000) 1 20 (583 / 1000) 1 = true ∧
      Analysis.rationalLogIntervalCheck 5 3 20 1 (17 / 10) = true := by
  decide +kernel

end PseudoPrime.LLS
