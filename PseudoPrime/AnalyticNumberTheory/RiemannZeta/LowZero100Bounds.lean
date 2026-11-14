/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.VecNotation

/-! # Abstract ordinate bracket conditions through height 100 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The rational lower endpoints used by the height-100 reciprocal check.
The data are internal to this arithmetic module and do not certify that any
zero belongs to an interval. -/
private def lowZero100Lower : Fin 29 → ℚ :=
  ![14473 / 1024, 10763 / 512, 25611 / 1024, 31155 / 1024, 33725 / 1024, 4811 / 128, 10475 / 256,
    22183 / 512, 49157 / 1024, 6371 / 128, 54241 / 1024, 7225 / 128, 60771 / 1024, 62291 / 1024,
    66675 / 1024, 68689 / 1024, 71215 / 1024, 18449 / 256, 77521 / 1024, 19749 / 256, 81241 / 1024,
    21225 / 256, 86769 / 1024, 89523 / 1024, 22735 / 256, 94711 / 1024, 48461 / 512, 98171 / 1024,
    101203 / 1024]

/-- The 29 ordinates lie above the rational lower brackets used by the
height-100 arithmetic certificate. This predicate is an input to the
reciprocal-sum bound; it does not assert the existence or completeness of
any zeta zeros. -/
def LowZero100LowerBounds (g : Fin 29 → ℝ) : Prop :=
  ∀ i, (lowZero100Lower i : ℝ) ≤ g i

/-- The 29 ordinates lie below the rational upper brackets used by the
height-100 arithmetic certificate. Each bracket has width `1/100`; this is
an input condition and does not assert the existence of zeta zeros. -/
def LowZero100UpperBounds (g : Fin 29 → ℝ) : Prop :=
  ∀ i, g i ≤ (lowZero100Lower i : ℝ) + 1 / 100

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
