/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.Scan
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import PseudoPrime.Analysis.HighPrecisionLogBounds

/-! # Certified logarithm grid for the joint prime walk -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- Binary shift and Taylor depth chosen for each logarithm proof. -/
private def row : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | 1 => (0, 8)
  | 2 => (0, 10)
  | 3 => (0, 12)
  | 4 => (0, 13)
  | 5 => (0, 15)
  | 6 => (0, 17)
  | 7 => (0, 20)
  | 8 => (0, 21)
  | 9 => (0, 22)
  | 10 => (0, 24)
  | 11 => (1, 26)
  | 12 => (1, 24)
  | 13 => (1, 23)
  | 14 => (1, 22)
  | 15 => (1, 21)
  | 16 => (1, 21)
  | 17 => (1, 20)
  | 18 => (1, 18)
  | 19 => (1, 18)
  | 20 => (1, 17)
  | 21 => (1, 16)
  | 22 => (1, 15)
  | 23 => (1, 14)
  | 24 => (1, 13)
  | 25 => (1, 13)
  | 26 => (1, 12)
  | 27 => (1, 12)
  | 28 => (1, 10)
  | 29 => (1, 9)
  | 30 => (1, 8)
  | 31 => (1, 7)
  | 32 => (1, 0)
  | _ => (0, 0)

/-- The integer enclosure for log((32+i)/32) for i ≤ 32. Index 32 provides log 2. -/
def gridTicks : ℕ → ℕ × ℕ
  | 0 => (0, 1)
  | 1 => (30771658666, 30771658667)
  | 2 => (60624621816, 60624621817)
  | 3 => (89612158689, 89612158690)
  | 4 => (117783035656, 117783035657)
  | 5 => (145182009844, 145182009845)
  | 6 => (171850256926, 171850256927)
  | 7 => (197825743329, 197825743330)
  | 8 => (223143551314, 223143551315)
  | 9 => (247836163904, 247836163905)
  | 10 => (271933715483, 271933715484)
  | 11 => (295464212893, 295464212894)
  | 12 => (318453731118, 318453731119)
  | 13 => (340926586970, 340926586971)
  | 14 => (362905493689, 362905493690)
  | 15 => (384411698910, 384411698911)
  | 16 => (405465108108, 405465108109)
  | 17 => (426084395310, 426084395311)
  | 18 => (446287102628, 446287102629)
  | 19 => (466089729924, 466089729925)
  | 20 => (485507815781, 485507815782)
  | 21 => (504556010752, 504556010753)
  | 22 => (523248143764, 523248143765)
  | 23 => (541597282432, 541597282433)
  | 24 => (559615787935, 559615787936)
  | 25 => (577315365034, 577315365035)
  | 26 => (594707107746, 594707107747)
  | 27 => (611801541105, 611801541106)
  | 28 => (628608659422, 628608659423)
  | 29 => (645137961373, 645137961374)
  | 30 => (661398482245, 661398482246)
  | 31 => (677398823591, 677398823592)
  | 32 => (693147180559, 693147180560)
  | _ => (0, 0)

private def checkRow (i : ℕ) : Bool :=
  Analysis.fineLogCheck (mkRat (32 + (i : ℤ)) 32) (row i).1 (row i).2 (mkRat (gridTicks i).1 scale)
    (mkRat (gridTicks i).2 scale)

private theorem checked : (List.range 33).all checkRow = true := by decide +kernel

/-- Every used logarithm lies between its two rational tick bounds. The finite
table is checked once and consumers need only the scalar index bound. -/
theorem gridTicks_sound {i : ℕ} (hi : i < 33) :
    (gridTicks i).1 / (scale : ℝ) ≤ Real.log ((32 + (i : ℝ)) / 32) ∧
      Real.log ((32 + (i : ℝ)) / 32) ≤ (gridTicks i).2 / (scale : ℝ) := by
  have h := List.all_eq_true.mp checked i (List.mem_range.mpr hi)
  have hr := Analysis.fineLogCheck_sound (show checkRow i = true from h)
  simpa only [Rat.mkRat_eq_divInt, Rat.cast_divInt, Int.cast_natCast, Int.cast_add, Int.cast_ofNat,
    Nat.cast_ofNat] using hr

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
