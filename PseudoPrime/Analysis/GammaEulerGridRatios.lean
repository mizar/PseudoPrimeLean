/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Gamma.RationalResolventApproximation

/-! # Sequential lookup for finite Gamma node intervals -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Traverse labels and natural values together, returning the value at the
first matching label. If no label matches, return the next value after the
label list; return zero if the value list ends first. -/
def sequentialNodeLookup {α : Type} [DecidableEq α] : List α → List ℕ → α → ℕ
  | [], [], _ => 0
  | [], r :: _, _ => r
  | _ :: _, [], _ => 0
  | k :: ks, r :: rs, a => if k = a then r else sequentialNodeLookup ks rs a

/-- Input: ten grid numerators and a resolvent node. Definition: consecutive millionth
endpoints selected by the fixed node order. Output: a rational power interval.
Role: supply compact data whose twentieth-power checks are verified below. -/
def smallSeedRatios (rs : List ℕ) (a : ℚ) : ℚ × ℚ :=
  let r :=
    sequentialNodeLookup (AnalyticNumberTheory.Gamma.gammaResolventCoefficients.map Prod.fst) rs a
  ((r : ℚ) / 1000000, ((r + 1 : ℕ) : ℚ) / 1000000)

end PseudoPrime.Analysis
