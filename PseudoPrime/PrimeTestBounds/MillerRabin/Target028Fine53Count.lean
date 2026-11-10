/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Fine53Supply
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Fine53Row0
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Fine53Row1
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Fine53Row2
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Fine53Row3
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Fine53Row4
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Fine53Row5
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Fine53Row6
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Fine53Row7
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Fine53Row8
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Fine53Row9
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Fine53Row10
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Fine53Row11
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Fine53Row12
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Fine53Row13
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Fine53Row14
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Fine53Row15
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Fine53Row16

/-! # Refined sixteen-prime weighted count -/

@[expose] public section

set_option maxRecDepth 65536

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The first checked row gives the full count. -/
abbrev target028Fine53Row : Array ℕ :=
  target028Fine53Row0

/-- The remaining checked rows certify the suffix counts. -/
def target028Fine53Tail : List (Array ℕ) :=
  [target028Fine53Row1, target028Fine53Row2, target028Fine53Row3, target028Fine53Row4,
    target028Fine53Row5, target028Fine53Row6, target028Fine53Row7, target028Fine53Row8,
    target028Fine53Row9, target028Fine53Row10, target028Fine53Row11, target028Fine53Row12,
    target028Fine53Row13, target028Fine53Row14, target028Fine53Row15, target028Fine53Row16]

-- This recurrence check reduces 456 entries.
/-- The independently checked rows form an exact weighted-count table. -/
theorem target028_fine53_checked :
    weightedPrimeTableCheck 455 target028Fine53Weights (target028Fine53Row :: target028Fine53Tail) =
      true := by
  simp only [weightedPrimeTableCheck, target028Fine53Weights, target028Fine53Row,
    target028Fine53Tail, target028_fine53_step0, target028_fine53_step1, target028_fine53_step2,
    target028_fine53_step3, target028_fine53_step4, target028_fine53_step5, target028_fine53_step6,
    target028_fine53_step7, target028_fine53_step8, target028_fine53_step9, target028_fine53_step10,
    target028_fine53_step11, target028_fine53_step12, target028_fine53_step13,
    target028_fine53_step14, target028_fine53_step15, target028_fine53_base, Bool.true_and]

/-- The checked recurrence gives the exact weighted-family cardinality for
every budget through 455. The count-to-family theorem transfers the table. -/
theorem target028_fine53_card (H : ℕ) (hH : H ≤ 455) :
    (weightedPrimeFamily target028SixteenPrimes.toFinset target028Fine53Weight H).card =
      target028Fine53Row.getD H 0 :=
  (weightedPrimeCount_weights_eq_card target028Fine53Weight H target028SixteenPrimes
        target028Fine53Weights target028_fine53_labels.1 target028_fine53_labels.2.2
        target028_fine53_labels.2.1).symm.trans
    ((weightedPrimeTableCheck_sound 455 target028Fine53Weights target028Fine53Row
        target028Fine53Tail target028_fine53_checked H hH).symm)

end PseudoPrime.PrimeTestBounds.MillerRabin
