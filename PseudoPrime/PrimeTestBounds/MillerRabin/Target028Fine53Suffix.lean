/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Fine53Count

/-! # Suffix counts for extending the certified budget -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The final certified row counts the empty weight list. -/
theorem target028_fine53_suffix16 (h : ℕ) (hh : h ≤ 455) :
    weightedPrimeCount id [] h = target028Fine53Row16.getD h 0 := by
  have hc : weightedPrimeTableCheck 455 [] [target028Fine53Row16] = true := target028_fine53_base
  exact ((weightedPrimeTableCheck_sound 455 [] target028Fine53Row16 [] hc h hh)).symm

/-- The checked suffix row computes its weighted count through budget 455. -/
theorem target028_fine53_suffix15 (h : ℕ) (hh : h ≤ 455) :
    weightedPrimeCount id [203] h = target028Fine53Row15.getD h 0 := by
  exact
    (weightedPrimeRow_correct 203 455 [] target028Fine53Row16 target028Fine53Row15
        target028_fine53_step15 (fun k hk ↦ (target028_fine53_suffix16 k hk).symm) h hh).symm

/-- The checked suffix row computes its weighted count through budget 455. -/
theorem target028_fine53_suffix14 (h : ℕ) (hh : h ≤ 455) :
    weightedPrimeCount id [199, 203] h = target028Fine53Row14.getD h 0 := by
  exact
    (weightedPrimeRow_correct 199 455 [203] target028Fine53Row15 target028Fine53Row14
        target028_fine53_step14 (fun k hk ↦ (target028_fine53_suffix15 k hk).symm) h hh).symm

/-- The checked suffix row computes its weighted count through budget 455. -/
theorem target028_fine53_suffix13 (h : ℕ) (hh : h ≤ 455) :
    weightedPrimeCount id [185, 199, 203] h = target028Fine53Row13.getD h 0 := by
  exact
    (weightedPrimeRow_correct 185 455 [199, 203] target028Fine53Row14 target028Fine53Row13
        target028_fine53_step13 (fun k hk ↦ (target028_fine53_suffix14 k hk).symm) h hh).symm

/-- The checked suffix row computes its weighted count through budget 455. -/
theorem target028_fine53_suffix12 (h : ℕ) (hh : h ≤ 455) :
    weightedPrimeCount id [174, 185, 199, 203] h = target028Fine53Row12.getD h 0 := by
  exact
    (weightedPrimeRow_correct 174 455 [185, 199, 203] target028Fine53Row13 target028Fine53Row12
        target028_fine53_step12 (fun k hk ↦ (target028_fine53_suffix13 k hk).symm) h hh).symm

/-- The checked suffix row computes its weighted count through budget 455. -/
theorem target028_fine53_suffix11 (h : ℕ) (hh : h ≤ 455) :
    weightedPrimeCount id [168, 174, 185, 199, 203] h = target028Fine53Row11.getD h 0 := by
  exact
    (weightedPrimeRow_correct 168 455 [174, 185, 199, 203] target028Fine53Row12 target028Fine53Row11
        target028_fine53_step11 (fun k hk ↦ (target028_fine53_suffix12 k hk).symm) h hh).symm

/-- The checked suffix row computes its weighted count through budget 455. -/
theorem target028_fine53_suffix10 (h : ℕ) (hh : h ≤ 455) :
    weightedPrimeCount id [152, 168, 174, 185, 199, 203] h = target028Fine53Row10.getD h 0 := by
  exact
    (weightedPrimeRow_correct 152 455 [168, 174, 185, 199, 203] target028Fine53Row11
        target028Fine53Row10 target028_fine53_step10
        (fun k hk ↦ (target028_fine53_suffix11 k hk).symm) h hh).symm

/-- The checked suffix row computes its weighted count through budget 455. -/
theorem target028_fine53_suffix9 (h : ℕ) (hh : h ≤ 455) :
    weightedPrimeCount id [142, 152, 168, 174, 185, 199, 203] h = target028Fine53Row9.getD h 0 := by
  exact
    (weightedPrimeRow_correct 142 455 [152, 168, 174, 185, 199, 203] target028Fine53Row10
        target028Fine53Row9 target028_fine53_step9
        (fun k hk ↦ (target028_fine53_suffix10 k hk).symm) h hh).symm

/-- The checked suffix row computes its weighted count through budget 455. -/
theorem target028_fine53_suffix8 (h : ℕ) (hh : h ≤ 455) :
    weightedPrimeCount id [115, 142, 152, 168, 174, 185, 199, 203] h =
      target028Fine53Row8.getD h 0 := by
  exact
    (weightedPrimeRow_correct 115 455 [142, 152, 168, 174, 185, 199, 203] target028Fine53Row9
        target028Fine53Row8 target028_fine53_step8 (fun k hk ↦ (target028_fine53_suffix9 k hk).symm)
        h hh).symm

/-- The checked suffix row computes its weighted count through budget 455. -/
theorem target028_fine53_suffix7 (h : ℕ) (hh : h ≤ 455) :
    weightedPrimeCount id [95, 115, 142, 152, 168, 174, 185, 199, 203] h =
      target028Fine53Row7.getD h 0 := by
  exact
    (weightedPrimeRow_correct 95 455 [115, 142, 152, 168, 174, 185, 199, 203] target028Fine53Row8
        target028Fine53Row7 target028_fine53_step7 (fun k hk ↦ (target028_fine53_suffix8 k hk).symm)
        h hh).symm

/-- The checked suffix row computes its weighted count through budget 455. -/
theorem target028_fine53_suffix6 (h : ℕ) (hh : h ≤ 455) :
    weightedPrimeCount id [65, 95, 115, 142, 152, 168, 174, 185, 199, 203] h =
      target028Fine53Row6.getD h 0 := by
  exact
    (weightedPrimeRow_correct 65 455 [95, 115, 142, 152, 168, 174, 185, 199, 203]
        target028Fine53Row7 target028Fine53Row6 target028_fine53_step6
        (fun k hk ↦ (target028_fine53_suffix7 k hk).symm) h hh).symm

/-- The checked suffix row computes its weighted count through budget 455. -/
theorem target028_fine53_suffix5 (h : ℕ) (hh : h ≤ 455) :
    weightedPrimeCount id [41, 65, 95, 115, 142, 152, 168, 174, 185, 199, 203] h =
      target028Fine53Row5.getD h 0 := by
  exact
    (weightedPrimeRow_correct 41 455 [65, 95, 115, 142, 152, 168, 174, 185, 199, 203]
        target028Fine53Row6 target028Fine53Row5 target028_fine53_step5
        (fun k hk ↦ (target028_fine53_suffix6 k hk).symm) h hh).symm

/-- The checked suffix row computes its weighted count through budget 455. -/
theorem target028_fine53_suffix4 (h : ℕ) (hh : h ≤ 455) :
    weightedPrimeCount id [214, 41, 65, 95, 115, 142, 152, 168, 174, 185, 199, 203] h =
      target028Fine53Row4.getD h 0 := by
  exact
    (weightedPrimeRow_correct 214 455 [41, 65, 95, 115, 142, 152, 168, 174, 185, 199, 203]
        target028Fine53Row5 target028Fine53Row4 target028_fine53_step4
        (fun k hk ↦ (target028_fine53_suffix5 k hk).symm) h hh).symm

/-- The checked suffix row computes its weighted count through budget 455. -/
theorem target028_fine53_suffix3 (h : ℕ) (hh : h ≤ 455) :
    weightedPrimeCount id [222, 214, 41, 65, 95, 115, 142, 152, 168, 174, 185, 199, 203] h =
      target028Fine53Row3.getD h 0 := by
  exact
    (weightedPrimeRow_correct 222 455 [214, 41, 65, 95, 115, 142, 152, 168, 174, 185, 199, 203]
        target028Fine53Row4 target028Fine53Row3 target028_fine53_step3
        (fun k hk ↦ (target028_fine53_suffix4 k hk).symm) h hh).symm

/-- The checked suffix row computes its weighted count through budget 455. -/
theorem target028_fine53_suffix2 (h : ℕ) (hh : h ≤ 455) :
    weightedPrimeCount id [220, 222, 214, 41, 65, 95, 115, 142, 152, 168, 174, 185, 199, 203] h =
      target028Fine53Row2.getD h 0 := by
  exact
    (weightedPrimeRow_correct 220 455 [222, 214, 41, 65, 95, 115, 142, 152, 168, 174, 185, 199, 203]
        target028Fine53Row3 target028Fine53Row2 target028_fine53_step2
        (fun k hk ↦ (target028_fine53_suffix3 k hk).symm) h hh).symm

/-- The checked suffix row computes its weighted count through budget 455. -/
theorem target028_fine53_suffix1 (h : ℕ) (hh : h ≤ 455) :
    weightedPrimeCount id [228, 220, 222, 214, 41, 65, 95, 115, 142, 152, 168, 174, 185, 199, 203]
        h =
      target028Fine53Row1.getD h 0 := by
  exact
    (weightedPrimeRow_correct 228 455
        [220, 222, 214, 41, 65, 95, 115, 142, 152, 168, 174, 185, 199, 203] target028Fine53Row2
        target028Fine53Row1 target028_fine53_step1 (fun k hk ↦ (target028_fine53_suffix2 k hk).symm)
        h hh).symm

/-- The checked suffix row computes its weighted count through budget 455. -/
theorem target028_fine53_suffix0 (h : ℕ) (hh : h ≤ 455) :
    weightedPrimeCount id
        [235, 228, 220, 222, 214, 41, 65, 95, 115, 142, 152, 168, 174, 185, 199, 203] h =
      target028Fine53Row0.getD h 0 := by
  exact
    (weightedPrimeRow_correct 235 455
        [228, 220, 222, 214, 41, 65, 95, 115, 142, 152, 168, 174, 185, 199, 203] target028Fine53Row1
        target028Fine53Row0 target028_fine53_step0 (fun k hk ↦ (target028_fine53_suffix1 k hk).symm)
        h hh).symm

end PseudoPrime.PrimeTestBounds.MillerRabin
