/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Fine53Row0

/-! # Refined sixteen-prime weighted count -/

@[expose] public section

set_option maxRecDepth 65536

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Sixteen prime labels with logarithmic weights rounded to fifty-ninths.
The sharper weights extend the semiprime counting range. -/
def target028SixteenPrimes : List ℕ :=
  53 :: 47 :: 41 :: 43 :: 37 :: target028ElevenPrimes

/-- Rounded logarithmic weights for the sixteen selected primes. -/
def target028Fine53Weight : ℕ → ℕ
  | 53 => 235
  | 47 => 228
  | 41 => 220
  | 43 => 222
  | 37 => 214
  | 2 => 41
  | 3 => 65
  | 5 => 95
  | 7 => 115
  | 11 => 142
  | 13 => 152
  | 17 => 168
  | 19 => 174
  | 23 => 185
  | 29 => 199
  | 31 => 203
  | _ => 0

/-- The checked weights of the sixteen prime labels. -/
def target028Fine53Weights : List ℕ :=
  [235, 228, 220, 222, 214, 41, 65, 95, 115, 142, 152, 168, 174, 185, 199, 203]

/-- The first checked row gives the full count. -/
abbrev target028Fine53Row : Array ℕ :=
  target028Fine53Row0

/-- The remaining checked rows certify the suffix counts. -/
def target028Fine53Tail : List (Array ℕ) :=
  [target028Fine53Row1, target028Fine53Row2, target028Fine53Row3, target028Fine53Row4,
    target028Fine53Row5, target028Fine53Row6, target028Fine53Row7, target028Fine53Row8,
    target028Fine53Row9, target028Fine53Row10, target028Fine53Row11, target028Fine53Row12,
    target028Fine53Row13, target028Fine53Row14, target028Fine53Row15, target028Fine53Row16]

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

/-- The prime labels are distinct and carry the listed positive weights. -/
theorem target028_fine53_labels :
    target028SixteenPrimes.Nodup ∧
      target028SixteenPrimes.map target028Fine53Weight = target028Fine53Weights ∧
      ∀ p ∈ target028SixteenPrimes, 0 < target028Fine53Weight p := by
  decide +kernel

-- Sixteen logarithm intervals are checked by the finite Taylor criterion.
set_option maxRecDepth 65536 in
/-- Each refined weight is an upper bound for fifty-nine times the prime logarithm. -/
theorem target028_fine53_log_check :
    ∀ p ∈ target028SixteenPrimes,
      Analysis.rationalLogIntervalCheck p (Nat.log2 p + 1) 24 0
          ((target028Fine53Weight p : ℚ) / 59) =
        true := by
  decide +kernel

/-- Each refined label is a prime at most 53 and satisfies its logarithmic
weight bound. The existing primality evidence and the checked logarithm
interval provide the hypotheses for weighted semiprime counting. -/
theorem target028_fine53_supply (p : ℕ) (hp : p ∈ target028SixteenPrimes) :
    p.Prime ∧ p ≤ 53 ∧ Real.log p ≤ (target028Fine53Weight p : ℝ) / 59 := by
  have h := Analysis.rationalLogIntervalCheck_sound (target028_fine53_log_check p hp)
  have hprime : p.Prime ∧ p ≤ 53 := by
    have hc : ∀ p ∈ target028SixteenPrimes, p.Prime ∧ p ≤ 53 := by decide +kernel
    exact hc p hp
  simp only [Rat.cast_natCast, Rat.cast_div, Rat.cast_ofNat] at h
  exact ⟨hprime.1, hprime.2, h.2⟩

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
