/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028ElevenCount

/-! # Refined sixteen-prime supply -/

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

end PseudoPrime.PrimeTestBounds.MillerRabin
