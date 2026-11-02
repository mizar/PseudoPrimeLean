/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.DivisorMaskCheck
public import PseudoPrime.NumberTheory.PrimeBitmapCoverage

/-! # Soundness of divisor masks used by finite LLS certificates

This proof layer transfers checked divisor masks to exact coverage of coprime residues.
Divisors need not be prime or complete, and their submitted doubling levels need not be minimal.
The nontrivial-divisor guard is essential to keep unit bits out of the exclusion mask.

Keep this proof layer out of finite certificate imports. Adding or editing its declarations or
proof dependencies must not invalidate the expensive data checks; computation stays in the
separate divisor-mask and product-check modules.
-/

@[expose] public section

namespace PseudoPrime.LLS

/-- The computational spreading loop equals the existing arithmetic implementation.
Input: arbitrary level, stride and bits. Proof: induction on the level.
Role: reuse the established multiples-only invariant without trusting computation. -/
private theorem spread_eq_legacy (level step bits : ℕ) :
    spreadDivisorBits level step bits = NumberTheory.spreadMultiples level step bits := by
  induction level generalizing step bits
  case zero => rfl
  case succ level ih => exact ih (2 * step) (bits ||| (bits <<< step))

/-- Submitted divisor unions agree with the existing arithmetic mask.
Input: arbitrary divisor/level pairs. Proof: induction and equality of the spreading loops.
Role: transfer the existing coprime-exclusion theorem to the computational entry. -/
private theorem mask_eq_legacy (ds : List (ℕ × ℕ)) :
    divisorLevelMask ds = NumberTheory.badMaskDoubling ds := by
  induction ds
  case nil => rfl
  case cons entry ds ih =>
    rcases entry with ⟨d, level⟩
    rw [divisorLevelMask, NumberTheory.badMaskDoubling, spread_eq_legacy, ih]

/-- Every coprime residue avoids a mask of checked nontrivial divisors.
Input: checked divisor validity and coprimality, with arbitrary submitted levels.
Claim: the residue's bit is false. Proof: transfer the arithmetic exclusion theorem.
Role: ensure the exclusion mask cannot substitute for a missing unit product. -/
theorem divisorLevelMask_coprime {q a : ℕ} {ds : List (ℕ × ℕ)} (hd : divisorLevelsValid q ds = true)
    (ha : Nat.Coprime a q) : (divisorLevelMask ds).testBit a = false := by
  rw [mask_eq_legacy]
  exact NumberTheory.badMaskDoubling_coprime hd ha

/-- The full low-bit mask contains every residue below its bound.
Input: an index strictly below the modulus. Claim: its mask bit is true.
Proof: the power-of-two bit law. Role: read exact coverage at an arbitrary residue. -/
theorem divisorFullMask_testBit {q a : ℕ} (ha : a < q) : (divisorFullMask q).testBit a = true := by
  rw [divisorFullMask, Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow_sub_one]
  simp only [ha, decide_true]

/-- A coprime residue covered by products or divisor masks is covered by products.
Input: valid submitted divisors, exact low-bit coverage and a coprime residue below the modulus.
Claim: the product mask contains that bit. Proof: the divisor bit is false and the full bit true.
Role: extract product coverage without enumerating gcd values in finite computation. -/
theorem divisorCoverage_testBit {q a products : ℕ} {ds : List (ℕ × ℕ)}
    (hd : divisorLevelsValid q ds = true)
    (hcover : ((products ||| divisorLevelMask ds) &&& divisorFullMask q) = divisorFullMask q)
    (ha : a < q) (hc : Nat.Coprime a q) : products.testBit a = true := by
  have hbad := divisorLevelMask_coprime hd hc
  have hfull := divisorFullMask_testBit ha
  have he := congrArg (fun mask : ℕ ↦ mask.testBit a) hcover
  simp only [Nat.testBit_land, Nat.testBit_lor, hfull, hbad, Bool.or_false, Bool.and_true] at he
  exact he

end PseudoPrime.LLS
