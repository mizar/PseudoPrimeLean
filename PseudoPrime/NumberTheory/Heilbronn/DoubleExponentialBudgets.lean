/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.QuotientCoefficientMagnitude

/-! # Symbolic arithmetic for double-exponential coefficient bounds -/

public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- A natural power of a number at most 2^(2^r) is at most 2^(2^(r+e)).
Bound e by 2^e after collecting powers. This absorbs the growth-order
exponent in each finite-fiber degree coefficient without evaluating it. -/
theorem pow_le_double_exp_add {Q r : ℕ} (hQ : Q ≤ 2 ^ (2 ^ r)) (e : ℕ) :
    Q ^ e ≤ 2 ^ (2 ^ (r + e)) := by
  have h := Nat.pow_le_pow_left hQ e
  have he := Nat.mul_le_mul_left (2 ^ r) (Nat.lt_two_pow_self (n := e)).le
  rw [← pow_add] at he
  exact h.trans ((pow_mul 2 (2 ^ r) e).symm.trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) he))

/-- If the outer power exponent e fits in ell binary bits, absorb it using
those bits rather than adding e to the inner exponent. Compare 2^B*e with
2^(B+ell) symbolically; no large power is evaluated. -/
theorem pow_le_double_exp_add_of_exponent_bound {Q B e ell : ℕ} (hQ : Q ≤ 2 ^ (2 ^ B))
    (he : e ≤ 2 ^ ell) : Q ^ e ≤ 2 ^ (2 ^ (B + ell)) := by
  have hpow := Nat.pow_le_pow_left hQ e
  have hscale := Nat.mul_le_mul_left (2 ^ B) he
  have heq : 2 ^ B * 2 ^ ell = 2 ^ (B + ell) := by rw [← pow_add]
  have hinner : 2 ^ B * e ≤ 2 ^ (B + ell) := hscale.trans_eq heq
  calc
    Q ^ e ≤ (2 ^ (2 ^ B)) ^ e := hpow
    _ = 2 ^ (2 ^ B * e) := by rw [pow_mul]
    _ ≤ 2 ^ (2 ^ (B + ell)) := Nat.pow_le_pow_right (by decide : 0 < 2) hinner

/-- Multiplication by a coefficient at most 2^k can be absorbed by adding
k to the inner exponent of 2^(2^B). Use k+1≤2^k and 1≤2^B. This handles
the finite degree sum and harmonic coefficient in an explicit threshold. -/
theorem mul_le_double_exp_add {A B k : ℕ} (hA : A ≤ 2 ^ k) :
    A * 2 ^ (2 ^ B) ≤ 2 ^ (2 ^ (B + k)) := by
  have hT : 1 ≤ (2 : ℕ) ^ B := Nat.one_le_pow _ _ (by decide)
  have hk := Nat.mul_le_mul_left k hT
  have ht := Nat.mul_le_mul_right (2 ^ B) (Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := k)))
  have he : k + 2 ^ B ≤ 2 ^ (B + k) := by
    rw [pow_add]
    nlinarith only [hk, ht]
  calc
    _ ≤ 2 ^ k * 2 ^ (2 ^ B) := Nat.mul_le_mul_right _ hA
    _ = 2 ^ (k + 2 ^ B) := (pow_add 2 _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide : 0 < 2) he

/-- If A is smaller than 2^(2^B), multiplying by A needs only one more
inner exponent bit: A·2^(2^B) < 2^(2^(B+1)). Compare A with the same
double-exponential unit before multiplying. -/
theorem mul_lt_double_exp_succ {A B : ℕ} (hA : A < 2 ^ (2 ^ B)) :
    A * 2 ^ (2 ^ B) < 2 ^ (2 ^ (B + 1)) := by
  have hmul : A * 2 ^ (2 ^ B) < (2 ^ (2 ^ B)) * (2 ^ (2 ^ B)) :=
    Nat.mul_lt_mul_of_pos_right hA (Nat.pow_pos (by decide : 0 < 2))
  calc
    _ < (2 ^ (2 ^ B)) * (2 ^ (2 ^ B)) := hmul
    _ = 2 ^ (2 ^ (B + 1)) := by
      rw [← pow_add]
      congr 1
      rw [pow_succ]
      ring

/-- If D≤2^(2^B), the band coefficient 5(D+1)+1 is at most
2^(2^(B+4)). First bound it by 16 times 2^(2^B), then absorb 16.
This also covers D=0 without any positivity premise. -/
theorem band_coefficient_le_double_exp {D B : ℕ} (hD : D ≤ 2 ^ (2 ^ B)) :
    5 * (D + 1) + 1 ≤ 2 ^ (2 ^ (B + 4)) := by
  have hU : 1 ≤ (2 : ℕ) ^ (2 ^ B) := Nat.one_le_pow _ _ (by decide)
  have h : 5 * (D + 1) + 1 ≤ 16 * 2 ^ (2 ^ B) := by nlinarith only [hD, hU]
  exact h.trans (mul_le_double_exp_add (A := 16) (k := 4) (by decide))

/-- If a finite set has at most k terms bounded by U≥1, its sum plus one
is at most (k+1)U. Compare finite sums and collect multiplication explicitly.
This avoids normalizing a closed double-exponential U in numerical tactics. -/
theorem one_add_sum_le_card_budget {α : Type*} (S : Finset α) (F : α → ℕ) {k U : ℕ}
    (hk : S.card ≤ k) (hU : 1 ≤ U) (hF : ∀ x ∈ S, F x ≤ U) : 1 + ∑ x ∈ S, F x ≤ (k + 1) * U := by
  have hs : ∑ x ∈ S, F x ≤ S.card * U := by
    simpa only [Finset.sum_const, Nat.nsmul_eq_mul] using Finset.sum_le_sum hF
  have ht := hs.trans (Nat.mul_le_mul_right U hk)
  exact (Nat.add_le_add hU ht).trans_eq (by ring)

/-- If C≤2^(2^B), A^a≤2^k, and B+s+k<B', the product A^a C^s
is smaller than 2^(2^B'). Absorb the power s and the multiplier symbolically.
This supplies a strict magnitude bound for fixed integer energy coefficients. -/
theorem mul_power_lt_double_exp_of_budget {A C a s B k B' : ℕ} (hC : C ≤ 2 ^ (2 ^ B))
    (hA : A ^ a ≤ 2 ^ k) (hgap : B + s + k < B') : A ^ a * C ^ s < 2 ^ (2 ^ B') := by
  have hp := pow_le_double_exp_add hC s
  have h := (Nat.mul_le_mul_left (A ^ a) hp).trans (mul_le_double_exp_add hA)
  exact
    h.trans_lt
      (Nat.pow_lt_pow_right (by decide : 1 < 2) (Nat.pow_lt_pow_right (by decide : 1 < 2) hgap))

end PseudoPrime.NumberTheory.Heilbronn
