/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-! # Additive and Teichmuller lifts modulo a prime square -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- Reduction from ZMod(p^2) to ZMod p, used to normalize lifted coset equations. -/
def squareReduction (p : ℕ) : ZMod (p ^ 2) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p (by decide : (2 : ℕ) ≠ 0)) (ZMod p)

/-- Reduction preserves natural-number representatives; this is the cast interface. -/
theorem squareReduction_natCast (p a : ℕ) : squareReduction p (a : ZMod (p ^ 2)) = (a : ZMod p) :=
  map_natCast _ _

/-- For prime p, reduction is the residue of the canonical representative. -/
theorem squareReduction_val {p : ℕ} [Fact p.Prime] (a : ZMod (p ^ 2)) :
    squareReduction p a = (a.val : ZMod p) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val a]
  exact squareReduction_natCast p a.val

/-- For prime p, the kernel of reduction consists exactly of multiples of p. -/
theorem squareReduction_eq_zero_iff_dvd {p : ℕ} [Fact p.Prime] (a : ZMod (p ^ 2)) :
    squareReduction p a = 0 ↔ (p : ZMod (p ^ 2)) ∣ a := by
  constructor
  · intro h
    rw [squareReduction_val, ZMod.natCast_eq_zero_iff] at h
    obtain ⟨k, hk⟩ := h
    refine ⟨(k : ZMod (p ^ 2)), ?_⟩
    rw [← Nat.cast_mul, ← hk, ZMod.natCast_zmod_val]
  · rintro ⟨k, rfl⟩
    rw [map_mul, squareReduction_natCast, ZMod.natCast_self, zero_mul]

/-- The square of p vanishes modulo p^2; no primality assumption is needed. -/
theorem prime_square_cast_zero {p : ℕ} : (p : ZMod (p ^ 2)) ^ 2 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_self]

/-- Equal reductions give equal p-multiples modulo p^2, by the square-zero kernel. -/
theorem prime_mul_eq_of_reduction_eq {p : ℕ} [Fact p.Prime] {a b : ZMod (p ^ 2)}
    (h : squareReduction p a = squareReduction p b) : (p : ZMod (p ^ 2)) * a = p * b := by
  have hz : squareReduction p (a - b) = 0 := by rw [map_sub, h, sub_self]
  obtain ⟨k, hk⟩ := (squareReduction_eq_zero_iff_dvd (a - b)).mp hz
  apply sub_eq_zero.mp
  calc
    (p : ZMod (p ^ 2)) * a - p * b = p * (a - b) := by ring
    _ = p * (p * k) := by rw [hk]
    _ = 0 := by rw [← mul_assoc, ← pow_two, prime_square_cast_zero, zero_mul]

/-- For prime p, equal reductions have equal p-th powers modulo p^2.
Use the power divisibility lemma with one lifting step. -/
theorem pow_prime_eq_of_reduction_eq {p : ℕ} [Fact p.Prime] {a b : ZMod (p ^ 2)}
    (h : squareReduction p a = squareReduction p b) : a ^ p = b ^ p := by
  have hz : squareReduction p (a - b) = 0 := by rw [map_sub, h, sub_self]
  have hd := dvd_sub_pow_of_dvd_sub ((squareReduction_eq_zero_iff_dvd (a - b)).mp hz) 1
  simp only [Nat.one_add, pow_one, prime_square_cast_zero] at hd
  exact sub_eq_zero.mp (zero_dvd_iff.mp hd)

/-- Additive lift a |-> p*a.val into ZMod(p^2). For prime p it is injective;
it identifies the residue field with the square-zero reduction kernel. -/
noncomputable def primeLift (p : ℕ) (a : ZMod p) : ZMod (p ^ 2) :=
  (p : ZMod (p ^ 2)) * (a.val : ZMod (p ^ 2))

/-- For prime p, lifting the reduction of x gives p*x. This removes representatives. -/
theorem primeLift_reduction {p : ℕ} [Fact p.Prime] (a : ZMod (p ^ 2)) :
    primeLift p (squareReduction p a) = p * a := by
  apply prime_mul_eq_of_reduction_eq
  rw [squareReduction_natCast, ZMod.natCast_zmod_val]

/-- The canonical representative of a residue reduces back to that residue. -/
theorem squareReduction_lift_val {p : ℕ} [Fact p.Prime] (a : ZMod p) :
    squareReduction p (a.val : ZMod (p ^ 2)) = a := by
  rw [squareReduction_natCast, ZMod.natCast_zmod_val]

/-- For prime p the additive lift is injective, by representative bounds and cancellation. -/
theorem primeLift_injective {p : ℕ} [Fact p.Prime] : Function.Injective (primeLift p) := by
  intro a b h
  have hp : 0 < p := Nat.Prime.pos Fact.out
  have ha : p * a.val < p ^ 2 := by
    simpa only [pow_two] using Nat.mul_lt_mul_of_pos_left (ZMod.val_lt a) hp
  have hb : p * b.val < p ^ 2 := by
    simpa only [pow_two] using Nat.mul_lt_mul_of_pos_left (ZMod.val_lt b) hp
  have he : p * a.val = p * b.val := by
    change (p : ZMod (p ^ 2)) * a.val = p * b.val at h
    rw [← Nat.cast_mul, ← Nat.cast_mul, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha,
      Nat.mod_eq_of_lt hb] at h
    exact h
  exact (ZMod.val_injective p) (Nat.eq_of_mul_eq_mul_left hp he)

/-- The additive lift preserves zero. -/
theorem primeLift_zero {p : ℕ} : primeLift p 0 = 0 := by
  rw [primeLift, ZMod.val_zero, Nat.cast_zero, mul_zero]

/-- For prime p the additive lift preserves addition, by reduction of representatives. -/
theorem primeLift_add {p : ℕ} [Fact p.Prime] (a b : ZMod p) :
    primeLift p (a + b) = primeLift p a + primeLift p b := by
  have hr : squareReduction p ((a.val : ZMod (p ^ 2)) + b.val) = a + b := by
    rw [map_add, squareReduction_lift_val, squareReduction_lift_val]
  rw [← hr, primeLift_reduction, mul_add]
  rfl

/-- For prime p the additive lift preserves negation, by its addition law. -/
theorem primeLift_neg {p : ℕ} [Fact p.Prime] (a : ZMod p) : primeLift p (-a) = -primeLift p a := by
  have h := primeLift_add a (-a)
  rw [add_neg_cancel, primeLift_zero] at h
  exact (eq_neg_of_add_eq_zero_right h.symm)

/-- For prime p the additive lift preserves subtraction; used in coset differences. -/
theorem primeLift_sub {p : ℕ} [Fact p.Prime] (a b : ZMod p) :
    primeLift p (a - b) = primeLift p a - primeLift p b := by
  rw [sub_eq_add_neg, primeLift_add, primeLift_neg, sub_eq_add_neg]

/-- The additive lift is compatible with multiplication by the reduction of an element. -/
theorem primeLift_mul {p : ℕ} [Fact p.Prime] (a : ZMod p) (b : ZMod (p ^ 2)) :
    primeLift p (a * squareReduction p b) = primeLift p a * b := by
  have hr : squareReduction p ((a.val : ZMod (p ^ 2)) * b) = a * squareReduction p b := by
    rw [map_mul, squareReduction_lift_val]
  rw [← hr, primeLift_reduction]
  exact (mul_assoc _ _ _).symm

/-- For prime p every additive lift reduces to zero. -/
theorem squareReduction_primeLift {p : ℕ} [Fact p.Prime] (a : ZMod p) :
    squareReduction p (primeLift p a) = 0 := by
  rw [primeLift, map_mul, squareReduction_natCast, ZMod.natCast_self, zero_mul]

/-- Products of additive lifts vanish, since the reduction kernel is square-zero. -/
theorem primeLift_mul_primeLift {p : ℕ} [Fact p.Prime] (a b : ZMod p) :
    primeLift p a * primeLift p b = 0 := by
  rw [← primeLift_mul, squareReduction_primeLift, mul_zero, primeLift_zero]

/-- Teichmuller lift a |-> a.val^p modulo p^2. For prime p it is multiplicative
and reduces to a, including at zero; used to parametrize Heilbronn cosets. -/
noncomputable def teichLift (p : ℕ) (a : ZMod p) : ZMod (p ^ 2) :=
  (a.val : ZMod (p ^ 2)) ^ p

/-- For prime p the Teichmuller lift is a section of reduction, by finite-field Frobenius. -/
theorem squareReduction_teichLift {p : ℕ} [Fact p.Prime] (a : ZMod p) :
    squareReduction p (teichLift p a) = a := by
  rw [teichLift, map_pow, squareReduction_lift_val, ZMod.pow_card]

/-- For prime p lifting the reduction of x gives x^p, by power-lifting invariance. -/
theorem teichLift_reduction {p : ℕ} [Fact p.Prime] (a : ZMod (p ^ 2)) :
    teichLift p (squareReduction p a) = a ^ p := by
  exact pow_prime_eq_of_reduction_eq (squareReduction_lift_val (squareReduction p a))

/-- For prime p each Teichmuller lift is fixed by the p-th power map. -/
theorem teichLift_pow {p : ℕ} [Fact p.Prime] (a : ZMod p) : teichLift p a ^ p = teichLift p a := by
  have he : squareReduction p (teichLift p a) = squareReduction p (a.val : ZMod (p ^ 2)) := by
    rw [squareReduction_teichLift, squareReduction_lift_val]
  exact pow_prime_eq_of_reduction_eq he

/-- For prime p the Teichmuller lift preserves products, by power-lifting invariance. -/
theorem teichLift_mul {p : ℕ} [Fact p.Prime] (a b : ZMod p) :
    teichLift p (a * b) = teichLift p a * teichLift p b := by
  have hr : squareReduction p ((a.val : ZMod (p ^ 2)) * b.val) = a * b := by
    rw [map_mul, squareReduction_lift_val, squareReduction_lift_val]
  rw [← hr, teichLift_reduction, mul_pow]
  rfl

/-- For prime p the Teichmuller lift preserves zero. -/
theorem teichLift_zero {p : ℕ} [Fact p.Prime] : teichLift p 0 = 0 := by
  rw [teichLift, ZMod.val_zero, Nat.cast_zero, zero_pow (Nat.Prime.ne_zero Fact.out)]

/-- For prime p the Teichmuller lift preserves one. -/
theorem teichLift_one {p : ℕ} [Fact p.Prime] : teichLift p 1 = 1 := by
  have h := teichLift_reduction (1 : ZMod (p ^ 2))
  rw [map_one, one_pow] at h
  exact h

/-- For prime p the Teichmuller lift is injective because reduction is a left inverse. -/
theorem teichLift_injective {p : ℕ} [Fact p.Prime] : Function.Injective (teichLift p) := by
  intro a b h
  have hr := congrArg (squareReduction p) h
  simpa only [squareReduction_teichLift] using hr

/-- Principal unit 1+primeLift(a) modulo p^2. Its reduction is one;
its multiplication law adds the residue parameters. -/
noncomputable def principalShift (p : ℕ) (a : ZMod p) : ZMod (p ^ 2) :=
  1 + primeLift p a

/-- For prime p each principal shift reduces to one. -/
theorem squareReduction_principalShift {p : ℕ} [Fact p.Prime] (a : ZMod p) :
    squareReduction p (principalShift p a) = 1 := by
  rw [principalShift, map_add, map_one, squareReduction_primeLift, add_zero]

/-- For prime p principal shifts multiply by adding their parameters, by square-zero products. -/
theorem principalShift_mul {p : ℕ} [Fact p.Prime] (a b : ZMod p) :
    principalShift p a * principalShift p b = principalShift p (a + b) := by
  rw [principalShift, principalShift, principalShift, primeLift_add]
  have h := primeLift_mul_primeLift a b
  linear_combination h

end PseudoPrime.NumberTheory.Heilbronn
