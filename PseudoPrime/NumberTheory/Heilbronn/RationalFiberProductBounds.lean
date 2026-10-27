/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.RationalResidueFibers
public import PseudoPrime.NumberTheory.Heilbronn.RationalProductGrowth

/-! # Product growth beyond injective rational residue heights -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- A height-Q rational family represented in the Heilbronn subgroup satisfies
card(A)*p² ≤ (p-1)*(p²+4Q²). Sum finite residue fibers using the exact subgroup
cardinality. Unlike the short-height bound, no restriction on Q is imposed. -/
theorem card_rational_family_mul_square_le_heilbronn {p Q : ℕ} [Fact p.Prime] (A : Finset ℚ)
    (hA :
      ∀ q ∈ A,
        ∃ u : heilbronnSubgroup p, boundedRationalResidue (p ^ 2) Q q (u.val : ZMod (p ^ 2))) :
    A.card * p ^ 2 ≤ (p - 1) * (p ^ 2 + 4 * Q ^ 2) := by
  let : Fintype (heilbronnSubgroup p) := Fintype.ofFinite _
  have hh :=
    boundedRationalResidue_family_card_mul_modulus_le A
      (fun u : heilbronnSubgroup p ↦ (u.val : ZMod (p ^ 2))) hA
  rw [← Nat.card_eq_fintype_card, card_heilbronnSubgroup] at hh
  exact hh

/-- The n-fold product set of height-Q subgroup fractions obeys the same
finite-fiber estimate at height Q^n. Raw representations multiply even beyond
the modulus, so no short-height assumption enters this counting bound. -/
theorem card_rationalProductSet_mul_square_le_heilbronn {p Q n : ℕ} [Fact p.Prime] (A : Finset ℚ)
    (hA :
      ∀ q ∈ A,
        ∃ u : heilbronnSubgroup p, boundedRationalResidue (p ^ 2) Q q (u.val : ZMod (p ^ 2))) :
    (rationalProductSet A n).card * p ^ 2 ≤ (p - 1) * (p ^ 2 + 4 * Q ^ (2 * n)) := by
  have hh :=
    card_rational_family_mul_square_le_heilbronn _ (rationalProductSet_has_residues A hA (n := n))
  rw [← pow_mul, Nat.mul_comm n 2] at hh
  exact hh

/-- For prime p, any n-fold product set represented in the Heilbronn subgroup
has cardinality at most p+4Q^(2n)/p after clearing denominators. Relax p-1 to p
and cancel one positive p. This supplies the long-height growth input. -/
theorem card_rationalProductSet_mul_prime_le {p Q n : ℕ} [Fact p.Prime] (A : Finset ℚ)
    (hA :
      ∀ q ∈ A,
        ∃ u : heilbronnSubgroup p, boundedRationalResidue (p ^ 2) Q q (u.val : ZMod (p ^ 2))) :
    (rationalProductSet A n).card * p ≤ p ^ 2 + 4 * Q ^ (2 * n) := by
  have hh := card_rationalProductSet_mul_square_le_heilbronn A hA (n := n)
  have hb := hh.trans (Nat.mul_le_mul_right (p ^ 2 + 4 * Q ^ (2 * n)) (Nat.sub_le p 1))
  have he : (rationalProductSet A n).card * p ^ 2 = ((rationalProductSet A n).card * p) * p := by
    ring
  rw [he, Nat.mul_comm p] at hb
  exact Nat.le_of_mul_le_mul_right hb (Fact.out : p.Prime).pos

/-- For positive height H, degree m and power precision n, combine rational
product growth with the finite-fiber upper bound. All divisor losses remain
explicit in quotientPowerConstant, and there is no H^(2m)<p² hypothesis.
This is the powered estimate used for the eight-degree ratio count. -/
theorem rationalProductSet_power_growth_finite_fibers {p H m n : ℕ} [Fact p.Prime] {A : Finset ℚ}
    (hH : 0 < H) (hm : 0 < m) (hn : 0 < n) (hA : ∀ q ∈ A, 0 < q ∧ q.num.natAbs ≤ H ∧ q.den ≤ H)
    (hres :
      ∀ q ∈ A,
        ∃ u : heilbronnSubgroup p, boundedRationalResidue (p ^ 2) H q (u.val : ZMod (p ^ 2))) :
    A.card ^ (n * m) * p ^ n ≤
      quotientPowerConstant (H ^ (2 * m)) ^ (n ^ 2 * (m - 1)) * H ^ ((m - 1) * m) *
        (p ^ 2 + 4 * H ^ (2 * m)) ^ n := by
  have hg := rationalProductSet_power_growth_explicit hH hm hn hA
  have hf := Nat.pow_le_pow_left (card_rationalProductSet_mul_prime_le A hres (n := m)) n
  have hh := Nat.mul_le_mul_right (p ^ n) hg
  rw [Nat.mul_assoc, ← mul_pow] at hh
  exact hh.trans (Nat.mul_le_mul_left _ hf)

end PseudoPrime.NumberTheory.Heilbronn
