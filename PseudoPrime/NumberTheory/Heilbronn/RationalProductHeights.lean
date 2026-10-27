/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.RationalQuotientPowers

/-! # Heights and quotient descriptions of rational product sets -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- For positive rational factors of respective common numerator-denominator heights Q,D,
their product has height at most Q*D. Retain the canonical reduction gcd and its positivity. -/
theorem positive_product_height {q t : ℚ} {Q D : ℕ} (hq : 0 < q ∧ q.num.natAbs ≤ Q ∧ q.den ≤ Q)
    (ht : 0 < t ∧ t.num.natAbs ≤ D ∧ t.den ≤ D) :
    0 < q * t ∧ (q * t).num.natAbs ≤ Q * D ∧ (q * t).den ≤ Q * D := by
  have hg : 0 < (q.num * t.num).natAbs.gcd (q.den * t.den) :=
    Nat.gcd_pos_of_pos_right _ (Nat.mul_pos q.den_pos t.den_pos)
  have hn := congrArg Int.natAbs (Rat.num_mul_num_eq_num_mul_gcd q t)
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at hn hg
  have hnum := (Nat.le_mul_of_pos_right (q * t).num.natAbs hg).trans_eq hn.symm
  have hden : (q * t).den ≤ q.den * t.den := by
    rw [Rat.mul_den]
    exact Nat.div_le_self _ _
  exact
    ⟨mul_pos hq.1 ht.1, hnum.trans (Nat.mul_le_mul hq.2.1 ht.2.1),
      hden.trans (Nat.mul_le_mul hq.2.2 ht.2.2)⟩

/-- Membership in the (n+1)-fold rational product set is equivalent to a product of an element
of A and an element of the n-fold product set. Split and construct functions on Fin(n+1). -/
theorem mem_rationalProductSet_succ {A : Finset ℚ} {n : ℕ} {z : ℚ} :
    z ∈ rationalProductSet A (n + 1) ↔ ∃ a ∈ A, ∃ b ∈ rationalProductSet A n, z = a * b := by
  classical
  constructor
  · intro hz
    obtain ⟨f, hf, he⟩ := Finset.mem_image.mp hz
    refine
      ⟨(f 0).val, (f 0).property, ∏ i : Fin n, (f i.succ).val,
        Finset.mem_image.mpr ⟨(fun i ↦ f i.succ), Finset.mem_univ _, rfl⟩, ?_⟩
    rw [Fin.prod_univ_succ] at he
    exact he.symm
  · rintro ⟨a, ha, b, hb, he⟩
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hb
    apply Finset.mem_image.mpr
    refine ⟨Fin.cons ⟨a, ha⟩ f, Finset.mem_univ _, ?_⟩
    simpa only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ] using he.symm

/-- If A consists of positive rationals of common height H, every n-fold product is positive
with canonical numerator and denominator at most H^n, including the empty product. -/
theorem rationalProductSet_height {A : Finset ℚ} {H n : ℕ}
    (hA : ∀ q ∈ A, 0 < q ∧ q.num.natAbs ≤ H ∧ q.den ≤ H) :
    ∀ q ∈ rationalProductSet A n, 0 < q ∧ q.num.natAbs ≤ H ^ n ∧ q.den ≤ H ^ n := by
  classical
    induction n with
  | zero =>
    intro q hq
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hq
    simp only [Fin.prod_univ_zero, Rat.num_one, Int.natAbs_one, Rat.den_one, pow_zero]
    exact ⟨by norm_num only, le_refl _, le_refl _⟩
  | succ n ih =>
    intro q hq
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_rationalProductSet_succ.mp hq
    have h := positive_product_height (hA a ha) (ih b hb)
    simpa only [pow_succ, Nat.mul_comm H] using h

/-- Inversion preserves positivity and the common canonical height bound of a finite family.
The positive inverse exchanges the original numerator and denominator. -/
theorem inverse_family_height {A : Finset ℚ} {H : ℕ}
    (hA : ∀ q ∈ A, 0 < q ∧ q.num.natAbs ≤ H ∧ q.den ≤ H) :
    ∀ q ∈ A.image (fun t ↦ t⁻¹), 0 < q ∧ q.num.natAbs ≤ H ∧ q.den ≤ H := by
  classical
  intro q hq
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hq
  have h := hA t ht
  have hn : t⁻¹.num.natAbs = t.den := by
    simp only [Rat.num_inv, Int.sign_eq_one_of_pos (Rat.num_pos.mpr h.1), one_mul,
      Int.natAbs_natCast]
  exact ⟨inv_pos.mpr h.1, hn ▸ h.2.2, (Rat.den_inv_of_ne_zero (ne_of_gt h.1)).symm ▸ h.2.1⟩

/-- The one-fold rational product set equals the original family.
Evaluate the single factor indexed by Fin 1, and construct the constant representing function. -/
theorem rationalProductSet_one (A : Finset ℚ) : rationalProductSet A 1 = A := by
  classical
  ext q
  constructor
  · intro hq
    obtain ⟨f, hf, he⟩ := Finset.mem_image.mp hq
    rw [Fin.prod_univ_one] at he
    exact he ▸ (f 0).property
  · intro hq
    exact Finset.mem_image.mpr ⟨(fun _ ↦ ⟨q, hq⟩), Finset.mem_univ _, Fin.prod_univ_one _⟩

/-- The quotient of the n-fold product set by the inverse family of A equals the (n+1)-fold
product set. Unpack witnesses and use division by an inverse, allowing product growth to
use the proved quotient-set lower bound. -/
theorem quotient_inverse_eq_product_succ (A : Finset ℚ) (n : ℕ) :
    rationalQuotientSet (rationalProductSet A n) (A.image (fun q ↦ q⁻¹)) =
      rationalProductSet A (n + 1) := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨ab, hab, he⟩ := Finset.mem_image.mp hz
    obtain ⟨a, ha, hea⟩ := Finset.mem_image.mp (Finset.mem_product.mp hab).2
    apply mem_rationalProductSet_succ.mpr
    refine ⟨a, ha, ab.1, (Finset.mem_product.mp hab).1, ?_⟩
    change ab.1 / ab.2 = z at he
    rw [← hea, div_inv_eq_mul] at he
    exact he.symm.trans (mul_comm _ _)
  · intro hz
    obtain ⟨a, ha, b, hb, he⟩ := mem_rationalProductSet_succ.mp hz
    apply Finset.mem_image.mpr
    refine ⟨(b, a⁻¹), Finset.mem_product.mpr ⟨hb, Finset.mem_image.mpr ⟨a, ha, rfl⟩⟩, ?_⟩
    change b / a⁻¹ = z
    rw [div_inv_eq_mul, mul_comm b a]
    exact he.symm

end PseudoPrime.NumberTheory.Heilbronn
