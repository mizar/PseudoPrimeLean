/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.Tactic

/-!
# Roots of unity and torsion units in quadratic number fields

The degree bound on cyclotomic extensions restricts root orders to `1, 2, 3, 4, 6`.
Orders three, four, and six force discriminant `-3` or `-4`; below `-4`, the only torsion
units are `1` and `-1`. Thus the torsion order in the class-number formula is two.
-/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- For positive n with φ(n) ≤ 2, show n divides twelve. Bound each prime-power
factor using the divisibility of totients: only primes two and three occur,
with exponents at most two and one. Used to classify quadratic roots of unity. -/
private theorem totient_small_dvd_twelve (n : ℕ) (hn : 0 < n) (hφ : n.totient ≤ 2) : n ∣ 12 := by
  apply (Nat.dvd_iff_prime_pow_dvd_dvd 12 n).mpr
  intro p k hp hd
  by_cases hk : k = 0
  · subst k
    exact one_dvd 12
  have hkpos := Nat.pos_of_ne_zero hk
  have ht := (Nat.le_of_dvd (Nat.totient_pos.mpr hn) (Nat.totient_dvd_of_dvd hd)).trans hφ
  rw [Nat.totient_prime_pow hp hkpos] at ht
  have hpow : 1 ≤ p ^ (k - 1) := Nat.succ_le_of_lt (pow_pos hp.pos _)
  have hp3 : p ≤ 3 := by
    have hprod := Nat.mul_le_mul_right (p - 1) hpow
    have hsub := Nat.sub_add_cancel hp.one_lt.le
    nlinarith only [ht, hprod, hsub]
  have hpcases : p = 2 ∨ p = 3 := by
    rcases Nat.eq_or_lt_of_le hp3 with h | h
    · exact Or.inr h
    · exact Or.inl (Nat.le_antisymm (Nat.le_of_lt_succ h) hp.two_le)
  rcases hpcases with rfl | rfl
  · have hk2 : k ≤ 2 := by
      by_contra h
      have h3 : 3 ≤ k := Nat.succ_le_of_lt (Nat.lt_of_not_ge h)
      have he : 2 ≤ k - 1 := Nat.le_sub_of_add_le h3
      have hb := Nat.pow_le_pow_right (by norm_num only : 0 < (2 : ℕ)) he
      norm_num only at ht hb
      nlinarith only [ht, hb]
    exact dvd_trans (pow_dvd_pow 2 hk2) (by norm_num only : (2 : ℕ) ^ 2 ∣ 12)
  · have hk1 : k ≤ 1 := by
      by_contra h
      have h2 : 2 ≤ k := Nat.succ_le_of_lt (Nat.lt_of_not_ge h)
      have he : 1 ≤ k - 1 := Nat.le_sub_of_add_le h2
      have hb := Nat.pow_le_pow_right (by norm_num only : 0 < (3 : ℕ)) he
      norm_num only at ht hb
      nlinarith only [ht, hb]
    exact dvd_trans (pow_dvd_pow 3 hk1) (by norm_num only : (3 : ℕ) ^ 1 ∣ 12)

/-- For positive n with φ(n) ≤ 2, classify n as 1, 2, 3, 4 or 6.
Use divisibility by twelve and check its six divisors; twelve has totient four.
This finite arithmetic step supplies the possible quadratic root orders. -/
private theorem totient_le_two_orders (n : ℕ) (hn : 0 < n) (hφ : n.totient ≤ 2) :
    n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 6 := by
  have hd := totient_small_dvd_twelve n hn hφ
  have hm := Nat.mem_divisors.mpr ⟨hd, (by norm_num only : (12 : ℕ) ≠ 0)⟩
  have hv : Nat.divisors 12 = {1, 2, 3, 4, 6, 12} := by decide
  rw [hv] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · subst n
    have ht : Nat.totient 12 = 4 := by decide
    rw [ht] at hφ
    norm_num only at hφ

/-- A degree-two number field containing a primitive n-th root with φ(n)=2
is the n-th cyclotomic extension. The root's rational adjoin has dimension
two and equals the whole field. This permits applying cyclotomic discriminants. -/
theorem quadratic_isCyclotomic_of_primitiveRoot (K : Type) [Field K] [NumberField K]
    (hdeg : Module.finrank ℚ K = 2) (n : ℕ) [NeZero n] (hn : n.totient = 2) {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) : IsCyclotomicExtension {n} ℚ K := by
  let : IsCyclotomicExtension {n} ℚ (Algebra.adjoin ℚ {ζ}) := hζ.adjoin_isCyclotomicExtension ℚ
  have hf :=
    IsCyclotomicExtension.finrank (Algebra.adjoin ℚ {ζ})
      (Polynomial.cyclotomic.irreducible_rat (NeZero.pos n))
  have hs : Algebra.adjoin ℚ {ζ} = ⊤ := by
    apply Subalgebra.toSubmodule_injective
    exact Submodule.eq_top_of_finrank_eq (hf.trans (hn.trans hdeg.symm))
  constructor
  · intro j hj _
    have hjn : j = n := Set.mem_singleton_iff.mp hj
    subst j
    exact ⟨ζ, hζ⟩
  · intro x
    have hx : x ∈ Algebra.adjoin ℚ {ζ} := by
      rw [hs]; exact Set.mem_univ x
    apply
      Algebra.adjoin_mono
        (show {ζ} ⊆ {b : K | ∃ j : ℕ, j ∈ ({n} : Set ℕ) ∧ j ≠ 0 ∧ b ^ j = 1} from ?_) hx
    intro b hb
    have hbζ : b = ζ := Set.mem_singleton_iff.mp hb
    subst b
    exact ⟨n, Set.mem_singleton n, NeZero.ne n, hζ.pow_eq_one⟩

/-- A degree-two number field containing a primitive cube root has discriminant
-3. Identify the field as the third cyclotomic extension and evaluate its
discriminant formula. This isolates a small exceptional quadratic field. -/
theorem quadratic_discr_of_primitive_third_root (K : Type) [Field K] [NumberField K]
    (hdeg : Module.finrank ℚ K = 2) {ζ : K} (hζ : IsPrimitiveRoot ζ 3) :
    NumberField.discr K = -3 := by
  let : IsCyclotomicExtension {3} ℚ K :=
    quadratic_isCyclotomic_of_primitiveRoot K hdeg 3 (by decide) hζ
  have hd := IsCyclotomicExtension.Rat.discr 3 K
  have ht : Nat.totient 3 = 2 := by decide
  have hp : Nat.primeFactors 3 = {3} := Nat.Prime.primeFactors Nat.prime_three
  rw [ht, hp] at hd
  norm_num only [Finset.prod_singleton] at hd
  exact hd

/-- A degree-two number field containing a primitive fourth root has discriminant
-4. Identify the field as the fourth cyclotomic extension and evaluate its
discriminant formula. This isolates the other small exceptional quadratic field. -/
theorem quadratic_discr_of_primitive_fourth_root (K : Type) [Field K] [NumberField K]
    (hdeg : Module.finrank ℚ K = 2) {ζ : K} (hζ : IsPrimitiveRoot ζ 4) :
    NumberField.discr K = -4 := by
  let : IsCyclotomicExtension {4} ℚ K :=
    quadratic_isCyclotomic_of_primitiveRoot K hdeg 4 (by decide) hζ
  have hd := IsCyclotomicExtension.Rat.discr 4 K
  have ht : Nat.totient 4 = 2 := by decide
  have hp : Nat.primeFactors 4 = {2} := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num only]
    exact Nat.primeFactors_prime_pow (by norm_num only : (2 : ℕ) ≠ 0) Nat.prime_two
  rw [ht, hp] at hd
  norm_num only [Finset.prod_singleton] at hd
  exact hd

/-- In a degree-two field of discriminant less than -4, every root of unity
squares to one. Its primitive order has totient at most two; orders three,
four and six force discriminant -3 or -4. Used to control torsion units. -/
theorem quadratic_rootOfUnity_sq_eq_one (K : Type) [Field K] [NumberField K]
    (hdeg : Module.finrank ℚ K = 2) (hd : NumberField.discr K < -4) {ζ : K} {n : ℕ} (hn : n ≠ 0)
    (hz : ζ ^ n = 1) : ζ ^ 2 = 1 := by
  obtain ⟨m, hm, hζ⟩ := IsPrimitiveRoot.exists_pos hz hn
  have hφ :=
    hζ.lcm_totient_le_finrank (K := ℚ) hζ
      (by simpa only [Nat.lcm_self] using Polynomial.cyclotomic.irreducible_rat hm)
  simp only [Nat.lcm_self, hdeg] at hφ
  rcases totient_le_two_orders m hm hφ with h | h | h | h | h
  · subst m
    exact hζ.pow_eq_one_iff_dvd 2 |>.mpr (one_dvd 2)
  · subst m
    exact hζ.pow_eq_one
  · subst m
    have he := quadratic_discr_of_primitive_third_root K hdeg hζ
    rw [he] at hd
    norm_num only at hd
  · subst m
    have he := quadratic_discr_of_primitive_fourth_root K hdeg hζ
    rw [he] at hd
    exact (lt_irrefl (-4 : ℤ) hd).elim
  · subst m
    have h3 : IsPrimitiveRoot (ζ ^ 2) 3 :=
      hζ.pow (by norm_num only) (by norm_num only : (6 : ℕ) = 2 * 3)
    have he := quadratic_discr_of_primitive_third_root K hdeg h3
    rw [he] at hd
    norm_num only at hd

/-- In a degree-two field of discriminant less than -4, each torsion unit
squares to one. Map the finite-order unit into the field, apply the root-order
classification, and lift the equality through the injective coercions. -/
theorem quadratic_torsion_sq_eq_one (K : Type) [Field K] [NumberField K]
    (hdeg : Module.finrank ℚ K = 2) (hd : NumberField.discr K < -4)
    (x : NumberField.Units.torsion K) : (x : (NumberField.RingOfIntegers K)ˣ) ^ 2 = 1 := by
  have hu := NumberField.Units.pow_torsionOrder_eq_one K x.property
  have hz : (x.1 : K) ^ NumberField.Units.torsionOrder K = 1 := by
    have hm := congrArg (fun u : (NumberField.RingOfIntegers K)ˣ => (u : K)) hu
    simpa only [Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one] using hm
  have hs := quadratic_rootOfUnity_sq_eq_one K hdeg hd (NumberField.Units.torsionOrder_ne_zero K) hz
  apply Units.val_injective
  apply NumberField.RingOfIntegers.ext
  simpa only [Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one] using hs

/-- A degree-two number field with discriminant less than -4 has torsion order
two. Every torsion unit squares to one and hence is ±1; these two units are
distinct in characteristic zero. Removes the torsion-order premise from the
imaginary quadratic class-number residue specialization. -/
theorem quadratic_torsionOrder_eq_two (K : Type) [Field K] [NumberField K]
    (hdeg : Module.finrank ℚ K = 2) (hd : NumberField.discr K < -4) :
    NumberField.Units.torsionOrder K = 2 := by
  classical
  let := Fintype.ofFinite (NumberField.Units.torsion K)
  rw [NumberField.Units.torsionOrder, Nat.card_eq_fintype_card]
  apply Finset.card_eq_two.mpr
  refine ⟨1, ⟨-1, neg_one_mem_torsion⟩, ?_, ?_⟩
  · intro he
    have hu := congrArg Subtype.val he
    have ho := congrArg Units.val hu
    simp only [Units.val_one, Units.val_neg] at ho
    have hK := congrArg (algebraMap (NumberField.RingOfIntegers K) K) ho
    simp only [map_one, map_neg] at hK
    exact (neg_ne_self.mpr (one_ne_zero : (1 : K) ≠ 0)) hK.symm
  · apply Finset.ext
    intro x
    constructor
    · intro _
      have hs := quadratic_torsion_sq_eq_one K hdeg hd x
      have ho := congrArg Units.val hs
      simp only [Units.val_pow_eq_pow_val, Units.val_one] at ho
      have hm := sq_eq_one_iff.mp ho
      simp only [Finset.mem_insert, Finset.mem_singleton, ← Subtype.val_inj, ← Units.val_inj,
        Units.val_one, Units.val_neg]
      exact hm
    · intro _
      exact Finset.mem_univ x

end PseudoPrime.NumberTheory
