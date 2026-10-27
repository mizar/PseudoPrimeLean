/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.HeilbronnIntervalBound
public import Mathlib.NumberTheory.SmoothNumbers

/-! # Smooth integers and extraction of a prime outside the Heilbronn subgroup -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- The zero-shift Heilbronn coset viewed as a submonoid of the residue ring.
One and multiplication are inherited from its representation by subgroup units. -/
def heilbronnResidueSubmonoid (p : ℕ) [Fact p.Prime] : Submonoid (ZMod (p ^ 2)) where
  carrier := shiftedTeichCoset p 0
  one_mem' := by
    apply (shiftedTeichCoset_eq_heilbronn_coset 0 _).mpr
    exact ⟨1, (heilbronnSubgroup p).one_mem, by rw [principalShift_zero, Units.val_one, mul_one]⟩
  mul_mem' := by
    intro x y hx hy
    obtain ⟨u, hu, he⟩ := (shiftedTeichCoset_eq_heilbronn_coset 0 x).mp hx
    obtain ⟨v, hv, hf⟩ := (shiftedTeichCoset_eq_heilbronn_coset 0 y).mp hy
    rw [principalShift_zero, one_mul] at he hf
    apply (shiftedTeichCoset_eq_heilbronn_coset 0 _).mpr
    exact
      ⟨u * v, (heilbronnSubgroup p).mul_mem hu hv, by
        rw [principalShift_zero, one_mul, Units.val_mul, he, hf]⟩

/-- If every prime below y maps into a submonoid, every positive y-smooth natural
number maps into it. Multiply its prime factors, retaining repeated factors. -/
theorem smooth_mem_submonoid {R : Type*} [Semiring R] (S : Submonoid R) {a y : ℕ}
    (ha : a ∈ Nat.smoothNumbers y) (hprime : ∀ q : ℕ, q.Prime → q < y → (q : R) ∈ S) :
    (a : R) ∈ S := by
  have ht := Nat.mem_smoothNumbers.mp ha
  have hp : ∀ z ∈ a.primeFactorsList.map (fun q : ℕ ↦ (q : R)), z ∈ S := by
    intro z hz
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hz
    exact hprime q (Nat.prime_of_mem_primeFactorsList hq) (ht.2 q hq)
  have h := S.list_prod_mem hp
  rw [← Nat.cast_list_prod, Nat.prod_primeFactorsList ht.1] at h
  exact h

/-- If all primes below y lie in the Heilbronn coset, the y-smooth integers up to k
are included in its initial interval count. Mathlib smoothness uses primes strictly below y. -/
theorem smoothNumbersUpTo_card_le_initialCount {p k y : ℕ} [Fact p.Prime]
    (hprime : ∀ q : ℕ, q.Prime → q < y → (q : ZMod (p ^ 2)) ∈ shiftedTeichCoset p 0) :
    (Nat.smoothNumbersUpTo k y).card ≤ heilbronnInitialCount p k := by
  classical
  apply Finset.card_le_card
  intro a ha
  have ht := Nat.mem_smoothNumbersUpTo.mp ha
  have ha0 := (Nat.mem_smoothNumbers.mp ht.2).1
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr ha0, ht.1⟩, ?_⟩
  exact smooth_mem_submonoid (heilbronnResidueSubmonoid p) ht.2 hprime

/-- If there are more smooth integers than initial coset members, some prime below y
lies outside the coset. Contradict inclusion of all smooth integers. -/
theorem exists_prime_outside_heilbronn_of_smooth_count {p k y : ℕ} [Fact p.Prime]
    (hcount : heilbronnInitialCount p k < (Nat.smoothNumbersUpTo k y).card) :
    ∃ q : ℕ, q.Prime ∧ q < y ∧ (q : ZMod (p ^ 2)) ∉ shiftedTeichCoset p 0 := by
  classical
  by_contra hno
  have hp : ∀ q : ℕ, q.Prime → q < y → (q : ZMod (p ^ 2)) ∈ shiftedTeichCoset p 0 := by
    intro q hq hqy
    by_contra hmem
    exact hno ⟨q, hq, hqy, hmem⟩
  exact (not_lt_of_ge (smoothNumbersUpTo_card_le_initialCount hp)) hcount

/-- A residue outside the zero-shift coset has nontrivial (p-1)-st power.
A hypothetical trivial power would make it a unit fixed by the Teichmuller lift. -/
theorem pow_sub_one_ne_one_of_not_mem_coset {p : ℕ} [Fact p.Prime] {x : ZMod (p ^ 2)}
    (hx : x ∉ shiftedTeichCoset p 0) : x ^ (p - 1) ≠ 1 := by
  intro hpw
  have hp : 1 ≤ p := Nat.one_le_of_lt (Fact.out : p.Prime).one_lt
  have hne : p - 1 ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt)
  have hu := IsUnit.of_pow_eq_one hpw hne
  have hfix : x ^ p = x := by
    calc
      x ^ p = x ^ (p - 1 + 1) := congrArg (fun j : ℕ ↦ x ^ j) (Nat.sub_add_cancel hp).symm
      _ = x := by rw [pow_succ x (p - 1), hpw, one_mul]
  apply hx
  refine ⟨squareReduction p x, (isUnit_iff_reduction_ne_zero x).mp hu, ?_⟩
  rw [principalShift_zero, one_mul, teichLift_reduction, hfix]

/-- Combine the proved interval upper bound with a quantitative smooth-number lower
bound to extract a prime q<y with nontrivial (p-1)-st power modulo p^2.
Only the displayed smooth-number comparison remains as an input. -/
theorem exists_prime_nontrivial_power_of_interval_and_smooth {p k y : ℕ} [Fact p.Prime]
    (hinterval : p * heilbronnInitialCount p k < 256 * k)
    (hsmooth : 256 * k ≤ p * (Nat.smoothNumbersUpTo k y).card) :
    ∃ q : ℕ, q.Prime ∧ q < y ∧ (q : ZMod (p ^ 2)) ^ (p - 1) ≠ 1 := by
  have hc := Nat.lt_of_mul_lt_mul_left (hinterval.trans_le hsmooth)
  obtain ⟨q, hq, hqy, houtside⟩ := exists_prime_outside_heilbronn_of_smooth_count hc
  exact ⟨q, hq, hqy, pow_sub_one_ne_one_of_not_mem_coset houtside⟩

end PseudoPrime.NumberTheory.Heilbronn
