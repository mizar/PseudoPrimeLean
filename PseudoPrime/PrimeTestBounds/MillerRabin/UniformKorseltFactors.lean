/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.UniformKorseltTriple

/-! # Ordered factors of uniform Korselt triples -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A three-element finite set of naturals admits an increasing enumeration.
Permuting the three distinct elements provides the factor ordering used below. -/
private theorem lowBridge_ordered_three_set (S : Finset ℕ) (hcard : S.card = 3) :
    ∃ p q r, p < q ∧ q < r ∧ S = {p, q, r} := by
  obtain ⟨p, q, r, hpq, hpr, hqr, hset⟩ := Finset.card_eq_three.mp hcard
  rcases lt_or_gt_of_ne hpq with hpq' | hqp'
  · rcases lt_or_gt_of_ne hqr with hqr' | hrq'
    · exact ⟨p, q, r, hpq', hqr', hset⟩
    · rcases lt_or_gt_of_ne hpr with hpr' | hrp'
      · refine ⟨p, r, q, hpr', hrq', ?_⟩
        rw [hset]
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton, or_comm]
      · refine ⟨r, p, q, hrp', hpq', ?_⟩
        rw [hset]
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm]
  · rcases lt_or_gt_of_ne hpr with hpr' | hrp'
    · exact ⟨q, p, r, hqp', hpr', by simpa only [Finset.insert_comm] using hset⟩
    · rcases lt_or_gt_of_ne hqr with hqr' | hrq'
      · refine ⟨q, r, p, hqr', hrp', ?_⟩
        rw [hset]
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm]
      · refine ⟨r, q, p, hrq', hqp', ?_⟩
        rw [hset]
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm]

/-- A uniform Korselt triple has three increasing prime factors whose product
is the input. Squarefreeness supplies the product and finite ordering chooses
the factors in the order required by the low-bridge spacing theorem. -/
theorem uniformKorselt_ordered_factors {n : ℕ} (hu : UniformKorseltTriple n) :
    ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p < q ∧ q < r ∧ n = p * q * r := by
  obtain ⟨p, q, r, hpq, hqr, hset⟩ := lowBridge_ordered_three_set n.primeFactors hu.2.1
  have hpMem : p ∈ n.primeFactors := hset ▸ Finset.mem_insert_self p _
  have hqMem : q ∈ n.primeFactors := hset ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self q _)
  have hrMem : r ∈ n.primeFactors :=
    hset ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self r))
  have hp := (Nat.mem_primeFactors.mp hpMem).1
  have hq := (Nat.mem_primeFactors.mp hqMem).1
  have hr := (Nat.mem_primeFactors.mp hrMem).1
  have hprod := (Nat.prod_primeFactors_of_squarefree hu.1).symm
  rw [hset] at hprod
  have hnprod : n = p * q * r := by
    have hpq' : p ≠ q := ne_of_lt hpq
    have hpr' : p ≠ r := ne_of_lt (hpq.trans hqr)
    have hqr' : q ≠ r := ne_of_lt hqr
    simpa only [Finset.prod_insert, Finset.prod_singleton, Finset.mem_insert, Finset.mem_singleton,
      hpq', hpr', hqr', or_self, not_false_eq_true, mul_assoc] using hprod
  exact ⟨p, q, r, hp, hq, hr, hpq, hqr, hnprod⟩

/-- If the predecessor of a positive factor divides the predecessor of a
positive product, it also divides the predecessor of the other factor. The
product is expanded using the factor predecessor for later Korselt reductions. -/
theorem korselt_predecessor_factor {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (h : b - 1 ∣ a * b - 1) :
    b - 1 ∣ a - 1 := by
  have hab : 1 ≤ a * b := Nat.mul_pos ha hb
  have h1 := congrArg (fun x : ℕ ↦ a * x) (Nat.sub_add_cancel hb)
  have h2 := Nat.sub_add_cancel ha
  have h3 := Nat.sub_add_cancel hab
  have hid : a * b - 1 = a * (b - 1) + (a - 1) := by nlinarith only [h1, h2, h3]
  rw [hid] at h
  exact (Nat.dvd_add_iff_right (dvd_mul_left (b - 1) a)).2 h

end PseudoPrime.PrimeTestBounds.MillerRabin
