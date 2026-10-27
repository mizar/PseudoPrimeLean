/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Logarithmic means of the first two prime factors -/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- A common real lower bound times list length is no larger than the sum.
Induct on the list, retaining the pointwise hypothesis for the tail. -/
theorem length_mul_le_sum_of_lower_bound {a : ℝ} {l : List ℝ} (h : ∀ t ∈ l, a ≤ t) :
    (l.length : ℝ) * a ≤ l.sum := by
  induction l with
  | nil => simp only [List.length_nil, Nat.cast_zero, zero_mul, List.sum_nil, le_refl]
  | cons b l ih =>
    have hb := h b List.mem_cons_self
    have ht := ih (fun t ht ↦ h t (List.mem_cons_of_mem b ht))
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one, List.sum_cons]
    nlinarith only [hb, ht]

/-- For positive natural p at most q and a tail bounded below by q,
length times log(pq) is at most twice log of the full product.
Apply the logarithmic lower bound to the tail and compare the first two terms.
This permits repeated factors and avoids any finite integer enumeration. -/
theorem first_pair_log_mean {p q : ℕ} {l : List ℕ} (hp : 0 < p) (hq : 0 < q) (hpq : p ≤ q)
    (ht : ∀ t ∈ l, q ≤ t) :
    ((p :: q :: l).length : ℝ) * Real.log ((p * q : ℕ) : ℝ) ≤
      2 * Real.log (((p :: q :: l).prod : ℕ) : ℝ) := by
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have hall (t : ℕ) (hm : t ∈ l) : (0 : ℝ) < t := hqR.trans_le (Nat.cast_le.mpr (ht t hm))
  have hs :=
    length_mul_le_sum_of_lower_bound (a := Real.log q) (l := l.map (fun t : ℕ ↦ Real.log t))
      (by
        intro t hm
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hm
        exact Real.log_le_log hqR (Nat.cast_le.mpr (ht u hu)))
  have hlog := Real.log_le_log hpR (Nat.cast_le.mpr hpq)
  have hprod : (l.map (fun t : ℕ ↦ (t : ℝ))).prod = (l.prod : ℕ) := by
    exact (Nat.cast_list_prod l).symm
  have he : Real.log ((l.prod : ℕ) : ℝ) = (l.map (fun t : ℕ ↦ Real.log t)).sum := by
    rw [← hprod,
      Real.log_list_prod
        (by
          intro t hm
          obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hm
          exact (hall u hu).ne')]
    simp only [List.map_map, Function.comp_def]
  have htailpos : (0 : ℝ) < (l.prod : ℕ) := by
    rw [← hprod]
    exact
      List.prod_pos
        (by
          intro t hm
          obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hm
          exact hall u hu)
  simp only [List.length_map] at hs
  simp only [List.length_cons, Nat.cast_add, Nat.cast_one, List.prod_cons, Nat.cast_mul]
  rw [Real.log_mul hpR.ne' hqR.ne', Real.log_mul hpR.ne' (mul_ne_zero hqR.ne' htailpos.ne'),
    Real.log_mul hqR.ne' htailpos.ne', he]
  nlinarith only [hs, hlog, mul_nonneg (Nat.cast_nonneg l.length) (sub_nonneg.mpr hlog)]

/-- A positive integer with at least two prime factors counted with
multiplicity admits a two-prime divisor with log(pq) at most twice the mean
factor logarithm. Select the sorted factor list prefix and retain its product.
This provides the local modulus for an Omega-dependent MR witness bound. -/
theorem exists_prime_pair_log_mean {n : ℕ} (hn : 0 < n) (hc : 2 ≤ n.primeFactorsList.length) :
    ∃ p q : ℕ,
      p.Prime ∧
        q.Prime ∧
        p * q ∣ n ∧
        (n.primeFactorsList.length : ℝ) * Real.log ((p * q : ℕ) : ℝ) ≤ 2 * Real.log n := by
  have hprod := Nat.prod_primeFactorsList hn.ne'
  have hpr (p : ℕ) (hp : p ∈ n.primeFactorsList) : p.Prime := Nat.prime_of_mem_primeFactorsList hp
  have hsorted := (Nat.primeFactorsList_sorted n).pairwise
  cases he : n.primeFactorsList with
  | nil =>
    rw [he, List.length_nil] at hc
    exact False.elim ((by decide : ¬2 ≤ 0) hc)
  | cons p tail =>
    cases ht : tail with
    | nil =>
      rw [he, ht, List.length_cons, List.length_nil] at hc
      exact False.elim ((by decide : ¬2 ≤ 0 + 1) hc)
    | cons q l =>
      rw [he, ht] at hprod hsorted hpr
      have hp := hpr p List.mem_cons_self
      have hq := hpr q (List.mem_cons_of_mem p List.mem_cons_self)
      have hpq := (List.pairwise_cons.mp hsorted).1 q List.mem_cons_self
      have htail := (List.pairwise_cons.mp (List.pairwise_cons.mp hsorted).2).1
      have hb := first_pair_log_mean hp.pos hq.pos hpq htail
      have hdiv : p * q ∣ n := by
        refine ⟨l.prod, ?_⟩
        simpa only [List.prod_cons, mul_assoc] using hprod.symm
      refine ⟨p, q, hp, hq, hdiv, ?_⟩
      rw [← hprod]
      exact hb

end PseudoPrime.NumberTheory
