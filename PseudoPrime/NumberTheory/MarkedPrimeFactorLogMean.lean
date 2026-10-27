/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic

/-! # A marked prime factor or a small complementary pair -/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- In a finite set with at least two elements, two distinct weights have
sum at most twice the mean weight. Choose successive minima and bound
the remaining sum below. No sign hypothesis on the real weights is needed.
This is the pair-selection input for a marked-factor conductor bound. -/
theorem exists_pair_weight_le_twice_sum {α : Type*} (S : Finset α) (w : α → ℝ) (hc : 2 ≤ S.card) :
    ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧ (S.card : ℝ) * (w p + w q) ≤ 2 * ∑ t ∈ S, w t := by
  classical
  obtain ⟨p, hp, hminp⟩ :=
    S.exists_min_image w (Finset.card_pos.mp ((by decide : 0 < 2).trans_le hc))
  have hT : (S.erase p).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem hp]
    exact Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 1 < 2) hc)
  obtain ⟨q, hq, hminq⟩ := (S.erase p).exists_min_image w hT
  have hqS := (Finset.mem_erase.mp hq).2
  have hs := (S.erase p).card_nsmul_le_sum w (w q) hminq
  rw [nsmul_eq_mul, Finset.card_erase_of_mem hp, Nat.cast_sub (le_trans (by decide : 1 ≤ 2) hc),
    Nat.cast_one] at hs
  have he := Finset.sum_erase_add S w hp
  have hcard : (2 : ℝ) ≤ S.card := Nat.cast_le.mpr hc
  have hdiff := mul_nonneg (sub_nonneg.mpr hcard) (sub_nonneg.mpr (hminp q hqS))
  refine ⟨p, hp, q, hqS, (Finset.mem_erase.mp hq).1.symm, ?_⟩
  nlinarith only [hs, he, hdiff]

/-- For at least three weights and a marked member r, either w(r) or a
pair avoiding r is at most twice the total divided by card(S)+1.
Apply pair averaging to S without r and retain its missing weight.
This improves the denominator for branches with a usable single factor. -/
theorem marked_or_pair_weight_le_twice_sum {α : Type*} (S : Finset α) (w : α → ℝ) {r : α}
    (hr : r ∈ S) (hc : 3 ≤ S.card) :
    ((S.card : ℝ) + 1) * w r ≤ 2 * ∑ t ∈ S, w t ∨
      ∃ p ∈ S,
        ∃ q ∈ S, p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ ((S.card : ℝ) + 1) * (w p + w q) ≤ 2 * ∑ t ∈ S, w t := by
  classical
  by_cases hm : ((S.card : ℝ) + 1) * w r ≤ 2 * ∑ t ∈ S, w t
  · exact Or.inl hm
  have hT : 2 ≤ (S.erase r).card := by
    rw [Finset.card_erase_of_mem hr]
    exact Nat.sub_le_sub_right hc 1
  obtain ⟨p, hp, q, hq, hpq, hmean⟩ := exists_pair_weight_le_twice_sum (S.erase r) w hT
  rw [Finset.card_erase_of_mem hr, Nat.cast_sub (le_trans (by decide : 1 ≤ 3) hc),
    Nat.cast_one] at hmean
  have he := Finset.sum_erase_add S w hr
  have hsum : (∑ t ∈ S.erase r, w t) = (∑ t ∈ S, w t) - w r := by linarith only [he]
  rw [hsum] at hmean
  have hcard : (3 : ℝ) ≤ S.card := Nat.cast_le.mpr hc
  have hscaled := mul_le_mul_of_nonneg_left hmean (by linarith only [hcard] : 0 ≤ (S.card : ℝ) + 1)
  have hcancel :
    ((S.card : ℝ) - 1) * (((S.card : ℝ) + 1) * (w p + w q)) ≤
      ((S.card : ℝ) - 1) * (2 * ∑ t ∈ S, w t) := by
    nlinarith only [hscaled, lt_of_not_ge hm]
  have hbound :=
    (mul_le_mul_iff_right₀ (by linarith only [hcard] : (0 : ℝ) < S.card - 1)).mp hcancel
  exact
    Or.inr
      ⟨p, (Finset.mem_erase.mp hp).2, q, (Finset.mem_erase.mp hq).2, hpq,
        (Finset.mem_erase.mp hp).1, (Finset.mem_erase.mp hq).1, hbound⟩

/-- For n>0 the sum of logarithms of its distinct prime factors is at
most log n. Their squarefree product divides n; apply the logarithm to
that divisibility bound. This does not assume that n is squarefree. -/
theorem sum_log_primeFactors_le_log {n : ℕ} (hn : 0 < n) :
    ∑ p ∈ n.primeFactors, Real.log p ≤ Real.log n := by
  have hp (p : ℕ) (h : p ∈ n.primeFactors) : p.Prime := Nat.prime_of_mem_primeFactors h
  have hpos : 0 < ∏ p ∈ n.primeFactors, p := Finset.prod_pos (fun p h ↦ (hp p h).pos)
  have hprod :=
    Real.log_le_log (Nat.cast_pos.mpr hpos)
      (Nat.cast_le.mpr (Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)))
  rw [Nat.cast_prod, Real.log_prod (fun p h ↦ Nat.cast_ne_zero.mpr (hp p h).ne_zero)] at hprod
  exact hprod

/-- For n>0 with at least three distinct prime factors and a marked factor r,
either r or a pair of other prime factors has logarithm at most
2 log(n)/(omega(n)+1). Apply the marked-weight lemma to prime logarithms.
This selects the small local modulus for the mixed-two-adic MR branch. -/
theorem marked_prime_or_pair_log_mean {n r : ℕ} (hn : 0 < n) (hr : r ∈ n.primeFactors)
    (hc : 3 ≤ n.primeFactors.card) :
    ((n.primeFactors.card : ℝ) + 1) * Real.log r ≤ 2 * Real.log n ∨
      ∃ p q : ℕ,
        p.Prime ∧
          q.Prime ∧
          p ≠ q ∧
          p * q ∣ n ∧
          ((n.primeFactors.card : ℝ) + 1) * Real.log ((p * q : ℕ) : ℝ) ≤ 2 * Real.log n := by
  have hs :=
    mul_le_mul_of_nonneg_left (sum_log_primeFactors_le_log hn) (by norm_num only : (0 : ℝ) ≤ 2)
  rcases marked_or_pair_weight_le_twice_sum n.primeFactors (fun p : ℕ ↦ Real.log p) hr hc with hm |
    ⟨p, hp, q, hq, hpq, _, _, hm⟩
  · exact Or.inl (hm.trans hs)
  · have hpP := Nat.prime_of_mem_primeFactors hp
    have hqP := Nat.prime_of_mem_primeFactors hq
    have hd :=
      ((Nat.coprime_primes hpP hqP).mpr hpq).mul_dvd_of_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hq)
    refine Or.inr ⟨p, q, hpP, hqP, hpq, hd, ?_⟩
    rw [Nat.cast_mul,
      Real.log_mul (Nat.cast_ne_zero.mpr hpP.ne_zero) (Nat.cast_ne_zero.mpr hqP.ne_zero)]
    exact hm.trans hs

end PseudoPrime.NumberTheory
