/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith

/-! # Selecting finite subsets by their total weight

Double counting and a finite averaging bound control the number of fixed-size subsets whose
nonnegative weights have a prescribed upper bound.
-/

@[expose] public section

namespace PseudoPrime.Combinatorics

/-- If nonnegative weights on a finite set have total at most `(τ - δ) * card s`, the
number of entries with weight below `τ` satisfies `δ * card s ≤ τ * card good`.
The complementary entries each contribute at least `τ`; comparison of the two sums gives the
bound. It supplies the selection step for counting small-weight subsets. -/
theorem card_lt_weight_of_sum {α : Type*} (s : Finset α) (w : α → ℝ) (τ δ : ℝ)
    (hw : ∀ x ∈ s, 0 ≤ w x) (havg : (∑ x ∈ s, w x) ≤ (τ - δ) * s.card) :
    δ * s.card ≤ τ * (s.filter fun x ↦ w x < τ).card := by
  classical
  let bad := s.filter fun x ↦ ¬w x < τ
  have hb : τ * (bad.card : ℝ) ≤ ∑ x ∈ bad, w x := by
    have h :=
      Finset.sum_le_sum (s := bad) (f := fun _ ↦ τ) (g := w)
        (fun x hx ↦ le_of_not_gt (Finset.mem_filter.mp hx).2)
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_comm] using h
  have hs : (∑ x ∈ bad, w x) ≤ ∑ x ∈ s, w x :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun x hx _ ↦ hw x hx)
  have hc := Finset.card_filter_add_card_filter_not (s := s) (fun x ↦ w x < τ)
  have hc' : ((s.filter fun x ↦ w x < τ).card : ℝ) + bad.card = s.card := by exact_mod_cast hc
  have hcτ := congrArg (fun z : ℝ ↦ τ * z) hc'
  nlinarith only [hb, hs, havg, hcτ]

/-- For `1 ≤ k`, the sum of the weights of all `k`-element subsets equals the sum on
`s` multiplied by `choose (card s - 1) (k - 1)`. Interchange the two finite sums and
count subsets containing each element. This computes the average used in subset selection. -/
theorem sum_powersetCard_weight {α : Type*} (s : Finset α) (w : α → ℝ) {k : ℕ} (hk : 1 ≤ k) :
    (∑ t ∈ s.powersetCard k, ∑ x ∈ t, w x) =
      (Nat.choose (s.card - 1) (k - 1) : ℝ) * ∑ x ∈ s, w x := by
  classical
    calc
    _ = ∑ t ∈ s.powersetCard k, ∑ x ∈ s, if x ∈ t then w x else 0 := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter,
        Finset.inter_eq_right.mpr (Finset.mem_powersetCard.mp ht).1]
    _ = ∑ x ∈ s, ∑ t ∈ s.powersetCard k, if x ∈ t then w x else 0 := Finset.sum_comm
    _ = ∑ x ∈ s, (Nat.choose (s.card - 1) (k - 1) : ℝ) * w x := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      congr 1
      exact_mod_cast
        (by
          simpa only [Finset.singleton_subset_iff, Finset.card_singleton] using
            Finset.card_filter_powersetCard_subset {x} s k (Finset.singleton_subset_iff.mpr hx)
              (by simpa only [Finset.card_singleton] using hk))
    _ = _ := (Finset.mul_sum s w _).symm

/-- For nonnegative weights and `1 ≤ k`, a bound on their total gives a lower bound on the
number of `k`-element subsets with weight below `τ`. Double counting turns the hypothesis
into a bound on the total subset weight, then the finite averaging estimate selects the subsets.
This is the counting interface for products with a prescribed logarithmic size. -/
theorem card_powersetCard_weight_lt {α : Type*} (s : Finset α) (w : α → ℝ) (τ δ : ℝ) {k : ℕ}
    (hk : 1 ≤ k) (hw : ∀ x ∈ s, 0 ≤ w x)
    (havg :
      (Nat.choose (s.card - 1) (k - 1) : ℝ) * (∑ x ∈ s, w x) ≤ (τ - δ) * Nat.choose s.card k) :
    δ * Nat.choose s.card k ≤ τ * ((s.powersetCard k).filter fun t ↦ (∑ x ∈ t, w x) < τ).card := by
  classical
  have hh :=
    card_lt_weight_of_sum (s.powersetCard k) (fun t ↦ ∑ x ∈ t, w x) τ δ
      (fun t ht ↦ Finset.sum_nonneg (fun x hx ↦ hw x ((Finset.mem_powersetCard.mp ht).1 hx)))
  rw [sum_powersetCard_weight s w hk, Finset.card_powersetCard] at hh
  exact hh havg

/-- For positive `m` and `k`, an upper bound on `k * W / m` gives the corresponding
binomial-weight inequality without division. The standard binomial identity clears `m`,
and positivity permits cancellation. This converts an ordinary mean bound to the input
of fixed-size subset selection. -/
theorem choose_weight_of_mean (m k : ℕ) (W τ δ : ℝ) (hk : 1 ≤ k) (hm : 1 ≤ m)
    (ha : (k : ℝ) * W ≤ (τ - δ) * m) :
    (Nat.choose (m - 1) (k - 1) : ℝ) * W ≤ (τ - δ) * Nat.choose m k := by
  have hn : m * Nat.choose (m - 1) (k - 1) = k * Nat.choose m k := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.mul_comm] using
      (Nat.add_one_mul_choose_eq m k)
  have he : (m : ℝ) * Nat.choose (m - 1) (k - 1) = k * Nat.choose m k := by exact_mod_cast hn
  have ha' := mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg (Nat.choose m k) : (0 : ℝ) ≤ _)
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hm)
  have he' := congrArg (fun x : ℝ ↦ x * W) he
  have hh :
    (m : ℝ) * ((Nat.choose (m - 1) (k - 1) : ℝ) * W) ≤ (m : ℝ) * ((τ - δ) * Nat.choose m k) := by
    nlinarith only [ha', he']
  exact (mul_le_mul_iff_right₀ hm').mp hh

/-- If `s` is nonempty, `k ≥ 1`, and the average subset weight is at most `τ - δ`,
at least the displayed fraction of its `k`-element subsets has weight below `τ`.
Convert the mean estimate with the binomial identity and apply the subset selection bound.
The division-free form is suited to explicit arithmetic budgets. -/
theorem card_powersetCard_lt_of_mean {α : Type*} (s : Finset α) (w : α → ℝ) (τ δ : ℝ) {k : ℕ}
    (hk : 1 ≤ k) (hs : 1 ≤ s.card) (hw : ∀ x ∈ s, 0 ≤ w x)
    (havg : (k : ℝ) * (∑ x ∈ s, w x) ≤ (τ - δ) * s.card) :
    δ * Nat.choose s.card k ≤ τ * ((s.powersetCard k).filter fun t ↦ (∑ x ∈ t, w x) < τ).card := by
  exact card_powersetCard_weight_lt s w τ δ hk hw (choose_weight_of_mean s.card k _ τ δ hk hs havg)

end PseudoPrime.Combinatorics
