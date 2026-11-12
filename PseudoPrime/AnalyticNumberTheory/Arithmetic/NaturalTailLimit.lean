/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.AbelSummation

/-! # Limits of finite natural-number tails -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For a summable real series whose zeroth term vanishes, tails beginning
strictly above a fixed real cutoff converge to the total sum minus its finite
prefix. Both finite intervals retain their upper endpoints. -/
theorem tendsto_tail_prefix (f : ℕ → ℝ) (hf0 : f 0 = 0) (hf : Summable f) (a : ℝ) :
    Filter.Tendsto (fun n : ℕ ↦ ∑ m ∈ Finset.Ioc ⌊a⌋₊ n, f m) Filter.atTop
      (nhds ((∑' m : ℕ, f m) - ∑ m ∈ Finset.Ioc 0 ⌊a⌋₊, f m)) := by
  have ht := hf.hasSum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
  have ht' :
    Filter.Tendsto (fun n : ℕ ↦ ∑ m ∈ Finset.Ioc 0 n, f m) Filter.atTop (nhds (∑' m : ℕ, f m)) := by
    apply Filter.Tendsto.congr (fun n ↦ ?_) ht
    dsimp only [Function.comp_apply]
    rw [Nat.range_eq_Icc_zero_sub_one (n + 1) (Nat.add_one_ne_zero n), Nat.add_sub_cancel, ←
      Finset.sum_Ioc_add_eq_sum_Icc (Nat.zero_le n)]
    simp only [hf0, add_zero]
  have hm := ht'.sub_const (∑ m ∈ Finset.Ioc 0 ⌊a⌋₊, f m)
  apply Filter.Tendsto.congr' ?_ hm
  apply (Filter.eventually_ge_atTop ⌊a⌋₊).mono
  intro n hn
  have hd : Disjoint (Finset.Ioc 0 ⌊a⌋₊) (Finset.Ioc ⌊a⌋₊ n) :=
    Finset.disjoint_left.mpr
      (fun m hm ht ↦ (not_lt_of_ge (Finset.mem_Ioc.mp hm).2) (Finset.mem_Ioc.mp ht).1)
  have he := Finset.sum_union (f := f) hd
  rw [Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) hn] at he
  dsimp only
  linarith only [he]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
