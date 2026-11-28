/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevIntervalPrefix
import Mathlib.Tactic

/-! # Signed Chebyshev floors from prime-power prefix rows -/

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- A signed lower bound for psi on a real interval follows from its value
at the right endpoint and the left limits at the prime powers inside it.
The rows use the prefix through the preceding integer. -/
public theorem psi_signed_floor_of_jumps {l u e : ℝ} (hl : 0 ≤ l) (hend : e ≤ Chebyshev.psi u - u)
    (hjump : ∀ m : ℕ, IsPrimePow m → (m : ℝ) ∈ Set.Ioc l u → e ≤ Chebyshev.psi (m - 1 : ℕ) - m)
    {x : ℝ} (hx : x ∈ Set.Icc l u) : e ≤ Chebyshev.psi x - x := by
  classical
  have hx0 : 0 ≤ x := hl.trans hx.1
  have hu0 : 0 ≤ u := hx0.trans hx.2
  let n := ⌊x⌋₊
  let b := ⌊u⌋₊
  have hnb : n ≤ b := Nat.floor_mono hx.2
  rw [Chebyshev.psi_eq_psi_coe_floor]
  by_cases h : ∃ m : ℕ, n < m ∧ m ≤ b ∧ IsPrimePow m
  · let m := Nat.find h
    obtain ⟨hnm, hmb, hm⟩ := Nat.find_spec h
    have hxm : x < (m : ℝ) := (Nat.floor_lt hx0).mp hnm
    have hmu : (m : ℝ) ≤ u := (Nat.le_floor_iff hu0).mp hmb
    have hnm' : n ≤ m - 1 := Nat.le_sub_one_of_lt hnm
    have hgap : ∀ k ∈ Finset.Ioc n (m - 1), ¬IsPrimePow k := by
      intro k hk hp
      obtain ⟨hnk, hkm⟩ := Finset.mem_Ioc.mp hk
      have hmin : m ≤ k := Nat.find_min' h ⟨hnk, (hkm.trans (Nat.sub_le _ _)).trans hmb, hp⟩
      exact (Nat.not_le.mpr (Nat.sub_lt (Nat.zero_lt_of_lt hnm) Nat.zero_lt_one)) (hmin.trans hkm)
    have he := hjump m hm ⟨hx.1.trans_lt hxm, hmu⟩
    rw [psi_eq_of_no_prime_power hnm' hgap] at he
    exact he.trans (sub_le_sub_left hxm.le _)
  · have hgap : ∀ k ∈ Finset.Ioc n b, ¬IsPrimePow k := by
      intro k hk hp
      obtain ⟨hnk, hkb⟩ := Finset.mem_Ioc.mp hk
      exact h ⟨k, hnk, hkb, hp⟩
    rw [Chebyshev.psi_eq_psi_coe_floor, psi_eq_of_no_prime_power hnb hgap] at hend
    exact hend.trans (sub_le_sub_left hx.2 _)

end PseudoPrime.AnalyticNumberTheory.Arithmetic
