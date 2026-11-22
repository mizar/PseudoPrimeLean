/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.SieveBounds
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.PowerTable

/-! # Scalar lookup of higher prime powers in a segment -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- The higher powers up to one million with their prime bases. -/
def powerEntries (bases : Array ℕ) : List (ℕ × ℕ) :=
  bases.toList.flatMap fun p ↦
    ((List.range 18).map fun i ↦ (p ^ (i + 2), p)).filter (fun v ↦ decide (v.1 ≤ 1000000))

private theorem checked : highPowers = powerEntries basePrimes := by decide +kernel

private theorem mem_high {n p : ℕ} :
    (n, p) ∈ highPowers ↔ n ≤ 1000000 ∧ baseHas p = true ∧ ∃ i < 18, p ^ (i + 2) = n := by
  rw [checked, powerEntries, List.mem_flatMap]
  simp only [List.mem_filter, List.mem_map, List.mem_range, Prod.mk.injEq, Array.mem_toList_iff,
    decide_eq_true_eq]
  constructor
  · rintro ⟨q, hq, ⟨i, hi, hn, rfl⟩, hu⟩
    exact ⟨hu, Array.contains_iff_mem.mpr hq, i, hi, hn⟩
  · rintro ⟨hu, hq, i, hi, hn⟩
    exact ⟨p, Array.contains_iff_mem.mp hq, ⟨i, hi, hn, rfl⟩, hu⟩

/-- Return a scalar lookup function after filtering the shared table to this segment. -/
def lookupPower (entries : List (ℕ × ℕ)) (a b : ℕ) : ℕ → ℕ :=
  let hits := entries.filter (fun v ↦ decide (a ≤ v.1 ∧ v.1 < b))
  fun n ↦
  match hits.find? (fun v ↦ v.1 == n) with
  | some v => v.2
  | none => 0

/-- The higher-power marker from the shared table at an absolute index. -/
abbrev powerAt :=
  lookupPower highPowers

/-- At a nonprime in the segment, zero excludes every prime power. A nonzero
result gives a prime base and an exponent at least two for the queried integer. -/
theorem powerAt_spec {a b n : ℕ} (ha : a ≤ n) (hb : n < b) (hu : n ≤ 1000000) (hc : ¬n.Prime) :
    (powerAt a b n = 0 → ¬IsPrimePow n) ∧
      (powerAt a b n ≠ 0 → (powerAt a b n).Prime ∧ ∃ k ≥ 2, (powerAt a b n) ^ k = n) := by
  unfold powerAt lookupPower
  split
  next v hv =>
    obtain ⟨q, p⟩ := v
    have he : q = n := eq_of_beq (List.find?_some (p := fun v : ℕ × ℕ ↦ v.1 == n) hv)
    subst q
    have hmem := (List.mem_filter.mp (List.mem_of_find?_eq_some hv)).1
    obtain ⟨_, hp, i, _, hi⟩ := mem_high.mp hmem
    have hpr := ((baseHas_iff _).mp hp).2
    exact ⟨fun hz ↦ False.elim (hpr.ne_zero hz), fun _ ↦ ⟨hpr, i + 2, Nat.le_add_left 2 i, hi⟩⟩
  next hn =>
    constructor
    · intro _ hh
      obtain ⟨p, k, hp, hk, ht, hpr, he⟩ := composite_power_range hu hc hh
      have hrow : (n, p) ∈ highPowers :=
        mem_high.mpr
          ⟨hu, (baseHas_iff _).2 ⟨Nat.lt_succ_of_le hp, hpr⟩, k - 2, Nat.sub_lt_sub_right hk ht, by
            rwa [Nat.sub_add_cancel hk]⟩
      exact
        List.find?_eq_none.mp hn (n, p) (List.mem_filter.mpr ⟨hrow, decide_eq_true ⟨ha, hb⟩⟩)
          (beq_self_eq_true n)
    · intro h
      exact False.elim (h rfl)

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
