/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith

/-! # Endpoint bounds for floor-invariant functions -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- If a monotone function is unchanged by taking the natural floor, its values on
`[a, b)` are bounded below by its value at `a` and above by its value at `b - 1`.
The natural endpoints satisfy `a < b`. -/
theorem floor_monotone_bounds {f : ℝ → ℝ} (hf : Monotone f) (hfloor : ∀ t : ℝ, f t = f ⌊t⌋₊)
    {a b : ℕ} {x : ℝ} (ha : (a : ℝ) ≤ x) (hb : x < b) : f a ≤ f x ∧ f x ≤ f (b - 1 : ℕ) := by
  have hx0 : 0 ≤ x := (Nat.cast_nonneg a).trans ha
  have hlt : ⌊x⌋₊ < b := (Nat.floor_lt hx0).2 hb
  constructor
  · exact hf ha
  · rw [hfloor x]
    exact hf (Nat.cast_le.mpr (Nat.le_sub_one_of_lt hlt))

/-- Let `f` be monotone and invariant under the natural floor. If `t - E t` and
`t + E t` are nondecreasing on `[a, b]`, the displayed endpoint estimates and
cross comparisons imply `|f x - x| ≤ E x` for every `x` in `[a, b)`.
The upper value of `f` is needed only at `b - 1`. -/
theorem halfopen_error_of_endpoints {f E : ℝ → ℝ} (hf : Monotone f) (hfloor : ∀ t : ℝ, f t = f ⌊t⌋₊)
    {a b : ℕ} {L U ca cb x : ℝ} (hax : (a : ℝ) ≤ x) (hxb : x < b)
    (hminus : MonotoneOn (fun t ↦ t - E t) (Set.Icc (a : ℝ) b))
    (hplus : MonotoneOn (fun t ↦ t + E t) (Set.Icc (a : ℝ) b)) (hl : L ≤ f a)
    (hu : f (b - 1 : ℕ) ≤ U) (hca : ca ≤ E a) (hcb : cb ≤ E b) (hcrossl : (b : ℝ) ≤ L + cb)
    (hcrossu : U ≤ (a : ℝ) + ca) : |f x - x| ≤ E x := by
  have hab : (a : ℝ) ≤ b := hax.trans hxb.le
  have hbounds := floor_monotone_bounds hf hfloor hax hxb
  have hxmem : x ∈ Set.Icc (a : ℝ) b := ⟨hax, hxb.le⟩
  have hamem : (a : ℝ) ∈ Set.Icc (a : ℝ) b := ⟨le_rfl, hab⟩
  have hbmem : (b : ℝ) ∈ Set.Icc (a : ℝ) b := ⟨hab, le_rfl⟩
  have h1 := hminus hxmem hbmem hxb.le
  have h2 := hplus hamem hxmem hax
  apply abs_le.mpr
  constructor <;> linarith only [hbounds.1, hbounds.2, h1, h2, hl, hu, hca, hcb, hcrossl, hcrossu]

end PseudoPrime.Analysis
