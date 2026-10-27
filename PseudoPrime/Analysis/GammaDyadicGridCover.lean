/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaDyadicGridCertificate

/-! # Real interval coverage of the dyadic rational grid -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Every real scale in [20000,40000) belongs to one of the two hundred
certified grid intervals. The natural floor of (x-20000)/100 supplies its
index, and the floor inequalities give both endpoints. This proves that
the finite grid certificates cover all real scales in the bounded range. -/
theorem gamma_dyadic_grid_covers {x : ℝ} (hlo : 20000 ≤ x) (hhi : x < 40000) :
    ∃ i ∈ Finset.range 200,
      (gammaDyadicGridLower i : ℝ) ≤ x ∧ x ≤ (gammaDyadicGridUpper i : ℝ) := by
  have ht : (0 : ℝ) ≤ (x - 20000) / 100 := by linarith only [hlo]
  let i := ⌊(x - 20000) / 100⌋₊
  have hil : (i : ℝ) ≤ (x - 20000) / 100 := Nat.floor_le ht
  have hiu : (x - 20000) / 100 < (i : ℝ) + 1 := Nat.lt_floor_add_one _
  have him : i < 200 :=
    (Nat.floor_lt ht).mpr
      (by
        norm_num only; linarith only [hhi])
  refine ⟨i, Finset.mem_range.mpr him, ?_, ?_⟩
  · norm_num only [gammaDyadicGridLower, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat,
      Rat.cast_natCast]
    linarith only [hil]
  · norm_num only [gammaDyadicGridUpper, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat,
      Rat.cast_natCast]
    linarith only [hiu]

end PseudoPrime.Analysis
