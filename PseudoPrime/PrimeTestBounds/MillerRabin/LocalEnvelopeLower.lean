/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.LocalEnvelopeMonotone
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimePairLogSquareBounds

/-! # Lower bounds for the local witness envelope -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At any scale at least `log 9`, the common local envelope is at least three. The
plain square, adaptive square, moderate guard and every even anchor separately exceed
three. This allows the prime factor three to be used directly in local pair arguments. -/
theorem three_le_local_full {s : ℝ} (hs : Real.log 9 ≤ s) : 3 ≤ localFullEnvelope s := by
  have h9 : (0 : ℝ) ≤ Real.log 9 := Real.log_natCast_nonneg 9
  have hs2 : (3 : ℝ) ≤ s ^ 2 :=
    (three_le_log_sq_of_nine_le (m := 9) (by norm_num only)).trans (pow_le_pow_left₀ h9 hs 2)
  have ha : (3 : ℝ) ≤ (Analysis.adaptivePart2CutoffRoot (max 7 s)) ^ 2 := by
    have h := adaptive_clamped_radius_ge_seven s
    nlinarith only [h]
  have hg : (3 : ℝ) ≤ localInterpolatedGuard s := by
    have h :=
      le_max_left (61 : ℝ)
        ((1 - localInterpolationWeight s) * ((81 / 100 : ℝ) * s ^ 2) +
          localInterpolationWeight s * (Analysis.adaptivePart2CutoffRoot (max 7 s)) ^ 2)
    change (61 : ℝ) ≤ localInterpolatedGuard s at h
    linarith only [h]
  have he : (3 : ℝ) ≤ localEvenEnvelope s := by
    apply Finset.le_inf'
    intro ⟨b, d, j⟩ hm
    have hm' : (b, d, j) ∈ localEvenAnchors := List.mem_toFinset.mp hm
    have hc := (List.all_eq_true.mp localEvenAnchors_checked) (b, d, j) hm'
    have hbq : (8 : ℚ) ≤ b := (of_decide_eq_true hc).1
    have hb : (8 : ℝ) ≤ b := by exact_mod_cast hbq
    have hm := le_max_left (b : ℝ) (s - d)
    nlinarith only [hb, hm]
  exact le_min (le_min hs2 (le_min ha hg)) he

end PseudoPrime.PrimeTestBounds.MillerRabin
