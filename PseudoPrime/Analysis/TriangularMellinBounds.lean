/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.TriangularMellin

/-! # Uniform decay of the triangular Mellin kernel

Entire continuation controls the kernel near zero. The exponential quotient
gives quadratic decay uniformly on the strip with real part between -1 and 1.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Outside the unit disk, the exponential quotient bounds the kernel after
multiplication by the squared norm. The strip bounds both exponentials. -/
private theorem triangular_large_norm_bound {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : |s.re| ≤ 1)
    (hn : 1 ≤ ‖s‖) : ‖triangularMellinFunction a s‖ * ‖s‖ ^ 2 ≤ (2 * Real.exp a) ^ 2 := by
  have hs0 : s ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hn
    exact (not_le_of_gt (by norm_num only : (0 : ℝ) < 1)) hn
  have he1 : ‖Complex.exp ((a : ℂ) * s)‖ ≤ Real.exp a := by
    rw [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact Real.exp_le_exp.mpr (by nlinarith only [(abs_le.mp hs).2, ha])
  have he2 : ‖Complex.exp (-((a : ℂ) * s))‖ ≤ Real.exp a := by
    rw [Complex.norm_exp, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    exact Real.exp_le_exp.mpr (by nlinarith only [(abs_le.mp hs).1, ha])
  have he :=
    (norm_sub_le (Complex.exp ((a : ℂ) * s)) (Complex.exp (-((a : ℂ) * s)))).trans
      (add_le_add he1 he2)
  rw [triangularMellinFunction_of_ne_zero ha.ne' hs0, norm_pow, norm_div]
  have hd :
    (‖Complex.exp ((a : ℂ) * s) - Complex.exp (-((a : ℂ) * s))‖ / ‖s‖) * ‖s‖ =
      ‖Complex.exp ((a : ℂ) * s) - Complex.exp (-((a : ℂ) * s))‖ :=
    div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hs0)
  rw [← mul_pow, hd]
  have ht := mul_self_le_mul_self (norm_nonneg _) he
  nlinarith only [ht]

/-- Continuity of the entire kernel gives a positive bound on the closed unit
 disk. This supplies the compact part of the uniform strip estimate. -/
private theorem triangular_compact_bound (a : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ s : ℂ, ‖s‖ ≤ 1 → ‖triangularMellinFunction a s‖ ≤ B := by
  obtain ⟨B, hB⟩ :=
    (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
      (differentiable_triangularMellinFunction a).continuous.continuousOn
  refine ⟨|B| + 1, by linarith only [abs_nonneg B], ?_⟩
  intro s hs
  have hm : s ∈ Metric.closedBall (0 : ℂ) 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hs
  exact (hB s hm).trans (by linarith only [le_abs_self B])

/-- For a positive parameter, the triangular kernel has uniform quadratic
 decay on `|s.re| ≤ 1`. Compactness handles zero, and the explicit exponential
 quotient handles the complement of the unit disk. This estimate supplies the
 decay condition for the triangular Mellin kernel and bounds shifted integrals. -/
theorem triangularMellinFunction_strip_bound {a : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, |s.re| ≤ 1 → ‖triangularMellinFunction a s‖ ≤ C / (1 + ‖s‖ ^ 2) := by
  obtain ⟨B, hB, hb⟩ := triangular_compact_bound a
  let A := (2 * Real.exp a) ^ 2
  have hA : 0 ≤ A := sq_nonneg _
  refine ⟨2 * B + 2 * A, by linarith only [hB, hA], ?_⟩
  intro s hs
  have hN : 0 ≤ ‖triangularMellinFunction a s‖ := norm_nonneg _
  apply (le_div_iff₀ (by nlinarith only [sq_nonneg ‖s‖] : 0 < 1 + ‖s‖ ^ 2)).mpr
  by_cases hn : ‖s‖ ≤ 1
  · have hh := hb s hn
    have hn0 : 0 ≤ ‖s‖ := norm_nonneg _
    have hn2 : ‖s‖ ^ 2 ≤ 1 := by nlinarith only [hn, hn0]
    have hm := mul_le_mul_of_nonneg_left hn2 hN
    nlinarith only [hh, hm, hA]
  · have hn1 : 1 ≤ ‖s‖ := (lt_of_not_ge hn).le
    have hh := triangular_large_norm_bound ha hs hn1
    have hn2 : 1 ≤ ‖s‖ ^ 2 := by nlinarith only [hn1]
    have hm := mul_le_mul_of_nonneg_left hn2 hN
    change ‖triangularMellinFunction a s‖ * ‖s‖ ^ 2 ≤ A at hh
    nlinarith only [hh, hm, hB]

end PseudoPrime.Analysis
