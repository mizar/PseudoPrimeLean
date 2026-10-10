/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.UnitDiskMinimum
public import PseudoPrime.LLS.PrimePowerFiniteComparison

/-! Finite prime-power lower comparison for all roots in the closed unit disk. -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For a prime below a cutoff at least one hundred, each root of norm at most one has
weighted real prime-power sum at least the sum for the root minus one. Regard the finite
sum as a complex polynomial and extend the unit-circle comparison by the minimum principle.
This supplies the local arithmetic lower bound for general admissible L-functions. -/
theorem prime_disk_interval_comparison {x : ℝ} (hx : 100 ≤ x) {p : ℕ} (hp : p.Prime)
    (hpx : (p : ℝ) ≤ x) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    (∑ k ∈ Finset.Icc 1 (p.log ⌊x⌋₊), primePowerComparisonWeight x p k * (-1 : ℝ) ^ k) ≤
      ∑ k ∈ Finset.Icc 1 (p.log ⌊x⌋₊), primePowerComparisonWeight x p k * (z ^ k).re := by
  let g : ℂ → ℂ := fun w ↦
    ∑ k ∈ Finset.Icc 1 (p.log ⌊x⌋₊), (primePowerComparisonWeight x p k : ℂ) * w ^ k
  have hg : Differentiable ℂ g :=
    Differentiable.fun_sum fun k _ ↦ (differentiable_const _).mul (differentiable_id.pow k)
  have he (w : ℂ) :
    (g w).re = ∑ k ∈ Finset.Icc 1 (p.log ⌊x⌋₊), primePowerComparisonWeight x p k * (w ^ k).re := by
    simp only [g, Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero]
  have hb :
    ∀ w : ℂ,
      ‖w‖ = 1 →
        (∑ k ∈ Finset.Icc 1 (p.log ⌊x⌋₊), primePowerComparisonWeight x p k * (-1 : ℝ) ^ k) ≤
          (g w).re := by
    intro w hw
    have h := prime_unit_interval_comparison hx hp hpx hw
    rw [he]
    simp only [mul_sub, Finset.sum_sub_distrib] at h
    exact sub_nonneg.mp h
  rw [← he]
  exact Analysis.lower_re_on_unitDisk hg hb hz

end PseudoPrime.LLS.PaperStatements
