/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogSquareRootBounds
public import PseudoPrime.LLS.CosetScaledComparison

/-! # Coarse and refined radii in the explicit coset prime argument

The logarithmic decay certificate absorbs the coarse error, and the resulting
cutoff bound sharpens every remaining cutoff logarithm.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For index at least two and level logarithm at least nine, a coarse radius
inequality with relative error one hundredth implies twice the subgroup scale.
The positive product of the index minus one and the logarithm minus nine absorbs
the fixed linear term. This is the algebraic bootstrap in the coset argument. -/
private theorem coset_rough_radius {s h L : ℝ} (hh : 2 ≤ h) (hL : 9 ≤ L)
    (hbound : s ≤ (h - 1) * L + (5 / 4 : ℝ) * (h + 1) + s / 100) : s ≤ 2 * (h - 1) * L := by
  have hh0 : 0 ≤ h - 1 := by linarith only [hh]
  have hprod := mul_nonneg hh0 (show 0 ≤ L - 9 by linarith only [hL])
  nlinarith only [hbound, hh, hprod]

/-- At modulus at least twenty thousand, index at least two and cutoff at least
one billion, the coarse Section 4 radius inequality implies a square-root bound
of twice the index-minus-one scale times the modulus logarithm. Absorb the two
cutoff logarithmic terms by the explicit square-root fraction, then use the
algebraic bootstrap. The coarse radius inequality remains the displayed input. -/
theorem coset_cutoff_le_twice_scale {q h : ℕ} (hq : 20000 ≤ q) (hh : 2 ≤ h) {x : ℝ}
    (hx : 1000000000 ≤ x)
    (hc :
      Real.sqrt x ≤
        ((h : ℝ) - 1) * Real.log q + (5 / 4 : ℝ) * ((h : ℝ) + 1) + (7 / 2 : ℝ) * Real.log x +
          (Real.log x) ^ 2 / (3 * ((h : ℝ) - 1))) :
    Real.sqrt x ≤ 2 * ((h : ℝ) - 1) * Real.log q := by
  have hhR : (2 : ℝ) ≤ h := by exact_mod_cast hh
  have hd : (1 : ℝ) ≤ (h : ℝ) - 1 := by linarith only [hhR]
  have hm :=
    div_le_div_of_nonneg_left (sq_nonneg (Real.log x)) (by norm_num only : (0 : ℝ) < 3)
      (by linarith only [hd] : (3 : ℝ) ≤ 3 * ((h : ℝ) - 1))
  have hb := Analysis.log_error_le_sqrt_hundredth hx
  have hl : (9 : ℝ) ≤ Real.log q := by
    have he :=
      Real.log_le_log (by norm_num only : (0 : ℝ) < 19683)
        (show (19683 : ℝ) ≤ q by exact_mod_cast (by linarith only [hq] : 19683 ≤ q))
    rw [show (19683 : ℝ) = 3 ^ 9 by norm_num only, Real.log_pow] at he
    norm_num only at he
    linarith only [he, Real.log_three_gt_d9]
  exact coset_rough_radius hhR hl (by linarith only [hc, hm, hb])

/-- Under the modulus, index and cutoff lower bounds, the coarse Section 4 radius
inequality implies its refined logarithmic radius. First bound the cutoff square
root by twice the subgroup scale, then replace the cutoff logarithm and its square
by the logarithm of that upper radius. This completes the numerical bootstrap
once the weighted character comparison supplies the coarse inequality. -/
theorem coset_refined_radius_of_coarse_bound {q h : ℕ} (hq : 20000 ≤ q) (hh : 2 ≤ h) {x : ℝ}
    (hx : 1000000000 ≤ x)
    (hc :
      Real.sqrt x ≤
        ((h : ℝ) - 1) * Real.log q + (5 / 4 : ℝ) * ((h : ℝ) + 1) + (7 / 2 : ℝ) * Real.log x +
          (Real.log x) ^ 2 / (3 * ((h : ℝ) - 1))) :
    Real.sqrt x ≤
      ((h : ℝ) - 1) * Real.log q + (5 / 4 : ℝ) * ((h : ℝ) + 1) +
        7 * Real.log (2 * ((h : ℝ) - 1) * Real.log q) +
        4 * (Real.log (2 * ((h : ℝ) - 1) * Real.log q)) ^ 2 / (3 * ((h : ℝ) - 1)) := by
  have hb := coset_cutoff_le_twice_scale hq hh hx hc
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num only) hx
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg ((by norm_num only : (1 : ℝ) ≤ 1000000000).trans hx)
  have hd : (0 : ℝ) < 3 * ((h : ℝ) - 1) := by
    have hr : (2 : ℝ) ≤ h := by exact_mod_cast hh
    linarith only [hr]
  have hlog := Real.log_le_log hx0 (Real.sqrt_le_iff.mp hb).2
  rw [Real.log_pow] at hlog
  norm_num only at hlog
  have hs := mul_self_le_mul_self hl0 hlog
  have hs' := div_le_div_of_nonneg_right hs hd.le
  simp only [← pow_two, mul_pow] at hs'
  nlinarith only [hc, hlog, hs']

end PseudoPrime.LLS.PaperStatements
