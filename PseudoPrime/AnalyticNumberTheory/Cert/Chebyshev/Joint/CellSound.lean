/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.Prefix
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.GuardSound
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.ThetaTransfer
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrtGeneral
import PseudoPrime.Analysis.FloorIntervalBounds

/-! # From scalar prefix states to real bounds on joint cells -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- The fixed-point scale is strictly positive, so comparisons can be unscaled. -/
theorem scale_pos : 0 < (scale : ℝ) := by norm_num only [scale, Nat.cast_pow, Nat.cast_ofNat]

/-- The lower tick difference at a natural prefix bounds theta throughout its right ray.
If natural subtraction truncates, nonnegativity supplies the result. -/
theorem theta_lower_from_prefix {n l h d e : ℕ} (a : Prefix n l h d e) {x : ℝ} (hn : (n : ℝ) ≤ x) :
    ((l - d : ℕ) : ℝ) / scale ≤ Chebyshev.theta x := by
  apply le_trans ((div_le_iff₀ scale_pos).2 ?_) (Chebyshev.theta_mono hn)
  rw [mul_comm (Chebyshev.theta _)]
  by_cases hd : d ≤ l
  · simpa only [Nat.cast_sub hd] using a.thetaLo
  · rw [Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hd), Nat.cast_zero]
    exact mul_nonneg scale_pos.le (Chebyshev.theta_nonneg _)

/-- A successful lower crossing with a positive denominator yields a real inequality
at the right endpoint, including when natural subtraction truncated the error. -/
theorem lower_crossing {b l u v : ℕ} (hv : 0 < v) (hg : within (scale * b - l) b u v = true) :
    (b : ℝ) - (l : ℝ) / scale ≤ ((u : ℝ) / v) * Real.sqrt b := by
  have hn : scale * b ≤ (scale * b - l) + l := Nat.le_add_of_sub_le le_rfl
  have hr : (scale : ℝ) * b ≤ ((scale * b - l : ℕ) : ℝ) + l := by exact_mod_cast hn
  have hv' : (0 : ℝ) < v := Nat.cast_pos.mpr hv
  rw [div_mul_eq_mul_div, le_div_iff₀ hv', sub_mul, div_mul_eq_mul_div, sub_le_iff_le_add, ←
    sub_le_iff_le_add', le_div_iff₀ scale_pos]
  nlinarith only [within_sound hg, mul_le_mul_of_nonneg_right hr hv'.le]

/-- On a cell to the right of a certified prefix, the integer lower guard and a
psi estimate with smaller coefficient imply the two-sided theta estimate. -/
theorem theta_cell_of_prefix {a b l h d e u v : ℕ} {x c : ℝ} (st : Prefix a l h d e)
    (ha : (a : ℝ) ≤ x) (hb : x ≤ b) (hv : 0 < v) (hc : c ≤ (u : ℝ) / v)
    (hp : |Chebyshev.psi x - x| ≤ c * Real.sqrt x)
    (hg : within (scale * b - (l - d)) b u v = true) :
    |Chebyshev.theta x - x| ≤ ((u : ℝ) / v) * Real.sqrt x := by
  exact
    theta_abs_on_cell ((Nat.cast_nonneg a).trans ha) hb
      (div_nonneg (Nat.cast_nonneg _) scale_pos.le) (theta_lower_from_prefix st ha) hc hp
      (lower_crossing hv hg)

/-- The upper integer guard bounds the excess of the upper tick over the left endpoint. -/
theorem upper_crossing {a h u v : ℕ} (hv : 0 < v) (hg : within (h - scale * a) a u v = true) :
    (h : ℝ) / scale - a ≤ ((u : ℝ) / v) * Real.sqrt a := by
  have hn : h ≤ (h - scale * a) + scale * a := Nat.le_add_of_sub_le le_rfl
  have hr : (h : ℝ) ≤ ((h - scale * a : ℕ) : ℝ) + (scale : ℝ) * a := by exact_mod_cast hn
  have hv' := Nat.cast_pos (α := ℝ).mpr hv
  rw [div_mul_eq_mul_div, le_div_iff₀ hv', sub_mul, div_mul_eq_mul_div, sub_le_iff_le_add,
    div_le_iff₀ scale_pos]
  nlinarith only [within_sound hg, mul_le_mul_of_nonneg_right hr hv'.le]

/-- Two successful guards enclose psi at every real point of the half-open cell. -/
theorem psi_cell_of_prefix {a b l h d e L H D E u v : ℕ} {x : ℝ} (sa : Prefix a l h d e)
    (sb : Prefix (b - 1) L H D E) (hv : 0 < v) (hc : (u : ℝ) / v ≤ 2) (ha : (1 : ℝ) ≤ a)
    (hx : (a : ℝ) ≤ x) (hb : x < b) (hl : within (scale * b - l) b u v = true)
    (hh : within (H - scale * a) a u v = true) :
    |Chebyshev.psi x - x| ≤ ((u : ℝ) / v) * Real.sqrt x := by
  refine
    Arithmetic.psi_sqrt_cross_cell (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hc ha hx hb
      (lo := (l : ℝ) / scale) (hi := (H : ℝ) / scale) ?_ ?_ le_rfl le_rfl ?_ ?_
  · exact (div_le_iff₀ scale_pos).2 (by simpa only [mul_comm (scale : ℝ)] using sa.psiLo)
  · exact (le_div_iff₀ scale_pos).2 (by simpa only [mul_comm (scale : ℝ)] using sb.psiHi)
  · linarith only [lower_crossing hv hl]
  · linarith only [upper_crossing hv hh]

/-- Higher prime powers have nonnegative Mangoldt weights, so their total is monotone. -/
private theorem defect_mono : Monotone (fun x ↦ Chebyshev.psi x - Chebyshev.theta x) := by
  intro x y hxy
  simp only [Chebyshev.psi_sub_theta_eq_sum_not_prime]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc_right (Nat.floor_mono hxy))
  · exact fun n _ _ ↦ ArithmeticFunction.vonMangoldt_nonneg

/-- The upper defect tick at the last integer bounds the defect on the half-open cell. -/
theorem defect_le_of_prefix {a b l h d e : ℕ} {x : ℝ} (sb : Prefix (b - 1) l h d e)
    (ha : (a : ℝ) ≤ x) (hb : x < b) : Chebyshev.psi x - Chebyshev.theta x ≤ (e : ℝ) / scale := by
  have hf (t : ℝ) :
    Chebyshev.psi t - Chebyshev.theta t = Chebyshev.psi ⌊t⌋₊ - Chebyshev.theta ⌊t⌋₊ :=
    congrArg₂ (· - ·) (Chebyshev.psi_eq_psi_coe_floor t) (Chebyshev.theta_eq_theta_coe_floor t)
  apply (Analysis.floor_monotone_bounds defect_mono hf ha hb).2.trans
  exact (le_div_iff₀ scale_pos).2 (by linarith only [sb.defectHi])

/-- A successful integer defect guard transfers a psi estimate to theta throughout the cell. -/
theorem theta_cell_of_defect {a b l h d e u v : ℕ} {x c t : ℝ} (sb : Prefix (b - 1) l h d e)
    (ha : (a : ℝ) ≤ x) (hb : x < b) (hv : 0 < v) (hg : within e a u v = true)
    (hgap : (u : ℝ) / v ≤ t - c) (hp : |Chebyshev.psi x - x| ≤ c * Real.sqrt x) :
    |Chebyshev.theta x - x| ≤ t * Real.sqrt x := by
  have hn := div_nonneg (Nat.cast_nonneg u : (0 : ℝ) ≤ u) (Nat.cast_nonneg v)
  have hv' := Nat.cast_pos (α := ℝ).mpr hv
  have he : (e : ℝ) / scale ≤ ((u : ℝ) / v) * Real.sqrt a := by
    rw [div_le_iff₀ scale_pos, div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hv']
    linarith only [within_sound hg]
  apply theta_abs_of_defect (by linarith only [hn, hgap]) hp
  exact
    (defect_le_of_prefix sb ha hb).trans
      (he.trans (mul_le_mul hgap (Real.sqrt_le_sqrt ha) (Real.sqrt_nonneg _) (hn.trans hgap)))

/-- For an active theta cell, the two accepted guard branches give the same theta estimate.
The scalar gap hypothesis interprets the integer coefficient used by the defect guard. -/
theorem theta_cell_of_guards {a b l h d e L H D E u v : ℕ} {x c : ℝ} (sa : Prefix a l h d e)
    (sb : Prefix (b - 1) L H D E) (ha : (a : ℝ) ≤ x) (hb : x < b) (hv : 0 < v)
    (gap : ((5 * u - 4 * v : ℕ) : ℝ) / (5 * v : ℕ) ≤ (u : ℝ) / v - c)
    (hp : |Chebyshev.psi x - x| ≤ c * Real.sqrt x)
    (hg : (within E a (5 * u - 4 * v) (5 * v) || within (scale * b - (l - d)) b u v) = true) :
    |Chebyshev.theta x - x| ≤ ((u : ℝ) / v) * Real.sqrt x := by
  rcases Bool.or_eq_true_iff.mp hg with hd | hl
  · exact theta_cell_of_defect sb ha hb (Nat.mul_pos (by decide) hv) hd gap hp
  · have hn := div_nonneg (Nat.cast_nonneg (5 * u - 4 * v) : (0 : ℝ) ≤ _) (Nat.cast_nonneg (5 * v))
    exact theta_cell_of_prefix sa ha hb.le hv (by linarith only [hn, gap]) hp hl

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
