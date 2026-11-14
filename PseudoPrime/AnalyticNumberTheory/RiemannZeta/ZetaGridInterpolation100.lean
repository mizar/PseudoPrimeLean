/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaFiniteDerivative128
import PseudoPrime.Analysis.SecondDerivativeInterpolation

/-! # Second-order interpolation on the height-100 horizontal segment -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The real part of zeta on the height-100 horizontal line has derivative
equal to the real part of the complex derivative. -/
private theorem hasDerivAt_zeta_line (x : ℝ) :
    HasDerivAt (fun y : ℝ => (riemannZeta ((y : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)).re)
      (deriv riemannZeta ((x : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)).re x := by
  let s : ℂ := (x : ℂ) + ((100 : ℝ) : ℂ) * Complex.I
  have hs : s ≠ 1 := by
    intro he
    have hi := congrArg Complex.im he
    simp only [s, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, zero_add, add_zero, Complex.one_im] at hi
    norm_num only at hi
  have hd := (analyticOn_riemannZeta s hs).differentiableAt.hasDerivAt
  have hc := hd.comp (x : ℂ) ((hasDerivAt_id (x : ℂ)).add_const (((100 : ℝ) : ℂ) * Complex.I))
  simpa only [mul_one, Function.comp_apply, id_eq] using hc.real_of_complex

/-- The first real derivative of zeta on the height-100 line has derivative
equal to the real part of the second complex derivative. -/
private theorem hasDerivAt_zeta_line_deriv (x : ℝ) :
    HasDerivAt (fun y : ℝ => (deriv riemannZeta ((y : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)).re)
      (iteratedDeriv 2 riemannZeta ((x : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)).re x := by
  let s : ℂ := (x : ℂ) + ((100 : ℝ) : ℂ) * Complex.I
  have hs : s ≠ 1 := by
    intro he
    have hi := congrArg Complex.im he
    simp only [s, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, zero_add, add_zero, Complex.one_im] at hi
    norm_num only at hi
  have hd := (analyticOn_riemannZeta s hs).deriv.differentiableAt.hasDerivAt
  have hc := hd.comp (x : ℂ) ((hasDerivAt_id (x : ℂ)).add_const (((100 : ℝ) : ℂ) * Complex.I))
  have he : iteratedDeriv 2 riemannZeta = deriv (deriv riemannZeta) := by
    rw [show (2 : ℕ) = 1 + 1 by norm_num only, iteratedDeriv_succ, iteratedDeriv_one]
  rw [he]
  simpa only [mul_one, Function.comp_apply, id_eq] using hc.real_of_complex

/-- Every point of `[1/2,3/2]` lies in one of the 8 cells of width `1/8`.
The right endpoint is assigned to the last cell. -/
private theorem exists_grid_cell (t : ℝ) (ht : t ∈ Set.Icc (1 / 2) (3 / 2)) :
    ∃ j : ℕ, j < 8 ∧ t ∈ Set.Icc (1 / 2 + (j : ℝ) / 8) (1 / 2 + ((j + 1 : ℕ) : ℝ) / 8) := by
  by_cases he : t = 3 / 2
  · refine ⟨7, by norm_num only, ?_⟩
    rw [he]
    norm_num only [Set.mem_Icc, Nat.cast_add, Nat.cast_one, and_self]
  · have hl : t < 3 / 2 := lt_of_le_of_ne ht.2 he
    have hn : 0 ≤ 8 * (t - 1 / 2) := by nlinarith only [ht.1]
    have hj : Nat.floor (8 * (t - 1 / 2)) < 8 := by
      apply (Nat.floor_lt hn).2
      norm_num only
      nlinarith only [hl]
    refine ⟨Nat.floor (8 * (t - 1 / 2)), hj, ?_⟩
    have hlo := Nat.floor_le hn
    have hhi := Nat.lt_floor_add_one (8 * (t - 1 / 2))
    constructor
    · nlinarith only [hlo]
    · simp only [Nat.cast_add, Nat.cast_one]
      nlinarith only [hhi]

/-- Lower bounds of 1 at the 9 nodes `1/2 + j/8` imply that the real
part of zeta is positive throughout the height-100 segment. A second
derivative bound of 511 limits the interpolation loss on each cell. -/
theorem zeta_100_positive_of_grid
    (hnodes :
      ∀ j : ℕ,
        j ≤ 8 →
          1 ≤ (riemannZeta (((1 / 2 + (j : ℝ) / 8 : ℝ) : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)).re) :
    ∀ t : ℝ,
      t ∈ Set.Icc (1 / 2) (3 / 2) →
        0 < (riemannZeta ((t : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)).re := by
  intro t ht
  obtain ⟨j, hj, hcell⟩ := exists_grid_cell t ht
  have hju : j + 1 ≤ 8 := Nat.succ_le_iff.mpr hj
  have hjuR : ((j + 1 : ℕ) : ℝ) ≤ 8 := by exact_mod_cast hju
  have hsub {y : ℝ} (hy : y ∈ Set.Icc (1 / 2 + (j : ℝ) / 8) (1 / 2 + ((j + 1 : ℕ) : ℝ) / 8)) :
    y ∈ Set.Icc (1 / 2) (3 / 2) := by
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    constructor <;> nlinarith only [hy.1, hy.2, hj0, hjuR]
  have hab : (1 / 2 : ℝ) + (j : ℝ) / 8 < 1 / 2 + ((j + 1 : ℕ) : ℝ) / 8 := by
    simp only [Nat.cast_add, Nat.cast_one]
    linarith only
  have hw : (1 / 2 : ℝ) + ((j + 1 : ℕ) : ℝ) / 8 - (1 / 2 + (j : ℝ) / 8) = 1 / 8 := by
    simp only [Nat.cast_add, Nat.cast_one]
    ring
  have hbound (y : ℝ) (hy : y ∈ Set.Icc (1 / 2) (3 / 2)) :
    (iteratedDeriv 2 riemannZeta ((y : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)).re ≤ 511 := by
    exact (le_abs_self _).trans ((Complex.abs_re_le_norm _).trans (norm_deriv2_zeta_100_le y hy))
  have h :=
    Analysis.lower_bound_on_interval_of_second_deriv_le hab (by norm_num only : (0 : ℝ) ≤ 511)
      (fun y _ => hasDerivAt_zeta_line y) (fun y _ => hasDerivAt_zeta_line_deriv y)
      (fun y hy => hbound y (hsub hy)) (hnodes j hj.le) (hnodes (j + 1) hju) hcell
  rw [hw] at h
  nlinarith only [h]

/-- Under RH, 9 lower bounds for zeta on the height-100 grid imply
`N(100) ≤ 58`. Second-order interpolation supplies the positive line. -/
theorem count_100_le_58_of_grid8 (hRH : RiemannHypothesis)
    (hnodes :
      ∀ j : ℕ,
        j ≤ 8 →
          1 ≤ (riemannZeta (((1 / 2 + (j : ℝ) / 8 : ℝ) : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)).re) :
    zeroCount 100 ≤ 58 := by
  exact count_100_le_58_of_positive_line hRH (zeta_100_positive_of_grid hnodes)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
