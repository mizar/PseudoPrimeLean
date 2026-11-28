/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevPsiLeeNosal
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Chebyshev boundary errors for the middle Gaussian range -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Lee–Nosal's logarithmic profile is bounded by one twenty-fourth of the square. -/
private theorem middle_rho_le_square {s : ℝ} (hs : 1 ≤ s) :
    s * (s - Real.log s) / (8 * Real.pi) ≤ s ^ 2 / 24 := by
  have hs0 : 0 ≤ s := zero_le_one.trans hs
  have hpi : (24 : ℝ) ≤ 8 * Real.pi := by linarith only [Real.pi_gt_three]
  calc
    _ ≤ s ^ 2 / (8 * Real.pi) := by
      rw [pow_two]
      exact
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (sub_le_self _ (Real.log_nonneg hs)) hs0)
          (le_trans (by norm_num only) hpi)
    _ ≤ _ := div_le_div_of_nonneg_left (sq_nonneg s) (by norm_num only) hpi

/-- For two points with logarithms `s` and `s + b`, the weighted normalized RH errors
fit the quadratic budget `β * (s / 2)^2` when `s ≥ 20` and the scalar budget holds. -/
private theorem middle_psi_boundary_le (hRH : RiemannHypothesis) {x z s b w c β : ℝ} (hx : 101 ≤ x)
    (hz : 101 ≤ z) (hxs : Real.log x = s) (hzs : Real.log z = s + b) (hs : 20 ≤ s) (hb : 0 ≤ b)
    (hw : 0 ≤ w) (hc : 0 ≤ c) (hβ : (4 * w + c * (2 + b / 10) ^ 2) / 6 ≤ β) :
    4 * w * (|Chebyshev.psi x - x| / Real.sqrt x) + 4 * c * (|Chebyshev.psi z - z| / Real.sqrt z) ≤
      β * (s / 2) ^ 2 := by
  have hs1 : 1 ≤ s := le_trans (by norm_num only) hs
  have hsb1 : 1 ≤ s + b := hs1.trans (le_add_of_nonneg_right hb)
  have hxρ := AnalyticNumberTheory.Arithmetic.psi_lee_nosal_of_RH hRH hx
  have hzρ := AnalyticNumberTheory.Arithmetic.psi_lee_nosal_of_RH hRH hz
  rw [hxs] at hxρ
  rw [hzs] at hzρ
  have hshift : s + b ≤ (2 + b / 10) * (s / 2) := by
    nlinarith only [mul_le_mul_of_nonneg_left hs hb]
  have hsq :=
    (sq_le_sq₀ (zero_le_one.trans hsb1) ((zero_le_one.trans hsb1).trans hshift)).mpr hshift
  calc
    _ ≤ 4 * w * (s ^ 2 / 24) + 4 * c * ((s + b) ^ 2 / 24) :=
      add_le_add
        (mul_le_mul_of_nonneg_left (hxρ.trans (middle_rho_le_square hs1))
          (mul_nonneg (by norm_num only) hw))
        (mul_le_mul_of_nonneg_left (hzρ.trans (middle_rho_le_square hsb1))
          (mul_nonneg (by norm_num only) hc))
    _ ≤ 4 * w * (s ^ 2 / 24) + 4 * c * (((2 + b / 10) * (s / 2)) ^ 2 / 24) :=
      add_le_add le_rfl
        (mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hsq (by norm_num only : (0 : ℝ) ≤ 24))
          (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4) hc))
    _ = ((4 * w + c * (2 + b / 10) ^ 2) / 6) * (s / 2) ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hβ (sq_nonneg _)

/-- Under RH, the weighted normalized errors at `exp s` and `exp (s + b)` fit
the quadratic boundary budget for `s ≥ 20`, nonnegative shift and weights, and the
stated coefficient inequality. This supplies the middle Gaussian boundary term. -/
public theorem middle_exp_psi_boundary_le (hRH : RiemannHypothesis) {s b w c β : ℝ} (hs : 20 ≤ s)
    (hb : 0 ≤ b) (hw : 0 ≤ w) (hc : 0 ≤ c) (hβ : (4 * w + c * (2 + b / 10) ^ 2) / 6 ≤ β) :
    4 * w * (|Chebyshev.psi (Real.exp s) - Real.exp s| / Real.sqrt (Real.exp s)) +
        4 * c *
          (|Chebyshev.psi (Real.exp (s + b)) - Real.exp (s + b)| / Real.sqrt (Real.exp (s + b))) ≤
      β * (s / 2) ^ 2 := by
  have h101 : (101 : ℝ) ≤ Real.exp 20 :=
    (by norm_num only : (101 : ℝ) ≤ 1 + 20 + 20 ^ 2 / 2).trans
      (Real.quadratic_le_exp_of_nonneg (by norm_num only))
  exact
    middle_psi_boundary_le hRH (h101.trans (Real.exp_le_exp.mpr hs))
      (h101.trans (Real.exp_le_exp.mpr (hs.trans (le_add_of_nonneg_right hb)))) (Real.log_exp _)
      (Real.log_exp _) hs hb hw hc hβ

/-- The shared rational bounds on the boundary weights fit the coefficient `61/1000`. -/
private theorem middle_boundary_budget {w κ v : ℝ} (hw : w ≤ 903 / 10000) (hκ : κ ≤ 7 / 1000)
    (hv : v ≤ 2 / 25) (hv0 : 0 ≤ v) :
    (4 * w + (κ * v) * (2 + (7 / 2) / 10) ^ 2) / 6 ≤ 61 / 1000 := by
  have hprod : κ * v ≤ (7 / 1000 : ℝ) * (2 / 25) := mul_le_mul hκ hv hv0 (by norm_num only)
  norm_num only at hprod ⊢
  linarith only [hw, hprod]

/-- The K141 and K156 boundary terms fit `61/1000` once their weights
satisfy the stated rational caps. -/
public theorem middle_boundary_le_061 (hRH : RiemannHypothesis) {s w κ v : ℝ} (hs : 20 ≤ s)
    (hw0 : 0 ≤ w) (hw : w ≤ 903 / 10000) (hκ0 : 0 ≤ κ) (hκ : κ ≤ 7 / 1000) (hv0 : 0 ≤ v)
    (hv : v ≤ 2 / 25) :
    4 * w * (|Chebyshev.psi (Real.exp s) - Real.exp s| / Real.sqrt (Real.exp s)) +
        4 * (κ * v) *
          (|Chebyshev.psi (Real.exp (s + 7 / 2)) - Real.exp (s + 7 / 2)| /
            Real.sqrt (Real.exp (s + 7 / 2))) ≤
      (61 / 1000) * (s / 2) ^ 2 := by
  exact
    middle_exp_psi_boundary_le hRH hs (by norm_num only) hw0 (mul_nonneg hκ0 hv0)
      (middle_boundary_budget hw hκ hv hv0)

/-- The principal cutoff term and the compensation variation fit the common
quadratic budget. The nonnegative centering constant can be dropped in a lower bound. -/
public theorem middle_signed_boundary (hRH : RiemannHypothesis) {s W w κ v : ℝ} (hs : 20 ≤ s)
    (hw0 : 0 ≤ w) (hw : w ≤ 903 / 10000) (hκ0 : 0 ≤ κ) (hκ : κ ≤ 7 / 1000) (hv0 : 0 ≤ v)
    (hv : v ≤ 2 / 25) (hW : W = w / Real.sqrt (Real.exp s)) :
    -(61 / 1000) * (s / 2) ^ 2 ≤
      4 * (W * (Chebyshev.psi (Real.exp s) - Real.exp s + Real.log (2 * Real.pi))) -
        4 * κ * ((s + 7 / 2) ^ 2 / 24 * v) := by
  have hβ := middle_boundary_budget hw hκ hv hv0
  have hr : 0 < Real.sqrt (Real.exp s) := Real.sqrt_pos_of_pos (Real.exp_pos _)
  have hlog : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith only [Real.pi_gt_three])
  have hsign :=
    mul_le_mul_of_nonneg_left
      ((neg_abs_le (Chebyshev.psi (Real.exp s) - Real.exp s)).trans (le_add_of_nonneg_right hlog))
      (div_nonneg hw0 hr.le)
  have h101 : (101 : ℝ) ≤ Real.exp s := by
    have h20 := Real.quadratic_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 20)
    exact
      ((by norm_num only : (101 : ℝ) ≤ 1 + 20 + 20 ^ 2 / 2).trans h20).trans
        (Real.exp_le_exp.mpr hs)
  have hρ := AnalyticNumberTheory.Arithmetic.psi_lee_nosal_of_RH hRH h101
  rw [Real.log_exp] at hρ
  have hψ :=
    mul_le_mul_of_nonneg_left
      (hρ.trans (middle_rho_le_square ((by norm_num only : (1 : ℝ) ≤ 20).trans hs)))
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4) hw0)
  have hshift : s + 7 / 2 ≤ (2 + (7 / 2) / 10) * (s / 2) := by linarith only [hs]
  have hsz : 0 ≤ s + 7 / 2 := by linarith only [hs]
  have hsq := (sq_le_sq₀ hsz (hsz.trans hshift)).mpr hshift
  have hV :=
    mul_le_mul_of_nonneg_left hsq
      (div_nonneg (mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4) hκ0) hv0)
        (by norm_num only : (0 : ℝ) ≤ 24))
  have hcost := mul_le_mul_of_nonneg_right hβ (sq_nonneg (s / 2))
  rw [hW]
  let A := |Chebyshev.psi (Real.exp s) - Real.exp s|
  let Q := (2 + (7 / 2) / 10) * (s / 2)
  calc
    _ ≤ -(((4 * w + κ * v * (2 + (7 / 2) / 10) ^ 2) / 6) * (s / 2) ^ 2) := by
      rw [neg_mul]
      exact neg_le_neg hcost
    _ = -(4 * w * (s ^ 2 / 24)) - (4 * κ * v / 24) * Q ^ 2 := by
      dsimp only [Q]; ring
    _ ≤ -(4 * w * (A / Real.sqrt (Real.exp s))) - (4 * κ * v / 24) * (s + 7 / 2) ^ 2 :=
      sub_le_sub (neg_le_neg hψ) hV
    _ = 4 * (w / Real.sqrt (Real.exp s) * -A) - 4 * κ * ((s + 7 / 2) ^ 2 / 24 * v) := by ring
    _ ≤ _ := sub_le_sub_right (mul_le_mul_of_nonneg_left hsign (by norm_num only)) _

end PseudoPrime.PrimeTestBounds.MillerRabin
