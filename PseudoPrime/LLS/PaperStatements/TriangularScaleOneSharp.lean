/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RelativeChebyshevLowerBounds
public import PseudoPrime.LLS.PaperStatements.TriangularScaleOneAbel

/-! # Relative Chebyshev input for the sharper scale-one bound -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under RH from 16 onward, use relative width 1/(3 t^(1/4)) in the existing
Chebyshev lower bound. The resulting explicit error supplies the sharper
scale-one Abel estimate without a new prime-distribution assumption. -/
theorem scaleOne_psi_lower (hRH : RiemannHypothesis) {t : ℝ} (ht : 16 ≤ t) :
    t - (19 / 30 : ℝ) * t ^ (3 / 4 : ℝ) - (63 / 10 : ℝ) * t ^ (1 / 4 : ℝ) - 1839 / 1000 ≤
      Chebyshev.psi t := by
  have hp : 0 < t := by linarith only [ht]
  let q := t ^ (1 / 4 : ℝ)
  have hq0 : 0 ≤ q := Real.rpow_nonneg hp.le _
  have hq2 : q ^ 2 = Real.sqrt t := by
    have he := Real.rpow_mul hp.le (1 / 4) 2
    norm_num only [Real.rpow_two] at he
    rw [Real.sqrt_eq_rpow]
    exact he.symm
  have hsq : (4 : ℝ) ≤ Real.sqrt t := by
    apply (Real.le_sqrt (by norm_num only) hp.le).mpr
    nlinarith only [ht]
  have hq : 2 ≤ q := by nlinarith only [hq0, hq2, hsq]
  have hqp : 0 < q := by linarith only [hq]
  let h := 1 / (3 * q)
  have hh : 0 < h := div_pos zero_lt_one (mul_pos (by norm_num only) hqp)
  have hh1 : h ≤ 1 / 2 := by
    apply (div_le_iff₀ (mul_pos (by norm_num only) hqp)).mpr
    nlinarith only [hq]
  have hpow : t ^ (3 / 4 : ℝ) * q = t := by
    dsimp only [q]
    rw [← Real.rpow_add hp]
    norm_num only [Real.rpow_one]
  have hdiv : t / q = t ^ (3 / 4 : ℝ) := (div_eq_iff hqp.ne').mpr hpow.symm
  have hsqrt : Real.sqrt t * q = t ^ (3 / 4 : ℝ) := by
    dsimp only [q]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hp]
    norm_num only
  have hprod : h * t = (1 / 3 : ℝ) * t ^ (3 / 4 : ℝ) := by
    dsimp only [h]
    calc
      _ = (1 / 3 : ℝ) * (t / q) := by ring
      _ = _ := by rw [hdiv]
  have herr :
    (Real.sqrt t / 10 + 21 / 10) / h = (3 / 10 : ℝ) * t ^ (3 / 4 : ℝ) + (63 / 10) * q := by
    dsimp only [h]
    have hinv : (1 / (3 * q))⁻¹ = 3 * q := by rw [one_div, inv_inv]
    rw [div_eq_mul_inv, hinv]
    calc
      _ = (3 / 10 : ℝ) * (Real.sqrt t * q) + (63 / 10) * q := by ring
      _ = _ := by rw [hsqrt]
  have hb := LLS.psi_lower_relative_log_shift hRH hh hh1 hp.le
  have hmain : (1 - h) * t = t - (1 / 3 : ℝ) * t ^ (3 / 4 : ℝ) := by nlinarith only [hprod]
  rw [hmain, herr] at hb
  exact (by linarith only [hb])

/-- The inverse-fourth-root error profile has the explicit primitive needed for
the sharper Abel bound. Differentiate the logarithmic power expression on positive inputs. -/
theorem scaleOne_quarter_deriv {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun z : ℝ ↦ z ^ (-1 / 4 : ℝ) * (-68 + 2 * Real.log z))
      (u ^ (-5 / 4 : ℝ) * (19 - Real.log u / 2)) u := by
  have h :=
    (Real.hasDerivAt_rpow_const (p := -1 / 4) (Or.inl hu.ne')).mul
      ((Real.hasDerivAt_log hu.ne').const_mul 2 |>.const_add (-68))
  have hp : u ^ (-1 / 4 : ℝ) = u ^ (-5 / 4 : ℝ) * u := by
    have e := Real.rpow_add hu (-5 / 4) 1
    norm_num only [Real.rpow_one] at e
    simpa only [neg_div] using e
  apply h.congr_deriv
  norm_num only
  simp only [neg_div] at hp
  rw [hp]
  have hm : u⁻¹ * u = 1 := inv_mul_cancel₀ hu.ne'
  have hr : u * (2 * u⁻¹) = 2 := by nlinarith only [hm]
  have he : u ^ (-(5 / 4 : ℝ)) * u * (2 * u⁻¹) = u ^ (-(5 / 4 : ℝ)) * 2 := by rw [mul_assoc, hr]
  rw [he]
  ring

end PseudoPrime.LLS.PaperStatements
