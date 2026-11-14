/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! # Monotonicity of the integrated ψ envelope main-term margin -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The Lee–Nosal logarithmic ψ envelope `L * (L - log L) / (8π)`.
It is the comparison target for the normalized integrated envelope. -/
@[expose]
noncomputable def leeNosalPsiLog (L : ℝ) : ℝ :=
  L * (L - Real.log L) / (8 * Real.pi)

/-- The main term of the integrated ψ envelope before the smoothing and
tail remainders, with the certified target constant `-317/10000`. -/
@[expose]
noncomputable def integratedPsiMain (L : ℝ) : ℝ :=
  let a := L / 2 - Real.log (5 * L / 6)
  (5 * L / (6 * Real.pi)) / 2 + (a ^ 2 + 2 * a + 2) / (2 * Real.pi) - 317 / 10000

/-- On the half-line starting at 97/5, the logarithm lies between 8/3 and
one quarter of its argument. Bounds for log two and the tangent inequality
at eight give a table-free proof. -/
theorem log_bounds_194 {L : ℝ} (hL : (97 / 5 : ℝ) ≤ L) :
    (8 / 3 : ℝ) ≤ Real.log L ∧ Real.log L ≤ L / 4 := by
  have hL0 : 0 < L := by linarith only [hL]
  have hlower :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 16) (show (16 : ℝ) ≤ L by linarith only [hL])
  have hlog16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    have he : (16 : ℝ) = 2 ^ 4 := by norm_num only
    rw [he, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  have hlog8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    have he : (8 : ℝ) = 2 ^ 3 := by norm_num only
    rw [he, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  have ht := Real.log_le_sub_one_of_pos (div_pos hL0 (by norm_num only : (0 : ℝ) < 8))
  have he : Real.log (L / 8) = Real.log L - Real.log 8 := by
    rw [Real.log_div hL0.ne' (by norm_num only : (8 : ℝ) ≠ 0)]
  rw [he, hlog8] at ht
  constructor
  · linarith only [hlower, hlog16, Real.log_two_gt_d9]
  · linarith only [ht, Real.log_two_lt_d9, hL]

/-- The logarithmic shift in the integrated envelope is between zero and
one fifth. The upper bound is the tangent inequality for the logarithm. -/
theorem log_six_fifths_bounds : 0 ≤ Real.log (6 / 5 : ℝ) ∧ Real.log (6 / 5 : ℝ) ≤ 1 / 5 := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 6 / 5 by norm_num only)
  constructor
  · apply Real.log_nonneg
    norm_num only
  · linarith only [h]

/-- The derivative of the scaled main-term gap for a fixed logarithmic
shift. This expression is used to establish a half-line comparison. -/
theorem integrated_main_gap_deriv (k : ℝ) {L : ℝ} (hL : 0 < L) :
    HasDerivAt
      (fun t : ℝ ↦
        t * (t - Real.log t) - (10 / 3 : ℝ) * t -
          4 * ((t / 2 - Real.log t + k) ^ 2 + 2 * (t / 2 - Real.log t + k) + 2))
      (3 * Real.log L - (13 / 3 : ℝ) - 4 * k + 8 * (1 - Real.log L + k) / L) L := by
  have hi := Real.hasDerivAt_log hL.ne'
  have hid := hasDerivAt_id L
  have ha := ((hid.div_const 2).sub hi).add_const k
  have hb :=
    ((hid.mul (hid.sub hi)).sub (hid.const_mul (10 / 3 : ℝ))).sub
      (((ha.pow 2).add (ha.const_mul 2)).add_const 2 |>.const_mul 4)
  convert hb using 1
  · funext t
    simp only [Pi.sub_apply, Pi.mul_apply, Pi.add_apply, Pi.pow_apply, id_eq]
  · simp only [Pi.sub_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, div_eq_mul_inv]
    have h := mul_inv_cancel₀ hL.ne'
    linear_combination (-3 : ℝ) * h

/-- For a shift between zero and one fifth, the scaled main-term gap is
strictly increasing from 97/5 onward. The logarithm bounds make its explicit
derivative positive throughout the half-line. -/
theorem integrated_main_gap_strictMono (k : ℝ) (hk0 : 0 ≤ k) (hk1 : k ≤ 1 / 5) :
    StrictMonoOn
      (fun t : ℝ ↦
        t * (t - Real.log t) - (10 / 3 : ℝ) * t -
          4 * ((t / 2 - Real.log t + k) ^ 2 + 2 * (t / 2 - Real.log t + k) + 2))
      (Set.Ici (97 / 5 : ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _)
  · intro t ht
    change (97 / 5 : ℝ) ≤ t at ht
    have ht0 : 0 < t := by linarith only [ht]
    exact ((integrated_main_gap_deriv k ht0).continuousAt).continuousWithinAt
  · intro t ht
    have ht' : (97 / 5 : ℝ) ≤ t := interior_subset ht
    have ht0 : 0 < t := by linarith only [ht']
    have hl := log_bounds_194 ht'
    have hfrac : -(1 / 4 : ℝ) ≤ (1 - Real.log t + k) / t := by
      apply (le_div_iff₀ ht0).2
      linarith only [hl.2, hk0]
    rw [(integrated_main_gap_deriv k ht0).deriv]
    have heq : 8 * (1 - Real.log t + k) / t = 8 * ((1 - Real.log t + k) / t) := by ring
    rw [heq]
    linarith only [hl.1, hk1, hfrac]

/-- At positive logarithmic height, the difference between the Lee–Nosal
target and the integrated main term equals the scaled gap with shift
`log(6/5)`. The logarithm product identity supplies the shift. -/
theorem integrated_main_gap_eq {L : ℝ} (hL : 0 < L) :
    leeNosalPsiLog L - integratedPsiMain L =
      (L * (L - Real.log L) - (10 / 3 : ℝ) * L -
            4 *
              ((L / 2 - Real.log L + Real.log (6 / 5)) ^ 2 +
                2 * (L / 2 - Real.log L + Real.log (6 / 5)) +
                2) +
          (317 / 1250 : ℝ) * Real.pi) /
        (8 * Real.pi) := by
  have he : 5 * L / 6 = L * (6 / 5 : ℝ)⁻¹ := by ring
  have hl : Real.log (5 * L / 6) = Real.log L - Real.log (6 / 5) := by
    rw [he, Real.log_mul hL.ne' (inv_ne_zero (by norm_num only : (6 / 5 : ℝ) ≠ 0)), Real.log_inv]
    ring
  simp only [leeNosalPsiLog, integratedPsiMain, hl]
  have hp := Real.pi_ne_zero
  field_simp
  ring

/-- The difference between the Lee–Nosal logarithmic target and the
integrated envelope main term is strictly increasing from 97/5 onward.
The positive factor `1/(8π)` transfers the scaled derivative comparison. -/
theorem integratedPsiMain_gap_mono :
    StrictMonoOn (fun L ↦ leeNosalPsiLog L - integratedPsiMain L) (Set.Ici (97 / 5 : ℝ)) := by
  intro x hx y hy hxy
  have hx' : (97 / 5 : ℝ) ≤ x := hx
  have hy' : (97 / 5 : ℝ) ≤ y := hy
  have hk := log_six_fifths_bounds
  have hm := integrated_main_gap_strictMono (Real.log (6 / 5)) hk.1 hk.2 hx hy hxy
  change leeNosalPsiLog x - integratedPsiMain x < leeNosalPsiLog y - integratedPsiMain y
  rw [integrated_main_gap_eq (by linarith only [hx']),
    integrated_main_gap_eq (by linarith only [hy'])]
  apply div_lt_div_of_pos_right _ (mul_pos (by norm_num only) Real.pi_pos)
  linarith only [hm]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
