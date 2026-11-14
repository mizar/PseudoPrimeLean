/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiEnvelope20Numerics
import PseudoPrime.Analysis.LogTaylorBounds

/-! # Uniform main-term margin for the height-20 ψ envelope -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For `L ≥ 20`, `log L` lies above `299/100` and below `L/4`. A certified
endpoint bound and the logarithm tangent inequality give these estimates. -/
theorem log_bounds_20 {L : ℝ} (hL : (20 : ℝ) ≤ L) :
    (299 / 100 : ℝ) < Real.log L ∧ Real.log L ≤ L / 4 := by
  have h20 :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck 20 4 64 (299572 / 100000) (299574 / 100000) = true
        from by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h20
  have h8 :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck 8 3 64 (2079 / 1000) (2081 / 1000) = true from by
        decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h8
  have hL0 : 0 < L := by linarith only [hL]
  have hlower := Real.log_le_log (by norm_num only : (0 : ℝ) < 20) hL
  have ht := Real.log_le_sub_one_of_pos (div_pos hL0 (by norm_num only : (0 : ℝ) < 8))
  have he : Real.log (L / 8) = Real.log L - Real.log 8 := by
    rw [Real.log_div hL0.ne' (by norm_num only : (8 : ℝ) ≠ 0)]
  rw [he] at ht
  constructor
  · linarith only [hlower, h20.1]
  · linarith only [ht, h8.2, hL]

/-- The logarithmic shift `log(4/π)` lies in `[0,1/3]`. Elementary bounds
for π and the logarithm tangent inequality give the required range. -/
private theorem log_four_div_pi_bounds :
    0 ≤ Real.log (4 / Real.pi) ∧ Real.log (4 / Real.pi) ≤ 1 / 3 := by
  have hp : 0 < Real.pi := Real.pi_pos
  have hratio : (1 : ℝ) ≤ 4 / Real.pi := by
    apply (le_div_iff₀ hp).2
    linarith only [Real.pi_lt_four]
  have hu : (4 / Real.pi : ℝ) ≤ 4 / 3 := by
    apply (div_le_div_iff₀ hp (by norm_num only : (0 : ℝ) < 3)).2
    linarith only [Real.pi_gt_three]
  have h := Real.log_le_sub_one_of_pos (div_pos (by norm_num only : (0 : ℝ) < 4) hp)
  exact ⟨Real.log_nonneg hratio, by linarith only [h, hu]⟩

/-- Differentiate the scaled main-term gap with a fixed logarithmic shift.
This form is used to prove monotonicity above height 20. -/
private theorem main_gap20_deriv (k : ℝ) {L : ℝ} (hL : 0 < L) :
    HasDerivAt
      (fun t : ℝ ↦
        t * (t - Real.log t) - Real.pi * t -
          4 * ((t / 2 - Real.log t + k) ^ 2 + 2 * (t / 2 - Real.log t + k) + 2))
      (3 * Real.log L - (1 + Real.pi) - 4 * k + 8 * (1 - Real.log L + k) / L) L := by
  have hi := Real.hasDerivAt_log hL.ne'
  have hid := hasDerivAt_id L
  have ha := ((hid.div_const 2).sub hi).add_const k
  have hb :=
    ((hid.mul (hid.sub hi)).sub (hid.const_mul Real.pi)).sub
      (((ha.pow 2).add (ha.const_mul 2)).add_const 2 |>.const_mul 4)
  convert hb using 1
  · funext t
    simp only [Pi.sub_apply, Pi.mul_apply, Pi.add_apply, Pi.pow_apply, id_eq]
  · simp only [Pi.sub_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, div_eq_mul_inv]
    have h := mul_inv_cancel₀ hL.ne'
    linear_combination (-3 : ℝ) * h

/-- For `0 ≤ k ≤ 1/3`, the scaled main-term gap is strictly increasing on
`[20, ∞)`. Its derivative is positive by the uniform logarithm bounds. -/
private theorem main_gap20_strictMono (k : ℝ) (hk0 : 0 ≤ k) (hk1 : k ≤ 1 / 3) :
    StrictMonoOn
      (fun t : ℝ ↦
        t * (t - Real.log t) - Real.pi * t -
          4 * ((t / 2 - Real.log t + k) ^ 2 + 2 * (t / 2 - Real.log t + k) + 2))
      (Set.Ici (20 : ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _)
  · intro t ht
    change (20 : ℝ) ≤ t at ht
    exact ((main_gap20_deriv k (by linarith only [ht])).continuousAt).continuousWithinAt
  · intro t ht
    have ht' : (20 : ℝ) ≤ t := interior_subset ht
    have ht0 : 0 < t := by linarith only [ht']
    have hlogt := log_bounds_20 ht'
    have hfrac : -(1 / 4 : ℝ) ≤ (1 - Real.log t + k) / t := by
      apply (le_div_iff₀ ht0).2
      linarith only [hlogt.2, hk0]
    rw [(main_gap20_deriv k ht0).deriv]
    have heq : 8 * (1 - Real.log t + k) / t = 8 * ((1 - Real.log t + k) / t) := by ring
    rw [heq]
    linarith only [hlogt.1, hk1, hfrac, Real.pi_lt_four]

/-- For every `L ≥ 20`, the Lee–Nosal target exceeds the main term of the
height-100 combined-zero envelope by more than `1/100`. The scaled gap is
increasing and its endpoint is certified using rational logarithm bounds. -/
theorem envelope20_main_gap_uniform {L : ℝ} (hL : 20 ≤ L) :
    (1 / 100 : ℝ) <
      (L * (L - Real.log L) - Real.pi * L -
          4 *
            ((L / 2 - Real.log (Real.pi * L / 4)) ^ 2 + 2 * (L / 2 - Real.log (Real.pi * L / 4)) +
              2) -
          (8 / 25 : ℝ) * Real.pi) /
        (8 * Real.pi) := by
  let k := Real.log (4 / Real.pi)
  have hk := log_four_div_pi_bounds
  have hm :=
    (main_gap20_strictMono k hk.1 hk.2).monotoneOn (show (20 : ℝ) ∈ Set.Ici (20 : ℝ) from le_rfl) hL
      hL
  have hlog (t : ℝ) (ht : 0 < t) : Real.log (Real.pi * t / 4) = Real.log t - k := by
    have he : Real.pi * t / 4 = t * (Real.pi / 4) := by ring
    rw [he, Real.log_mul ht.ne' (div_ne_zero Real.pi_ne_zero (by norm_num only))]
    have hi : Real.pi / 4 = (4 / Real.pi)⁻¹ := by simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    rw [hi, Real.log_inv]
    ring
  have hla : L / 2 - Real.log L + k = L / 2 - Real.log (Real.pi * L / 4) := by
    rw [hlog L (by linarith only [hL])]
    ring
  have hla0 : (20 : ℝ) / 2 - Real.log 20 + k = 10 - Real.log (5 * Real.pi) := by
    have hl := hlog 20 (by norm_num only)
    have he : Real.pi * (20 : ℝ) / 4 = 5 * Real.pi := by ring
    rw [he] at hl
    linarith only [hl]
  change
    (20 : ℝ) * (20 - Real.log 20) - Real.pi * 20 -
        4 * ((20 / 2 - Real.log 20 + k) ^ 2 + 2 * (20 / 2 - Real.log 20 + k) + 2) ≤
      L * (L - Real.log L) - Real.pi * L -
        4 * ((L / 2 - Real.log L + k) ^ 2 + 2 * (L / 2 - Real.log L + k) + 2) at hm
  rw [hla, hla0] at hm
  have hdiv :=
    div_le_div_of_nonneg_right (sub_le_sub_right hm ((8 / 25 : ℝ) * Real.pi))
      (show 0 ≤ 8 * Real.pi by nlinarith only [Real.pi_pos])
  exact lt_of_lt_of_le envelope20_main_gap hdiv

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
