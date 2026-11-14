/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiEnvelope226Numerics
import PseudoPrime.Analysis.LogTaylorBounds

/-! # Monotonicity of the high-range Chebyshev envelope margin -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For `L ≥ 113/5`, the logarithm lies strictly above three and at most
`L/4`. Certified endpoint bounds and the logarithm tangent inequality give
uniform estimates for the derivative of the main envelope gap. -/
theorem log_bounds_226 {L : ℝ} (hL : (113 / 5 : ℝ) ≤ L) : 3 < Real.log L ∧ Real.log L ≤ L / 4 := by
  have h22 :=
    Analysis.rationalLogIntervalCheck_sound
      (show
        Analysis.rationalLogIntervalCheck (113 / 5) 5 64 (311794 / 100000) (311796 / 100000) = true
        from by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h22
  have h8 :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck 8 3 64 (2079 / 1000) (2081 / 1000) = true from by
        decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h8
  have hL0 : 0 < L := by linarith only [hL]
  have hlower := Real.log_le_log (by norm_num only : (0 : ℝ) < 113 / 5) hL
  have ht := Real.log_le_sub_one_of_pos (div_pos hL0 (by norm_num only : (0 : ℝ) < 8))
  have he : Real.log (L / 8) = Real.log L - Real.log 8 := by
    rw [Real.log_div hL0.ne' (by norm_num only : (8 : ℝ) ≠ 0)]
  rw [he] at ht
  constructor
  · linarith only [hlower, h22.1]
  · linarith only [ht, h8.2, hL]

/-- Differentiate the scaled main gap for positive `L`. The logarithmic
shift `k` is kept as a parameter for the monotonicity argument. -/
private theorem main_gap_deriv (k : ℝ) {L : ℝ} (hL : 0 < L) :
    HasDerivAt
      (fun t : ℝ ↦
        t * (t - Real.log t) - (10 / 3 : ℝ) * t -
          4 * ((t / 2 - Real.log t + k) ^ 2 + 2 * (t / 2 - Real.log t + k) + 2))
      (3 * Real.log L - 13 / 3 - 4 * k + 8 * (1 - Real.log L + k) / L) L := by
  have hi := Real.hasDerivAt_log hL.ne'
  have hid := hasDerivAt_id L
  have ha := ((hid.div_const 2).sub hi).add_const k
  have hb :=
    ((hid.mul (hid.sub hi)).sub (hid.const_mul (10 / 3))).sub
      (((ha.pow 2).add (ha.const_mul 2)).add_const 2 |>.const_mul 4)
  convert hb using 1
  · funext t
    simp only [Pi.sub_apply, Pi.mul_apply, Pi.add_apply, Pi.pow_apply, id_eq]
  · simp only [Pi.sub_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, div_eq_mul_inv]
    have h := mul_inv_cancel₀ hL.ne'
    linear_combination (-3 : ℝ) * h

/-- If `0 ≤ k ≤ 1/5`, the scaled main envelope gap is strictly increasing
on `[113/5, ∞)`. The logarithm bounds make its derivative positive. -/
private theorem main_gap_strictMono (k : ℝ) (hk0 : 0 ≤ k) (hk1 : k ≤ 1 / 5) :
    StrictMonoOn
      (fun t : ℝ ↦
        t * (t - Real.log t) - (10 / 3 : ℝ) * t -
          4 * ((t / 2 - Real.log t + k) ^ 2 + 2 * (t / 2 - Real.log t + k) + 2))
      (Set.Ici (113 / 5 : ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _)
  · intro t ht
    change (113 / 5 : ℝ) ≤ t at ht
    exact ((main_gap_deriv k (by linarith only [ht])).continuousAt).continuousWithinAt
  · intro t ht
    have ht' : (113 / 5 : ℝ) ≤ t := interior_subset ht
    have ht0 : 0 < t := by linarith only [ht']
    have hlogt := log_bounds_226 ht'
    have hfrac : -(1 / 4 : ℝ) ≤ (1 - Real.log t + k) / t := by
      apply (le_div_iff₀ ht0).2
      linarith only [hlogt.2, hk0]
    rw [(main_gap_deriv k ht0).deriv]
    have heq : 8 * (1 - Real.log t + k) / t = 8 * ((1 - Real.log t + k) / t) := by ring
    rw [heq]
    linarith only [hlogt.1, hk1, hfrac]

/-- For every `L ≥ 113/5`, the Lee–Nosal normalized target exceeds the
main part of the combined-zero envelope by more than `11/2000`. The scaled
gap increases from the independently certified endpoint value. -/
theorem envelope226_main_gap_uniform {L : ℝ} (hL : (113 / 5 : ℝ) ≤ L) :
    (11 / 2000 : ℝ) <
      (L * (L - Real.log L) - (10 / 3 : ℝ) * L -
          4 * ((L / 2 - Real.log (5 * L / 6)) ^ 2 + 2 * (L / 2 - Real.log (5 * L / 6)) + 2) -
          (16 / 5 : ℝ) * Real.pi) /
        (8 * Real.pi) := by
  let k := Real.log (6 / 5 : ℝ)
  have hk0 : 0 ≤ k := Real.log_nonneg (by norm_num only)
  have hk1 : k ≤ 1 / 5 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 6 / 5)
    linarith only [h]
  have hmono :=
    (main_gap_strictMono k hk0 hk1).monotoneOn
      (show (113 / 5 : ℝ) ∈ Set.Ici (113 / 5 : ℝ) from le_rfl) hL hL
  have hlog (t : ℝ) (ht : 0 < t) : Real.log (5 * t / 6) = Real.log t - k := by
    have h : 5 * t / 6 = t * (5 / 6) := by ring
    rw [h, Real.log_mul ht.ne' (by norm_num only : (5 / 6 : ℝ) ≠ 0)]
    have he : (5 / 6 : ℝ) = (6 / 5 : ℝ)⁻¹ := by norm_num only
    rw [he, Real.log_inv]
    rfl
  have hla : L / 2 - Real.log L + k = L / 2 - Real.log (5 * L / 6) := by
    rw [hlog L (by linarith only [hL])]
    ring
  have hla0 : (113 / 5 : ℝ) / 2 - Real.log (113 / 5) + k = (113 / 10 : ℝ) - Real.log (113 / 6) := by
    have hl := hlog (113 / 5) (by norm_num only)
    norm_num only at hl ⊢
    linarith only [hl]
  rw [hla, hla0] at hmono
  have hdiv :=
    div_le_div_of_nonneg_right (sub_le_sub_right hmono ((16 / 5 : ℝ) * Real.pi))
      (show 0 ≤ 8 * Real.pi by nlinarith only [Real.pi_pos])
  exact lt_of_lt_of_le envelope226_main_gap hdiv

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
