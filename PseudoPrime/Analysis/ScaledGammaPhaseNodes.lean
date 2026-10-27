/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ScaledRationalPhase
public import PseudoPrime.Analysis.RationalGammaPhaseNodes

/-! # Low-degree scaled rational Gamma phase endpoints -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: a phase within epsilon of a rational center of magnitude at most 128.
Claim: the scaled rational phase has error at most epsilon+8747/10^12.
Proof: combine unit-phase stability and the certified scaled evaluator.
Role: supply a uniform phase uncertainty allowance at spectral nodes. -/
theorem norm_scaled_phase_interval_error {θ ε : ℝ} (v : ℚ) (hv : |(v : ℝ)| ≤ 128)
    (hε : |θ - (v : ℝ)| ≤ ε) :
    ‖Complex.exp (Complex.I * θ) - rationalComplexCast (rationalScaledPhase (10 ^ 12) v 16 7)‖ ≤
      ε + 8747 / 1000000000000 := by
  have ht :=
    norm_sub_le_norm_sub_add_norm_sub (Complex.exp (Complex.I * θ))
      (Complex.exp (Complex.I * (v : ℂ)))
      (rationalComplexCast (rationalScaledPhase (10 ^ 12) v 16 7))
  have hc := norm_phase_exp_sub_le θ (v : ℝ)
  simp only [Complex.ofReal_ratCast] at hc
  exact ht.trans (add_le_add (hc.trans hε) (norm_scaled_phase_grid12_error v hv))

/-- Input: a coefficient norm cap and a certified phase enclosure with center magnitude at most 128.
Claim: the scaled product real part minus its error is a lower bound for the actual phase.
Proof: bound real parts by norms and multiply the uniform scaled error.
Role: preserve signed Gamma-phase savings in finite arithmetic certificates. -/
theorem phase_product_re_lower_of_scaled {C : ℂ} {K θ ε : ℝ} (v : ℚ) (hK : ‖C‖ ≤ K)
    (hv : |(v : ℝ)| ≤ 128) (hε : |θ - (v : ℝ)| ≤ ε) :
    (C * rationalComplexCast (rationalScaledPhase (10 ^ 12) v 16 7)).re -
        K * (ε + 8747 / 1000000000000) ≤
      (C * Complex.exp (Complex.I * θ)).re := by
  have h := norm_scaled_phase_interval_error v hv hε
  have hm := mul_le_mul hK h (norm_nonneg _) ((norm_nonneg _).trans hK)
  have hr :=
    Complex.abs_re_le_norm
      (C *
        (Complex.exp (Complex.I * θ) - rationalComplexCast (rationalScaledPhase (10 ^ 12) v 16 7)))
  rw [norm_mul, mul_sub, Complex.sub_re] at hr
  have ha := (abs_le.mp (hr.trans hm)).1
  linarith only [ha]

/-- Input: Euler grid, ordinate, rational phase center and uncertainty.
Output: the rational resolvent plus scaled Gamma product minus the full phase error.
Role: evaluate endpoint gaps with a fixed length-16 Taylor sum and seven rounded squares. -/
def rationalScaledPhase64Lower (G : ℕ) (t v ε : ℚ) : ℚ :=
  let C := rationalGamma256Coefficient G t
  rationalSignedResolvent phaseResolvent64Coefficients t +
      (rationalComplexMul C (rationalScaledPhase (10 ^ 12) v 16 7)).1 -
    (|C.1| + |C.2|) * (ε + 8747 / 1000000000000)

/-- Input: a rational phase center of magnitude at most 128 and an actual phase enclosure.
Claim: the executable lower value is below the rounded Gamma-resolvent gap.
Proof: identify the exact rational coefficient and apply the scaled product estimate.
Role: replace high-degree direct Taylor endpoint checks in continuous arithmetic bounds. -/
theorem rationalScaledPhase64Lower_le {x : ℝ} (G : ℕ) (t v ε : ℚ) (hv : |(v : ℝ)| ≤ 128)
    (hphase : |(t : ℝ) * Real.log (256 * x) - (v : ℝ)| ≤ (ε : ℝ)) :
    (rationalScaledPhase64Lower G t v ε : ℝ) ≤ roundedPhase64Gap G x t := by
  have h :=
    phase_product_re_lower_of_scaled v
      (norm_rationalComplexCast_le (rationalGamma256Coefficient G t)) hv hphase
  have hp :=
    congrArg Complex.re
      (rationalComplexCast_mul (rationalGamma256Coefficient G t)
        (rationalScaledPhase (10 ^ 12) v 16 7))
  change
    ((rationalComplexMul (rationalGamma256Coefficient G t)
            (rationalScaledPhase (10 ^ 12) v 16 7)).1 :
        ℝ) =
      (rationalComplexCast (rationalGamma256Coefficient G t) *
          rationalComplexCast (rationalScaledPhase (10 ^ 12) v 16 7)).re at hp
  simp only [Rat.cast_add, Rat.cast_abs] at h
  rw [rationalGamma256Coefficient_cast] at h hp
  dsimp only [rationalScaledPhase64Lower]
  simp only [Rat.cast_sub, Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_abs, Rat.cast_ofNat]
  rw [rationalSignedResolvent_cast]
  dsimp only [roundedPhase64Gap]
  rw [hp]
  linarith only [h]

end PseudoPrime.Analysis
