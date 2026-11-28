/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseCurvature644
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterLowPhase

/-! # Real scalar form of the section 122 zero-phase endpoint sum -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The degree-five numerator of the unshifted rational term in (122.28).
Keeping a common denominator preserves cancellation in interval evaluation. -/
noncomputable def quarterPhaseNumerator644 (s : ℂ) : ℂ :=
  ∑ j ∈ Finset.range 6, (quarterPhaseCoeff644 j : ℂ) * s ^ (5 - j)

/-- The unshifted coefficient at real ordinate t, in common-denominator form.
The real exponential appears only in the normalization. -/
noncomputable def quarterPhaseRational644 (t : ℝ) : ℂ :=
  let s : ℂ := 107 / 100 + Complex.I * t
  let w : ℂ := 1 / 2 + Complex.I * t
  let C : ℝ := (107 / 100) ^ 5 * Real.exp (-(107 / 100) * (2687 / 1000)) / 120
  ((4 * C : ℝ) : ℂ) * (quarterPhaseNumerator644 s / (w * s ^ 6))

/-- The coefficient of the phase with shift 2687/1000, given by the
full Mellin term with the unit complex exponential removed. -/
noncomputable def quarterPhasePole644 (t : ℝ) : ℂ :=
  (107 / 100 : ℂ) ^ 5 / ((107 / 100 : ℂ) + Complex.I * t) ^ 6

private theorem phase_line_ne_zero {a : ℝ} (ha : a ≠ 0) (t : ℝ) : (a : ℂ) + Complex.I * t ≠ 0 := by
  intro h
  apply ha
  simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero, Complex.zero_re] using
    congrArg Complex.re h

private theorem phase_term_common_den {s w : ℂ} (hs : s ≠ 0) {j : ℕ} (hj : j < 6) (d : ℂ) :
    d / (w * s ^ (j + 1)) = (d * s ^ (5 - j)) / (w * s ^ 6) := by
  have he : j + 1 + (5 - j) = 6 :=
    calc
      _ = j + (5 - j) + 1 := by ac_rfl
      _ = _ := by rw [Nat.add_sub_of_le (Nat.le_of_lt_succ hj)]
  have hd : (w * s ^ (j + 1)) * s ^ (5 - j) = w * s ^ 6 := by rw [mul_assoc, ← pow_add, he]
  rw [← hd]
  exact (mul_div_mul_right _ _ (pow_ne_zero _ hs)).symm

/-- The critical-line kernel splits into two rational coefficients and a
unit phase shift. The common-denominator identity uses the six terms of
the section 122 kernel and the nonvanishing of their two linear factors. -/
theorem quarter_phase_split_644 (t : ℝ) :
    quarterPhaseKernel644 t =
      quarterPhaseRational644 t +
        quarterPhasePole644 t * Complex.exp (Complex.I * ((2687 / 1000 : ℝ) * t : ℝ)) := by
  let s : ℂ := 107 / 100 + Complex.I * t
  let w : ℂ := 1 / 2 + Complex.I * t
  have hs : s ≠ 0 := by
    simpa only [s, Complex.ofReal_div, Complex.ofReal_ofNat] using
      phase_line_ne_zero (a := 107 / 100) (by norm_num only) t
  have hsum :
    (∑ j ∈ Finset.range 6, (quarterPhaseCoeff644 j : ℂ) / (w * s ^ (j + 1))) =
      quarterPhaseNumerator644 s / (w * s ^ 6) := by
    unfold quarterPhaseNumerator644
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun j hj ↦ phase_term_common_den hs (Finset.mem_range.mp hj) _)
  let C : ℝ := (107 / 100) ^ 5 * Real.exp (-(107 / 100) * (2687 / 1000)) / 120
  change
    (↑(4 * C) : ℂ) * (∑ j ∈ Finset.range 6, (quarterPhaseCoeff644 j : ℂ) / (w * s ^ (j + 1))) + _ =
      (↑(4 * C) : ℂ) * (quarterPhaseNumerator644 s / (w * s ^ 6)) + _
  rw [hsum]
  unfold quarterPhasePole644
  ring

/-- The two coefficients multiply cosine and sine at the unshifted and
shifted angles. This real form is used by the finite endpoint certificates. -/
theorem quarter_phase_scalar_644 (x t : ℝ) :
    (Complex.exp (Complex.I * ((x * t : ℝ) : ℂ)) * quarterPhaseKernel644 t).re =
      (quarterPhaseRational644 t).re * Real.cos (x * t) -
          (quarterPhaseRational644 t).im * Real.sin (x * t) +
        ((quarterPhasePole644 t).re * Real.cos ((x + 2687 / 1000) * t) -
          (quarterPhasePole644 t).im * Real.sin ((x + 2687 / 1000) * t)) := by
  rw [quarter_phase_split_644, mul_add, Complex.add_re]
  rw [mul_comm (Complex.exp (Complex.I * ((x * t : ℝ) : ℂ))),
    mul_left_comm (Complex.exp (Complex.I * ((x * t : ℝ) : ℂ))), ← Complex.exp_add]
  have he :
    Complex.I * ((x * t : ℝ) : ℂ) + Complex.I * ((2687 / 1000 : ℝ) * t : ℝ) =
      (((x + 2687 / 1000) * t : ℝ) : ℂ) * Complex.I := by
    simp only [Complex.ofReal_mul, Complex.ofReal_add]
    ring
  rw [he, mul_comm Complex.I ((x * t : ℝ) : ℂ), complex_phase_re, complex_phase_re]
  ring

/-- The paired phase sum is a real finite sum of the two scalar terms
at each ordinate. This equality allows the endpoint checker to supply
a scalar lower bound directly to the curvature interpolation theorem. -/
theorem quarter_phase_sum_scalar_644 (g : Fin 29 → ℝ) (x : ℝ) :
    pairedPhase g (fun i ↦ quarterPhaseKernel644 (g i)) x =
      2 *
        ∑ i : Fin 29,
          ((quarterPhaseRational644 (g i)).re * Real.cos (x * g i) -
              (quarterPhaseRational644 (g i)).im * Real.sin (x * g i) +
            ((quarterPhasePole644 (g i)).re * Real.cos ((x + 2687 / 1000) * g i) -
              (quarterPhasePole644 (g i)).im * Real.sin ((x + 2687 / 1000) * g i))) := by
  simp only [pairedPhase, quarter_phase_scalar_644]

end PseudoPrime.PrimeTestBounds.MillerRabin
