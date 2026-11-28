/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterKernel656
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseInterpolation644
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseScalar644
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterLowPhase
import PseudoPrime.Analysis.ExponentialFixedPointBounds

/-! # Real scalar form of the section 132 zero-phase endpoint sum -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The differentiated unit-cutoff coefficients, indexed from zero.
At index j the coefficient multiplies the inverse power of degree j+1. -/
noncomputable def quarterPhaseCoeff656 (j : ℕ) : ℝ :=
  let c (k : ℕ) : ℝ := if k ≤ 5 then (120 / (5 - k).factorial) * (21 / 8) ^ (5 - k) else 0
  3 / 5 * c j - c (j + 1)

/-- The phase kernel in (132.22), with the critical-line ordinate t.
The first summand retains the derivative coefficients and the second
is the full Mellin term. -/
noncomputable def quarterPhaseKernel656 (t : ℝ) : ℂ :=
  let s : ℂ := 11 / 10 + Complex.I * t
  let w : ℂ := 1 / 2 + Complex.I * t
  let C : ℝ := (11 / 10) ^ 5 * Real.exp (-(11 / 10) * (21 / 8)) / 120
  ((4 * C : ℝ) : ℂ) * (∑ j ∈ Finset.range 6, (quarterPhaseCoeff656 j : ℂ) / (w * s ^ (j + 1))) +
    ((11 / 10 : ℂ) ^ 5 * Complex.exp (Complex.I * ((21 / 8 : ℝ) * t : ℝ))) / s ^ 6

/-- The degree-five numerator of the unshifted rational term in (132.22).
Keeping a common denominator preserves cancellation in interval evaluation. -/
noncomputable def quarterPhaseNumerator656 (s : ℂ) : ℂ :=
  ∑ j ∈ Finset.range 6, (quarterPhaseCoeff656 j : ℂ) * s ^ (5 - j)

/-- The unshifted coefficient at real ordinate t, in common-denominator form.
The real exponential appears only in the normalization. -/
noncomputable def quarterPhaseRational656 (t : ℝ) : ℂ :=
  let s : ℂ := 11 / 10 + Complex.I * t
  let w : ℂ := 1 / 2 + Complex.I * t
  let C : ℝ := (11 / 10) ^ 5 * Real.exp (-(11 / 10) * (21 / 8)) / 120
  ((4 * C : ℝ) : ℂ) * (quarterPhaseNumerator656 s / (w * s ^ 6))

/-- The coefficient of the phase with shift 21/8, given by the
full Mellin term with the unit complex exponential removed. -/
noncomputable def quarterPhasePole656 (t : ℝ) : ℂ :=
  (11 / 10 : ℂ) ^ 5 / ((11 / 10 : ℂ) + Complex.I * t) ^ 6

/-- The critical-line kernel splits into two rational coefficients and a
unit phase shift. The common-denominator identity uses the six terms of
the section 132 kernel and the nonvanishing of their two linear factors. -/
theorem quarter_phase_split_656 (t : ℝ) :
    quarterPhaseKernel656 t =
      quarterPhaseRational656 t +
        quarterPhasePole656 t * Complex.exp (Complex.I * ((21 / 8 : ℝ) * t : ℝ)) := by
  let s : ℂ := 11 / 10 + Complex.I * t
  let w : ℂ := 1 / 2 + Complex.I * t
  have hs : s ≠ 0 := by
    simpa only [s, Complex.ofReal_div, Complex.ofReal_ofNat] using
      phase_line_ne_zero (a := 11 / 10) (by norm_num only) t
  have hsum :
    (∑ j ∈ Finset.range 6, (quarterPhaseCoeff656 j : ℂ) / (w * s ^ (j + 1))) =
      quarterPhaseNumerator656 s / (w * s ^ 6) := by
    unfold quarterPhaseNumerator656
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun j hj ↦ phase_term_common_den hs (Finset.mem_range.mp hj) _)
  let C : ℝ := (11 / 10) ^ 5 * Real.exp (-(11 / 10) * (21 / 8)) / 120
  change
    (↑(4 * C) : ℂ) * (∑ j ∈ Finset.range 6, (quarterPhaseCoeff656 j : ℂ) / (w * s ^ (j + 1))) + _ =
      (↑(4 * C) : ℂ) * (quarterPhaseNumerator656 s / (w * s ^ 6)) + _
  rw [hsum]
  unfold quarterPhasePole656
  ring

/-- The two coefficients multiply cosine and sine at the unshifted and
shifted angles. This real form is used by the finite endpoint certificates. -/
theorem quarter_phase_scalar_656 (x t : ℝ) :
    (Complex.exp (Complex.I * ((x * t : ℝ) : ℂ)) * quarterPhaseKernel656 t).re =
      (quarterPhaseRational656 t).re * Real.cos (x * t) -
          (quarterPhaseRational656 t).im * Real.sin (x * t) +
        ((quarterPhasePole656 t).re * Real.cos ((x + 21 / 8) * t) -
          (quarterPhasePole656 t).im * Real.sin ((x + 21 / 8) * t)) := by
  rw [quarter_phase_split_656, mul_add, Complex.add_re]
  rw [mul_comm (Complex.exp (Complex.I * ((x * t : ℝ) : ℂ))),
    mul_left_comm (Complex.exp (Complex.I * ((x * t : ℝ) : ℂ))), ← Complex.exp_add]
  have he :
    Complex.I * ((x * t : ℝ) : ℂ) + Complex.I * ((21 / 8 : ℝ) * t : ℝ) =
      (((x + 21 / 8) * t : ℝ) : ℂ) * Complex.I := by
    simp only [Complex.ofReal_mul, Complex.ofReal_add]
    ring
  rw [he, mul_comm Complex.I ((x * t : ℝ) : ℂ), complex_phase_re, complex_phase_re]
  ring

/-- Sum the section 132 scalar identity over both signs of each
ordinate. The result uses the same unshifted and shifted terms as the
endpoint enclosure. -/
theorem quarter_phase_sum_scalar_656 {n : ℕ} (g : Fin n → ℝ) (x : ℝ) :
    pairedPhase g (fun i ↦ quarterPhaseKernel656 (g i)) x =
      2 *
        ∑ i : Fin n,
          ((quarterPhaseRational656 (g i)).re * Real.cos (x * g i) -
              (quarterPhaseRational656 (g i)).im * Real.sin (x * g i) +
            ((quarterPhasePole656 (g i)).re * Real.cos ((x + 21 / 8) * g i) -
              (quarterPhasePole656 (g i)).im * Real.sin ((x + 21 / 8) * g i))) := by
  simp only [pairedPhase, quarter_phase_scalar_656]

/-- Taylor bounds on the exponential give an outward enclosure of the
normalization of the unshifted section 132 phase coefficient. -/
theorem quarter_phase_normalization_656 :
    4 * ((11 / 10 : ℝ) ^ 5 * Real.exp (-(11 / 10) * (21 / 8)) / 120) ∈
      Set.Icc (299100304093266000 / 10 ^ 20) (299100304093269000 / 10 ^ 20) := by
  have hu :=
    Analysis.exp_le_taylor_add_two_next (x := (231 / 80 : ℝ)) (n := 24) (by norm_num only)
      (by norm_num only)
  have hl := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 231 / 80) 26
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at hu hl
  have hlo := one_div_le_one_div_of_le (Real.exp_pos _) hu
  have hhi := one_div_le_one_div_of_le (by norm_num only) hl
  rw [one_div (Real.exp _), ← Real.exp_neg] at hlo hhi
  rw [show -(11 / 10 : ℝ) * (21 / 8) = -(231 / 80) by norm_num only]
  exact ⟨by linarith only [hlo], by linarith only [hhi]⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
