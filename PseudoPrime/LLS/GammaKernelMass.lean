/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaKernel
public import PseudoPrime.Analysis.InverseSqrtPolynomial
public import PseudoPrime.Analysis.ExponentialAbsoluteIntegral
public import Mathlib.Analysis.Real.Pi.Bounds

/-! # Certified upper bound for the gamma-kernel mass

A rational polynomial majorant expands into a finite sum of integrable
exponentials. Its integral and rational pi bounds certify the kernel mass.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- At each height the gamma norm is bounded by the rational polynomial
majorant after exponential substitution. Euler reflection and the certified
squared polynomial inequality prove the norm comparison.
This gives a finite exponential majorant for the kernel mass. -/
theorem norm_gamma_le_mass_polynomial (t : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t)‖ ≤
      Real.sqrt (2 * Real.pi) * Real.exp (-|Real.pi * t| / 2) *
        Analysis.invSqrtOneAddPolynomial (Real.exp (-2 * |Real.pi * t|)) := by
  let z := Real.exp (-2 * |Real.pi * t|)
  have hz : z ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr ?_⟩
    exact mul_nonpos_of_nonpos_of_nonneg (by norm_num only) (abs_nonneg _)
  have hroot : 0 < Real.sqrt (1 + z) := Real.sqrt_pos.mpr (by linarith only [hz.1])
  have hp := Analysis.inv_sqrt_one_add_le_invSqrtOneAddPolynomial hz
  have hP : 0 ≤ Analysis.invSqrtOneAddPolynomial z :=
    (div_nonneg (by norm_num only) hroot.le).trans hp
  have hr := (div_le_iff₀ hroot).mp hp
  have hsq := mul_self_le_mul_self (by norm_num only : (0 : ℝ) ≤ 1) hr
  have hPs : 1 ≤ (1 + z) * Analysis.invSqrtOneAddPolynomial z ^ 2 := by
    have he :
      (Analysis.invSqrtOneAddPolynomial z * Real.sqrt (1 + z)) *
          (Analysis.invSqrtOneAddPolynomial z * Real.sqrt (1 + z)) =
        (1 + z) * Analysis.invSqrtOneAddPolynomial z ^ 2 := by
      rw [← pow_two, mul_pow, Real.sq_sqrt (by linarith only [hz.1] : 0 ≤ 1 + z)]
      ring
    rw [he] at hsq
    simpa only [one_mul] using hsq
  have hnorm :
    ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t)‖ ^ 2 * Real.cosh (Real.pi * t) = Real.pi := by
    rw [Analysis.norm_Gamma_half_add_I_sq, div_mul_cancel₀ _ (Real.cosh_pos _).ne']
  have hc := Analysis.cosh_mul_twice_exp_neg (Real.pi * t)
  have hn :
    ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t)‖ ^ 2 * (1 + z) =
      2 * Real.pi * Real.exp (-|Real.pi * t|) := by
    change _ * (1 + Real.exp (-2 * |Real.pi * t|)) = _
    rw [← hc]
    calc
      _ =
          (‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t)‖ ^ 2 * Real.cosh (Real.pi * t)) *
            (2 * Real.exp (-|Real.pi * t|)) :=
        by ring
      _ = _ := by
        rw [hnorm]; ring
  have hb :
    ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t)‖ ^ 2 ≤
      2 * Real.pi * Real.exp (-|Real.pi * t|) * Analysis.invSqrtOneAddPolynomial z ^ 2 := by
    apply (mul_le_mul_iff_of_pos_right (by linarith only [hz.1] : 0 < 1 + z)).mp
    rw [hn]
    have hp0 : 0 ≤ 2 * Real.pi * Real.exp (-|Real.pi * t|) :=
      mul_nonneg (mul_nonneg (by norm_num only) Real.pi_pos.le) (Real.exp_pos _).le
    have hm := mul_le_mul_of_nonneg_left hPs hp0
    nlinarith only [hm]
  have he : Real.exp (-|Real.pi * t| / 2) ^ 2 = Real.exp (-|Real.pi * t|) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hD :
    (Real.sqrt (2 * Real.pi) * Real.exp (-|Real.pi * t| / 2) * Analysis.invSqrtOneAddPolynomial z) ^
        2 =
      2 * Real.pi * Real.exp (-|Real.pi * t|) * Analysis.invSqrtOneAddPolynomial z ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg (by norm_num only) Real.pi_pos.le), he]
  have hDp :
    0 ≤
      Real.sqrt (2 * Real.pi) * Real.exp (-|Real.pi * t| / 2) *
        Analysis.invSqrtOneAddPolynomial z :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le) hP
  change
    _ ≤ Real.sqrt (2 * Real.pi) * Real.exp (-|Real.pi * t| / 2) * Analysis.invSqrtOneAddPolynomial z
  nlinarith only [hb, hD, hDp, norm_nonneg (Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t))]

/-- The integrable polynomial majorant of the gamma norm on the half line.
Substitute an exponential into the certified inverse-square-root polynomial.
Its finite exponential expansion gives an exact mass upper bound. -/
noncomputable def gammaMassMajorant (t : ℝ) : ℝ :=
  Real.sqrt (2 * Real.pi) * Real.exp (-|Real.pi * t| / 2) *
    Analysis.invSqrtOneAddPolynomial (Real.exp (-2 * |Real.pi * t|))

/-- Each polynomial monomial becomes one decaying exponential.
Use exponential multiplication and positive pi to combine the rates.
This permits termwise integration of the majorant. -/
theorem exponential_mass_monomial (i : ℕ) (t : ℝ) :
    Real.exp (-|Real.pi * t| / 2) * Real.exp (-2 * |Real.pi * t|) ^ i =
      Real.exp (-(Real.pi * (1 / 2 + 2 * i)) * |t|) := by
  rw [← Real.exp_nat_mul, ← Real.exp_add, abs_mul, abs_of_pos Real.pi_pos]
  congr 1
  ring

/-- The gamma mass majorant is a finite linear combination of decaying
exponentials. Expand the certified polynomial and combine exponential powers.
This supplies the finite sum interface for integration. -/
theorem gammaMassMajorant_eq_sum (t : ℝ) :
    gammaMassMajorant t =
      Real.sqrt (2 * Real.pi) *
        ∑ i ∈ Finset.range 11,
          (Analysis.invSqrtOneAddMonomialCoefficients.getD i 0 : ℝ) *
            Real.exp (-(Real.pi * (1 / 2 + 2 * i)) * |t|) := by
  unfold gammaMassMajorant
  rw [Analysis.invSqrtOneAddPolynomial_eq_sum, mul_assoc, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← exponential_mass_monomial i t]
  ring

/-- Every exponential term has positive decay rate, since pi is positive
and its natural index is nonnegative. This establishes absolute integrability. -/
theorem gamma_mass_rate_pos (i : ℕ) : 0 < Real.pi * (1 / 2 + 2 * i) := by
  apply mul_pos Real.pi_pos
  have hn : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  linarith only [hn]

/-- The polynomial gamma majorant is integrable on the real line.
Every exponential term is integrable at its positive decay rate.
The finite sum and constant factor preserve integrability. -/
theorem integrable_gammaMassMajorant : MeasureTheory.Integrable gammaMassMajorant := by
  have hi :
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        ∑ i ∈ Finset.range 11,
          (Analysis.invSqrtOneAddMonomialCoefficients.getD i 0 : ℝ) *
            Real.exp (-(Real.pi * (1 / 2 + 2 * i)) * |t|)) := by
    apply MeasureTheory.integrable_finsetSum
    intro i _
    exact (Analysis.integrable_exp_neg_mul_abs (gamma_mass_rate_pos i)).const_mul _
  apply (hi.const_mul (Real.sqrt (2 * Real.pi))).congr
  apply Filter.Eventually.of_forall
  intro t
  exact (gammaMassMajorant_eq_sum t).symm

/-- The polynomial majorant has the displayed exact integral.
Integrate each exponential using its positive rate, and verify the resulting
rational coefficient sum. This supplies the quantitative mass certificate. -/
theorem integral_gammaMassMajorant :
    (∫ t : ℝ, gammaMassMajorant t) =
      Real.sqrt (2 * Real.pi) * (2 / Real.pi) *
        (87200369111842041392983877 / 47030364339978240000000000 : ℝ) := by
  have he :=
    MeasureTheory.integral_congr_ae (μ := MeasureTheory.volume)
      (Filter.Eventually.of_forall gammaMassMajorant_eq_sum)
  rw [he, MeasureTheory.integral_const_mul, MeasureTheory.integral_finsetSum]
  · simp only [MeasureTheory.integral_const_mul,
      Analysis.integral_exp_neg_mul_abs (gamma_mass_rate_pos _)]
    simp only [div_mul_eq_div_mul_one_div]
    have hsum :
      (∑ i ∈ Finset.range 11,
          (Analysis.invSqrtOneAddMonomialCoefficients.getD i 0 : ℝ) *
            (2 / Real.pi * (1 / (1 / 2 + 2 * i)))) =
        (2 / Real.pi) *
          ∑ i ∈ Finset.range 11,
            (Analysis.invSqrtOneAddMonomialCoefficients.getD i 0 : ℝ) * (1 / (1 / 2 + 2 * i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hsum]
    have hs :
      (∑ i ∈ Finset.range 11,
          (Analysis.invSqrtOneAddMonomialCoefficients.getD i 0 : ℝ) * (1 / (1 / 2 + 2 * i))) =
        (87200369111842041392983877 / 47030364339978240000000000 : ℝ) := by
      norm_num only [Analysis.invSqrtOneAddMonomialCoefficients, Finset.sum_range_succ,
        Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    rw [hs]
    ring
  · intro i _
    exact (Analysis.integrable_exp_neg_mul_abs (gamma_mass_rate_pos i)).const_mul _

/-- The exact majorant integral divided by `2*pi` is at most `471/1000`.
The rational lower bound for pi certifies the squared comparison.
Positive square roots and denominators recover the unsquared inequality. -/
theorem gamma_mass_integral_certificate :
    Real.sqrt (2 * Real.pi) * (2 / Real.pi) *
          (87200369111842041392983877 / 47030364339978240000000000 : ℝ) /
        (2 * Real.pi) ≤
      471 / 1000 := by
  have he :
    Real.sqrt (2 * Real.pi) * (2 / Real.pi) *
          (87200369111842041392983877 / 47030364339978240000000000 : ℝ) /
        (2 * Real.pi) =
      (Real.sqrt (2 * Real.pi) * (87200369111842041392983877 / 47030364339978240000000000 : ℝ)) /
        Real.pi ^ 2 := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [he]
  apply (div_le_iff₀ (sq_pos_of_pos Real.pi_pos)).mpr
  have hpi : (31415 / 10000 : ℝ) ≤ Real.pi := by
    calc
      _ = (3.1415 : ℝ) := by norm_num only
      _ ≤ _ := Real.pi_gt_d4.le
  have hc := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 31415 / 10000) hpi 3
  have hn :
    2 * (87200369111842041392983877 / 47030364339978240000000000 : ℝ) ^ 2 ≤
      (471 / 1000) ^ 2 * (31415 / 10000 : ℝ) ^ 3 := by
    norm_num only
  have hm := mul_le_mul_of_nonneg_left hc (sq_nonneg (471 / 1000 : ℝ))
  have hbound := mul_le_mul_of_nonneg_left (hn.trans hm) Real.pi_pos.le
  have hs :
    (Real.sqrt (2 * Real.pi) * (87200369111842041392983877 / 47030364339978240000000000 : ℝ)) ^ 2 =
      Real.pi * (2 * (87200369111842041392983877 / 47030364339978240000000000 : ℝ) ^ 2) := by
    rw [mul_pow, Real.sq_sqrt (mul_nonneg (by norm_num only) Real.pi_pos.le)]
    ring
  have hr : 0 ≤ (471 / 1000 : ℝ) * Real.pi ^ 2 := mul_nonneg (by norm_num only) (sq_nonneg _)
  nlinarith only [hbound, hs, hr]

/-- The Section 6.3 gamma kernel has mass at most `471/1000`.
Compare its integrable norm with the certified polynomial majorant, evaluate
that integral exactly, and apply the rational pi certificate.
This discharges the numerical mass input for the small-index prime bounds. -/
theorem gammaMellinKernel_mass_le : gammaMellinKernel.mass ≤ 471 / 1000 := by
  have hi :=
    MeasureTheory.integral_mono Analysis.integrable_Gamma_half_add_I.norm
      integrable_gammaMassMajorant norm_gamma_le_mass_polynomial
  have hm :
    gammaMellinKernel.mass =
      (∫ t : ℝ, ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t)‖) / (2 * Real.pi) := by
    unfold MellinKernel.mass
    change (∫ t : ℝ, ‖Complex.Gamma (Complex.I * t + 1 / 2)‖) / (2 * Real.pi) = _
    congr 1
    apply MeasureTheory.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro t
    dsimp only
    rw [add_comm]
  calc
    _ = _ := hm
    _ ≤ (∫ t : ℝ, gammaMassMajorant t) / (2 * Real.pi) :=
      div_le_div_of_nonneg_right hi (mul_nonneg (by norm_num only) Real.pi_pos.le)
    _ ≤ _ := by
      rw [integral_gammaMassMajorant]; exact gamma_mass_integral_certificate

end PseudoPrime.LLS.PaperStatements
