/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.PaperProofs
public import PseudoPrime.LLS.Extensions.UniformReciprocalBounds

/-!
# Truncated value formula from logarithmic and reciprocal identities

The weighted arithmetic sums combine into the truncated Euler-value sum.
Cancel the gamma endpoint between the two explicit formulas and bound the remaining
zero and gamma errors explicitly, for every cutoff at least two.
-/

@[expose] public section

namespace PseudoPrime.LLS.Extensions.GeneralLFunction

/-- For any general L-function data and cutoff greater than one, the logarithmic sum
plus the smoothed reciprocal sum divided by log cutoff is the truncated value sum.
Combine the weights termwise, treating the index one separately since its Mangoldt value
is zero. This is the arithmetic identity used when the two explicit formulas are combined. -/
theorem logValueSum_add_reciprocalWeightedSum_div_log (f : GeneralLFunction) {x : ℝ} (hx : 1 < x) :
    f.logValueSum x + f.reciprocalWeightedSum x / (Real.log x : ℂ) = f.truncatedValueSum x := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hlx : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  unfold logValueSum reciprocalWeightedSum truncatedValueSum
  rw [Finset.sum_div, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hn1 : n = 1
  · subst n
    simp only [ArithmeticFunction.vonMangoldt_apply_one, zero_div, zero_mul, Complex.ofReal_zero,
      mul_zero, add_zero]
  · have hn0 : 0 < (n : ℝ) := Nat.cast_pos.mpr (Finset.mem_Ioc.mp hn).1
    have hn2 : 1 < (n : ℝ) := by
      exact_mod_cast (lt_of_le_of_ne (Finset.mem_Ioc.mp hn).1 (Ne.symm hn1))
    have hln : Real.log (n : ℝ) ≠ 0 := (Real.log_pos hn2).ne'
    rw [mul_div_assoc, ← Complex.ofReal_div, ← mul_add, ← Complex.ofReal_add]
    congr 1
    rw [Real.log_div hx0.ne' hn0.ne']
    congr 1
    field_simp (disch := simp only [hx0.ne', hn0.ne', hlx, hln, ne_eq, not_false_eq_true])
    ring

/-- For admissible RH data and cutoff at least two, express log of the L-value norm
as the real truncated value sum, three bounded real error coefficients, and the reciprocal
remainder divided by log cutoff. Combine the logarithmic and reciprocal formulas and
cancel their gamma endpoints using the ordinary endpoint identity.
This is the exact starting formula for uniform truncated L-value bounds. -/
theorem log_norm_L_one_eq_truncatedValueSum_errors (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) {x : ℝ} (hx : 2 ≤ x) :
    ∃ θ₁ θ₂ θ₃ : ℝ,
      |θ₁| ≤ 1 ∧
        |θ₂| ≤ 1 ∧
        |θ₃| ≤ 1 ∧
        Real.log ‖f.L 1‖ =
          (f.truncatedValueSum x).re + (θ₃ / Real.sqrt x - 1 / (2 * x)) * f.zeroMass / Real.log x -
              θ₁ * f.zeroMass / (Real.sqrt x * (Real.log x) ^ 2) +
            2 * (f.degree : ℝ) * θ₂ / (x * (Real.log x) ^ 2) +
            f.reciprocalRemainder x / Real.log x := by
  have hx1 : 1 < x := lt_of_lt_of_le (show (1 : ℝ) < 2 by norm_num only) hx
  obtain ⟨θ₁, θ₂, hθ₁, hθ₂, h1⟩ := (lls_propL1_general_proof f hf hRH).2 x hx
  obtain ⟨θ₃, hθ₃, h2⟩ := reciprocalFormula_eq_theta f hf hRH hx1
  refine ⟨θ₁, θ₂, θ₃, hθ₁, hθ₂, hθ₃, ?_⟩
  have hsum := congrArg Complex.re (logValueSum_add_reciprocalWeightedSum_div_log f hx1)
  simp only [Complex.add_re, Complex.div_ofReal_re] at hsum
  rw [re_logDeriv_ordinary_one_eq_half_zeroMass_sub_gamma f hf hRH] at h2
  rw [← hsum]
  linear_combination h1 + h2 / Real.log x

/-- For admissible RH data and cutoff at least two, a real coefficient of absolute value
at most one represents the leading mass term in the truncated L-value formula.
The remaining error is bounded explicitly by mass, degree and reciprocal remainder terms.
Take absolute values of each correction in the exact formula.
This separates the leading zero contribution from the smaller errors in value estimates. -/
theorem exists_truncatedValue_error_le (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) {x : ℝ} (hx : 2 ≤ x) :
    ∃ θ : ℝ,
      |θ| ≤ 1 ∧
        |Real.log ‖f.L 1‖ - (f.truncatedValueSum x).re -
              θ * f.zeroMass / (Real.sqrt x * Real.log x)| ≤
          f.zeroMass / (2 * x * Real.log x) + f.zeroMass / (Real.sqrt x * (Real.log x) ^ 2) +
            2 * (f.degree : ℝ) / (x * (Real.log x) ^ 2) +
            ‖f.reciprocalRemainder x‖ / Real.log x := by
  have hx1 : 1 < x := lt_of_lt_of_le (show (1 : ℝ) < 2 by norm_num only) hx
  have hx0 : 0 < x := zero_lt_one.trans hx1
  have hl : 0 < Real.log x := Real.log_pos hx1
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hM : 0 ≤ f.zeroMass := tsum_nonneg (fun ρ ↦ div_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  obtain ⟨θ₁, θ₂, θ₃, hθ₁, hθ₂, hθ₃, he⟩ := log_norm_L_one_eq_truncatedValueSum_errors f hf hRH hx
  refine ⟨θ₃, hθ₃, ?_⟩
  have h1 :
    |θ₁ * f.zeroMass / (Real.sqrt x * (Real.log x) ^ 2)| ≤
      f.zeroMass / (Real.sqrt x * (Real.log x) ^ 2) := by
    rw [abs_div, abs_mul, abs_of_nonneg hM, abs_of_pos (mul_pos hs (sq_pos_of_pos hl))]
    exact div_le_div_of_nonneg_right (mul_le_of_le_one_left hM hθ₁) (mul_nonneg hs.le (sq_nonneg _))
  have h2 :
    |2 * (f.degree : ℝ) * θ₂ / (x * (Real.log x) ^ 2)| ≤
      2 * (f.degree : ℝ) / (x * (Real.log x) ^ 2) := by
    rw [abs_div, abs_mul, abs_of_nonneg (mul_nonneg (by norm_num only) (Nat.cast_nonneg _)),
      abs_of_pos (mul_pos hx0 (sq_pos_of_pos hl))]
    exact
      div_le_div_of_nonneg_right
        (mul_le_of_le_one_right (mul_nonneg (by norm_num only) (Nat.cast_nonneg _)) hθ₂)
        (mul_nonneg hx0.le (sq_nonneg _))
  have h3 : |f.reciprocalRemainder x / Real.log x| = ‖f.reciprocalRemainder x‖ / Real.log x := by
    rw [abs_div, abs_of_pos hl, Real.norm_eq_abs]
  have h4 : |f.zeroMass / (2 * x * Real.log x)| = f.zeroMass / (2 * x * Real.log x) := by
    rw [abs_div, abs_of_nonneg hM, abs_of_pos (mul_pos (mul_pos (by norm_num only) hx0) hl)]
  have hid :
    Real.log ‖f.L 1‖ - (f.truncatedValueSum x).re - θ₃ * f.zeroMass / (Real.sqrt x * Real.log x) =
      -f.zeroMass / (2 * x * Real.log x) - θ₁ * f.zeroMass / (Real.sqrt x * (Real.log x) ^ 2) +
        2 * (f.degree : ℝ) * θ₂ / (x * (Real.log x) ^ 2) +
        f.reciprocalRemainder x / Real.log x := by
    rw [he]
    ring
  rw [hid, neg_div]
  apply abs_le.mpr
  constructor <;>
    linarith only [(abs_le.mp h1).1, (abs_le.mp h1).2, (abs_le.mp h2).1, (abs_le.mp h2).2,
      le_abs_self (f.reciprocalRemainder x / Real.log x),
      neg_le_abs (f.reciprocalRemainder x / Real.log x), h3, h4,
      le_abs_self (f.zeroMass / (2 * x * Real.log x)),
      neg_le_abs (f.zeroMass / (2 * x * Real.log x))]

/-- For admissible data and any cutoff, the absolute difference between zero mass and
log analytic conductor is at most twice the degree-weighted reciprocal Mangoldt sum plus
the zero-mass remainder norm. Rearrange the definition of that remainder and take absolute
values. This controls replacing the leading mass term by the logarithmic conductor. -/
theorem abs_zeroMass_sub_log_conductor_le_arithmetic (f : GeneralLFunction) (hf : f.IsAdmissible)
    (x : ℝ) :
    |f.zeroMass - Real.log f.analyticConductor| ≤
      2 * ((f.degree : ℝ) * AnalyticNumberTheory.Arithmetic.reciprocalMangoldtSum x) +
        ‖f.zeroMassReciprocalRemainder x‖ := by
  have hs :=
    (Complex.abs_re_le_norm (f.reciprocalSum x)).trans
      (norm_reciprocalSum_le_degree_majorant f hf x)
  have hr := (le_abs_self (f.zeroMassReciprocalRemainder x))
  have hnr := (neg_le_abs (f.zeroMassReciprocalRemainder x))
  rw [← Real.norm_eq_abs] at hr hnr
  unfold zeroMassReciprocalRemainder at hr hnr ⊢
  apply abs_le.mpr
  constructor <;> linarith only [(abs_le.mp hs).1, (abs_le.mp hs).2, hr, hnr]

/-- For admissible RH data and cutoff at least two, a bounded real coefficient represents
the leading logarithmic conductor term in the truncated value formula. Its remaining error
is bounded by the earlier mass error plus the reciprocal arithmetic majorant and zero-mass
remainder, divided by sqrt(cutoff) times log(cutoff).
Use the mass-conductor difference estimate. This is the conductor-centered L-value formula. -/
theorem exists_truncatedValue_conductor_error_le (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) {x : ℝ} (hx : 2 ≤ x) :
    ∃ θ : ℝ,
      |θ| ≤ 1 ∧
        |Real.log ‖f.L 1‖ - (f.truncatedValueSum x).re -
              θ * Real.log f.analyticConductor / (Real.sqrt x * Real.log x)| ≤
          f.zeroMass / (2 * x * Real.log x) + f.zeroMass / (Real.sqrt x * (Real.log x) ^ 2) +
            2 * (f.degree : ℝ) / (x * (Real.log x) ^ 2) +
            ‖f.reciprocalRemainder x‖ / Real.log x +
            (2 * ((f.degree : ℝ) * AnalyticNumberTheory.Arithmetic.reciprocalMangoldtSum x) +
                ‖f.zeroMassReciprocalRemainder x‖) /
              (Real.sqrt x * Real.log x) := by
  have hx1 : 1 < x := lt_of_lt_of_le (show (1 : ℝ) < 2 by norm_num only) hx
  have hd : 0 < Real.sqrt x * Real.log x :=
    mul_pos (Real.sqrt_pos.mpr (zero_lt_one.trans hx1)) (Real.log_pos hx1)
  obtain ⟨θ, hθ, he⟩ := exists_truncatedValue_error_le f hf hRH hx
  refine ⟨θ, hθ, ?_⟩
  have hchange :
    |θ * (f.zeroMass - Real.log f.analyticConductor) / (Real.sqrt x * Real.log x)| ≤
      (2 * ((f.degree : ℝ) * AnalyticNumberTheory.Arithmetic.reciprocalMangoldtSum x) +
          ‖f.zeroMassReciprocalRemainder x‖) /
        (Real.sqrt x * Real.log x) := by
    rw [abs_div, abs_mul, abs_of_pos hd]
    exact
      div_le_div_of_nonneg_right
        ((mul_le_of_le_one_left (abs_nonneg _) hθ).trans
          (abs_zeroMass_sub_log_conductor_le_arithmetic f hf x))
        hd.le
  have hid :
    Real.log ‖f.L 1‖ - (f.truncatedValueSum x).re -
        θ * Real.log f.analyticConductor / (Real.sqrt x * Real.log x) =
      (Real.log ‖f.L 1‖ - (f.truncatedValueSum x).re -
          θ * f.zeroMass / (Real.sqrt x * Real.log x)) +
        θ * (f.zeroMass - Real.log f.analyticConductor) / (Real.sqrt x * Real.log x) := by
    ring
  rw [hid]
  exact (abs_add_le _ _).trans (add_le_add he hchange)

end PseudoPrime.LLS.Extensions.GeneralLFunction
