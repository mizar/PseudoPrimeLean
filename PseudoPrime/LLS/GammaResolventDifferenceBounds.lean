/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaParityResolventSums

/-! # Actual Gamma-weighted reciprocal differences and their one-sided bounds -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Positive decay and scale make the actual Gamma reciprocal weight integrable.
Subtract the already integrable reciprocal difference from the constant multiple
of the kernel. This permits separating the two integrals within a single term. -/
theorem integrable_gammaCentralReciprocalWeight {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    MeasureTheory.Integrable
      (fun t : ℝ ↦ (1 / ((c : ℂ) + Complex.I * (t : ℂ) / 2)) * gammaCentralMellinWeight x t) := by
  have hD :=
    integrable_weighted_vertical_resolvent hc (gammaCentralMellinWeight x)
      (continuous_gammaCentralMellinWeight hx).aestronglyMeasurable
      (integrable_abs_mul_norm_gammaCentralMellinWeight hx)
  have hW := (integrable_gammaCentralMellinWeight hx).const_mul (1 / (c : ℂ))
  exact
    (hW.sub hD).congr
      (MeasureTheory.ae_of_all _
        (fun t ↦ by
          simp only [Pi.sub_apply]
          ring))

/-- At positive decay and scale, one normalized reciprocal-difference term is
exactly the baseline density divided by c minus the real scalar resolvent.
Linearity is used only after both integrands are proved integrable.
This exposes the real signed term needed for summing the archimedean series. -/
theorem gamma_central_resolvent_difference_integral_eq_real {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          (1 / (c : ℂ) - 1 / ((c : ℂ) + Complex.I * (t : ℂ) / 2)) * gammaCentralMellinWeight x t) =
      ((Real.sqrt x⁻¹ * Real.exp (-x⁻¹) / c -
            (∫ r : ℝ in Set.Ioi 0, gammaResolventScalarDensity c x r) :
          ℝ) :
        ℂ) := by
  have hE (t : ℝ) :
    (1 / (c : ℂ) - 1 / ((c : ℂ) + Complex.I * (t : ℂ) / 2)) * gammaCentralMellinWeight x t =
      (1 / (c : ℂ)) * gammaCentralMellinWeight x t -
        (1 / ((c : ℂ) + Complex.I * (t : ℂ) / 2)) * gammaCentralMellinWeight x t := by
    ring
  rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ hE),
    MeasureTheory.integral_sub ((integrable_gammaCentralMellinWeight hx).const_mul _)
      (integrable_gammaCentralReciprocalWeight hc hx),
    MeasureTheory.integral_const_mul, mul_sub, mul_left_comm _ (1 / (c : ℂ)) _,
    gamma_central_kernel_integral_eq_density hx, gamma_central_resolvent_integral_eq_real hc hx]
  simp only [Complex.ofReal_sub, div_eq_mul_inv, Complex.ofReal_mul, Complex.ofReal_inv, mul_one,
    mul_comm]

/-- For c greater than 3/4 and positive scale, the real part of the actual
normalized reciprocal-difference integral is bounded above by a reciprocal
difference plus the certified rational error. This is the termwise inequality
needed to retain cancellation while summing the archimedean tail. -/
theorem gamma_central_resolvent_difference_re_le {c x : ℝ} (hc : 3 / 4 < c) (hx : 0 < x) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            (1 / (c : ℂ) - 1 / ((c : ℂ) + Complex.I * (t : ℂ) / 2)) *
              gammaCentralMellinWeight x t)).re ≤
      (Real.sqrt x⁻¹ * Real.exp (-x⁻¹)) *
        (1 / c - ((1 + x⁻¹) / (c - 1 / 4) - x⁻¹ / (c - 3 / 4))) := by
  have hc0 : 0 < c := by linarith only [hc]
  rw [gamma_central_resolvent_difference_integral_eq_real hc0 hx, Complex.ofReal_re]
  have h := integral_gammaResolventScalarDensity_ge_rational hc hx
  simp only [div_eq_mul_inv, one_mul] at h ⊢
  nlinarith only [h]

/-- At positive base and scale, the scalar reciprocal-difference integrals
form a summable real series. Summable integrated norms dominate the actual
complex integrals, and the exact scalar identity transfers their summability.
This supplies the convergence premise for the infinite tail comparison. -/
theorem summable_gammaCentralScalarDifference {b x : ℝ} (hb : 0 < b) (hx : 0 < x) :
    Summable
      (fun n : ℕ ↦
        Real.sqrt x⁻¹ * Real.exp (-x⁻¹) / (b + n) -
          ∫ r : ℝ in Set.Ioi 0, gammaResolventScalarDensity (b + n) x r) := by
  have hs :=
    summable_weighted_vertical_resolvent_integral_norm hb (gammaCentralMellinWeight x)
      (continuous_gammaCentralMellinWeight hx).aestronglyMeasurable
      (integrable_abs_mul_norm_gammaCentralMellinWeight hx)
  have hi :
    Summable
      (fun n : ℕ ↦
        ∫ t : ℝ,
          (1 / ((b + n : ℝ) : ℂ) - 1 / (((b + n : ℝ) : ℂ) + Complex.I * (t / 2))) *
            gammaCentralMellinWeight x t) :=
    hs.of_norm_bounded (fun n ↦ MeasureTheory.norm_integral_le_integral_norm _)
  have hC := hi.mul_left (((1 / (2 * Real.pi) : ℝ) : ℂ))
  apply Complex.summable_ofReal.mp
  exact
    hC.congr
      (fun n ↦ by
        simpa only [mul_div_assoc] using
          gamma_central_resolvent_difference_integral_eq_real
            (add_pos_of_pos_of_nonneg hb (Nat.cast_nonneg n)) hx)

/-- For positive base and scale, the tail after the initial resolvent term
is bounded by two convergent digamma differences. Compare the summable scalar
series term by term and then evaluate only the reciprocal differences.
This connects the actual Gamma integrals to the parity-tail constants. -/
theorem tsum_gammaCentralScalarDifference_tail_le {b x : ℝ} (hb : 0 < b) (hx : 0 < x) :
    (∑' n : ℕ,
        (Real.sqrt x⁻¹ * Real.exp (-x⁻¹) / (b + 1 + n) -
          ∫ r : ℝ in Set.Ioi 0, gammaResolventScalarDensity (b + 1 + n) x r)) ≤
      (Real.sqrt x⁻¹ * Real.exp (-x⁻¹)) *
        ((Complex.digamma ((b + 3 / 4 : ℝ) : ℂ) - Complex.digamma ((b + 1 : ℝ) : ℂ)).re +
          x⁻¹ *
            (Complex.digamma ((b + 3 / 4 : ℝ) : ℂ) -
                Complex.digamma ((b + 1 / 4 : ℝ) : ℂ)).re) := by
  have ha : 0 < b + 3 / 4 := by linarith only [hb]
  have hd : 0 < b + 1 / 4 := by linarith only [hb]
  have h1 : 0 < b + 1 := by linarith only [hb]
  let K := Real.sqrt x⁻¹ * Real.exp (-x⁻¹)
  let U := fun n : ℕ ↦
    K *
      ((1 / (b + 1 + n) - 1 / (b + 3 / 4 + n)) + x⁻¹ * (1 / (b + 1 / 4 + n) - 1 / (b + 3 / 4 + n)))
  have hsU : Summable U :=
    ((summable_real_reciprocal_difference ha h1).add
          ((summable_real_reciprocal_difference ha hd).mul_left x⁻¹)).mul_left
      K
  have hterm (n : ℕ) :
    K / (b + 1 + n) - (∫ r : ℝ in Set.Ioi 0, gammaResolventScalarDensity (b + 1 + n) x r) ≤
      U n := by
    have hc : (3 / 4 : ℝ) < b + 1 + n := by
      linarith only [hb, (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
    have h := integral_gammaResolventScalarDensity_ge_rational hc hx
    have he1 : b + 1 + (n : ℝ) - 1 / 4 = b + 3 / 4 + n := by ring
    have he2 : b + 1 + (n : ℝ) - 3 / 4 = b + 1 / 4 + n := by ring
    rw [he1, he2] at h
    dsimp only [K, U]
    simp only [div_eq_mul_inv, one_mul] at h ⊢
    nlinarith only [h]
  have hi := (summable_gammaCentralScalarDifference h1 hx).tsum_le_tsum hterm hsU
  have hv :
    (∑' n : ℕ, U n) =
      K *
        ((Complex.digamma ((b + 3 / 4 : ℝ) : ℂ) - Complex.digamma ((b + 1 : ℝ) : ℂ)).re +
          x⁻¹ *
            (Complex.digamma ((b + 3 / 4 : ℝ) : ℂ) -
                Complex.digamma ((b + 1 / 4 : ℝ) : ℂ)).re) := by
    dsimp only [U]
    rw [tsum_mul_left,
      (summable_real_reciprocal_difference ha h1).tsum_add
        ((summable_real_reciprocal_difference ha hd).mul_left x⁻¹),
      tsum_mul_left, tsum_real_reciprocal_difference ha h1, tsum_real_reciprocal_difference ha hd]
  rw [hv] at hi
  exact hi

end PseudoPrime.LLS.PaperStatements
