/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaScalarArchimedeanBounds
public import PseudoPrime.LLS.GammaCentralArchimedeanSeries

/-! # Exact real scalar series for the actual central Gamma integral -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Every character admits a positive Gamma base such that its actual
normalized archimedean integral has the signed real scalar series representation.
The proof substitutes the certified reciprocal inversions into the absolutely
convergent series before taking real parts. This connects the actual integral
to the scalar upper bound without adding an inversion hypothesis. -/
theorem gamma_central_archimedean_integral_re_eq_scalar_series {q : ℕ}
    (χ : DirichletCharacter ℂ q) :
    ∃ b : ℝ,
      1 / 4 ≤ b ∧
        b ≤ 1 ∧
        ∀ x : ℝ,
          0 < x →
            (((1 / (2 * Real.pi) : ℝ) : ℂ) *
                  (∫ t : ℝ,
                    logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
                      gammaCentralMellinWeight x t)).re =
              ((-Real.log Real.pi + (Complex.digamma (b : ℂ)).re) / 2) *
                  (Real.sqrt x⁻¹ * Real.exp (-x⁻¹)) +
                (1 / 2 : ℝ) *
                  (∑' n : ℕ,
                    (Real.sqrt x⁻¹ * Real.exp (-x⁻¹) / (b + n) -
                      ∫ r : ℝ in Set.Ioi 0, gammaResolventScalarDensity (b + n) x r)) := by
  obtain ⟨b, hb, hb1, h⟩ := gamma_central_archimedean_integral_eq_density_series χ
  refine ⟨b, hb, hb1, ?_⟩
  intro x hx
  have hb0 : 0 < b := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1 / 4) hb
  let C : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  let K : ℝ := Real.sqrt x⁻¹ * Real.exp (-x⁻¹)
  let J := fun n : ℕ ↦
    ∫ t : ℝ,
      (1 / ((b + n : ℝ) : ℂ) - 1 / (((b + n : ℝ) : ℂ) + Complex.I * (t / 2))) *
        gammaCentralMellinWeight x t
  let F := fun n : ℕ ↦ K / (b + n) - ∫ r : ℝ in Set.Ioi 0, gammaResolventScalarDensity (b + n) x r
  have hJ : C * (∑' n : ℕ, J n) = ((∑' n : ℕ, F n) : ℝ) := by
    rw [← tsum_mul_left, Complex.ofReal_tsum]
    apply tsum_congr
    intro n
    simpa only [C, J, F, K, mul_div_assoc] using
      gamma_central_resolvent_difference_integral_eq_real
        (add_pos_of_pos_of_nonneg hb0 (Nat.cast_nonneg n)) hx
  have he := h x hx
  have he' :
    C * (∫ t : ℝ, logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) * gammaCentralMellinWeight x t) =
      ((-Complex.log Real.pi + Complex.digamma (b : ℂ)) / 2) * (K : ℂ) +
        (1 / 2 : ℂ) * (C * (∑' n : ℕ, J n)) := by
    rw [he]
    dsimp only [C, K, J]
    ring
  rw [he', hJ]
  norm_num only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero, Complex.div_ofNat_re, Complex.neg_re, ← Complex.ofReal_log Real.pi_pos.le,
    show (1 / 2 : ℂ).re = (1 / 2 : ℝ) from by norm_num only [Complex.div_ofNat_re, Complex.one_re],
    show (1 / 2 : ℂ).im = (0 : ℝ) from by norm_num only [Complex.div_ofNat_im, Complex.one_im],
    Complex.one_re, Complex.one_im]
  rfl

/-- The actual normalized central archimedean integral has the signed scalar
upper bound with the initial resolvent subtracted. The exact real series and
the proved full scalar inequality discharge all integrability and convergence
conditions, leaving only the explicit digamma coefficients for sign evaluation. -/
theorem gamma_central_archimedean_integral_re_le_scalar {q : ℕ} (χ : DirichletCharacter ℂ q) :
    ∃ b : ℝ,
      1 / 4 ≤ b ∧
        b ≤ 1 ∧
        ∀ x : ℝ,
          0 < x →
            (((1 / (2 * Real.pi) : ℝ) : ℂ) *
                  (∫ t : ℝ,
                    logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
                      gammaCentralMellinWeight x t)).re ≤
              (Real.sqrt x⁻¹ * Real.exp (-x⁻¹)) *
                  ((-Real.log Real.pi + (Complex.digamma ((b + 3 / 4 : ℝ) : ℂ)).re) / 2 +
                    (x⁻¹ / 2) *
                      (Complex.digamma ((b + 3 / 4 : ℝ) : ℂ) -
                          Complex.digamma ((b + 1 / 4 : ℝ) : ℂ)).re) -
                (1 / 2 : ℝ) * (∫ r : ℝ in Set.Ioi 0, gammaResolventScalarDensity b x r) := by
  obtain ⟨b, hb, hb1, h⟩ := gamma_central_archimedean_integral_re_eq_scalar_series χ
  refine ⟨b, hb, hb1, ?_⟩
  intro x hx
  rw [h x hx]
  exact
    gamma_scalar_archimedean_series_le (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1 / 4) hb) hx

end PseudoPrime.LLS.PaperStatements
