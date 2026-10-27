/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaResolventDifferenceBounds

/-! # Signed scalar Gamma archimedean series bounds -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For a positive real base, the real digamma recurrence increments its value
by the reciprocal of the base. Positivity excludes all Gamma poles.
This identity cancels the initial reciprocal against the signed baseline. -/
theorem re_digamma_real_add_one {b : ℝ} (hb : 0 < b) :
    (Complex.digamma ((b + 1 : ℝ) : ℂ)).re = (Complex.digamma (b : ℂ)).re + 1 / b := by
  have h :=
    Complex.digamma_apply_add_one (b : ℂ)
      (AnalyticNumberTheory.Gamma.not_neg_nat_of_re_pos
        (by simpa only [Complex.ofReal_re] using hb))
  have hr := congrArg Complex.re h
  simpa only [Complex.ofReal_add, Complex.ofReal_one, Complex.add_re, ← Complex.ofReal_inv,
    Complex.ofReal_re, one_div] using hr

/-- For positive base and scale, combine the signed digamma baseline with
the entire scalar resolvent series. The recurrence cancels the initial
reciprocal, while the nonnegative initial scalar integral remains subtracted.
This gives the full scalar archimedean upper bound before parity specialization. -/
theorem gamma_scalar_archimedean_series_le {b x : ℝ} (hb : 0 < b) (hx : 0 < x) :
    ((-Real.log Real.pi + (Complex.digamma (b : ℂ)).re) / 2) * (Real.sqrt x⁻¹ * Real.exp (-x⁻¹)) +
        (1 / 2 : ℝ) *
          (∑' n : ℕ,
            (Real.sqrt x⁻¹ * Real.exp (-x⁻¹) / (b + n) -
              ∫ r : ℝ in Set.Ioi 0, gammaResolventScalarDensity (b + n) x r)) ≤
      (Real.sqrt x⁻¹ * Real.exp (-x⁻¹)) *
          ((-Real.log Real.pi + (Complex.digamma ((b + 3 / 4 : ℝ) : ℂ)).re) / 2 +
            (x⁻¹ / 2) *
              (Complex.digamma ((b + 3 / 4 : ℝ) : ℂ) - Complex.digamma ((b + 1 / 4 : ℝ) : ℂ)).re) -
        (1 / 2 : ℝ) * (∫ r : ℝ in Set.Ioi 0, gammaResolventScalarDensity b x r) := by
  have hs := summable_gammaCentralScalarDifference hb hx
  have hsplit :
    (∑' n : ℕ,
        (Real.sqrt x⁻¹ * Real.exp (-x⁻¹) / (b + n) -
          ∫ r : ℝ in Set.Ioi 0, gammaResolventScalarDensity (b + n) x r)) =
      Real.sqrt x⁻¹ * Real.exp (-x⁻¹) / b -
          (∫ r : ℝ in Set.Ioi 0, gammaResolventScalarDensity b x r) +
        (∑' n : ℕ,
          (Real.sqrt x⁻¹ * Real.exp (-x⁻¹) / (b + 1 + n) -
            ∫ r : ℝ in Set.Ioi 0, gammaResolventScalarDensity (b + 1 + n) x r)) := by
    rw [hs.tsum_eq_zero_add]
    simp only [Nat.cast_zero, add_zero]
    congr 1
    apply tsum_congr
    intro n
    simp only [Nat.cast_add, Nat.cast_one]
    rw [← add_assoc, add_right_comm b (n : ℝ) 1]
  rw [hsplit]
  have ht := tsum_gammaCentralScalarDifference_tail_le hb hx
  rw [Complex.sub_re, Complex.sub_re, re_digamma_real_add_one hb] at ht
  norm_num only [Complex.sub_re, div_eq_mul_inv, one_mul] at ht ⊢
  nlinarith only [ht]

end PseudoPrime.LLS.PaperStatements
