/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RectangleGeometry.Boundary
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Vertical-line limits of rectangle boundary integrals
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RectangleGeometry

/-- For a kernel integrable on both vertical lines and horizontal integrals tending to zero,
rectangles with heights tending to infinity converge to I times the difference of the
whole-line right and left integrals. Expand the oriented edges and exhaust the real lines.
This assembles shifted contours without assuming any residue formula. -/
theorem tendsto_rectangleBoundaryIntegral_of_horizontal_limits {K : ℂ → ℂ} {a b : ℝ} (T : ℕ → ℝ)
    (hT : Filter.Tendsto T Filter.atTop Filter.atTop)
    (hbottom :
      Filter.Tendsto (fun k ↦ ∫ u in a..b, K ((u : ℂ) - T k * Complex.I)) Filter.atTop (nhds 0))
    (htop :
      Filter.Tendsto (fun k ↦ ∫ u in a..b, K ((u : ℂ) + T k * Complex.I)) Filter.atTop (nhds 0))
    (hleft : MeasureTheory.Integrable (fun y : ℝ ↦ K ((a : ℂ) + y * Complex.I)))
    (hright : MeasureTheory.Integrable (fun y : ℝ ↦ K ((b : ℂ) + y * Complex.I))) :
    Filter.Tendsto
      (fun k ↦ rectangleBoundaryIntegral K ((a : ℂ) - T k * Complex.I) ((b : ℂ) + T k * Complex.I))
      Filter.atTop
      (nhds
        (Complex.I *
          ((∫ y : ℝ, K ((b : ℂ) + y * Complex.I)) - ∫ y : ℝ, K ((a : ℂ) + y * Complex.I)))) := by
  have htneg := Filter.tendsto_neg_atTop_atBot.comp hT
  have hr := MeasureTheory.intervalIntegral_tendsto_integral hright htneg hT
  have hl := MeasureTheory.intervalIntegral_tendsto_integral hleft htneg hT
  have hh := ((hbottom.sub htop).add (hr.const_mul Complex.I)).sub (hl.const_mul Complex.I)
  have heq :
    ∀ k,
      rectangleBoundaryIntegral K ((a : ℂ) - T k * Complex.I) ((b : ℂ) + T k * Complex.I) =
        ((∫ u in a..b, K ((u : ℂ) - T k * Complex.I)) -
              ∫ u in a..b, K ((u : ℂ) + T k * Complex.I)) +
            Complex.I * (∫ y in (-T k)..T k, K ((b : ℂ) + y * Complex.I)) -
          Complex.I * (∫ y in (-T k)..T k, K ((a : ℂ) + y * Complex.I)) := by
    intro k
    simp only [rectangleBoundaryIntegral, Complex.sub_re, Complex.add_re, Complex.sub_im,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, sub_self, add_zero, zero_add,
      zero_sub, smul_eq_mul, Complex.ofReal_neg, neg_mul]
    simp only [sub_eq_add_neg]
  have heqlim :
    (0 - 0 + Complex.I * (∫ y : ℝ, K ((b : ℂ) + y * Complex.I)) -
        Complex.I * (∫ y : ℝ, K ((a : ℂ) + y * Complex.I))) =
      Complex.I *
        ((∫ y : ℝ, K ((b : ℂ) + y * Complex.I)) - ∫ y : ℝ, K ((a : ℂ) + y * Complex.I)) := by
    ring
  rw [heqlim] at hh
  exact hh.congr (fun k ↦ (heq k).symm)

/-- An entire function with quadratic decay on the closed unit strip has equal
whole-line integrals on any two vertical lines in that strip, provided both
integrals exist. Cauchy's theorem annihilates finite rectangular boundaries;
the decay estimate removes horizontal edges, and integrability gives the
vertical limits. This supplies integration-line independence for Mellin kernels. -/
theorem integral_vertical_eq_of_strip_decay {f : ℂ → ℂ} (hf : Differentiable ℂ f) {c d C : ℝ}
    (hc : |c| ≤ 1) (hd : |d| ≤ 1) (hC : 0 ≤ C)
    (hb : ∀ s : ℂ, |s.re| ≤ 1 → ‖f s‖ ≤ C / (1 + ‖s‖ ^ 2))
    (hi : ∀ x : ℝ, |x| ≤ 1 → MeasureTheory.Integrable (fun t : ℝ ↦ f ((x : ℂ) + t * Complex.I))) :
    (∫ t : ℝ, f ((c : ℂ) + t * Complex.I)) = ∫ t : ℝ, f ((d : ℂ) + t * Complex.I) := by
  have hhor (e : ℝ) (he : e = 1 ∨ e = -1) :
    Filter.Tendsto (fun n : ℕ ↦ ∫ x in c..d, f ((x : ℂ) + (e * n : ℝ) * Complex.I)) Filter.atTop
      (nhds 0) := by
    apply squeeze_zero_norm (a := fun n : ℕ ↦ C / (n + 1) * |d - c|)
    · intro n
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      have hx1 : |x| ≤ 1 := by
        have hx' := (Set.mem_uIoc.mp hx)
        rcases hx' with hx' | hx'
        · exact abs_le.mpr ⟨(abs_le.mp hc).1.trans hx'.1.le, hx'.2.trans (abs_le.mp hd).2⟩
        · exact abs_le.mpr ⟨(abs_le.mp hd).1.trans hx'.1.le, hx'.2.trans (abs_le.mp hc).2⟩
      have hr : ((x : ℂ) + (e * n : ℝ) * Complex.I).re = x := by
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, zero_mul, sub_zero, add_zero]
      have hm : ((x : ℂ) + (e * n : ℝ) * Complex.I).im = e * n := by
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
      have hn : (n : ℝ) ≤ ‖(x : ℂ) + (e * n : ℝ) * Complex.I‖ ^ 2 := by
        have hi' := Complex.abs_im_le_norm ((x : ℂ) + (e * n : ℝ) * Complex.I)
        rw [hm] at hi'
        have hnsq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
          rw [pow_two]
          exact_mod_cast Nat.le_mul_self n
        have habs : |e * (n : ℝ)| = n := by
          rcases he with rfl | rfl
          · rw [one_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]
          · rw [neg_one_mul, abs_neg, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]
        rw [habs] at hi'
        nlinarith only [hi', hnsq, norm_nonneg ((x : ℂ) + (e * n : ℝ) * Complex.I),
          Nat.cast_nonneg (α := ℝ) n]
      exact
        (hb _
              (by
                rw [hr]; exact hx1)).trans
          (div_le_div_of_nonneg_left hC (by positivity : 0 < (n : ℝ) + 1) (by linarith only [hn]))
    · have hlim : Filter.Tendsto (fun n : ℕ ↦ C / ((n : ℝ) + 1)) Filter.atTop (nhds 0) := by
        simpa only [div_eq_mul_inv, one_mul, mul_zero] using
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul C
      simpa only [zero_mul] using hlim.mul_const |d - c|
  have ht :=
    tendsto_rectangleBoundaryIntegral_of_horizontal_limits (fun n : ℕ ↦ (n : ℝ))
      tendsto_natCast_atTop_atTop
      (by
        simpa only [neg_one_mul, Complex.ofReal_neg, neg_mul, sub_eq_add_neg, one_mul] using
          hhor (-1) (Or.inr rfl))
      (by simpa only [one_mul] using hhor 1 (Or.inl rfl)) (hi c hc) (hi d hd)
  have hz (n : ℕ) :
    rectangleBoundaryIntegral f ((c : ℂ) - n * Complex.I) ((d : ℂ) + n * Complex.I) = 0 :=
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn f _ _ hf.differentiableOn
  have he := tendsto_nhds_unique ht (tendsto_const_nhds.congr (fun n ↦ (hz n).symm))
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left Complex.I_ne_zero) |>.symm

end PseudoPrime.AnalyticNumberTheory.RectangleGeometry
