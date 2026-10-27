/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RectangleGeometry.VerticalLimits

/-! # Vertical integration on a nonnegative strip -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RectangleGeometry

/-- For a function differentiable at every point of the closed nonnegative unit strip,
quadratic decay and integrable vertical lines imply equal integrals at any two strip lines.
Remove horizontal edges by decay and apply Cauchy rectangles within the strip.
This allows negative-real-part poles outside the strip; global entire differentiability
is not required. It supplies the resolvent shift from the central line. -/
theorem integral_vertical_eq_of_nonnegative_strip_decay {f : ℂ → ℂ}
    (hf : ∀ s : ℂ, s.re ∈ Set.Icc (0 : ℝ) 1 → DifferentiableAt ℂ f s) {c d C : ℝ}
    (hc : c ∈ Set.Icc (0 : ℝ) 1) (hd : d ∈ Set.Icc (0 : ℝ) 1) (hC : 0 ≤ C)
    (hb : ∀ s : ℂ, s.re ∈ Set.Icc (0 : ℝ) 1 → ‖f s‖ ≤ C / (1 + ‖s‖ ^ 2))
    (hi :
      ∀ x : ℝ,
        x ∈ Set.Icc (0 : ℝ) 1 →
          MeasureTheory.Integrable (fun t : ℝ ↦ f ((x : ℂ) + t * Complex.I))) :
    (∫ t : ℝ, f ((c : ℂ) + t * Complex.I)) = ∫ t : ℝ, f ((d : ℂ) + t * Complex.I) := by
  have hhor (e : ℝ) (he : e = 1 ∨ e = -1) :
    Filter.Tendsto (fun n : ℕ ↦ ∫ x in c..d, f ((x : ℂ) + (e * n : ℝ) * Complex.I)) Filter.atTop
      (nhds 0) := by
    apply squeeze_zero_norm (a := fun n : ℕ ↦ C / (n + 1) * |d - c|)
    · intro n
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      have hx1 : x ∈ Set.Icc (0 : ℝ) 1 := by
        have hx' := (Set.mem_uIoc.mp hx)
        rcases hx' with hx' | hx'
        · exact ⟨hc.1.trans hx'.1.le, hx'.2.trans hd.2⟩
        · exact ⟨hd.1.trans hx'.1.le, hx'.2.trans hc.2⟩
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
          (div_le_div_of_nonneg_left hC
            (by linarith only [Nat.cast_nonneg (α := ℝ) n] : 0 < (n : ℝ) + 1)
            (by linarith only [hn]))
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
    rectangleBoundaryIntegral f ((c : ℂ) - n * Complex.I) ((d : ℂ) + n * Complex.I) = 0 := by
    apply rectangleBoundaryIntegral_eq_zero_of_differentiableOn
    intro s hs
    have hr := hs.1
    change s.re ∈ Set.uIcc _ _ at hr
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.natCast_im, Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero] at hr
    have hsr : s.re ∈ Set.Icc (0 : ℝ) 1 := by
      rcases Set.mem_uIcc.mp hr with h | h
      · exact ⟨hc.1.trans h.1, h.2.trans hd.2⟩
      · exact ⟨hd.1.trans h.1, h.2.trans hc.2⟩
    exact (hf s hsr).differentiableWithinAt
  have he := tendsto_nhds_unique ht (tendsto_const_nhds.congr (fun n ↦ (hz n).symm))
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left Complex.I_ne_zero) |>.symm

end PseudoPrime.AnalyticNumberTheory.RectangleGeometry
