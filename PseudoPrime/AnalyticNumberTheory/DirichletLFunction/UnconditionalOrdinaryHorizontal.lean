/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.UnconditionalHorizontalLimits
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaFactorGrowth

/-! # Unconditional ordinary logarithmic-derivative envelopes at good heights -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- At a nonzero imaginary coordinate where the completed function is nonzero,
an ordinary logarithmic-derivative norm divided by height squared is bounded by
the centered completed norm, its center value, and a gamma-factor bound with the
same normalization. Subtract the gamma logarithmic derivative and use the triangle
inequality. This transfers unconditional completed envelopes to ordinary L-functions. -/
theorem ordinary_logDeriv_normalized_le_completed {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hne : χ ≠ 1) (s : ℂ) (hsim : s.im ≠ 0) (hc : χ.completedLFunction s ≠ 0) (T G : ℝ)
    (hgamma : ‖logDeriv (DirichletCharacter.gammaFactor χ) s‖ ≤ G) :
    ‖logDeriv χ.LFunction s‖ / T ^ 2 ≤
      ‖logDeriv χ.completedLFunction s - logDeriv χ.completedLFunction 0‖ / T ^ 2 +
        ‖logDeriv χ.completedLFunction 0‖ / T ^ 2 +
        G / T ^ 2 := by
  have htri :=
    norm_add_le (logDeriv χ.completedLFunction s - logDeriv χ.completedLFunction 0)
      (logDeriv χ.completedLFunction 0)
  rw [sub_add_cancel] at htri
  have hbound :
    ‖logDeriv χ.LFunction s‖ ≤
      ‖logDeriv χ.completedLFunction s - logDeriv χ.completedLFunction 0‖ +
        ‖logDeriv χ.completedLFunction 0‖ +
        G := by
    rw [logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor hne hc hsim]
    exact (norm_sub_le _ _).trans (add_le_add htri hgamma)
  have h := div_le_div_of_nonneg_right hbound (sq_nonneg T)
  convert h using 1
  ring

/-- Along a real height sequence tending to infinity, a nonnegative constant and
nonnegative linear growth term divided by height squared tend to zero. Squeeze
by a constant divided by height. This absorbs the centered value and gamma correction. -/
theorem tendsto_constant_add_linear_div_sq (T : ℕ → ℝ)
    (hT : Filter.Tendsto T Filter.atTop Filter.atTop) (F G : ℝ) (hF : 0 ≤ F) (hG : 0 ≤ G) :
    Filter.Tendsto (fun k : ℕ ↦ F / (T k) ^ 2 + G * (T k + 1) / (T k) ^ 2) Filter.atTop
      (nhds 0) := by
  have hlower : ∀ᶠ k : ℕ in Filter.atTop, 0 ≤ F / (T k) ^ 2 + G * (T k + 1) / (T k) ^ 2 := by
    filter_upwards [hT.eventually_ge_atTop (0 : ℝ)] with k hk
    exact
      add_nonneg (div_nonneg hF (sq_nonneg _))
        (div_nonneg (mul_nonneg hG (add_nonneg hk zero_le_one)) (sq_nonneg _))
  have hupper :
    ∀ᶠ k : ℕ in Filter.atTop, F / (T k) ^ 2 + G * (T k + 1) / (T k) ^ 2 ≤ (F + 2 * G) / T k := by
    filter_upwards [hT.eventually_ge_atTop (1 : ℝ)] with k hk
    have htpos : 0 < T k := zero_lt_one.trans_le hk
    rw [← add_div, div_le_div_iff₀ (pow_pos htpos 2) htpos]
    have h₁ := mul_nonneg (mul_nonneg hF htpos.le) (sub_nonneg.mpr hk)
    have h₂ := mul_nonneg (mul_nonneg hG htpos.le) (sub_nonneg.mpr hk)
    nlinarith only [h₁, h₂]
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (tendsto_const_nhds.div_atTop hT)
      hlower hupper

/-- Every primitive nonprincipal character with nonprincipal inverse admits one
height sequence tending to infinity and an ordinary logarithmic-derivative
envelope tending to zero after height-square normalization, uniformly on the
central strip at both signs. The completed function is nonzero on both edges.
Subtract the gamma factor from the unconditional completed height sequence.
This supplies the kernel estimates for unconditional horizontal contour limits. -/
theorem exists_unconditional_ordinary_horizontal_height_sequence {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    ∃ T η : ℕ → ℝ,
      Filter.Tendsto T Filter.atTop Filter.atTop ∧
        Filter.Tendsto η Filter.atTop (nhds 0) ∧
        ∀ k : ℕ,
          (k : ℝ) + 1 ≤ T k ∧
            ∀ σ : ℝ,
              |σ| ≤ 2 →
                ‖logDeriv χ.LFunction ((σ : ℂ) + T k * Complex.I)‖ / (T k) ^ 2 ≤ η k ∧
                  ‖logDeriv χ.LFunction ((σ : ℂ) - T k * Complex.I)‖ / (T k) ^ 2 ≤ η k ∧
                  χ.completedLFunction ((σ : ℂ) + T k * Complex.I) ≠ 0 ∧
                  χ.completedLFunction ((σ : ℂ) - T k * Complex.I) ≠ 0 := by
  obtain ⟨T, ε, hT, hε, hspec⟩ := exists_unconditional_horizontal_height_sequence hq hp hne hinv
  obtain ⟨G, hG, hgamma⟩ := exists_norm_logDeriv_gammaFactor_horizontal_le
  let η := fun k : ℕ ↦
    ε k + ‖logDeriv χ.completedLFunction 0‖ / (T k) ^ 2 + G * (T k + 1) / (T k) ^ 2
  have hrest :=
    tendsto_constant_add_linear_div_sq T hT ‖logDeriv χ.completedLFunction 0‖ G (norm_nonneg _) hG
  have hη : Filter.Tendsto η Filter.atTop (nhds 0) := by
    have h := hε.add hrest
    simpa only [η, add_zero, add_assoc] using h
  refine ⟨T, η, hT, hη, ?_⟩
  intro k
  refine ⟨(hspec k).1, ?_⟩
  intro σ hσ
  have hk : 1 ≤ (k : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg k)
  have hσwide : |σ| ≤ 2 * ((k : ℝ) + 1) := hσ.trans (by linarith only [hk])
  obtain ⟨hplus, hminus, hnplus, hnminus⟩ := (hspec k).2 σ hσwide
  have hTge : 1 ≤ T k := hk.trans (hspec k).1
  have hTpos : 0 < T k := zero_lt_one.trans_le hTge
  have hmain (t : ℝ) (ht : |t| = T k)
    (hc : χ.completedLFunction ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0)
    (hεbound :
      ‖logDeriv χ.completedLFunction ((σ : ℂ) + (t : ℂ) * Complex.I) -
              logDeriv χ.completedLFunction 0‖ /
          (T k) ^ 2 ≤
        ε k) :
    ‖logDeriv χ.LFunction ((σ : ℂ) + (t : ℂ) * Complex.I)‖ / (T k) ^ 2 ≤ η k := by
    have him : (((σ : ℂ) + (t : ℂ) * Complex.I).im) = t := by
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
        mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
    have htim : t ≠ 0 := by
      intro hz
      rw [hz, abs_zero] at ht
      exact hTpos.ne' ht.symm
    have hgbound :=
      hgamma χ σ t hσ
        (by
          rw [ht]; exact hTge)
    rw [ht] at hgbound
    have hraw :=
      ordinary_logDeriv_normalized_le_completed hne _ (by rwa [him]) hc (T k) (G * (T k + 1))
        hgbound
    dsimp only [η]
    linarith only [hraw, hεbound]
  have hform : (σ : ℂ) - (T k : ℂ) * Complex.I = (σ : ℂ) + ((-(T k) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  refine ⟨hmain (T k) (abs_of_nonneg hTpos.le) hnplus hplus, ?_, hnplus, hnminus⟩
  rw [hform]
  rw [hform] at hnminus hminus
  exact hmain (-(T k)) (by rw [abs_neg, abs_of_nonneg hTpos.le]) hnminus hminus

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
