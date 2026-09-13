/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaFactorGrowth
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveHorizontalLogDerivBound

/-!
# Ordinary logarithmic-derivative envelopes along selected heights

Subtract the gamma-factor logarithmic derivative from the completed one. The centered
completed envelope, its constant value at zero divided by height squared, and the
gamma-factor bound `C*(T+1)/T²` all tend to zero. This yields uniform ordinary `L'/L`
envelopes on `|σ| ≤ 2` at both selected heights.
-/

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/--
Input/assumptions: `N ≥ 2`, `χ` a primitive quadratic non-principal character mod `N` with
`χ⁻¹ ≠ 1`, GRH.
Conclusion: there is an envelope `η : ℕ → ℝ with η k → 0` such that for every `k` and every `σ` with
`|σ| ≤ 2`, `‖logDeriv (LFunction χ) (σ ± i (primitiveHorizontalHeightSeq k))‖ /
(primitiveHorizontalHeightSeq k)² ≤ η k`.
Content: writes `logDeriv (LFunction χ) s = logDeriv (completedLFunction χ) s -
logDeriv (gammaFactor χ) s` (valid since `T k ≥ k + 1 ≥ 1 > 0` gives `s.im ≠ 0`, and
`completedLFunction χ s ≠ 0` is supplied by
`primitiveHorizontalHeightSeq_completedLFunction_ne_zero`), bounds the first term via the
triangle inequality against
`primitiveHorizontalHeightSeq_completedLogDeriv_bound`'s difference-from-`0` bound `ε k` plus the
constant `‖logDeriv (completedLFunction χ) 0‖ / (T k)²`, and the second term via
`DirichletLFunction.exists_norm_logDeriv_gammaFactor_horizontal_le`'s `C_Γ (T k + 1) / (T k)²`. The
resulting envelope
`η k := ε k + ‖logDeriv (completedLFunction χ) 0‖ / (T k)² + C_Γ (T k + 1) / (T k)²` tends to `0`
since `ε k → 0` and `T k → ∞` makes both the constant-over-square and the linear-over-square terms
vanish.
Role: the horizontal estimate checkpoint, feeding the reciprocal contour kernel pointwise bound.
Stated
directly against the named `primitiveHorizontalHeightSeq` (rather than an opaque `∃ T`) so later
steps can reuse the same height sequence's nonvanishing/good-height facts without re-choosing `T`.
-/
theorem exists_envelope_primitiveHorizontalHeightSeq_LLogDeriv_small {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) :
    ∃ η : ℕ → ℝ,
      Filter.Tendsto η Filter.atTop (nhds 0) ∧
        ∀ k : ℕ,
          ∀ σ : ℝ,
            |σ| ≤ 2 →
              ‖logDeriv (DirichletCharacter.LFunction χ)
                        ((σ : ℂ) +
                          primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k *
                            Complex.I)‖ /
                    (primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k) ^ 2 ≤
                  η k ∧
                ‖logDeriv (DirichletCharacter.LFunction χ)
                        ((σ : ℂ) -
                          primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k *
                            Complex.I)‖ /
                    (primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k) ^ 2 ≤
                  η k := by
  obtain ⟨CΓ, hCΓnonneg, hCΓ⟩ :=
    exists_norm_logDeriv_gammaFactor_horizontal_le
  set T : ℕ → ℝ := primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad with hT_def
  set ε : ℕ → ℝ := primitiveHorizontalStripEpsilon hN2 hGRH hprimitive hne hinv hquad with hε_def
  set η : ℕ → ℝ := fun k =>
    ε k + ‖logDeriv (DirichletCharacter.completedLFunction χ) (0 : ℂ)‖ / (T k) ^ 2 +
      CΓ * (T k + 1) / (T k) ^ 2 with
    hη_def
  have hT_tendsto : Filter.Tendsto T Filter.atTop Filter.atTop :=
    tendsto_primitiveHorizontalHeightSeq_atTop hN2 hGRH hprimitive hne hinv hquad
  have hε_tendsto : Filter.Tendsto ε Filter.atTop (nhds 0) :=
    tendsto_primitiveHorizontalStripEpsilon_atTop hN2 hGRH hprimitive hne hinv hquad
  refine ⟨η, ?_, fun k σ hσ => ?_⟩
  · set F0 : ℝ := ‖logDeriv (DirichletCharacter.completedLFunction χ) (0 : ℂ)‖ with hF0_def
    set K : ℝ := F0 + 2 * CΓ with hK_def
    have hKnonneg : 0 ≤ K := by
      rw [hK_def]
      have h0 := norm_nonneg (logDeriv (DirichletCharacter.completedLFunction χ) (0 : ℂ))
      linarith
    have hrest_upper :
      ∀ᶠ k : ℕ in Filter.atTop, F0 / (T k) ^ 2 + CΓ * (T k + 1) / (T k) ^ 2 ≤ K / T k := by
      filter_upwards [hT_tendsto.eventually_ge_atTop (1 : ℝ)] with k hk
      have hTk_pos : 0 < T k := by linarith
      rw [← add_div, div_le_div_iff₀ (by positivity) hTk_pos]
      have h1 : 0 ≤ F0 * T k * (T k - 1) := by
        apply mul_nonneg (mul_nonneg (norm_nonneg _) hTk_pos.le)
        linarith
      have h2 : 0 ≤ CΓ * T k * (T k - 1) := by
        apply mul_nonneg (mul_nonneg hCΓnonneg hTk_pos.le)
        linarith
      have h3 : 0 ≤ CΓ * (T k) ^ 2 := mul_nonneg hCΓnonneg (sq_nonneg _)
      nlinarith [h1, h2, h3]
    have hrest_lower :
      ∀ᶠ k : ℕ in Filter.atTop, (0 : ℝ) ≤ F0 / (T k) ^ 2 + CΓ * (T k + 1) / (T k) ^ 2 := by
      filter_upwards [hT_tendsto.eventually_gt_atTop (0 : ℝ)] with k hk
      have h1 : (0 : ℝ) ≤ F0 / (T k) ^ 2 := by positivity
      have h2 : (0 : ℝ) ≤ CΓ * (T k + 1) / (T k) ^ 2 := by
        apply div_nonneg (mul_nonneg hCΓnonneg (by linarith)) (by positivity)
      linarith
    have hK_tendsto : Filter.Tendsto (fun k : ℕ => K / T k) Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop hT_tendsto
    have hrest_tendsto :
      Filter.Tendsto (fun k : ℕ => F0 / (T k) ^ 2 + CΓ * (T k + 1) / (T k) ^ 2) Filter.atTop
        (nhds 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hK_tendsto hrest_lower
        hrest_upper
    have hsum := hε_tendsto.add hrest_tendsto
    simpa only [hη_def, hF0_def, add_assoc, add_zero] using hsum
  · have hTk_ge1 : 1 ≤ T k := by
      have h := primitiveHorizontalHeightSeq_ge hN2 hGRH hprimitive hne hinv hquad k
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      rw [hT_def]; linarith
    have hTk_pos : 0 < T k := by linarith
    have hTksq_pos : 0 < (T k) ^ 2 := by positivity
    have hmain :
      ∀ Treal : ℝ,
        |Treal| = T k →
          DirichletCharacter.completedLFunction χ ((σ : ℂ) + (Treal : ℂ) * Complex.I) ≠ 0 →
          ‖logDeriv (DirichletCharacter.completedLFunction χ) ((σ : ℂ) + (Treal : ℂ) * Complex.I) -
                  logDeriv (DirichletCharacter.completedLFunction χ) 0‖ /
              (T k) ^ 2 ≤
            ε k →
          ‖logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (Treal : ℂ) * Complex.I)‖ /
              (T k) ^ 2 ≤
            η k := by
      intro Treal habs hFne hdiff_le
      have hTreal_ge1 : 1 ≤ |Treal| := by
        rw [habs]; exact hTk_ge1
      have hsim_eq : ((σ : ℂ) + (Treal : ℂ) * Complex.I).im = Treal := by
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
      have hsim_ne : ((σ : ℂ) + (Treal : ℂ) * Complex.I).im ≠ 0 := by
        rw [hsim_eq]
        intro h
        rw [h] at hTreal_ge1
        norm_num only at hTreal_ge1
      have hbridge :=
        logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor
          hne hFne hsim_ne
      have hgamma_bound := hCΓ χ σ Treal hσ hTreal_ge1
      rw [habs] at hgamma_bound
      have hcompleted_diff_le :
        ‖logDeriv (DirichletCharacter.completedLFunction χ) ((σ : ℂ) + (Treal : ℂ) * Complex.I) -
              logDeriv (DirichletCharacter.completedLFunction χ) 0‖ ≤
          ε k * (T k) ^ 2 :=
        (div_le_iff₀ hTksq_pos).mp hdiff_le
      have htri :
        ‖logDeriv (DirichletCharacter.completedLFunction χ) ((σ : ℂ) + (Treal : ℂ) * Complex.I)‖ ≤
          ‖logDeriv (DirichletCharacter.completedLFunction χ) ((σ : ℂ) + (Treal : ℂ) * Complex.I) -
                logDeriv (DirichletCharacter.completedLFunction χ) 0‖ +
            ‖logDeriv (DirichletCharacter.completedLFunction χ) (0 : ℂ)‖ := by
        have :=
          norm_add_le
            (logDeriv (DirichletCharacter.completedLFunction χ)
                ((σ : ℂ) + (Treal : ℂ) * Complex.I) -
              logDeriv (DirichletCharacter.completedLFunction χ) 0)
            (logDeriv (DirichletCharacter.completedLFunction χ) (0 : ℂ))
        simpa only [ge_iff_le, sub_add_cancel] using this
      have hLbound :
        ‖logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (Treal : ℂ) * Complex.I)‖ ≤
          ε k * (T k) ^ 2 + ‖logDeriv (DirichletCharacter.completedLFunction χ) (0 : ℂ)‖ +
            CΓ * (T k + 1) := by
        rw [hbridge]
        calc
          ‖logDeriv (DirichletCharacter.completedLFunction χ) ((σ : ℂ) + (Treal : ℂ) * Complex.I) -
                  logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) + (Treal : ℂ) * Complex.I)‖ ≤
              ‖logDeriv (DirichletCharacter.completedLFunction χ)
                    ((σ : ℂ) + (Treal : ℂ) * Complex.I)‖ +
                ‖logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) + (Treal : ℂ) * Complex.I)‖ :=
            norm_sub_le _ _
          _ ≤
              (‖logDeriv (DirichletCharacter.completedLFunction χ) (0 : ℂ)‖ + ε k * (T k) ^ 2) +
                CΓ * (T k + 1) :=
            by
            gcongr
            linarith [htri, hcompleted_diff_le]
          _ =
              ε k * (T k) ^ 2 + ‖logDeriv (DirichletCharacter.completedLFunction χ) (0 : ℂ)‖ +
                CΓ * (T k + 1) :=
            by ring
      rw [div_le_iff₀ hTksq_pos, hη_def]
      have heq :
        (ε k + ‖logDeriv (DirichletCharacter.completedLFunction χ) (0 : ℂ)‖ / (T k) ^ 2 +
              CΓ * (T k + 1) / (T k) ^ 2) *
            (T k) ^ 2 =
          ε k * (T k) ^ 2 + ‖logDeriv (DirichletCharacter.completedLFunction χ) (0 : ℂ)‖ +
            CΓ * (T k + 1) := by
        field_simp
      rw [heq]
      exact hLbound
    refine ⟨?_, ?_⟩
    · exact
        hmain (T k) (abs_of_nonneg hTk_pos.le)
          (primitiveHorizontalHeightSeq_completedLFunction_ne_zero hN2 hGRH hprimitive hne hinv
              hquad k hσ).1
          (primitiveHorizontalHeightSeq_completedLogDeriv_bound hN2 hGRH hprimitive hne hinv hquad k
              hσ).1
    · have hform : (σ : ℂ) - (T k : ℂ) * Complex.I = (σ : ℂ) + ((-(T k) : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [hform]
      have hFne :=
        (primitiveHorizontalHeightSeq_completedLFunction_ne_zero hN2 hGRH hprimitive hne hinv hquad
            k hσ).2
      rw [hform] at hFne
      have hdiff :=
        (primitiveHorizontalHeightSeq_completedLogDeriv_bound hN2 hGRH hprimitive hne hinv hquad k
            hσ).2
      rw [hform] at hdiff
      exact
        hmain (-(T k))
          (by
            rw [abs_neg]; exact abs_of_nonneg hTk_pos.le)
          hFne hdiff

/--
Input/assumptions: `N ≥ 2`, `χ` a primitive non-principal character mod `N` with
`χ⁻¹ ≠ 1`, GRH.
Conclusion: there is an envelope `η : ℕ → ℝ with η k → 0` such that for every `k` and every `σ` with
`|σ| ≤ 2`, `‖logDeriv (LFunction χ) (σ ± i (primitiveHorizontalHeightSeq_of_grh k))‖ /
(primitiveHorizontalHeightSeq_of_grh k)² ≤ η k`.
Content: writes `logDeriv (LFunction χ) s = logDeriv (completedLFunction χ) s -
logDeriv (gammaFactor χ) s` (valid since `T k ≥ k + 1 ≥ 1 > 0` gives `s.im ≠ 0`, and
`completedLFunction χ s ≠ 0` is supplied by
`primitiveHorizontalHeightSeq_completedLFunction_ne_zero_of_grh`), bounds the first term via the
triangle inequality against
`primitiveHorizontalHeightSeq_completedLogDeriv_bound_of_grh`'s difference-from-`0` bound `ε k`
plus the constant `‖logDeriv (completedLFunction χ) 0‖ / (T k)²`, and the second term via
`DirichletLFunction.exists_norm_logDeriv_gammaFactor_horizontal_le`'s `C_Γ (T k + 1) / (T k)²`. The
resulting envelope
`η k := ε k + ‖logDeriv (completedLFunction χ) 0‖ / (T k)² + C_Γ (T k + 1) / (T k)²` tends to `0`
since `ε k → 0` and `T k → ∞` makes both the constant-over-square and the linear-over-square terms
vanish.
Role: the horizontal estimate checkpoint, feeding the reciprocal contour kernel pointwise bound.
Stated
directly against the named `primitiveHorizontalHeightSeq_of_grh` (rather than an opaque `∃ T`) so
later steps can reuse the same height sequence's nonvanishing/good-height facts without
re-choosing `T`.
-/
theorem exists_envelope_primitiveHorizontalHeightSeq_LLogDeriv_small_of_grh {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    ∃ η : ℕ → ℝ,
      Filter.Tendsto η Filter.atTop (nhds 0) ∧
        ∀ k : ℕ,
          ∀ σ : ℝ,
            |σ| ≤ 2 →
              ‖logDeriv (DirichletCharacter.LFunction χ)
                        ((σ : ℂ) +
                          primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k *
                            Complex.I)‖ /
                    (primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k) ^ 2 ≤
                  η k ∧
                ‖logDeriv (DirichletCharacter.LFunction χ)
                        ((σ : ℂ) -
                          primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k *
                            Complex.I)‖ /
                    (primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k) ^ 2 ≤
                  η k := by
  obtain ⟨CΓ, hCΓnonneg, hCΓ⟩ :=
    exists_norm_logDeriv_gammaFactor_horizontal_le
  set T : ℕ → ℝ := primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv with hT_def
  set ε : ℕ → ℝ := primitiveHorizontalStripEpsilon_of_grh hN2 hGRH hprimitive hne hinv with hε_def
  set η : ℕ → ℝ := fun k =>
    ε k + ‖logDeriv (DirichletCharacter.completedLFunction χ) (0 : ℂ)‖ / (T k) ^ 2 +
      CΓ * (T k + 1) / (T k) ^ 2 with
    hη_def
  have hT_tendsto : Filter.Tendsto T Filter.atTop Filter.atTop :=
    tendsto_primitiveHorizontalHeightSeq_atTop_of_grh hN2 hGRH hprimitive hne hinv
  have hε_tendsto : Filter.Tendsto ε Filter.atTop (nhds 0) :=
    tendsto_primitiveHorizontalStripEpsilon_atTop_of_grh hN2 hGRH hprimitive hne hinv
  refine ⟨η, ?_, fun k σ hσ => ?_⟩
  · set F0 : ℝ := ‖logDeriv (DirichletCharacter.completedLFunction χ) (0 : ℂ)‖ with hF0_def
    set K : ℝ := F0 + 2 * CΓ with hK_def
    have hKnonneg : 0 ≤ K := by
      rw [hK_def]
      have h0 := norm_nonneg (logDeriv (DirichletCharacter.completedLFunction χ) (0 : ℂ))
      linarith
    have hrest_upper :
      ∀ᶠ k : ℕ in Filter.atTop, F0 / (T k) ^ 2 + CΓ * (T k + 1) / (T k) ^ 2 ≤ K / T k := by
      filter_upwards [hT_tendsto.eventually_ge_atTop (1 : ℝ)] with k hk
      have hTk_pos : 0 < T k := by linarith
      rw [← add_div, div_le_div_iff₀ (by positivity) hTk_pos]
      have h1 : 0 ≤ F0 * T k * (T k - 1) := by
        apply mul_nonneg (mul_nonneg (norm_nonneg _) hTk_pos.le)
        linarith
      have h2 : 0 ≤ CΓ * T k * (T k - 1) := by
        apply mul_nonneg (mul_nonneg hCΓnonneg hTk_pos.le)
        linarith
      have h3 : 0 ≤ CΓ * (T k) ^ 2 := mul_nonneg hCΓnonneg (sq_nonneg _)
      nlinarith [h1, h2, h3]
    have hrest_lower :
      ∀ᶠ k : ℕ in Filter.atTop, (0 : ℝ) ≤ F0 / (T k) ^ 2 + CΓ * (T k + 1) / (T k) ^ 2 := by
      filter_upwards [hT_tendsto.eventually_gt_atTop (0 : ℝ)] with k hk
      have h1 : (0 : ℝ) ≤ F0 / (T k) ^ 2 := by positivity
      have h2 : (0 : ℝ) ≤ CΓ * (T k + 1) / (T k) ^ 2 := by
        apply div_nonneg (mul_nonneg hCΓnonneg (by linarith)) (by positivity)
      linarith
    have hK_tendsto : Filter.Tendsto (fun k : ℕ => K / T k) Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop hT_tendsto
    have hrest_tendsto :
      Filter.Tendsto (fun k : ℕ => F0 / (T k) ^ 2 + CΓ * (T k + 1) / (T k) ^ 2) Filter.atTop
        (nhds 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hK_tendsto hrest_lower
        hrest_upper
    have hsum := hε_tendsto.add hrest_tendsto
    simpa only [hη_def, hF0_def, add_assoc, add_zero] using hsum
  · have hTk_ge1 : 1 ≤ T k := by
      have h := primitiveHorizontalHeightSeq_ge_of_grh hN2 hGRH hprimitive hne hinv k
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      rw [hT_def]; linarith
    have hTk_pos : 0 < T k := by linarith
    have hTksq_pos : 0 < (T k) ^ 2 := by positivity
    have hmain :
      ∀ Treal : ℝ,
        |Treal| = T k →
          DirichletCharacter.completedLFunction χ ((σ : ℂ) + (Treal : ℂ) * Complex.I) ≠ 0 →
          ‖logDeriv (DirichletCharacter.completedLFunction χ) ((σ : ℂ) + (Treal : ℂ) * Complex.I) -
                  logDeriv (DirichletCharacter.completedLFunction χ) 0‖ /
              (T k) ^ 2 ≤
            ε k →
          ‖logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (Treal : ℂ) * Complex.I)‖ /
              (T k) ^ 2 ≤
            η k := by
      intro Treal habs hFne hdiff_le
      have hTreal_ge1 : 1 ≤ |Treal| := by
        rw [habs]; exact hTk_ge1
      have hsim_eq : ((σ : ℂ) + (Treal : ℂ) * Complex.I).im = Treal := by
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
      have hsim_ne : ((σ : ℂ) + (Treal : ℂ) * Complex.I).im ≠ 0 := by
        rw [hsim_eq]
        intro h
        rw [h] at hTreal_ge1
        norm_num only at hTreal_ge1
      have hbridge :=
        logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor
          hne hFne hsim_ne
      have hgamma_bound := hCΓ χ σ Treal hσ hTreal_ge1
      rw [habs] at hgamma_bound
      have hcompleted_diff_le :
        ‖logDeriv (DirichletCharacter.completedLFunction χ) ((σ : ℂ) + (Treal : ℂ) * Complex.I) -
              logDeriv (DirichletCharacter.completedLFunction χ) 0‖ ≤
          ε k * (T k) ^ 2 :=
        (div_le_iff₀ hTksq_pos).mp hdiff_le
      have htri :
        ‖logDeriv (DirichletCharacter.completedLFunction χ) ((σ : ℂ) + (Treal : ℂ) * Complex.I)‖ ≤
          ‖logDeriv (DirichletCharacter.completedLFunction χ) ((σ : ℂ) + (Treal : ℂ) * Complex.I) -
                logDeriv (DirichletCharacter.completedLFunction χ) 0‖ +
            ‖logDeriv (DirichletCharacter.completedLFunction χ) (0 : ℂ)‖ := by
        have :=
          norm_add_le
            (logDeriv (DirichletCharacter.completedLFunction χ)
                ((σ : ℂ) + (Treal : ℂ) * Complex.I) -
              logDeriv (DirichletCharacter.completedLFunction χ) 0)
            (logDeriv (DirichletCharacter.completedLFunction χ) (0 : ℂ))
        simpa only [ge_iff_le, sub_add_cancel] using this
      have hLbound :
        ‖logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (Treal : ℂ) * Complex.I)‖ ≤
          ε k * (T k) ^ 2 + ‖logDeriv (DirichletCharacter.completedLFunction χ) (0 : ℂ)‖ +
            CΓ * (T k + 1) := by
        rw [hbridge]
        calc
          ‖logDeriv (DirichletCharacter.completedLFunction χ) ((σ : ℂ) + (Treal : ℂ) * Complex.I) -
                  logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) + (Treal : ℂ) * Complex.I)‖ ≤
              ‖logDeriv (DirichletCharacter.completedLFunction χ)
                    ((σ : ℂ) + (Treal : ℂ) * Complex.I)‖ +
                ‖logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) + (Treal : ℂ) * Complex.I)‖ :=
            norm_sub_le _ _
          _ ≤
              (‖logDeriv (DirichletCharacter.completedLFunction χ) (0 : ℂ)‖ + ε k * (T k) ^ 2) +
                CΓ * (T k + 1) :=
            by
            gcongr
            linarith [htri, hcompleted_diff_le]
          _ =
              ε k * (T k) ^ 2 + ‖logDeriv (DirichletCharacter.completedLFunction χ) (0 : ℂ)‖ +
                CΓ * (T k + 1) :=
            by ring
      rw [div_le_iff₀ hTksq_pos, hη_def]
      have heq :
        (ε k + ‖logDeriv (DirichletCharacter.completedLFunction χ) (0 : ℂ)‖ / (T k) ^ 2 +
              CΓ * (T k + 1) / (T k) ^ 2) *
            (T k) ^ 2 =
          ε k * (T k) ^ 2 + ‖logDeriv (DirichletCharacter.completedLFunction χ) (0 : ℂ)‖ +
            CΓ * (T k + 1) := by
        field_simp
      rw [heq]
      exact hLbound
    refine ⟨?_, ?_⟩
    · exact
        hmain (T k) (abs_of_nonneg hTk_pos.le)
          (primitiveHorizontalHeightSeq_completedLFunction_ne_zero_of_grh hN2 hGRH hprimitive hne
              hinv k hσ).1
          (primitiveHorizontalHeightSeq_completedLogDeriv_bound_of_grh hN2 hGRH hprimitive hne hinv
              k hσ).1
    · have hform : (σ : ℂ) - (T k : ℂ) * Complex.I = (σ : ℂ) + ((-(T k) : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [hform]
      have hFne :=
        (primitiveHorizontalHeightSeq_completedLFunction_ne_zero_of_grh hN2 hGRH hprimitive hne hinv
            k hσ).2
      rw [hform] at hFne
      have hdiff :=
        (primitiveHorizontalHeightSeq_completedLogDeriv_bound_of_grh hN2 hGRH hprimitive hne hinv k
            hσ).2
      rw [hform] at hdiff
      exact
        hmain (-(T k))
          (by
            rw [abs_neg]; exact abs_of_nonneg hTk_pos.le)
          hFne hdiff

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
