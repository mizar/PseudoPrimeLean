/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveScaledHorizontalBounds
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaFactorGrowth

/-!
# Ordinary logarithmic derivative bounds on growing strips

The scaled centered envelope, the completed derivative at zero, and the fixed-strip gamma
bound give a common vanishing envelope for both signs of each selected height.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For a primitive non-principal character with non-principal inverse and any admissible
scaled family, there is a vanishing envelope for ordinary `L'/L` on the intersection of the
growing strip and the fixed strip `[-A-1/2,A+3/2]`. Subtract the gamma logarithmic derivative,
then squeeze the constant and linear correction terms divided by height squared.
This supplies the horizontal estimates for shifted rectangles. -/
theorem exists_envelope_scaledHorizontalStrip_LLogDeriv_small {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (data : ∀ k : ℕ, PrimitiveScaledHorizontalStripData χ ((k : ℝ) + 1)) (A : ℕ)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    ∃ η : ℕ → ℝ,
      Filter.Tendsto η Filter.atTop (nhds 0) ∧
        ∀ k : ℕ,
          ∀ σ : ℝ,
            |σ| ≤ 2 * ((k : ℝ) + 1) →
              -(A : ℝ) - 1 / 2 ≤ σ →
              σ ≤ (A : ℝ) + 3 / 2 →
              ‖logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (data k).T * Complex.I)‖ /
                    ((data k).T) ^ 2 ≤
                  η k ∧
                ‖logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) - (data k).T * Complex.I)‖ /
                    ((data k).T) ^ 2 ≤
                  η k := by
  obtain ⟨CΓ, hCΓnonneg, hCΓ⟩ := exists_norm_logDeriv_gammaFactor_fixed_strip_le A
  set T : ℕ → ℝ := fun k => (data k).T with hT_def
  set ε : ℕ → ℝ := scaledHorizontalStripEpsilon data with hε_def
  set η : ℕ → ℝ := fun k =>
    ε k + ‖logDeriv (DirichletCharacter.completedLFunction χ) (0 : ℂ)‖ / (T k) ^ 2 +
      CΓ * (T k + 1) / (T k) ^ 2 with
    hη_def
  have hT_tendsto : Filter.Tendsto T Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun k => (data k).T_mem.1)
      (Filter.tendsto_atTop_add_const_right Filter.atTop 1 tendsto_natCast_atTop_atTop)
  have hε_tendsto : Filter.Tendsto ε Filter.atTop (nhds 0) :=
    tendsto_scaledHorizontalStripEpsilon_atTop hN2 data hprimitive hne hinv
  refine ⟨η, ?_, fun k σ hσ hlo hhi => ?_⟩
  · set F0 : ℝ := ‖logDeriv (DirichletCharacter.completedLFunction χ) (0 : ℂ)‖ with hF0_def
    set K : ℝ := F0 + 2 * CΓ with hK_def
    have hKnonneg : 0 ≤ K := by
      rw [hK_def]
      have h0 := norm_nonneg (logDeriv (DirichletCharacter.completedLFunction χ) (0 : ℂ))
      rw [← hF0_def] at h0
      exact add_nonneg h0 (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) hCΓnonneg)
    have hrest_upper :
      ∀ᶠ k : ℕ in Filter.atTop, F0 / (T k) ^ 2 + CΓ * (T k + 1) / (T k) ^ 2 ≤ K / T k := by
      filter_upwards [hT_tendsto.eventually_ge_atTop (1 : ℝ)] with k hk
      have hTk_pos : 0 < T k := lt_of_lt_of_le zero_lt_one hk
      rw [← add_div, div_le_div_iff₀ (pow_pos hTk_pos 2) hTk_pos]
      have h1 : 0 ≤ F0 * T k * (T k - 1) := by
        apply mul_nonneg (mul_nonneg (norm_nonneg _) hTk_pos.le)
        exact sub_nonneg.mpr hk
      have h2 : 0 ≤ CΓ * T k * (T k - 1) := by
        apply mul_nonneg (mul_nonneg hCΓnonneg hTk_pos.le)
        exact sub_nonneg.mpr hk
      nlinarith only [hK_def, h1, h2]
    have hrest_lower :
      ∀ᶠ k : ℕ in Filter.atTop, (0 : ℝ) ≤ F0 / (T k) ^ 2 + CΓ * (T k + 1) / (T k) ^ 2 := by
      filter_upwards [hT_tendsto.eventually_gt_atTop (0 : ℝ)] with k hk
      have h1 : (0 : ℝ) ≤ F0 / (T k) ^ 2 := by
        rw [hF0_def]
        exact div_nonneg (norm_nonneg _) (sq_nonneg _)
      have h2 : (0 : ℝ) ≤ CΓ * (T k + 1) / (T k) ^ 2 := by
        exact div_nonneg (mul_nonneg hCΓnonneg (add_nonneg (le_of_lt hk) zero_le_one)) (sq_nonneg _)
      exact add_nonneg h1 h2
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
      have h := (data k).T_mem.1
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
        calc
          (1 : ℝ) = 0 + 1 := by norm_num only
          _ ≤ (k : ℝ) + 1 := add_le_add_left hk0 1
      rw [hT_def]
      exact le_trans hk1 h
    have hTk_pos : 0 < T k := lt_of_lt_of_le zero_lt_one hTk_ge1
    have hTksq_pos : 0 < (T k) ^ 2 := pow_pos hTk_pos 2
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
        rw [habs]
        exact hTk_ge1
      have hsim_eq : ((σ : ℂ) + (Treal : ℂ) * Complex.I).im = Treal := by
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
      have hsim_ne : ((σ : ℂ) + (Treal : ℂ) * Complex.I).im ≠ 0 := by
        rw [hsim_eq]
        intro h
        rw [h] at hTreal_ge1
        norm_num only at hTreal_ge1
      have hbridge := logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor hne hFne hsim_ne
      have hgamma_bound := hCΓ χ σ Treal hlo hhi hTreal_ge1
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
            calc
              _ ≤ _ := htri
              _ = _ := add_comm _ _
              _ ≤ _ := add_le_add_right hcompleted_diff_le _
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
        field_simp [ne_of_gt hTk_pos]
      rw [heq]
      exact hLbound
    refine ⟨?_, ?_⟩
    · exact
        hmain (T k) (abs_of_nonneg hTk_pos.le) ((data k).nonzero σ hσ).1
          (scaledHorizontalStripEpsilon_bound hN2 data hprimitive hne hinv k hσ).1
    · have hform : (σ : ℂ) - (T k : ℂ) * Complex.I = (σ : ℂ) + ((-(T k) : ℝ) : ℂ) * Complex.I := by
        push_cast
        ring
      rw [hform]
      have hFne := ((data k).nonzero σ hσ).2
      rw [hform] at hFne
      have hdiff := (scaledHorizontalStripEpsilon_bound hN2 data hprimitive hne hinv k hσ).2
      rw [hform] at hdiff
      exact
        hmain (-(T k))
          (by
            rw [abs_neg]
            exact abs_of_nonneg hTk_pos.le)
          hFne hdiff

/-- Individual character RH supplies heights tending to infinity and a common vanishing
ordinary logarithmic-derivative envelope on any fixed strip. Primitivity and non-principality
of the character and its inverse permit the completed-to-ordinary bridge. Discarding the
initial scales places the fixed strip inside every growing strip of the remaining family. -/
theorem exists_fixedStrip_LLogDeriv_envelope_of_dirichletRH {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (A : ℕ) :
    ∃ T η : ℕ → ℝ,
      Filter.Tendsto T Filter.atTop Filter.atTop ∧
        (∀ k, 1 ≤ T k) ∧
        Filter.Tendsto η Filter.atTop (nhds 0) ∧
        ∀ k v,
          -(A : ℝ) - 1 / 2 ≤ v →
            v ≤ (A : ℝ) + 3 / 2 →
            ‖logDeriv χ.LFunction ((v : ℂ) + T k * Complex.I)‖ / (T k) ^ 2 ≤ η k ∧
              ‖logDeriv χ.LFunction ((v : ℂ) - T k * Complex.I)‖ / (T k) ^ 2 ≤ η k := by
  let data := primitiveScaledHorizontalStripDataSeq_of_dirichletRH hN2 hRH hp hne hinv
  obtain ⟨η, hη, hbound⟩ :=
    exists_envelope_scaledHorizontalStrip_LLogDeriv_small hN2 data A hp hne hinv
  have hT : Filter.Tendsto (fun k => (data k).T) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun k => (data k).T_mem.1)
      (Filter.tendsto_atTop_add_const_right Filter.atTop 1 tendsto_natCast_atTop_atTop)
  refine ⟨fun k => (data (k + A + 1)).T, fun k => η (k + A + 1), ?_, ?_, ?_, ?_⟩
  · exact hT.comp ((Filter.tendsto_add_atTop_nat 1).comp (Filter.tendsto_add_atTop_nat A))
  · intro k
    have hn := (data (k + A + 1)).T_mem.1
    have hnonneg : (0 : ℝ) ≤ ((k + A + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    exact le_trans (by linarith only [hnonneg]) hn
  · exact hη.comp ((Filter.tendsto_add_atTop_nat 1).comp (Filter.tendsto_add_atTop_nat A))
  · intro k v hlo hhi
    apply hbound (k + A + 1) v _ hlo hhi
    rw [abs_le]
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    simp only [Nat.cast_add, Nat.cast_one]
    constructor <;> linarith only [hk, hlo, hhi, (Nat.cast_nonneg A : (0 : ℝ) ≤ (A : ℝ))]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
