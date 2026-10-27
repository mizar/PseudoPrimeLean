/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.ZeroMeanSquareBounds

/-!
# Analytic-conductor budgets for fixed-completion mean squares

The explicit completed logarithmic derivative estimate supplies the row budget.
Only arithmetic completion data and an analytic-conductor cap remain as inputs;
there is no assumed zero-sum energy or pair-correlation estimate.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- The explicit real-part-three logarithmic-derivative allowance for endpoint order k,
degree d, and analytic-conductor cap C. The two universal convergent sums come from the
existing gamma and arithmetic bounds; no hidden asymptotic constant is introduced. -/
noncomputable def zeroRowBudget (k : ℤ) (d : ℕ) (C : ℝ) : ℝ :=
  2 * |(k : ℝ)| + Real.log C / 2 +
    (d : ℝ) *
      ((‖Complex.log (Real.pi : ℂ)‖ + Real.pi + Gamma.digammaLogErrorBound) / 2 +
        ∑' n : ℕ, Real.log n / (n : ℝ) ^ 2)

/-- If the conductor cap is at least one, the explicit row budget is nonnegative.
All terms have nonnegative signs, including the actual universal series. -/
theorem zeroRowBudget_nonneg (k : ℤ) (d : ℕ) {C : ℝ} (hC : 1 ≤ C) : 0 ≤ zeroRowBudget k d C := by
  have hg : 0 ≤ Gamma.digammaLogErrorBound := by
    exact tsum_nonneg (fun n ↦ div_nonneg (by norm_num only) (sq_nonneg _))
  have ha : 0 ≤ ∑' n : ℕ, Real.log n / (n : ℝ) ^ 2 :=
    tsum_nonneg (fun n ↦ div_nonneg (Real.log_natCast_nonneg n) (sq_nonneg _))
  exact
    add_nonneg
      (add_nonneg (mul_nonneg (by norm_num only) (abs_nonneg _))
        (div_nonneg (Real.log_nonneg hC) (by norm_num only)))
      (mul_nonneg (Nat.cast_nonneg d)
        (add_nonneg
          (div_nonneg (add_nonneg (add_nonneg (norm_nonneg _) Real.pi_pos.le) hg)
            (by norm_num only))
          ha))

/-- The existing arithmetic and archimedean estimates bound the actual completed
logarithmic derivative by zeroRowBudget whenever the analytic conductor is capped by C.
This supplies a row bound with explicit constants instead of an assumed energy bound. -/
theorem norm_logDeriv_le_zeroRowBudget {F L : ℂ → ℂ} {q d : ℕ} (hq : 1 ≤ q) (k : ℤ) (κ : Fin d → ℂ)
    (hκ : ∀ j, -1 < (κ j).re)
    (hreg :
      ∀ z,
        z ≠ 0 →
          z ≠ 1 → F z = (z * (1 - z)) ^ k * ((q : ℂ) ^ (z / 2) * archimedeanGammaFactor κ z * L z))
    {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ (d : ℝ) * n * Real.log n) {s : ℂ} (hs : s.re = 3) (hL : L s ≠ 0)
    (hdL : DifferentiableAt ℂ L s) (hlog : logDeriv L s = -LSeries a s) {C : ℝ}
    (hC : analyticConductor q κ s ≤ C) : ‖logDeriv F s‖ ≤ zeroRowBudget k d C := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hq)
  have hp : 0 < analyticConductor q κ s := by
    exact mul_pos hq0 (Finset.prod_pos (fun j hj ↦ by linarith only [norm_nonneg (s + κ j)]))
  have hl := Real.log_le_log hp hC
  have hb := norm_logDeriv_le_log_analyticConductor_at_three hq k κ hκ hreg ha hs hL hdL hlog
  dsimp only [zeroRowBudget]
  linarith only [hb, hl]

/-- Actual zero-height prefix energies are bounded by an explicit analytic-conductor
budget times the coefficient l2 mass. Completion, Euler-series, and conductor data replace
the previous abstract energy assumption. This statement is for one fixed completion. -/
theorem finite_zero_prefix_energy_le_conductor {F L : ℂ → ℂ} {ε : ℂ} {q d : ℕ} (hq : 1 ≤ q) (k : ℤ)
    (κ : Fin d → ℂ) (hκ : ∀ j, -1 < (κ j).re)
    (hreg :
      ∀ z,
        z ≠ 0 →
          z ≠ 1 → F z = (z * (1 - z)) ^ k * ((q : ℂ) ^ (z / 2) * archimedeanGammaFactor κ z * L z))
    (hε : ε ≠ 0) (hfe : ∀ z, F z = ε * star (F (1 - star z))) (hright : ∀ s, 1 < s.re → F s ≠ 0)
    (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) (horder : HasOrderAtMostOne F) {a : ℕ → ℂ}
    (ha : ∀ n, ‖a n‖ ≤ (d : ℝ) * n * Real.log n) (S : Finset ℂ) (b : ℂ → ℂ) {C : ℝ} (hC0 : 1 ≤ C)
    (hC : ∀ ρ ∈ S, analyticConductor q κ (((3 : ℝ) : ℂ) + ρ.im * Complex.I) ≤ C)
    (hL : ∀ ρ ∈ S, L (((3 : ℝ) : ℂ) + ρ.im * Complex.I) ≠ 0)
    (hdL : ∀ ρ ∈ S, DifferentiableAt ℂ L (((3 : ℝ) : ℂ) + ρ.im * Complex.I))
    (hlog :
      ∀ ρ ∈ S,
        logDeriv L (((3 : ℝ) : ℂ) + ρ.im * Complex.I) =
          -LSeries a (((3 : ℝ) : ℂ) + ρ.im * Complex.I))
    (t : ℝ) :
    PseudoPrime.Analysis.ExponentialMeanSquare.energy
        (PseudoPrime.Analysis.ExponentialMeanSquare.exponentialSum S Complex.im
          (PseudoPrime.Analysis.ExponentialMeanSquare.heightCoefficients Complex.im
            (fun ρ ↦ ((analyticOrderNatAt F ρ : ℝ) : ℂ) * b ρ) t)) ≤
      (9 * zeroRowBudget k d C) * ∑ ρ ∈ S, (analyticOrderNatAt F ρ : ℝ) * ‖b ρ‖ ^ 2 := by
  apply finite_zero_prefix_energy_le hε hfe hright hF h0 horder S b (zeroRowBudget_nonneg k d hC0)
  intro ρ hρ
  have hs : ((((3 : ℝ) : ℂ) + ρ.im * Complex.I)).re = 3 := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero]
    norm_num only
  exact
    (Complex.re_le_norm _).trans
      (norm_logDeriv_le_zeroRowBudget hq k κ hκ hreg ha hs (hL ρ hρ) (hdL ρ hρ) (hlog ρ hρ)
        (hC ρ hρ))

/-- The explicit conductor-based prefix estimate supplies the actual Abel block point
bound. All intermediate energies and derivative energies are proved internally.
Only the displayed arithmetic completion and analytic-conductor hypotheses remain. -/
theorem finite_zero_block_point_le_conductor {F L : ℂ → ℂ} {ε : ℂ} {q d : ℕ} (hq : 1 ≤ q) (k : ℤ)
    (κ : Fin d → ℂ) (hκ : ∀ j, -1 < (κ j).re)
    (hreg :
      ∀ z,
        z ≠ 0 →
          z ≠ 1 → F z = (z * (1 - z)) ^ k * ((q : ℂ) ^ (z / 2) * archimedeanGammaFactor κ z * L z))
    (hε : ε ≠ 0) (hfe : ∀ z, F z = ε * star (F (1 - star z))) (hright : ∀ s, 1 < s.re → F s ≠ 0)
    (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) (horder : HasOrderAtMostOne F) {a : ℕ → ℂ}
    (ha : ∀ n, ‖a n‖ ≤ (d : ℝ) * n * Real.log n) (S : Finset ℂ) (b : ℂ → ℂ) {C : ℝ} (hC0 : 1 ≤ C)
    (hC : ∀ ρ ∈ S, analyticConductor q κ (((3 : ℝ) : ℂ) + ρ.im * Complex.I) ≤ C)
    (hL : ∀ ρ ∈ S, L (((3 : ℝ) : ℂ) + ρ.im * Complex.I) ≠ 0)
    (hdL : ∀ ρ ∈ S, DifferentiableAt ℂ L (((3 : ℝ) : ℂ) + ρ.im * Complex.I))
    (hlog :
      ∀ ρ ∈ S,
        logDeriv L (((3 : ℝ) : ℂ) + ρ.im * Complex.I) =
          -LSeries a (((3 : ℝ) : ℂ) + ρ.im * Complex.I))
    {U T : ℝ} (hU : 0 ≤ U) (hUT : U ≤ T) :
    ‖PseudoPrime.Analysis.ExponentialMeanSquare.exponentialSum S Complex.im
              (PseudoPrime.Analysis.ExponentialMeanSquare.heightCoefficients Complex.im
                (fun ρ ↦ ((analyticOrderNatAt F ρ : ℝ) : ℂ) * b ρ) T)
              0 -
            PseudoPrime.Analysis.ExponentialMeanSquare.exponentialSum S Complex.im
              (PseudoPrime.Analysis.ExponentialMeanSquare.heightCoefficients Complex.im
                (fun ρ ↦ ((analyticOrderNatAt F ρ : ℝ) : ℂ) * b ρ) U)
              0‖ ^
        2 ≤
      4 * (1 + 2 * T - U) *
        ((9 * zeroRowBudget k d C) * ∑ ρ ∈ S, (analyticOrderNatAt F ρ : ℝ) * ‖b ρ‖ ^ 2) := by
  apply
    PseudoPrime.Analysis.ExponentialMeanSquare.block_point_le_of_prefix S Complex.im
      (fun ρ ↦ ((analyticOrderNatAt F ρ : ℝ) : ℂ) * b ρ) hU hUT
      (mul_nonneg (mul_nonneg (by norm_num only) (zeroRowBudget_nonneg k d hC0))
        (Finset.sum_nonneg (fun ρ hρ ↦ mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))))
  exact fun t ht ↦
    finite_zero_prefix_energy_le_conductor hq k κ hκ hreg hε hfe hright hF h0 horder ha S b hC0 hC
      hL hdL hlog t

/-- A real height window and a norm bound on gamma shifts give an explicit conductor cap.
Use the triangle inequality for each archimedean factor, then multiply the factor bounds. -/
theorem analyticConductor_le_height_cap {d : ℕ} (q : ℕ) (κ : Fin d → ℂ) {t H K : ℝ} (ht : |t| ≤ H)
    (hκ : ∀ j, ‖κ j‖ ≤ K) :
    analyticConductor q κ (((3 : ℝ) : ℂ) + t * Complex.I) ≤ (q : ℝ) * (6 + H + K) ^ d := by
  have hn : ‖((3 : ℝ) : ℂ) + t * Complex.I‖ ≤ 3 + |t| := by
    have h := norm_add_le (((3 : ℝ) : ℂ)) ((t : ℂ) * Complex.I)
    simpa only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by norm_num only : (0 : ℝ) < 3)] using h
  have hf : ∀ j : Fin d, ‖(((3 : ℝ) : ℂ) + t * Complex.I) + κ j‖ + 3 ≤ 6 + H + K := by
    intro j
    have h := norm_add_le ((((3 : ℝ) : ℂ) + t * Complex.I)) (κ j)
    linarith only [h, hn, ht, hκ j]
  have hp :=
    Finset.prod_le_prod₀ (s := Finset.univ)
      (fun j hj ↦ add_nonneg (norm_nonneg _) (by norm_num only)) (fun j hj ↦ hf j)
  have hh := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  simpa only [analyticConductor, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hh

/-- Positive conductor and nonnegative height and shift bounds make the explicit
height conductor cap at least one. This supplies positivity of the row budget. -/
theorem one_le_height_conductor_cap {q d : ℕ} (hq : 1 ≤ q) {H K : ℝ} (hH : 0 ≤ H) (hK : 0 ≤ K) :
    1 ≤ (q : ℝ) * (6 + H + K) ^ d := by
  have hb : 1 ≤ 6 + H + K := by linarith only [hH, hK]
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  exact one_le_mul_of_one_le_of_one_le hq1 (one_le_pow₀ hb)

/-- A bounded height window and bounded gamma shifts give a fixed-completion prefix
energy estimate with conductor cap q(6+H+K)^d, explicitly in q and the height.
The coefficient l2 mass remains visible for subsequent Mellin-kernel optimization. -/
theorem finite_zero_prefix_energy_le_height {F L : ℂ → ℂ} {ε : ℂ} {q d : ℕ} (hq : 1 ≤ q) (k : ℤ)
    (κ : Fin d → ℂ) (hκ : ∀ j, -1 < (κ j).re)
    (hreg :
      ∀ z,
        z ≠ 0 →
          z ≠ 1 → F z = (z * (1 - z)) ^ k * ((q : ℂ) ^ (z / 2) * archimedeanGammaFactor κ z * L z))
    (hε : ε ≠ 0) (hfe : ∀ z, F z = ε * star (F (1 - star z))) (hright : ∀ s, 1 < s.re → F s ≠ 0)
    (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) (horder : HasOrderAtMostOne F) {a : ℕ → ℂ}
    (ha : ∀ n, ‖a n‖ ≤ (d : ℝ) * n * Real.log n) (S : Finset ℂ) (b : ℂ → ℂ) {H K : ℝ} (hH : 0 ≤ H)
    (hK : 0 ≤ K) (hκnorm : ∀ j, ‖κ j‖ ≤ K) (hheight : ∀ ρ ∈ S, |ρ.im| ≤ H)
    (hL : ∀ ρ ∈ S, L (((3 : ℝ) : ℂ) + ρ.im * Complex.I) ≠ 0)
    (hdL : ∀ ρ ∈ S, DifferentiableAt ℂ L (((3 : ℝ) : ℂ) + ρ.im * Complex.I))
    (hlog :
      ∀ ρ ∈ S,
        logDeriv L (((3 : ℝ) : ℂ) + ρ.im * Complex.I) =
          -LSeries a (((3 : ℝ) : ℂ) + ρ.im * Complex.I))
    (t : ℝ) :
    PseudoPrime.Analysis.ExponentialMeanSquare.energy
        (PseudoPrime.Analysis.ExponentialMeanSquare.exponentialSum S Complex.im
          (PseudoPrime.Analysis.ExponentialMeanSquare.heightCoefficients Complex.im
            (fun ρ ↦ ((analyticOrderNatAt F ρ : ℝ) : ℂ) * b ρ) t)) ≤
      (9 * zeroRowBudget k d ((q : ℝ) * (6 + H + K) ^ d)) *
        ∑ ρ ∈ S, (analyticOrderNatAt F ρ : ℝ) * ‖b ρ‖ ^ 2 := by
  exact
    finite_zero_prefix_energy_le_conductor hq k κ hκ hreg hε hfe hright hF h0 horder ha S b
      (one_le_height_conductor_cap hq hH hK)
      (fun ρ hρ ↦ analyticConductor_le_height_cap q κ (hheight ρ hρ) hκnorm) hL hdL hlog t

end PseudoPrime.AnalyticNumberTheory.General
