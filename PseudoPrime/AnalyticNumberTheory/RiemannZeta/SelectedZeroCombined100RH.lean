/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.SelectedZeroExhaustion
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCombinedAbove100RH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiSign100RH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadDistance100

/-! # Combined height-100 budget after subtracting selected copies -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The combined reciprocal and tail budget above height 100, with the
reciprocals of selected unit copies subtracted. Inputs are the positive cutoff
T and finite selection Q. Under RH, T >= 100 and Q in (100,T], this scalar is
nonnegative and bounds the actual residual band plus T times the ordinate tail. -/
@[expose]
noncomputable def selectedReciprocalCost (T : ℝ) (Q : Finset ℂ) : ℝ :=
  ((Real.log (T / (2 * Real.pi))) ^ 2 + 2 * Real.log (T / (2 * Real.pi)) + 2) / (2 * Real.pi) -
        143 / 125 -
        (3 / 8 : ℝ) / T +
      1 / (15 * T ^ 2) -
    ∑ ρ ∈ Q, 1 / |ρ.im|

/-- Under RH and T >= 100, subtracting the selected reciprocal sum from
the proved combined budget bounds the actual residual plus the tail. The
height-100 zero count is supplied by the existing internal sign certificates. -/
theorem selected_combined100_le (hRH : RiemannHypothesis) {T : ℝ} (hT : 100 ≤ T) (Q : Finset ℂ) :
    zeroReciprocalSum T - zeroReciprocalSum 100 - (∑ ρ ∈ Q, 1 / |ρ.im|) + T * ordinateTail T ≤
      selectedReciprocalCost T Q := by
  have hb := combined_zero_above100 hRH (count_100_eq_58_of_RH hRH) hT
  dsimp only [selectedReciprocalCost]
  linarith only [hb]

/-- Under RH, choosing unit copies from the height band leaves a
nonnegative reciprocal difference. Apply the residual subset bound to the
empty finite sum; positivity of actual multiplicity justifies the subtraction. -/
theorem selected_reciprocal_nonneg (hRH : RiemannHypothesis) {A T : ℝ} (hA : 0 ≤ A) (hAT : A ≤ T)
    (Q : Finset ℂ) (hQ : Q ⊆ zerosUpTo T) (hQA : ∀ ρ ∈ Q, A < |ρ.im|) :
    0 ≤ zeroReciprocalSum T - zeroReciprocalSum A - ∑ ρ ∈ Q, 1 / |ρ.im| := by
  classical
  have hband : Q ⊆ (zerosUpTo T).filter (fun ρ ↦ A < |ρ.im|) := by
    intro ρ hρ
    exact Finset.mem_filter.mpr ⟨hQ hρ, hQA ρ hρ⟩
  have hne (ρ : ℂ) (hρ : ρ ∈ Q) : ρ ≠ 1 := by
    have hz := (mem_zerosUpTo (hA.trans hAT)).mp (hQ hρ)
    exact selected_zero_ne_one hRH hz.1 hz.2.1
  have hb := selected_band_reciprocal_le hA hAT ∅ Q (Finset.empty_subset _) hband hne
  simpa only [Finset.sum_empty] using hb

/-- Under RH, the explicit selected reciprocal cost is nonnegative for
selections in (100,T]. Both the residual band and the actual tail are
nonnegative, which permits the conservative scalar factor 1+delta. -/
theorem selected_cost_nonneg (hRH : RiemannHypothesis) {T : ℝ} (hT : 100 ≤ T) (Q : Finset ℂ)
    (hQ : Q ⊆ zerosUpTo T) (hQA : ∀ ρ ∈ Q, 100 < |ρ.im|) : 0 ≤ selectedReciprocalCost T Q := by
  have hr := selected_reciprocal_nonneg hRH (by norm_num only) hT Q hQ hQA
  have hu : 0 ≤ ordinateTail T := by
    rw [ordinateTail_eq]
    exact tsum_nonneg (fun ρ ↦ (ordinateTailWeight_bound hRH T ρ).1)
  have ht : 0 ≤ T := le_trans (by norm_num only) hT
  exact (add_nonneg hr (mul_nonneg ht hu)).trans (selected_combined100_le hRH hT Q)

/-- Under RH, the residual combined budget is at most (1+delta) times
the explicit selected cost whenever delta >= 0. This is the conservative
factor used by the existing rational middle-range certificate formula. -/
theorem selected_combined100_scaled (hRH : RiemannHypothesis) {T δ : ℝ} (hT : 100 ≤ T) (hd : 0 ≤ δ)
    (Q : Finset ℂ) (hQ : Q ⊆ zerosUpTo T) (hQA : ∀ ρ ∈ Q, 100 < |ρ.im|) :
    zeroReciprocalSum T - zeroReciprocalSum 100 - (∑ ρ ∈ Q, 1 / |ρ.im|) + T * ordinateTail T ≤
      (1 + δ) * selectedReciprocalCost T Q := by
  have hb := selected_combined100_le hRH hT Q
  have hp := mul_nonneg hd (selected_cost_nonneg hRH hT Q hQ hQA)
  nlinarith only [hb, hp]

/-- Under RH, the internally certified low zeros give the strict moment
bound 3640. Existence, brackets and the height-100 count are discharged
internally rather than supplied as parameters of downstream theta bounds. -/
theorem low_head_moment_lt_3640 (hRH : RiemannHypothesis) :
    (∑ ρ ∈ zerosUpTo 100, (riemannZetaZeroMultiplicity ρ : ℝ) * ‖ρ - 1‖) < 3640 := by
  obtain ⟨g, hm, hp, hh, hz, _, hu⟩ := low_zero_100_exists
  exact zero_head_distance100_lt hRH g hm hp hh hz (count_100_eq_58_of_RH hRH).le hu

/-- Under RH, the distance moment of selected unit copies is bounded by
the sum of absolute ordinates plus one half. The critical-line identity
controls each term without a multiplicity or completeness hypothesis. -/
theorem selected_moment_le_ordinates (hRH : RiemannHypothesis) {T : ℝ} (hT : 0 ≤ T) (Q : Finset ℂ)
    (hQ : Q ⊆ zerosUpTo T) : (∑ ρ ∈ Q, ‖ρ - 1‖) ≤ ∑ ρ ∈ Q, (|ρ.im| + 1 / 2) := by
  apply Finset.sum_le_sum
  intro ρ hρ
  have hz := (mem_zerosUpTo hT).mp (hQ hρ)
  have hr :=
    RiemannXi.xi_zero_re_eq_half_of_riemannHypothesis hRH
      (RiemannXi.xi_zero_of_zeta_zero_of_re_nonneg hz.1 hz.2.1)
  have hn := Complex.norm_le_abs_re_add_abs_im (ρ - 1)
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero, hr] at hn
  norm_num only at hn
  linarith only [hn]

/-- Under RH, the combined low and selected midpoint moment is strictly
below 3640 plus the selected ordinate costs. This supplies the rational
moment constant after the selected ordinates are enclosed in their brackets. -/
theorem selected_total_moment_lt (hRH : RiemannHypothesis) {T : ℝ} (hT : 0 ≤ T) (Q : Finset ℂ)
    (hQ : Q ⊆ zerosUpTo T) :
    (∑ ρ ∈ zerosUpTo 100, (riemannZetaZeroMultiplicity ρ : ℝ) * ‖ρ - 1‖) + (∑ ρ ∈ Q, ‖ρ - 1‖) <
      3640 + (∑ ρ ∈ Q, (|ρ.im| + 1 / 2)) := by
  exact
    add_lt_add_of_lt_of_le (low_head_moment_lt_3640 hRH) (selected_moment_le_ordinates hRH hT Q hQ)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
