/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.SelectedZeroWeights
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroReciprocalInterval
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.OrdinateTail
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.IntegratedHighZeroBound

/-! # Residual reciprocal budgets after selecting zero copies -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- A finite residual sum in the height band `(A,T]` is bounded by the full
reciprocal difference minus selected unit copies. Positivity of zero multiplicities
justifies subtraction, without completeness or simplicity of the selected set. -/
theorem selected_band_reciprocal_le {A T : ℝ} (hA : 0 ≤ A) (hAT : A ≤ T) (M Q : Finset ℂ)
    (hM : M ⊆ (zerosUpTo T).filter (fun ρ ↦ A < |ρ.im|))
    (hQ : Q ⊆ (zerosUpTo T).filter (fun ρ ↦ A < |ρ.im|)) (hρ : ∀ ρ ∈ Q, ρ ≠ 1) :
    (∑ ρ ∈ M, ((riemannZetaZeroMultiplicity ρ : ℝ) - (if ρ ∈ Q then 1 else 0)) / |ρ.im|) ≤
      zeroReciprocalSum T - zeroReciprocalSum A - ∑ ρ ∈ Q, 1 / |ρ.im| := by
  classical
  have hz : ∀ ρ ∈ Q, riemannZeta ρ = 0 := by
    intro ρ hmem
    have hb := Finset.mem_filter.mp (hQ hmem)
    exact ((mem_zerosUpTo (hA.trans hAT)).mp hb.1).1
  have h :=
    selected_reciprocal_le M ((zerosUpTo T).filter (fun ρ ↦ A < |ρ.im|)) Q hM hQ
      (fun ρ ↦ (riemannZetaZeroMultiplicity ρ : ℝ)) (fun ρ ↦ |ρ.im|)
      (fun ρ hmem ↦ selected_weight_nonneg Q hz hρ ρ) (fun ρ hmem ↦ abs_nonneg ρ.im)
  rw [zeroReciprocal_interval hA hAT] at h
  exact h

/-- The integrated finite residual kernel is controlled by the selected-copy
reciprocal budget. This connects weighted low-zero analysis to the exact subtraction
of the chosen zeros in `(A,T]`. -/
theorem selected_band_kernel_le (hRH : RiemannHypothesis) {A T a b : ℝ} (hA : 0 ≤ A) (hAT : A ≤ T)
    (ha : 0 < a) (hab : a < b) (M Q : Finset ℂ) (hM : M ⊆ (zerosUpTo T).filter (fun ρ ↦ A < |ρ.im|))
    (hQ : Q ⊆ (zerosUpTo T).filter (fun ρ ↦ A < |ρ.im|)) (hρM : ∀ ρ ∈ M, ρ ≠ 1)
    (hρQ : ∀ ρ ∈ Q, ρ ≠ 1) :
    ‖∑ ρ ∈ M,
            ((((riemannZetaZeroMultiplicity ρ : ℝ) - (if ρ ∈ Q then 1 else 0) : ℝ) : ℂ) *
              (((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) / (ρ * (ρ + 1))))‖ /
        (b - a) ≤
      Real.sqrt b * (zeroReciprocalSum T - zeroReciprocalSum A - ∑ ρ ∈ Q, 1 / |ρ.im|) := by
  classical
  have hmem : ∀ ρ ∈ M, riemannZeta ρ = 0 ∧ 0 ≤ ρ.re := by
    intro ρ hρ
    have h := (mem_zerosUpTo (hA.trans hAT)).mp (Finset.mem_filter.mp (hM hρ)).1
    exact ⟨h.1, h.2.1⟩
  have hzQ : ∀ ρ ∈ Q, riemannZeta ρ = 0 := by
    intro ρ hρ
    exact ((mem_zerosUpTo (hA.trans hAT)).mp (Finset.mem_filter.mp (hQ hρ)).1).1
  have hs :=
    low_weighted_sum hRH M (fun ρ ↦ (riemannZetaZeroMultiplicity ρ : ℝ) - (if ρ ∈ Q then 1 else 0))
      (fun ρ hρ ↦ (hmem ρ hρ).1) (fun ρ hρ ↦ (hmem ρ hρ).2) hρM
      (fun ρ hρ ↦ selected_weight_nonneg Q hzQ hρQ ρ) ha hab
  exact
    hs.trans
      (mul_le_mul_of_nonneg_left (selected_band_reciprocal_le hA hAT M Q hM hQ hρQ)
        (Real.sqrt_nonneg b))

/-- Every finite high-zero kernel sum is controlled by the actual full
inverse-square ordinate tail. No separate finite-ledger tail hypothesis remains. -/
theorem selected_high_kernel_le (hRH : RiemannHypothesis) (U : Finset ℂ)
    (hz : ∀ ρ ∈ U, riemannZeta ρ = 0) (hre : ∀ ρ ∈ U, 0 ≤ ρ.re) {a b T : ℝ} (ha : 0 < a)
    (hab : a < b) (hT : ∀ ρ ∈ U, T < |ρ.im|) :
    ‖∑ ρ ∈ U,
            (riemannZetaZeroMultiplicity ρ : ℂ) *
              (((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) / (ρ * (ρ + 1)))‖ /
        (b - a) ≤
      (b ^ (3 / 2 : ℝ) + a ^ (3 / 2 : ℝ)) / (b - a) * ordinateTail T := by
  have ht := finite_ordinate_tail_le hRH U T hz hre hT
  have h := high_sum_of_tail hRH U hz hre ha (ha.trans hab) (sub_pos.mpr hab) ht
  simpa only [mul_div_assoc] using h

/-- The middle and high normalized kernel budgets add to the full residual
budget used after cancelling the signed head. Both bounds are analytic, and the
high budget uses the actual summable ordinate tail. -/
theorem selected_kernel_pair_le {mid high : ℂ} {a b R U : ℝ} (hab : a < b)
    (hm : ‖mid‖ / (b - a) ≤ Real.sqrt b * R)
    (hu : ‖high‖ / (b - a) ≤ (b ^ (3 / 2 : ℝ) + a ^ (3 / 2 : ℝ)) / (b - a) * U) :
    ‖mid + high‖ ≤
      (b - a) * (Real.sqrt b * R + (b ^ (3 / 2 : ℝ) + a ^ (3 / 2 : ℝ)) / (b - a) * U) := by
  have h := div_le_div_of_nonneg_right (norm_add_le mid high) (sub_nonneg.mpr hab.le)
  rw [add_div] at h
  have hs := h.trans (add_le_add hm hu)
  exact (div_le_iff₀ (sub_pos.mpr hab)).mp hs |>.trans_eq (mul_comm _ _)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
