/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.SelectedZeroSplit
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.UnifiedZeroExhaustion

/-! # Eventual selected-zero bounds in unified contour sums -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- A fixed selection of zeros in `(A,T]` eventually lies in the middle band
of every unified contour ledger. Only bounded-height exhaustion is required. -/
theorem selected_eventually_in_middle {A T : ℝ} (hT : 0 ≤ T) (Q : Finset ℂ) (hQ : Q ⊆ zerosUpTo T)
    (hA : ∀ ρ ∈ Q, A < |ρ.im|) :
    ∀ᶠ m : ℕ in Filter.atTop,
      Q ⊆
        ((riemannZetaZerosInAnyRectangle (unifiedRectangleLower m)
                  (unifiedTauRectangleUpper 2 m)).filter
              (fun ρ ↦ ¬ρ.re < 0)).filter
          (fun ρ ↦ A < |ρ.im| ∧ |ρ.im| ≤ T) := by
  filter_upwards [zerosUpTo_eventually_in_unified hT] with m hm
  intro ρ hρ
  exact Finset.mem_filter.mpr ⟨hm (hQ hρ), hA ρ hρ, ((mem_zerosUpTo hT).mp (hQ hρ)).2.2⟩

/-- Under RH, the integrated kernel of a nonnegative-real-part zeta zero can
use the selected-copy API's exclusion of one. RH forces its real part to one half. -/
theorem selected_zero_ne_one (hRH : RiemannHypothesis) {ρ : ℂ} (hz : riemannZeta ρ = 0)
    (hre : 0 ≤ ρ.re) : ρ ≠ 1 := by
  have hxi := RiemannXi.xi_zero_of_zeta_zero_of_re_nonneg hz hre
  have hr := RiemannXi.xi_zero_re_eq_half_of_riemannHypothesis hRH hxi
  intro he
  rw [he, Complex.one_re] at hr
  norm_num only at hr

/-- Unified finite ledgers eventually satisfy the selected-copy residual
kernel estimate with a fixed low head. This is the uniform finite bound needed
for the signed integrated explicit-formula limit. -/
theorem selected_kernel_eventually_le (hRH : RiemannHypothesis) {A T a b : ℝ} (hA : 0 ≤ A)
    (hAT : A ≤ T) (ha : 0 < a) (hab : a < b) (Q : Finset ℂ) (hQ : Q ⊆ zerosUpTo T)
    (hQA : ∀ ρ ∈ Q, A < |ρ.im|) :
    let S := fun m : ℕ ↦
      (riemannZetaZerosInAnyRectangle (unifiedRectangleLower m)
            (unifiedTauRectangleUpper 2 m)).filter
        (fun ρ ↦ ¬ρ.re < 0)
    let f := fun ρ : ℂ ↦ ((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) / (ρ * (ρ + 1))
    ∀ᶠ m : ℕ in Filter.atTop,
      ‖(∑ ρ ∈ S m, (riemannZetaZeroMultiplicity ρ : ℂ) * f ρ) -
            (∑ ρ ∈ zerosUpTo A, (riemannZetaZeroMultiplicity ρ : ℂ) * f ρ) -
            (∑ ρ ∈ Q, f ρ)‖ ≤
        (b - a) *
            (Real.sqrt b * (zeroReciprocalSum T - zeroReciprocalSum A - ∑ ρ ∈ Q, 1 / |ρ.im|)) +
          (b ^ (3 / 2 : ℝ) + a ^ (3 / 2 : ℝ)) * ordinateTail T := by
  classical
  dsimp only
  filter_upwards [unified_head_eventually_eq hA,
    selected_eventually_in_middle (hA.trans hAT) Q hQ hQA] with m hhead hmiddle
  let S :=
    (riemannZetaZerosInAnyRectangle (unifiedRectangleLower m) (unifiedTauRectangleUpper 2 m)).filter
      (fun ρ ↦ ¬ρ.re < 0)
  have hz : ∀ ρ ∈ S, riemannZeta ρ = 0 := by
    intro ρ hρ
    exact (mem_riemannZetaZerosInAnyRectangle_iff.mp (Finset.mem_filter.mp hρ).1).2
  have hre : ∀ ρ ∈ S, 0 ≤ ρ.re := fun ρ hρ ↦ not_lt.mp (Finset.mem_filter.mp hρ).2
  have h :=
    selected_finite_kernel_le hRH S Q hz hre
      (fun ρ hρ ↦ selected_zero_ne_one hRH (hz ρ hρ) (hre ρ hρ)) hA hAT ha hab hmiddle
  dsimp only at h
  rw [show S.filter (fun ρ ↦ |ρ.im| ≤ A) = zerosUpTo A from hhead] at h
  exact h

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
