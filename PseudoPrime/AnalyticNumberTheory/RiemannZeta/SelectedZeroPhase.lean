/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.SelectedZeroMidpoint
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadPhase

/-! # Phase normalization of selected signed midpoint sums -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- A finite weighted sum on the critical line factors into the square root
of its positive base and a signed exponential phase sum. The weights are
arbitrary real numbers, so the identity also applies to selected unit copies. -/
theorem weighted_critical_phase (S : Finset ℂ) (w : ℂ → ℝ) (hr : ∀ ρ ∈ S, ρ.re = 1 / 2) {t : ℝ}
    (ht : 0 < t) :
    (∑ ρ ∈ S, (w ρ : ℂ) * ((t : ℂ) ^ ρ / ρ)).re =
      Real.sqrt t *
        (∑ ρ ∈ S,
            (w ρ : ℂ) * (Complex.exp (((ρ.im * Real.log t : ℝ) : ℂ) * Complex.I) / ρ)).re := by
  have hc (ρ : ℂ) (hρ : ρ ∈ S) :
    (t : ℂ) ^ ρ = (Real.sqrt t : ℂ) * Complex.exp (((ρ.im * Real.log t : ℝ) : ℂ) * Complex.I) := by
    have he := Complex.re_add_im ρ
    rw [hr ρ hρ] at he
    conv_lhs => rw [← he]
    exact cpow_critical_phase ht ρ.im
  have hs :
    (∑ ρ ∈ S, (w ρ : ℂ) * ((t : ℂ) ^ ρ / ρ)) =
      (Real.sqrt t : ℂ) *
        (∑ ρ ∈ S, (w ρ : ℂ) * (Complex.exp (((ρ.im * Real.log t : ℝ) : ℂ) * Complex.I) / ρ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ρ hρ
    rw [hc ρ hρ]
    ring
  rw [hs, Complex.re_ofReal_mul]

/-- Under RH, a signed midpoint head consisting of all zeros through A
and unit copies selected through T is exactly a square-root amplitude times
its finite phase sum. No zero count is needed for the additional selection. -/
theorem selected_head_phase (hRH : RiemannHypothesis) {A T t : ℝ} (hA : 0 ≤ A) (hT : 0 ≤ T)
    (ht : 0 < t) (Q : Finset ℂ) (hQ : Q ⊆ zerosUpTo T) :
    let f := fun ρ : ℂ ↦ (t : ℂ) ^ ρ / ρ
    let p := fun ρ : ℂ ↦ Complex.exp (((ρ.im * Real.log t : ℝ) : ℂ) * Complex.I) / ρ
    ((∑ ρ ∈ zerosUpTo A, (riemannZetaZeroMultiplicity ρ : ℂ) * f ρ) + (∑ ρ ∈ Q, f ρ)).re =
      Real.sqrt t *
        ((∑ ρ ∈ zerosUpTo A, (riemannZetaZeroMultiplicity ρ : ℂ) * p ρ) + (∑ ρ ∈ Q, p ρ)).re := by
  have hr {U : ℝ} (hU : 0 ≤ U) (ρ : ℂ) (hρ : ρ ∈ zerosUpTo U) : ρ.re = 1 / 2 := by
    have hz := (mem_zerosUpTo hU).mp hρ
    exact
      RiemannXi.xi_zero_re_eq_half_of_riemannHypothesis hRH
        (RiemannXi.xi_zero_of_zeta_zero_of_re_nonneg hz.1 hz.2.1)
  have hl :=
    weighted_critical_phase (zerosUpTo A) (fun ρ ↦ (riemannZetaZeroMultiplicity ρ : ℝ)) (hr hA) ht
  have hq := weighted_critical_phase Q (fun _ ↦ 1) (fun ρ hρ ↦ hr hT ρ (hQ hρ)) ht
  simp only [Complex.ofReal_natCast, Complex.ofReal_one, one_mul] at hl hq
  dsimp only
  rw [Complex.add_re, Complex.add_re, hl, hq, mul_add]

/-- Under RH, the selected backward midpoint bound is expressed entirely
through signed exponential phases at the logarithmic midpoint. This connects
the integrated zero formula to finite scalar interval certificates. -/
theorem psi_selected_phase (hRH : RiemannHypothesis) {A T x h : ℝ} (hA : 0 ≤ A) (hAT : A ≤ T)
    (hh : 0 < h) (hx : 1 < x - h) (Q : Finset ℂ) (hQ : Q ⊆ zerosUpTo T)
    (hQA : ∀ ρ ∈ Q, A < |ρ.im|) :
    let g := fun ρ : ℂ ↦ Complex.exp (((ρ.im * Real.log ((x - h + x) / 2) : ℝ) : ℂ) * Complex.I) / ρ
    let P :=
      Real.sqrt ((x - h + x) / 2) *
        ((∑ ρ ∈ zerosUpTo A, (riemannZetaZeroMultiplicity ρ : ℂ) * g ρ) + (∑ ρ ∈ Q, g ρ)).re
    let M := (∑ ρ ∈ zerosUpTo A, (riemannZetaZeroMultiplicity ρ : ℝ) * ‖ρ - 1‖) + (∑ ρ ∈ Q, ‖ρ - 1‖)
    let D := M * (x - h) ^ (-(3 / 2 : ℝ)) * h ^ 3 / 24
    let E :=
      h * (Real.sqrt x * (zeroReciprocalSum T - zeroReciprocalSum A - ∑ ρ ∈ Q, 1 / |ρ.im|)) +
        (x ^ (3 / 2 : ℝ) + (x - h) ^ (3 / 2 : ℝ)) * ordinateTail T +
        1
    x - Chebyshev.psi x ≤ h / 2 + Real.log (2 * Real.pi) + (h * P + D + E) / h := by
  have ht : 0 < (x - h + x) / 2 := by linarith only [hx, hh]
  have he := selected_head_phase hRH hA (hA.trans hAT) ht Q hQ
  have hp := psi_selected_midpoint hRH hA hAT hh hx Q hQ hQA
  dsimp only at he hp ⊢
  rw [he] at hp
  exact hp

/-- Under RH, the selected signed phase estimate bounds the lower normalized
theta deviation after adding the unconditional three-root prime-power bound.
All analytic errors are explicit; only finite phase and scalar estimates remain. -/
theorem theta_selected_phase (hRH : RiemannHypothesis) {A T x h : ℝ} (hA : 0 ≤ A) (hAT : A ≤ T)
    (hh : 0 < h) (hx : 1 < x - h) (Q : Finset ℂ) (hQ : Q ⊆ zerosUpTo T)
    (hQA : ∀ ρ ∈ Q, A < |ρ.im|) :
    let g := fun ρ : ℂ ↦ Complex.exp (((ρ.im * Real.log ((x - h + x) / 2) : ℝ) : ℂ) * Complex.I) / ρ
    let P :=
      Real.sqrt ((x - h + x) / 2) *
        ((∑ ρ ∈ zerosUpTo A, (riemannZetaZeroMultiplicity ρ : ℂ) * g ρ) + (∑ ρ ∈ Q, g ρ)).re
    let M := (∑ ρ ∈ zerosUpTo A, (riemannZetaZeroMultiplicity ρ : ℝ) * ‖ρ - 1‖) + (∑ ρ ∈ Q, ‖ρ - 1‖)
    let D := M * (x - h) ^ (-(3 / 2 : ℝ)) * h ^ 3 / 24
    let E :=
      h * (Real.sqrt x * (zeroReciprocalSum T - zeroReciprocalSum A - ∑ ρ ∈ Q, 1 / |ρ.im|)) +
        (x ^ (3 / 2 : ℝ) + (x - h) ^ (3 / 2 : ℝ)) * ordinateTail T +
        1
    (x - Chebyshev.theta x) / Real.sqrt x ≤
      (h / 2 + Real.log (2 * Real.pi) + (h * P + D + E) / h +
          (Chebyshev.psi (x ^ (2 : ℝ)⁻¹) + Chebyshev.psi (x ^ (3 : ℝ)⁻¹) +
            Chebyshev.psi (x ^ (5 : ℝ)⁻¹))) /
        Real.sqrt x := by
  have hp := psi_selected_phase hRH hA hAT hh hx Q hQ hQA
  have hg := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  dsimp only at hp ⊢
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg x)
  linarith only [hp, hg]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
