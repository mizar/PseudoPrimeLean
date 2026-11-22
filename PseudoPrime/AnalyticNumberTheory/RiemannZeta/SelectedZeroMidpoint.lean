/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.SelectedZeroIntegral
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadMidpointRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadMidpoint

/-! # Signed midpoint bounds with selected zero copies -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH, unit copies of any finite selection of bounded-height zeros
admit midpoint quadrature with the unweighted distance sum as error constant.
No completeness or simplicity of the selected zeros is required. -/
theorem selected_midpoint_error (hRH : RiemannHypothesis) {T a b : ℝ} (hT : 0 ≤ T) (ha : 0 < a)
    (hab : a ≤ b) (Q : Finset ℂ) (hQ : Q ⊆ zerosUpTo T) :
    |(∑ ρ ∈ Q, ((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) / (ρ * (ρ + 1))).re -
          (b - a) * (∑ ρ ∈ Q, ((↑((a + b) / 2) : ℂ) ^ ρ / ρ)).re| ≤
      (∑ ρ ∈ Q, ‖ρ - 1‖) * a ^ (-(3 / 2 : ℝ)) * (b - a) ^ 3 / 24 := by
  have hr : ∀ ρ ∈ Q, ρ.re = 1 / 2 := by
    intro ρ hρ
    have hz := (mem_zerosUpTo hT).mp (hQ hρ)
    exact
      RiemannXi.xi_zero_re_eq_half_of_riemannHypothesis hRH
        (RiemannXi.xi_zero_of_zeta_zero_of_re_nonneg hz.1 hz.2.1)
  have he := weighted_head_midpoint_error Q (fun _ ↦ 1) (fun _ _ ↦ zero_le_one) hr ha hab
  simpa only [Complex.ofReal_one, one_mul] using he

/-- Under RH, midpoint quadrature retains the signed sum of the complete
low head and selected unit copies. The error constants add, while cancellation
between the two midpoint sums remains available to the scalar checker. -/
theorem selected_head_midpoint_error (hRH : RiemannHypothesis) {A T a b : ℝ} (hA : 0 ≤ A)
    (hT : 0 ≤ T) (ha : 0 < a) (hab : a ≤ b) (Q : Finset ℂ) (hQ : Q ⊆ zerosUpTo T) :
    let f := fun ρ : ℂ ↦ ((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) / (ρ * (ρ + 1))
    let g := fun ρ : ℂ ↦ (↑((a + b) / 2) : ℂ) ^ ρ / ρ
    |((∑ ρ ∈ zerosUpTo A, (riemannZetaZeroMultiplicity ρ : ℂ) * f ρ) + (∑ ρ ∈ Q, f ρ)).re -
          (b - a) *
            ((∑ ρ ∈ zerosUpTo A, (riemannZetaZeroMultiplicity ρ : ℂ) * g ρ) + (∑ ρ ∈ Q, g ρ)).re| ≤
      ((∑ ρ ∈ zerosUpTo A, (riemannZetaZeroMultiplicity ρ : ℝ) * ‖ρ - 1‖) + (∑ ρ ∈ Q, ‖ρ - 1‖)) *
          a ^ (-(3 / 2 : ℝ)) *
          (b - a) ^ 3 /
        24 := by
  dsimp only
  rw [Complex.add_re, Complex.add_re]
  have hl := (abs_le.mp (zero_head_midpoint_error hRH hA ha hab))
  have hq := (abs_le.mp (selected_midpoint_error hRH hT ha hab Q hQ))
  apply abs_le.mpr
  constructor <;> nlinarith only [hl.1, hl.2, hq.1, hq.2]

/-- Under RH, the backward psi bound is expressed using the signed midpoint
head and selected unit copies. Its error contains the proved reciprocal tail
and the explicit quadrature moment, with no numerical certificate assumptions. -/
theorem psi_selected_midpoint (hRH : RiemannHypothesis) {A T x h : ℝ} (hA : 0 ≤ A) (hAT : A ≤ T)
    (hh : 0 < h) (hx : 1 < x - h) (Q : Finset ℂ) (hQ : Q ⊆ zerosUpTo T)
    (hQA : ∀ ρ ∈ Q, A < |ρ.im|) :
    let g := fun ρ : ℂ ↦ (↑((x - h + x) / 2) : ℂ) ^ ρ / ρ
    let P := ((∑ ρ ∈ zerosUpTo A, (riemannZetaZeroMultiplicity ρ : ℂ) * g ρ) + (∑ ρ ∈ Q, g ρ)).re
    let M := (∑ ρ ∈ zerosUpTo A, (riemannZetaZeroMultiplicity ρ : ℝ) * ‖ρ - 1‖) + (∑ ρ ∈ Q, ‖ρ - 1‖)
    let D := M * (x - h) ^ (-(3 / 2 : ℝ)) * h ^ 3 / 24
    let E :=
      h * (Real.sqrt x * (zeroReciprocalSum T - zeroReciprocalSum A - ∑ ρ ∈ Q, 1 / |ρ.im|)) +
        (x ^ (3 / 2 : ℝ) + (x - h) ^ (3 / 2 : ℝ)) * ordinateTail T +
        1
    x - Chebyshev.psi x ≤ h / 2 + Real.log (2 * Real.pi) + (h * P + D + E) / h := by
  classical
  dsimp only
  have hab : x - h ≤ x := (sub_lt_self x hh).le
  have hm := selected_head_midpoint_error hRH hA (hA.trans hAT) (zero_lt_one.trans hx) hab Q hQ
  dsimp only at hm
  have hw : x - (x - h) = h := by ring
  rw [hw] at hm
  have hp := psi_selected_backward hRH hA hAT hh hx Q hQ hQA
  dsimp only at hp
  have hc := (abs_le.mp hm).2
  apply hp.trans
  apply add_le_add_right
  apply (div_le_div_iff_of_pos_right hh).mpr
  linarith only [hc]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
