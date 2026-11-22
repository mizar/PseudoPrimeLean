/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.SelectedZeroExhaustion
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.TrivialZeroIntegralBound
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.IntegratedChebyshev

/-! # Signed integrated errors with a fixed retained head -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- An eventual finite-kernel bound after subtracting a fixed complex head
passes to the integrated explicit formula. The head stays inside the left-hand
absolute value, preserving its sign for subsequent one-sided estimates. -/
theorem psi1_signed_of_kernel {a b B : ℝ} (ha : 1 < a) (hab : a < b) (H : ℂ)
    (hbound :
      ∀ᶠ m : ℕ in Filter.atTop,
        ‖(∑
                ρ ∈
                  (riemannZetaZerosInAnyRectangle (unifiedRectangleLower m)
                        (unifiedTauRectangleUpper 2 m)).filter
                    (fun ρ ↦ ¬ρ.re < 0),
                (riemannZetaZeroMultiplicity ρ : ℂ) *
                  (((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) / (ρ * (ρ + 1)))) -
              H‖ ≤
          B) :
    |Arithmetic.psiIntegralSum b - Arithmetic.psiIntegralSum a - (b ^ 2 - a ^ 2) / 2 +
          Real.log (2 * Real.pi) * (b - a) +
          H.re| ≤
      B + 1 := by
  classical
  obtain ⟨r, hr, hlim⟩ := psi1_finite_zero_remainder ha hab.le
  have hlim' :=
    (((hlim.sub_const ((b ^ 2 - a ^ 2) / 2)).add_const (Real.log (2 * Real.pi) * (b - a))).add_const
        H.re).abs
  apply le_of_tendsto hlim'
  filter_upwards [hbound] with m hm
  let S :=
    (riemannZetaZerosInAnyRectangle (unifiedRectangleLower m) (unifiedTauRectangleUpper 2 m)).filter
      (fun ρ ↦ ¬ρ.re < 0)
  let f := fun ρ : ℂ ↦
    (riemannZetaZeroMultiplicity ρ : ℂ) * (((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) / (ρ * (ρ + 1)))
  have he :
    (∑ ρ ∈ S,
        -(riemannZetaZeroMultiplicity ρ : ℂ) * ((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) /
          (ρ * (ρ + 1))) =
      -(∑ ρ ∈ S, f ρ) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro ρ hρ
    dsimp only [f]
    ring
  change
    |((b ^ 2 - a ^ 2) / 2 - Real.log (2 * Real.pi) * (b - a) +
              (∑ ρ ∈ S,
                  -(riemannZetaZeroMultiplicity ρ : ℂ) * ((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) /
                    (ρ * (ρ + 1))).re +
              r) -
            (b ^ 2 - a ^ 2) / 2 +
          Real.log (2 * Real.pi) * (b - a) +
          H.re| ≤
      B + 1
  rw [he, Complex.neg_re]
  have halg :
    (b ^ 2 - a ^ 2) / 2 - Real.log (2 * Real.pi) * (b - a) - (∑ ρ ∈ S, f ρ).re + r -
          (b ^ 2 - a ^ 2) / 2 +
        Real.log (2 * Real.pi) * (b - a) +
        H.re =
      -((∑ ρ ∈ S, f ρ) - H).re + r := by
    rw [Complex.sub_re]
    ring
  change ‖(∑ ρ ∈ S, f ρ) - H‖ ≤ B at hm
  change
    |(b ^ 2 - a ^ 2) / 2 - Real.log (2 * Real.pi) * (b - a) - (∑ ρ ∈ S, f ρ).re + r -
            (b ^ 2 - a ^ 2) / 2 +
          Real.log (2 * Real.pi) * (b - a) +
          H.re| ≤
      B + 1
  rw [halg]
  have hb := (Complex.abs_re_le_norm ((∑ ρ ∈ S, f ρ) - H)).trans hm
  have ht := abs_add_le (-((∑ ρ ∈ S, f ρ) - H).re) r
  rw [abs_neg] at ht
  exact ht.trans (add_le_add hb hr)

/-- Under RH, retain the signed low head and one copy of each selected zero
in the integrated explicit formula. The residual budget is proved internally
from reciprocal differences and the actual inverse-square ordinate tail. -/
theorem psi1_selected_signed (hRH : RiemannHypothesis) {A T a b : ℝ} (hA : 0 ≤ A) (hAT : A ≤ T)
    (ha : 1 < a) (hab : a < b) (Q : Finset ℂ) (hQ : Q ⊆ zerosUpTo T) (hQA : ∀ ρ ∈ Q, A < |ρ.im|) :
    let f := fun ρ : ℂ ↦ ((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) / (ρ * (ρ + 1))
    |Arithmetic.psiIntegralSum b - Arithmetic.psiIntegralSum a - (b ^ 2 - a ^ 2) / 2 +
          Real.log (2 * Real.pi) * (b - a) +
          ((∑ ρ ∈ zerosUpTo A, (riemannZetaZeroMultiplicity ρ : ℂ) * f ρ) + (∑ ρ ∈ Q, f ρ)).re| ≤
      (b - a) * (Real.sqrt b * (zeroReciprocalSum T - zeroReciprocalSum A - ∑ ρ ∈ Q, 1 / |ρ.im|)) +
        (b ^ (3 / 2 : ℝ) + a ^ (3 / 2 : ℝ)) * ordinateTail T +
        1 := by
  classical
  dsimp only
  apply psi1_signed_of_kernel ha hab
  have h := selected_kernel_eventually_le hRH hA hAT (zero_lt_one.trans ha) hab Q hQ hQA
  dsimp only at h
  filter_upwards [h] with m hm
  simpa only [sub_add_eq_sub_sub] using hm

/-- A signed backward integrated error implies a one-sided pointwise psi
bound with the signed head retained. Monotonicity of psi supplies the backward
average inequality, avoiding an absolute value on the head contribution. -/
theorem psi_backward_of_signed {x h H E : ℝ} (hh : 0 < h) (hx : 0 < x - h)
    (he :
      |Arithmetic.psiIntegralSum x - Arithmetic.psiIntegralSum (x - h) - (x ^ 2 - (x - h) ^ 2) / 2 +
            Real.log (2 * Real.pi) * h +
            H| ≤
        E) :
    x - Chebyshev.psi x ≤ h / 2 + Real.log (2 * Real.pi) + (H + E) / h := by
  have hm := (Arithmetic.psi1_bounds hx (show x - h ≤ x by linarith only [hh])).2
  have hl := (abs_le.mp he).1
  have hb : (x - Chebyshev.psi x) * h ≤ h ^ 2 / 2 + Real.log (2 * Real.pi) * h + (H + E) := by
    nlinarith only [hm, hl]
  have hr :
    (h / 2 + Real.log (2 * Real.pi) + (H + E) / h) * h =
      h ^ 2 / 2 + Real.log (2 * Real.pi) * h + (H + E) := by
    rw [add_mul, div_mul_cancel₀ _ hh.ne']
    ring
  exact (mul_le_mul_iff_left₀ hh).mp (hb.trans_eq hr.symm)

/-- Under RH, a backward average retains the signed low-zero head and selected
unit copies in a pointwise upper bound for `x-psi x`. The residual budget is
supplied by the proved selected-zero integrated formula. -/
theorem psi_selected_backward (hRH : RiemannHypothesis) {A T x h : ℝ} (hA : 0 ≤ A) (hAT : A ≤ T)
    (hh : 0 < h) (hx : 1 < x - h) (Q : Finset ℂ) (hQ : Q ⊆ zerosUpTo T)
    (hQA : ∀ ρ ∈ Q, A < |ρ.im|) :
    let f := fun ρ : ℂ ↦ ((x : ℂ) ^ (ρ + 1) - ((x - h : ℝ) : ℂ) ^ (ρ + 1)) / (ρ * (ρ + 1))
    let H := ((∑ ρ ∈ zerosUpTo A, (riemannZetaZeroMultiplicity ρ : ℂ) * f ρ) + (∑ ρ ∈ Q, f ρ)).re
    let E :=
      h * (Real.sqrt x * (zeroReciprocalSum T - zeroReciprocalSum A - ∑ ρ ∈ Q, 1 / |ρ.im|)) +
        (x ^ (3 / 2 : ℝ) + (x - h) ^ (3 / 2 : ℝ)) * ordinateTail T +
        1
    x - Chebyshev.psi x ≤ h / 2 + Real.log (2 * Real.pi) + (H + E) / h := by
  classical
  dsimp only
  have hab : x - h < x := sub_lt_self x hh
  have he := psi1_selected_signed hRH hA hAT hx hab Q hQ hQA
  dsimp only at he
  have hw : x - (x - h) = h := by ring
  rw [hw] at he
  exact psi_backward_of_signed hh (zero_lt_one.trans hx) he

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
