/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.IntegratedLowZeroBound
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCounting

/-! # Unit-weight bounds for selected zeta zeros -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH, one copy of a nontrivial zeta zero satisfies the integrated
low-zero estimate. Cancel its positive multiplicity from the existing bound;
this permits subtracting selected copies without assuming simplicity. -/
theorem low_unit_term (hRH : RiemannHypothesis) {ρ : ℂ} (hz : riemannZeta ρ = 0) (hre : 0 ≤ ρ.re)
    (hρ : ρ ≠ 1) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ‖((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) / (ρ * (ρ + 1))‖ / (b - a) ≤ Real.sqrt b / |ρ.im| := by
  have hm : (0 : ℝ) < riemannZetaZeroMultiplicity ρ := by
    exact_mod_cast riemannZetaZeroMultiplicity_pos hρ hz
  have h := low_term hRH hz hre ha hab
  rw [mul_div_assoc, norm_mul, Complex.norm_natCast, mul_div_assoc, mul_div_assoc] at h
  exact (mul_le_mul_iff_right₀ hm).mp h

/-- Any nonnegative real weight may replace the actual multiplicity in the
integrated low-zero estimate. Multiply the unit-copy bound by the weight;
selected-zero residual weights are an intended application. -/
theorem low_weighted_term (hRH : RiemannHypothesis) {ρ : ℂ} (hz : riemannZeta ρ = 0)
    (hre : 0 ≤ ρ.re) (hρ : ρ ≠ 1) {a b w : ℝ} (ha : 0 < a) (hab : a < b) (hw : 0 ≤ w) :
    ‖(w : ℂ) * (((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) / (ρ * (ρ + 1)))‖ / (b - a) ≤
      w * (Real.sqrt b / |ρ.im|) := by
  have h := mul_le_mul_of_nonneg_left (low_unit_term hRH hz hre hρ ha hab) hw
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw, mul_div_assoc] using
    h

/-- Nonnegative weights on a finite set of nontrivial zeros satisfy the
integrated low-zero sum bound. Combine the unit-copy estimate with the triangle
inequality; residual multiplicities are permitted. -/
theorem low_weighted_sum (hRH : RiemannHypothesis) (S : Finset ℂ) (w : ℂ → ℝ)
    (hz : ∀ ρ ∈ S, riemannZeta ρ = 0) (hre : ∀ ρ ∈ S, 0 ≤ ρ.re) (hρ : ∀ ρ ∈ S, ρ ≠ 1)
    (hw : ∀ ρ ∈ S, 0 ≤ w ρ) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ‖∑ ρ ∈ S, (w ρ : ℂ) * (((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) / (ρ * (ρ + 1)))‖ / (b - a) ≤
      Real.sqrt b * ∑ ρ ∈ S, w ρ / |ρ.im| := by
  have htri :=
    div_le_div_of_nonneg_right
      (norm_sum_le S
        (fun ρ ↦ (w ρ : ℂ) * (((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) / (ρ * (ρ + 1)))))
      (sub_nonneg.mpr hab.le)
  rw [Finset.sum_div] at htri
  have hs :=
    Finset.sum_le_sum
      (fun ρ hρS ↦ low_weighted_term hRH (hz ρ hρS) (hre ρ hρS) (hρ ρ hρS) ha hab (hw ρ hρS))
  have he : (∑ ρ ∈ S, w ρ * (Real.sqrt b / |ρ.im|)) = Real.sqrt b * ∑ ρ ∈ S, w ρ / |ρ.im| := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ρ hρS
    ring
  exact (htri.trans hs).trans_eq he

/-- Removing one copy at selected zeros leaves nonnegative real multiplicity.
Only positivity of the actual multiplicity is needed, not simplicity. -/
theorem selected_weight_nonneg (Q : Finset ℂ) (hz : ∀ ρ ∈ Q, riemannZeta ρ = 0)
    (hρ : ∀ ρ ∈ Q, ρ ≠ 1) (ρ : ℂ) :
    0 ≤ (riemannZetaZeroMultiplicity ρ : ℝ) - (if ρ ∈ Q then 1 else 0) := by
  classical
  by_cases hmem : ρ ∈ Q
  · rw [ite_eq_left hmem]
    have hm : (1 : ℝ) ≤ riemannZetaZeroMultiplicity ρ := by
      exact_mod_cast riemannZetaZeroMultiplicity_pos (hρ ρ hmem) (hz ρ hmem)
    exact sub_nonneg.mpr hm
  · rw [ite_eq_right hmem, sub_zero]
    exact Nat.cast_nonneg _

/-- A selected-copy indicator sum over a containing finite set equals the
unweighted sum over the selected points. Terms outside the selection vanish. -/
theorem selected_indicator_sum (S Q : Finset ℂ) (hQS : Q ⊆ S) (f : ℂ → ℂ) :
    (∑ ρ ∈ S, (if ρ ∈ Q then (1 : ℂ) else 0) * f ρ) = ∑ ρ ∈ Q, f ρ := by
  classical
  have h :=
    Finset.sum_subset hQS (f := fun ρ ↦ (if ρ ∈ Q then (1 : ℂ) else 0) * f ρ)
      (fun ρ hρ hnot ↦ by rw [ite_eq_right hnot, zero_mul])
  rw [← h]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [ite_eq_left hρ, one_mul]

/-- A multiplicity-weighted finite sum splits exactly into one selected copy
and the residual real weights. This algebraic identity does not assume simplicity. -/
theorem selected_copy_sum (S Q : Finset ℂ) (hQS : Q ⊆ S) (f : ℂ → ℂ) :
    (∑ ρ ∈ S, (riemannZetaZeroMultiplicity ρ : ℂ) * f ρ) =
      (∑ ρ ∈ Q, f ρ) +
        ∑ ρ ∈ S,
          (((riemannZetaZeroMultiplicity ρ : ℝ) - (if ρ ∈ Q then 1 else 0) : ℝ) : ℂ) * f ρ := by
  classical
  rw [← selected_indicator_sum S Q hQS f, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ρ hρ
  by_cases hmem : ρ ∈ Q
  · simp only [ite_eq_left hmem, Complex.ofReal_sub, Complex.ofReal_natCast, Complex.ofReal_one]
    ring
  · simp only [ite_eq_right hmem, Complex.ofReal_sub, Complex.ofReal_natCast, Complex.ofReal_zero]
    ring

/-- A selected real indicator divided by any height function sums to the
reciprocal sum on the selected subset. Outside that subset its terms vanish. -/
theorem selected_reciprocal_indicator (S Q : Finset ℂ) (hQS : Q ⊆ S) (v : ℂ → ℝ) :
    (∑ ρ ∈ S, (if ρ ∈ Q then (1 : ℝ) else 0) / v ρ) = ∑ ρ ∈ Q, 1 / v ρ := by
  classical
  have h :=
    Finset.sum_subset hQS (f := fun ρ ↦ (if ρ ∈ Q then (1 : ℝ) else 0) / v ρ)
      (fun ρ hρ hnot ↦ by rw [ite_eq_right hnot, zero_div])
  rw [← h]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [ite_eq_left hρ]

/-- Residual reciprocal weights equal the full weighted reciprocal sum minus
one reciprocal per selected point. This justifies subtracting selected copies
before estimating the nonnegative remainder. -/
theorem selected_reciprocal_eq (S Q : Finset ℂ) (hQS : Q ⊆ S) (m v : ℂ → ℝ) :
    (∑ ρ ∈ S, (m ρ - (if ρ ∈ Q then 1 else 0)) / v ρ) =
      (∑ ρ ∈ S, m ρ / v ρ) - ∑ ρ ∈ Q, 1 / v ρ := by
  classical
  simp only [sub_div, Finset.sum_sub_distrib]
  rw [selected_reciprocal_indicator S Q hQS v]

/-- A subset's nonnegative residual reciprocal sum is bounded by the complete
finite residual sum, expressed as a full sum minus selected unit copies. -/
theorem selected_reciprocal_le (M S Q : Finset ℂ) (hMS : M ⊆ S) (hQS : Q ⊆ S) (m v : ℂ → ℝ)
    (hw : ∀ ρ ∈ S, 0 ≤ m ρ - (if ρ ∈ Q then 1 else 0)) (hv : ∀ ρ ∈ S, 0 ≤ v ρ) :
    (∑ ρ ∈ M, (m ρ - (if ρ ∈ Q then 1 else 0)) / v ρ) ≤
      (∑ ρ ∈ S, m ρ / v ρ) - ∑ ρ ∈ Q, 1 / v ρ := by
  classical
  rw [← selected_reciprocal_eq S Q hQS m v]
  apply Finset.sum_le_sum_of_subset_of_nonneg hMS
  intro ρ hρ hnot
  exact div_nonneg (hw ρ hρ) (hv ρ hρ)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
