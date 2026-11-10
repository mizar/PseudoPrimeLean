/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeightCounting

/-! # Conjugation and positive-height zero counts

Relate the two-sided multiplicity count to the positive-height convention.
-/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Every iterated derivative of the Riemann zeta function commutes with
complex conjugation. Induct using the conjugation rule for derivatives. -/
theorem iterDeriv_conj (n : ℕ) (z : ℂ) :
    iteratedDeriv n riemannZeta ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (iteratedDeriv n riemannZeta z) := by
  induction n generalizing z with
  | zero => simpa only [iteratedDeriv_zero] using riemannZeta_conj z
  | succ n
    ih =>
    have heq :
      (starRingEnd ℂ ∘ iteratedDeriv n riemannZeta ∘ starRingEnd ℂ) =
        iteratedDeriv n riemannZeta := by
      funext w
      simp only [Function.comp_apply, ih, starRingEnd_self_apply]
    have h := congrFun (deriv_conj_conj (f := iteratedDeriv n riemannZeta)) ((starRingEnd ℂ) z)
    rw [heq] at h
    simpa only [iteratedDeriv_succ, Function.comp_apply, starRingEnd_self_apply] using h

/-- Away from the pole at one, the analytic multiplicity of zeta at a point
is unchanged by complex conjugation. Characterize the analytic order by
vanishing of iterated derivatives and use their conjugation symmetry. -/
theorem multiplicity_conj {z : ℂ} (hz : z ≠ 1) :
    riemannZetaZeroMultiplicity ((starRingEnd ℂ) z) = riemannZetaZeroMultiplicity z := by
  have hc : (starRingEnd ℂ) z ≠ 1 := by
    intro h
    have h' := congrArg (starRingEnd ℂ) h
    simp only [starRingEnd_self_apply, map_one] at h'
    exact hz h'
  have hA := analyticOn_riemannZeta z hz
  have hB := analyticOn_riemannZeta ((starRingEnd ℂ) z) hc
  have heq : analyticOrderAt riemannZeta ((starRingEnd ℂ) z) = analyticOrderAt riemannZeta z := by
    apply ENat.eq_of_forall_natCast_le_iff
    intro n
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hB,
      natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hA]
    constructor
    · intro h i hi
      have hh := h i hi
      rw [iterDeriv_conj, map_eq_zero] at hh
      exact hh
    · intro h i hi
      rw [iterDeriv_conj, h i hi, map_zero]
  unfold riemannZetaZeroMultiplicity analyticOrderNatAt
  rw [heq]

/-- Count nontrivial zeta zeros with positive imaginary part and height at
most `T`, weighted by analytic multiplicity. The height endpoint is closed. -/
noncomputable def positiveZeroCount (T : ℝ) : ℝ :=
  ∑ ρ ∈ (zerosUpTo T).filter (fun ρ ↦ 0 < ρ.im), (riemannZetaZeroMultiplicity ρ : ℝ)

/-- Under RH, the two-sided zero count equals twice the positive-height
count. The low-zero exclusion removes real zeros, and conjugation pairs the
two signs while preserving multiplicities. -/
theorem zeroCount_eq_two_positive (hRH : RiemannHypothesis) {T : ℝ} (hT : 0 ≤ T) :
    zeroCount T = 2 * positiveZeroCount T := by
  classical
  rw [zeroCount_eq_sum]
  unfold positiveZeroCount
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not (zerosUpTo T) (fun ρ : ℂ ↦ 0 < ρ.im)
      (fun ρ ↦ (riemannZetaZeroMultiplicity ρ : ℝ))
  rw [← hsplit]
  have heq :
    (∑ ρ ∈ (zerosUpTo T).filter (fun ρ ↦ ¬0 < ρ.im), (riemannZetaZeroMultiplicity ρ : ℝ)) =
      ∑ ρ ∈ (zerosUpTo T).filter (fun ρ ↦ 0 < ρ.im), (riemannZetaZeroMultiplicity ρ : ℝ) := by
    apply Finset.sum_bij (fun ρ _ ↦ (starRingEnd ℂ) ρ)
    · intro ρ hρ
      have hh := Finset.mem_filter.mp hρ
      have hz := (mem_zerosUpTo hT).1 hh.1
      have hgap := zero_height_gt_two_pi hRH hz.1 hz.2.1
      have hneg : ρ.im < 0 := by
        have hp : 0 < 2 * Real.pi := by positivity
        have hnon : ρ.im ≠ 0 := by
          intro he
          rw [he, abs_zero] at hgap
          linarith only [hgap, hp]
        exact lt_of_le_of_ne (le_of_not_gt hh.2) hnon
      apply Finset.mem_filter.mpr
      constructor
      · apply (mem_zerosUpTo hT).2
        refine ⟨?_, ?_, ?_⟩
        · rw [riemannZeta_conj, hz.1, map_zero]
        · simpa only [Complex.conj_re] using hz.2.1
        · simpa only [Complex.conj_im, abs_neg] using hz.2.2
      · simpa only [Complex.conj_im] using neg_pos.mpr hneg
    · intro ρ hρ σ hσ h
      have hh := congrArg (starRingEnd ℂ) h
      simpa only [starRingEnd_self_apply] using hh
    · intro σ hσ
      refine ⟨(starRingEnd ℂ) σ, ?_, ?_⟩
      · have hh := Finset.mem_filter.mp hσ
        have hz := (mem_zerosUpTo hT).1 hh.1
        apply Finset.mem_filter.mpr
        constructor
        · apply (mem_zerosUpTo hT).2
          refine ⟨?_, ?_, ?_⟩
          · rw [riemannZeta_conj, hz.1, map_zero]
          · simpa only [Complex.conj_re] using hz.2.1
          · simpa only [Complex.conj_im, abs_neg] using hz.2.2
        · simp only [Complex.conj_im, not_lt]
          linarith only [hh.2]
      · exact starRingEnd_self_apply σ
    · intro ρ hρ
      have hh := Finset.mem_filter.mp hρ
      have hz := (mem_zerosUpTo hT).1 hh.1
      have hr :=
        RiemannXi.xi_zero_re_eq_half_of_riemannHypothesis hRH
          (RiemannXi.xi_zero_of_zeta_zero_of_re_nonneg hz.1 hz.2.1)
      have hne : ρ ≠ 1 := by
        intro he
        rw [he, Complex.one_re] at hr
        norm_num only at hr
      rw [multiplicity_conj hne]
  rw [heq]
  ring

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
