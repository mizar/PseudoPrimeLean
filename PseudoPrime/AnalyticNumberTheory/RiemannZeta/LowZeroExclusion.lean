/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.FiniteZeroSums
import PseudoPrime.AnalyticNumberTheory.RiemannXi.ZeroMassBounds

/-! # Low-height zero exclusion under RH

Exclude low nontrivial zeta zeros using the existing inverse-square zero mass.
-/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH, a nontrivial zeta zero has squared norm at least 20. Apply
the finite inverse-square zero-mass bound to the singleton containing it and
use positivity of its multiplicity. -/
theorem zero_norm_ge20 (hRH : RiemannHypothesis) {ρ : ℂ} (hz : riemannZeta ρ = 0) (hre : 0 ≤ ρ.re) :
    20 ≤ Complex.normSq ρ := by
  have hxi := RiemannXi.xi_zero_of_zeta_zero_of_re_nonneg hz hre
  have hr := RiemannXi.xi_zero_re_eq_half_of_riemannHypothesis hRH hxi
  have hn1 : ρ ≠ 1 := by
    intro he
    rw [he] at hr
    norm_num only [Complex.one_re] at hr
  have hm : (1 : ℝ) ≤ riemannZetaZeroMultiplicity ρ := by
    exact_mod_cast riemannZetaZeroMultiplicity_pos hn1 hz
  have hS :=
    sum_zetaZeroMultiplicity_invNormSq_le hRH {ρ}
      (by
        intro z h
        have he := Finset.mem_singleton.mp h
        subst z
        exact hz)
      (by
        intro z h
        have he := Finset.mem_singleton.mp h
        subst z
        exact hre)
  simp only [Finset.sum_singleton] at hS
  have hmass := RiemannXi.riemannZeroMass_le_one_fortieth
  have hnpos : 0 < Complex.normSq ρ := by
    have hne : ρ ≠ 0 := by
      intro he
      rw [he, Complex.zero_re] at hr
      norm_num only at hr
    exact Complex.normSq_pos.mpr hne
  have hbound : (riemannZetaZeroMultiplicity ρ : ℝ) / Complex.normSq ρ ≤ 1 / 20 := by
    linarith only [hS, hmass]
  have hdiv := (div_le_iff₀ hnpos).mp hbound
  nlinarith only [hdiv, hm]

/-- Under RH, every zeta zero of nonnegative real part has imaginary part
of absolute value greater than `2π`. The zero and its distinct conjugate
would otherwise contribute too much to the finite inverse-square mass. -/
theorem zero_height_gt_two_pi (hRH : RiemannHypothesis) {ρ : ℂ} (hz : riemannZeta ρ = 0)
    (hre : 0 ≤ ρ.re) : 2 * Real.pi < |ρ.im| := by
  classical
  have hxi := RiemannXi.xi_zero_of_zeta_zero_of_re_nonneg hz hre
  have hr := RiemannXi.xi_zero_re_eq_half_of_riemannHypothesis hRH hxi
  have hn := zero_norm_ge20 hRH hz hre
  have him : ρ.im ≠ 0 := by
    intro h
    rw [Complex.normSq_apply, hr, h] at hn
    norm_num only at hn
  have hneq : ρ ≠ (starRingEnd ℂ) ρ := by
    intro h
    have h' := congrArg Complex.im h
    rw [Complex.conj_im] at h'
    exact him (by linarith only [h'])
  have hzc : riemannZeta ((starRingEnd ℂ) ρ) = 0 := by rw [riemannZeta_conj, hz, map_zero]
  have hrc : 0 ≤ ((starRingEnd ℂ) ρ).re := by simpa only [Complex.conj_re] using hre
  have hn1 : ρ ≠ 1 := by
    intro he
    rw [he, Complex.one_re] at hr
    norm_num only at hr
  have hnc1 : (starRingEnd ℂ) ρ ≠ 1 := by
    intro he
    have hh := congrArg Complex.re he
    simp only [Complex.conj_re, Complex.one_re] at hh
    linarith only [hh, hr]
  have hm : (1 : ℝ) ≤ riemannZetaZeroMultiplicity ρ := by
    exact_mod_cast riemannZetaZeroMultiplicity_pos hn1 hz
  have hmc : (1 : ℝ) ≤ riemannZetaZeroMultiplicity ((starRingEnd ℂ) ρ) := by
    exact_mod_cast riemannZetaZeroMultiplicity_pos hnc1 hzc
  have hS :=
    sum_zetaZeroMultiplicity_invNormSq_le hRH {ρ, (starRingEnd ℂ) ρ}
      (by
        intro z h
        have hh := Finset.mem_insert.mp h
        rcases hh with he | he
        · subst z
          exact hz
        · have he' := Finset.mem_singleton.mp he
          subst z
          exact hzc)
      (by
        intro z h
        have hh := Finset.mem_insert.mp h
        rcases hh with he | he
        · subst z
          exact hre
        · have he' := Finset.mem_singleton.mp he
          subst z
          exact hrc)
  rw [Finset.sum_pair hneq, Complex.normSq_conj] at hS
  have hmass := RiemannXi.riemannZeroMass_le_one_fortieth
  have hnpos : 0 < Complex.normSq ρ := by linarith only [hn]
  have hs :
    (riemannZetaZeroMultiplicity ρ : ℝ) / Complex.normSq ρ +
        (riemannZetaZeroMultiplicity ((starRingEnd ℂ) ρ) : ℝ) / Complex.normSq ρ ≤
      1 / 20 := by
    linarith only [hS, hmass]
  rw [← add_div] at hs
  have hd := (div_le_iff₀ hnpos).mp hs
  have hnorm : 40 ≤ Complex.normSq ρ := by nlinarith only [hd, hm, hmc]
  by_contra hh
  have hb : |ρ.im| ≤ 2 * Real.pi := le_of_not_gt hh
  have hpi : Real.pi < (31416 / 10000 : ℝ) := by
    have h := Real.pi_lt_d4
    norm_num only at h ⊢
    exact h
  have himlo := (abs_le.mp hb).1
  have himhi := (abs_le.mp hb).2
  rw [Complex.normSq_apply, hr] at hnorm
  nlinarith only [hnorm, hpi, Real.pi_pos, himlo, himhi, sq_nonneg (2 * (31416 / 10000 : ℝ) - ρ.im),
    sq_nonneg (2 * (31416 / 10000 : ℝ) + ρ.im)]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
