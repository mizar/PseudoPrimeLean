/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannXi.Conjugation

/-! # Critical-line zeros from sign changes of the xi function -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannXi

/-- The Riemann xi function is real at every point on the critical line.
Conjugation and the functional equation both map the value to the value at
`1 - s`, so the value is fixed by conjugation. -/
theorem riemannXi_critical_im_eq_zero {s : ℂ} (hs : s.re = 1 / 2) : (riemannXi s).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  rw [← riemannXi_conj, ← riemannXi_one_sub s]
  congr 1
  apply Complex.ext
  · simp only [Complex.conj_re, Complex.sub_re, Complex.one_re]
    linarith only [hs]
  · simp only [Complex.conj_im, Complex.sub_im, Complex.one_im, zero_sub]

/-- On the critical line, a zero of xi is a zero of zeta. The real part
excludes the pole and the negative even integers, so the xi-zeta factor is
nonzero. -/
theorem riemannZeta_zero_of_critical_xi_zero {s : ℂ} (hs : s.re = 1 / 2) (hz : riemannXi s = 0) :
    riemannZeta s = 0 := by
  have hs1 : s ≠ 1 := by
    intro he
    rw [he, Complex.one_re] at hs
    norm_num only at hs
  have hnt : ∀ n : ℕ, s ≠ -2 * (n + 1) := by
    intro n he
    rw [he] at hs
    simp only [Complex.neg_re, Complex.mul_re, Complex.re_ofNat, Complex.add_re, Complex.one_re,
      Complex.add_im, Complex.one_im, Complex.natCast_re, Complex.natCast_im] at hs
    nlinarith only [hs, Nat.cast_nonneg (α := ℝ) n]
  exact (riemannXi_eq_zero_iff_of_denom_ne_zero hs1 (riemannZetaDenom_ne_zero hnt)).1 hz

/-- If the real xi values at two ordered critical-line ordinates have opposite
strict signs, xi has a zero in the open interval. Continuity gives a real-part
zero, and critical-line reality supplies the imaginary part. -/
theorem exists_critical_xi_zero_of_sign {a b : ℝ} (hab : a < b)
    (hsign :
      let f := fun t : ℝ ↦ (riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re
      (f a < 0 ∧ 0 < f b) ∨ (f b < 0 ∧ 0 < f a)) :
    ∃ t ∈ Set.Ioo a b, riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) = 0 := by
  let f : ℝ → ℝ := fun t ↦ (riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re
  have hz : Continuous (fun t : ℝ ↦ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hf : Continuous f := Complex.continuous_re.comp (differentiable_riemannXi.continuous.comp hz)
  have hex : ∃ t ∈ Set.Ioo a b, f t = 0 := by
    rcases hsign with h | h
    · exact intermediate_value_Ioo hab.le hf.continuousOn h
    · exact intermediate_value_Ioo' hab.le hf.continuousOn h
  obtain ⟨t, ht, hzero⟩ := hex
  refine ⟨t, ht, ?_⟩
  apply Complex.ext
  · simpa only [Complex.zero_re, f] using hzero
  · have hs : (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I).re = 1 / 2 := by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    simpa only [Complex.zero_im] using riemannXi_critical_im_eq_zero hs

/-- If xi changes sign between two ordered critical-line ordinates, zeta has
a zero at a critical-line point with ordinate in the open interval. This
connects independently certified endpoint signs to zero existence. -/
theorem exists_critical_zeta_zero_of_sign {a b : ℝ} (hab : a < b)
    (hsign :
      let f := fun t : ℝ ↦ (riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re
      (f a < 0 ∧ 0 < f b) ∨ (f b < 0 ∧ 0 < f a)) :
    ∃ t ∈ Set.Ioo a b, riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) = 0 := by
  obtain ⟨t, ht, hz⟩ := exists_critical_xi_zero_of_sign hab hsign
  refine ⟨t, ht, ?_⟩
  apply riemannZeta_zero_of_critical_xi_zero ?_ hz
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]

/-- Opposite xi signs on each of finitely many ordered disjoint intervals
give a strictly increasing family of critical-line zeta-zero ordinates.
The intermediate value theorem supplies each entry independently. -/
theorem critical_zeros_of_sign_intervals {n : ℕ} (a b : Fin n → ℝ) (hab : ∀ i, a i < b i)
    (hsep : ∀ i j, i < j → b i ≤ a j)
    (hsign :
      ∀ i,
        let f := fun t : ℝ ↦ (riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re
        (f (a i) < 0 ∧ 0 < f (b i)) ∨ (f (b i) < 0 ∧ 0 < f (a i))) :
    ∃ g : Fin n → ℝ,
      StrictMono g ∧
        (∀ i, a i < g i ∧ g i < b i) ∧
        ∀ i, riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 0 := by
  have hex :
    ∀ i,
      ∃ t : ℝ, (a i < t ∧ t < b i) ∧ riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) = 0 := by
    intro i
    exact exists_critical_zeta_zero_of_sign (hab i) (hsign i)
  choose g hg using hex
  refine ⟨g, ?_, (fun i ↦ (hg i).1), (fun i ↦ (hg i).2)⟩
  intro i j hij
  exact ((hg i).1.2.trans_le (hsep i j hij)).trans (hg j).1.1

end PseudoPrime.AnalyticNumberTheory.RiemannXi
