/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ShiftedPoissonEulerBounds

/-!
# Transfer of signed rational height majorants to completed zero sums

Use nonnegative zero multiplicities and convergent shifted Poisson kernels to transfer
global real height certificates, while retaining signed conductor and Gamma terms.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- The real Poisson height kernel at horizontal distance 1/2+r and height t.
Its value at zero height u is (1/2+r)/((1/2+r)^2+(t-u)^2). It is total for all
real inputs; positive horizontal gap is imposed by the analytic summation results. -/
noncomputable def shiftedPoissonHeightKernel (r t u : ℝ) : ℝ :=
  (1 / 2 + r) / ((1 / 2 + r) ^ 2 + (t - u) ^ 2)

/-- For primitive nonprincipal individual-RH data, each divisor-weighted shifted
Poisson term equals its real height-kernel value. Away from zeros the divisor
vanishes; at zeros RH supplies real part one half. This identifies rational height tests. -/
theorem shifted_poisson_term_eq_height_kernel {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1)
    (r t : ℝ) (ρ : ℂ) :
    (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
        ((1 / 2 + r) / Complex.normSq ((((1 + r : ℝ) : ℂ) + t * Complex.I) - ρ)) =
      (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
        shiftedPoissonHeightKernel r t ρ.im := by
  let D := MeromorphicOn.divisor χ.completedLFunction Set.univ ρ
  by_cases hD : D = 0
  · dsimp only [D] at hD
    simp only [hD, Int.cast_zero, zero_mul]
  · have hr :=
      completedLFunction_zero_re_eq_half_of_dirichletRH hRH hp hinv
        (dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero hne hD)
    have he :
      Complex.normSq ((((1 + r : ℝ) : ℂ) + t * Complex.I) - ρ) =
        (1 / 2 + r) ^ 2 + (t - ρ.im) ^ 2 := by
      rw [Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero,
        Complex.sub_im, Complex.add_im, Complex.mul_im, zero_add, hr]
      ring
    rw [he]
    rfl

/-- For primitive nonprincipal individual-RH data, positive r and any height, the
divisor-weighted Poisson height terms form a summable real series. Transfer the
completed Poisson summability through the critical-line identity. This justifies
finite signed combinations even when some weights are negative. -/
theorem summable_shifted_poisson_height_terms {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {r : ℝ} (hr : 0 < r) (t : ℝ) :
    Summable
      (fun ρ : ℂ ↦
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          shiftedPoissonHeightKernel r t ρ.im) := by
  have hs :=
    summable_completed_poisson_terms hq hRH hp hne hinv (s := (((1 + r : ℝ) : ℂ) + t * Complex.I))
      (by
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero]
        linarith only [hr])
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero,
    show 1 + r - 1 / 2 = 1 / 2 + r by ring] at hs
  exact hs.congr (shifted_poisson_term_eq_height_kernel hRH hp hne hinv r t)

/-- For primitive nonprincipal individual-RH data, the shifted completed Poisson
sum equals the divisor-weighted rational height-kernel sum. Use termwise critical-line
identification. This connects an elementary rational function certificate to actual zeros. -/
theorem shiftedCompletedPoissonSum_eq_height_sum {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1)
    (r t : ℝ) :
    shiftedCompletedPoissonSum χ r t =
      ∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          shiftedPoissonHeightKernel r t ρ.im := by
  unfold shiftedCompletedPoissonSum
  exact tsum_congr (shifted_poisson_term_eq_height_kernel hRH hp hne hinv r t)

/-- For primitive nonprincipal individual-RH data, a summable divisor-weighted
height test bounded at every real height by a finite signed combination of positive-gap
Poisson kernels has zero sum at most that combination of actual Poisson sums.
Multiplicity is nonnegative; exchange the finite sum with the convergent series.
The pointwise certificate remains an explicit assumption. -/
theorem zero_height_sum_le_shifted_poisson_majorant {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {ι : Type*} (S : Finset ι) (r t w : ι → ℝ)
    (hr : ∀ i ∈ S, 0 < r i) (g : ℝ → ℝ)
    (hg : ∀ u, g u ≤ ∑ i ∈ S, w i * shiftedPoissonHeightKernel (r i) (t i) u)
    (hs :
      Summable (fun ρ : ℂ ↦ (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * g ρ.im)) :
    (∑' ρ : ℂ, (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * g ρ.im) ≤
      ∑ i ∈ S, w i * shiftedCompletedPoissonSum χ (r i) (t i) := by
  let F := fun i ρ ↦
    w i *
      ((MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
        shiftedPoissonHeightKernel (r i) (t i) ρ.im)
  have hf (i : ι) (hi : i ∈ S) : Summable (F i) :=
    (summable_shifted_poisson_height_terms hq hRH hp hne hinv (hr i hi) (t i)).mul_left (w i)
  have hsum : Summable (fun ρ : ℂ ↦ ∑ i ∈ S, F i ρ) :=
    (hasSum_sum (fun i hi ↦ (hf i hi).hasSum)).summable
  have hb (ρ : ℂ) :
    (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * g ρ.im ≤ ∑ i ∈ S, F i ρ := by
    have ha : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := fun z _ ↦
      (DirichletCharacter.differentiable_completedLFunction hne).analyticAt z
    have hn : (0 : ℝ) ≤ MeromorphicOn.divisor χ.completedLFunction Set.univ ρ := by
      exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg ha ρ
    have h := mul_le_mul_of_nonneg_left (hg ρ.im) hn
    rw [Finset.mul_sum] at h
    simpa only [F, mul_assoc, mul_comm, mul_left_comm] using h
  have h := Summable.tsum_le_tsum hb hs hsum
  rw [Summable.tsum_finsetSum hf] at h
  simp only [F, tsum_mul_left] at h
  rw [Finset.sum_congr rfl
      (fun i _ ↦
        congrArg (fun z : ℝ ↦ w i * z)
          (shiftedCompletedPoissonSum_eq_height_sum hRH hp hne hinv (r i) (t i)).symm)] at h
  exact h

/-- Under the same pointwise certificate and convergence assumptions, bound the
height-test zero sum by half the signed weight sum times log q, the exact signed
Gamma combination and absolute-weighted Euler ratios. Apply the height majorant
and centered Poisson error theorem. This separates the certificate and its analytic cost. -/
theorem zero_height_sum_le_shifted_poisson_budget {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {ι : Type*} (S : Finset ι) (r t w : ι → ℝ)
    (hr : ∀ i ∈ S, 0 < r i) (g : ℝ → ℝ)
    (hg : ∀ u, g u ≤ ∑ i ∈ S, w i * shiftedPoissonHeightKernel (r i) (t i) u)
    (hs :
      Summable (fun ρ : ℂ ↦ (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * g ρ.im)) :
    (∑' ρ : ℂ, (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * g ρ.im) ≤
      (∑ i ∈ S, w i) * (Real.log q / 2) +
        (∑ i ∈ S, w i * (logDeriv χ.gammaFactor ((((1 + r i : ℝ) : ℂ) + t i * Complex.I))).re) +
        ∑ i ∈ S, |w i| * (((r i)⁻¹ ^ 2 + (r i + 1)⁻¹) / (1 + (2 : ℝ) ^ (-r i) / r i)) := by
  have hc := zero_height_sum_le_shifted_poisson_majorant hq hRH hp hne hinv S r t w hr g hg hs
  have he := shifted_poisson_signed_combination_error_le hq hRH hp hne hinv S r t w hr
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul] at he
  have hu := (abs_le.mp he).2
  linarith only [hc, hu]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
