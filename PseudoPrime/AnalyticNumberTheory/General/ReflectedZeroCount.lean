/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.EndpointRegularization
public import PseudoPrime.AnalyticNumberTheory.General.FunctionalEquationZeros

/-!
# Reflected resolvent mass and local zero counts

A conjugate functional equation cancels the centered Hadamard constant.
The resulting nonnegative zero mass controls multiplicity in unit height
windows before any estimate involving a conductor is imposed.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- For an entire F of subquadratic exponential growth, nonzero at zero and at
both reflected points, a conjugate functional equation identifies twice the
real logarithmic derivative with the reflected resolvent series. Subtract the
centered Hadamard identities and take real parts of the absolutely convergent
series. This avoids a separate identity for the Hadamard center constant. -/
theorem two_re_logDeriv_eq_reflectedResolventSum {F : ℂ → ℂ} {ε : ℂ} (hε : ε ≠ 0)
    (hfe : ∀ z, F z = ε * star (F (1 - star z))) (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) {C r : ℝ}
    (hC : 0 < C) (hr0 : 0 ≤ r) (hr2 : r < 2) (hg : ∀ z : ℂ, ‖F z‖ ≤ Real.exp (C * (‖z‖ + 1) ^ r))
    {s : ℂ} (hs : F s ≠ 0) (ht : F (1 - star s) ≠ 0) :
    2 * (logDeriv F s).re =
      ∑' ρ : ℂ, ((analyticOrderNatAt F ρ : ℂ) * (1 / (s - ρ) - 1 / (1 - star s - ρ))).re := by
  have hgs := summable_genusTerms_of_entireGrowth hF h0 hC hr0 hr2 hg s
  have hgt := summable_genusTerms_of_entireGrowth hF h0 hC hr0 hr2 hg (1 - star s)
  have hd :
    Summable (fun ρ : ℂ ↦ (analyticOrderNatAt F ρ : ℂ) * (1 / (s - ρ) - 1 / (1 - star s - ρ))) :=
    (hgs.sub hgt).congr (fun ρ ↦ by ring)
  have hs' := centered_logDeriv_eq_genusSum hF h0 hC hr0 hr2 hg hs hgs
  have ht' := centered_logDeriv_eq_genusSum hF h0 hC hr0 hr2 hg ht hgt
  have he :
    logDeriv F s - logDeriv F (1 - star s) =
      ∑' ρ : ℂ, (analyticOrderNatAt F ρ : ℂ) * (1 / (s - ρ) - 1 / (1 - star s - ρ)) := by
    calc
      _ = (logDeriv F s - logDeriv F 0) - (logDeriv F (1 - star s) - logDeriv F 0) := by ring
      _ = _ := by
        rw [hs', ht', ← hgs.tsum_sub hgt]
        exact tsum_congr (fun ρ ↦ by ring)
  have hre := logDeriv_eq_neg_conjugateReflection hε hfe (hF (1 - star s))
  have hr := congrArg Complex.re hre
  simp only [Complex.neg_re, Complex.star_def, Complex.conj_re] at hr
  change (logDeriv F s).re = -(logDeriv F (1 - star s)).re at hr
  have hz := congrArg Complex.re he
  rw [Complex.sub_re] at hz
  have hm := Complex.reCLM.map_tsum hd
  change
    (∑' ρ : ℂ, (analyticOrderNatAt F ρ : ℂ) * (1 / (s - ρ) - 1 / (1 - star s - ρ))).re =
      ∑' ρ : ℂ, ((analyticOrderNatAt F ρ : ℂ) * (1 / (s - ρ) - 1 / (1 - star s - ρ))).re at hm
  linarith only [hr, hz, hm]

/-- The real part of the resolvent on the vertical line Re s=a is the Poisson
fraction (a-Re rho)/((a-Re rho)^2+(T-Im rho)^2). Expand the complex inverse
using its norm square. This gives positivity and local lower bounds for
critical-strip zeros. -/
theorem resolvent_re (a T : ℝ) (ρ : ℂ) :
    (1 / ((a : ℂ) + T * Complex.I - ρ)).re = (a - ρ.re) / ((a - ρ.re) ^ 2 + (T - ρ.im) ^ 2) := by
  simp only [one_div, Complex.inv_re, Complex.normSq_apply, Complex.sub_re, Complex.add_re,
    Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
    mul_one, sub_zero, add_zero, Complex.sub_im, Complex.add_im, Complex.mul_im, zero_add]
  ring

/-- If Re rho<=1 and a>=1, the real part of the vertical resolvent is nonnegative.
The explicit Poisson fraction has a nonnegative numerator and denominator.
This supplies positivity on the right boundary of the zero strip. -/
theorem strip_resolvent_re_nonneg {a T : ℝ} {ρ : ℂ} (ha : 1 ≤ a) (hρ : ρ.re ≤ 1) :
    0 ≤ (1 / ((a : ℂ) + T * Complex.I - ρ)).re := by
  rw [resolvent_re]
  exact div_nonneg (sub_nonneg.mpr (hρ.trans ha)) (add_nonneg (sq_nonneg _) (sq_nonneg _))

/-- For 0<=Re rho<=1 and |T-Im rho|<=1, the resolvent at 3+iT has real part
at least 1/5. Bound the denominator using the unit height window and the
critical strip. This turns a resolvent mass bound into a local zero count. -/
theorem strip_resolvent_re_lower {T : ℝ} {ρ : ℂ} (hlo : 0 ≤ ρ.re) (hhi : ρ.re ≤ 1)
    (hnear : |T - ρ.im| ≤ 1) : (1 / 5 : ℝ) ≤ (1 / ((3 : ℝ) + T * Complex.I - ρ)).re := by
  rw [resolvent_re]
  have hpos : 0 < (3 - ρ.re) ^ 2 + (T - ρ.im) ^ 2 := by nlinarith only [hhi, sq_nonneg (T - ρ.im)]
  rw [le_div_iff₀ hpos]
  have hsq : (T - ρ.im) ^ 2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using (sq_le_sq₀ (abs_nonneg _) zero_le_one).mpr hnear
  nlinarith only [hlo, hhi, hsq, sq_nonneg (ρ.re - 1)]

/-- If Re rho>=0 and a<=0, the real part of the vertical resolvent is nonpositive.
Its numerator is nonpositive and denominator nonnegative. This controls the
left contribution in the reflected resolvent difference. -/
theorem strip_resolvent_re_nonpos {a T : ℝ} {ρ : ℂ} (ha : a ≤ 0) (hρ : 0 ≤ ρ.re) :
    (1 / ((a : ℂ) + T * Complex.I - ρ)).re ≤ 0 := by
  rw [resolvent_re]
  exact
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (ha.trans hρ))
      (add_nonneg (sq_nonneg _) (sq_nonneg _))

/-- The real part of the difference of resolvents at 3+iT and -2+iT.
The height T is real and rho is a complex zero location. On the closed
critical strip the difference is nonnegative, allowing its total mass to
control local zero multiplicities without a Riemann hypothesis. -/
noncomputable def stripResolventPair (T : ℝ) (ρ : ℂ) : ℝ :=
  (1 / (((3 : ℝ) : ℂ) + T * Complex.I - ρ) - 1 / (((-2 : ℝ) : ℂ) + T * Complex.I - ρ)).re

/-- For a zero location in the closed critical strip, the reflected resolvent
pair is nonnegative. Combine right positivity and left negativity.
This permits comparison of finite local sums with the full zero series. -/
theorem stripResolventPair_nonneg {T : ℝ} {ρ : ℂ} (hlo : 0 ≤ ρ.re) (hhi : ρ.re ≤ 1) :
    0 ≤ stripResolventPair T ρ := by
  rw [stripResolventPair, Complex.sub_re]
  exact
    sub_nonneg.mpr
      ((strip_resolvent_re_nonpos (a := -2) (by norm_num only) hlo).trans
        (strip_resolvent_re_nonneg (a := 3) (by norm_num only) hhi))

/-- A critical-strip location within unit distance in height of T contributes
at least 1/5 to the reflected resolvent pair. The right resolvent already
has this lower bound and subtracting the left one only increases it.
This is the pointwise local-count comparison. -/
theorem stripResolventPair_lower {T : ℝ} {ρ : ℂ} (hlo : 0 ≤ ρ.re) (hhi : ρ.re ≤ 1)
    (hnear : |T - ρ.im| ≤ 1) : (1 / 5 : ℝ) ≤ stripResolventPair T ρ := by
  rw [stripResolventPair, Complex.sub_re]
  have hl := strip_resolvent_re_lower hlo hhi hnear
  have hn := strip_resolvent_re_nonpos (a := -2) (T := T) (by norm_num only) hlo
  linarith only [hl, hn]

/-- Conjugate reflection sends 3+iT to -2+iT. Verify its real and imaginary
parts directly. This identifies the two vertical lines in the reflected
Hadamard formula. -/
theorem reflection_at_three (T : ℝ) :
    1 - star (((3 : ℝ) : ℂ) + T * Complex.I) = ((-2 : ℝ) : ℂ) + T * Complex.I := by
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.one_re, Complex.star_def, Complex.conj_re, Complex.add_re,
      Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero]
    norm_num only
  · simp only [Complex.sub_im, Complex.one_im, Complex.star_def, Complex.conj_im, Complex.add_im,
      Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one,
      mul_zero, add_zero, zero_add, sub_neg_eq_add]

/-- For entire F nonzero at zero with subquadratic exponential growth, the
multiplicity-weighted reflected resolvent pair is absolutely summable at
every real height T. Subtract two convergent genus-one series and take real
parts. This justifies total-mass comparisons. -/
theorem summable_stripResolventPair {F : ℂ → ℂ} (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) {C r : ℝ}
    (hC : 0 < C) (hr0 : 0 ≤ r) (hr2 : r < 2) (hg : ∀ z : ℂ, ‖F z‖ ≤ Real.exp (C * (‖z‖ + 1) ^ r))
    (T : ℝ) : Summable (fun ρ : ℂ ↦ (analyticOrderNatAt F ρ : ℝ) * stripResolventPair T ρ) := by
  have hs := summable_genusTerms_of_entireGrowth hF h0 hC hr0 hr2 hg (((3 : ℝ) : ℂ) + T * Complex.I)
  have ht :=
    summable_genusTerms_of_entireGrowth hF h0 hC hr0 hr2 hg (((-2 : ℝ) : ℂ) + T * Complex.I)
  have hd :
    Summable
      (fun ρ : ℂ ↦
        (analyticOrderNatAt F ρ : ℂ) *
          (1 / (((3 : ℝ) : ℂ) + T * Complex.I - ρ) - 1 / (((-2 : ℝ) : ℂ) + T * Complex.I - ρ))) :=
    (hs.sub ht).congr (fun ρ ↦ by ring)
  exact
    (Complex.reCLM.summable hd).congr
      (fun ρ ↦ by
        simp only [Complex.reCLM_apply, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
          zero_mul, sub_zero, stripResolventPair])

/-- For an entire F satisfying the conjugate functional equation and the
subquadratic growth bound, nonvanishing at 3+iT identifies the reflected
zero mass with twice Re(logDeriv F(3+iT)). Reflect nonvanishing, apply the
centered two-point identity, and move natural multiplicities outside real
parts. This is the total-mass identity for local zero counts. -/
theorem tsum_stripResolventPair_eq {F : ℂ → ℂ} {ε : ℂ} (hε : ε ≠ 0)
    (hfe : ∀ z, F z = ε * star (F (1 - star z))) (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) {C r : ℝ}
    (hC : 0 < C) (hr0 : 0 ≤ r) (hr2 : r < 2) (hg : ∀ z : ℂ, ‖F z‖ ≤ Real.exp (C * (‖z‖ + 1) ^ r))
    (T : ℝ) (hs : F (((3 : ℝ) : ℂ) + T * Complex.I) ≠ 0) :
    (∑' ρ : ℂ, (analyticOrderNatAt F ρ : ℝ) * stripResolventPair T ρ) =
      2 * (logDeriv F (((3 : ℝ) : ℂ) + T * Complex.I)).re := by
  have ht : F (1 - star (((3 : ℝ) : ℂ) + T * Complex.I)) ≠ 0 :=
    (zero_iff_reflected_zero hε hfe _).not.mp hs
  have he := two_re_logDeriv_eq_reflectedResolventSum hε hfe hF h0 hC hr0 hr2 hg hs ht
  rw [reflection_at_three] at he
  rw [he]
  exact
    tsum_congr
      (fun ρ ↦ by
        simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero,
          stripResolventPair])

/-- If all zeros of F lie in the closed critical strip, every multiplicity
weighted reflected resolvent term is nonnegative. Nonzero values have
analytic order zero; zeros use strip positivity. This supplies the global
nonnegativity required for comparisons with the infinite series. -/
theorem multiplicity_stripResolventPair_nonneg {F : ℂ → ℂ}
    (hstrip : ∀ ρ, F ρ = 0 → 0 ≤ ρ.re ∧ ρ.re ≤ 1) (T : ℝ) (ρ : ℂ) :
    0 ≤ (analyticOrderNatAt F ρ : ℝ) * stripResolventPair T ρ := by
  by_cases hz : F ρ = 0
  · exact mul_nonneg (Nat.cast_nonneg _) (stripResolventPair_nonneg (hstrip ρ hz).1 (hstrip ρ hz).2)
  · have ho : analyticOrderNatAt F ρ = 0 := by
      rw [analyticOrderNatAt, analyticOrderAt_eq_zero.mpr (Or.inr hz), ENat.toNat_zero]
    simp only [ho, Nat.cast_zero, zero_mul, le_refl]

/-- Under the conjugate functional equation, entire subquadratic growth,
nonvanishing at zero and 3+iT, and critical-strip zero location, every
finite collection of points in the unit height window has multiplicity sum
at most 10*Re(logDeriv F(3+iT)). Dominate each multiplicity by five times its
reflected resolvent mass and use the full-mass identity. This is the finite
form of the local zero count used in Proposition 5.7. -/
theorem sum_localZeroMultiplicity_le_logDeriv {F : ℂ → ℂ} {ε : ℂ} (hε : ε ≠ 0)
    (hfe : ∀ z, F z = ε * star (F (1 - star z))) (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0)
    (hstrip : ∀ ρ, F ρ = 0 → 0 ≤ ρ.re ∧ ρ.re ≤ 1) {C r : ℝ} (hC : 0 < C) (hr0 : 0 ≤ r) (hr2 : r < 2)
    (hg : ∀ z : ℂ, ‖F z‖ ≤ Real.exp (C * (‖z‖ + 1) ^ r)) (T : ℝ)
    (hs : F (((3 : ℝ) : ℂ) + T * Complex.I) ≠ 0) (U : Finset ℂ) (hU : ∀ ρ ∈ U, |T - ρ.im| ≤ 1) :
    (∑ ρ ∈ U, (analyticOrderNatAt F ρ : ℝ)) ≤
      10 * (logDeriv F (((3 : ℝ) : ℂ) + T * Complex.I)).re := by
  have hpt :
    ∀ ρ ∈ U,
      (analyticOrderNatAt F ρ : ℝ) ≤
        5 * ((analyticOrderNatAt F ρ : ℝ) * stripResolventPair T ρ) := by
    intro ρ hρ
    by_cases hz : F ρ = 0
    · have hh :=
        mul_le_mul_of_nonneg_left
          (stripResolventPair_lower (hstrip ρ hz).1 (hstrip ρ hz).2 (hU ρ hρ))
          (Nat.cast_nonneg (analyticOrderNatAt F ρ) : (0 : ℝ) ≤ _)
      linarith only [hh]
    · have ho : analyticOrderNatAt F ρ = 0 := by
        rw [analyticOrderNatAt, analyticOrderAt_eq_zero.mpr (Or.inr hz), ENat.toNat_zero]
      simp only [ho, Nat.cast_zero, zero_mul, mul_zero, le_refl]
  have hsum := summable_stripResolventPair hF h0 hC hr0 hr2 hg T
  have hb := hsum.sum_le_tsum U (fun ρ _ ↦ multiplicity_stripResolventPair_nonneg hstrip T ρ)
  calc
    _ ≤ ∑ ρ ∈ U, 5 * ((analyticOrderNatAt F ρ : ℝ) * stripResolventPair T ρ) :=
      Finset.sum_le_sum hpt
    _ = 5 * ∑ ρ ∈ U, (analyticOrderNatAt F ρ : ℝ) * stripResolventPair T ρ :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ 5 * ∑' ρ : ℂ, (analyticOrderNatAt F ρ : ℝ) * stripResolventPair T ρ :=
      mul_le_mul_of_nonneg_left hb (by norm_num only)
    _ = _ := by
      rw [tsum_stripResolventPair_eq hε hfe hF h0 hC hr0 hr2 hg T hs]
      ring

/-- The natural analytic multiplicity of F at rho, cast to a real number,
when |T-Im rho|<=1, and zero outside this unit height window. The all-plane
indexing assigns zero to nonzero values of F. Summing these nonnegative
terms gives the multiplicity-counted local zero count. -/
noncomputable def localZeroMultiplicity (F : ℂ → ℂ) (T : ℝ) (ρ : ℂ) : ℝ := by
  classical exact if |T - ρ.im| ≤ 1 then (analyticOrderNatAt F ρ : ℝ) else 0

/-- Every local zero multiplicity is nonnegative, since analytic multiplicity
is natural and the cutoff is zero outside the height window. This permits
derivation of summability from bounded finite sums. -/
theorem localZeroMultiplicity_nonneg (F : ℂ → ℂ) (T : ℝ) (ρ : ℂ) :
    0 ≤ localZeroMultiplicity F T ρ := by
  classical
  by_cases h : |T - ρ.im| ≤ 1
  · simp only [localZeroMultiplicity, ite_eq_left h]
    exact Nat.cast_nonneg _
  · simp only [localZeroMultiplicity, ite_eq_right h, le_refl]

/-- For an entire critical-strip function with the conjugate functional
equation and subquadratic growth, the unit-height multiplicity series is
summable and bounded by 10*Re(logDeriv F(3+iT)). Apply the finite local-count
bound to each filtered finite set. Nonnegativity then gives summability and
the bound for the full sum, avoiding a default zero for a divergent tsum. -/
theorem summable_localZeroMultiplicity_and_bound {F : ℂ → ℂ} {ε : ℂ} (hε : ε ≠ 0)
    (hfe : ∀ z, F z = ε * star (F (1 - star z))) (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0)
    (hstrip : ∀ ρ, F ρ = 0 → 0 ≤ ρ.re ∧ ρ.re ≤ 1) {C r : ℝ} (hC : 0 < C) (hr0 : 0 ≤ r) (hr2 : r < 2)
    (hg : ∀ z : ℂ, ‖F z‖ ≤ Real.exp (C * (‖z‖ + 1) ^ r)) (T : ℝ)
    (hs : F (((3 : ℝ) : ℂ) + T * Complex.I) ≠ 0) :
    Summable (localZeroMultiplicity F T) ∧
      (∑' ρ : ℂ, localZeroMultiplicity F T ρ) ≤
        10 * (logDeriv F (((3 : ℝ) : ℂ) + T * Complex.I)).re := by
  classical
  have hb :
    ∀ U : Finset ℂ,
      (∑ ρ ∈ U, localZeroMultiplicity F T ρ) ≤
        10 * (logDeriv F (((3 : ℝ) : ℂ) + T * Complex.I)).re := by
    intro U
    simp only [localZeroMultiplicity, ← Finset.sum_filter]
    exact
      sum_localZeroMultiplicity_le_logDeriv hε hfe hF h0 hstrip hC hr0 hr2 hg T hs
        (U.filter (fun ρ ↦ |T - ρ.im| ≤ 1)) (fun ρ hρ ↦ (Finset.mem_filter.mp hρ).2)
  have hsummable := summable_of_sum_le (localZeroMultiplicity_nonneg F T) hb
  exact ⟨hsummable, hsummable.tsum_le_of_sum_le hb⟩

/-- An entire function of order at most one, nonzero at zero and in Re s>1,
with nonzero root number and conjugate functional equation has a summable
unit-height zero count bounded by 10*Re(logDeriv F(3+iT)). The functional
equation locates zeros in the critical strip; order one supplies a global
exponent-3/2 growth bound. This removes separate strip, growth-constant,
and convergence premises from the local-count interface. -/
theorem localZeroCount_bound_of_orderAtMostOne {F : ℂ → ℂ} {ε : ℂ} (hε : ε ≠ 0)
    (hfe : ∀ z, F z = ε * star (F (1 - star z))) (hright : ∀ s, 1 < s.re → F s ≠ 0)
    (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) (horder : HasOrderAtMostOne F) (T : ℝ) :
    Summable (localZeroMultiplicity F T) ∧
      (∑' ρ : ℂ, localZeroMultiplicity F T ρ) ≤
        10 * (logDeriv F (((3 : ℝ) : ℂ) + T * Complex.I)).re := by
  obtain ⟨C, hC, hg⟩ :=
    exists_global_exponential_bound_of_orderAtMostOne hF.continuous horder (r := 3 / 2)
      (by norm_num only)
  have hs : F (((3 : ℝ) : ℂ) + T * Complex.I) ≠ 0 := by
    apply hright
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero]
    norm_num only
  exact
    summable_localZeroMultiplicity_and_bound hε hfe hF h0
      (fun ρ hz ↦ zero_re_mem_Icc_of_functionalEquation hε hfe hright hz) hC
      (by norm_num only : (0 : ℝ) ≤ 3 / 2) (by norm_num only : (3 / 2 : ℝ) < 2) hg T hs

end PseudoPrime.AnalyticNumberTheory.General
