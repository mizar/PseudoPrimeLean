/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalKernel
public import PseudoPrime.LLS.MellinKernelZeros
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaSignedPoissonIdentity
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PositiveEulerPrefix

/-! # Real-axis Poisson budgets for the compact reciprocal kernel -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Input: a > 0, a squared <= 3/4 and a real ordinate t.
Claim: the reciprocal kernel norm is at most 1/(a squared+t squared).
Proof: compare squared positive denominators with the exact two-factor norm.
Role: control the rational zero mass by one adjustable real Poisson line. -/
theorem norm_reciprocalMellinFunction_le_resolvent {a t : ℝ} (ha : 0 < a) (hau : a ^ 2 ≤ 3 / 4) :
    ‖reciprocalMellinFunction (Complex.I * t)‖ ≤ 1 / (a ^ 2 + t ^ 2) := by
  have hA : 0 < ‖Complex.I * (t : ℂ) + 1 / 2‖ := by
    apply norm_pos_iff.mpr
    intro he
    have hr := congrArg Complex.re he
    norm_num only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_self, Complex.div_ofNat_re, Complex.one_re,
      Complex.zero_re, zero_add] at hr
  have hB : 0 < ‖Complex.I * (t : ℂ) + 3 / 2‖ := by
    apply norm_pos_iff.mpr
    intro he
    have hr := congrArg Complex.re he
    norm_num only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_self, Complex.div_ofNat_re, Complex.re_ofNat,
      Complex.zero_re, zero_add] at hr
  have hprod := mul_pos hA hB
  have hsq :
    (‖Complex.I * (t : ℂ) + 1 / 2‖ * ‖Complex.I * (t : ℂ) + 3 / 2‖) ^ 2 =
      (1 / 4 + t ^ 2) * (9 / 4 + t ^ 2) := by
    rw [mul_pow, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.div_ofNat_re,
      Complex.div_ofNat_im, Complex.one_re, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat,
      zero_mul, mul_zero, one_mul, zero_add, sub_zero]
    ring
  have ha4 := (sq_le_sq₀ (sq_nonneg a) (by norm_num only : (0 : ℝ) ≤ 3 / 4)).mpr hau
  have ht := mul_nonneg (show 0 ≤ 5 / 2 - 2 * a ^ 2 by linarith only [hau]) (sq_nonneg t)
  have hden0 : 0 < a ^ 2 + t ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) (sq_nonneg t)
  have hden : a ^ 2 + t ^ 2 ≤ ‖Complex.I * (t : ℂ) + 1 / 2‖ * ‖Complex.I * (t : ℂ) + 3 / 2‖ := by
    apply (sq_le_sq₀ hden0.le hprod.le).mp
    nlinarith only [hsq, ha4, ht]
  rw [reciprocalMellinFunction, norm_div, norm_one, norm_mul]
  exact one_div_le_one_div_of_le hden0 hden

/-- Input: a nonprincipal character, a > 0 with a squared <= 3/4, and any complex point.
Claim: its actual kernel zero term is bounded by the scaled Poisson term.
Proof: completed analyticity gives nonnegative multiplicity; apply the ordinate majorant.
Role: supply the convergent pointwise majorant for the full zero series. -/
theorem reciprocal_kernelZeroTerm_le_resolvent {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) {a : ℝ} (ha : 0 < a) (hau : a ^ 2 ≤ 3 / 4) (ρ : ℂ) :
    ‖reciprocalMellinKernel.kernelZeroTerm χ ρ‖ ≤
      (1 / a) *
        ((MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          (a / (a ^ 2 + ρ.im ^ 2))) := by
  have hAn : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := fun z _ ↦
    (DirichletCharacter.differentiable_completedLFunction hne).analyticAt z
  have hn : (0 : ℝ) ≤ (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) := by
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAn ρ
  rw [MellinKernel.kernelZeroTerm, norm_mul, Complex.norm_intCast, abs_of_nonneg hn]
  have hb :=
    mul_le_mul_of_nonneg_left (norm_reciprocalMellinFunction_le_resolvent ha hau (t := ρ.im)) hn
  change
    (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
        ‖reciprocalMellinFunction (Complex.I * ρ.im)‖ ≤
      _
  have he :
    (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * (1 / (a ^ 2 + ρ.im ^ 2)) =
      (1 / a) *
        ((MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          (a / (a ^ 2 + ρ.im ^ 2))) := by
    field_simp [ha.ne', (add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) (sq_nonneg ρ.im)).ne']
  exact hb.trans_eq he

/-- Input: GRH, primitive nonprincipal data at q >= 2, x > 0 and 1/2 < a with a squared <= 3/4.
Claim: the zero-sum norm is bounded by the real conductor, Gamma and L derivatives at 1/2+a.
Proof: sum the resolvent majorant and use the exact signed Poisson identity.
Role: preserve the real Euler derivative before any arithmetic estimate. -/
theorem norm_reciprocal_zeroSum_le_real_axis {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {a x : ℝ} (ha : 1 / 2 < a)
    (hau : a ^ 2 ≤ 3 / 4) (hx : 0 < x) :
    ‖∑' ρ : ℂ, reciprocalMellinKernel.oscillatingZeroTerm χ x ρ‖ ≤
      (1 / a) *
        (Real.log q / 2 + (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + a) : ℂ)).re +
          (logDeriv χ.LFunction (((1 / 2 : ℝ) + a) : ℂ)).re) := by
  have ha0 : 0 < a := lt_trans (by norm_num only) ha
  have hrh := hGRH q χ hp
  have hs :=
    AnalyticNumberTheory.DirichletLFunction.summable_completed_resolvent_terms hq hrh hp hne hinv
      ha0
  have hk := MellinKernel.summable_oscillatingZeroTerm reciprocalMellinKernel hq hGRH hp hne hinv hx
  have hb (ρ : ℂ) :
    ‖reciprocalMellinKernel.oscillatingZeroTerm χ x ρ‖ ≤
      (1 / a) *
        ((MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          (a / (a ^ 2 + ρ.im ^ 2))) := by
    rw [MellinKernel.norm_oscillatingZeroTerm reciprocalMellinKernel χ hx]
    exact reciprocal_kernelZeroTerm_le_resolvent χ hne ha0 hau ρ
  have hu := (norm_tsum_le_tsum_norm hk.norm).trans (hk.norm.tsum_le_tsum hb (hs.mul_left (1 / a)))
  rw [tsum_mul_left] at hu
  have he :=
    AnalyticNumberTheory.DirichletLFunction.completed_poissonSum_eq_signed_ordinary hq hrh hp hne
      hinv (show (1 : ℝ) < 1 / 2 + a by linarith only [ha])
  simp only [add_sub_cancel_left, Complex.ofReal_add] at he
  have ht :
    (∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * (a / (a ^ 2 + ρ.im ^ 2))) =
      Real.log q / 2 + (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + a) : ℂ)).re +
        (logDeriv χ.LFunction (((1 / 2 : ℝ) + a) : ℂ)).re := by
    rw [← he]
    apply tsum_congr
    intro ρ
    simpa only [Complex.ofReal_add] using
      AnalyticNumberTheory.DirichletLFunction.completed_resolventTerm_eq_poisson hrh hp hne hinv a ρ
  rw [ht] at hu
  exact hu

/-- Input: the same analytic data and an arbitrary finite set of natural indices.
Claim: the zero budget subtracts the actual nonnegative Euler prefix from principal Euler mass.
Proof: insert the kernel-independent real logarithmic-derivative prefix inequality.
Role: connect finite prime-power gains to the actual rational kernel zero sum. -/
theorem norm_reciprocal_zeroSum_le_positive_prefix {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {a x : ℝ} (ha : 1 / 2 < a)
    (hau : a ^ 2 ≤ 3 / 4) (hx : 0 < x) (B : Finset ℕ) :
    ‖∑' ρ : ℂ, reciprocalMellinKernel.oscillatingZeroTerm χ x ρ‖ ≤
      (1 / a) *
        (Real.log q / 2 + (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + a) : ℂ)).re +
            (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + a)) -
          ∑ n ∈ B, (1 + (χ n).re) * ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + a)) := by
  have hU := norm_reciprocal_zeroSum_le_real_axis hq hGRH hp hne hinv ha hau hx
  have hE :=
    AnalyticNumberTheory.DirichletLFunction.re_logDeriv_le_principal_sub_positive_prefix χ
      (show (1 : ℝ) < 1 / 2 + a by linarith only [ha]) B
  simp only [Complex.ofReal_add] at hE
  have hm :=
    mul_le_mul_of_nonneg_left
      (add_le_add_left hE (Real.log q / 2 + (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + a) : ℂ)).re))
      (one_div_nonneg.mpr (show (0 : ℝ) ≤ a by linarith only [ha]))
  exact hU.trans (by linarith only [hm])

/-- Input: a > 0 with a squared <= 3/4, as required by this majorant.
Claim: the squared ratio of the leading zero coefficient to the endpoint is at least 4/3.
Proof: positive-denominator rational arithmetic.
Role: identify the limitation of this single-resolvent comparison, not of arbitrary kernels. -/
theorem reciprocal_single_resolvent_leading_coefficient {a : ℝ} (ha : 0 < a) (hau : a ^ 2 ≤ 3 / 4) :
    (4 / 3 : ℝ) ≤ (1 / a) ^ 2 := by
  rw [div_pow, one_pow, le_div_iff₀ (sq_pos_of_pos ha)]
  nlinarith only [hau]

end PseudoPrime.LLS.PaperStatements
