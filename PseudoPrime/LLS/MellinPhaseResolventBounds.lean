/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.FiniteSignedResolvent
public import PseudoPrime.LLS.GammaSignedConductorRemainder

/-! # Phase-sensitive Mellin zero bounds with paired Euler savings -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements.MellinKernel

/-- Input: a Mellin kernel, a character, scale and zero index.
Claim: the negative real zero term is its multiplicity times the signed phase.
Proof: expand the real part of a product with a real multiplicity.
Role: avoid replacing the phase by the absolute value of the kernel. -/
theorem neg_re_oscillatingZeroTerm (K : MellinKernel) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (x : ℝ) (ρ : ℂ) :
    -(K.oscillatingZeroTerm χ x ρ).re =
      (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
        (-(K.function (Complex.I * ρ.im) * (x : ℂ) ^ (Complex.I * ρ.im)).re) := by
  dsimp only [oscillatingZeroTerm, kernelZeroTerm]
  rw [mul_assoc]
  norm_num only [Complex.mul_re, Complex.intCast_re, Complex.intCast_im, zero_mul, sub_zero]
  ring

/-- Input: GRH, a primitive nonprincipal character, positive scale and positive nodes;
the signed phase is pointwise bounded by the finite resolvent on every real ordinate.
Claim: the negative real zero sum is bounded by the resolvent zero mass.
Proof: use nonnegative zero multiplicities and summability of both series.
Role: transfer phase-sensitive majorants to the actual explicit formula. -/
theorem neg_re_oscillatingZeroSum_le_finiteResolvent (K : MellinKernel) {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) (l : List (ℚ × ℚ))
    (ha : ∀ ab ∈ l, (0 : ℚ) < ab.1)
    (hphase :
      ∀ t : ℝ,
        -(K.function (Complex.I * t) * (x : ℂ) ^ (Complex.I * t)).re ≤
          Analysis.finiteSignedResolvent l t) :
    -(∑' ρ : ℂ, K.oscillatingZeroTerm χ x ρ).re ≤
      ∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          Analysis.finiteSignedResolvent l ρ.im := by
  have hs := summable_oscillatingZeroTerm K hq hGRH hp hne hinv hx
  have hr :=
    AnalyticNumberTheory.DirichletLFunction.summable_finiteSignedResolvent_terms hq (hGRH q χ hp) hp
      hne hinv l ha
  have hAn : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := fun z _ ↦
    (DirichletCharacter.differentiable_completedLFunction hne).analyticAt z
  have hn (ρ : ℂ) : 0 ≤ (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) := by
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAn ρ
  have hb (ρ : ℂ) :
    -(K.oscillatingZeroTerm χ x ρ).re ≤
      (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
        Analysis.finiteSignedResolvent l ρ.im := by
    rw [neg_re_oscillatingZeroTerm]
    exact mul_le_mul_of_nonneg_left (hphase ρ.im) (hn ρ)
  have h := ((Complex.reCLM.summable hs).neg).tsum_le_tsum hb hr
  rw [tsum_neg, ← Complex.re_tsum hs] at h
  exact h

/-- Input: the phase-majorant hypotheses, nodes exceeding one half and a finite prefix.
Claim: the negative real zero sum is bounded by the budget minus the exact paired tail.
Proof: combine spectral comparison with the exact Euler identity.
Role: retain all paired prime-power savings for arbitrary Mellin kernels. -/
theorem neg_re_oscillatingZeroSum_le_prefix_tail (K : MellinKernel) {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) (l : List (ℚ × ℚ))
    (ha : ∀ ab ∈ l, (1 / 2 : ℚ) < ab.1) (B : Finset ℕ)
    (hphase :
      ∀ t : ℝ,
        -(K.function (Complex.I * t) * (x : ℂ) ^ (Complex.I * t)).re ≤
          Analysis.finiteSignedResolvent l t) :
    -(∑' ρ : ℂ, K.oscillatingZeroTerm χ x ρ).re ≤
      AnalyticNumberTheory.DirichletLFunction.finiteSignedPrefixBudget χ l B -
        Analysis.pairedWeightTail (Analysis.finiteSignedMangoldtWeight l) (fun n ↦ (χ n).re) B := by
  have h :=
    neg_re_oscillatingZeroSum_le_finiteResolvent K hq hGRH hp hne hinv hx l
      (fun ab hab ↦ lt_trans (by norm_num only : (0 : ℚ) < 1 / 2) (ha ab hab)) hphase
  exact
    h.trans_eq
      (AnalyticNumberTheory.DirichletLFunction.finiteSignedResolvent_zeroMass_eq_prefix_tail hq
        (hGRH q χ hp) hp hne hinv l ha B)

/-- Input: the phase-majorant hypotheses and nonnegative common Mangoldt weights.
Claim: the prefix budget bounds the negative real zero sum.
Proof: combine spectral comparison with the nonnegative-tail upper bound.
Role: support finite-scale rational spectral certificates. -/
theorem neg_re_oscillatingZeroSum_le_prefix (K : MellinKernel) {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) (l : List (ℚ × ℚ))
    (ha : ∀ ab ∈ l, (1 / 2 : ℚ) < ab.1) (hW : ∀ n, 0 ≤ Analysis.finiteSignedMangoldtWeight l n)
    (B : Finset ℕ)
    (hphase :
      ∀ t : ℝ,
        -(K.function (Complex.I * t) * (x : ℂ) ^ (Complex.I * t)).re ≤
          Analysis.finiteSignedResolvent l t) :
    -(∑' ρ : ℂ, K.oscillatingZeroTerm χ x ρ).re ≤
      AnalyticNumberTheory.DirichletLFunction.finiteSignedPrefixBudget χ l B := by
  have h :=
    neg_re_oscillatingZeroSum_le_finiteResolvent K hq hGRH hp hne hinv hx l
      (fun ab hab ↦ lt_trans (by norm_num only : (0 : ℚ) < 1 / 2) (ha ab hab)) hphase
  exact
    h.trans
      (AnalyticNumberTheory.DirichletLFunction.finiteSignedResolvent_zeroMass_le_prefix hq
        (hGRH q χ hp) hp hne hinv l ha hW B)

end PseudoPrime.LLS.PaperStatements.MellinKernel

namespace PseudoPrime.LLS.PaperStatements

/-- Input: GRH, 20000 <= q, primitive conductor 3 <= m <= q, scale x >= 2,
admissible nodes and a global signed-phase majorant.
Claim: the actual Gamma arithmetic sum is bounded by the exact prefix-tail budget
and the certified remainder, retaining the signed conductor term.
Proof: combine the completed explicit formula remainder and the phase bound.
Role: connect rational majorants to quadratic and general-character witness arguments. -/
theorem gamma_primitive_sum_re_le_phase_prefix_tail {q m : ℕ} [NeZero m] (hq : 20000 ≤ q)
    (hm : 3 ≤ m) (hmq : m ≤ q) {χ : DirichletCharacter ℂ m}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 2 ≤ x) (l : List (ℚ × ℚ))
    (ha : ∀ ab ∈ l, (1 / 2 : ℚ) < ab.1) (B : Finset ℕ)
    (hphase :
      ∀ t : ℝ,
        -(gammaMellinKernel.function (Complex.I * t) * (x : ℂ) ^ (Complex.I * t)).re ≤
          Analysis.finiteSignedResolvent l t) :
    (∑' k : ℕ, gammaMellinKernel.summand χ x k).re ≤
      AnalyticNumberTheory.DirichletLFunction.finiteSignedPrefixBudget χ l B -
          Analysis.pairedWeightTail (Analysis.finiteSignedMangoldtWeight l) (fun n ↦ (χ n).re) B +
        ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
        Analysis.gammaNegativeConductorTerm (Real.log m) x +
        43 * x ^ (-9 / 16 : ℝ) := by
  have hr := re_gamma_primitive_remainder_le_signed_conductor hq hm hmq hp hne hinv hGRH hx
  have hz :=
    gammaMellinKernel.neg_re_oscillatingZeroSum_le_prefix_tail
      (le_trans (by norm_num only : (2 : ℕ) ≤ 3) hm) hGRH hp hne hinv
      (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 2) hx) l ha B hphase
  simp only [Complex.add_re] at hr
  linarith only [hr, hz]

/-- Input: the Gamma phase-majorant hypotheses and nonnegative common Mangoldt weights.
Claim: an upper bound for the actual Gamma arithmetic sum with the certified conductor-free error.
Proof: combine the phase bound with the existing explicit-formula remainder.
Role: provide a general-character interface for quadratic and Miller-Rabin improvements. -/
theorem gamma_primitive_sum_re_le_phase_prefix {q m : ℕ} [NeZero m] (hq : 20000 ≤ q) (hm : 3 ≤ m)
    (hmq : m ≤ q) {χ : DirichletCharacter ℂ m}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 2 ≤ x) (l : List (ℚ × ℚ))
    (ha : ∀ ab ∈ l, (1 / 2 : ℚ) < ab.1) (hW : ∀ n, 0 ≤ Analysis.finiteSignedMangoldtWeight l n)
    (B : Finset ℕ)
    (hphase :
      ∀ t : ℝ,
        -(gammaMellinKernel.function (Complex.I * t) * (x : ℂ) ^ (Complex.I * t)).re ≤
          Analysis.finiteSignedResolvent l t) :
    (∑' k : ℕ, gammaMellinKernel.summand χ x k).re ≤
      AnalyticNumberTheory.DirichletLFunction.finiteSignedPrefixBudget χ l B +
        ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
        43 * x ^ (-9 / 16 : ℝ) := by
  have hr := re_gamma_primitive_remainder_le_conductor_free hq hm hmq hp hne hinv hGRH hx
  have hz :=
    gammaMellinKernel.neg_re_oscillatingZeroSum_le_prefix
      (le_trans (by norm_num only : (2 : ℕ) ≤ 3) hm) hGRH hp hne hinv
      (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 2) hx) l ha hW B hphase
  simp only [Complex.add_re] at hr
  linarith only [hr, hz]

end PseudoPrime.LLS.PaperStatements
