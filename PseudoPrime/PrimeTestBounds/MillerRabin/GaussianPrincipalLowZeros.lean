/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPrincipalHeadNumeric
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100Bounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterZetaLedger
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPrincipalHeadNumeric
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighKernelData
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100Bounds
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroEnumerationCount
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.SincTailAnchorRH
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPrincipalZeroCoeff
import Mathlib.Tactic.Ring
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroConjugateSum

/-! # Principal head bounds on the certified low-zero brackets -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational midpoint of one certified positive zero bracket. -/
public def highZeroBracketMid (i : Fin 29) : ℚ :=
  AnalyticNumberTheory.RiemannZeta.lowZero100Lower i + 1 / 200

/-- The H26 midpoint error on one of the 29 certified brackets. -/
public def highZeroBracketError (K : HighGaussianKernel) (i : Fin 29) : ℚ :=
  let l := AnalyticNumberTheory.RiemannZeta.lowZero100Lower i
  highPrincipalBracketError K l (l + 1 / 100)

/-- All left endpoints in the positive zero table are strictly positive. -/
private theorem high_zero_left_pos (i : Fin 29) :
    0 < AnalyticNumberTheory.RiemannZeta.lowZero100Lower i := by
  exact (by decide +kernel : ∀ j : Fin 29, 0 < AnalyticNumberTheory.RiemannZeta.lowZero100Lower j) i

/-- The bracket predicates give a pointwise H26 bound for the same zero family. -/
public theorem high_low_zero_midpoint (K : HighGaussianKernel) (g : Fin 29 → ℝ)
    (hlo : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g)
    (hhi : AnalyticNumberTheory.RiemannZeta.LowZero100UpperBounds g)
    (hc : highPrincipalHeadCap K ≤ (highHeadCapTicks K : ℝ) / 1000) (i : Fin 29) :
    ‖highPrincipalMultiplier K (g i)‖ ≤
      ‖highPrincipalMultiplier K (highZeroBracketMid i : ℝ)‖ + (highZeroBracketError K i : ℝ) := by
  let l := AnalyticNumberTheory.RiemannZeta.lowZero100Lower i
  have h :=
    high_principal_midpoint_bracket K (r := l + 1 / 100) (high_zero_left_pos i)
      ⟨hlo i, by simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hhi i⟩
      hc
  have hm (l : ℚ) : (l + (l + 1 / 100)) / 2 = l + 1 / 200 := by ring
  simpa only [hm, highZeroBracketMid, highZeroBracketError, l] using h

/-- Rational upper caps on the total H26 midpoint variation over the positive zero brackets. -/
@[expose]
public def highZeroErrorBudget : HighGaussianKernel → ℚ
  | .k186 => 306 / 1000000
  | .k196 => 479 / 1000000

/-- The sum of the 29 rational error charges fits the corresponding kernel budget. -/
public theorem high_zero_bracket_error_sum (K : HighGaussianKernel) :
    (∑ i, highZeroBracketError K i) ≤ highZeroErrorBudget K := by cases K <;> decide +kernel

/-- Sum the midpoint norms and add the certified error budget for the 29 positive brackets. -/
public theorem high_low_zero_head_le (K : HighGaussianKernel) (g : Fin 29 → ℝ)
    (hlo : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g)
    (hhi : AnalyticNumberTheory.RiemannZeta.LowZero100UpperBounds g)
    (hc : highPrincipalHeadCap K ≤ (highHeadCapTicks K : ℝ) / 1000) :
    (∑ i, ‖highPrincipalMultiplier K (g i)‖) ≤
      (∑ i, ‖highPrincipalMultiplier K (highZeroBracketMid i : ℝ)‖) +
        (highZeroErrorBudget K : ℝ) := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ high_low_zero_midpoint K g hlo hhi hc i)
  have he : ((∑ i, highZeroBracketError K i : ℚ) : ℝ) ≤ (highZeroErrorBudget K : ℝ) :=
    Rat.cast_le.mpr (high_zero_bracket_error_sum K)
  rw [Finset.sum_add_distrib] at h
  rw [Rat.cast_sum] at he
  exact h.trans (add_le_add le_rfl he)

/-- A bound on any family in the certified brackets controls the positive zero ledger. -/
public theorem high_positive_head_of_brackets (K : HighGaussianKernel) (hRH : RiemannHypothesis)
    {B : ℝ}
    (hbr :
      ∀ g : Fin 29 → ℝ,
        AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g →
          AnalyticNumberTheory.RiemannZeta.LowZero100UpperBounds g →
          (∑ i, ‖highPrincipalMultiplier K (g i)‖) ≤ B) :
    (∑ ρ ∈ (AnalyticNumberTheory.RiemannZeta.zerosUpTo 100).filter (fun ρ ↦ 0 < ρ.im),
        (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
          ‖highPrincipalMultiplier K ρ.im‖) ≤
      B := by
  classical
  obtain ⟨g, hm, _, _, _, hlo, hhi, hcover, hmult⟩ := quarter_low_zeros_complete hRH
  let Z := fun i : Fin 29 ↦ ((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I
  let w := fun ρ : ℂ ↦
    (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
      ‖highPrincipalMultiplier K ρ.im‖
  refine
    (Finset.sum_le_sum_of_subset_of_nonneg hcover
          (fun ρ _ _ ↦ mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))).trans
      ?_
  change (∑ ρ ∈ Finset.univ.image Z, w ρ) ≤ _
  rw [Finset.sum_image
      (fun i _ j _ hij ↦
        AnalyticNumberTheory.RiemannZeta.critical_points_injective g hm.injective hij)]
  have hi (i : Fin 29) : (Z i).im = g i := by
    simp only [Z, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
  refine le_trans ?_ (hbr g hlo hhi)
  apply Finset.sum_le_sum
  intro i _
  change w (Z i) ≤ ‖highPrincipalMultiplier K (g i)‖
  have hm₁ : AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity (Z i) = 1 := hmult i
  simp only [w, hi, hm₁, Nat.cast_one, one_mul, le_refl]

/-- Under RH the certified positive zeros through height 100 satisfy the H26 head bound,
with each zero counted with its multiplicity. -/
public theorem high_positive_zero_head_le (K : HighGaussianKernel) (hRH : RiemannHypothesis)
    (hc : highPrincipalHeadCap K ≤ (highHeadCapTicks K : ℝ) / 1000) :
    (∑ ρ ∈ (AnalyticNumberTheory.RiemannZeta.zerosUpTo 100).filter (fun ρ ↦ 0 < ρ.im),
        (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
          ‖highPrincipalMultiplier K ρ.im‖) ≤
      (∑ i, ‖highPrincipalMultiplier K (highZeroBracketMid i : ℝ)‖) +
        (highZeroErrorBudget K : ℝ) := by
  exact high_positive_head_of_brackets K hRH (fun g hlo hhi ↦ high_low_zero_head_le K g hlo hhi hc)

/-- The square-kernel factor at the reflected height is its complex conjugate. -/
private theorem high_height_neg (K : HighGaussianKernel) (t : ℝ) :
    highHeightKernel K (-t) = (starRingEnd ℂ) (highHeightKernel K t) := by
  have hrat : (starRingEnd ℂ).comp (Rat.castHom ℂ) = Rat.castHom ℂ := Subsingleton.elim _ _
  simp only [high_height_kernel_eq, map_div₀, map_mul, map_pow, map_add, map_ofNat, map_ratCast,
    ← Complex.exp_conj, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg,
    Polynomial.hom_eval₂, hrat, neg_mul, mul_neg]

/-- The finite Mellin head at the reflected height is its complex conjugate. -/
private theorem high_head_neg (K : HighGaussianKernel) (t : ℝ) :
    highPrincipalHead K (-t) = (starRingEnd ℂ) (highPrincipalHead K t) := by
  simp only [highPrincipalHead, map_mul, ← intervalIntegral.intervalIntegral_conj,
    ← Complex.exp_conj, map_ofNat, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg, map_add,
    map_neg, neg_mul, mul_neg]

/-- The principal zero multiplier is conjugated when its ordinate is reflected. -/
private theorem high_multiplier_neg (K : HighGaussianKernel) (t : ℝ) :
    highPrincipalMultiplier K (-t) = (starRingEnd ℂ) (highPrincipalMultiplier K t) := by
  simp only [highPrincipalMultiplier, high_height_neg, high_head_neg, map_add, map_mul, map_div₀,
    map_neg, map_ofNat, map_one, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg, neg_mul,
    mul_neg]

/-- A positive-side bound gives a two-sided bound by conjugation. -/
public theorem high_zero_head_of_positive (K : HighGaussianKernel) (hRH : RiemannHypothesis) {B : ℝ}
    (hpos :
      (∑ ρ ∈ (AnalyticNumberTheory.RiemannZeta.zerosUpTo 100).filter (fun ρ ↦ 0 < ρ.im),
          (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
            ‖highPrincipalMultiplier K ρ.im‖) ≤
        B) :
    (∑ ρ ∈ AnalyticNumberTheory.RiemannZeta.zerosUpTo 100,
        (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
          ‖highPrincipalMultiplier K ρ.im‖) ≤
      2 * B := by
  let w := fun ρ : ℂ ↦
    (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
      ‖highPrincipalMultiplier K ρ.im‖
  have h100 : (0 : ℝ) ≤ 100 := by norm_num only
  have hw (ρ : ℂ) (hρ : ρ ∈ AnalyticNumberTheory.RiemannZeta.zerosUpTo 100) :
    w ((starRingEnd ℂ) ρ) = w ρ := by
    have hz := (AnalyticNumberTheory.RiemannZeta.mem_zerosUpTo h100).mp hρ
    have hr :=
      AnalyticNumberTheory.RiemannZeta.zeta_zero_re_eq_half_of_riemannHypothesis hRH hz.1 hz.2.1
    have hne : ρ ≠ 1 := by
      intro he
      rw [he, Complex.one_re] at hr
      norm_num only at hr
    simp only [w, AnalyticNumberTheory.RiemannZeta.multiplicity_conj hne, Complex.conj_im,
      high_multiplier_neg, Complex.norm_conj]
  change (∑ ρ ∈ AnalyticNumberTheory.RiemannZeta.zerosUpTo 100, w ρ) ≤ _
  rw [AnalyticNumberTheory.RiemannZeta.zero_sum_eq_two_positive hRH h100 w hw]
  exact mul_le_mul_of_nonneg_left hpos (by norm_num only)

/-- Under RH the two-sided head through height 100 is at most twice the positive bracket bound. -/
public theorem high_zero_head_le (K : HighGaussianKernel) (hRH : RiemannHypothesis)
    (hc : highPrincipalHeadCap K ≤ (highHeadCapTicks K : ℝ) / 1000) :
    (∑ ρ ∈ AnalyticNumberTheory.RiemannZeta.zerosUpTo 100,
        (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
          ‖highPrincipalMultiplier K ρ.im‖) ≤
      2 *
        ((∑ i, ‖highPrincipalMultiplier K (highZeroBracketMid i : ℝ)‖) +
          (highZeroErrorBudget K : ℝ)) := by
  exact high_zero_head_of_positive K hRH (high_positive_zero_head_le K hRH hc)

/-- A unit Mellin phase leaves the norm bound for the scaled coefficient unchanged. -/
private theorem high_phase_abs_le (K : HighGaussianKernel) (hRH : RiemannHypothesis) (X : ℝ) {ρ : ℂ}
    (hz : riemannZeta ρ = 0 ∧ 0 ≤ ρ.re) :
    |(Complex.exp ((Real.log X : ℂ) * (ρ.im : ℂ) * Complex.I) *
            (Complex.exp (-(5 * (K.pole : ℂ))) * highPrincipalFiniteCoeff K ρ)).re| ≤
      (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
        ‖highPrincipalMultiplier K ρ.im‖ := by
  have hphase : ‖Complex.exp ((Real.log X : ℂ) * (ρ.im : ℂ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp, ← Complex.ofReal_mul]
    simp only [Complex.mul_re, Complex.I_re, Complex.ofReal_im, mul_zero, zero_mul, zero_sub,
      neg_zero, Real.exp_zero]
  refine (Complex.abs_re_le_norm _).trans_eq ?_
  rw [high_principal_multiplier_eq K hRH hz, norm_mul, hphase, one_mul, norm_mul,
    Complex.norm_natCast]

/-- The unit Mellin phases preserve the absolute head bound on the normalized coefficient sum. -/
public theorem high_principal_phase_head_le (K : HighGaussianKernel) (hRH : RiemannHypothesis)
    (hc : highPrincipalHeadCap K ≤ (highHeadCapTicks K : ℝ) / 1000) (X : ℝ) :
    |∑ ρ ∈ AnalyticNumberTheory.RiemannZeta.zerosUpTo 100,
          (Complex.exp ((Real.log X : ℂ) * (ρ.im : ℂ) * Complex.I) *
              (Complex.exp (-(5 * (K.pole : ℂ))) * highPrincipalFiniteCoeff K ρ)).re| ≤
      2 *
        ((∑ i, ‖highPrincipalMultiplier K (highZeroBracketMid i : ℝ)‖) +
          (highZeroErrorBudget K : ℝ)) := by
  refine
    ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)).trans
      (high_zero_head_le K hRH hc)
  intro ρ hρ
  have hz :=
    (AnalyticNumberTheory.RiemannZeta.mem_zerosUpTo (by norm_num only : (0 : ℝ) ≤ 100)).mp hρ
  exact high_phase_abs_le K hRH X ⟨hz.1, hz.2.1⟩

/-- The principal multiplier has the same norm at an ordinate and its absolute value. -/
private theorem high_multiplier_norm_abs (K : HighGaussianKernel) (t : ℝ) :
    ‖highPrincipalMultiplier K |t|‖ = ‖highPrincipalMultiplier K t‖ := by
  rcases le_total 0 t with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h, high_multiplier_neg, Complex.norm_conj]

/-- A height majorant yields one tail charge for both signs of the zero ordinate. -/
private theorem high_zero_tail_le (K : HighGaussianKernel) (hRH : RiemannHypothesis) (S : Finset ℂ)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ t : ℝ, 100 < t → ‖highPrincipalMultiplier K t‖ ≤ C / t ^ 2)
    (hz : ∀ ρ ∈ S, riemannZeta ρ = 0) (hre : ∀ ρ ∈ S, 0 ≤ ρ.re) (ht : ∀ ρ ∈ S, 100 < |ρ.im|) :
    (∑ ρ ∈ S,
        (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
          ‖highPrincipalMultiplier K ρ.im‖) ≤
      C * (13 / 1000) := by
  have h :=
    (AnalyticNumberTheory.RiemannZeta.finite_ordinate_tail_le hRH S 100 hz hre ht).trans
      (AnalyticNumberTheory.RiemannZeta.ordinateTail_hundred_le hRH)
  refine le_trans ?_ (mul_le_mul_of_nonneg_left h hC)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ρ hρ
  rw [← high_multiplier_norm_abs K ρ.im]
  exact (mul_le_mul_of_nonneg_left (hbound _ (ht ρ hρ)) (Nat.cast_nonneg _)).trans_eq (by ring)

/-- A finite zero ledger is bounded by the low brackets and one two-sided tail charge. -/
private theorem high_zero_spectral_of_head (K : HighGaussianKernel) (hRH : RiemannHypothesis)
    (S : Finset ℂ) {C : ℝ} (hC : 0 ≤ C) {B : ℝ}
    (hhead :
      (∑ ρ ∈ AnalyticNumberTheory.RiemannZeta.zerosUpTo 100,
          (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
            ‖highPrincipalMultiplier K ρ.im‖) ≤
        B)
    (hbound : ∀ t : ℝ, 100 < t → ‖highPrincipalMultiplier K t‖ ≤ C / t ^ 2)
    (hz : ∀ ρ ∈ S, riemannZeta ρ = 0) (hre : ∀ ρ ∈ S, 0 ≤ ρ.re) :
    (∑ ρ ∈ S,
        (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
          ‖highPrincipalMultiplier K ρ.im‖) ≤
      B + C * (13 / 1000) := by
  classical
  let p := fun ρ : ℂ ↦ |ρ.im| ≤ (100 : ℝ)
  let w := fun ρ : ℂ ↦
    (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
      ‖highPrincipalMultiplier K ρ.im‖
  have hsub : S.filter p ⊆ AnalyticNumberTheory.RiemannZeta.zerosUpTo 100 := by
    intro ρ hρ
    obtain ⟨hs, hp⟩ := Finset.mem_filter.mp hρ
    exact
      (AnalyticNumberTheory.RiemannZeta.mem_zerosUpTo (by norm_num only : (0 : ℝ) ≤ 100)).mpr
        ⟨hz ρ hs, hre ρ hs, hp⟩
  have hh :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun ρ _ _ ↦
            mul_nonneg (Nat.cast_nonneg _) (norm_nonneg (highPrincipalMultiplier K ρ.im)))).trans
      hhead
  have ht :=
    high_zero_tail_le K hRH (S.filter fun ρ ↦ ¬p ρ) hC hbound
      (fun ρ hρ ↦ hz ρ (Finset.mem_filter.mp hρ).1) (fun ρ hρ ↦ hre ρ (Finset.mem_filter.mp hρ).1)
      (fun ρ hρ ↦ lt_of_not_ge (Finset.mem_filter.mp hρ).2)
  change (∑ ρ ∈ S, w ρ) ≤ _
  rw [← Finset.sum_filter_add_sum_filter_not S p w]
  exact add_le_add hh ht

/-- A finite zero ledger is bounded by the low brackets and one two-sided tail charge. -/
public theorem high_zero_spectral_le (K : HighGaussianKernel) (hRH : RiemannHypothesis)
    (S : Finset ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hc : highPrincipalHeadCap K ≤ (highHeadCapTicks K : ℝ) / 1000)
    (hbound : ∀ t : ℝ, 100 < t → ‖highPrincipalMultiplier K t‖ ≤ C / t ^ 2)
    (hz : ∀ ρ ∈ S, riemannZeta ρ = 0) (hre : ∀ ρ ∈ S, 0 ≤ ρ.re) :
    (∑ ρ ∈ S,
        (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
          ‖highPrincipalMultiplier K ρ.im‖) ≤
      2 *
          ((∑ i, ‖highPrincipalMultiplier K (highZeroBracketMid i : ℝ)‖) +
            (highZeroErrorBudget K : ℝ)) +
        C * (13 / 1000) := by
  exact high_zero_spectral_of_head K hRH S hC (high_zero_head_le K hRH hc) hbound hz hre

/-- The finite spectral bound passes to the normalized principal zero series. -/
public theorem high_principal_series_of_head (K : HighGaussianKernel) (hRH : RiemannHypothesis)
    {B C : ℝ} (hC : 0 ≤ C)
    (hhead :
      (∑ ρ ∈ AnalyticNumberTheory.RiemannZeta.zerosUpTo 100,
          (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
            ‖highPrincipalMultiplier K ρ.im‖) ≤
        B)
    (hbound : ∀ t : ℝ, 100 < t → ‖highPrincipalMultiplier K t‖ ≤ C / t ^ 2) {X : ℝ} (hX : 0 < X) :
    let d := (K.pole : ℝ) - 1 / 2
    let W := fun u : ℝ ↦ u ^ d * K.realProfile.eval (5 - Real.log u)
    let F := fun u : ℝ ↦ u * deriv W u
    |Real.exp (-(5 * (K.pole : ℝ))) *
          (principalErrorFunctional (deriv F) gaussianLogZetaZeroSum (F 1) X (Real.exp 5) /
            Real.sqrt X)| ≤
      B + C * (13 / 1000) := by
  classical
  intro d W F
  let e := Real.exp (-(5 * (K.pole : ℝ)))
  let f := fun ρ : ℂ ↦
    (Complex.exp ((Real.log X : ℂ) * (ρ.im : ℂ) * Complex.I) * highPrincipalFiniteCoeff K ρ).re
  have hsum := (high_principal_finite_hasSum K hRH hX).mul_left e
  apply le_of_tendsto hsum.abs
  apply Filter.Eventually.of_forall
  intro S
  let p := fun ρ : ℂ ↦ riemannZeta ρ = 0 ∧ 0 ≤ ρ.re
  have hfilter : (∑ ρ ∈ S, e * f ρ) = ∑ ρ ∈ S.filter p, e * f ρ := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ρ _
    by_cases hρ : p ρ
    · rw [ite_eq_left hρ]
    · simp only [f, highPrincipalFiniteCoeff,
        ite_eq_right (show ¬(riemannZeta ρ = 0 ∧ 0 ≤ ρ.re) from hρ), mul_zero, Complex.zero_re]
  change |∑ ρ ∈ S, e * f ρ| ≤ _
  rw [hfilter]
  refine
    ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)).trans
      (high_zero_spectral_of_head K hRH (S.filter p) hC hhead hbound
        (fun ρ hρ ↦ (Finset.mem_filter.mp hρ).2.1) (fun ρ hρ ↦ (Finset.mem_filter.mp hρ).2.2))
  intro ρ hρ
  have hz := (Finset.mem_filter.mp hρ).2
  let A := Complex.exp ((Real.log X : ℂ) * (ρ.im : ℂ) * Complex.I)
  have he : (e : ℂ) = Complex.exp (-(5 * (K.pole : ℂ))) := by
    simp only [e, Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_ofNat,
      Complex.ofReal_ratCast]
  have hreal : e * f ρ = (A * ((e : ℂ) * highPrincipalFiniteCoeff K ρ)).re := by
    rw [← mul_assoc, mul_comm A, mul_assoc]
    simp only [f, A, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [hreal, he]
  exact high_phase_abs_le K hRH X hz

/-- The finite spectral bound passes to the normalized principal zero series. -/
public theorem high_principal_series_le (K : HighGaussianKernel) (hRH : RiemannHypothesis) {C : ℝ}
    (hC : 0 ≤ C) (hc : highPrincipalHeadCap K ≤ (highHeadCapTicks K : ℝ) / 1000)
    (hbound : ∀ t : ℝ, 100 < t → ‖highPrincipalMultiplier K t‖ ≤ C / t ^ 2) {X : ℝ} (hX : 0 < X) :
    let d := (K.pole : ℝ) - 1 / 2
    let W := fun u : ℝ ↦ u ^ d * K.realProfile.eval (5 - Real.log u)
    let F := fun u : ℝ ↦ u * deriv W u
    |Real.exp (-(5 * (K.pole : ℝ))) *
          (principalErrorFunctional (deriv F) gaussianLogZetaZeroSum (F 1) X (Real.exp 5) /
            Real.sqrt X)| ≤
      2 *
          ((∑ i, ‖highPrincipalMultiplier K (highZeroBracketMid i : ℝ)‖) +
            (highZeroErrorBudget K : ℝ)) +
        C * (13 / 1000) := by
  exact high_principal_series_of_head K hRH hC (high_zero_head_le K hRH hc) hbound hX

end PseudoPrime.PrimeTestBounds.MillerRabin
