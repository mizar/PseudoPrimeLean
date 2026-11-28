/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipal600
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.OrdinateTail
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.OrdinateTailRetainedRH
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100Bounds
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountConjugation
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipal600
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAbel570
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100Bounds
import Mathlib.Data.Fin.VecNotation
import PseudoPrime.Analysis.NumericalLogBounds
import PseudoPrime.Analysis.LogTaylorBounds

/-! # Zero contributions to the quarter-bound principal error -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH, the fixed-kernel tail over any finite family of distinct
nontrivial zeros above height one hundred is bounded by the full ordinate
tail with the factor 0.467. Multiplicities are included in both sums. -/
theorem section104_finite_high_le (hRH : RiemannHypothesis) (S : Finset ℂ)
    (hz : ∀ ρ ∈ S, riemannZeta ρ = 0) (hre : ∀ ρ ∈ S, 0 ≤ ρ.re) (ht : ∀ ρ ∈ S, 100 < |ρ.im|) :
    (∑ ρ ∈ S,
        (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
          ‖section99PhaseKernel ρ‖) ≤
      0.467 * AnalyticNumberTheory.RiemannZeta.ordinateTail 100 := by
  have hh := AnalyticNumberTheory.RiemannZeta.finite_ordinate_tail_le hRH S 100 hz hre ht
  have h := mul_le_mul_of_nonneg_left hh (by norm_num only : (0 : ℝ) ≤ 0.467)
  rw [Finset.mul_sum] at h
  apply (Finset.sum_le_sum (fun ρ hρ ↦ ?_)).trans h
  have hx := AnalyticNumberTheory.RiemannXi.xi_zero_of_zeta_zero_of_re_nonneg (hz ρ hρ) (hre ρ hρ)
  have hr := AnalyticNumberTheory.RiemannXi.xi_zero_re_eq_half_of_riemannHypothesis hRH hx
  have he : (1 / 2 : ℂ) + (ρ.im : ℂ) * Complex.I = ρ := by
    apply Complex.ext
    · rw [hr]
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero, Complex.one_re, Complex.div_ofNat_re]
    · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, mul_one, mul_zero, add_zero, zero_add, Complex.one_im, Complex.div_ofNat_im,
        zero_div]
  have hK := section104_kernel_high (ht ρ hρ).le
  rw [he, ← sq_abs] at hK
  exact (mul_le_mul_of_nonneg_left hK (Nat.cast_nonneg _)).trans_eq (by ring)

/-- Integer ceilings for ten million times the square-root envelope
at the existing 29 lower bracket endpoints. -/
private def section104RootCeiling : Fin 29 → ℕ :=
  ![10925060, 4933627, 3484431, 2354211, 2008960, 1542374, 1301351, 1160678, 945421, 879420, 776477,
    683788, 618556, 588734, 513852, 484159, 450419, 419461, 380116, 366052, 346100, 316909, 303403,
    285022, 276209, 254651, 243164, 237016, 223027]

/-- The rational polynomial used in the low-zero certificate. -/
private def section104RatPolynomial (z : ℚ) : ℚ :=
  (289622126450944 / 6103515625) * z ^ 5 + (262010390307638336 / 762939453125) * z ^ 4 +
    (541127807836464711968 / 476837158203125) * z ^ 3 +
    (691311736370338386621192 / 298023223876953125) * z ^ 2 +
    (555633899038052789188973049 / 186264514923095703125) * z +
    1404005148524444584781450458449 / 2328306436538696289062500

/-- The ceilings are valid by squaring and checking the rational inequality
at every certified lower bracket endpoint. -/
private theorem section104_root_check (i : Fin 29) :
    let l := AnalyticNumberTheory.RiemannZeta.lowZero100Lower i
    14 ≤ l ∧
      section104RatPolynomial (l ^ 2) / ((l ^ 2 + 1 / 4) * (l ^ 2 + (51 / 50) ^ 2) ^ 6) ≤
        ((section104RootCeiling i : ℚ) / 10000000) ^ 2 := by
  exact
    (show
        ∀ j : Fin 29,
          let l := AnalyticNumberTheory.RiemannZeta.lowZero100Lower j
          14 ≤ l ∧
            section104RatPolynomial (l ^ 2) / ((l ^ 2 + 1 / 4) * (l ^ 2 + (51 / 50) ^ 2) ^ 6) ≤
              ((section104RootCeiling j : ℚ) / 10000000) ^ 2
        from by decide +kernel)
      i

/-- Rational upper bound for the norm at one low bracket. -/
private def section104RatBound (i : Fin 29) : ℚ :=
  let z := (AnalyticNumberTheory.RiemannZeta.lowZero100Lower i) ^ 2
  4 * (53 / 100000) * ((section104RootCeiling i : ℚ) / 10000000) +
    (51 / 50) ^ 5 / (z + (51 / 50) ^ 2) ^ 3

/-- The endpoint bounds cover all 29 low absolute ordinates, with a
combined bound of 0.00791 for each choice of signs. -/
theorem section104_low_abs_sum_bound {g : Fin 29 → ℝ}
    (hg : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds (fun i ↦ |g i|)) :
    (∑ i : Fin 29, ‖section99PhaseKernel ((1 / 2 : ℂ) + (g i : ℂ) * Complex.I)‖) ≤ 0.00791 := by
  have hi (i : Fin 29) :
    ‖section99PhaseKernel ((1 / 2 : ℂ) + (g i : ℂ) * Complex.I)‖ ≤ (section104RatBound i : ℝ) := by
    let l := AnalyticNumberTheory.RiemannZeta.lowZero100Lower i
    have ⟨hl, hs⟩ := section104_root_check i
    have hl' : (14 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
    have hs' :
      section104NormPolynomial ((l : ℝ) ^ 2) /
          (((l : ℝ) ^ 2 + 1 / 4) * ((l : ℝ) ^ 2 + (51 / 50) ^ 2) ^ 6) ≤
        ((section104RootCeiling i : ℝ) / 10000000) ^ 2 := by
      unfold section104NormPolynomial
      unfold section104RatPolynomial at hs
      dsimp only [l]
      simpa only [Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_add, Rat.cast_ofNat,
        Rat.cast_natCast, Rat.cast_one] using (Rat.cast_le (K := ℝ)).mpr hs
    have hroot :=
      (Real.sqrt_le_sqrt hs').trans_eq
        (Real.sqrt_sq (by positivity : 0 ≤ (section104RootCeiling i : ℝ) / 10000000))
    have hb := section104_kernel_le_abs_endpoint hl' (hg i)
    apply hb.trans
    dsimp only [section104RatBound]
    push_cast
    exact
      add_le_add_left
        (mul_le_mul (mul_le_mul_of_nonneg_left section104_norm_constant_le (by norm_num only)) hroot
          (Real.sqrt_nonneg _) (by norm_num only : (0 : ℝ) ≤ 4 * (53 / 100000)))
        _
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ hi i)
  refine h.trans ?_
  have hQ : (∑ i : Fin 29, section104RatBound i) ≤ (791 / 100000 : ℚ) := by decide +kernel
  rw [show (0.00791 : ℝ) = 791 / 100000 by norm_num only]
  simpa only [Rat.cast_sum, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hQ

/-- The endpoint bounds cover all 29 low positive ordinates, with a
combined bound of 0.00791 before conjugation. -/
theorem section104_low_sum_bound {g : Fin 29 → ℝ}
    (hg : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g) :
    (∑ i : Fin 29, ‖section99PhaseKernel ((1 / 2 : ℂ) + (g i : ℂ) * Complex.I)‖) ≤ 0.00791 := by
  apply section104_low_abs_sum_bound
  exact fun i ↦ (hg i).trans (le_abs_self (g i))

/-- The 29 low zeros and their reflected ordinates have combined kernel
norm at most 0.01582 for the certified positive brackets. -/
theorem section104_low_pair_bound {g : Fin 29 → ℝ}
    (hg : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g) :
    (∑ i : Fin 29, ‖section99PhaseKernel ((1 / 2 : ℂ) + (g i : ℂ) * Complex.I)‖) +
        (∑ i : Fin 29, ‖section99PhaseKernel ((1 / 2 : ℂ) + ((-g i : ℝ) : ℂ) * Complex.I)‖) ≤
      0.01582 := by
  have hneg : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds (fun i ↦ |-g i|) := by
    intro i
    dsimp only
    rw [abs_neg]
    exact (hg i).trans (le_abs_self (g i))
  linarith only [section104_low_sum_bound hg, section104_low_abs_sum_bound hneg]

/-- The inverse-square tail above one hundred is at most 0.0128 under RH
and the height-100 count certificate. Retain the exact count of 58 zeros through the cutoff. -/
theorem section104_ordinate_tail_le (hRH : RiemannHypothesis)
    (hc : AnalyticNumberTheory.RiemannZeta.zeroCount 100 = 58) :
    AnalyticNumberTheory.RiemannZeta.ordinateTail 100 ≤ 0.0128 := by
  have h :=
    AnalyticNumberTheory.RiemannZeta.ordinateTail_retain_count hRH
      (by norm_num only : (40 : ℝ) ≤ 100)
  rw [hc] at h
  have hL :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 100 6 64 (460517 / 100000) (460518 / 100000) = true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hL
  have hn : Real.log 100 - Real.log (2 * Real.pi) ≤ (27682 / 10000 : ℝ) := by
    linarith only [hL, Analysis.log_two_mul_pi_gt]
  have hd :=
    div_le_div₀ (by norm_num only : (0 : ℝ) ≤ 27682 / 10000) hn
      (by norm_num only : (0 : ℝ) < 3.1415) Real.pi_gt_d4.le
  have he :
    (2 / Real.pi) * (Real.log 100 - Real.log (2 * Real.pi)) / 100 =
      (2 / 100) * ((Real.log 100 - Real.log (2 * Real.pi)) / Real.pi) := by
    ring
  rw [he] at h
  linarith only [h, hd, hL]

/-- With the retained zero count, the total finite kernel contribution
above height one hundred is at most 0.0059776 under RH and the count certificate. -/
theorem section104_finite_high_bound (hRH : RiemannHypothesis)
    (hc : AnalyticNumberTheory.RiemannZeta.zeroCount 100 = 58) (S : Finset ℂ)
    (hz : ∀ ρ ∈ S, riemannZeta ρ = 0) (hre : ∀ ρ ∈ S, 0 ≤ ρ.re) (ht : ∀ ρ ∈ S, 100 < |ρ.im|) :
    (∑ ρ ∈ S,
        (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
          ‖section99PhaseKernel ρ‖) ≤
      0.0059776 := by
  linarith only [section104_finite_high_le hRH S hz hre ht, section104_ordinate_tail_le hRH hc]

/-- Combine the certified low pairs and the counted tail for any finite
set of nontrivial zeros whose low members belong to those simple pairs. -/
theorem section104_finite_kernel_bound (hRH : RiemannHypothesis)
    (hc : AnalyticNumberTheory.RiemannZeta.zeroCount 100 = 58) (S : Finset ℂ)
    (hz : ∀ ρ ∈ S, riemannZeta ρ = 0) (hre : ∀ ρ ∈ S, 0 ≤ ρ.re) {g : Fin 29 → ℝ}
    (hg : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g) (hgmono : StrictMono g)
    (hgpos : ∀ i, 0 < g i)
    (hlo :
      ∀ ρ ∈ S,
        |ρ.im| ≤ 100 →
          AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ = 1 ∧
            (∃ i,
              ρ = (1 / 2 : ℂ) + (g i : ℂ) * Complex.I ∨
                ρ = (1 / 2 : ℂ) + ((-g i : ℝ) : ℂ) * Complex.I)) :
    (∑ ρ ∈ S,
        (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
          ‖section99PhaseKernel ρ‖) ≤
      0.0217976 := by
  classical
  let P := fun i : Fin 29 ↦ (1 / 2 : ℂ) + (g i : ℂ) * Complex.I
  let N := fun i : Fin 29 ↦ (1 / 2 : ℂ) + ((-g i : ℝ) : ℂ) * Complex.I
  let lo := S.filter (fun ρ ↦ |ρ.im| ≤ 100)
  let hi := S.filter (fun ρ ↦ 100 < |ρ.im|)
  let K := fun ρ : ℂ ↦ ‖section99PhaseKernel ρ‖
  let F := fun ρ : ℂ ↦ (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) * K ρ
  have hP (i : Fin 29) : (P i).im = g i := by
    simp only [P, Complex.add_im, Complex.mul_im, Complex.div_ofNat_im, Complex.one_im, zero_div,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero,
      zero_add]
  have hN (i : Fin 29) : (N i).im = -g i := by
    simp only [N, Complex.add_im, Complex.mul_im, Complex.div_ofNat_im, Complex.one_im, zero_div,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero,
      zero_add]
  have hPi : Function.Injective P := by
    intro i j h
    exact hgmono.injective ((hP i).symm.trans ((congrArg Complex.im h).trans (hP j)))
  have hNi : Function.Injective N := by
    intro i j h
    have he := (hN i).symm.trans ((congrArg Complex.im h).trans (hN j))
    exact hgmono.injective (neg_injective he)
  have hs : lo ⊆ Finset.univ.image P ∪ Finset.univ.image N := by
    intro ρ hρ
    have hp := Finset.mem_filter.mp hρ
    obtain ⟨i, hc⟩ := (hlo ρ hp.1 hp.2).2
    rcases hc with h | h
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h.symm⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h.symm⟩)
  have hdis : Disjoint (Finset.univ.image P) (Finset.univ.image N) := by
    apply Finset.disjoint_left.2
    intro ρ hp hn
    obtain ⟨i, _, hpi⟩ := Finset.mem_image.mp hp
    obtain ⟨j, _, hnj⟩ := Finset.mem_image.mp hn
    have h := congrArg Complex.im (hpi.trans hnj.symm)
    rw [hP, hN] at h
    linarith only [h, hgpos i, hgpos j]
  have hl : ∑ ρ ∈ lo, F ρ ≤ 0.01582 := by
    calc
      _ = ∑ ρ ∈ lo, K ρ := by
        apply Finset.sum_congr rfl
        intro ρ hρ
        have hp := Finset.mem_filter.mp hρ
        simp only [F, (hlo ρ hp.1 hp.2).1, Nat.cast_one, one_mul]
      _ ≤ ∑ ρ ∈ Finset.univ.image P ∪ Finset.univ.image N, K ρ :=
        Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ ↦ norm_nonneg _)
      _ = (∑ ρ ∈ Finset.univ.image P, K ρ) + ∑ ρ ∈ Finset.univ.image N, K ρ := Finset.sum_union hdis
      _ ≤ _ := by
        rw [Finset.sum_image (fun i _ j _ hij ↦ hPi hij),
          Finset.sum_image (fun i _ j _ hij ↦ hNi hij)]
        exact section104_low_pair_bound hg
  have hh :=
    section104_finite_high_bound hRH hc hi (fun ρ hρ ↦ hz ρ (Finset.mem_filter.mp hρ).1)
      (fun ρ hρ ↦ hre ρ (Finset.mem_filter.mp hρ).1) (fun ρ hρ ↦ (Finset.mem_filter.mp hρ).2)
  have he := Finset.sum_filter_add_sum_filter_not S (fun ρ ↦ |ρ.im| ≤ 100) F
  simp only [not_le] at he
  change (∑ ρ ∈ lo, F ρ) + (∑ ρ ∈ hi, F ρ) = ∑ ρ ∈ S, F ρ at he
  change (∑ ρ ∈ S, F ρ) ≤ _
  rw [← he]
  exact (add_le_add hl hh).trans_eq (by norm_num only)

/-- Positive completeness and simplicity through height 100 also cover
the negative ordinates, by conjugation and preservation of multiplicity. -/
theorem section104_low_pair_complete (hRH : RiemannHypothesis) {g : Fin 29 → ℝ}
    (hcover :
      (AnalyticNumberTheory.RiemannZeta.zerosUpTo 100).filter (fun ρ ↦ 0 < ρ.im) ⊆
        Finset.univ.image (fun i ↦ (1 / 2 : ℂ) + (g i : ℂ) * Complex.I))
    (hm :
      ∀ i,
        AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity
            ((1 / 2 : ℂ) + (g i : ℂ) * Complex.I) =
          1)
    {ρ : ℂ} (hz : riemannZeta ρ = 0) (hre : 0 ≤ ρ.re) (ht : |ρ.im| ≤ 100) :
    AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ = 1 ∧
      ∃ i,
        ρ = (1 / 2 : ℂ) + (g i : ℂ) * Complex.I ∨
          ρ = (1 / 2 : ℂ) + ((-g i : ℝ) : ℂ) * Complex.I := by
  classical
  have hpos {z : ℂ} (hz' : riemannZeta z = 0) (hr' : 0 ≤ z.re) (ht' : |z.im| ≤ 100)
    (hi : 0 < z.im) : ∃ i, (1 / 2 : ℂ) + (g i : ℂ) * Complex.I = z := by
    have hmem :=
      (AnalyticNumberTheory.RiemannZeta.mem_zerosUpTo (by norm_num only : (0 : ℝ) ≤ 100)).2
        ⟨hz', hr', ht'⟩
    obtain ⟨i, _, he⟩ := Finset.mem_image.mp (hcover (Finset.mem_filter.mpr ⟨hmem, hi⟩))
    exact ⟨i, he⟩
  have hne : ρ.im ≠ 0 := by
    have h := AnalyticNumberTheory.RiemannZeta.zero_height_gt_two_pi hRH hz hre
    intro hzero
    rw [hzero, abs_zero] at h
    linarith only [h, Real.pi_pos]
  rcases lt_or_gt_of_ne hne with hneg | hplus
  · let z := (starRingEnd ℂ) ρ
    have hz' : riemannZeta z = 0 := by
      dsimp only [z]
      rw [riemannZeta_conj, hz, map_zero]
    have hi : z.im = -ρ.im := Complex.conj_im ρ
    obtain ⟨i, he⟩ :=
      hpos hz' (show 0 ≤ z.re from hre)
        (by
          rw [hi, abs_neg]; exact ht)
        (by
          rw [hi]; exact neg_pos.mpr hneg)
    have hρ : ρ ≠ 1 := by
      intro e
      exact hne (by rw [e, Complex.one_im])
    have hm' := AnalyticNumberTheory.RiemannZeta.multiplicity_conj hρ
    change AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity z = _ at hm'
    rw [← he, hm i] at hm'
    refine ⟨hm'.symm, i, Or.inr ?_⟩
    have hc := congrArg (starRingEnd ℂ) he.symm
    simpa only [z, Complex.conj_conj, map_add, map_div₀, map_one, map_ofNat, map_mul,
      Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg, mul_neg, neg_mul] using hc
  · obtain ⟨i, he⟩ := hpos hz hre ht hplus
    exact ⟨he ▸ hm i, i, Or.inl he.symm⟩

/-- The finite sum of normalized phase terms is bounded below uniformly
in the physical cutoff, using the complete low pairs and the high tail. -/
theorem section104_finite_phase_lower (hRH : RiemannHypothesis)
    (hc : AnalyticNumberTheory.RiemannZeta.zeroCount 100 = 58) (S : Finset ℂ)
    (hz : ∀ ρ ∈ S, riemannZeta ρ = 0) (hre : ∀ ρ ∈ S, 0 ≤ ρ.re) {g : Fin 29 → ℝ}
    (hg : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g) (hgmono : StrictMono g)
    (hgpos : ∀ i, 0 < g i)
    (hcover :
      (AnalyticNumberTheory.RiemannZeta.zerosUpTo 100).filter (fun ρ ↦ 0 < ρ.im) ⊆
        Finset.univ.image (fun i ↦ (1 / 2 : ℂ) + (g i : ℂ) * Complex.I))
    (hm :
      ∀ i,
        AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity
            ((1 / 2 : ℂ) + (g i : ℂ) * Complex.I) =
          1)
    {X : ℝ} (hX : 0 < X) :
    -0.0217976 ≤
      ∑ ρ ∈ S,
        ((AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ) *
            ((X : ℂ) ^ ρ / (Real.sqrt X : ℂ)) *
            section99PhaseKernel ρ).re := by
  have hu :=
    section104_finite_kernel_bound hRH hc S hz hre hg hgmono hgpos
      (fun ρ hρ ht ↦ section104_low_pair_complete hRH hcover hm (hz ρ hρ) (hre ρ hρ) ht)
  apply (neg_le_neg hu).trans
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro ρ hρ
  have hx := AnalyticNumberTheory.RiemannXi.xi_zero_of_zeta_zero_of_re_nonneg (hz ρ hρ) (hre ρ hρ)
  have hr := AnalyticNumberTheory.RiemannXi.xi_zero_re_eq_half_of_riemannHypothesis hRH hx
  exact (abs_le.mp (section99_phase_kernel_bound hX hr _)).1

/-- The cutoff phase cancels the phase of the lower-end power. Its
product is the real decay factor at the physical endpoint one. -/
theorem section99_lower_power_cancel {X : ℝ} (hX : 0 < X) (ρ : ℂ) :
    ((X : ℂ) ^ ρ / (Real.sqrt X : ℂ)) * ((1 / X : ℝ) : ℂ) ^ (ρ + 13 / 25) =
      (X ^ (-(51 / 50 : ℝ)) : ℝ) := by
  have hx : (X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
  have hy : ((1 / X : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (one_div_pos.mpr hX).ne'
  have hpow : (X : ℂ) ^ ρ * ((1 / X : ℝ) : ℂ) ^ (ρ + 13 / 25) = (X ^ (-(13 / 25 : ℝ)) : ℝ) := by
    rw [Complex.cpow_def_of_ne_zero hx, Complex.cpow_def_of_ne_zero hy, Complex.ofReal_cpow hX.le,
      Complex.cpow_def_of_ne_zero hx, ← Complex.ofReal_log hX.le, ←
      Complex.ofReal_log (one_div_pos.mpr hX).le, one_div, Real.log_inv, Complex.ofReal_neg, ←
      Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [div_mul_eq_mul_div, hpow, ← Complex.ofReal_div, Real.sqrt_eq_rpow, ← Real.rpow_sub hX]
  rw [show -(13 / 25 : ℝ) - 1 / 2 = -(51 / 50) by ring]

/-- The physical weight at one has the same decay factor and shifted
logarithm as the lower-end Mellin correction. -/
theorem section99_weight_one_power {X : ℝ} (hX : 0 < X) :
    quarterWeight570 X 1 =
      (Real.exp (-(14 / 5 * (51 / 50))) / ((50 / 51) ^ 5 * 120)) *
        (X ^ (-(51 / 50 : ℝ)) * (14 / 5 + Real.log X) ^ 5) := by
  rw [quarterWeight570, Real.sqrt_one, one_div_one, one_mul, one_div, Real.log_inv, sub_neg_eq_add]
  rw [Real.rpow_def_of_pos hX]
  have he :
    -((2 * (7 / 5) + Real.log X) / (2 * (25 / 51))) =
      -(14 / 5 * (51 / 50)) + Real.log X * -(51 / 50) := by
    ring
  rw [he, Real.exp_add]
  ring

/-- Both lower-end corrections in a zero contribution share a real decay
factor. The remaining expression uses the shifted logarithmic polynomial
and the reciprocal from the boundary value. -/
theorem section99_zero_lower_formula {X : ℝ} (hX : 1 ≤ X) {ρ : ℂ} (hρ : 0 < ρ.re + 13 / 25) :
    let m := (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ)
    let p := (X : ℂ) ^ ρ / (Real.sqrt X : ℂ)
    let s := ρ + (13 / 25 : ℂ)
    let b := 14 / 5 + Real.log X
    let C := (Real.exp (-(14 / 5 * (51 / 50))) / ((50 / 51) ^ 5 * 120) : ℝ)
    section99ZeroIntegral X ρ =
      (m * p * section99PhaseKernel ρ).re +
        3 * C * X ^ (-(51 / 50 : ℝ)) *
          ((m *
                (∑ j ∈ Finset.range 6,
                  (((5 : ℕ).choose j : ℂ) * (b : ℂ) ^ (5 - j)) *
                    ((j.factorial : ℂ) / s ^ (j + 1)))).re +
            (-m / ρ).re * b ^ 5) := by
  intro m p s b C
  have hx := zero_lt_one.trans_le hX
  let A :=
    ∑ j ∈ Finset.range 6,
      (((5 : ℕ).choose j : ℂ) * (b : ℂ) ^ (5 - j)) * ((j.factorial : ℂ) / s ^ (j + 1))
  have hM : section99Moment s (1 / X) = ((1 / X : ℝ) : ℂ) ^ s * A := by
    unfold section99Moment
    rw [show (14 / 5 - Real.log (1 / X) : ℝ) = b
        by
        dsimp only [b]
        rw [one_div, Real.log_inv, sub_neg_eq_add]]
  have hP : p * ((1 / X : ℝ) : ℂ) ^ s = (X ^ (-(51 / 50 : ℝ)) : ℝ) :=
    section99_lower_power_cancel hx ρ
  have h := section99_zero_phase_split hX hρ
  dsimp only at h
  change
    section99ZeroIntegral X ρ =
      (m * p * section99PhaseKernel ρ).re + 3 * C * (m * p * section99Moment s (1 / X)).re +
        3 * (-m / ρ).re * quarterWeight570 X 1 at h
  rw [h, hM, section99_weight_one_power hx]
  rw [show m * p * (((1 / X : ℝ) : ℂ) ^ s * A) = (p * ((1 / X : ℝ) : ℂ) ^ s) * (m * A) by ring, hP]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  dsimp only [C, b]
  ring

/-- The lower-end coefficient after the first reciprocal cancels with
the boundary term. Every remaining denominator has degree at least two. -/
noncomputable def section99LowerKernel (b : ℝ) (ρ : ℂ) : ℂ :=
  let s := ρ + (13 / 25 : ℂ)
  (-((b : ℂ) ^ 5 * (13 / 25) / (ρ * s)) +
    (∑ j ∈ Finset.range 5,
      (((5 : ℕ).choose (j + 1) : ℂ) * (b : ℂ) ^ (5 - (j + 1))) *
        (((j + 1).factorial : ℂ) / s ^ ((j + 1) + 1))))

/-- The lower endpoint contributes the real part of the cancelled
coefficient times the real cutoff decay factor and the zero multiplicity. -/
theorem section99_zero_lower_cancel {X : ℝ} (hX : 1 ≤ X) {ρ : ℂ} (hn : ρ ≠ 0)
    (hρ : 0 < ρ.re + 13 / 25) :
    let m := (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ)
    let p := (X : ℂ) ^ ρ / (Real.sqrt X : ℂ)
    let b := 14 / 5 + Real.log X
    let C := (Real.exp (-(14 / 5 * (51 / 50))) / ((50 / 51) ^ 5 * 120) : ℝ)
    section99ZeroIntegral X ρ =
      (m * p * section99PhaseKernel ρ).re +
        3 * C * X ^ (-(51 / 50 : ℝ)) * (m * section99LowerKernel b ρ).re := by
  intro m p b C
  let s := ρ + (13 / 25 : ℂ)
  have hs : s ≠ 0 := by
    have hre : 0 < s.re := by
      dsimp only [s]
      norm_num only [Complex.add_re, Complex.div_ofNat_re]
      exact hρ
    intro he
    rw [he, Complex.zero_re] at hre
    exact (lt_irrefl _ hre)
  have hdiff : (1 : ℂ) / s - 1 / ρ = -(13 / 25) / (ρ * s) := by
    field_simp [hn, hs]
    dsimp only [s]
    ring
  let A :=
    ∑ j ∈ Finset.range 6,
      (((5 : ℕ).choose j : ℂ) * (b : ℂ) ^ (5 - j)) * ((j.factorial : ℂ) / s ^ (j + 1))
  have hA : m * A + (-m / ρ) * (b : ℂ) ^ 5 = m * section99LowerKernel b ρ := by
    unfold A section99LowerKernel
    rw [Finset.sum_range_succ']
    simp only [Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero, Nat.factorial_zero, Nat.zero_add,
      pow_one, one_mul, mul_one_div]
    change _ = m * (-((b : ℂ) ^ 5 * (13 / 25) / (ρ * s)) + _)
    rw [show -((b : ℂ) ^ 5 * (13 / 25) / (ρ * s)) = (b : ℂ) ^ 5 * (1 / s - 1 / ρ) by
        rw [hdiff]; ring]
    ring
  have h := section99_zero_lower_formula hX hρ
  change
    section99ZeroIntegral X ρ =
      (m * p * section99PhaseKernel ρ).re +
        3 * C * X ^ (-(51 / 50 : ℝ)) * ((m * A).re + (-m / ρ).re * b ^ 5) at h
  rw [h]
  have hre : (((-m / ρ) * (b : ℂ) ^ 5)).re = (-m / ρ).re * b ^ 5 := by
    simp only [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero]
  rw [← hre, ← Complex.add_re, hA]

/-- The cancelled lower kernel is bounded by 51/50 times the fifth power of the
shift divided by the squared ordinate, for shifts at least fourteen. -/
theorem section99_lower_kernel_bound {b : ℝ} (hb : 14 ≤ b) {ρ : ℂ} (ht : 1 ≤ |ρ.im|) :
    ‖section99LowerKernel b ρ‖ ≤ (51 / 50) * b ^ 5 / |ρ.im| ^ 2 := by
  let t := |ρ.im|
  let s := ρ + (13 / 25 : ℂ)
  have hb0 : 0 ≤ b := by linarith only [hb]
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hρ : t ≤ ‖ρ‖ := Complex.abs_im_le_norm ρ
  have hs : t ≤ ‖s‖ := by
    have he : s.im = ρ.im := by
      dsimp only [s]
      rw [Complex.add_im, ← Complex.ofReal_ofNat, ← Complex.ofReal_ofNat, ← Complex.ofReal_div,
        Complex.ofReal_im, add_zero]
    rw [show t = |s.im| from congrArg abs he.symm]
    exact Complex.abs_im_le_norm s
  have hprod : t ^ 2 ≤ ‖ρ‖ * ‖s‖ := by
    rw [sq]
    exact mul_le_mul hρ hs ht0.le (norm_nonneg _)
  have hpow (n : ℕ) (h : 2 ≤ n) : t ^ 2 ≤ ‖s‖ ^ n :=
    (pow_le_pow_left₀ ht0.le hs 2).trans (pow_le_pow_right₀ (ht.trans hs) h)
  let F := fun j : ℕ ↦
    (((5 : ℕ).choose (j + 1) : ℂ) * (b : ℂ) ^ (5 - (j + 1))) *
      (((j + 1).factorial : ℂ) / s ^ ((j + 1) + 1))
  have hF (j : ℕ) :
    ‖F j‖ ≤
      (((5 : ℕ).choose (j + 1) : ℝ) * b ^ (5 - (j + 1)) * ((j + 1).factorial : ℝ)) / t ^ 2 := by
    simp only [F, norm_mul, norm_div, norm_pow, Complex.norm_natCast, Complex.norm_real,
      Real.norm_of_nonneg hb0, ← mul_div_assoc]
    exact
      div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos ht0)
        (hpow _ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le j))))
  have hA : ‖-((b : ℂ) ^ 5 * (13 / 25) / (ρ * s))‖ ≤ b ^ 5 * (13 / 25) / t ^ 2 := by
    simp only [norm_neg, norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hb0,
      Complex.norm_ofNat]
    exact div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos ht0) hprod
  change ‖-((b : ℂ) ^ 5 * (13 / 25) / (ρ * s)) + ∑ j ∈ Finset.range 5, F j‖ ≤ _
  apply (norm_add_le _ _).trans
  refine (add_le_add hA ((norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ hF j))).trans ?_
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, Nat.reduceSub,
    Nat.choose, Nat.factorial, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, zero_add,
    add_zero, pow_zero, pow_one, mul_one, one_mul]
  change _ ≤ (51 / 50) * b ^ 5 / t ^ 2
  rw [← add_div, ← add_div, ← add_div, ← add_div, ← add_div]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  have h₁ := mul_le_mul_of_nonneg_left hb (pow_nonneg hb0 4)
  have h₂ := mul_le_mul_of_nonneg_left hb (pow_nonneg hb0 3)
  have h₃ := mul_le_mul_of_nonneg_left hb (pow_nonneg hb0 2)
  have h₄ := mul_le_mul_of_nonneg_left hb hb0
  nlinarith only [h₁, h₂, h₃, h₄, hb]

/-- Each corrected zero coefficient differs from its phase term by at
most the endpoint weight times a multiple of its inverse-square mass. -/
theorem section99_zero_lower_error {X : ℝ} (hX : 1 ≤ X) (hb : 14 ≤ 14 / 5 + Real.log X) {ρ : ℂ}
    (ht : 1 ≤ |ρ.im|) (hr : ρ.re = 1 / 2) :
    let m := AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ
    let p := (X : ℂ) ^ ρ / (Real.sqrt X : ℂ)
    |section99ZeroIntegral X ρ - ((m : ℂ) * p * section99PhaseKernel ρ).re| ≤
      (153 / 50) * quarterWeight570 X 1 * ((m : ℝ) / |ρ.im| ^ 2) := by
  intro m p
  let b := 14 / 5 + Real.log X
  let C := (Real.exp (-(14 / 5 * (51 / 50))) / ((50 / 51) ^ 5 * 120) : ℝ)
  let d := X ^ (-(51 / 50 : ℝ))
  have hn : ρ ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hr
    norm_num only at hr
  have hρ : 0 < ρ.re + 13 / 25 := by
    rw [hr]; norm_num only
  have he := section99_zero_lower_cancel hX hn hρ
  change
    section99ZeroIntegral X ρ =
      ((m : ℂ) * p * section99PhaseKernel ρ).re +
        3 * C * d * ((m : ℂ) * section99LowerKernel b ρ).re at he
  rw [he, add_sub_cancel_left, abs_mul,
    abs_of_nonneg
      (by
        dsimp only [C, d]; positivity)]
  have h := (Complex.abs_re_le_norm ((m : ℂ) * section99LowerKernel b ρ))
  rw [norm_mul, Complex.norm_natCast] at h
  have hh :=
    h.trans (mul_le_mul_of_nonneg_left (section99_lower_kernel_bound hb ht) (Nat.cast_nonneg m))
  refine
    (mul_le_mul_of_nonneg_left hh
          (by
            dsimp only [C, d]; positivity)).trans_eq
      ?_
  rw [section99_weight_one_power (zero_lt_one.trans_le hX)]
  change
    3 * C * d * ((m : ℝ) * ((51 / 50) * b ^ 5 / |ρ.im| ^ 2)) =
      153 / 50 * (C * (d * b ^ 5)) * ((m : ℝ) / |ρ.im| ^ 2)
  ring

end PseudoPrime.PrimeTestBounds.MillerRabin
