/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterLowPhase
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalPhase
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.UnifiedZeroExhaustion
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipal600

/-! # Complete conjugate-pair phase sum and Abel action -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational coefficient at the negative ordinate is the complex conjugate
of the coefficient at the positive ordinate. -/
theorem section99_rat_coeff_neg (t : ℝ) :
    section99RatCoeff (-t) = (starRingEnd ℂ) (section99RatCoeff t) := by
  simp only [section99RatCoeff, section104Numerator, map_mul, map_div₀, map_pow, map_add, map_sub,
    map_neg, map_ofNat, map_one, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg, mul_neg,
    neg_mul]

/-- The shifted pole coefficient also respects conjugation of the ordinate. -/
theorem section99_pole_coeff_neg (t : ℝ) :
    section99PoleCoeff (-t) = (starRingEnd ℂ) (section99PoleCoeff t) := by
  simp only [section99PoleCoeff, map_mul, map_div₀, map_pow, map_add, map_ofNat,
    Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg, mul_neg, neg_mul]

/-- The real normalized phase term is even in the ordinate. -/
theorem section99_phase_re_neg {r : ℝ} (hr : 0 < r) (t : ℝ) :
    let F (y : ℝ) :=
      let ρ := (1 / 2 : ℂ) + (y : ℂ) * Complex.I
      ((((r ^ 2 : ℝ) : ℂ) ^ ρ / (Real.sqrt (r ^ 2) : ℂ)) * section99PhaseKernel ρ).re
    F (-t) = F t := by
  dsimp only
  rw [section99_phase_re_split hr, section99_phase_re_split hr, section99_rat_coeff_neg,
    section99_pole_coeff_neg]
  have h (x : ℝ) :
    Complex.exp (((-t * x : ℝ) : ℂ) * Complex.I) =
      (starRingEnd ℂ) (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)) := by
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
    rw [neg_mul, Complex.ofReal_neg, neg_mul, mul_neg]
  rw [h, h, ← map_mul, ← map_mul, Complex.conj_re, Complex.conj_re]

/-- The positive and negative images of the ordinate list are disjoint.
The signed sum over their union equals twice the positive-ordinate sum
when all selected zeros have multiplicity one. -/
theorem quarter_low_phase_pairs {r : ℝ} (hr : 0 < r) (g : Fin 29 → ℝ) (hg : StrictMono g)
    (hp : ∀ i, 0 < g i)
    (hm :
      ∀ i,
        AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity
            ((1 / 2 : ℂ) + (g i : ℂ) * Complex.I) =
          1)
    (hn :
      ∀ i,
        AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity
            ((1 / 2 : ℂ) + ((-g i : ℝ) : ℂ) * Complex.I) =
          1) :
    let p (i : Fin 29) := (1 / 2 : ℂ) + (g i : ℂ) * Complex.I
    let q (i : Fin 29) := (1 / 2 : ℂ) + ((-g i : ℝ) : ℂ) * Complex.I
    ∑ ρ ∈ (Finset.univ.image p ∪ Finset.univ.image q),
        ((AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ) *
            (((r ^ 2 : ℝ) : ℂ) ^ ρ / (Real.sqrt (r ^ 2) : ℂ)) *
            section99PhaseKernel ρ).re =
      quarterLowPhase g r := by
  intro p q
  have hi (y : ℝ) : ((1 / 2 : ℂ) + (y : ℂ) * Complex.I).im = y := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_one, ← Complex.ofReal_div]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.I_re, mul_one, zero_mul, add_zero, zero_add]
  have hpi (i : Fin 29) : (p i).im = g i := hi _
  have hqi (i : Fin 29) : (q i).im = -g i := hi _
  have hdis : Disjoint (Finset.univ.image p) (Finset.univ.image q) := by
    apply Finset.disjoint_left.mpr
    intro ρ hρ hρ'
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hρ
    obtain ⟨j, _, h⟩ := Finset.mem_image.mp hρ'
    have he := congrArg Complex.im h
    rw [hqi, hpi] at he
    linarith only [hp i, hp j, he]
  rw [Finset.sum_union hdis, Finset.sum_image, Finset.sum_image, ← Finset.sum_add_distrib]
  · unfold quarterLowPhase
    apply Finset.sum_congr rfl
    intro i _
    change
      ((AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity (p i) : ℂ) * _ * _).re +
          ((AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity (q i) : ℂ) * _ * _).re =
        _
    rw [show AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity (p i) = 1 from hm i,
      show AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity (q i) = 1 from hn i]
    simp only [Nat.cast_one, one_mul]
    dsimp only [p, q]
    have hneg := section99_phase_re_neg hr (g i)
    dsimp only at hneg
    rw [hneg, two_mul]
  · intro i _ j _ he
    exact hg.injective (neg_injective (by simpa only [hqi] using congrArg Complex.im he))
  · intro i _ j _ he
    exact hg.injective (by simpa only [hpi] using congrArg Complex.im he)

/-- If a finite truncation contains every low conjugate pair, its normalized
phase sum is at least the low phase minus the already certified high tail. -/
theorem quarter_phase_lower_of_pairs (hRH : RiemannHypothesis) {r : ℝ} (hr : 0 < r) (S : Finset ℂ)
    (hz : ∀ ρ ∈ S, riemannZeta ρ = 0) (hre : ∀ ρ ∈ S, 0 ≤ ρ.re) (g : Fin 29 → ℝ) (hg : StrictMono g)
    (hp : ∀ i, 0 < g i) (hh : ∀ i, g i ≤ 100)
    (hcover :
      (AnalyticNumberTheory.RiemannZeta.zerosUpTo 100).filter (fun ρ ↦ 0 < ρ.im) ⊆
        Finset.univ.image (fun i ↦ (1 / 2 : ℂ) + (g i : ℂ) * Complex.I))
    (hm :
      ∀ i,
        AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity
            ((1 / 2 : ℂ) + (g i : ℂ) * Complex.I) =
          1)
    (hS :
      ∀ i,
        ((1 / 2 : ℂ) + (g i : ℂ) * Complex.I) ∈ S ∧
          ((1 / 2 : ℂ) + ((-g i : ℝ) : ℂ) * Complex.I) ∈ S) :
    quarterLowPhase g r - 0.0059776 ≤
      ∑ ρ ∈ S,
        ((AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ) *
            (((r ^ 2 : ℝ) : ℂ) ^ ρ / (Real.sqrt (r ^ 2) : ℂ)) *
            section99PhaseKernel ρ).re := by
  let p (i : Fin 29) := (1 / 2 : ℂ) + (g i : ℂ) * Complex.I
  let q (i : Fin 29) := (1 / 2 : ℂ) + ((-g i : ℝ) : ℂ) * Complex.I
  have hi (y : ℝ) : ((1 / 2 : ℂ) + (y : ℂ) * Complex.I).im = y := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_one, ← Complex.ofReal_div]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.I_re, mul_one, zero_mul, add_zero, zero_add]
  have hpi (i : Fin 29) : |(p i).im| ≤ 100 := by
    change |((1 / 2 : ℂ) + (g i : ℂ) * Complex.I).im| ≤ 100
    rw [hi, abs_of_pos (hp i)]
    exact hh i
  have hqi (i : Fin 29) : |(q i).im| ≤ 100 := by
    change |((1 / 2 : ℂ) + ((-g i : ℝ) : ℂ) * Complex.I).im| ≤ 100
    rw [hi, abs_neg, abs_of_pos (hp i)]
    exact hh i
  have he : S.filter (fun ρ ↦ |ρ.im| ≤ 100) = Finset.univ.image p ∪ Finset.univ.image q := by
    ext ρ
    constructor
    · intro hρ
      obtain ⟨hs, ht⟩ := Finset.mem_filter.mp hρ
      obtain ⟨i, he | he⟩ := (section104_low_pair_complete hRH hcover hm (hz ρ hs) (hre ρ hs) ht).2
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, he.symm⟩)
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, he.symm⟩)
    · intro hρ
      rcases Finset.mem_union.mp hρ with h | h
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
        exact Finset.mem_filter.mpr ⟨(hS i).1, hpi i⟩
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
        exact Finset.mem_filter.mpr ⟨(hS i).2, hqi i⟩
  have hn (i : Fin 29) :=
    (section104_low_pair_complete hRH hcover hm (hz (q i) (hS i).2) (hre (q i) (hS i).2) (hqi i)).1
  have hlow := quarter_low_phase_pairs hr g hg hp hm hn
  have hhigh :=
    section99_phase_high_lower hRH (S.filter (fun ρ ↦ ¬|ρ.im| ≤ 100))
      (fun ρ h ↦ hz ρ (Finset.mem_filter.mp h).1) (fun ρ h ↦ hre ρ (Finset.mem_filter.mp h).1)
      (fun ρ h ↦ lt_of_not_ge (Finset.mem_filter.mp h).2) (sq_pos_of_pos hr)
  rw [← Finset.sum_filter_add_sum_filter_not S (fun ρ ↦ |ρ.im| ≤ 100), he, hlow]
  linarith only [hhigh]

/-- The expanding rectangles eventually contain all low pairs of a certified
ordinate list. Their normalized phase sums then inherit the low phase lower
bound with the uniform height-100 tail loss. -/
theorem quarter_rect_phase_lower (hRH : RiemannHypothesis) {r : ℝ} (hr : 0 < r) (g : Fin 29 → ℝ)
    (hg : StrictMono g) (hp : ∀ i, 0 < g i) (hh : ∀ i, g i ≤ 100)
    (hzero : ∀ i, riemannZeta ((1 / 2 : ℂ) + (g i : ℂ) * Complex.I) = 0)
    (hcover :
      (AnalyticNumberTheory.RiemannZeta.zerosUpTo 100).filter (fun ρ ↦ 0 < ρ.im) ⊆
        Finset.univ.image (fun i ↦ (1 / 2 : ℂ) + (g i : ℂ) * Complex.I))
    (hm :
      ∀ i,
        AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity
            ((1 / 2 : ℂ) + (g i : ℂ) * Complex.I) =
          1) :
    ∀ᶠ k : ℕ in Filter.atTop,
      quarterLowPhase g r - 0.0059776 ≤
        ∑
          ρ ∈
            (AnalyticNumberTheory.RiemannZeta.riemannZetaZerosInAnyRectangle
                  (AnalyticNumberTheory.RiemannZeta.unifiedRectangleLower k)
                  (AnalyticNumberTheory.RiemannZeta.unifiedTauRectangleUpper 2 k)).filter
              (fun ρ ↦ ¬ρ.re < 0),
          ((AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ) *
              (((r ^ 2 : ℝ) : ℂ) ^ ρ / (Real.sqrt (r ^ 2) : ℂ)) *
              section99PhaseKernel ρ).re := by
  have hmem {t : ℝ} (hz : riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) = 0) (ht : |t| ≤ 100) :
    (1 / 2 : ℂ) + (t : ℂ) * Complex.I ∈ AnalyticNumberTheory.RiemannZeta.zerosUpTo 100 := by
    apply (AnalyticNumberTheory.RiemannZeta.mem_zerosUpTo (by norm_num only)).mpr
    refine ⟨hz, ?_, ?_⟩
    · rw [← Complex.ofReal_ofNat, ← Complex.ofReal_one, ← Complex.ofReal_div]
      norm_num only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero]
    · rw [← Complex.ofReal_ofNat, ← Complex.ofReal_one, ← Complex.ofReal_div]
      simpa only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_one, zero_mul, add_zero, zero_add] using ht
  have hn (i : Fin 29) : riemannZeta ((1 / 2 : ℂ) + ((-g i : ℝ) : ℂ) * Complex.I) = 0 := by
    have he := congrArg (starRingEnd ℂ) (hzero i)
    rw [← riemannZeta_conj, map_zero] at he
    simpa only [map_add, map_div₀, map_one, map_ofNat, map_mul, Complex.conj_ofReal, Complex.conj_I,
      Complex.ofReal_neg, mul_neg, neg_mul] using he
  filter_upwards [AnalyticNumberTheory.RiemannZeta.zerosUpTo_eventually_in_unified
      (show (0 : ℝ) ≤ 100 by norm_num only)] with
    k hk
  refine quarter_phase_lower_of_pairs hRH hr _ ?_ ?_ g hg hp hh hcover hm ?_
  · intro ρ hρ
    exact
      (AnalyticNumberTheory.RiemannZeta.mem_riemannZetaZerosInAnyRectangle_iff.mp
          (Finset.mem_filter.mp hρ).1).2
  · intro ρ hρ
    exact not_lt.mp (Finset.mem_filter.mp hρ).2
  · intro i
    have ht : |g i| ≤ 100 := by
      rw [abs_of_pos (hp i)]; exact hh i
    exact
      ⟨hk (hmem (hzero i) ht),
        hk
          (hmem (hn i)
            (by
              rw [abs_neg]; exact ht))⟩

/-- The complete low phase sum bounds the nontrivial-zero Abel action from
below after subtracting the high-zero tail and the physical-cutoff error. -/
theorem quarter_abel_of_low_phase (hRH : RiemannHypothesis) {r : ℝ} (hr : 292 ≤ r) (g : Fin 29 → ℝ)
    (hg : StrictMono g) (hp : ∀ i, 0 < g i) (hh : ∀ i, g i ≤ 100)
    (hz : ∀ i, riemannZeta ((1 / 2 : ℂ) + (g i : ℂ) * Complex.I) = 0)
    (hcover :
      (AnalyticNumberTheory.RiemannZeta.zerosUpTo 100).filter (fun ρ ↦ 0 < ρ.im) ⊆
        Finset.univ.image (fun i ↦ (1 / 2 : ℂ) + (g i : ℂ) * Complex.I))
    (hm :
      ∀ i,
        AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity
            ((1 / 2 : ℂ) + (g i : ℂ) * Complex.I) =
          1) :
    quarterLowPhase g r - 0.0064276 ≤
      section99AbelAction (r ^ 2)
        (fun t ↦ (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re) := by
  have h := quarter_rect_phase_lower hRH (by linarith only [hr] : 0 < r) g hg hp hh hz hcover hm
  linarith only [section99_nontrivial_of_phase hRH hr h]

end PseudoPrime.PrimeTestBounds.MillerRabin
