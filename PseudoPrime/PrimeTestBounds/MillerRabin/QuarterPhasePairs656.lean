/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseTransfer656
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseTail656
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseRemainder656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhasePairs644
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseTransfer656

/-! # Complete finite truncations of the section 132 phase sum -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Negating the ordinate conjugates the section 132 kernel because all
fixed coefficients are real. The two inverse powers retain their signs. -/
theorem quarter_phase_kernel_conj_656 (t : ℝ) :
    (starRingEnd ℂ) (quarterPhaseKernel656 t) = quarterPhaseKernel656 (-t) := by
  unfold quarterPhaseKernel656
  simp only [map_add, map_sum, map_mul, map_div₀, map_pow, map_ofNat, map_one, Complex.conj_ofReal,
    Complex.conj_I, ← Complex.exp_conj, Complex.ofReal_neg, mul_neg, neg_mul]

/-- The real part of the oscillating kernel is even in the ordinate.
A conjugate pair thus contributes twice its positive-ordinate value. -/
theorem quarter_phase_re_even_656 (x t : ℝ) :
    (Complex.exp (Complex.I * ((x * (-t) : ℝ) : ℂ)) * quarterPhaseKernel656 (-t)).re =
      (Complex.exp (Complex.I * ((x * t : ℝ) : ℂ)) * quarterPhaseKernel656 t).re := by
  rw [← quarter_phase_kernel_conj_656, mul_neg, Complex.ofReal_neg, mul_neg]
  rw [←
    show (starRingEnd ℂ) (Complex.I * ((x * t : ℝ) : ℂ)) = -(Complex.I * ((x * t : ℝ) : ℂ)) by
      simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, neg_mul]]
  rw [Complex.exp_conj, ← map_mul, Complex.conj_re]

/-- Under RH the height-100 phase sum with multiplicities is the sum of
twice the real contributions from the 29 certified positive ordinates. -/
theorem quarter_phase_low_pairs_656 (hRH : RiemannHypothesis) {g : Fin 29 → ℝ} (hm : StrictMono g)
    (hp : ∀ i, 0 < g i) (hu : ∀ i, g i ≤ 100)
    (hz : ∀ i, riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 0) (x : ℝ) :
    (∑ ρ ∈ AnalyticNumberTheory.RiemannZeta.zerosUpTo 100,
        (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
          (Complex.exp (Complex.I * ((x * ρ.im : ℝ) : ℂ)) * quarterPhaseKernel656 ρ.im).re) =
      2 *
        ∑ i : Fin 29,
          (Complex.exp (Complex.I * ((x * g i : ℝ) : ℂ)) * quarterPhaseKernel656 (g i)).re := by
  classical
  let p := fun i : Fin 29 ↦ criticalPoint (g i)
  let n := fun i : Fin 29 ↦ criticalPoint (-g i)
  have hip : Function.Injective p := critical_injective.comp hm.injective
  have hin : Function.Injective n := critical_injective.comp (neg_injective.comp hm.injective)
  have hd : Disjoint (Finset.univ.image p) (Finset.univ.image n) := by
    apply Finset.disjoint_left.mpr
    intro ρ hP hN
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hP
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hN
    have h := critical_injective (hi.trans hj.symm)
    linarith only [h, hp i, hp j]
  have hc := AnalyticNumberTheory.RiemannZeta.count_100_eq_58_of_RH hRH
  have hmP :=
    (AnalyticNumberTheory.RiemannZeta.critical_zeros_complete_simple hRH hc.le g hm hp hu hz).2
  have hmN (i : Fin 29) :
    AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity (n i) = 1 := by
    have hne : p i ≠ 1 := by
      intro h
      have hi := congrArg Complex.im h
      change (criticalPoint (g i)).im = (1 : ℂ).im at hi
      rw [critical_im, Complex.one_im] at hi
      exact (hp i).ne' hi
    change AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity (criticalPoint (-g i)) = 1
    rw [← critical_conj, AnalyticNumberTheory.RiemannZeta.multiplicity_conj hne]
    exact hmP i
  rw [low_ledger hRH hm hp hu hz]
  change (∑ ρ ∈ Finset.univ.image p ∪ Finset.univ.image n, _) = _
  rw [Finset.sum_union hd, Finset.sum_image (fun _ _ _ _ h ↦ hip h),
    Finset.sum_image (fun _ _ _ _ h ↦ hin h), two_mul]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    rw [show AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity (p i) = 1 from hmP i]
    simp only [p, critical_im, Nat.cast_one, one_mul]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [hmN i]
    simp only [n, critical_im, Nat.cast_one, one_mul, quarter_phase_re_even_656]

/-- The 29 positive ordinates and the high-zero budget bound every complete
finite height truncation at or above 100. Each truncation includes all low pairs. -/
theorem quarter_phase_truncation_lower_656 (hRH : RiemannHypothesis) {g : Fin 29 → ℝ}
    (hm : StrictMono g) (hp : ∀ i, 0 < g i) (hu : ∀ i, g i ≤ 100)
    (hz : ∀ i, riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 0) {T : ℝ} (hT : 100 ≤ T)
    (x B : ℝ)
    (hB :
      B ≤
        2 *
          ∑ i : Fin 29,
            (Complex.exp (Complex.I * ((x * g i : ℝ) : ℂ)) * quarterPhaseKernel656 (g i)).re) :
    B - 0.006592787 ≤
      ∑ ρ ∈ AnalyticNumberTheory.RiemannZeta.zerosUpTo T,
        (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
          (Complex.exp (Complex.I * ((x * ρ.im : ℝ) : ℂ)) * quarterPhaseKernel656 ρ.im).re := by
  classical
  have h100 : (0 : ℝ) ≤ 100 := by norm_num only
  have hmem (ρ : ℂ) := AnalyticNumberTheory.RiemannZeta.mem_zerosUpTo (ρ := ρ) (h100.trans hT)
  have he :
    (AnalyticNumberTheory.RiemannZeta.zerosUpTo T).filter (fun ρ ↦ |ρ.im| ≤ 100) =
      AnalyticNumberTheory.RiemannZeta.zerosUpTo 100 := by
    ext ρ
    rw [Finset.mem_filter, hmem ρ, AnalyticNumberTheory.RiemannZeta.mem_zerosUpTo h100]
    constructor
    · exact fun h ↦ ⟨h.1.1, h.1.2.1, h.2⟩
    · exact fun h ↦ ⟨⟨h.1, h.2.1, h.2.2.trans hT⟩, h.2.2⟩
  apply
    quarter_phase_finite_lower_656 hRH _ (fun ρ hρ ↦ ((hmem ρ).mp hρ).1)
      (fun ρ hρ ↦ ((hmem ρ).mp hρ).2.1) x B
  dsimp only
  rw [he, quarter_phase_low_pairs_656 hRH hm hp hu hz]
  exact hB

/-- Under RH, every complete truncation above height 100 satisfies the
section 132 phase bound after subtracting the allotted remainder. -/
theorem quarter_phase_truncations_656 (hRH : RiemannHypothesis) {r T : ℝ} (hr : r ∈ Set.Icc 322 328)
    (hT : 100 ≤ T) :
    -(201 / 40000 : ℝ) ≤
      (∑ ρ ∈ AnalyticNumberTheory.RiemannZeta.zerosUpTo T,
          (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
            (Complex.exp (Complex.I * ((2 * Real.log r * ρ.im : ℝ) : ℂ)) *
                quarterPhaseKernel656 ρ.im).re) -
        2665 / 1000000 := by
  obtain ⟨g, hm, hp, hu, hz, hlo, hhi⟩ := AnalyticNumberTheory.RiemannZeta.low_zero_100_exists
  have h := quarter_phase_head_656 hlo hhi hr
  have ht :=
    quarter_phase_truncation_lower_656 hRH hm hp hu hz hT (2 * Real.log r)
      (pairedPhase g (fun i ↦ quarterPhaseKernel656 (g i)) (2 * Real.log r)) le_rfl
  linarith only [h, ht]

/-- For every complete height truncation, the phase sum less the scalar
section 132 remainder satisfies the uniform lower bound. -/
theorem quarter_phase_with_rem_656 (hRH : RiemannHypothesis) {r T : ℝ} (hr : r ∈ Set.Icc 322 328)
    (hT : 100 ≤ T) :
    -(201 / 40000 : ℝ) ≤
      (∑ ρ ∈ AnalyticNumberTheory.RiemannZeta.zerosUpTo T,
          (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
            (Complex.exp (Complex.I * ((2 * Real.log r * ρ.im : ℝ) : ℂ)) *
                quarterPhaseKernel656 ρ.im).re) -
        quarterPhaseRem656 r := by
  exact
    (quarter_phase_truncations_656 hRH hr hT).trans
      (sub_le_sub_left (quarter_phase_rem_le_656 hr.1) _)

private theorem phase_re_ge_neg_norm (x t : ℝ) :
    -‖quarterPhaseKernel656 t‖ ≤
      (Complex.exp (Complex.I * ((x * t : ℝ) : ℂ)) * quarterPhaseKernel656 t).re := by
  have h :=
    (abs_le.mp
        (Complex.abs_re_le_norm
          (Complex.exp (Complex.I * ((x * t : ℝ) : ℂ)) * quarterPhaseKernel656 t))).1
  have hn : ‖Complex.exp (Complex.I * ((x * t : ℝ) : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp only [Complex.mul_re, Complex.I_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero,
      Real.exp_zero]
  simpa only [norm_mul, hn, one_mul] using h

/-- Under RH, the common principal kernel has a phase-independent lower
bound of minus one fortieth at every complete height truncation above 100. -/
theorem quarter_phase_uniform_lower_656 (hRH : RiemannHypothesis) {T : ℝ} (hT : 100 ≤ T) (x : ℝ) :
    (-1 / 40 : ℝ) ≤
      ∑ ρ ∈ AnalyticNumberTheory.RiemannZeta.zerosUpTo T,
        (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
          (Complex.exp (Complex.I * ((x * ρ.im : ℝ) : ℂ)) * quarterPhaseKernel656 ρ.im).re := by
  obtain ⟨g, hm, hp, hu, hz, hlo, hhi⟩ := AnalyticNumberTheory.RiemannZeta.low_zero_100_exists
  have hs :=
    Finset.sum_le_sum (s := Finset.univ)
      (fun i (_ : i ∈ Finset.univ) ↦
        (neg_le_neg (phase_kernel_norm (g i))).trans (phase_re_ge_neg_norm x (g i)))
  rw [Finset.sum_neg_distrib] at hs
  have hlow :
    (-0.018 : ℝ) ≤
      2 *
        ∑ i : Fin 29,
          (Complex.exp (Complex.I * ((x * g i : ℝ) : ℂ)) * quarterPhaseKernel656 (g i)).re := by
    linarith only [hs, quarter_low_phase_mass_656 hlo hhi]
  have h := quarter_phase_truncation_lower_656 hRH hm hp hu hz hT x _ hlow
  linarith only [h]

end PseudoPrime.PrimeTestBounds.MillerRabin
