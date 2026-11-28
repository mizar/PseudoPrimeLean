/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseTail644
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeightCounting
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalZeros
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiSign100RH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCount100RH

/-! # Conjugate pairing of the 29 low ordinates for the section 122 phase kernel -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Negating the ordinate conjugates the section 122 kernel because all
fixed coefficients are real. The two inverse powers retain their signs. -/
theorem quarter_phase_kernel_conj_644 (t : ℝ) :
    (starRingEnd ℂ) (quarterPhaseKernel644 t) = quarterPhaseKernel644 (-t) := by
  unfold quarterPhaseKernel644
  simp only [map_add, map_sum, map_mul, map_div₀, map_pow, map_ofNat, map_one, Complex.conj_ofReal,
    Complex.conj_I, ← Complex.exp_conj, Complex.ofReal_neg, mul_neg, neg_mul]

/-- The real part of the oscillating kernel is even in the ordinate.
A conjugate pair thus contributes twice its positive-ordinate value. -/
theorem quarter_phase_re_even_644 (x t : ℝ) :
    (Complex.exp (Complex.I * ((x * (-t) : ℝ) : ℂ)) * quarterPhaseKernel644 (-t)).re =
      (Complex.exp (Complex.I * ((x * t : ℝ) : ℂ)) * quarterPhaseKernel644 t).re := by
  rw [← quarter_phase_kernel_conj_644, mul_neg, Complex.ofReal_neg, mul_neg]
  rw [←
    show (starRingEnd ℂ) (Complex.I * ((x * t : ℝ) : ℂ)) = -(Complex.I * ((x * t : ℝ) : ℂ)) by
      simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, neg_mul]]
  rw [Complex.exp_conj, ← map_mul, Complex.conj_re]

private noncomputable def criticalPoint (t : ℝ) : ℂ :=
  ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I

private theorem critical_im (t : ℝ) : (criticalPoint t).im = t := by
  simp only [criticalPoint, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add]

private theorem critical_re (t : ℝ) : (criticalPoint t).re = 1 / 2 := by
  simp only [criticalPoint, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]

private theorem critical_conj (t : ℝ) : (starRingEnd ℂ) (criticalPoint t) = criticalPoint (-t) := by
  simp only [criticalPoint, map_add, Complex.conj_ofReal, map_mul, Complex.conj_I,
    Complex.ofReal_neg, mul_neg, neg_mul]

private theorem critical_injective : Function.Injective criticalPoint := by
  intro t u h
  exact (critical_im t).symm.trans ((congrArg Complex.im h).trans (critical_im u))

/-- Under RH the complete height-100 ledger is exactly the two images of
the 29 certified ordinates. This uses completeness for positive heights,
and conjugation gives the negative half without duplicating any entries. -/
private theorem low_ledger (hRH : RiemannHypothesis) {g : Fin 29 → ℝ} (hm : StrictMono g)
    (hp : ∀ i, 0 < g i) (hu : ∀ i, g i ≤ 100) (hz : ∀ i, riemannZeta (criticalPoint (g i)) = 0) :
    let P := Finset.univ.image (fun i ↦ criticalPoint (g i))
    let N := Finset.univ.image (fun i ↦ criticalPoint (-g i))
    AnalyticNumberTheory.RiemannZeta.zerosUpTo 100 = P ∪ N := by
  classical
  intro P N
  have hc := AnalyticNumberTheory.RiemannZeta.count_100_eq_58_of_RH hRH
  have h := AnalyticNumberTheory.RiemannZeta.critical_zeros_complete_simple hRH hc.le g hm hp hu hz
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at h
  have hmem (ρ : ℂ) :=
    AnalyticNumberTheory.RiemannZeta.mem_zerosUpTo (ρ := ρ) (by norm_num only : (0 : ℝ) ≤ 100)
  ext ρ
  constructor
  · intro hr
    obtain ⟨hζ, hre, hhi⟩ := (hmem ρ).mp hr
    obtain ⟨_, i, hi | hi⟩ := section104_low_pair_complete hRH (g := g) h.1 h.2 (ρ := ρ) hζ hre hhi
    · exact
        Finset.mem_union_left N
          (Finset.mem_image.mpr
            ⟨i, Finset.mem_univ _, by
              simpa only [criticalPoint, Complex.ofReal_div, Complex.ofReal_one,
                Complex.ofReal_ofNat] using hi.symm⟩)
    · exact
        Finset.mem_union_right P
          (Finset.mem_image.mpr
            ⟨i, Finset.mem_univ _, by
              simpa only [criticalPoint, Complex.ofReal_div, Complex.ofReal_one,
                Complex.ofReal_ofNat] using hi.symm⟩)
  · intro hr
    rcases Finset.mem_union.mp hr with hP | hN
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hP
      exact
        (hmem _).mpr
          ⟨hz i, by
            rw [critical_re]; norm_num only, by
            rw [critical_im, abs_of_pos (hp i)]; exact hu i⟩
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hN
      refine
        (hmem _).mpr
          ⟨?_, by
            rw [critical_re]; norm_num only, ?_⟩
      · rw [← critical_conj, riemannZeta_conj, hz, map_zero]
      · rw [critical_im, abs_neg, abs_of_pos (hp i)]
        exact hu i

/-- Under RH the height-100 phase sum with multiplicities is the sum of
twice the real contributions from the 29 certified positive ordinates. -/
theorem quarter_phase_low_pairs_644 (hRH : RiemannHypothesis) {g : Fin 29 → ℝ} (hm : StrictMono g)
    (hp : ∀ i, 0 < g i) (hu : ∀ i, g i ≤ 100)
    (hz : ∀ i, riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 0) (x : ℝ) :
    (∑ ρ ∈ AnalyticNumberTheory.RiemannZeta.zerosUpTo 100,
        (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
          (Complex.exp (Complex.I * ((x * ρ.im : ℝ) : ℂ)) * quarterPhaseKernel644 ρ.im).re) =
      2 *
        ∑ i : Fin 29,
          (Complex.exp (Complex.I * ((x * g i : ℝ) : ℂ)) * quarterPhaseKernel644 (g i)).re := by
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
    simp only [n, critical_im, Nat.cast_one, one_mul, quarter_phase_re_even_644]

/-- The 29 positive ordinates and the high-zero budget bound every complete
finite height truncation at or above 100. Each truncation includes all low pairs. -/
theorem quarter_phase_truncation_lower_644 (hRH : RiemannHypothesis) {g : Fin 29 → ℝ}
    (hm : StrictMono g) (hp : ∀ i, 0 < g i) (hu : ∀ i, g i ≤ 100)
    (hz : ∀ i, riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 0) {T : ℝ} (hT : 100 ≤ T)
    (x B : ℝ)
    (hB :
      B ≤
        2 *
          ∑ i : Fin 29,
            (Complex.exp (Complex.I * ((x * g i : ℝ) : ℂ)) * quarterPhaseKernel644 (g i)).re) :
    B - 0.0061952 ≤
      ∑ ρ ∈ AnalyticNumberTheory.RiemannZeta.zerosUpTo T,
        (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
          (Complex.exp (Complex.I * ((x * ρ.im : ℝ) : ℂ)) * quarterPhaseKernel644 ρ.im).re := by
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
    quarter_phase_finite_lower_644 hRH _ (fun ρ hρ ↦ ((hmem ρ).mp hρ).1)
      (fun ρ hρ ↦ ((hmem ρ).mp hρ).2.1) x B
  dsimp only
  rw [he, quarter_phase_low_pairs_644 hRH hm hp hu hz]
  exact hB

/-- The existing 29 certified ordinate brackets suffice to bound all
section 122 finite height truncations. Once the positive-ordinate sum is
bounded for these brackets, no further zero data below height 100 is needed. -/
theorem quarter_phase_brackets_644 (hRH : RiemannHypothesis) :
    ∃ g : Fin 29 → ℝ,
      AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g ∧
        AnalyticNumberTheory.RiemannZeta.LowZero100UpperBounds g ∧
        ∀ (T : ℝ),
          100 ≤ T →
            ∀ (x B : ℝ),
              B ≤
                  (2 *
                    ∑ i : Fin 29,
                      (Complex.exp (Complex.I * ((x * g i : ℝ) : ℂ)) *
                          quarterPhaseKernel644 (g i)).re) →
                B - 0.0061952 ≤
                  ∑ ρ ∈ AnalyticNumberTheory.RiemannZeta.zerosUpTo T,
                    (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
                      (Complex.exp (Complex.I * ((x * ρ.im : ℝ) : ℂ)) *
                          quarterPhaseKernel644 ρ.im).re := by
  obtain ⟨g, hm, hp, hu, hz, hlo, hhi⟩ := AnalyticNumberTheory.RiemannZeta.low_zero_100_exists
  exact
    ⟨g, hlo, hhi, fun _ hT x B hB ↦ quarter_phase_truncation_lower_644 hRH hm hp hu hz hT x B hB⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
