/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197FirstWitness
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197FirstWitness
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197PowerBounds
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Main1165
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Abel1165
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Boundary163
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Gain148
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Gain162

/-! # K197 witnesses across the million-point Chebyshev cutoff -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem witness1165_of_gain {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {U s a T P C B D : ℝ}
    {K : Finset ℕ} (hK : K ⊆ fixedPowers663.erase (337 ^ 2)) (hL : Real.log n ≤ U)
    (hm : k197Slope s ≤ 0) (ha₀ : (995 : ℝ) ≤ a) (hT : ∀ r : ℝ, a ≤ r → T ≤ gaussianTheta197 r)
    (hvs : 1.02 ≤ s) (hP : P ≤ T / s + 0.0178 - 0.00146)
    (hC : ∀ r : ℝ, a ≤ r → 4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ C)
    (hmargin :
      0 ≤
        (15.0472769 : ℝ) + (-0.0065 - B) + P + k197Slope s * (U / 2) + D - 4 * 0.0069 - C - 0.0013 +
          0.00059) :
    let r := s * Real.log n / 2
    r ∈ Set.Ico a 1165 →
      (-4 * (Chebyshev.psi (r ^ 2) - r ^ 2) * quarterWeight656 (r ^ 2) (r ^ 2) ≤ B) →
      ((∀ n ∈ K, r ^ 2 < (n : ℝ)) ∧
        D ≤ ∑ n ∈ K, 4 * (ArithmeticFunction.vonMangoldt n * quarterWeight656 (r ^ 2) n)) →
      ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  intro r hra hb hgain
  have hr₀ : r ∈ Set.Ico 995 1165 := ⟨ha₀.trans hra.1, hra.2⟩
  apply uniform_witness_of_pair_false hn ho hu (X := r ^ 2)
  intro p q k _ _ _ a b c ha hb' hc hp hq hk hlev ht hsmall
  have hs₁ : 1 ≤ s := (by norm_num only : (1 : ℝ) ≤ 1.02).trans hvs
  have hscale : r / s = Real.log n / 2 := by
    dsimp only [r]
    apply (div_eq_iff (zero_lt_one.trans_le hs₁).ne').mpr
    ring
  have hlevel : Real.log p + Real.log q + Real.log k = 4 * (Real.log n / 2) := by
    linarith only [hlev]
  have hpa l hl hcut := (hsmall l hl hcut).1
  have hpb l hl hcut := (hsmall l hl hcut).2.1
  have hpc l hl hcut := (hsmall l hl hcut).2.2
  have hspos : 0 < s := (by norm_num only : (0 : ℝ) < 1.02).trans_le hvs
  have hθ := div_le_div_of_nonneg_right (hT r hra.1) hspos.le
  have hpole : (0.0178 : ℝ) ≤ gaussianNegPole197 / r := by
    apply (le_div_iff₀ ((by norm_num only : (0 : ℝ) < 995).trans_le hr₀.1)).mpr
    linarith only [hr₀.2.le, gaussian_neg_pole_lower_197]
  have hcost : P + 0.00146 ≤ gaussianTheta197 r / s + gaussianNegPole197 / r := by
    linarith only [hP, hθ, hpole]
  have hshift₀ :=
    shift_forward_of_refl ha hb' hc hG.riemann ((by norm_num only : (328 : ℝ) ≤ 995).trans hr₀.1)
      (by
        rw [mul_div_assoc, hscale]; exact hlevel)
      ht hpa hpb hpc hcost (gaussian_joint_to1165 hG.riemann ⟨hr₀.1, hr₀.2.le⟩)
  have hshift :
    P ≤
      (gaussianShiftedForward197 a r + gaussianShiftedForward197 b r +
          gaussianShiftedForward197 c r) +
        gaussianHalfCoeff197 * r := by
    linarith only [hshift₀]
  have hcond := hC r hra.1
  rw [hscale] at hcond
  have hmain :=
    gaussian_k197_principal_to1165 hG.riemann
      ⟨(by norm_num only : (663 / 2 : ℝ) ≤ 995).trans hr₀.1, hr₀.2.le⟩ hb
  have hcompare :=
    retained_comparison_of_gain ha hb' hc hp hq hk hG (C := D)
      ((by norm_num only : (336.8 : ℝ) ≤ 995).trans hr₀.1) K hK hgain.1 hlevel ht hpa hpb hpc
      hgain.2
  have hrF : r ∈ Set.Icc 328 1165 := ⟨(by norm_num only : (328 : ℝ) ≤ 995).trans hr₀.1, hr₀.2.le⟩
  refine
    mid_pair_false_with_abel (a := a) (b := b) (c := c) hG (B := -0.0065 - B) (P := D)
      ((by norm_num only : (336.8 : ℝ) ≤ 995).trans hr₀.1)
      (gaussian_abel_tail_to1165 hG.riemann ⟨hr₀.1, hr₀.2.le⟩) hcond (k197_main_reflect_to1165 hrF)
      (gaussian_k197_reflect_credit_to1165 hrF) ht hpa hpb hpc hcompare ?_ hshift
      (wide_linear_lower (Real.log_natCast_nonneg n) hL hs₁ hm) ?_
  · simpa only [sub_eq_add_neg, add_assoc] using hmain
  · linarith only [hmargin]

private theorem witness_below1165 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {U s a T P C B : ℝ}
    (hL : Real.log n ≤ U) (hm : k197Slope s ≤ 0) (ha₀ : (995 : ℝ) ≤ a)
    (hT : ∀ r : ℝ, a ≤ r → T ≤ gaussianTheta197 r) (hvs : 1.02 ≤ s)
    (hP : P ≤ T / s + 0.0178 - 0.00146)
    (hC : ∀ r : ℝ, a ≤ r → 4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ C)
    (hmargin :
      0 ≤
        (15.0472769 : ℝ) + (-0.0065 - B) + P + k197Slope s * (U / 2) - 4 * 0.0069 - C - 0.0013 +
          0.00059) :
    let r := s * Real.log n / 2
    r ∈ Set.Ico a 1165 →
      (-4 * (Chebyshev.psi (r ^ 2) - r ^ 2) * quarterWeight656 (r ^ 2) (r ^ 2) ≤ B) →
      ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  intro r hra hb
  apply
    witness1165_of_gain hn ho hu hG (D := 0) (K := ∅) (Finset.empty_subset _) hL hm ha₀ hT hvs hP hC
      (by linarith only [hmargin]) hra hb
  exact ⟨fun n hn ↦ (Finset.notMem_empty n hn).elim, by rw [Finset.sum_empty]⟩

/-- Under GRH, a uniform Korselt triple in compressed cell 144 has a prime
rejecting base within the squared certified radius by the signed Chebyshev bound. -/
theorem gaussian_k197_row144_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (7759 / 4) (7823 / 4)) :
    let r := (513263932131 / 500000000000 : ℝ) * Real.log n / 2
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    witness_below1165 hn ho hu hG (s := 513263932131 / 500000000000) (B := 0.20332) (a := 9956 / 10)
      (P := -1.369670) hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from9956 (s := 1.02) hr le_rfl).1) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ (conductors_from9956 hr (by norm_num only)).2)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 991226) (B := 1007647) (E := 543) (a := 9956 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell144 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in compressed cell 145 has a prime
rejecting base within the squared certified radius by the signed Chebyshev bound. -/
theorem gaussian_k197_row145_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (7823 / 4) (7951 / 4)) :
    let r := (256659997727 / 250000000000 : ℝ) * Real.log n / 2
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    witness_below1165 hn ho hu hG (s := 256659997727 / 250000000000) (B := 0.09952) (a :=
      10039 / 10) (P := -1.360836) hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from10039 (s := 1.02) hr le_rfl).1) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ (conductors_from10039 hr (by norm_num only)).2)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 1007866) (B := 1041118) (E := 268) (a := 10039 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell145 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in compressed cell 146 has a prime
rejecting base within the squared certified radius by the signed Chebyshev bound. -/
theorem gaussian_k197_row146_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (7951 / 4) (8015 / 4)) :
    let r := (102685894319 / 100000000000 : ℝ) * Real.log n / 2
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    witness_below1165 hn ho hu hG (s := 102685894319 / 100000000000) (B := 0.16074) (a :=
      10205 / 10) (P := -1.343515) hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from10205 (s := 1.02) hr le_rfl).1) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ (conductors_from10205 hr (by norm_num only)).2)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 1041561) (B := 1058398) (E := 440) (a := 10205 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell146 hx hy)
        (by norm_num only)

private theorem witness_part147_0 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (8015 / 4) (8075 / 4)) :
    let r := (32092682933 / 31250000000 : ℝ) * Real.log n / 2
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    witness1165_of_gain hn ho hu hG (s := 32092682933 / 31250000000) (D := 0.03454) (B := 0.23191)
      (a := 10288 / 10) (P := -1.335032) retainedSquares148_subset hL.2
      (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from10288 (s := 1.02) hr le_rfl).1) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ (conductors_from10288 hr (by norm_num only)).2)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 1058617) (B := 1074527) (E := 640) (a := 10288 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_part147_0 hx hy)
        (by norm_num only)
  · have hr : (32092682933 / 31250000000 : ℝ) * Real.log n / 2 ∈ Set.Icc 1028 1046 :=
      ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
    exact ⟨fun _ hn ↦ retainedSquares148_above hr hn, retained_squares_gain148 hr⟩

private theorem witness_part147_1 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (8075 / 4) (8079 / 4)) :
    let r := (32092682933 / 31250000000 : ℝ) * Real.log n / 2
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    witness1165_of_gain hn ho hu hG (s := 32092682933 / 31250000000) (D := 0.03454) (B := 0.20537)
      (a := 10365 / 10) (P := -1.327387) retainedSquares148_subset hL.2
      (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from10365 (s := 1.02) hr le_rfl).1) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ (conductors_from10365 hr (by norm_num only)).2)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 1074526) (B := 1075592) (E := 571) (a := 10365 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_part147_1 hx hy)
        (by norm_num only)
  · have hr : (32092682933 / 31250000000 : ℝ) * Real.log n / 2 ∈ Set.Icc 1028 1046 :=
      ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
    exact ⟨fun _ hn ↦ retainedSquares148_above hr hn, retained_squares_gain148 hr⟩

/-- Under GRH, a uniform Korselt triple in compressed cell 147 has a prime
rejecting base within the squared certified radius using the retained squares. -/
theorem gaussian_k197_row147_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (8015 / 4) (8079 / 4)) :
    let r := (32092682933 / 31250000000 : ℝ) * Real.log n / 2
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases h0 : Real.log n ≤ 8075 / 4
  · exact witness_part147_0 hn ho hu hG ⟨hL.1, h0⟩
  exact witness_part147_1 hn ho hu hG ⟨le_of_not_ge h0, hL.2⟩

private theorem witness_part148_0 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (8079 / 4) (8131 / 4)) :
    let r := (513535554317 / 500000000000 : ℝ) * Real.log n / 2
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    witness1165_of_gain hn ho hu hG (s := 513535554317 / 500000000000) (D := 0.03454) (B := 0.20667)
      (a := 10372 / 10) (P := -1.326561) retainedSquares148_subset hL.2
      (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from10372 (s := 1.02) hr le_rfl).1) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ (conductors_from10372 hr (by norm_num only)).2)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 1075811) (B := 1089706) (E := 575) (a := 10372 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_part148_0 hx hy)
        (by norm_num only)
  · have hr : (513535554317 / 500000000000 : ℝ) * Real.log n / 2 ∈ Set.Icc 1028 1046 :=
      ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
    exact ⟨fun _ hn ↦ retainedSquares148_above hr hn, retained_squares_gain148 hr⟩

private theorem witness_part148_1 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (8131 / 4) (8135 / 4)) :
    let r := (513535554317 / 500000000000 : ℝ) * Real.log n / 2
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    witness1165_of_gain hn ho hu hG (s := 513535554317 / 500000000000) (D := 0.03454) (B := 0.23894)
      (a := 10438 / 10) (P := -1.320087) retainedSquares148_subset hL.2
      (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from10438 (s := 1.02) hr le_rfl).1) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ (conductors_from10438 hr (by norm_num only)).2)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 1089705) (B := 1090778) (E := 669) (a := 10438 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_part148_1 hx hy)
        (by norm_num only)
  · have hr : (513535554317 / 500000000000 : ℝ) * Real.log n / 2 ∈ Set.Icc 1028 1046 :=
      ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
    exact ⟨fun _ hn ↦ retainedSquares148_above hr hn, retained_squares_gain148 hr⟩

private theorem witness_part148_2 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (8135 / 4) (8139 / 4)) :
    let r := (513535554317 / 500000000000 : ℝ) * Real.log n / 2
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    witness1165_of_gain hn ho hu hG (s := 513535554317 / 500000000000) (D := 0.03454) (B := 0.23344)
      (a := 10444 / 10) (P := -1.319502) retainedSquares148_subset hL.2
      (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from10444 (s := 1.02) hr le_rfl).1) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ (conductors_from10444 hr (by norm_num only)).2)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 1090777) (B := 1091851) (E := 654) (a := 10444 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_part148_2 hx hy)
        (by norm_num only)
  · have hr : (513535554317 / 500000000000 : ℝ) * Real.log n / 2 ∈ Set.Icc 1028 1046 :=
      ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
    exact ⟨fun _ hn ↦ retainedSquares148_above hr hn, retained_squares_gain148 hr⟩

private theorem witness_part148_3 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (8139 / 4) (8143 / 4)) :
    let r := (513535554317 / 500000000000 : ℝ) * Real.log n / 2
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    witness1165_of_gain hn ho hu hG (s := 513535554317 / 500000000000) (D := 0.03454) (B := 0.16947)
      (a := 10449 / 10) (P := -1.319015) retainedSquares148_subset hL.2
      (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from10449 (s := 1.02) hr le_rfl).1) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ (conductors_from10449 hr (by norm_num only)).2)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 1091850) (B := 1092924) (E := 475) (a := 10449 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_part148_3 hx hy)
        (by norm_num only)
  · have hr : (513535554317 / 500000000000 : ℝ) * Real.log n / 2 ∈ Set.Icc 1028 1046 :=
      ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
    exact ⟨fun _ hn ↦ retainedSquares148_above hr hn, retained_squares_gain148 hr⟩

/-- Under GRH, a uniform Korselt triple in compressed cell 148 has a prime
rejecting base within the squared certified radius using the retained squares. -/
theorem gaussian_k197_row148_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (8079 / 4) (8143 / 4)) :
    let r := (513535554317 / 500000000000 : ℝ) * Real.log n / 2
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases h0 : Real.log n ≤ 8131 / 4
  · exact witness_part148_0 hn ho hu hG ⟨hL.1, h0⟩
  by_cases h1 : Real.log n ≤ 8135 / 4
  · exact witness_part148_1 hn ho hu hG ⟨le_of_not_ge h0, h1⟩
  by_cases h2 : Real.log n ≤ 8139 / 4
  · exact witness_part148_2 hn ho hu hG ⟨le_of_not_ge h1, h2⟩
  exact witness_part148_3 hn ho hu hG ⟨le_of_not_ge h2, hL.2⟩

/-- Under GRH, a uniform Korselt triple in compressed cell 149 has a prime
rejecting base within the squared certified radius by the signed Chebyshev bound. -/
theorem gaussian_k197_row149_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (8143 / 4) (8207 / 4)) :
    let r := (1027174746727 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    witness_below1165 hn ho hu hG (s := 1027174746727 / 1000000000000) (B := 0.15119) (a :=
      10455 / 10) (P := -1.318300) hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from10455 (s := 1.02) hr le_rfl).1) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ (conductors_from10455 hr (by norm_num only)).2)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 1093144) (B := 1110396) (E := 424) (a := 10455 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_part149_0 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in compressed cell 150 has a prime
rejecting base within the squared certified radius by the signed Chebyshev bound. -/
theorem gaussian_k197_row150_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (8207 / 4) (8271 / 4)) :
    let r := (102727680611 / 100000000000 : ℝ) * Real.log n / 2
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    witness_below1165 hn ho hu hG (s := 102727680611 / 100000000000) (B := 0.09481) (a :=
      10538 / 10) (P := -1.310138) hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from10538 (s := 1.02) hr le_rfl).1) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ (conductors_from10538 hr (by norm_num only)).2)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 1110615) (B := 1128006) (E := 268) (a := 10538 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_part150_0 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in compressed cell 151 has a prime
rejecting base within the squared certified radius by the signed Chebyshev bound. -/
theorem gaussian_k197_row151_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (8271 / 4) (8335 / 4)) :
    let r := (513688661787 / 500000000000 : ℝ) * Real.log n / 2
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    witness_below1165 hn ho hu hG (s := 513688661787 / 500000000000) (B := 0.09126) (a :=
      10621 / 10) (P := -1.302091) hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from10621 (s := 1.02) hr le_rfl).1) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ (conductors_from10621 hr (by norm_num only)).2)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 1128225) (B := 1145754) (E := 260) (a := 10621 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_part151_0 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in compressed cell 152 has a prime
rejecting base within the squared certified radius by the signed Chebyshev bound. -/
theorem gaussian_k197_row152_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (8335 / 4) (8399 / 4)) :
    let r := (1027476334773 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    witness_below1165 hn ho hu hG (s := 1027476334773 / 1000000000000) (B := 0.13303) (a :=
      10705 / 10) (P := -1.294049) hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from10705 (s := 1.02) hr le_rfl).1) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ (conductors_from10705 hr (by norm_num only)).2)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 1145974) (B := 1163641) (E := 382) (a := 10705 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_part152_0 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in compressed cell 153 has a prime
rejecting base within the squared certified radius by the signed Chebyshev bound. -/
theorem gaussian_k197_row153_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (8399 / 4) (8527 / 4)) :
    let r := (1027573874267 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    witness_below1165 hn ho hu hG (s := 1027573874267 / 1000000000000) (B := 0.00035) (a :=
      10788 / 10) (P := -1.286203) hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from10788 (s := 1.02) hr le_rfl).1) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ (conductors_from10788 hr (by norm_num only)).2)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 1163861) (B := 1199607) (E := 1) (a := 10788 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_part153_0 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in compressed cell 154 has a prime
rejecting base within the squared certified radius by the signed Chebyshev bound. -/
theorem gaussian_k197_row154_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (8527 / 4) (8591 / 4)) :
    let r := (205552934231 / 200000000000 : ℝ) * Real.log n / 2
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    witness_below1165 hn ho hu hG (s := 205552934231 / 200000000000) (B := 0.00375) (a :=
      10954 / 10) (P := -1.270808) hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from10954 (s := 1.02) hr le_rfl).1) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ (conductors_from10954 hr (by norm_num only)).2)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 1200051) (B := 1218134) (E := 11) (a := 10954 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_part154_0 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in compressed cell 155 has a prime
rejecting base within the squared certified radius by the signed Chebyshev bound. -/
theorem gaussian_k197_row155_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (8591 / 4) (8655 / 4)) :
    let r := (513928996283 / 500000000000 : ℝ) * Real.log n / 2
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    witness_below1165 hn ho hu hG (s := 513928996283 / 500000000000) (B := 0.08141) (a :=
      11037 / 10) (P := -1.263252) hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from11037 (s := 1.02) hr le_rfl).1) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ (conductors_from11037 hr (by norm_num only)).2)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 1218354) (B := 1236575) (E := 241) (a := 11037 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_part155_0 hx hy)
        (by norm_num only)

private theorem witness_part156_0 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (8655 / 4) (8687 / 4)) :
    let r := (128493746297 / 125000000000 : ℝ) * Real.log n / 2
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    witness_below1165 hn ho hu hG (s := 128493746297 / 125000000000) (B := 0.09319) (a :=
      11121 / 10) (P := -1.255702) hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from11121 (s := 1.02) hr le_rfl).1) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ (conductors_from11121 hr (by norm_num only)).2)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 1236796) (B := 1245959) (E := 278) (a := 11121 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_part156_0 hx hy)
        (by norm_num only)

private theorem witness_part156_1 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (8687 / 4) (8719 / 4)) :
    let r := (128493746297 / 125000000000 : ℝ) * Real.log n / 2
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    witness_below1165 hn ho hu hG (s := 128493746297 / 125000000000) (B := 0.08651) (a :=
      11162 / 10) (P := -1.252108) hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from11162 (s := 1.02) hr le_rfl).1) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ (conductors_from11162 hr (by norm_num only)).2)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 1245958) (B := 1255155) (E := 259) (a := 11162 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_part156_1 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in compressed cell 156 has a prime
rejecting base within the squared certified radius across both signed bounds. -/
theorem gaussian_k197_row156_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (8655 / 4) (8719 / 4)) :
    let r := (128493746297 / 125000000000 : ℝ) * Real.log n / 2
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases hm : Real.log n ≤ 8687 / 4
  · exact witness_part156_0 hn ho hu hG ⟨hL.1, hm⟩
  exact witness_part156_1 hn ho hu hG ⟨le_of_not_ge hm, hL.2⟩

/-- Under GRH, a uniform Korselt triple in compressed cell 157 has a prime
rejecting base within the squared certified radius by the signed Chebyshev bound. -/
theorem gaussian_k197_row157_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (8719 / 4) (8783 / 4)) :
    let r := (205608126853 / 200000000000 : ℝ) * Real.log n / 2
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    witness_below1165 hn ho hu hG (s := 205608126853 / 200000000000) (B := 0.05224) (a :=
      11204 / 10) (P := -1.248338) hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from11204 (s := 1.02) hr le_rfl).1) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ (conductors_from11204 hr (by norm_num only)).2)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 1255376) (B := 1273874) (E := 157) (a := 11204 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_part157_0 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in compressed cell 158 has a prime
rejecting base within the squared certified radius by the signed Chebyshev bound. -/
theorem gaussian_k197_row158_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (8783 / 4) (8847 / 4)) :
    let r := (1028130013039 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    witness_below1165 hn ho hu hG (s := 1028130013039 / 1000000000000) (B := 0.00034) (a :=
      11287 / 10) (P := -1.241058) hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from11287 (s := 1.02) hr le_rfl).1) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ (conductors_from11287 hr (by norm_num only)).2)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 1274095) (B := 1292731) (E := 1) (a := 11287 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_part158_0 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in compressed cell 159 has a prime
rejecting base within the squared certified radius by the signed Chebyshev bound. -/
theorem gaussian_k197_row159_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (8847 / 4) (8911 / 4)) :
    let r := (1028218134669 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    witness_below1165 hn ho hu hG (s := 1028218134669 / 1000000000000) (B := 0.02689) (a :=
      11370 / 10) (P := -1.233868) hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from11370 (s := 1.02) hr le_rfl).1) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ (conductors_from11370 hr (by norm_num only)).2)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 1292952) (B := 1311727) (E := 82) (a := 11370 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_part159_0 hx hy)
        (by norm_num only)

private theorem witness_part160_0 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (8911 / 4) (8943 / 4)) :
    let r := (205661005263 / 200000000000 : ℝ) * Real.log n / 2
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    witness_below1165 hn ho hu hG (s := 205661005263 / 200000000000) (B := 0.06965) (a :=
      11454 / 10) (P := -1.226679) hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from11454 (s := 1.02) hr le_rfl).1) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ (conductors_from11454 hr (by norm_num only)).2)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 1311948) (B := 1321389) (E := 214) (a := 11454 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_part160_0 hx hy)
        (by norm_num only)

private theorem witness_part160_1 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (8943 / 4) (8975 / 4)) :
    let r := (205661005263 / 200000000000 : ℝ) * Real.log n / 2
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    witness_below1165 hn ho hu hG (s := 205661005263 / 200000000000) (B := 0.04087) (a :=
      11495 / 10) (P := -1.223258) hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from11495 (s := 1.02) hr le_rfl).1) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ (conductors_from11495 hr (by norm_num only)).2)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 1321388) (B := 1330862) (E := 126) (a := 11495 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_part160_1 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in compressed cell 160 has a prime
rejecting base within the squared certified radius across both signed bounds. -/
theorem gaussian_k197_row160_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (8911 / 4) (8975 / 4)) :
    let r := (205661005263 / 200000000000 : ℝ) * Real.log n / 2
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases hm : Real.log n ≤ 8943 / 4
  · exact witness_part160_0 hn ho hu hG ⟨hL.1, hm⟩
  exact witness_part160_1 hn ho hu hG ⟨le_of_not_ge hm, hL.2⟩

/-- Under GRH, a uniform Korselt triple in compressed cell 161 has a prime
rejecting base within the squared certified radius by the signed Chebyshev bound. -/
theorem gaussian_k197_row161_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (8975 / 4) (9007 / 4)) :
    let r := (514195357179 / 500000000000 : ℝ) * Real.log n / 2
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    witness_below1165 hn ho hu hG (s := 514195357179 / 500000000000) (B := 0.06786) (a :=
      11537 / 10) (P := -1.219664) hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from11537 (s := 1.02) hr le_rfl).1) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ (conductors_from11537 hr (by norm_num only)).2)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 1331083) (B := 1340593) (E := 210) (a := 11537 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_part161_0 hx hy)
        (by norm_num only)

private theorem rescale_conductor_1165 {r s C : ℝ} (hs : 0 < s)
    (h : 4 * (r / 1.02) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ C) :
    4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ C * 1.02 / s := by
  calc
    _ = (4 * (r / 1.02) * (quarterKernel656.transform (r ^ 2)⁻¹).re) * 1.02 / s := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h (by norm_num only)) hs.le

private theorem witness_part162_0 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (9007 / 4) (9037 / 4)) :
    let r := (205686623013 / 200000000000 : ℝ) * Real.log n / 2
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    witness1165_of_gain hn ho hu hG (s := 205686623013 / 200000000000) (D := 0.0136) (B := 0.08791)
      (a := 11578 / 10) (P := -1.216229) retainedPowers162_subset hL.2
      (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from11578 (s := 1.02) hr le_rfl).1) (by norm_num only)
      (by norm_num only)
      (fun _ hr ↦
        rescale_conductor_1165 (by norm_num only) (conductors_from11578 (s := 1.02) hr le_rfl).2)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 1340702) (B := 1349649) (E := 273) (a := 11578 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_part162_0 hx hy)
        (by norm_num only)
  · have hr : (205686623013 / 200000000000 : ℝ) * Real.log n / 2 ∈ Set.Icc 1157 1162.1 :=
      ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
    exact ⟨fun _ hn ↦ retainedPowers162_above hr hn, retained_powers_gain162 hr⟩

private theorem witness_part162_1 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (9037 / 4) (9039 / 4)) :
    let r := (205686623013 / 200000000000 : ℝ) * Real.log n / 2
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    witness1165_of_gain hn ho hu hG (s := 205686623013 / 200000000000) (D := 0.0136) (B := 0.09724)
      (a := 11617 / 10) (P := -1.213029) retainedPowers162_subset hL.2
      (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from11617 (s := 1.02) hr le_rfl).1) (by norm_num only)
      (by norm_num only)
      (fun _ hr ↦
        rescale_conductor_1165 (by norm_num only) (conductors_from11617 (s := 1.02) hr le_rfl).2)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 1349648) (B := 1350247) (E := 303) (a := 11617 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_part162_1 hx hy)
        (by norm_num only)
  · have hr : (205686623013 / 200000000000 : ℝ) * Real.log n / 2 ∈ Set.Icc 1157 1162.1 :=
      ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
    exact ⟨fun _ hn ↦ retainedPowers162_above hr hn, retained_powers_gain162 hr⟩

/-- Under GRH, a uniform Korselt triple in compressed cell 162 has a prime
rejecting base within the squared certified radius across both signed bounds. -/
theorem gaussian_k197_row162_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (9007 / 4) (9039 / 4)) :
    let r := (205686623013 / 200000000000 : ℝ) * Real.log n / 2
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases hm : Real.log n ≤ 9037 / 4
  · exact witness_part162_0 hn ho hu hG ⟨hL.1, hm⟩
  exact witness_part162_1 hn ho hu hG ⟨le_of_not_ge hm, hL.2⟩

private theorem witness_part163_0 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (9039 / 4) (9047 / 4)) :
    let r := (514237612213 / 500000000000 : ℝ) * Real.log n / 2
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    witness_below1165 hn ho hu hG (s := 514237612213 / 500000000000) (B := 0.0908) (a := 11620 / 10)
      (P := -1.212734) hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from11620 (s := 1.02) hr le_rfl).1) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ (conductors_from11620 hr (by norm_num only)).2)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 1350356) (B := 1352748) (E := 283) (a := 11620 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_part163_0 hx hy)
        (by norm_num only)

private theorem witness_part163_1 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (9047 / 4) (9055 / 4)) :
    let r := (514237612213 / 500000000000 : ℝ) * Real.log n / 2
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    witness_below1165 hn ho hu hG (s := 514237612213 / 500000000000) (B := 0.08815) (a :=
      11630 / 10) (P := -1.211919) hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from11630 (s := 1.02) hr le_rfl).1) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ (conductors_from11630 hr (by norm_num only)).2)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 1352747) (B := 1355142) (E := 275) (a := 11630 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_part163_1 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in compressed cell 163 has a prime
rejecting base within the squared certified radius across both signed bounds. -/
theorem gaussian_k197_row163_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (9039 / 4) (9055 / 4)) :
    let r := (514237612213 / 500000000000 : ℝ) * Real.log n / 2
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases hm : Real.log n ≤ 9047 / 4
  · exact witness_part163_0 hn ho hu hG ⟨hL.1, hm⟩
  exact witness_part163_1 hn ho hu hG ⟨le_of_not_ge hm, hL.2⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
