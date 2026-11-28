/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianCutoffPhase
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSmoothedTail
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiSign100RH
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100Bounds
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhasePairs644

/-! # Signed integral estimate for the first compressed Gaussian cell -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private def selected : Fin 4 → Fin 29 :=
  ![0, 1, 2, 4]

private def credit : Fin 4 → ℝ :=
  ![2.55, 1.025, 0.5, 0.425]

private theorem selected_inj : Function.Injective selected := by decide

private theorem selected_credit_of_interval (hRH : RiemannHypothesis) {y : ℝ}
    (hy : y ∈ Set.Icc (663 / 2 : ℝ) (1329 / 4)) (i : Fin 4) {ρ : ℂ} (hz : riemannZeta ρ = 0)
    (hr : ρ.re = 1 / 2)
    (h :
      |ρ.im| ∈
        Set.Icc (AnalyticNumberTheory.RiemannZeta.lowZero100Lower (selected i) : ℝ)
          ((AnalyticNumberTheory.RiemannZeta.lowZero100Lower (selected i) : ℝ) + 1 / 100)) :
    let z := AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm (y ^ 2) ρ
    credit i ≤ z.re + ‖z‖ := by
  fin_cases i
  · exact
      gaussian_credit_ordinate_1 hRH hy hz hr
        (by
          change
            |ρ.im| ∈ Set.Icc (↑(14473 / 1024 : ℚ) : ℝ) ((↑(14473 / 1024 : ℚ) : ℝ) + 1 / 100) at h
          simpa only [Rat.cast_div, Rat.cast_ofNat] using h)
  · exact
      gaussian_credit_ordinate_2 hRH hy hz hr
        (by
          change |ρ.im| ∈ Set.Icc (↑(10763 / 512 : ℚ) : ℝ) ((↑(10763 / 512 : ℚ) : ℝ) + 1 / 100) at h
          simpa only [Rat.cast_div, Rat.cast_ofNat] using h)
  · exact
      gaussian_credit_ordinate_3 hRH hy hz hr
        (by
          change
            |ρ.im| ∈ Set.Icc (↑(25611 / 1024 : ℚ) : ℝ) ((↑(25611 / 1024 : ℚ) : ℝ) + 1 / 100) at h
          simpa only [Rat.cast_div, Rat.cast_ofNat] using h)
  · exact
      gaussian_credit_ordinate_5 hRH hy hz hr
        (by
          change
            |ρ.im| ∈ Set.Icc (↑(33725 / 1024 : ℚ) : ℝ) ((↑(33725 / 1024 : ℚ) : ℝ) + 1 / 100) at h
          simpa only [Rat.cast_div, Rat.cast_ofNat] using h)

private theorem credit_sum : (∑ i : Fin 4, credit i) = 4.5 := by
  norm_num only [credit, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, add_zero]

/-- The certified enclosure for the absolute ordinate at a low-zero index. -/
noncomputable def gaussianLowOrdinateBox (i : Fin 29) : Set ℝ :=
  Set.Icc (AnalyticNumberTheory.RiemannZeta.lowZero100Lower i : ℝ)
    ((AnalyticNumberTheory.RiemannZeta.lowZero100Lower i : ℝ) + 1 / 100)

/-- Using the certified low-ordinate enclosures, pointwise credit bounds for selected
positive ordinates give twice their total credit in the smoothed log error. -/
theorem gaussian_log_error_low_zero_credit {ι : Type*} [Fintype ι] (hRH : RiemannHypothesis) {y : ℝ}
    (hy : 1 < y) (select : ι → Fin 29) (hinj : Function.Injective select) (credit : ι → ℝ)
    (hcredit :
      ∀ i : ι,
        ∀ ρ : ℂ,
          riemannZeta ρ = 0 →
            ρ.re = 1 / 2 →
              |ρ.im| ∈ gaussianLowOrdinateBox (select i) →
                let z := AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm (y ^ 2) ρ
                credit i ≤ z.re + ‖z‖) :
    2 * (∑ i, credit i) - y / 20 - 21 / 20 ≤ gaussianLogError (Real.log (y ^ 2)) := by
  classical
  obtain ⟨g, hm, hp, _, hz, hlo, hhi⟩ := AnalyticNumberTheory.RiemannZeta.low_zero_100_exists
  let p := fun i : ι ↦ criticalPoint (g (select i))
  let n := fun i : ι ↦ criticalPoint (-g (select i))
  have hpi : Function.Injective p := critical_injective.comp (hm.injective.comp hinj)
  have hni : Function.Injective n :=
    critical_injective.comp (neg_injective.comp (hm.injective.comp hinj))
  have hd : Disjoint (Finset.univ.image p) (Finset.univ.image n) := by
    apply Finset.disjoint_left.mpr
    intro ρ hP hN
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hP
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hN
    have h := critical_injective (hi.trans hj.symm)
    linarith only [h, hp (select i), hp (select j)]
  have h :=
    gaussian_log_error_of_credit hRH (one_lt_pow₀ hy (by decide : 2 ≠ 0))
      (Finset.univ.image p ∪ Finset.univ.image n)
  dsimp only at h
  rw [Real.sqrt_sq (zero_le_one.trans hy.le), Finset.sum_union hd,
    Finset.sum_image (fun _ _ _ _ he ↦ hpi he), Finset.sum_image (fun _ _ _ _ he ↦ hni he)] at h
  have hb (i : ι) :
    g (select i) ∈
      Set.Icc (AnalyticNumberTheory.RiemannZeta.lowZero100Lower (select i) : ℝ)
        ((AnalyticNumberTheory.RiemannZeta.lowZero100Lower (select i) : ℝ) + 1 / 100) :=
    ⟨hlo _, hhi _⟩
  have hP :=
    Finset.sum_le_sum (s := Finset.univ)
      (fun i _ ↦
        hcredit i (p i) (hz (select i)) (critical_re _)
          (by
            rw [critical_im, abs_of_pos (hp (select i))]; exact hb i))
  have hN :=
    Finset.sum_le_sum (s := Finset.univ)
      (fun i _ ↦
        hcredit i (n i)
          (by
            change riemannZeta (criticalPoint (-g (select i))) = 0
            rw [← critical_conj, riemannZeta_conj]
            exact (congrArg (starRingEnd ℂ) (hz (select i))).trans (map_zero _))
          (critical_re _)
          (by
            rw [critical_im, abs_neg, abs_of_pos (hp (select i))]; exact hb i))
  linarith only [h, hP, hN]

/-- The certified first, second, third and fifth positive zeros and their
conjugates give enough signed credit for the lower bound at the cutoff. -/
theorem gaussian_first_cutoff_lower (hRH : RiemannHypothesis) {y : ℝ}
    (hy : y ∈ Set.Icc (663 / 2 : ℝ) (1329 / 4)) : -9 ≤ gaussianLogError (Real.log (y ^ 2)) := by
  have hy₀ : 1 < y := by linarith only [hy.1]
  have h :=
    gaussian_log_error_low_zero_credit hRH hy₀ selected selected_inj credit
      (fun i ρ hz hr hmem ↦ selected_credit_of_interval hRH hy i hz hr hmem)
  rw [credit_sum] at h
  linarith only [h, hy.2]

/-- Under RH, the signed principal Abel integral is at most 0.053 for
radii in `[663 / 2, 1329 / 4]`, which covers the three K137 comparisons. -/
theorem gaussian_first_integral_le (hRH : RiemannHypothesis) {y : ℝ}
    (hy : y ∈ Set.Icc (663 / 2 : ℝ) (1329 / 4)) :
    (-4 : ℝ) *
        (∫ t in y ^ 2..y ^ 2 * Real.exp (21 / 8),
          (Chebyshev.psi t - t) * deriv (quarterWeight656 (y ^ 2)) t) ≤
      0.053 := by
  exact gaussian_first_tail_of_cutoff hRH hy.1 (gaussian_first_cutoff_lower hRH hy)

end PseudoPrime.PrimeTestBounds.MillerRabin
