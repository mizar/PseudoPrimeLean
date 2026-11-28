/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianDirectCutoff
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianDirectMiddleCells
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianDirectMiddleRange
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131TailWitness

/-! # Assembly of the direct Gaussian witness ranges -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Join the K141, K156 and K186 witnesses at the common rational scale
with the already proved uniform prefix. The three kernel witnesses are supplied at
their respective closed ranges. -/
theorem uniform_gaussian_of_direct {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hL : 663 ≤ Real.log n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (h141 :
      Real.log n ∈ Set.Icc (42410 : ℝ) 400000 →
        HasRejectingPrime n ((gaussianDirectScale * Real.log n) ^ 2))
    (h156 :
      Real.log n ∈ Set.Icc (400000 : ℝ) 7000000 →
        HasRejectingPrime n ((gaussianDirectScale * Real.log n) ^ 2))
    (h186 : 6300000 ≤ Real.log n → HasRejectingPrime n ((gaussianDirectScale * Real.log n) ^ 2)) :
    HasRejectingPrime n (gaussianWitnessCutoff (Real.log n)) := by
  apply uniform_gaussian_of_final_ranges hn ho hu hL hGRH
  · intro hmid
    apply HasRejectingPrime.mono _ (gaussian_direct_cutoff hmid.1)
    by_cases h : Real.log n ≤ 400000
    · exact h141 ⟨hmid.1, h⟩
    exact h156 ⟨le_of_not_ge h, hmid.2⟩
  · intro hhigh
    exact
      (h186 hhigh).mono
        (gaussian_direct_cutoff ((by norm_num only : (42410 : ℝ) ≤ 6300000).trans hhigh))

/-- Combine the direct uniform-triple witnesses with the quarter witness for
the low and nonuniform composites. -/
theorem gaussian_criterion_of_direct {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (h141 :
      UniformKorseltTriple n →
        Real.log n ∈ Set.Icc (42410 : ℝ) 400000 →
        HasRejectingPrime n ((gaussianDirectScale * Real.log n) ^ 2))
    (h156 :
      UniformKorseltTriple n →
        Real.log n ∈ Set.Icc (400000 : ℝ) 7000000 →
        HasRejectingPrime n ((gaussianDirectScale * Real.log n) ^ 2))
    (h186 :
      UniformKorseltTriple n →
        6300000 ≤ Real.log n → HasRejectingPrime n ((gaussianDirectScale * Real.log n) ^ 2)) :
    (∀ p : ℕ,
        p.Prime →
          (p : ℝ) ≤ gaussianWitnessCutoff (Real.log n) →
          PrimeTest.StrongMillerRabinPass n (p : ZMod n)) ↔
      n.Prime := by
  exact
    gaussian_criterion_of_uniform_witness hn ho hGRH
      (fun hu hL ↦ uniform_gaussian_of_direct hn ho hu hL hGRH (h141 hu) (h156 hu) (h186 hu))

/-- A positive residual contradicted by passage of all prime bases gives a witness. -/
private theorem direct_witness_of_pos {n : ℕ} {X g : ℝ} (hg : 0 < g)
    (hpass :
      (∀ p : ℕ, p.Prime → (p : ℝ) ≤ X → PrimeTest.StrongMillerRabinPass n (p : ZMod n)) → g ≤ 0) :
    HasRejectingPrime n X := by
  by_contra hnone
  refine (not_lt_of_ge (hpass ?_)) hg
  intro p hp hb
  by_contra h
  exact hnone ⟨p, hp, hb, h⟩

/-- Connect the certified K141 cells to a rejecting prime at the shared cutoff
when the analytic residual is nonpositive under passage of all prime bases. -/
theorem gaussian_k141_witness_of_cells {n : ℕ} {f f' f'' : ℝ → ℝ}
    (hL : Real.log n ∈ Set.Icc (42410 : ℝ) 400000)
    (hc : ∀ i, (gaussianK141Cells i).AnalyticBounds f f' f'')
    (hnonpos :
      (∀ p : ℕ,
          p.Prime →
            (p : ℝ) ≤ (gaussianDirectScale * Real.log n) ^ 2 →
            PrimeTest.StrongMillerRabinPass n (p : ZMod n)) →
        f (Real.log ((gaussianDirectScale * Real.log n) ^ 2)) ≤ 0) :
    HasRejectingPrime n ((gaussianDirectScale * Real.log n) ^ 2) := by
  exact
    direct_witness_of_pos
      (zero_lt_one.trans (gaussian_k141_residual_gt_one hc (gaussian_k141_log_range hL))) hnonpos

/-- Connect the certified K156 cells to a rejecting prime at the shared cutoff
when the analytic residual is nonpositive under passage of all prime bases. -/
theorem gaussian_k156_witness_of_cells {n : ℕ} {f f' f'' : ℝ → ℝ}
    (hL : Real.log n ∈ Set.Icc (400000 : ℝ) 7000000)
    (hc : ∀ i, (gaussianK156Cells i).AnalyticBounds f f' f'')
    (hnonpos :
      (∀ p : ℕ,
          p.Prime →
            (p : ℝ) ≤ (gaussianDirectScale * Real.log n) ^ 2 →
            PrimeTest.StrongMillerRabinPass n (p : ZMod n)) →
        f (Real.log ((gaussianDirectScale * Real.log n) ^ 2)) ≤ 0) :
    HasRejectingPrime n ((gaussianDirectScale * Real.log n) ^ 2) := by
  exact
    direct_witness_of_pos
      (zero_lt_one.trans (gaussian_k156_residual_gt_one hc (gaussian_k156_log_range hL))) hnonpos

/-- Assemble the criterion from positive residuals on the two middle ranges,
their analytic implications under passage, and the high-range witness. -/
theorem gaussian_criterion_of_mid_residuals {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (f141 f156 : ℝ → ℝ)
    (h141 : ∀ t ∈ Set.Icc (20 : ℝ) 25, 0 < f141 t)
    (h156 : ∀ t ∈ Set.Icc (24 : ℝ) (121 / 4), 0 < f156 t)
    (hpass141 :
      UniformKorseltTriple n →
        Real.log n ∈ Set.Icc (42410 : ℝ) 400000 →
        (∀ p : ℕ,
          p.Prime →
            (p : ℝ) ≤ (gaussianDirectScale * Real.log n) ^ 2 →
            PrimeTest.StrongMillerRabinPass n (p : ZMod n)) →
        f141 (Real.log ((gaussianDirectScale * Real.log n) ^ 2)) ≤ 0)
    (hpass156 :
      UniformKorseltTriple n →
        Real.log n ∈ Set.Icc (400000 : ℝ) 7000000 →
        (∀ p : ℕ,
          p.Prime →
            (p : ℝ) ≤ (gaussianDirectScale * Real.log n) ^ 2 →
            PrimeTest.StrongMillerRabinPass n (p : ZMod n)) →
        f156 (Real.log ((gaussianDirectScale * Real.log n) ^ 2)) ≤ 0)
    (hhigh :
      UniformKorseltTriple n →
        6300000 ≤ Real.log n → HasRejectingPrime n ((gaussianDirectScale * Real.log n) ^ 2)) :
    (∀ p : ℕ,
        p.Prime →
          (p : ℝ) ≤ gaussianWitnessCutoff (Real.log n) →
          PrimeTest.StrongMillerRabinPass n (p : ZMod n)) ↔
      n.Prime := by
  exact
    gaussian_criterion_of_direct hn ho hGRH
      (fun hu hL ↦ direct_witness_of_pos (h141 _ (gaussian_k141_log_range hL)) (hpass141 hu hL))
      (fun hu hL ↦ direct_witness_of_pos (h156 _ (gaussian_k156_log_range hL)) (hpass156 hu hL))
      hhigh

end PseudoPrime.PrimeTestBounds.MillerRabin
