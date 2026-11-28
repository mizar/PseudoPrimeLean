/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Witness
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131TailPartition

import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131EulerTail

/-! # K131 witnesses for logarithms from 8000 through 42410 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH an odd uniform Korselt triple with logarithm in [8000, 42410]
has a prime rejecting base within the old Gaussian envelope. -/
theorem uniform_k131_tail_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (8000 : ℝ) 42410) :
    HasRejectingPrime n
      (max 2
        (max ((1 / 4 : ℝ) * Real.log n ^ 2)
          ((9090 / 33659 : ℝ) * Real.log n ^ 2 -
            8 * Real.log n * Real.exp (-(Real.log n / 1000000) ^ 2)))) := by
  obtain ⟨lo, hi, a, b, r, c, hmem, ha, hr, hp, hl, hupp, hc, hgap⟩ :=
    k131_tail_partition_enclosure hL
  refine
    k131_tail_witness_of_box hn ho hu hGRH hL ?_ ha hr hp hl hupp hc
      (fun hy hroot hlog ↦ k131_rounded_tail_cap_sound hy ha.le hr hroot hlog) hgap
  simp only [Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast,
    gaussianK131TailScale]
  exact ⟨by linarith only [hmem.1], by linarith only [hmem.2]⟩

/-- Under GRH, the compressed prefix and both K131 ranges provide a uniform
Korselt witness through log 42410. Only the witness above that range is supplied separately. -/
theorem uniform_gaussian_to_k131_cutoff {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hL : 663 ≤ Real.log n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (htail :
      UniformKorseltTriple n →
        42410 < Real.log n → HasRejectingPrime n (gaussianWitnessCutoff (Real.log n))) :
    HasRejectingPrime n (gaussianWitnessCutoff (Real.log n)) := by
  apply uniform_gaussian_witness_of_cutoff hn ho hu hL hGRH
  · exact fun h ha hb ↦ uniform_k131_gaussian_witness hn ho h hGRH ⟨ha, hb⟩
  · intro h hlo
    by_cases hhi : Real.log n ≤ 42410
    · exact (uniform_k131_tail_witness hn ho h hGRH ⟨hlo, hhi⟩).mono (gaussian_old_cutoff_le hlo)
    · exact htail h (lt_of_not_ge hhi)

/-- Reuse a tail already proved with the old Gaussian cutoff. -/
theorem uniform_gaussian_witness_to_k131 {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hL : 663 ≤ Real.log n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (htail :
      UniformKorseltTriple n →
        42410 < Real.log n →
        HasRejectingPrime n
          (max 2
            (max ((1 / 4 : ℝ) * Real.log n ^ 2)
              ((9090 / 33659 : ℝ) * Real.log n ^ 2 -
                8 * Real.log n * Real.exp (-(Real.log n / 1000000) ^ 2))))) :
    HasRejectingPrime n (gaussianWitnessCutoff (Real.log n)) := by
  apply uniform_gaussian_to_k131_cutoff hn ho hu hL hGRH
  intro h ha
  have hlo := (by norm_num only : (8000 : ℝ) ≤ 42410).trans ha.le
  exact (htail h ha).mono (gaussian_old_cutoff_le hlo)

/-- Compatibility form of the uniform Gaussian witness through the K131 ranges. -/
theorem uniform_gaussian_witness_of_k131 {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hL : 663 ≤ Real.log n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (_hcell :
      UniformKorseltTriple n →
        2657 / 4 < Real.log n →
        ∀ i : Fin 166,
          gaussianCompressedLeft i ≤ Real.log n →
            Real.log n ≤ gaussianCompressedRight i →
            HasRejectingPrime n ((gaussianCompressedScale i * Real.log n / 2) ^ 2))
    (htail :
      UniformKorseltTriple n →
        42410 < Real.log n →
        HasRejectingPrime n
          (max 2
            (max ((1 / 4 : ℝ) * Real.log n ^ 2)
              ((9090 / 33659 : ℝ) * Real.log n ^ 2 -
                8 * Real.log n * Real.exp (-(Real.log n / 1000000) ^ 2))))) :
    HasRejectingPrime n (gaussianWitnessCutoff (Real.log n)) := by
  exact uniform_gaussian_witness_to_k131 hn ho hu hL hGRH htail

/-- The Gaussian criterion with both K131 intervals discharged. The
compressed cells and witnesses above log 42410 remain as hypotheses. -/
theorem gaussian_criterion_of_k131_tail {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hcell :
      UniformKorseltTriple n →
        2657 / 4 < Real.log n →
        ∀ i : Fin 166,
          gaussianCompressedLeft i ≤ Real.log n →
            Real.log n ≤ gaussianCompressedRight i →
            HasRejectingPrime n ((gaussianCompressedScale i * Real.log n / 2) ^ 2))
    (htail :
      UniformKorseltTriple n →
        42410 ≤ Real.log n →
        HasRejectingPrime n
          (max 2
            (max ((1 / 4 : ℝ) * Real.log n ^ 2)
              ((9090 / 33659 : ℝ) * Real.log n ^ 2 -
                8 * Real.log n * Real.exp (-(Real.log n / 1000000) ^ 2))))) :
    (∀ p : ℕ,
        p.Prime →
          (p : ℝ) ≤ gaussianWitnessCutoff (Real.log n) →
          PrimeTest.StrongMillerRabinPass n (p : ZMod n)) ↔
      n.Prime := by
  exact
    gaussian_criterion_of_uniform_witness hn ho hGRH
      (fun hu hL ↦
        uniform_gaussian_witness_of_k131 hn ho hu hL hGRH hcell (fun h hh ↦ htail h hh.le))

/-- Under GRH, the Gaussian cutoff characterizes odd primes with logarithm
at most 42410 by combining the compressed prefix and both K131 ranges. -/
theorem gaussian_criterion_to42410 {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hU : Real.log n ≤ 42410) :
    (∀ p : ℕ,
        p.Prime →
          (p : ℝ) ≤ gaussianWitnessCutoff (Real.log n) →
          PrimeTest.StrongMillerRabinPass n (p : ZMod n)) ↔
      n.Prime := by
  exact
    gaussian_criterion_of_uniform_witness hn ho hGRH
      (fun hu hL ↦
        uniform_gaussian_witness_to_k131 hn ho hu hL hGRH (fun _ hh ↦ (not_lt_of_ge hU hh).elim))

/-- The manuscript's middle-range envelope with loss coefficient 64/5
is dominated by the old Gaussian envelope, and hence by the target cutoff. -/
theorem gaussian_middle_cutoff_le {L : ℝ} (hL : 42410 ≤ L) :
    max 2
        (max ((1 / 4 : ℝ) * L ^ 2)
          ((9090 / 33659 : ℝ) * L ^ 2 - (64 / 5 : ℝ) * L * Real.exp (-(L / 1000000) ^ 2))) ≤
      gaussianWitnessCutoff L := by
  apply le_trans _ (gaussian_old_cutoff_le ((by norm_num only : (8000 : ℝ) ≤ 42410).trans hL))
  apply max_le_max_left
  apply max_le_max_left
  have h :=
    mul_nonneg ((by norm_num only : (0 : ℝ) ≤ 42410).trans hL)
      (Real.exp_pos (-(L / 1000000) ^ 2)).le
  linarith only [h]

/-- The manuscript's high-range quadratic coefficient is dominated by
the old Gaussian envelope for every logarithm at least 6,300,000. -/
theorem gaussian_high_le_old {L : ℝ} (hL : 6300000 ≤ L) :
    (0.270061456043740 : ℝ) * L ^ 2 ≤
      (9090 / 33659 : ℝ) * L ^ 2 - 8 * L * Real.exp (-(L / 1000000) ^ 2) := by
  have hL0 : 0 ≤ L := (by norm_num only : (0 : ℝ) ≤ 6300000).trans hL
  have hs := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 6300000) hL 2
  have hex : (40 : ℝ) ≤ Real.exp ((L / 1000000) ^ 2) := by
    have h := Real.add_one_le_exp ((L / 1000000) ^ 2)
    linarith only [hs, h, show (L / 1000000) ^ 2 = L ^ 2 / 1000000000000 by ring]
  have hinv : Real.exp (-(L / 1000000) ^ 2) ≤ 1 / 40 := by
    rw [Real.exp_neg, one_div]
    exact (inv_le_inv₀ (Real.exp_pos _) (by norm_num only)).2 hex
  have hd : (1 / 5 : ℝ) ≤ (9090 / 33659 - 0.270061456043740) * L := by
    have h :=
      mul_le_mul_of_nonneg_left hL (by norm_num only : (0 : ℝ) ≤ 9090 / 33659 - 0.270061456043740)
    linarith only [h]
  have h :=
    mul_le_mul_of_nonneg_right
      (show 8 * Real.exp (-(L / 1000000) ^ 2) ≤ (9090 / 33659 - 0.270061456043740) * L by
        linarith only [hinv, hd])
      hL0
  nlinarith only [h]

/-- The manuscript's high-range quadratic cutoff fits the final Gaussian
cutoff directly, using a reciprocal bound for the exponential at the entrance. -/
theorem gaussian_high_le_final {L : ℝ} (hL : 6300000 ≤ L) :
    max 2 ((0.270061456043740 : ℝ) * L ^ 2) ≤ gaussianWitnessCutoff L := by
  have hL0 := (by norm_num only : (0 : ℝ) ≤ 6300000).trans hL
  have hs := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 6300000) hL 2
  have hex : (100 : ℝ) ≤ Real.exp ((L / 11000) ^ 2) := by
    have h := Real.add_one_le_exp ((L / 11000) ^ 2)
    linarith only [hs, h, show (L / 11000) ^ 2 = L ^ 2 / 121000000 by ring]
  have he : Real.exp (-(L / 11000) ^ 2) ≤ 1 / 100 := by
    rw [Real.exp_neg, one_div]
    exact (inv_le_inv₀ (Real.exp_pos _) (by norm_num only)).2 hex
  have hc : (53 / 400 : ℝ) ≤ (9090 / 33659 - 0.270061456043740) * L :=
    (by norm_num only : (53 / 400 : ℝ) ≤ (9090 / 33659 - 0.270061456043740) * 6300000).trans
      (mul_le_mul_of_nonneg_left hL (by norm_num only))
  have hm :=
    mul_le_mul_of_nonneg_right
      (show (53 / 4 : ℝ) * Real.exp (-(L / 11000) ^ 2) ≤ (9090 / 33659 - 0.270061456043740) * L by
        linarith only [he, hc])
      hL0
  exact
    max_le_max_left _
      ((by nlinarith only [hm] :
            (0.270061456043740 : ℝ) * L ^ 2 ≤
              (9090 / 33659 : ℝ) * L ^ 2 - (53 / 4 : ℝ) * L * Real.exp (-(L / 11000) ^ 2)).trans
        (le_max_right _ _))

/-- Under GRH, assemble the proved Gaussian ranges through log 42410 with
the middle and high witnesses at their manuscript cutoffs. -/
theorem uniform_gaussian_witness_of_upper {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hL : 663 ≤ Real.log n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hmid :
      Real.log n ∈ Set.Icc (42410 : ℝ) 7000000 →
        HasRejectingPrime n
          (max 2
            (max ((1 / 4 : ℝ) * Real.log n ^ 2)
              ((9090 / 33659 : ℝ) * Real.log n ^ 2 -
                (64 / 5 : ℝ) * Real.log n * Real.exp (-(Real.log n / 1000000) ^ 2)))))
    (hhigh :
      6300000 ≤ Real.log n →
        HasRejectingPrime n (max 2 ((0.270061456043740 : ℝ) * Real.log n ^ 2))) :
    HasRejectingPrime n (gaussianWitnessCutoff (Real.log n)) := by
  by_cases hhighRange : 6300000 ≤ Real.log n
  · exact (hhigh hhighRange).mono (gaussian_high_le_final hhighRange)
  by_cases hmidRange : 42410 ≤ Real.log n
  · exact
      (hmid ⟨hmidRange, (le_of_not_ge hhighRange).trans (by norm_num only)⟩).mono
        (gaussian_middle_cutoff_le hmidRange)
  exact uniform_gaussian_to_k131_cutoff hn ho hu hL hGRH (fun _ h ↦ False.elim (hmidRange h.le))

/-- Compatibility form of the upper assembly with the compressed prefix supplied. -/
theorem uniform_gaussian_witness_of_middle_high {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hL : 663 ≤ Real.log n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (_hcell :
      UniformKorseltTriple n →
        2657 / 4 < Real.log n →
        ∀ i : Fin 166,
          gaussianCompressedLeft i ≤ Real.log n →
            Real.log n ≤ gaussianCompressedRight i →
            HasRejectingPrime n ((gaussianCompressedScale i * Real.log n / 2) ^ 2))
    (hmid :
      Real.log n ∈ Set.Icc (42410 : ℝ) 7000000 →
        HasRejectingPrime n
          (max 2
            (max ((1 / 4 : ℝ) * Real.log n ^ 2)
              ((9090 / 33659 : ℝ) * Real.log n ^ 2 -
                (64 / 5 : ℝ) * Real.log n * Real.exp (-(Real.log n / 1000000) ^ 2)))))
    (hhigh :
      6300000 ≤ Real.log n →
        HasRejectingPrime n (max 2 ((0.270061456043740 : ℝ) * Real.log n ^ 2))) :
    HasRejectingPrime n (gaussianWitnessCutoff (Real.log n)) := by
  exact uniform_gaussian_witness_of_upper hn ho hu hL hGRH hmid hhigh

/-- Join the proved Gaussian prefix with middle and high uniform-triple
witnesses established directly at the final cutoff. -/
theorem uniform_gaussian_of_final_ranges {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hL : 663 ≤ Real.log n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hmid :
      Real.log n ∈ Set.Icc (42410 : ℝ) 7000000 →
        HasRejectingPrime n (gaussianWitnessCutoff (Real.log n)))
    (hhigh : 6300000 ≤ Real.log n → HasRejectingPrime n (gaussianWitnessCutoff (Real.log n))) :
    HasRejectingPrime n (gaussianWitnessCutoff (Real.log n)) := by
  apply uniform_gaussian_to_k131_cutoff hn ho hu hL hGRH
  intro _ hlo
  by_cases h : 6300000 ≤ Real.log n
  · exact hhigh h
  exact hmid ⟨hlo.le, (le_of_not_ge h).trans (by norm_num only)⟩

/-- Combine the final-cutoff uniform ranges with the existing quarter witness
for the other composites. -/
theorem gaussian_criterion_of_final_ranges {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hmid :
      UniformKorseltTriple n →
        Real.log n ∈ Set.Icc (42410 : ℝ) 7000000 →
        HasRejectingPrime n (gaussianWitnessCutoff (Real.log n)))
    (hhigh :
      UniformKorseltTriple n →
        6300000 ≤ Real.log n → HasRejectingPrime n (gaussianWitnessCutoff (Real.log n))) :
    (∀ p : ℕ,
        p.Prime →
          (p : ℝ) ≤ gaussianWitnessCutoff (Real.log n) →
          PrimeTest.StrongMillerRabinPass n (p : ZMod n)) ↔
      n.Prime := by
  exact
    gaussian_criterion_of_uniform_witness hn ho hGRH
      (fun hu hL ↦ uniform_gaussian_of_final_ranges hn ho hu hL hGRH (hmid hu) (hhigh hu))

end PseudoPrime.PrimeTestBounds.MillerRabin
