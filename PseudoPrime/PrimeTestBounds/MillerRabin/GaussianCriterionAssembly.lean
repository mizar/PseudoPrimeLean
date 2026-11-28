/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianBridgeAffine
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianCompressedCutoff
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197LateWitness
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCriterionTo663
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianCompressedCutoff

/-! # Assembly of the Gaussian Miller–Rabin criterion -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem quarter_max_le_gaussian (L : ℝ) :
    max 2 ((1 / 4 : ℝ) * L ^ 2) ≤ gaussianWitnessCutoff L := by
  exact max_le_max_left _ (le_max_left _ _)

/-- The quarter bound supplies the Gaussian witness below log 663 and for
all nonuniform odd composites. -/
theorem gaussian_quarter_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hrange : Real.log n ≤ 663 ∨ ¬UniformKorseltTriple n) :
    HasRejectingPrime n (gaussianWitnessCutoff (Real.log n)) := by
  exact (quarter_witness_to663 hn ho hc hGRH hrange).mono (quarter_max_le_gaussian (Real.log n))

private theorem gaussian_prime_pass {n p : ℕ} (ho : Odd n) (hn : n.Prime) (hp : p.Prime)
    (hb : (p : ℝ) ≤ gaussianWitnessCutoff (Real.log n)) :
    PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  exact
    prime_pass_of_log_sq ho hn hp
      (hb.trans
        ((gaussianCutoff_le_threeEleven (Real.log_natCast_nonneg n)).trans
          (max_le_max_left _ (by nlinarith only [sq_nonneg (Real.log n)]))))

/-- The Gaussian criterion implies the quadratic criterion with coefficient
9090/33659 by monotonicity of the cutoff. -/
theorem criterion_027007_of_gaussian {n : ℕ} (ho : Odd n)
    (hG :
      (∀ p : ℕ,
          p.Prime →
            (p : ℝ) ≤ gaussianWitnessCutoff (Real.log n) →
            PrimeTest.StrongMillerRabinPass n (p : ZMod n)) ↔
        n.Prime) :
    (∀ p : ℕ,
        p.Prime →
          (p : ℝ) ≤ max 2 ((9090 / 33659 : ℝ) * Real.log n ^ 2) →
          PrimeTest.StrongMillerRabinPass n (p : ZMod n)) ↔
      n.Prime := by
  refine ⟨fun h ↦ hG.mp (fun p hp hb ↦ h p hp (hb.trans ?_)), fun hn p hp hb ↦ ?_⟩
  · apply max_le_max_left
    apply max_le
    · nlinarith only [sq_nonneg (Real.log n)]
    · exact
        sub_le_self _
          (mul_nonneg (mul_nonneg (by norm_num only) (Real.log_natCast_nonneg n))
            (Real.exp_pos _).le)
  · exact
      prime_pass_of_log_sq ho hn hp
        (hb.trans (max_le_max_left _ (by nlinarith only [sq_nonneg (Real.log n)])))

/-- Under GRH, join the Gaussian witness ranges for an odd uniform Korselt
triple above log 663. The compressed prefix is supplied under GRH. Each tail uses its own cutoff,
which is then bounded by the target Gaussian cutoff. -/
theorem uniform_gaussian_witness_of_cutoff {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hL : 663 ≤ Real.log n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hbridge :
      UniformKorseltTriple n →
        9055 / 4 ≤ Real.log n →
        Real.log n ≤ 8000 → HasRejectingPrime n (gaussianBridgeScale (Real.log n) ^ 2))
    (htail :
      UniformKorseltTriple n →
        8000 ≤ Real.log n → HasRejectingPrime n (gaussianWitnessCutoff (Real.log n))) :
    HasRejectingPrime n (gaussianWitnessCutoff (Real.log n)) := by
  by_cases hk137 : Real.log n ≤ 2657 / 4
  · exact gaussian_k137_witness hn ho hu hGRH ⟨hL, hk137⟩
  by_cases hk197 : Real.log n ≤ 2659 / 4
  · have hw := gaussian_k197_first_witness hn ho hu hGRH ⟨le_of_not_ge hk137, hk197⟩
    have hleft : gaussianCompressedLeft (3 : Fin 166) ≤ Real.log n := by
      change (2657 : ℝ) / 4 ≤ Real.log n
      exact le_of_not_ge hk137
    have hcut := gaussian_compressed_cutoff (3 : Fin 166) hleft
    change
      ((500186760939 / 500000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases hk197₂ : Real.log n ≤ 2661 / 4
  · have hw := gaussian_k197_second_witness hn ho hu hGRH ⟨le_of_not_ge hk197, hk197₂⟩
    have hleft : gaussianCompressedLeft (4 : Fin 166) ≤ Real.log n := by
      change (2659 : ℝ) / 4 ≤ Real.log n
      exact le_of_not_ge hk197
    have hcut := gaussian_compressed_cutoff (4 : Fin 166) hleft
    change
      ((12505045329 / 12500000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases hk197₃ : Real.log n ≤ 2665 / 4
  · have hw := gaussian_k197_third_witness hn ho hu hGRH ⟨le_of_not_ge hk197₂, hk197₃⟩
    have hleft : gaussianCompressedLeft (5 : Fin 166) ≤ Real.log n := by
      change (2661 : ℝ) / 4 ≤ Real.log n
      exact le_of_not_ge hk197₂
    have hcut := gaussian_compressed_cutoff (5 : Fin 166) hleft
    change
      ((1000433684769 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases hk197₄ : Real.log n ≤ 2669 / 4
  · have hw := gaussian_k197_fourth_witness hn ho hu hGRH ⟨le_of_not_ge hk197₃, hk197₄⟩
    have hleft : gaussianCompressedLeft (6 : Fin 166) ≤ Real.log n := by
      change (2665 : ℝ) / 4 ≤ Real.log n
      exact le_of_not_ge hk197₃
    have hcut := gaussian_compressed_cutoff (6 : Fin 166) hleft
    change
      ((500246832053 / 500000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases hk197₅ : Real.log n ≤ 2671 / 4
  · have hw := gaussian_k197_cell5_witness hn ho hu hGRH ⟨le_of_not_ge hk197₄, hk197₅⟩
    have hleft : gaussianCompressedLeft (7 : Fin 166) ≤ Real.log n := by
      change (2669 : ℝ) / 4 ≤ Real.log n
      exact le_of_not_ge hk197₄
    have hcut := gaussian_compressed_cutoff (7 : Fin 166) hleft
    change
      ((1000553460733 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases hk197₆ : Real.log n ≤ 2675 / 4
  · have hw := gaussian_k197_cell6_witness hn ho hu hGRH ⟨le_of_not_ge hk197₅, hk197₆⟩
    have hleft : gaussianCompressedLeft (8 : Fin 166) ≤ Real.log n := by
      change (2671 : ℝ) / 4 ≤ Real.log n
      exact le_of_not_ge hk197₅
    have hcut := gaussian_compressed_cutoff (8 : Fin 166) hleft
    change
      ((1000583290791 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases hk197₇ : Real.log n ≤ 2679 / 4
  · have hw := gaussian_k197_cell7_witness hn ho hu hGRH ⟨le_of_not_ge hk197₆, hk197₇⟩
    have hleft : gaussianCompressedLeft (9 : Fin 166) ≤ Real.log n := by
      change (2675 : ℝ) / 4 ≤ Real.log n
      exact le_of_not_ge hk197₆
    have hcut := gaussian_compressed_cutoff (9 : Fin 166) hleft
    change
      ((1000642814919 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases hk197₈ : Real.log n ≤ 2683 / 4
  · have hw := gaussian_k197_cell8_witness hn ho hu hGRH ⟨le_of_not_ge hk197₇, hk197₈⟩
    have hleft : gaussianCompressedLeft (10 : Fin 166) ≤ Real.log n := by
      change (2679 : ℝ) / 4 ≤ Real.log n
      exact le_of_not_ge hk197₇
    have hcut := gaussian_compressed_cutoff (10 : Fin 166) hleft
    change
      ((1000702158417 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases hk197₉ : Real.log n ≤ 2685 / 4
  · have hw := gaussian_k197_cell9_witness hn ho hu hGRH ⟨le_of_not_ge hk197₈, hk197₉⟩
    have hleft : gaussianCompressedLeft (11 : Fin 166) ≤ Real.log n := by
      change (2683 : ℝ) / 4 ≤ Real.log n
      exact le_of_not_ge hk197₈
    have hcut := gaussian_compressed_cutoff (11 : Fin 166) hleft
    change
      ((1000761322111 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases hk197₁₀ : Real.log n ≤ 2686 / 4
  · have hw := gaussian_k197_cell10_witness hn ho hu hGRH ⟨le_of_not_ge hk197₉, hk197₁₀⟩
    have hleft : gaussianCompressedLeft (12 : Fin 166) ≤ Real.log n := by
      change (2685 : ℝ) / 4 ≤ Real.log n
      exact le_of_not_ge hk197₉
    have hcut := gaussian_compressed_cutoff (12 : Fin 166) hleft
    change
      ((1000790836787 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases hk197₁₁ : Real.log n ≤ 672
  · have hlo : (1343 / 2 : ℝ) ≤ Real.log n := by linarith only [le_of_not_ge hk197₁₀]
    have hw := gaussian_k197_cell11_witness hn ho hu hGRH ⟨hlo, hk197₁₁⟩
    have hleft : gaussianCompressedLeft (13 : Fin 166) ≤ Real.log n := by
      change (1343 : ℝ) / 2 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (13 : Fin 166) hleft
    change
      ((1000805577377 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases hk197₁₂ : Real.log n ≤ 673
  · have hw := gaussian_k197_cell12_witness hn ho hu hGRH ⟨le_of_not_ge hk197₁₁, hk197₁₂⟩
    have hleft : gaussianCompressedLeft (14 : Fin 166) ≤ Real.log n := by
      change ((672 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) ≤ Real.log n
      norm_num only [Nat.cast_ofNat, Nat.cast_one, div_one]
      simpa only [div_one] using le_of_not_ge hk197₁₁
    have hcut := gaussian_compressed_cutoff (14 : Fin 166) hleft
    change
      ((8006680201 / 8000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases hk197₁₃ : Real.log n ≤ (1347 / 2)
  · have hlo : (673 : ℝ) / 1 ≤ Real.log n := by linarith only [le_of_not_ge hk197₁₂]
    have hw := gaussian_k197_cell13_witness hn ho hu hGRH ⟨by linarith only [hlo], hk197₁₃⟩
    have hleft : gaussianCompressedLeft (15 : Fin 166) ≤ Real.log n := by
      change ((673 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) ≤ Real.log n
      norm_num only [Nat.cast_ofNat, Nat.cast_one, div_one]
      simpa only [div_one] using hlo
    have hcut := gaussian_compressed_cutoff (15 : Fin 166) hleft
    change
      ((500446893623 / 500000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases hk197₁₄ : Real.log n ≤ 674
  · have hlo : (1347 : ℝ) / 2 ≤ Real.log n := by linarith only [le_of_not_ge hk197₁₃]
    have hw := gaussian_k197_cell14_witness hn ho hu hGRH ⟨by linarith only [hlo], hk197₁₄⟩
    have hleft : gaussianCompressedLeft (16 : Fin 166) ≤ Real.log n := by
      change (1347 : ℝ) / 2 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (16 : Fin 166) hleft
    change
      ((50046155091 / 50000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases hk197₁₅ : Real.log n ≤ (1349 / 2)
  · have hlo : (674 : ℝ) / 1 ≤ Real.log n := by linarith only [le_of_not_ge hk197₁₄]
    have hw := gaussian_k197_cell15_witness hn ho hu hGRH ⟨by linarith only [hlo], hk197₁₅⟩
    have hleft : gaussianCompressedLeft (17 : Fin 166) ≤ Real.log n := by
      change ((674 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) ≤ Real.log n
      norm_num only [Nat.cast_ofNat, Nat.cast_one, div_one]
      simpa only [div_one] using hlo
    have hcut := gaussian_compressed_cutoff (17 : Fin 166) hleft
    change
      ((50046155091 / 50000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases hk197₁₆ : Real.log n ≤ (1351 / 2)
  · have hlo : (1349 : ℝ) / 2 ≤ Real.log n := by linarith only [le_of_not_ge hk197₁₅]
    have hw := gaussian_k197_cell16_witness hn ho hu hGRH ⟨by linarith only [hlo], hk197₁₆⟩
    have hleft : gaussianCompressedLeft (18 : Fin 166) ≤ Real.log n := by
      change (1349 : ℝ) / 2 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (18 : Fin 166) hleft
    change
      ((1000981598501 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases hk197₁₇ : Real.log n ≤ 676
  · have hlo : (1351 : ℝ) / 2 ≤ Real.log n := by linarith only [le_of_not_ge hk197₁₆]
    have hw := gaussian_k197_cell17_witness hn ho hu hGRH ⟨by linarith only [hlo], hk197₁₇⟩
    have hleft : gaussianCompressedLeft (19 : Fin 166) ≤ Real.log n := by
      change (1351 : ℝ) / 2 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (19 : Fin 166) hleft
    change
      ((125129989903 / 125000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases hk197₁₈ : Real.log n ≤ (2705 / 4)
  · have hlo : (676 : ℝ) / 1 ≤ Real.log n := by linarith only [le_of_not_ge hk197₁₇]
    have hw := gaussian_k197_cell18_witness hn ho hu hGRH ⟨by linarith only [hlo], hk197₁₈⟩
    have hleft : gaussianCompressedLeft (20 : Fin 166) ≤ Real.log n := by
      change ((676 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) ≤ Real.log n
      norm_num only [Nat.cast_ofNat, Nat.cast_one, div_one]
      simpa only [div_one] using hlo
    have hcut := gaussian_compressed_cutoff (20 : Fin 166) hleft
    change
      ((1001069013851 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases hk197₁₉ : Real.log n ≤ (1353 / 2)
  · have hlo : (2705 : ℝ) / 4 ≤ Real.log n := by linarith only [le_of_not_ge hk197₁₈]
    have hw := gaussian_k197_cell19_witness hn ho hu hGRH ⟨by linarith only [hlo], hk197₁₉⟩
    have hleft : gaussianCompressedLeft (21 : Fin 166) ≤ Real.log n := by
      change (2705 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (21 : Fin 166) hleft
    change
      ((1001083544773 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases hk197₂₀ : Real.log n ≤ 677
  · have hlo : (1353 : ℝ) / 2 ≤ Real.log n := by linarith only [le_of_not_ge hk197₁₉]
    have hw := gaussian_k197_cell20_witness hn ho hu hGRH ⟨by linarith only [hlo], hk197₂₀⟩
    have hleft : gaussianCompressedLeft (22 : Fin 166) ≤ Real.log n := by
      change (1353 : ℝ) / 2 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (22 : Fin 166) hleft
    change
      ((200219612957 / 200000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h21 : Real.log n ≤ (1355 / 2)
  · have hlo := le_of_not_ge hk197₂₀
    have hw := gaussian_k197_cell21_witness hn ho hu hGRH ⟨by linarith only [hlo], h21⟩
    have hleft : gaussianCompressedLeft (23 : Fin 166) ≤ Real.log n := by
      change ((677 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) ≤ Real.log n
      norm_num only [Nat.cast_ofNat, Nat.cast_one, div_one]
      simpa only [div_one] using hlo
    have hcut := gaussian_compressed_cutoff (23 : Fin 166) hleft
    change
      ((7821305251 / 7812500000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h22 : Real.log n ≤ 678
  · have hlo := le_of_not_ge h21
    have hw := gaussian_k197_cell22_witness hn ho hu hGRH ⟨by linarith only [hlo], h22⟩
    have hleft : gaussianCompressedLeft (24 : Fin 166) ≤ Real.log n := by
      change (1355 : ℝ) / 2 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (24 : Fin 166) hleft
    change
      ((125144504497 / 125000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h23 : Real.log n ≤ (1357 / 2)
  · have hlo := le_of_not_ge h22
    have hw := gaussian_k197_cell23_witness hn ho hu hGRH ⟨hlo, h23⟩
    have hleft : gaussianCompressedLeft (25 : Fin 166) ≤ Real.log n := by
      change ((678 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) ≤ Real.log n
      norm_num only [Nat.cast_ofNat, Nat.cast_one, div_one]
      simpa only [div_one] using hlo
    have hcut := gaussian_compressed_cutoff (25 : Fin 166) hleft
    change
      ((1001184956427 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h24 : Real.log n ≤ (2715 / 4)
  · have hlo := le_of_not_ge h23
    have hw := gaussian_k197_cell24_witness hn ho hu hGRH ⟨hlo, h24⟩
    have hleft : gaussianCompressedLeft (26 : Fin 166) ≤ Real.log n := by
      change (1357 : ℝ) / 2 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (26 : Fin 166) hleft
    change
      ((1001213833581 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h25 : Real.log n ≤ 679
  · have hlo := le_of_not_ge h24
    have hw := gaussian_k197_cell25_witness hn ho hu hGRH ⟨hlo, h25⟩
    have hleft : gaussianCompressedLeft (27 : Fin 166) ≤ Real.log n := by
      change (2715 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (27 : Fin 166) hleft
    change
      ((1001228255951 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h26 : Real.log n ≤ 5433 / 8
  · have hlo := le_of_not_ge h25
    have hleft : gaussianCompressedLeft (28 : Fin 166) ≤ Real.log n := by
      change ((679 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) ≤ Real.log n
      norm_num only [Nat.cast_ofNat, Nat.cast_one, div_one]
      simpa only [div_one] using hlo
    have hcut := gaussian_compressed_cutoff (28 : Fin 166) hleft
    change
      ((1001228255951 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    by_cases hm : Real.log n ≤ 679.011
    · exact HasRejectingPrime.mono (gaussian_k197_cell26_left_witness hn ho hu hGRH ⟨hlo, hm⟩) hcut
    · exact
        HasRejectingPrime.mono
          (gaussian_k197_cell26_right_witness hn ho hu hGRH ⟨le_of_not_ge hm, h26⟩) hcut
  by_cases h27 : Real.log n ≤ 2717 / 4
  · have hlo := le_of_not_ge h26
    have hw := gaussian_k197_cell27_witness hn ho hu hGRH ⟨hlo, h27⟩
    have hleft : gaussianCompressedLeft (29 : Fin 166) ≤ Real.log n := by
      change (5433 : ℝ) / 8 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (29 : Fin 166) hleft
    change
      ((1001228255951 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h28 : Real.log n ≤ (1359 / 2)
  · have hlo := le_of_not_ge h27
    have hw := gaussian_k197_cell28_witness hn ho hu hGRH ⟨hlo, h28⟩
    have hleft : gaussianCompressedLeft (30 : Fin 166) ≤ Real.log n := by
      change (2717 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (30 : Fin 166) hleft
    change
      ((50062853417 / 50000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h29 : Real.log n ≤ 5437 / 8
  · have hlo := le_of_not_ge h28
    have hleft : gaussianCompressedLeft (31 : Fin 166) ≤ Real.log n := by
      change (1359 : ℝ) / 2 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (31 : Fin 166) hleft
    change
      ((50062853417 / 50000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    by_cases hm : Real.log n ≤ 679.52
    · exact HasRejectingPrime.mono (gaussian_k197_cell29_left_witness hn ho hu hGRH ⟨hlo, hm⟩) hcut
    · exact
        HasRejectingPrime.mono
          (gaussian_k197_cell29_right_witness hn ho hu hGRH ⟨le_of_not_ge hm, h29⟩) hcut
  by_cases h30 : Real.log n ≤ (2719 / 4)
  · have hlo := le_of_not_ge h29
    have hw := gaussian_k197_cell30_witness hn ho hu hGRH ⟨hlo, h30⟩
    have hleft : gaussianCompressedLeft (32 : Fin 166) ≤ Real.log n := by
      change (5437 : ℝ) / 8 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (32 : Fin 166) hleft
    change
      ((50062853417 / 50000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h31 : Real.log n ≤ (2723 / 4)
  · have hlo := le_of_not_ge h30
    have hw := gaussian_k197_cell31_witness hn ho hu hGRH ⟨hlo, h31⟩
    have hleft : gaussianCompressedLeft (33 : Fin 166) ≤ Real.log n := by
      change (2719 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (33 : Fin 166) hleft
    change
      ((500642918837 / 500000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h32 : Real.log n ≤ (2727 / 4)
  · have hlo := le_of_not_ge h31
    have hw := gaussian_k197_cell32_witness hn ho hu hGRH ⟨hlo, h32⟩
    have hleft : gaussianCompressedLeft (34 : Fin 166) ≤ Real.log n := by
      change (2723 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (34 : Fin 166) hleft
    change
      ((250335811891 / 250000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h33 : Real.log n ≤ (2729 / 4)
  · have hlo := le_of_not_ge h32
    have hw := gaussian_k197_cell33_witness hn ho hu hGRH ⟨hlo, h33⟩
    have hleft : gaussianCompressedLeft (35 : Fin 166) ≤ Real.log n := by
      change (2727 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (35 : Fin 166) hleft
    change
      ((1001400486393 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h34 : Real.log n ≤ (2731 / 4)
  · have hlo := le_of_not_ge h33
    have hw := gaussian_k197_cell34_witness hn ho hu hGRH ⟨hlo, h34⟩
    have hleft : gaussianCompressedLeft (36 : Fin 166) ≤ Real.log n := by
      change (2729 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (36 : Fin 166) hleft
    change
      ((1001400486393 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h35 : Real.log n ≤ (2735 / 4)
  · have hlo := le_of_not_ge h34
    have hw := gaussian_k197_cell35_witness hn ho hu hGRH ⟨hlo, h35⟩
    have hleft : gaussianCompressedLeft (37 : Fin 166) ≤ Real.log n := by
      change (2731 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (37 : Fin 166) hleft
    change
      ((500728777463 / 500000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h36 : Real.log n ≤ (2739 / 4)
  · have hlo := le_of_not_ge h35
    have hw := gaussian_k197_cell36_witness hn ho hu hGRH ⟨hlo, h36⟩
    have hleft : gaussianCompressedLeft (38 : Fin 166) ≤ Real.log n := by
      change (2735 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (38 : Fin 166) hleft
    change
      ((40060578157 / 40000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h37 : Real.log n ≤ 2743 / 4
  · have hlo := le_of_not_ge h36
    have hw := gaussian_k197_cell37_witness hn ho hu hGRH ⟨hlo, h37⟩
    have hleft : gaussianCompressedLeft (39 : Fin 166) ≤ Real.log n := by
      change (2739 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (39 : Fin 166) hleft
    change
      ((1001571184149 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h38 : Real.log n ≤ 2747 / 4
  · have hlo := le_of_not_ge h37
    have hw := gaussian_k197_cell38_witness hn ho hu hGRH ⟨hlo, h38⟩
    have hleft : gaussianCompressedLeft (40 : Fin 166) ≤ Real.log n := by
      change (2743 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (40 : Fin 166) hleft
    change
      ((1001627746349 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h39 : Real.log n ≤ 2751 / 4
  · have hlo := le_of_not_ge h38
    have hw := gaussian_k197_cell39_witness hn ho hu hGRH ⟨hlo, h39⟩
    have hleft : gaussianCompressedLeft (41 : Fin 166) ≤ Real.log n := by
      change (2747 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (41 : Fin 166) hleft
    change
      ((40067365651 / 40000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h40 : Real.log n ≤ 2755 / 4
  · have hlo := le_of_not_ge h39
    have hw := gaussian_k197_cell40_witness hn ho hu hGRH ⟨hlo, h40⟩
    have hleft : gaussianCompressedLeft (42 : Fin 166) ≤ Real.log n := by
      change (2751 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (42 : Fin 166) hleft
    change
      ((1001740369669 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h41 : Real.log n ≤ 2759 / 4
  · have hlo := le_of_not_ge h40
    have hleft : gaussianCompressedLeft (43 : Fin 166) ≤ Real.log n := by
      change (2755 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (43 : Fin 166) hleft
    change
      ((62612277017 / 62500000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    by_cases hm : Real.log n ≤ 688.804
    · exact HasRejectingPrime.mono (gaussian_k197_cell41_left_witness hn ho hu hGRH ⟨hlo, hm⟩) hcut
    · exact
        HasRejectingPrime.mono
          (gaussian_k197_cell41_right_witness hn ho hu hGRH ⟨le_of_not_ge hm, h41⟩) hcut
  by_cases h42 : Real.log n ≤ 690
  · have hlo := le_of_not_ge h41
    have hw := gaussian_k197_cell42_witness hn ho hu hGRH ⟨hlo, h42⟩
    have hleft : gaussianCompressedLeft (44 : Fin 166) ≤ Real.log n := by
      change (2759 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (44 : Fin 166) hleft
    change
      ((500926164909 / 500000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h43 : Real.log n ≤ 5521 / 8
  · have hlo := le_of_not_ge h42
    have hw := gaussian_k197_cell43_witness hn ho hu hGRH ⟨hlo, h43⟩
    have hleft : gaussianCompressedLeft (45 : Fin 166) ≤ Real.log n := by
      change ((690 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) ≤ Real.log n
      norm_num only [Nat.cast_ofNat, Nat.cast_one, div_one]
      simpa only [div_one] using hlo
    have hcut := gaussian_compressed_cutoff (45 : Fin 166) hleft
    change
      ((500926164909 / 500000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h44 : Real.log n ≤ 2761 / 4
  · have hlo := le_of_not_ge h43
    have hw := gaussian_k197_cell44_witness hn ho hu hGRH ⟨hlo, h44⟩
    have hleft : gaussianCompressedLeft (46 : Fin 166) ≤ Real.log n := by
      change (5521 : ℝ) / 8 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (46 : Fin 166) hleft
    change
      ((500926164909 / 500000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h45 : Real.log n ≤ 2763 / 4
  · have hlo := le_of_not_ge h44
    have hleft : gaussianCompressedLeft (47 : Fin 166) ≤ Real.log n := by
      change (2761 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (47 : Fin 166) hleft
    change
      ((250470054231 / 250000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    by_cases hm : Real.log n ≤ 690.399
    · exact HasRejectingPrime.mono (gaussian_k197_cell45_left_witness hn ho hu hGRH ⟨hlo, hm⟩) hcut
    · exact
        HasRejectingPrime.mono
          (gaussian_k197_cell45_right_witness hn ho hu hGRH ⟨le_of_not_ge hm, h45⟩) hcut
  by_cases h46 : Real.log n ≤ 2767 / 4
  · have hlo := le_of_not_ge h45
    have hw := gaussian_k197_cell46_witness hn ho hu hGRH ⟨hlo, h46⟩
    have hleft : gaussianCompressedLeft (48 : Fin 166) ≤ Real.log n := by
      change (2763 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (48 : Fin 166) hleft
    change
      ((1001908063039 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h47 : Real.log n ≤ 2771 / 4
  · have hlo := le_of_not_ge h46
    have hw := gaussian_k197_cell47_witness hn ho hu hGRH ⟨hlo, h47⟩
    have hleft : gaussianCompressedLeft (49 : Fin 166) ≤ Real.log n := by
      change (2767 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (49 : Fin 166) hleft
    change
      ((1001963632661 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h48 : Real.log n ≤ 2773 / 4
  · have hlo := le_of_not_ge h47
    have hw := gaussian_k197_cell48_witness hn ho hu hGRH ⟨hlo, h48⟩
    have hleft : gaussianCompressedLeft (50 : Fin 166) ≤ Real.log n := by
      change (2771 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (50 : Fin 166) hleft
    change
      ((501009519703 / 500000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h49 : Real.log n ≤ 2775 / 4
  · have hlo := le_of_not_ge h48
    have hw := gaussian_k197_cell49_witness hn ho hu hGRH ⟨hlo, h49⟩
    have hleft : gaussianCompressedLeft (51 : Fin 166) ≤ Real.log n := by
      change (2773 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (51 : Fin 166) hleft
    change
      ((501009519703 / 500000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h50 : Real.log n ≤ 2779 / 4
  · have hlo := le_of_not_ge h49
    have hw := gaussian_k197_cell50_witness hn ho hu hGRH ⟨hlo, h50⟩
    have hleft : gaussianCompressedLeft (52 : Fin 166) ≤ Real.log n := by
      change (2775 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (52 : Fin 166) hleft
    change
      ((1002074283993 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h51 : Real.log n ≤ 2783 / 4
  · have hlo := le_of_not_ge h50
    have hw := gaussian_k197_cell51_witness hn ho hu hGRH ⟨hlo, h51⟩
    have hleft : gaussianCompressedLeft (53 : Fin 166) ≤ Real.log n := by
      change (2779 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (53 : Fin 166) hleft
    change
      ((1002074283993 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h52 : Real.log n ≤ 2791 / 4
  · have hlo := le_of_not_ge h51
    have hw := gaussian_k197_cell52_witness hn ho hu hGRH ⟨hlo, h52⟩
    have hleft : gaussianCompressedLeft (54 : Fin 166) ≤ Real.log n := by
      change (2783 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (54 : Fin 166) hleft
    change
      ((1002184289539 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h53 : Real.log n ≤ 2799 / 4
  · have hlo := le_of_not_ge h52
    have hw := gaussian_k197_cell53_witness hn ho hu hGRH ⟨hlo, h53⟩
    have hleft : gaussianCompressedLeft (55 : Fin 166) ≤ Real.log n := by
      change (2791 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (55 : Fin 166) hleft
    change
      ((1002293654961 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h54 : Real.log n ≤ 2807 / 4
  · have hlo := le_of_not_ge h53
    have hw := gaussian_k197_cell54_witness hn ho hu hGRH ⟨hlo, h54⟩
    have hleft : gaussianCompressedLeft (56 : Fin 166) ≤ Real.log n := by
      change (2799 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (56 : Fin 166) hleft
    change
      ((250600596463 / 250000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h55 : Real.log n ≤ 2815 / 4
  · have hlo := le_of_not_ge h54
    have hw := gaussian_k197_cell55_witness hn ho hu hGRH ⟨hlo, h55⟩
    have hleft : gaussianCompressedLeft (57 : Fin 166) ≤ Real.log n := by
      change (2807 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (57 : Fin 166) hleft
    change
      ((501255243871 / 500000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h56 : Real.log n ≤ 2823 / 4
  · have hlo := le_of_not_ge h55
    have hw := gaussian_k197_cell56_witness hn ho hu hGRH ⟨hlo, h56⟩
    have hleft : gaussianCompressedLeft (58 : Fin 166) ≤ Real.log n := by
      change (2815 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (58 : Fin 166) hleft
    change
      ((501255243871 / 500000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h57 : Real.log n ≤ 2839 / 4
  · have hlo := le_of_not_ge h56
    have hw := gaussian_k197_cell57_witness hn ho hu hGRH ⟨hlo, h57⟩
    have hleft : gaussianCompressedLeft (59 : Fin 166) ≤ Real.log n := by
      change (2823 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (59 : Fin 166) hleft
    change
      ((1002724826311 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h58 : Real.log n ≤ 2847 / 4
  · have hlo := le_of_not_ge h57
    have hw := gaussian_k197_cell58_witness hn ho hu hGRH ⟨hlo, h58⟩
    have hleft : gaussianCompressedLeft (60 : Fin 166) ≤ Real.log n := by
      change (2839 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (60 : Fin 166) hleft
    change
      ((1002936713637 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h59 : Real.log n ≤ 2855 / 4
  · have hlo := le_of_not_ge h58
    have hw := gaussian_k197_cell59_witness hn ho hu hGRH ⟨hlo, h59⟩
    have hleft : gaussianCompressedLeft (61 : Fin 166) ≤ Real.log n := by
      change (2847 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (61 : Fin 166) hleft
    change
      ((501520875621 / 500000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h60 : Real.log n ≤ 2863 / 4
  · have hlo := le_of_not_ge h59
    have hw := gaussian_k197_cell60_witness hn ho hu hGRH ⟨hlo, h60⟩
    have hleft : gaussianCompressedLeft (62 : Fin 166) ≤ Real.log n := by
      change (2855 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (62 : Fin 166) hleft
    change
      ((125393273963 / 125000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h61 : Real.log n ≤ 2879 / 4
  · have hlo := le_of_not_ge h60
    have hw := gaussian_k197_cell61_witness hn ho hu hGRH ⟨hlo, h61⟩
    have hleft : gaussianCompressedLeft (63 : Fin 166) ≤ Real.log n := by
      change (2863 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (63 : Fin 166) hleft
    change
      ((8026000321 / 8000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h62 : Real.log n ≤ 2895 / 4
  · have hlo := le_of_not_ge h61
    have hw := gaussian_k197_cell62_witness hn ho hu hGRH ⟨hlo, h62⟩
    have hleft : gaussianCompressedLeft (64 : Fin 166) ≤ Real.log n := by
      change (2879 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (64 : Fin 166) hleft
    change
      ((1003455980947 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h63 : Real.log n ≤ 2911 / 4
  · have hlo := le_of_not_ge h62
    have hw := gaussian_k197_cell63_witness hn ho hu hGRH ⟨hlo, h63⟩
    have hleft : gaussianCompressedLeft (65 : Fin 166) ≤ Real.log n := by
      change (2895 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (65 : Fin 166) hleft
    change
      ((12545745167 / 12500000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h64 : Real.log n ≤ 2927 / 4
  · have hlo := le_of_not_ge h63
    have hw := gaussian_k197_cell64_witness hn ho hu hGRH ⟨hlo, h64⟩
    have hleft : gaussianCompressedLeft (66 : Fin 166) ≤ Real.log n := by
      change (2911 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (66 : Fin 166) hleft
    change
      ((501930488063 / 500000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h65 : Real.log n ≤ 2943 / 4
  · have hlo := le_of_not_ge h64
    have hw := gaussian_k197_cell65_witness hn ho hu hGRH ⟨hlo, h65⟩
    have hleft : gaussianCompressedLeft (67 : Fin 166) ≤ Real.log n := by
      change (2927 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (67 : Fin 166) hleft
    change
      ((125507513393 / 125000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h66 : Real.log n ≤ 2959 / 4
  · have hlo := le_of_not_ge h65
    have hw := gaussian_k197_cell66_witness hn ho hu hGRH ⟨hlo, h66⟩
    have hleft : gaussianCompressedLeft (68 : Fin 166) ≤ Real.log n := by
      change (2943 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (68 : Fin 166) hleft
    change
      ((251064260869 / 250000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h67 : Real.log n ≤ 2975 / 4
  · have hlo := le_of_not_ge h66
    have hw := gaussian_k197_cell67_witness hn ho hu hGRH ⟨hlo, h67⟩
    have hleft : gaussianCompressedLeft (69 : Fin 166) ≤ Real.log n := by
      change (2959 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (69 : Fin 166) hleft
    change
      ((200890364273 / 200000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h68 : Real.log n ≤ 2991 / 4
  · have hlo := le_of_not_ge h67
    have hw := gaussian_k197_cell68_witness hn ho hu hGRH ⟨hlo, h68⟩
    have hleft : gaussianCompressedLeft (70 : Fin 166) ≤ Real.log n := by
      change (2975 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (70 : Fin 166) hleft
    change
      ((50232223813 / 50000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h69 : Real.log n ≤ 3007 / 4
  · have hlo := le_of_not_ge h68
    have hw := gaussian_k197_cell69_witness hn ho hu hGRH ⟨hlo, h69⟩
    have hleft : gaussianCompressedLeft (71 : Fin 166) ≤ Real.log n := by
      change (2991 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (71 : Fin 166) hleft
    change
      ((25120876071 / 25000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h70 : Real.log n ≤ 3023 / 4
  · have hlo := le_of_not_ge h69
    have hw := gaussian_k197_cell70_witness hn ho hu hGRH ⟨hlo, h70⟩
    have hleft : gaussianCompressedLeft (72 : Fin 166) ≤ Real.log n := by
      change (3007 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (72 : Fin 166) hleft
    change
      ((100502355503 / 100000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h71 : Real.log n ≤ 3039 / 4
  · have hlo := le_of_not_ge h70
    have hw := gaussian_k197_cell71_witness hn ho hu hGRH ⟨hlo, h71⟩
    have hleft : gaussianCompressedLeft (73 : Fin 166) ≤ Real.log n := by
      change (3023 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (73 : Fin 166) hleft
    change
      ((40208401841 / 40000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h72 : Real.log n ≤ 3055 / 4
  · have hlo := le_of_not_ge h71
    have hw := gaussian_k197_cell72_witness hn ho hu hGRH ⟨hlo, h72⟩
    have hleft : gaussianCompressedLeft (74 : Fin 166) ≤ Real.log n := by
      change (3039 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (74 : Fin 166) hleft
    change
      ((1005394548309 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h73 : Real.log n ≤ 3071 / 4
  · have hlo := le_of_not_ge h72
    have hw := gaussian_k197_cell73_witness hn ho hu hGRH ⟨hlo, h73⟩
    have hleft : gaussianCompressedLeft (75 : Fin 166) ≤ Real.log n := by
      change (3055 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (75 : Fin 166) hleft
    change
      ((125697136709 / 125000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h74 : Real.log n ≤ 3087 / 4
  · have hlo := le_of_not_ge h73
    have hw := gaussian_k197_cell74_witness hn ho hu hGRH ⟨hlo, h74⟩
    have hleft : gaussianCompressedLeft (76 : Fin 166) ≤ Real.log n := by
      change (3071 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (76 : Fin 166) hleft
    change
      ((62859857077 / 62500000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h75 : Real.log n ≤ 3103 / 4
  · have hlo := le_of_not_ge h74
    have hw := gaussian_k197_cell75_witness hn ho hu hGRH ⟨hlo, h75⟩
    have hleft : gaussianCompressedLeft (77 : Fin 166) ≤ Real.log n := by
      change (3087 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (77 : Fin 166) hleft
    change
      ((62859857077 / 62500000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h76 : Real.log n ≤ 3135 / 4
  · have hlo := le_of_not_ge h75
    have hw := gaussian_k197_cell76_witness hn ho hu hGRH ⟨hlo, h76⟩
    have hleft : gaussianCompressedLeft (78 : Fin 166) ≤ Real.log n := by
      change (3103 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (78 : Fin 166) hleft
    change
      ((1006113296139 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h77 : Real.log n ≤ 3167 / 4
  · have hlo := le_of_not_ge h76
    have hw := gaussian_k197_cell77_witness hn ho hu hGRH ⟨hlo, h77⟩
    have hleft : gaussianCompressedLeft (79 : Fin 166) ≤ Real.log n := by
      change (3135 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (79 : Fin 166) hleft
    change
      ((1006461533141 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h78 : Real.log n ≤ 3199 / 4
  · have hlo := le_of_not_ge h77
    have hw := gaussian_k197_cell78_witness hn ho hu hGRH ⟨hlo, h78⟩
    have hleft : gaussianCompressedLeft (80 : Fin 166) ≤ Real.log n := by
      change (3167 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (80 : Fin 166) hleft
    change
      ((503401325321 / 500000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h79 : Real.log n ≤ 3231 / 4
  · have hlo := le_of_not_ge h78
    have hw := gaussian_k197_cell79_witness hn ho hu hGRH ⟨hlo, h79⟩
    have hleft : gaussianCompressedLeft (81 : Fin 166) ≤ Real.log n := by
      change (3199 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (81 : Fin 166) hleft
    change
      ((1007136865833 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h80 : Real.log n ≤ 3247 / 4
  · have hlo := le_of_not_ge h79
    have hw := gaussian_k197_cell80_witness hn ho hu hGRH ⟨hlo, h80⟩
    have hleft : gaussianCompressedLeft (82 : Fin 166) ≤ Real.log n := by
      change (3231 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (82 : Fin 166) hleft
    change
      ((1007464387157 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h81 : Real.log n ≤ 3263 / 4
  · have hlo := le_of_not_ge h80
    have hw := gaussian_k197_cell81_witness hn ho hu hGRH ⟨hlo, h81⟩
    have hleft : gaussianCompressedLeft (83 : Fin 166) ≤ Real.log n := by
      change (3247 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (83 : Fin 166) hleft
    change
      ((503812850237 / 500000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h82 : Real.log n ≤ 3279 / 4
  · have hlo := le_of_not_ge h81
    have hw := gaussian_k197_cell82_witness hn ho hu hGRH ⟨hlo, h82⟩
    have hleft : gaussianCompressedLeft (84 : Fin 166) ≤ Real.log n := by
      change (3263 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (84 : Fin 166) hleft
    change
      ((503892707373 / 500000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h83 : Real.log n ≤ 3295 / 4
  · have hlo := le_of_not_ge h82
    have hw := gaussian_k197_cell83_witness hn ho hu hGRH ⟨hlo, h83⟩
    have hleft : gaussianCompressedLeft (85 : Fin 166) ≤ Real.log n := by
      change (3279 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (85 : Fin 166) hleft
    change
      ((6299647211 / 6250000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h84 : Real.log n ≤ 3311 / 4
  · have hlo := le_of_not_ge h83
    have hw := gaussian_k197_cell84_witness hn ho hu hGRH ⟨hlo, h84⟩
    have hleft : gaussianCompressedLeft (86 : Fin 166) ≤ Real.log n := by
      change (3295 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (86 : Fin 166) hleft
    change
      ((6299647211 / 6250000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h85 : Real.log n ≤ 3327 / 4
  · have hlo := le_of_not_ge h84
    have hw := gaussian_k197_cell85_witness hn ho hu hGRH ⟨hlo, h85⟩
    have hleft : gaussianCompressedLeft (87 : Fin 166) ≤ Real.log n := by
      change (3311 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (87 : Fin 166) hleft
    change
      ((504127599407 / 500000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h86 : Real.log n ≤ 3343 / 4
  · have hlo := le_of_not_ge h85
    have hw := gaussian_k197_cell86_witness hn ho hu hGRH ⟨hlo, h86⟩
    have hleft : gaussianCompressedLeft (88 : Fin 166) ≤ Real.log n := by
      change (3327 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (88 : Fin 166) hleft
    change
      ((504204375061 / 500000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h87 : Real.log n ≤ 3359 / 4
  · have hlo := le_of_not_ge h86
    have hw := gaussian_k197_cell87_witness hn ho hu hGRH ⟨hlo, h87⟩
    have hleft : gaussianCompressedLeft (89 : Fin 166) ≤ Real.log n := by
      change (3343 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (89 : Fin 166) hleft
    change
      ((100856081673 / 100000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h88 : Real.log n ≤ 3375 / 4
  · have hlo := le_of_not_ge h87
    have hw := gaussian_k197_cell88_witness hn ho hu hGRH ⟨hlo, h88⟩
    have hleft : gaussianCompressedLeft (90 : Fin 166) ≤ Real.log n := by
      change (3359 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (90 : Fin 166) hleft
    change
      ((100856081673 / 100000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h89 : Real.log n ≤ 3407 / 4
  · have hlo := le_of_not_ge h88
    have hw := gaussian_k197_cell89_witness hn ho hu hGRH ⟨hlo, h89⟩
    have hleft : gaussianCompressedLeft (91 : Fin 166) ≤ Real.log n := by
      change (3375 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (91 : Fin 166) hleft
    change
      ((126107572703 / 125000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h90 : Real.log n ≤ 3439 / 4
  · have hlo := le_of_not_ge h89
    have hw := gaussian_k197_cell90_witness hn ho hu hGRH ⟨hlo, h90⟩
    have hleft : gaussianCompressedLeft (92 : Fin 166) ≤ Real.log n := by
      change (3407 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (92 : Fin 166) hleft
    change
      ((1009154660969 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h91 : Real.log n ≤ 3471 / 4
  · have hlo := le_of_not_ge h90
    have hw := gaussian_k197_cell91_witness hn ho hu hGRH ⟨hlo, h91⟩
    have hleft : gaussianCompressedLeft (93 : Fin 166) ≤ Real.log n := by
      change (3439 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (93 : Fin 166) hleft
    change
      ((201888643181 / 200000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h92 : Real.log n ≤ 3503 / 4
  · have hlo := le_of_not_ge h91
    have hw := gaussian_k197_cell92_witness hn ho hu hGRH ⟨hlo, h92⟩
    have hleft : gaussianCompressedLeft (94 : Fin 166) ≤ Real.log n := by
      change (3471 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (94 : Fin 166) hleft
    change
      ((50486320077 / 50000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h93 : Real.log n ≤ 3535 / 4
  · have hlo := le_of_not_ge h92
    have hw := gaussian_k197_cell93_witness hn ho hu hGRH ⟨hlo, h93⟩
    have hleft : gaussianCompressedLeft (95 : Fin 166) ≤ Real.log n := by
      change (3503 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (95 : Fin 166) hleft
    change
      ((505002183613 / 500000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h94 : Real.log n ≤ 3567 / 4
  · have hlo := le_of_not_ge h93
    have hw := gaussian_k197_cell94_witness hn ho hu hGRH ⟨hlo, h94⟩
    have hleft : gaussianCompressedLeft (96 : Fin 166) ≤ Real.log n := by
      change (3535 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (96 : Fin 166) hleft
    change
      ((126284657103 / 125000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h95 : Real.log n ≤ 3599 / 4
  · have hlo := le_of_not_ge h94
    have hw := gaussian_k197_cell95_witness hn ho hu hGRH ⟨hlo, h95⟩
    have hleft : gaussianCompressedLeft (97 : Fin 166) ≤ Real.log n := by
      change (3567 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (97 : Fin 166) hleft
    change
      ((505272604479 / 500000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h96 : Real.log n ≤ 3631 / 4
  · have hlo := le_of_not_ge h95
    have hw := gaussian_k197_cell96_witness hn ho hu hGRH ⟨hlo, h96⟩
    have hleft : gaussianCompressedLeft (98 : Fin 166) ≤ Real.log n := by
      change (3599 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (98 : Fin 166) hleft
    change
      ((1010808357247 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h97 : Real.log n ≤ 3663 / 4
  · have hlo := le_of_not_ge h96
    have hw := gaussian_k197_cell97_witness hn ho hu hGRH ⟨hlo, h97⟩
    have hleft : gaussianCompressedLeft (99 : Fin 166) ≤ Real.log n := by
      change (3631 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (99 : Fin 166) hleft
    change
      ((101106683053 / 100000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h98 : Real.log n ≤ 3695 / 4
  · have hlo := le_of_not_ge h97
    have hw := gaussian_k197_cell98_witness hn ho hu hGRH ⟨hlo, h98⟩
    have hleft : gaussianCompressedLeft (100 : Fin 166) ≤ Real.log n := by
      change (3663 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (100 : Fin 166) hleft
    change
      ((505660376539 / 500000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h99 : Real.log n ≤ 3727 / 4
  · have hlo := le_of_not_ge h98
    have hw := gaussian_k197_cell99_witness hn ho hu hGRH ⟨hlo, h99⟩
    have hleft : gaussianCompressedLeft (101 : Fin 166) ≤ Real.log n := by
      change (3695 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (101 : Fin 166) hleft
    change
      ((252892561199 / 250000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h100 : Real.log n ≤ 3791 / 4
  · have hlo := le_of_not_ge h99
    have hw := gaussian_k197_cell100_witness hn ho hu hGRH ⟨hlo, h100⟩
    have hleft : gaussianCompressedLeft (102 : Fin 166) ≤ Real.log n := by
      change (3727 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (102 : Fin 166) hleft
    change
      ((1011815421411 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h101 : Real.log n ≤ 3823 / 4
  · have hlo := le_of_not_ge h100
    have hw := gaussian_k197_cell101_witness hn ho hu hGRH ⟨hlo, h101⟩
    have hleft : gaussianCompressedLeft (103 : Fin 166) ≤ Real.log n := by
      change (3791 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (103 : Fin 166) hleft
    change
      ((1012293272431 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h102 : Real.log n ≤ 3855 / 4
  · have hlo := le_of_not_ge h101
    have hw := gaussian_k197_cell102_witness hn ho hu hGRH ⟨hlo, h102⟩
    have hleft : gaussianCompressedLeft (104 : Fin 166) ≤ Real.log n := by
      change (3823 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (104 : Fin 166) hleft
    change
      ((1012526158983 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h103 : Real.log n ≤ 3919 / 4
  · have hlo := le_of_not_ge h102
    have hw := gaussian_k197_cell103_witness hn ho hu hGRH ⟨hlo, h103⟩
    have hleft : gaussianCompressedLeft (105 : Fin 166) ≤ Real.log n := by
      change (3855 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (105 : Fin 166) hleft
    change
      ((506377577521 / 500000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h104 : Real.log n ≤ 3983 / 4
  · have hlo := le_of_not_ge h103
    have hw := gaussian_k197_cell104_witness hn ho hu hGRH ⟨hlo, h104⟩
    have hleft : gaussianCompressedLeft (106 : Fin 166) ≤ Real.log n := by
      change (3919 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (106 : Fin 166) hleft
    change
      ((506600930973 / 500000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h105 : Real.log n ≤ 4047 / 4
  · have hlo := le_of_not_ge h104
    have hw := gaussian_k197_cell105_witness hn ho hu hGRH ⟨hlo, h105⟩
    have hleft : gaussianCompressedLeft (107 : Fin 166) ≤ Real.log n := by
      change (3983 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (107 : Fin 166) hleft
    change
      ((1013634134211 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h106 : Real.log n ≤ 4111 / 4
  · have hlo := le_of_not_ge h105
    have hw := gaussian_k197_cell106_witness hn ho hu hGRH ⟨hlo, h106⟩
    have hleft : gaussianCompressedLeft (108 : Fin 166) ≤ Real.log n := by
      change (4047 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (108 : Fin 166) hleft
    change
      ((126756583177 / 125000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h107 : Real.log n ≤ 4175 / 4
  · have hlo := le_of_not_ge h106
    have hw := gaussian_k197_cell107_witness hn ho hu hGRH ⟨hlo, h107⟩
    have hleft : gaussianCompressedLeft (109 : Fin 166) ≤ Real.log n := by
      change (4111 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (109 : Fin 166) hleft
    change
      ((1014458105391 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h108 : Real.log n ≤ 4239 / 4
  · have hlo := le_of_not_ge h107
    have hw := gaussian_k197_cell108_witness hn ho hu hGRH ⟨hlo, h108⟩
    have hleft : gaussianCompressedLeft (110 : Fin 166) ≤ Real.log n := by
      change (4175 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (110 : Fin 166) hleft
    change
      ((15857047869 / 15625000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h109 : Real.log n ≤ 4303 / 4
  · have hlo := le_of_not_ge h108
    have hw := gaussian_k197_cell109_witness hn ho hu hGRH ⟨hlo, h109⟩
    have hleft : gaussianCompressedLeft (111 : Fin 166) ≤ Real.log n := by
      change (4239 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (111 : Fin 166) hleft
    change
      ((1015232112301 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h110 : Real.log n ≤ 4367 / 4
  · have hlo := le_of_not_ge h109
    have hw := gaussian_k197_cell110_witness hn ho hu hGRH ⟨hlo, h110⟩
    have hleft : gaussianCompressedLeft (112 : Fin 166) ≤ Real.log n := by
      change (4303 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (112 : Fin 166) hleft
    change
      ((253900447299 / 250000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h111 : Real.log n ≤ 4431 / 4
  · have hlo := le_of_not_ge h110
    have hw := gaussian_k197_cell111_witness hn ho hu hGRH ⟨hlo, h111⟩
    have hleft : gaussianCompressedLeft (113 : Fin 166) ≤ Real.log n := by
      change (4367 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (113 : Fin 166) hleft
    change
      ((1015960600149 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h112 : Real.log n ≤ 4495 / 4
  · have hlo := le_of_not_ge h111
    have hw := gaussian_k197_cell112_witness hn ho hu hGRH ⟨hlo, h112⟩
    have hleft : gaussianCompressedLeft (114 : Fin 166) ≤ Real.log n := by
      change (4431 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (114 : Fin 166) hleft
    change
      ((101630902143 / 100000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h113 : Real.log n ≤ 4623 / 4
  · have hlo := le_of_not_ge h112
    have hw := gaussian_k197_cell113_witness hn ho hu hGRH ⟨hlo, h113⟩
    have hleft : gaussianCompressedLeft (115 : Fin 166) ≤ Real.log n := by
      change (4495 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (115 : Fin 166) hleft
    change
      ((254161875467 / 250000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h114 : Real.log n ≤ 4751 / 4
  · have hlo := le_of_not_ge h113
    have hw := gaussian_k197_cell114_witness hn ho hu hGRH ⟨hlo, h114⟩
    have hleft : gaussianCompressedLeft (116 : Fin 166) ≤ Real.log n := by
      change (4623 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (116 : Fin 166) hleft
    change
      ((1017296309847 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h115 : Real.log n ≤ 4815 / 4
  · have hlo := le_of_not_ge h114
    have hw := gaussian_k197_cell115_witness hn ho hu hGRH ⟨hlo, h115⟩
    have hleft : gaussianCompressedLeft (117 : Fin 166) ≤ Real.log n := by
      change (4751 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (117 : Fin 166) hleft
    change
      ((1017910135939 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h116 : Real.log n ≤ 4879 / 4
  · have hlo := le_of_not_ge h115
    have hw := gaussian_k197_cell116_witness hn ho hu hGRH ⟨hlo, h116⟩
    have hleft : gaussianCompressedLeft (118 : Fin 166) ≤ Real.log n := by
      change (4815 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (118 : Fin 166) hleft
    change
      ((254551202941 / 250000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h117 : Real.log n ≤ 4943 / 4
  · have hlo := le_of_not_ge h116
    have hw := gaussian_k197_cell117_witness hn ho hu hGRH ⟨hlo, h117⟩
    have hleft : gaussianCompressedLeft (119 : Fin 166) ≤ Real.log n := by
      change (4879 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (119 : Fin 166) hleft
    change
      ((509245880961 / 500000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h118 : Real.log n ≤ 5007 / 4
  · have hlo := le_of_not_ge h117
    have hw := gaussian_k197_cell118_witness hn ho hu hGRH ⟨hlo, h118⟩
    have hleft : gaussianCompressedLeft (120 : Fin 166) ≤ Real.log n := by
      change (4943 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (120 : Fin 166) hleft
    change
      ((63673205597 / 62500000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h119 : Real.log n ≤ 5071 / 4
  · have hlo := le_of_not_ge h118
    have hw := gaussian_k197_cell119_witness hn ho hu hGRH ⟨hlo, h119⟩
    have hleft : gaussianCompressedLeft (121 : Fin 166) ≤ Real.log n := by
      change (5007 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (121 : Fin 166) hleft
    change
      ((1019043682131 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h120 : Real.log n ≤ 5135 / 4
  · have hlo := le_of_not_ge h119
    have hw := gaussian_k197_cell120_witness hn ho hu hGRH ⟨hlo, h120⟩
    have hleft : gaussianCompressedLeft (122 : Fin 166) ≤ Real.log n := by
      change (5071 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (122 : Fin 166) hleft
    change
      ((509654606237 / 500000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h121 : Real.log n ≤ 5199 / 4
  · have hlo := le_of_not_ge h120
    have hw := gaussian_k197_cell121_witness hn ho hu hGRH ⟨hlo, h121⟩
    have hleft : gaussianCompressedLeft (123 : Fin 166) ≤ Real.log n := by
      change (5135 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (123 : Fin 166) hleft
    change
      ((127446017457 / 125000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h122 : Real.log n ≤ 5263 / 4
  · have hlo := le_of_not_ge h121
    have hw := gaussian_k197_cell122_witness hn ho hu hGRH ⟨hlo, h122⟩
    have hleft : gaussianCompressedLeft (124 : Fin 166) ≤ Real.log n := by
      change (5199 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (124 : Fin 166) hleft
    change
      ((127477588733 / 125000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h123 : Real.log n ≤ 5327 / 4
  · have hlo := le_of_not_ge h122
    have hw := gaussian_k197_cell123_witness hn ho hu hGRH ⟨hlo, h123⟩
    have hleft : gaussianCompressedLeft (125 : Fin 166) ≤ Real.log n := by
      change (5263 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (125 : Fin 166) hleft
    change
      ((204013431439 / 200000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h124 : Real.log n ≤ 5391 / 4
  · have hlo := le_of_not_ge h123
    have hw := gaussian_k197_cell124_witness hn ho hu hGRH ⟨hlo, h124⟩
    have hleft : gaussianCompressedLeft (126 : Fin 166) ≤ Real.log n := by
      change (5327 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (126 : Fin 166) hleft
    change
      ((1020307704381 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h125 : Real.log n ≤ 5519 / 4
  · have hlo := le_of_not_ge h124
    have hw := gaussian_k197_cell125_witness hn ho hu hGRH ⟨hlo, h125⟩
    have hleft : gaussianCompressedLeft (127 : Fin 166) ≤ Real.log n := by
      change (5391 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (127 : Fin 166) hleft
    change
      ((510271281739 / 500000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h126 : Real.log n ≤ 5647 / 4
  · have hlo := le_of_not_ge h125
    have hw := gaussian_k197_cell126_witness hn ho hu hGRH ⟨hlo, h126⟩
    have hleft : gaussianCompressedLeft (128 : Fin 166) ≤ Real.log n := by
      change (5519 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (128 : Fin 166) hleft
    change
      ((255249003993 / 250000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h127 : Real.log n ≤ 5775 / 4
  · have hlo := le_of_not_ge h126
    have hw := gaussian_k197_cell127_witness hn ho hu hGRH ⟨hlo, h127⟩
    have hleft : gaussianCompressedLeft (129 : Fin 166) ≤ Real.log n := by
      change (5647 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (129 : Fin 166) hleft
    change
      ((102142902047 / 100000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h128 : Real.log n ≤ 5903 / 4
  · have hlo := le_of_not_ge h127
    have hw := gaussian_k197_cell128_witness hn ho hu hGRH ⟨hlo, h128⟩
    have hleft : gaussianCompressedLeft (130 : Fin 166) ≤ Real.log n := by
      change (5775 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (130 : Fin 166) hleft
    change
      ((510921474027 / 500000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h129 : Real.log n ≤ 6031 / 4
  · have hlo := le_of_not_ge h128
    have hw := gaussian_k197_cell129_witness hn ho hu hGRH ⟨hlo, h129⟩
    have hleft : gaussianCompressedLeft (131 : Fin 166) ≤ Real.log n := by
      change (5903 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (131 : Fin 166) hleft
    change
      ((1022239049827 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h130 : Real.log n ≤ 6159 / 4
  · have hlo := le_of_not_ge h129
    have hw := gaussian_k197_cell130_witness hn ho hu hGRH ⟨hlo, h130⟩
    have hleft : gaussianCompressedLeft (132 : Fin 166) ≤ Real.log n := by
      change (6031 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (132 : Fin 166) hleft
    change
      ((1597841359 / 1562500000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h131 : Real.log n ≤ 6287 / 4
  · have hlo := le_of_not_ge h130
    have hw := gaussian_k197_cell131_witness hn ho hu hGRH ⟨hlo, h131⟩
    have hleft : gaussianCompressedLeft (133 : Fin 166) ≤ Real.log n := by
      change (6159 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (133 : Fin 166) hleft
    change
      ((127872781989 / 125000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h132 : Real.log n ≤ 6415 / 4
  · have hlo := le_of_not_ge h131
    have hw := gaussian_k197_cell132_witness hn ho hu hGRH ⟨hlo, h132⟩
    have hleft : gaussianCompressedLeft (134 : Fin 166) ≤ Real.log n := by
      change (6287 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (134 : Fin 166) hleft
    change
      ((25583284257 / 25000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h133 : Real.log n ≤ 6543 / 4
  · have hlo := le_of_not_ge h132
    have hw := gaussian_k197_cell133_witness hn ho hu hGRH ⟨hlo, h133⟩
    have hleft : gaussianCompressedLeft (135 : Fin 166) ≤ Real.log n := by
      change (6415 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (135 : Fin 166) hleft
    change
      ((255916674363 / 250000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h134 : Real.log n ≤ 6671 / 4
  · have hlo := le_of_not_ge h133
    have hw := gaussian_k197_cell134_witness hn ho hu hGRH ⟨hlo, h134⟩
    have hleft : gaussianCompressedLeft (136 : Fin 166) ≤ Real.log n := by
      change (6543 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (136 : Fin 166) hleft
    change
      ((511994526119 / 500000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h135 : Real.log n ≤ 6799 / 4
  · have hlo := le_of_not_ge h134
    have hw := gaussian_k197_cell135_witness hn ho hu hGRH ⟨hlo, h135⟩
    have hleft : gaussianCompressedLeft (137 : Fin 166) ≤ Real.log n := by
      change (6671 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (137 : Fin 166) hleft
    change
      ((51214959321 / 50000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h136 : Real.log n ≤ 6927 / 4
  · have hlo := le_of_not_ge h135
    have hw := gaussian_k197_cell136_witness hn ho hu hGRH ⟨hlo, h136⟩
    have hleft : gaussianCompressedLeft (138 : Fin 166) ≤ Real.log n := by
      change (6799 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (138 : Fin 166) hleft
    change
      ((512298897363 / 500000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h137 : Real.log n ≤ 7055 / 4
  · have hlo := le_of_not_ge h136
    have hw := gaussian_k197_cell137_witness hn ho hu hGRH ⟨hlo, h137⟩
    have hleft : gaussianCompressedLeft (139 : Fin 166) ≤ Real.log n := by
      change (6927 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (139 : Fin 166) hleft
    change
      ((512442760071 / 500000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h138 : Real.log n ≤ 7183 / 4
  · have hlo := le_of_not_ge h137
    have hw := gaussian_k197_cell138_witness hn ho hu hGRH ⟨hlo, h138⟩
    have hleft : gaussianCompressedLeft (140 : Fin 166) ≤ Real.log n := by
      change (7055 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (140 : Fin 166) hleft
    change
      ((256290739661 / 250000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h139 : Real.log n ≤ 7311 / 4
  · have hlo := le_of_not_ge h138
    have hw := gaussian_k197_cell139_witness hn ho hu hGRH ⟨hlo, h139⟩
    have hleft : gaussianCompressedLeft (141 : Fin 166) ≤ Real.log n := by
      change (7183 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (141 : Fin 166) hleft
    change
      ((1025430663409 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h140 : Real.log n ≤ 7439 / 4
  · have hlo := le_of_not_ge h139
    have hw := gaussian_k197_cell140_witness hn ho hu hGRH ⟨hlo, h140⟩
    have hleft : gaussianCompressedLeft (142 : Fin 166) ≤ Real.log n := by
      change (7311 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (142 : Fin 166) hleft
    change
      ((256422287149 / 250000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h141 : Real.log n ≤ 7567 / 4
  · have hlo := le_of_not_ge h140
    have hw := gaussian_k197_cell141_witness hn ho hu hGRH ⟨hlo, h141⟩
    have hleft : gaussianCompressedLeft (143 : Fin 166) ≤ Real.log n := by
      change (7439 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (143 : Fin 166) hleft
    change
      ((1025938892721 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h142 : Real.log n ≤ 7695 / 4
  · have hlo := le_of_not_ge h141
    have hw := gaussian_k197_cell142_witness hn ho hu hGRH ⟨hlo, h142⟩
    have hleft : gaussianCompressedLeft (144 : Fin 166) ≤ Real.log n := by
      change (7567 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (144 : Fin 166) hleft
    change
      ((513090170847 / 500000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h143 : Real.log n ≤ 7759 / 4
  · have hlo := le_of_not_ge h142
    have hw := gaussian_k197_cell143_witness hn ho hu hGRH ⟨hlo, h143⟩
    have hleft : gaussianCompressedLeft (145 : Fin 166) ≤ Real.log n := by
      change (7695 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (145 : Fin 166) hleft
    change
      ((1026413911551 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h144 : Real.log n ≤ 7823 / 4
  · have hlo := le_of_not_ge h143
    have hw := gaussian_k197_row144_witness hn ho hu hGRH ⟨hlo, h144⟩
    have hleft : gaussianCompressedLeft (146 : Fin 166) ≤ Real.log n := by
      change (7759 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (146 : Fin 166) hleft
    change
      ((513263932131 / 500000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h145 : Real.log n ≤ 7951 / 4
  · have hlo := le_of_not_ge h144
    have hw := gaussian_k197_row145_witness hn ho hu hGRH ⟨hlo, h145⟩
    have hleft : gaussianCompressedLeft (147 : Fin 166) ≤ Real.log n := by
      change (7823 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (147 : Fin 166) hleft
    change
      ((256659997727 / 250000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h146 : Real.log n ≤ 8015 / 4
  · have hlo := le_of_not_ge h145
    have hw := gaussian_k197_row146_witness hn ho hu hGRH ⟨hlo, h146⟩
    have hleft : gaussianCompressedLeft (148 : Fin 166) ≤ Real.log n := by
      change (7951 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (148 : Fin 166) hleft
    change
      ((102685894319 / 100000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h147 : Real.log n ≤ 8079 / 4
  · have hlo := le_of_not_ge h146
    have hw := gaussian_k197_row147_witness hn ho hu hGRH ⟨hlo, h147⟩
    have hleft : gaussianCompressedLeft (149 : Fin 166) ≤ Real.log n := by
      change (8015 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (149 : Fin 166) hleft
    change
      ((32092682933 / 31250000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h148 : Real.log n ≤ 8143 / 4
  · have hlo := le_of_not_ge h147
    have hw := gaussian_k197_row148_witness hn ho hu hGRH ⟨hlo, h148⟩
    have hleft : gaussianCompressedLeft (150 : Fin 166) ≤ Real.log n := by
      change (8079 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (150 : Fin 166) hleft
    change
      ((513535554317 / 500000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h149 : Real.log n ≤ 8207 / 4
  · have hlo := le_of_not_ge h148
    have hw := gaussian_k197_row149_witness hn ho hu hGRH ⟨hlo, h149⟩
    have hleft : gaussianCompressedLeft (151 : Fin 166) ≤ Real.log n := by
      change (8143 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (151 : Fin 166) hleft
    change
      ((1027174746727 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h150 : Real.log n ≤ 8271 / 4
  · have hlo := le_of_not_ge h149
    have hw := gaussian_k197_row150_witness hn ho hu hGRH ⟨hlo, h150⟩
    have hleft : gaussianCompressedLeft (152 : Fin 166) ≤ Real.log n := by
      change (8207 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (152 : Fin 166) hleft
    change
      ((102727680611 / 100000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h151 : Real.log n ≤ 8335 / 4
  · have hlo := le_of_not_ge h150
    have hw := gaussian_k197_row151_witness hn ho hu hGRH ⟨hlo, h151⟩
    have hleft : gaussianCompressedLeft (153 : Fin 166) ≤ Real.log n := by
      change (8271 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (153 : Fin 166) hleft
    change
      ((513688661787 / 500000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h152 : Real.log n ≤ 8399 / 4
  · have hlo := le_of_not_ge h151
    have hw := gaussian_k197_row152_witness hn ho hu hGRH ⟨hlo, h152⟩
    have hleft : gaussianCompressedLeft (154 : Fin 166) ≤ Real.log n := by
      change (8335 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (154 : Fin 166) hleft
    change
      ((1027476334773 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h153 : Real.log n ≤ 8527 / 4
  · have hlo := le_of_not_ge h152
    have hw := gaussian_k197_row153_witness hn ho hu hGRH ⟨hlo, h153⟩
    have hleft : gaussianCompressedLeft (155 : Fin 166) ≤ Real.log n := by
      change (8399 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (155 : Fin 166) hleft
    change
      ((1027573874267 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h154 : Real.log n ≤ 8591 / 4
  · have hlo := le_of_not_ge h153
    have hw := gaussian_k197_row154_witness hn ho hu hGRH ⟨hlo, h154⟩
    have hleft : gaussianCompressedLeft (156 : Fin 166) ≤ Real.log n := by
      change (8527 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (156 : Fin 166) hleft
    change
      ((205552934231 / 200000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h155 : Real.log n ≤ 8655 / 4
  · have hlo := le_of_not_ge h154
    have hw := gaussian_k197_row155_witness hn ho hu hGRH ⟨hlo, h155⟩
    have hleft : gaussianCompressedLeft (157 : Fin 166) ≤ Real.log n := by
      change (8591 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (157 : Fin 166) hleft
    change
      ((513928996283 / 500000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h156 : Real.log n ≤ 8719 / 4
  · have hlo := le_of_not_ge h155
    have hw := gaussian_k197_row156_witness hn ho hu hGRH ⟨hlo, h156⟩
    have hleft : gaussianCompressedLeft (158 : Fin 166) ≤ Real.log n := by
      change (8655 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (158 : Fin 166) hleft
    change
      ((128493746297 / 125000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h157 : Real.log n ≤ 8783 / 4
  · have hlo := le_of_not_ge h156
    have hw := gaussian_k197_row157_witness hn ho hu hGRH ⟨hlo, h157⟩
    have hleft : gaussianCompressedLeft (159 : Fin 166) ≤ Real.log n := by
      change (8719 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (159 : Fin 166) hleft
    change
      ((205608126853 / 200000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h158 : Real.log n ≤ 8847 / 4
  · have hlo := le_of_not_ge h157
    have hw := gaussian_k197_row158_witness hn ho hu hGRH ⟨hlo, h158⟩
    have hleft : gaussianCompressedLeft (160 : Fin 166) ≤ Real.log n := by
      change (8783 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (160 : Fin 166) hleft
    change
      ((1028130013039 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h159 : Real.log n ≤ 8911 / 4
  · have hlo := le_of_not_ge h158
    have hw := gaussian_k197_row159_witness hn ho hu hGRH ⟨hlo, h159⟩
    have hleft : gaussianCompressedLeft (161 : Fin 166) ≤ Real.log n := by
      change (8847 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (161 : Fin 166) hleft
    change
      ((1028218134669 / 1000000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h160 : Real.log n ≤ 8975 / 4
  · have hlo := le_of_not_ge h159
    have hw := gaussian_k197_row160_witness hn ho hu hGRH ⟨hlo, h160⟩
    have hleft : gaussianCompressedLeft (162 : Fin 166) ≤ Real.log n := by
      change (8911 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (162 : Fin 166) hleft
    change
      ((205661005263 / 200000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h161 : Real.log n ≤ 9007 / 4
  · have hlo := le_of_not_ge h160
    have hw := gaussian_k197_row161_witness hn ho hu hGRH ⟨hlo, h161⟩
    have hleft : gaussianCompressedLeft (163 : Fin 166) ≤ Real.log n := by
      change (8975 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (163 : Fin 166) hleft
    change
      ((514195357179 / 500000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h162 : Real.log n ≤ 9039 / 4
  · have hlo := le_of_not_ge h161
    have hw := gaussian_k197_row162_witness hn ho hu hGRH ⟨hlo, h162⟩
    have hleft : gaussianCompressedLeft (164 : Fin 166) ≤ Real.log n := by
      change (9007 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (164 : Fin 166) hleft
    change
      ((205686623013 / 200000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases h163 : Real.log n ≤ 9055 / 4
  · have hlo := le_of_not_ge h162
    have hw := gaussian_k197_row163_witness hn ho hu hGRH ⟨hlo, h163⟩
    have hleft : gaussianCompressedLeft (165 : Fin 166) ≤ Real.log n := by
      change (9039 : ℝ) / 4 ≤ Real.log n
      exact hlo
    have hcut := gaussian_compressed_cutoff (165 : Fin 166) hleft
    change
      ((514237612213 / 500000000000 : ℝ) * Real.log n / 2) ^ 2 ≤
        gaussianWitnessCutoff (Real.log n) at hcut
    exact HasRejectingPrime.mono hw hcut
  by_cases hb : Real.log n ≤ 8000
  · have ha := le_of_not_ge h163
    exact (hbridge hu ha hb).mono (gaussian_bridge_bound ha le_rfl)
  have ha := le_of_not_ge hb
  exact htail hu ha

/-- Reuse a tail already proved with the old Gaussian cutoff. -/
theorem uniform_gaussian_witness_of_tails {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hL : 663 ≤ Real.log n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hbridge :
      UniformKorseltTriple n →
        9055 / 4 ≤ Real.log n →
        Real.log n ≤ 8000 → HasRejectingPrime n (gaussianBridgeScale (Real.log n) ^ 2))
    (htail :
      UniformKorseltTriple n →
        8000 ≤ Real.log n →
        HasRejectingPrime n
          (max 2
            (max ((1 / 4 : ℝ) * Real.log n ^ 2)
              ((9090 / 33659 : ℝ) * Real.log n ^ 2 -
                8 * Real.log n * Real.exp (-(Real.log n / 1000000) ^ 2))))) :
    HasRejectingPrime n (gaussianWitnessCutoff (Real.log n)) := by
  apply uniform_gaussian_witness_of_cutoff hn ho hu hL hGRH hbridge
  intro h ha
  exact (htail h ha).mono (gaussian_old_cutoff_le ha)

/-- Compatibility form of the Gaussian range assembly with the compressed prefix supplied. -/
theorem uniform_gaussian_witness_of_ranges {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hL : 663 ≤ Real.log n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (_hcell :
      UniformKorseltTriple n →
        2657 / 4 < Real.log n →
        ∀ i : Fin 166,
          gaussianCompressedLeft i ≤ Real.log n →
            Real.log n ≤ gaussianCompressedRight i →
            HasRejectingPrime n ((gaussianCompressedScale i * Real.log n / 2) ^ 2))
    (hbridge :
      UniformKorseltTriple n →
        9055 / 4 ≤ Real.log n →
        Real.log n ≤ 8000 → HasRejectingPrime n (gaussianBridgeScale (Real.log n) ^ 2))
    (htail :
      UniformKorseltTriple n →
        8000 ≤ Real.log n →
        HasRejectingPrime n
          (max 2
            (max ((1 / 4 : ℝ) * Real.log n ^ 2)
              ((9090 / 33659 : ℝ) * Real.log n ^ 2 -
                8 * Real.log n * Real.exp (-(Real.log n / 1000000) ^ 2))))) :
    HasRejectingPrime n (gaussianWitnessCutoff (Real.log n)) := by
  exact uniform_gaussian_witness_of_tails hn ho hu hL hGRH hbridge htail

/-- Combine a Gaussian witness for uniform triples above log 663 with
the quarter bound for the low and nonuniform cases. -/
theorem gaussian_criterion_of_uniform_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hu :
      UniformKorseltTriple n →
        663 ≤ Real.log n → HasRejectingPrime n (gaussianWitnessCutoff (Real.log n))) :
    (∀ p : ℕ,
        p.Prime →
          (p : ℝ) ≤ gaussianWitnessCutoff (Real.log n) →
          PrimeTest.StrongMillerRabinPass n (p : ZMod n)) ↔
      n.Prime := by
  refine ⟨fun hpass ↦ ?_, fun hp _ hprime hb ↦ gaussian_prime_pass ho hp hprime hb⟩
  by_contra hc
  have hw : HasRejectingPrime n (gaussianWitnessCutoff (Real.log n)) := by
    by_cases hlow : Real.log n ≤ 663 ∨ ¬UniformKorseltTriple n
    · exact gaussian_quarter_witness hn ho hc hGRH hlow
    exact
      hu (Classical.not_not.mp (fun h ↦ hlow (Or.inr h))) (le_of_not_ge (fun h ↦ hlow (Or.inl h)))
  obtain ⟨p, hp, hb, hf⟩ := hw
  exact hf (hpass p hp hb)

/-- The Gaussian criterion follows from the remaining compressed cells, the
affine K131 interval and the old Gaussian envelope on the final half-line.
The quarter bounds and the three K137 cells are supplied unconditionally under GRH. -/
theorem gaussian_criterion_of_uniform {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hcell :
      UniformKorseltTriple n →
        2657 / 4 < Real.log n →
        ∀ i : Fin 166,
          gaussianCompressedLeft i ≤ Real.log n →
            Real.log n ≤ gaussianCompressedRight i →
            HasRejectingPrime n ((gaussianCompressedScale i * Real.log n / 2) ^ 2))
    (hbridge :
      UniformKorseltTriple n →
        9055 / 4 ≤ Real.log n →
        Real.log n ≤ 8000 → HasRejectingPrime n (gaussianBridgeScale (Real.log n) ^ 2))
    (htail :
      UniformKorseltTriple n →
        8000 ≤ Real.log n →
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
      (fun hu hL ↦ uniform_gaussian_witness_of_ranges hn ho hu hL hGRH hcell hbridge htail)

end PseudoPrime.PrimeTestBounds.MillerRabin
