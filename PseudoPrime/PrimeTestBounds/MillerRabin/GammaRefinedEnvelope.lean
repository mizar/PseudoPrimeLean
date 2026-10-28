/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaMidscaleEnvelope
public import PseudoPrime.LLS.GammaCheckpoint1000Refined

/-! # Refined 1000-prefix Gamma bounds without new node data -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The clipped Gamma bound at cutoff 1000 and certified credit 413/100.
It is a separate definition, leaving the 203/50-credit bound unchanged.
Its full-input witness theorem applies for L>=120. -/
noncomputable def gamma1000RefinedBound (L : ℝ) : ℝ :=
  gammaClippedPrefixBound L 1000 (413 / 100)

/-- At L>=120, the root with credit 413/100 is greater than 70.
Its gap at 70 is negative on the half-line. This separates the active root
from the prefix floor and permits a strict credit comparison. -/
theorem root70_lower {L : ℝ} (hL : 120 ≤ L) : (70 : ℝ) < gammaClippedPrefixRoot L (413 / 100) := by
  by_contra h
  have hgap :=
    gammaClippedPrefixGap_nonneg_of_root_le hL
      (by norm_num only : 0 ≤ 143420077 / 11856000 - 2 * (413 / 100 : ℝ)) (le_of_not_gt h)
  dsimp only [gammaClippedPrefixGap] at hgap
  linarith only [hgap, hL]

/-- At L>=120, the refined 1000-prefix bound is strictly below the 203/50-credit branch.
Compare roots using the larger credit and keep the common floor below the old root.
This is a continuous half-line comparison. -/
theorem prefix1000Refined_lt_first {L : ℝ} (hL : 120 ≤ L) :
    gamma1000RefinedBound L < gammaClippedBound1000 L := by
  have hroot :=
    root_credit_strict hL (by norm_num only : 0 ≤ 143420077 / 11856000 - 2 * (203 / 50 : ℝ))
      (by norm_num only : 0 ≤ 143420077 / 11856000 - 2 * (413 / 100 : ℝ))
      (by norm_num only : (203 / 50 : ℝ) < 413 / 100)
  have hfloor : Real.sqrt ((40 / 99 : ℝ) * 1000) < gammaClippedPrefixRoot L (203 / 50) := by
    have hs : Real.sqrt ((40 / 99 : ℝ) * 1000) < 70 :=
      (Real.sqrt_lt (by norm_num only) (by norm_num only)).mpr (by norm_num only)
    exact hs.trans ((root70_lower hL).trans hroot)
  have hrad : gammaClippedPrefixRadius L 1000 (413 / 100) < gammaClippedRadius1000 L :=
    (max_lt hfloor hroot).trans_le (le_max_right _ _)
  have hpos : 0 ≤ gammaClippedPrefixRadius L 1000 (413 / 100) :=
    (Real.sqrt_nonneg _).trans (le_max_left _ _)
  exact
    mul_lt_mul_of_pos_left ((sq_lt_sq₀ hpos (hpos.trans hrad.le)).mpr hrad)
      (by norm_num only : (0 : ℝ) < 99 / 40)

/-- On 120<=L<=240, the refined 1000-prefix bound is at most 48510.
The root and floor radius are at most 140. Squaring gives the comparison
needed to exclude the 50000-prefix branch. -/
theorem prefix1000Refined_upper {L : ℝ} (hL : 120 ≤ L) (hU : L ≤ 240) :
    gamma1000RefinedBound L ≤ 48510 := by
  have hr :=
    root140_upper hL hU (by norm_num only : (203 / 50 : ℝ) ≤ 413 / 100)
      (by norm_num only : 0 ≤ 143420077 / 11856000 - 2 * (413 / 100 : ℝ))
  have hf : Real.sqrt ((40 / 99 : ℝ) * 1000) ≤ 140 :=
    (Real.sqrt_le_iff).mpr ⟨by norm_num only, by norm_num only⟩
  have hrad : gammaClippedPrefixRadius L 1000 (413 / 100) ≤ 140 := max_le hf hr
  have hpos : 0 ≤ gammaClippedPrefixRadius L 1000 (413 / 100) :=
    (Real.sqrt_nonneg _).trans (le_max_left _ _)
  have hs := (sq_le_sq₀ hpos (by norm_num only : (0 : ℝ) ≤ 140)).mpr hrad
  change (99 / 40 : ℝ) * gammaClippedPrefixRadius L 1000 (413 / 100) ^ 2 ≤ 48510
  linarith only [hs]

/-- On 120<=L<=240, the refined 1000-prefix bound is below the clipped Gamma minimum.
Combine its first-branch strict comparison with its upper bound below 50000.
This certifies improvement over the Gamma interval of the baseline envelope. -/
theorem prefix1000Refined_lt_upper {L : ℝ} (hL : 120 ≤ L) (hU : L ≤ 240) :
    gamma1000RefinedBound L < gammaClippedUpper L := by
  have hb := prefix1000Refined_upper hL hU
  have hf : (50000 : ℝ) ≤ gammaClippedBound50000 L := by
    have hs := Real.sq_sqrt (by norm_num only : (0 : ℝ) ≤ (40 / 99) * 50000)
    have hr : Real.sqrt ((40 / 99 : ℝ) * 50000) ≤ gammaClippedPrefixRadius L 50000 (28493 / 5000) :=
      le_max_left _ _
    have hsq := (sq_le_sq₀ (Real.sqrt_nonneg _) ((Real.sqrt_nonneg _).trans hr)).mpr hr
    change (50000 : ℝ) ≤ (99 / 40 : ℝ) * gammaClippedPrefixRadius L 50000 (28493 / 5000) ^ 2
    linarith only [hs, hsq]
  exact lt_min (prefix1000Refined_lt_first hL) (lt_of_le_of_lt hb (by linarith only [hf]))

/-- Under GRH and log n>=120, an odd composite has a prime rejecting strong MR
below the refined 1000-prefix bound. Supply the existing ten-node certificate
through its new 413/100 lower bound to the parameterized Gamma theorem. -/
theorem exists_prime_gamma1000Refined {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 120 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ gamma1000RefinedBound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  exact
    exists_prime_witness_le_gammaClippedPrefixBound hn ho hc hGRH hL (by norm_num only)
      (by norm_num only) (LLS.gamma_prefix1000_refined hGRH.riemann (le_refl (1000 : ℝ)))

/-- Under the same GRH and logarithmic assumptions, the least rejecting prime
obeys the refined 1000-prefix bound. Extract it from the actual witness theorem.
All factorization and subgroup conditions remain internal. -/
theorem exists_least_gamma1000Refined {n : ℕ} [NeZero n] (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 120 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ gamma1000RefinedBound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  exact
    exists_least_prime_reject_of_exists_prime_reject
      (exists_prime_gamma1000Refined hn ho hc hGRH hL)

end PseudoPrime.PrimeTestBounds.MillerRabin
