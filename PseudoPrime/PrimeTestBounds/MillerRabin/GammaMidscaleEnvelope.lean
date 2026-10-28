/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaClippedComparison
public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointEvenPolynomial
public import PseudoPrime.LLS.GammaCheckpoint35000
public import PseudoPrime.PrimeTestBounds.MillerRabin.LeastWitnessBounds

/-! # Clipped Gamma bounds from the certified 35000 prefix -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The clipped Gamma prefix bound at cutoff 35000 and credit 11147/2000.
The parameter L is the logarithm of the input; the witness theorem applies from L=120.
It reuses the existing ten-node prefix certificate. -/
noncomputable def gamma35000Bound (L : ℝ) : ℝ :=
  gammaClippedPrefixBound L 35000 (11147 / 2000)

/-- At L>=120, increasing a prefix credit strictly decreases its quadratic root.
Assume the opposite order and compare the zero gap with the nonnegative earlier gap.
The nonnegative offset hypotheses are the existing root theorem requirements. -/
theorem root_credit_strict {L C D : ℝ} (hL : 120 ≤ L) (hC : 0 ≤ 143420077 / 11856000 - 2 * C)
    (hD : 0 ≤ 143420077 / 11856000 - 2 * D) (hCD : C < D) :
    gammaClippedPrefixRoot L D < gammaClippedPrefixRoot L C := by
  by_contra h
  have hnon := gammaClippedPrefixGap_nonneg_of_root_le hL hC (le_of_not_gt h)
  have hz := gammaClippedPrefixGap_root_eq_zero hL hD
  dsimp only [gammaClippedPrefixGap] at hnon hz
  linarith only [hnon, hz, hCD]

/-- At L>=209, the clipped root with credit 203/50 exceeds 119.
Its gap at 119 is negative throughout the half-line, contradicting the root-order criterion.
This places the old first-prefix bound above the new prefix floor. -/
theorem root119_lower {L : ℝ} (hL : 209 ≤ L) : (119 : ℝ) < gammaClippedPrefixRoot L (203 / 50) := by
  by_contra h
  have hgap :=
    gammaClippedPrefixGap_nonneg_of_root_le (by linarith only [hL] : 120 ≤ L)
      (by norm_num only : 0 ≤ 143420077 / 11856000 - 2 * (203 / 50 : ℝ)) (le_of_not_gt h)
  dsimp only [gammaClippedPrefixGap] at hgap
  linarith only [hgap, hL]

/-- At 120<=L<=240 and credit at least 203/50, the clipped root is at most 140.
Its rational gap at 140 is nonnegative. The nonnegative offset is retained explicitly.
This supplies comparisons with the 50000 prefix floor. -/
theorem root140_upper {L C : ℝ} (hL : 120 ≤ L) (hU : L ≤ 240) (hC : 203 / 50 ≤ C)
    (hD : 0 ≤ 143420077 / 11856000 - 2 * C) : gammaClippedPrefixRoot L C ≤ 140 := by
  apply gammaClippedPrefixRoot_le_of_gap_nonneg hL hD (by norm_num only)
  dsimp only [gammaClippedPrefixGap]
  linarith only [hU, hC]

/-- For L>=209, the 35000 prefix bound is strictly below the first clipped Gamma branch.
Both its floor radius and its improved-credit root are below the earlier root.
Square the positive radius comparison to obtain a witness-bound comparison. -/
theorem prefix35000_lt_first {L : ℝ} (hL : 209 ≤ L) :
    gamma35000Bound L < gammaClippedBound1000 L := by
  have h120 : 120 ≤ L := by linarith only [hL]
  have h119 := root119_lower hL
  have hroot :=
    root_credit_strict h120 (by norm_num only : 0 ≤ 143420077 / 11856000 - 2 * (203 / 50 : ℝ))
      (by norm_num only : 0 ≤ 143420077 / 11856000 - 2 * (11147 / 2000 : ℝ))
      (by norm_num only : (203 / 50 : ℝ) < 11147 / 2000)
  have hfloor : Real.sqrt ((40 / 99 : ℝ) * 35000) < gammaClippedPrefixRoot L (203 / 50) := by
    have hs : Real.sqrt ((40 / 99 : ℝ) * 35000) < 119 :=
      (Real.sqrt_lt (by norm_num only) (by norm_num only)).mpr (by norm_num only)
    exact hs.trans h119
  have hrad : gammaClippedPrefixRadius L 35000 (11147 / 2000) < gammaClippedRadius1000 L := by
    exact (max_lt hfloor hroot).trans_le (le_max_right _ _)
  have hpos : 0 ≤ gammaClippedPrefixRadius L 35000 (11147 / 2000) :=
    (Real.sqrt_nonneg _).trans (le_max_left _ _)
  exact
    mul_lt_mul_of_pos_left ((sq_lt_sq₀ hpos (hpos.trans hrad.le)).mpr hrad)
      (by norm_num only : (0 : ℝ) < 99 / 40)

/-- For 120<=L<=240, the 35000 prefix bound is at most 48510.
Bound its root and floor radius by 140, then square.
This is an upper comparison used against the second prefix floor. -/
theorem prefix_bound_upper {L : ℝ} (hL : 120 ≤ L) (hU : L ≤ 240) : gamma35000Bound L ≤ 48510 := by
  have hr :=
    root140_upper hL hU (by norm_num only : (203 / 50 : ℝ) ≤ 11147 / 2000)
      (by norm_num only : 0 ≤ 143420077 / 11856000 - 2 * (11147 / 2000 : ℝ))
  have hf : Real.sqrt ((40 / 99 : ℝ) * 35000) ≤ 140 :=
    (Real.sqrt_le_iff).mpr ⟨by norm_num only, by norm_num only⟩
  have hrad : gammaClippedPrefixRadius L 35000 (11147 / 2000) ≤ 140 := max_le hf hr
  have hpos : 0 ≤ gammaClippedPrefixRadius L 35000 (11147 / 2000) :=
    (Real.sqrt_nonneg _).trans (le_max_left _ _)
  have hs := (sq_le_sq₀ hpos (by norm_num only : (0 : ℝ) ≤ 140)).mpr hrad
  change (99 / 40 : ℝ) * gammaClippedPrefixRadius L 35000 (11147 / 2000) ^ 2 ≤ 48510
  linarith only [hs]

/-- For 209<=L<=240, the 35000 prefix bound is strictly below the clipped Gamma minimum.
Compare with the first branch by credit and with the second by its 50000 floor.
At L=240 this statement compares Gamma bounds only. -/
theorem prefix35000_lt_upper {L : ℝ} (hL : 209 ≤ L) (hU : L ≤ 240) :
    gamma35000Bound L < gammaClippedUpper L := by
  have hb := prefix_bound_upper (by linarith only [hL]) hU
  have hf : (50000 : ℝ) ≤ gammaClippedBound50000 L := by
    have hs := Real.sq_sqrt (by norm_num only : (0 : ℝ) ≤ (40 / 99) * 50000)
    have hr : Real.sqrt ((40 / 99 : ℝ) * 50000) ≤ gammaClippedPrefixRadius L 50000 (28493 / 5000) :=
      le_max_left _ _
    have hsq := (sq_le_sq₀ (Real.sqrt_nonneg _) ((Real.sqrt_nonneg _).trans hr)).mpr hr
    change (50000 : ℝ) ≤ (99 / 40 : ℝ) * gammaClippedPrefixRadius L 50000 (28493 / 5000) ^ 2
    linarith only [hs, hsq]
  exact lt_min (prefix35000_lt_first hL) (lt_of_le_of_lt hb (by linarith only [hf]))

/-- Under GRH and log n>=120, every odd composite has a prime strong-MR witness
below gamma35000Bound.
Insert the certified prefix and rational offset into the generic clipped-prefix theorem.
No input integer or prime-power list is enumerated. -/
theorem exists_prime_gamma35000 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 120 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ gamma35000Bound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  exact
    exists_prime_witness_le_gammaClippedPrefixBound hn ho hc hGRH hL (by norm_num only)
      (by norm_num only) (LLS.gamma_prefix35000_lower hGRH.riemann (le_refl (35000 : ℝ)))

/-- Under the same GRH and logarithmic premises, the least rejecting prime obeys gamma35000Bound.
Apply the existing least-prime extraction to the actual prime witness theorem.
All subgroup and factorization conditions remain internal. -/
theorem exists_least_gamma35000 {n : ℕ} [NeZero n] (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 120 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ gamma35000Bound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  exact exists_least_prime_reject_of_exists_prime_reject (exists_prime_gamma35000 hn ho hc hGRH hL)

/-- The pointwise minimum of the clipped Gamma bound and the 35000 prefix candidate.
Both witness theorems apply for L>=120. Comparison results may simplify this minimum
only on their certified intervals. -/
noncomputable def gammaMidscaleEnvelope (L : ℝ) : ℝ :=
  min (gammaClippedUpper L) (gamma35000Bound L)

/-- Under GRH and log n>=120, the Gamma minimum bounds the least rejecting prime.
Combine the two full-input witness theorems through the common minimum lemma.
The conclusion retains primality, rejection, and minimality. -/
theorem exists_least_gammaMidscale {n : ℕ} [NeZero n] (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 120 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ gammaMidscaleEnvelope (Real.log n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hb, hr, hm⟩ := exists_least_prime_witness_le_gammaClippedUpper hn ho hc hGRH hL
  obtain ⟨q, hq, hqb, hqr, hqm⟩ := exists_least_gamma35000 hn ho hc hGRH hL
  exact least_prime_witness_bound_min ⟨p, hp, hr, hb, hm⟩ ⟨q, hq, hqr, hqb, hqm⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
