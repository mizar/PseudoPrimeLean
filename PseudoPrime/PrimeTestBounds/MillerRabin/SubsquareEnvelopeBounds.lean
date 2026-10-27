/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RationalCutoffWitnessBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.SignedRationalWitnessBounds
public import PseudoPrime.Analysis.RationalProfileComparisons
public import PseudoPrime.Analysis.LogTaylorBounds

/-! # A proved MR envelope below the logarithmic square on a persistent tail -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The minimum of three proved MR cutoffs on their common valid domain.
The first two retain the small-input logarithmic improvement; the third gives
an asymptotic leading coefficient of 199/250, below four fifths.
The formula is used only above the shared starting value 3000. -/
noncomputable def subsquareEnvelope (L : ℝ) : ℝ :=
  min (min (L ^ 2) (Analysis.rationalPart2CutoffRoot L ^ 2)) ((199 / 250 : ℝ) * (L + 216) ^ 2)

/-- Two exact logarithm enclosures at the first integer above the real crossing.
The checks enclose log(70392) and then log of its rational lower endpoint. -/
theorem subsquare_log_endpoint_checks :
    Analysis.rationalLogIntervalCheck 70392 17 32 (5580917 / 500000) 12 = true ∧
      Analysis.rationalLogIntervalCheck (5580917 / 500000) 4 32 (241250001 / 100000000) 3 =
        true := by
  decide +kernel

/-- Input: n at least 70392.
Claim: the signed rational Part 2 square is strictly below log(n) squared.
Proof: use both certified logarithms and compare the positive roots.
This sharpens the entrance without changing the underlying witness theorem. -/
theorem rational_part2_sq_lt_log_sq_of_ge_70392 {n : ℕ} (hn : 70392 ≤ n) :
    Analysis.rationalPart2CutoffRoot (Real.log n) ^ 2 < (Real.log n) ^ 2 := by
  have h1 := Analysis.rationalLogIntervalCheck_sound subsquare_log_endpoint_checks.1
  have h2 := Analysis.rationalLogIntervalCheck_sound subsquare_log_endpoint_checks.2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  have hm := Real.log_le_log (by norm_num only : (0 : ℝ) < 70392) (Nat.cast_le.mpr hn)
  have hL : (5580917 / 500000 : ℝ) ≤ Real.log n := h1.1.trans hm
  have hz := Real.log_le_log (by norm_num only : (0 : ℝ) < 5580917 / 500000) hL
  have hR := Analysis.eight_lt_rationalPart2CutoffRoot (show 8 ≤ Real.log n by linarith only [hL])
  apply
    (sq_lt_sq₀ (show 0 ≤ Analysis.rationalPart2CutoffRoot (Real.log n) by linarith only [hR])
        (show 0 ≤ Real.log n by linarith only [hL])).mpr
  dsimp only [Analysis.rationalPart2CutoffRoot]
  linarith only [hz, h2.1]

/-- Input: an odd composite at least 3000 under GRH.
Claim: a prime rejecting base lies below the minimum of the three cutoffs.
Proof: choose the witness for whichever proved branch is smaller.
This combines different formulas without weakening either input theorem. -/
theorem exists_prime_witness_le_subsquareEnvelope {n : ℕ} (hnOdd : Odd n) (hnComposite : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 3000 ≤ n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ subsquareEnvelope (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hn1 : 1 < n := (by decide : (1 : ℕ) < 3000).trans_le hn
  by_cases h :
    min ((Real.log n) ^ 2) (Analysis.rationalPart2CutoffRoot (Real.log n) ^ 2) ≤
      (199 / 250 : ℝ) * (Real.log n + 216) ^ 2
  · obtain ⟨p, hp, hb, hf⟩ :=
      exists_prime_witness_le_rationalCutoff_of_large hn1 hnOdd hnComposite hn hGRH
    exact ⟨p, hp, le_min hb (hb.trans h), hf⟩
  · obtain ⟨p, hp, _, hb, hf⟩ :=
      exists_prime_witness_le_gamma_199_div_250_plus_216_3000 hnOdd hnComposite hGRH hn
    exact ⟨p, hp, le_min (hb.trans (le_of_not_ge h)) hb, hf⟩

/-- Input: n at least 70392.
Claim: the entire envelope is strictly below the logarithmic square.
Proof: retain the already certified negative-log correction branch.
No later switch of the minimum can invalidate this strict inequality. -/
theorem subsquareEnvelope_lt_log_sq {n : ℕ} (hn : 70392 ≤ n) :
    subsquareEnvelope (Real.log n) < (Real.log n) ^ 2 := by
  exact
    ((min_le_left _ _).trans (min_le_right _ _)).trans_lt
      (rational_part2_sq_lt_log_sq_of_ge_70392 hn)

/-- Input: an odd composite at least 70392 under GRH.
Claim: the same prime witness obeys the envelope and is strictly below log(n) squared.
Proof: combine witness existence with the persistent envelope comparison.
This gives an actual witness theorem, not just a comparison of candidate formulas. -/
theorem exists_prime_witness_lt_log_sq_of_subsquareEnvelope {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hn : 70392 ≤ n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ subsquareEnvelope (Real.log n) ∧
        (p : ℝ) < (Real.log n) ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hb, hf⟩ :=
    exists_prime_witness_le_subsquareEnvelope hnOdd hnComposite hGRH
      ((by decide : (3000 : ℕ) ≤ 70392).trans hn)
  exact ⟨p, hp, hb, hb.trans_lt (subsquareEnvelope_lt_log_sq hn), hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
