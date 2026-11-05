/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.LocalEvenWitness
public import PseudoPrime.LLS.PaperStatements.EndpointCorrectionIntervals

/-! # Rational local even-character correction certificates -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Check a lower bound `a` for the even endpoint correction at rational radius
`q`, using a specified power-of-two scale `j` and sixteen Taylor terms. The
Boolean includes the domain, convergence, sign and polynomial inequalities;
its soundness is used to certify the local radius anchors. -/
def localCorrectionCheck (q a : ℚ) (j : ℕ) : Bool :=
  let l := Analysis.rationalLogLower q j 16
  let u := Analysis.rationalLogUpper q j 16
  decide
    (8 ≤ q ∧
      |1 - q / 2 ^ j| < 1 ∧
      0 ≤ l ∧
      0 ≤ a ∧
      a * LLS.PaperStatements.endpointCorrectionDen q u ≤
        LLS.PaperStatements.endpointCorrectionNum q l)

/-- A successful scaled rational check bounds the real even correction from
below. The Taylor enclosure, monotone numerator and denominator, and positive
denominator transfer the rational inequality. This supports every anchor scale. -/
theorem localCorrectionCheck_sound {q a : ℚ} {j : ℕ} (h : localCorrectionCheck q a j = true) :
    (a : ℝ) ≤ LLS.PaperStatements.fullEndpointEvenGapCorrection (q : ℝ) := by
  rcases of_decide_eq_true h with ⟨hq, hx, hl0, ha, hlo⟩
  have hlog := Analysis.rationalLogBounds_sound (by linarith only [hq] : (0 : ℚ) < q) j 16 hx
  have hqR : (8 : ℝ) ≤ q := by exact_mod_cast hq
  have hlR : (0 : ℝ) ≤ (Analysis.rationalLogLower q j 16 : ℚ) := by exact_mod_cast hl0
  have haR : (0 : ℝ) ≤ a := by exact_mod_cast ha
  have hnlo := LLS.PaperStatements.endpointCorrectionNum_mono hqR hlR hlog.1
  have hdhi := LLS.PaperStatements.endpointCorrectionDen_mono hqR hlog.2
  have hdpos := LLS.PaperStatements.endpointCorrectionDen_pos hqR (hlR.trans hlog.1)
  rw [LLS.PaperStatements.endpointCorrection_eq]
  apply (le_div_iff₀ hdpos).mpr
  have hr := (Rat.cast_le (K := ℝ)).mpr hlo
  have hr' :
    (a : ℝ) *
        LLS.PaperStatements.endpointCorrectionDen (q : ℝ) (Analysis.rationalLogUpper q j 16 : ℚ) ≤
      LLS.PaperStatements.endpointCorrectionNum (q : ℝ) (Analysis.rationalLogLower q j 16 : ℚ) := by
    simpa only [Rat.cast_mul, LLS.PaperStatements.endpointCorrectionDen_cast,
      LLS.PaperStatements.endpointCorrectionNum_cast] using hr
  exact (mul_le_mul_of_nonneg_left hdhi haR).trans (hr'.trans hnlo)

set_option maxRecDepth 8192 in
/-- The even endpoint correction at radius eight exceeds `324969/100000`.
A kernel-checked rational logarithm enclosure gives a slightly stronger lower
bound. This is the first anchor for the local witness envelope. -/
theorem local_even_correction_eight :
    (324969 / 100000 : ℝ) < LLS.PaperStatements.fullEndpointEvenGapCorrection 8 := by
  have hc : LLS.PaperStatements.endpointCorrectionCheck 8 (32496901 / 10000000) 100 = true := by
    decide +kernel
  have h := (LLS.PaperStatements.endpointCorrectionCheck_sound hc).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
  linarith only [h]

/-- Under GRH, the radius-eight correction bounds a prime rejecting odd `n > 1`
whenever a proper subgroup at a divisor `q` contains every local passing residue
and `log q ≤ s`. Apply the certified correction to the general local witness
theorem. This gives the first concrete candidate in the local envelope. -/
theorem exists_prime_reject_local_eight {n q : ℕ} [NeZero q] (hn : 1 < n) (ho : Odd n) (hqn : q ∣ n)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hpass :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
          ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (a : ZMod q))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {s : ℝ} (hs : Real.log q ≤ s) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (max 8 (s - 324969 / 100000)) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  exact
    exists_prime_reject_of_local_shift hn ho hqn H hH hpass hGRH (by norm_num only)
      local_even_correction_eight hs

end PseudoPrime.PrimeTestBounds.MillerRabin
