/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.QuarterLogClippedNegativeBounds
public import PseudoPrime.PseudoSquare.Bounds.FixedRampAnchor128NegOneBounds

/-! # Negative Jacobi bounds with the quarter-logarithm clipped radius -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- The negative-witness radius (99/40)H(L+7/5) squared, using the quarter-logarithm
clipped root H. The shift covers log(4B) when evaluated at L=log B.
This is the common upper bound for all nonsquare odd inputs at most B. -/
noncomputable def quarterClippedTwoPoleNegOneRadius (L : ℝ) : ℝ :=
  (99 / 40 : ℝ) * LLS.quarterClippedNegativeRoot (L + 7 / 5) ^ 2

/-- For odd nonsquare n at most B under GRH with log B at least 500, an odd
prime negative Jacobi witness lies below the quarter-logarithm clipped radius at log B.
Apply the even quadratic character theorem and monotonicity of the common ambient root.
This improves the earlier fixed-anchor radius without a finite input certificate. -/
theorem exists_odd_prime_neg_one_le_quarterClippedTwoPole_log_ambient {n B : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hnB : n ≤ B) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 500 ≤ Real.log B) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧ (p : ℝ) ≤ quarterClippedTwoPoleNegOneRadius (Real.log B) ∧ jacobiSym n p = -1 := by
  let : NeZero (4 * n) := ⟨Nat.mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  have hBpos : 0 < B := hn.pos.trans_le hnB
  have hBA : (B : ℝ) ≤ (4 * B : ℕ) := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith only [(Nat.cast_nonneg B : (0 : ℝ) ≤ B)]
  have hLA : 500 ≤ Real.log (4 * B : ℕ) := hL.trans (Real.log_le_log (Nat.cast_pos.mpr hBpos) hBA)
  obtain ⟨p, hp, hd, hb, hv⟩ :=
    LLS.exists_prime_neg_one_le_quarterClipped_log_ambient
      (NumberTheory.complexQuadraticCharacter n hn)
      (NumberTheory.complexQuadraticCharacter_isQuadratic n hn)
      (NumberTheory.complexQuadraticCharacter_isEven n hn)
      (NumberTheory.complexQuadraticCharacter_ne_one_of_not_square n hn hns)
      (Nat.mul_le_mul_left 4 hnB) hGRH hLA
  have hlog : Real.log (4 * B : ℕ) ≤ Real.log B + 7 / 5 := by
    rw [LLS.log_original_quadratic_level hBpos]
    have he : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num only, Real.log_pow]
      norm_num only [Nat.cast_ofNat]
    rw [he]
    linarith only [Real.log_two_lt_d9]
  have hdata := LLS.quarterClippedNegativeRoot_data hLA
  have hr : 0 ≤ LLS.quarterClippedNegativeRoot (Real.log (4 * B : ℕ)) := by
    linarith only [hdata.1, hLA]
  have hu :=
    LLS.quarterClippedNegativeRoot_mono (by linarith only [hLA] : 0 < Real.log (4 * B : ℕ)) hlog
  have hs := mul_self_le_mul_self hr hu
  have hw :=
    NumberTheory.primeNegOneWitness_mem_of_complexQuadraticCharacter_ne_one n hn hp hd
      (by
        rw [hv]; norm_num only)
  refine ⟨p, hp, hw.2.1, ?_, hw.2.2⟩
  dsimp only [quarterClippedTwoPoleNegOneRadius]
  nlinarith only [hb, hs]

/-- Under the common-ambient GRH assumptions, the least odd-prime negative
Jacobi witness is bounded by the new radius. Apply leastness to the constructed witness.
This is the interface used for the finite maximum. -/
theorem primeNegOneWitness_cast_le_quarterClippedTwoPole_log_ambient {n B : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hnB : n ≤ B) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 500 ≤ Real.log B) (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤
      quarterClippedTwoPoleNegOneRadius (Real.log B) := by
  obtain ⟨p, hp, ho, hb, hv⟩ :=
    exists_odd_prime_neg_one_le_quarterClippedTwoPole_log_ambient hn hns hnB hGRH hL
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hb

/-- Under GRH and log B at least 500, QNegOne(B) is bounded by the new radius.
Apply the common-ambient theorem to every admissible n at most B, including small n.
No individual-input lower bound or finite input enumeration is required. -/
theorem QNegOne_le_quarterClippedTwoPole_logarithmic {B : ℕ} (hL : 500 ≤ Real.log B)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (QNegOne B : ℝ) ≤ quarterClippedTwoPoleNegOneRadius (Real.log B) := by
  apply QNegOne_cast_le_of_forall (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 99 / 40) (sq_nonneg _))
  intro n hn
  have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
  exact
    primeNegOneWitness_cast_le_quarterClippedTwoPole_log_ambient ha.odd ha.not_isSquare ha.le hGRH
      hL (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare ha.odd ha.not_isSquare)

/-- For odd nonsquare n under GRH with log n at least 500, a negative odd-prime
Jacobi witness lies below the new radius at log n. Specialize the ambient bound to B=n.
This is the pointwise public logarithmic bound. -/
theorem exists_prime_neg_one_witness_le_quarterClippedTwoPole_logarithmic {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 500 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧ (p : ℝ) ≤ quarterClippedTwoPoleNegOneRadius (Real.log n) ∧ jacobiSym n p = -1 := by
  exact exists_odd_prime_neg_one_le_quarterClippedTwoPole_log_ambient hn hns le_rfl hGRH hL

/-- Under the pointwise GRH and logarithmic-size assumptions, bound the least
negative odd-prime witness by the new radius. Specialize the common ambient leastness theorem.
This keeps the pointwise and finite-maximum claims separate. -/
theorem primeNegOneWitness_cast_le_quarterClippedTwoPole_logarithmic {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 500 ≤ Real.log n) (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤
      quarterClippedTwoPoleNegOneRadius (Real.log n) := by
  exact primeNegOneWitness_cast_le_quarterClippedTwoPole_log_ambient hn hns le_rfl hGRH hL hw

/-- For real L at least 500, the new radius is strictly smaller than the old
fixed-anchor radius. Compare the positive roots and their squares.
This certifies dominance over the entire common applicability range. -/
theorem quarterClippedTwoPoleNegOneRadius_lt_fixed {L : ℝ} (hL : 500 ≤ L) :
    quarterClippedTwoPoleNegOneRadius L < fixedAnchorTwoPoleNegOneRadius L := by
  have hT : 500 ≤ L + 7 / 5 := by linarith only [hL]
  have hd := LLS.quarterClippedNegativeRoot_data hT
  have hr := LLS.quarterClippedNegativeRoot_lt_fixed hT
  have hp :=
    mul_pos (sub_pos.mpr hr)
      (show 0 < LLS.fixedAnchorNegativeRoot (L + 7 / 5) + LLS.quarterClippedNegativeRoot (L + 7 / 5)
        by linarith only [hd.1, hr])
  dsimp only [quarterClippedTwoPoleNegOneRadius, fixedAnchorTwoPoleNegOneRadius]
  nlinarith only [hp]

/-- For real L at least 550, the new radius is strictly below L squared.
Use the global logarithmic tangent to bound the shifted root by 127L/200.
This gives a uniform strict comparison without sampled intersections. -/
theorem quarterClippedTwoPoleNegOneRadius_lt_log_square {L : ℝ} (hL : 550 ≤ L) :
    quarterClippedTwoPoleNegOneRadius L < L ^ 2 := by
  let T := L + 7 / 5
  have hT : 500 ≤ T := by
    dsimp only [T]; linarith only [hL]
  have hd := LLS.quarterClippedNegativeRoot_data hT
  have hr : 0 ≤ LLS.quarterClippedNegativeRoot T := by linarith only [hd.1]
  have ht :=
    LLS.conductorPrefix_log_tangent
      (by
        dsimp only [T]; linarith only [hL] : 0 < T)
  have hu : LLS.quarterClippedNegativeRoot T ≤ (127 / 200 : ℝ) * L := by
    dsimp only [T] at ht
    dsimp only [LLS.quarterClippedNegativeRoot, T]
    linarith only [ht, hL]
  have hs := mul_self_le_mul_self hr hu
  have hp := sq_pos_of_pos (show 0 < L by linarith only [hL])
  dsimp only [quarterClippedTwoPoleNegOneRadius]
  change (99 / 40 : ℝ) * LLS.quarterClippedNegativeRoot T ^ 2 < L ^ 2
  nlinarith only [hs, hp]

/-- For real L at least 600, the new radius is strictly below (99/100)L squared.
Bound the shifted root by 1581L/2500 using the logarithmic tangent.
This supplies the improved guaranteed comparison range with the coefficient 99/100. -/
theorem quarterClippedTwoPoleNegOneRadius_lt_ninety_nine {L : ℝ} (hL : 600 ≤ L) :
    quarterClippedTwoPoleNegOneRadius L < (99 / 100 : ℝ) * L ^ 2 := by
  let T := L + 7 / 5
  have hT : 500 ≤ T := by
    dsimp only [T]; linarith only [hL]
  have hd := LLS.quarterClippedNegativeRoot_data hT
  have hr : 0 ≤ LLS.quarterClippedNegativeRoot T := by linarith only [hd.1]
  have ht :=
    LLS.conductorPrefix_log_tangent
      (by
        dsimp only [T]; linarith only [hL] : 0 < T)
  have hu : LLS.quarterClippedNegativeRoot T ≤ (1581 / 2500 : ℝ) * L := by
    dsimp only [T] at ht
    dsimp only [LLS.quarterClippedNegativeRoot, T]
    linarith only [ht, hL]
  have hs := mul_self_le_mul_self hr hu
  have hp := sq_pos_of_pos (show 0 < L by linarith only [hL])
  dsimp only [quarterClippedTwoPoleNegOneRadius]
  change (99 / 40 : ℝ) * LLS.quarterClippedNegativeRoot T ^ 2 < (99 / 100 : ℝ) * L ^ 2
  nlinarith only [hs, hp]

end PseudoPrime.PseudoSquare
