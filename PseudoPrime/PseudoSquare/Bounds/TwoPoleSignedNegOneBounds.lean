/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TwoPoleSignedNegativeBounds
public import PseudoPrime.PseudoSquare.Bounds.TwoPoleNegOneLogBounds

/-! # Negative Jacobi witnesses from the signed logarithmic two-pole budget -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- The negative logarithmic two-pole radius (99/40)H(L+7/5) squared.
The root H retains the log-dependent local cost. Apply at log B to bound every
least negative odd-prime Jacobi witness with input at most B. -/
noncomputable def signedTwoPoleNegOneLogRadius (L : ℝ) : ℝ :=
  (99 / 40 : ℝ) * LLS.signedTwoPoleNegativeLogRoot (L + 7 / 5) ^ 2

/-- For odd nonsquare n at most B under GRH with log B at least 2000, an odd
prime negative Jacobi witness lies below the logarithmic two-pole radius at B.
Use original level 4n and common ambient level 4B. Monotonicity of the nonlinear
root transfers log(4B) to log B+7/5. No finite-input certificate is used. -/
theorem exists_odd_prime_neg_one_le_signedTwoPole_log_ambient {n B : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hnB : n ≤ B) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 2000 ≤ Real.log B) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧ (p : ℝ) ≤ signedTwoPoleNegOneLogRadius (Real.log B) ∧ jacobiSym n p = -1 := by
  let : NeZero (4 * n) := ⟨Nat.mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  have hBpos : 0 < B := hn.pos.trans_le hnB
  have hBA : (B : ℝ) ≤ (4 * B : ℕ) := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith only [(Nat.cast_nonneg B : (0 : ℝ) ≤ B)]
  have hLA : 2000 ≤ Real.log (4 * B : ℕ) := hL.trans (Real.log_le_log (Nat.cast_pos.mpr hBpos) hBA)
  obtain ⟨p, hp, hd, hb, hv⟩ :=
    LLS.exists_prime_neg_one_le_signedTwoPole_log_ambient
      (NumberTheory.complexQuadraticCharacter n hn)
      (NumberTheory.complexQuadraticCharacter_isQuadratic n hn)
      (NumberTheory.complexQuadraticCharacter_ne_one_of_not_square n hn hns)
      (Nat.mul_le_mul_left 4 hnB) hGRH hLA
  have hlog : Real.log (4 * B : ℕ) ≤ Real.log B + 7 / 5 := by
    rw [LLS.log_original_quadratic_level hBpos]
    have he : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num only, Real.log_pow]
      norm_num only [Nat.cast_ofNat]
    rw [he]
    linarith only [Real.log_two_lt_d9]
  have hdata := LLS.signedTwoPoleNegativeLogRoot_data hLA
  have hr : 0 ≤ LLS.signedTwoPoleNegativeLogRoot (Real.log (4 * B : ℕ)) := by
    linarith only [hdata.2.1, hLA]
  have hu :=
    LLS.signedTwoPoleNegativeLogRoot_mono (by linarith only [hLA] : 0 < Real.log (4 * B : ℕ)) hlog
  have hs := mul_self_le_mul_self hr hu
  have hw :=
    NumberTheory.primeNegOneWitness_mem_of_complexQuadraticCharacter_ne_one n hn hp hd
      (by
        rw [hv]; norm_num only)
  refine ⟨p, hp, hw.2.1, ?_, hw.2.2⟩
  dsimp only [signedTwoPoleNegOneLogRadius]
  nlinarith only [hb, hs]

/-- Under the common-ambient assumptions, bound the least odd-prime negative
Jacobi witness for n by the logarithmic radius at B. Apply leastness to the
constructed prime. This is the input to the full finite-maximum theorem. -/
theorem primeNegOneWitness_cast_le_signedTwoPole_log_ambient {n B : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hnB : n ≤ B) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 2000 ≤ Real.log B) (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ signedTwoPoleNegOneLogRadius (Real.log B) := by
  obtain ⟨p, hp, ho, hb, hv⟩ :=
    exists_odd_prime_neg_one_le_signedTwoPole_log_ambient hn hns hnB hGRH hL
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hb

/-- Under GRH with log B at least 2000, QNegOne(B) is at most the logarithmic
two-pole radius. Apply the common-ambient least-witness bound to every admissible
input, including small n. No separate finite range is required. -/
theorem QNegOne_le_signedTwoPole_logarithmic {B : ℕ} (hL : 2000 ≤ Real.log B)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (QNegOne B : ℝ) ≤ signedTwoPoleNegOneLogRadius (Real.log B) := by
  apply QNegOne_cast_le_of_forall (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 99 / 40) (sq_nonneg _))
  intro n hn
  have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
  exact
    primeNegOneWitness_cast_le_signedTwoPole_log_ambient ha.odd ha.not_isSquare ha.le hGRH hL
      (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare ha.odd ha.not_isSquare)

/-- For real L at least 2000, the logarithmic negative radius is strictly below
(99/100)L squared. Bound H(L+7/5) by 1581L/2500 and compare rational squares.
This certifies improvement over the previous coefficient 99/100. -/
theorem signedTwoPoleNegOneLogRadius_lt_ninety_nine {L : ℝ} (hL : 2000 ≤ L) :
    signedTwoPoleNegOneLogRadius L < (99 / 100 : ℝ) * L ^ 2 := by
  have hT : 2000 ≤ L + 7 / 5 := by linarith only [hL]
  have hd := LLS.signedTwoPoleNegativeLogRoot_data hT
  have hr : 0 ≤ LLS.signedTwoPoleNegativeLogRoot (L + 7 / 5) := by linarith only [hd.2.1, hT]
  have hu : LLS.signedTwoPoleNegativeLogRoot (L + 7 / 5) ≤ (1581 / 2500 : ℝ) * L := by
    have h := LLS.signedTwoPoleNegativeLogRoot_le_linear hT
    linarith only [h, hL]
  have hs := mul_self_le_mul_self hr hu
  have hsq : 0 < L ^ 2 := sq_pos_of_pos (by linarith only [hL])
  dsimp only [signedTwoPoleNegOneLogRadius]
  nlinarith only [hs, hsq]

/-- For odd nonsquare n under GRH with log n at least 2000, an odd prime negative
Jacobi witness lies below the logarithmic radius at n. Specialize the common
ambient theorem to B=n. -/
theorem exists_prime_neg_one_witness_le_signedTwoPole_logarithmic {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 2000 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧ (p : ℝ) ≤ signedTwoPoleNegOneLogRadius (Real.log n) ∧ jacobiSym n p = -1 := by
  exact exists_odd_prime_neg_one_le_signedTwoPole_log_ambient hn hns le_rfl hGRH hL

/-- Under the pointwise assumptions, the least odd-prime negative Jacobi witness
is bounded by the logarithmic radius. Specialize the common-ambient leastness
interface. This is the pointwise companion of the full QNegOne bound. -/
theorem primeNegOneWitness_cast_le_signedTwoPole_logarithmic {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 2000 ≤ Real.log n) (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ signedTwoPoleNegOneLogRadius (Real.log n) := by
  exact primeNegOneWitness_cast_le_signedTwoPole_log_ambient hn hns le_rfl hGRH hL hw

/-- For L at least 2000, the signed logarithmic negative radius is smaller than
the preceding logarithmic radius. The positive new root is eight below the old
root. Squaring preserves the strict inequality, so the old radius is never best. -/
theorem signedTwoPoleNegOneLogRadius_lt_previous {L : ℝ} (hL : 2000 ≤ L) :
    signedTwoPoleNegOneLogRadius L < twoPoleNegOneLogRadius L := by
  have hT : 2000 ≤ L + 7 / 5 := by linarith only [hL]
  have hd := LLS.signedTwoPoleNegativeLogRoot_data hT
  have hr : 0 < LLS.signedTwoPoleNegativeLogRoot (L + 7 / 5) := by linarith only [hd.2.1, hT]
  have he :
    LLS.twoPoleNegativeLogRoot (L + 7 / 5) = LLS.signedTwoPoleNegativeLogRoot (L + 7 / 5) + 8 := by
    dsimp only [LLS.signedTwoPoleNegativeLogRoot]
    ring
  dsimp only [signedTwoPoleNegOneLogRadius, twoPoleNegOneLogRadius]
  rw [he]
  nlinarith only [hr]

end PseudoPrime.PseudoSquare
