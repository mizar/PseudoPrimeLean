/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TwoPoleEvenGammaNegativeBounds
public import PseudoPrime.PseudoSquare.Bounds.TwoPoleSignedNegOneBounds

/-! # Negative Jacobi witnesses from direct signed errors and the half-count budget -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- The negative logarithmic two-pole radius (99/40)H(L+7/5) squared.
The root H retains the log-dependent local cost. Apply at log B to bound every
least negative odd-prime Jacobi witness with input at most B. -/
noncomputable def evenGammaTwoPoleNegOneRadius (L : ℝ) : ℝ :=
  (99 / 40 : ℝ) * LLS.evenGammaTwoPoleNegativeLogRoot (L + 7 / 5) ^ 2

/-- For odd nonsquare n at most B under GRH with log B at least 1250, an odd
prime negative Jacobi witness lies below the logarithmic two-pole radius at B.
Use original level 4n and common ambient level 4B. Monotonicity of the nonlinear
root transfers log(4B) to log B+7/5. No finite-input certificate is used. -/
theorem exists_odd_prime_neg_one_le_evenGammaTwoPole_log_ambient {n B : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hnB : n ≤ B) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 1250 ≤ Real.log B) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧ (p : ℝ) ≤ evenGammaTwoPoleNegOneRadius (Real.log B) ∧ jacobiSym n p = -1 := by
  let : NeZero (4 * n) := ⟨Nat.mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  have hBpos : 0 < B := hn.pos.trans_le hnB
  have hBA : (B : ℝ) ≤ (4 * B : ℕ) := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith only [(Nat.cast_nonneg B : (0 : ℝ) ≤ B)]
  have hLA : 1250 ≤ Real.log (4 * B : ℕ) := hL.trans (Real.log_le_log (Nat.cast_pos.mpr hBpos) hBA)
  obtain ⟨p, hp, hd, hb, hv⟩ :=
    LLS.exists_prime_neg_one_le_evenGammaTwoPole_log_ambient
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
  have hdata := LLS.evenGammaTwoPoleNegativeLogRoot_data hLA
  have hr : 0 ≤ LLS.evenGammaTwoPoleNegativeLogRoot (Real.log (4 * B : ℕ)) := by
    linarith only [hdata.2.1, hLA]
  have hu :=
    LLS.evenGammaTwoPoleNegativeLogRoot_mono (by linarith only [hLA] : 0 < Real.log (4 * B : ℕ))
      hlog
  have hs := mul_self_le_mul_self hr hu
  have hw :=
    NumberTheory.primeNegOneWitness_mem_of_complexQuadraticCharacter_ne_one n hn hp hd
      (by
        rw [hv]; norm_num only)
  refine ⟨p, hp, hw.2.1, ?_, hw.2.2⟩
  dsimp only [evenGammaTwoPoleNegOneRadius]
  nlinarith only [hb, hs]

/-- Under the common-ambient assumptions, bound the least odd-prime negative
Jacobi witness for n by the logarithmic radius at B. Apply leastness to the
constructed prime. This is the input to the full finite-maximum theorem. -/
theorem primeNegOneWitness_cast_le_evenGammaTwoPole_log_ambient {n B : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hnB : n ≤ B) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 1250 ≤ Real.log B) (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ evenGammaTwoPoleNegOneRadius (Real.log B) := by
  obtain ⟨p, hp, ho, hb, hv⟩ :=
    exists_odd_prime_neg_one_le_evenGammaTwoPole_log_ambient hn hns hnB hGRH hL
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hb

/-- Under GRH with log B at least 1250, QNegOne(B) is at most the logarithmic
two-pole radius. Apply the common-ambient least-witness bound to every admissible
input, including small n. No separate finite range is required. -/
theorem QNegOne_le_evenGammaTwoPole_logarithmic {B : ℕ} (hL : 1250 ≤ Real.log B)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (QNegOne B : ℝ) ≤ evenGammaTwoPoleNegOneRadius (Real.log B) := by
  apply QNegOne_cast_le_of_forall (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 99 / 40) (sq_nonneg _))
  intro n hn
  have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
  exact
    primeNegOneWitness_cast_le_evenGammaTwoPole_log_ambient ha.odd ha.not_isSquare ha.le hGRH hL
      (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare ha.odd ha.not_isSquare)

/-- For real L at least 1250, the logarithmic negative radius is strictly below
(99/100)L squared. Bound H(L+7/5) by 31621L/50000 and compare rational squares.
This certifies improvement over the previous coefficient 99/100. -/
theorem evenGammaTwoPoleNegOneRadius_lt_ninety_nine {L : ℝ} (hL : 1250 ≤ L) :
    evenGammaTwoPoleNegOneRadius L < (99 / 100 : ℝ) * L ^ 2 := by
  have hT : 1250 ≤ L + 7 / 5 := by linarith only [hL]
  have hd := LLS.evenGammaTwoPoleNegativeLogRoot_data hT
  have hr : 0 ≤ LLS.evenGammaTwoPoleNegativeLogRoot (L + 7 / 5) := by linarith only [hd.2.1, hT]
  have hu : LLS.evenGammaTwoPoleNegativeLogRoot (L + 7 / 5) ≤ (31621 / 50000 : ℝ) * L := by
    have h := LLS.evenGammaTwoPoleNegativeLogRoot_le_linear hT
    linarith only [h, hL]
  have hs := mul_self_le_mul_self hr hu
  have hsq : 0 < L ^ 2 := sq_pos_of_pos (by linarith only [hL])
  dsimp only [evenGammaTwoPoleNegOneRadius]
  nlinarith only [hs, hsq]

/-- For odd nonsquare n under GRH with log n at least 1250, an odd prime negative
Jacobi witness lies below the logarithmic radius at n. Specialize the common
ambient theorem to B=n. -/
theorem exists_prime_neg_one_witness_le_evenGammaTwoPole_logarithmic {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 1250 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧ (p : ℝ) ≤ evenGammaTwoPoleNegOneRadius (Real.log n) ∧ jacobiSym n p = -1 := by
  exact exists_odd_prime_neg_one_le_evenGammaTwoPole_log_ambient hn hns le_rfl hGRH hL

/-- Under the pointwise assumptions, the least odd-prime negative Jacobi witness
is bounded by the logarithmic radius. Specialize the common-ambient leastness
interface. This is the pointwise companion of the full QNegOne bound. -/
theorem primeNegOneWitness_cast_le_evenGammaTwoPole_logarithmic {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 1250 ≤ Real.log n) (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ evenGammaTwoPoleNegOneRadius (Real.log n) := by
  exact primeNegOneWitness_cast_le_evenGammaTwoPole_log_ambient hn hns le_rfl hGRH hL hw

/-- For L at least 1250, the sharp negative radius is smaller than the preceding
signed logarithmic radius. Both its logarithmic coefficient and additive constant
are smaller. Compare positive roots and square the strict inequality. -/
theorem evenGammaTwoPoleNegOneRadius_lt_previous {L : ℝ} (hL : 1250 ≤ L) :
    evenGammaTwoPoleNegOneRadius L < signedTwoPoleNegOneLogRadius L := by
  have hT : 1250 ≤ L + 7 / 5 := by linarith only [hL]
  have hd := LLS.evenGammaTwoPoleNegativeLogRoot_data hT
  have hr : 0 < LLS.evenGammaTwoPoleNegativeLogRoot (L + 7 / 5) := by linarith only [hd.2.1, hT]
  have hl0 : 0 ≤ Real.log (L + 7 / 5) := Real.log_nonneg (by linarith only [hT])
  have hlt :
    LLS.evenGammaTwoPoleNegativeLogRoot (L + 7 / 5) <
      LLS.signedTwoPoleNegativeLogRoot (L + 7 / 5) := by
    dsimp only [LLS.evenGammaTwoPoleNegativeLogRoot, LLS.signedTwoPoleNegativeLogRoot,
      LLS.twoPoleNegativeLogRoot]
    linarith only [hl0]
  have hp :
    0 <
      LLS.signedTwoPoleNegativeLogRoot (L + 7 / 5) +
        LLS.evenGammaTwoPoleNegativeLogRoot (L + 7 / 5) := by
    linarith only [hlt, hr]
  have hm := mul_pos (sub_pos.mpr hlt) hp
  dsimp only [evenGammaTwoPoleNegOneRadius, signedTwoPoleNegOneLogRadius]
  nlinarith only [hm]

end PseudoPrime.PseudoSquare
