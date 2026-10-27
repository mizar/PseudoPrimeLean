/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TwoPoleNegativeBounds
public import PseudoPrime.PseudoSquare.Bounds.ExcludedEndpointJacobi

/-! # Negative Jacobi witnesses from the two-pole prime-count bound -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- The negative two-pole upper radius at log input L. Use ambient log(4B) at most
log B+7/5 and root 5log(4B)/8+20. This bounds least odd-prime negative Jacobi
witnesses and their full finite maximum. -/
noncomputable def twoPoleNegOneRadius (L : ℝ) : ℝ :=
  (99 / 40 : ℝ) * ((5 / 8 : ℝ) * (L + 7 / 5) + 20) ^ 2

/-- For odd nonsquare n at most B under GRH with log B at least 3000, an odd prime
negative Jacobi witness lies below the common two-pole radius at B. Apply the
quadratic character theorem at original level 4n and ambient level 4B, then use
reciprocity. No lower bound on log n or finite-input certificate is required. -/
theorem exists_odd_prime_neg_one_le_twoPole_ambient {n B : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hnB : n ≤ B) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 3000 ≤ Real.log B) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ twoPoleNegOneRadius (Real.log B) ∧ jacobiSym n p = -1 := by
  let : NeZero (4 * n) := ⟨Nat.mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  have hBpos : 0 < B := hn.pos.trans_le hnB
  have hBA : (B : ℝ) ≤ (4 * B : ℕ) := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith only [(Nat.cast_nonneg B : (0 : ℝ) ≤ B)]
  have hLA : 3000 ≤ Real.log (4 * B : ℕ) := hL.trans (Real.log_le_log (Nat.cast_pos.mpr hBpos) hBA)
  obtain ⟨p, hp, hd, hb, hv⟩ :=
    LLS.exists_prime_neg_one_le_twoPole_ambient (NumberTheory.complexQuadraticCharacter n hn)
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
  have hr : 0 ≤ (5 / 8 : ℝ) * Real.log (4 * B : ℕ) + 20 := by linarith only [hLA]
  have hu : (5 / 8 : ℝ) * Real.log (4 * B : ℕ) + 20 ≤ (5 / 8 : ℝ) * (Real.log B + 7 / 5) + 20 := by
    linarith only [hlog]
  have hs := mul_self_le_mul_self hr hu
  have hw :=
    NumberTheory.primeNegOneWitness_mem_of_complexQuadraticCharacter_ne_one n hn hp hd
      (by
        rw [hv]; norm_num only)
  refine ⟨p, hp, hw.2.1, ?_, hw.2.2⟩
  dsimp only [twoPoleNegOneRadius]
  nlinarith only [hb, hs]

/-- Under the common-ambient assumptions, the least odd-prime negative Jacobi
witness for n is at most the two-pole radius at B. Apply leastness to the constructed
prime. This supplies the input for the full finite-maximum theorem. -/
theorem primeNegOneWitness_cast_le_twoPole_ambient {n B : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hnB : n ≤ B) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 3000 ≤ Real.log B) (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ twoPoleNegOneRadius (Real.log B) := by
  obtain ⟨p, hp, ho, hb, hv⟩ := exists_odd_prime_neg_one_le_twoPole_ambient hn hns hnB hGRH hL
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hb

/-- Under GRH with log B at least 3000, the full finite maximum QNegOne(B) is at
most the two-pole affine radius. Apply the common-ambient theorem to every
admissible input, including small n. No finite-input certificate is used. -/
theorem QNegOne_le_twoPole_affine {B : ℕ} (hL : 3000 ≤ Real.log B)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (QNegOne B : ℝ) ≤ twoPoleNegOneRadius (Real.log B) := by
  apply QNegOne_cast_le_of_forall (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 99 / 40) (sq_nonneg _))
  intro n hn
  have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
  exact
    primeNegOneWitness_cast_le_twoPole_ambient ha.odd ha.not_isSquare ha.le hGRH hL
      (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare ha.odd ha.not_isSquare)

/-- For real L at least 3000, the negative two-pole radius is strictly smaller than
(99/100)L squared. Bound its affine root by 79L/125 and compare rational squares.
This certifies improvement over the existing uniform coefficient 99/100. -/
theorem twoPoleNegOneRadius_lt_ninety_nine {L : ℝ} (hL : 3000 ≤ L) :
    twoPoleNegOneRadius L < (99 / 100 : ℝ) * L ^ 2 := by
  have hr : 0 ≤ (5 / 8 : ℝ) * (L + 7 / 5) + 20 := by linarith only [hL]
  have hu : (5 / 8 : ℝ) * (L + 7 / 5) + 20 ≤ (79 / 125 : ℝ) * L := by linarith only [hL]
  have hs := mul_self_le_mul_self hr hu
  have hsq : 0 < L ^ 2 := sq_pos_of_pos (by linarith only [hL])
  dsimp only [twoPoleNegOneRadius]
  nlinarith only [hs, hsq]

/-- For odd nonsquare n under GRH with log n at least 3000, there is an odd prime
negative Jacobi witness below the two-pole affine radius at n. Specialize the common
ambient existence theorem to B=n. -/
theorem exists_prime_neg_one_witness_le_twoPole_affine {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 3000 ≤ Real.log n) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ twoPoleNegOneRadius (Real.log n) ∧ jacobiSym n p = -1 := by
  exact exists_odd_prime_neg_one_le_twoPole_ambient hn hns le_rfl hGRH hL

/-- Under the pointwise GRH and logarithmic assumptions, the least odd-prime
negative Jacobi witness is bounded by the two-pole affine radius. Specialize the
common ambient leastness theorem. This is the companion of the QNegOne result. -/
theorem primeNegOneWitness_cast_le_twoPole_affine {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 3000 ≤ Real.log n)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ twoPoleNegOneRadius (Real.log n) := by
  exact primeNegOneWitness_cast_le_twoPole_ambient hn hns le_rfl hGRH hL hw

end PseudoPrime.PseudoSquare
