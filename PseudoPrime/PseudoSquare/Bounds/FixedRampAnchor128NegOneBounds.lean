/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.FixedRampAnchor128Bounds
public import PseudoPrime.PseudoSquare.Bounds.TwoPoleConductorPrefixNegOneBounds

/-! # Negative Jacobi witnesses from the fixed-width certified anchor -/

@[expose] public section

namespace PseudoPrime.LLS

/-- The conductor-prefix negative root is monotone on positive real inputs. Use logarithmic
monotonicity and positive coefficients. This transfers the common ambient level to the explicit
input-bound logarithm in the Jacobi witness theorem. -/
theorem fixedAnchorNegativeRoot_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    fixedAnchorNegativeRoot x ≤ fixedAnchorNegativeRoot y := by
  have h := Real.log_le_log hx hxy
  dsimp only [fixedAnchorNegativeRoot]
  linarith only [h, hxy]

end PseudoPrime.LLS

namespace PseudoPrime.PseudoSquare

/-- The negative logarithmic two-pole radius (99/40)H(L+7/5) squared.
The root H retains the log-dependent local cost. Apply at log B to bound every
least negative odd-prime Jacobi witness with input at most B. -/
noncomputable def fixedAnchorTwoPoleNegOneRadius (L : ℝ) : ℝ :=
  (99 / 40 : ℝ) * LLS.fixedAnchorNegativeRoot (L + 7 / 5) ^ 2

/-- For odd nonsquare n at most B under GRH with log B at least 500, an odd
prime negative Jacobi witness lies below the logarithmic two-pole radius at B.
Use original level 4n and common ambient level 4B. Monotonicity of the nonlinear
root transfers log(4B) to log B+7/5. No finite-input certificate is used. -/
theorem exists_odd_prime_neg_one_le_fixedAnchorTwoPole_log_ambient {n B : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hnB : n ≤ B) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 500 ≤ Real.log B) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧ (p : ℝ) ≤ fixedAnchorTwoPoleNegOneRadius (Real.log B) ∧ jacobiSym n p = -1 := by
  let : NeZero (4 * n) := ⟨Nat.mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  have hBpos : 0 < B := hn.pos.trans_le hnB
  have hBA : (B : ℝ) ≤ (4 * B : ℕ) := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith only [(Nat.cast_nonneg B : (0 : ℝ) ≤ B)]
  have hLA : 500 ≤ Real.log (4 * B : ℕ) := hL.trans (Real.log_le_log (Nat.cast_pos.mpr hBpos) hBA)
  obtain ⟨p, hp, hd, hb, hv⟩ :=
    LLS.exists_prime_neg_one_le_fixedAnchor_log_ambient
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
  have hdata := LLS.fixedAnchorNegativeRoot_data hLA
  have hr : 0 ≤ LLS.fixedAnchorNegativeRoot (Real.log (4 * B : ℕ)) := by
    linarith only [hdata.1, hLA]
  have hu :=
    LLS.fixedAnchorNegativeRoot_mono (by linarith only [hLA] : 0 < Real.log (4 * B : ℕ)) hlog
  have hs := mul_self_le_mul_self hr hu
  have hw :=
    NumberTheory.primeNegOneWitness_mem_of_complexQuadraticCharacter_ne_one n hn hp hd
      (by
        rw [hv]; norm_num only)
  refine ⟨p, hp, hw.2.1, ?_, hw.2.2⟩
  dsimp only [fixedAnchorTwoPoleNegOneRadius]
  nlinarith only [hb, hs]

/-- Under the common-ambient assumptions, bound the least odd-prime negative
Jacobi witness for n by the logarithmic radius at B. Apply leastness to the
constructed prime. This is the input to the full finite-maximum theorem. -/
theorem primeNegOneWitness_cast_le_fixedAnchorTwoPole_log_ambient {n B : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hnB : n ≤ B) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 500 ≤ Real.log B) (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ fixedAnchorTwoPoleNegOneRadius (Real.log B) := by
  obtain ⟨p, hp, ho, hb, hv⟩ :=
    exists_odd_prime_neg_one_le_fixedAnchorTwoPole_log_ambient hn hns hnB hGRH hL
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hb

/-- Under GRH with log B at least 500, QNegOne(B) is at most the logarithmic
two-pole radius. Apply the common-ambient least-witness bound to every admissible
input, including small n. No separate finite range is required. -/
theorem QNegOne_le_fixedAnchorTwoPole_logarithmic {B : ℕ} (hL : 500 ≤ Real.log B)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (QNegOne B : ℝ) ≤ fixedAnchorTwoPoleNegOneRadius (Real.log B) := by
  apply QNegOne_cast_le_of_forall (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 99 / 40) (sq_nonneg _))
  intro n hn
  have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
  exact
    primeNegOneWitness_cast_le_fixedAnchorTwoPole_log_ambient ha.odd ha.not_isSquare ha.le hGRH hL
      (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare ha.odd ha.not_isSquare)

/-- For real L at least 761, the retained negative radius is below (99/100)L squared.
Use the global logarithmic tangent to bound the shifted root by 12649L/20000.
This certifies the improvement over the preceding coefficient 99/100. -/
theorem fixedAnchorTwoPoleNegOneRadius_lt_ninety_nine {L : ℝ} (hL : 761 ≤ L) :
    fixedAnchorTwoPoleNegOneRadius L < (99 / 100 : ℝ) * L ^ 2 := by
  let T := L + 7 / 5
  have hT : 500 ≤ T := by
    dsimp only [T]; linarith only [hL]
  have hd := LLS.fixedAnchorNegativeRoot_data hT
  have hr : 0 ≤ LLS.fixedAnchorNegativeRoot T := by linarith only [hd.1]
  have hu : LLS.fixedAnchorNegativeRoot T ≤ (12649 / 20000 : ℝ) * L := by
    have ht :=
      LLS.conductorPrefix_log_tangent
        (by
          dsimp only [T]; linarith only [hL] : 0 < T)
    dsimp only [T] at ht
    dsimp only [LLS.fixedAnchorNegativeRoot, T]
    linarith only [ht, hL]
  have hs := mul_self_le_mul_self hr hu
  have hsq : 0 < L ^ 2 := sq_pos_of_pos (by linarith only [hL])
  dsimp only [fixedAnchorTwoPoleNegOneRadius]
  nlinarith only [hs, hsq]

/-- For real L at least 662, the retained negative radius is below L squared.
Bound the shifted root by 15891L/25000 using the logarithmic tangent.
This comparison is separate from the analytic applicability threshold 500. -/
theorem fixedAnchorTwoPoleNegOneRadius_lt_log_square {L : ℝ} (hL : 662 ≤ L) :
    fixedAnchorTwoPoleNegOneRadius L < L ^ 2 := by
  let T := L + 7 / 5
  have hT : 500 ≤ T := by
    dsimp only [T]; linarith only [hL]
  have hd := LLS.fixedAnchorNegativeRoot_data hT
  have hr : 0 ≤ LLS.fixedAnchorNegativeRoot T := by linarith only [hd.1]
  have hu : LLS.fixedAnchorNegativeRoot T ≤ (15891 / 25000 : ℝ) * L := by
    have ht :=
      LLS.conductorPrefix_log_tangent
        (by
          dsimp only [T]; linarith only [hL] : 0 < T)
    dsimp only [T] at ht
    dsimp only [LLS.fixedAnchorNegativeRoot, T]
    linarith only [ht, hL]
  have hs := mul_self_le_mul_self hr hu
  have hsq : 0 < L ^ 2 := sq_pos_of_pos (by linarith only [hL])
  dsimp only [fixedAnchorTwoPoleNegOneRadius]
  nlinarith only [hs, hsq]

/-- For odd nonsquare n under GRH with log n at least 500, an odd prime negative
Jacobi witness lies below the logarithmic radius at n. Specialize the common
ambient theorem to B=n. -/
theorem exists_prime_neg_one_witness_le_fixedAnchorTwoPole_logarithmic {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 500 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧ (p : ℝ) ≤ fixedAnchorTwoPoleNegOneRadius (Real.log n) ∧ jacobiSym n p = -1 := by
  exact exists_odd_prime_neg_one_le_fixedAnchorTwoPole_log_ambient hn hns le_rfl hGRH hL

/-- Under the pointwise assumptions, the least odd-prime negative Jacobi witness
is bounded by the logarithmic radius. Specialize the common-ambient leastness
interface. This is the pointwise companion of the full QNegOne bound. -/
theorem primeNegOneWitness_cast_le_fixedAnchorTwoPole_logarithmic {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 500 ≤ Real.log n) (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ fixedAnchorTwoPoleNegOneRadius (Real.log n) := by
  exact primeNegOneWitness_cast_le_fixedAnchorTwoPole_log_ambient hn hns le_rfl hGRH hL hw

/-- For L at least 500, the new negative radius is strictly smaller than the
previous conductor-prefix radius. The roots differ by three; both are positive.
This proves improvement on the entire common analytic domain. -/
theorem fixedAnchorTwoPoleNegOneRadius_lt_conductorPrefix {L : ℝ} (hL : 500 ≤ L) :
    fixedAnchorTwoPoleNegOneRadius L < conductorPrefixTwoPoleNegOneRadius L := by
  have hd := LLS.fixedAnchorNegativeRoot_data (show 500 ≤ L + 7 / 5 by linarith only [hL])
  have hr : 0 < LLS.fixedAnchorNegativeRoot (L + 7 / 5) := by linarith only [hd.1]
  have he :
    LLS.conductorPrefixNegativeLogRoot (L + 7 / 5) =
      LLS.fixedAnchorNegativeRoot (L + 7 / 5) + 3 := by
    dsimp only [LLS.conductorPrefixNegativeLogRoot, LLS.fixedAnchorNegativeRoot]
    ring
  dsimp only [fixedAnchorTwoPoleNegOneRadius, conductorPrefixTwoPoleNegOneRadius]
  rw [he]
  nlinarith only [hr]

end PseudoPrime.PseudoSquare
