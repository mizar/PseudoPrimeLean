/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TwoPoleRetainedScaleBounds
public import PseudoPrime.PseudoSquare.Bounds.ExcludedEndpointJacobi

/-! # Non-one Jacobi witnesses from direct signed errors -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- The odd non-one two-pole upper radius at logarithmic input L.
Use ambient log(4B) at most log B+7/5 and additive root shift 61/5.
The value bounds both least pointwise witnesses and their full finite maximum. -/
noncomputable def retainedScaleTwoPoleNeOneRadius (L : ℝ) : ℝ :=
  (99 / 40 : ℝ) * ((500 / 821 : ℝ) * (L + 7 / 5) + 61 / 5) ^ 2

/-- For odd nonsquare n at most B under GRH and log B at least 500, an odd prime
with non-one Jacobi value lies below the common two-pole radius at B. Apply the
character theorem with ambient level 4B, including small input conductors, and
convert the value by quadratic reciprocity. No lower bound on log n is required. -/
theorem exists_odd_prime_ne_one_le_retainedScaleTwoPole_ambient {n B : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hnB : n ≤ B) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 500 ≤ Real.log B) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧ (p : ℝ) ≤ retainedScaleTwoPoleNeOneRadius (Real.log B) ∧ jacobiSym n p ≠ 1 := by
  let : NeZero (4 * n) := ⟨Nat.mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  have hBpos : 0 < B := hn.pos.trans_le hnB
  have hBA : (B : ℝ) ≤ (4 * B : ℕ) := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith only [(Nat.cast_nonneg B : (0 : ℝ) ≤ B)]
  have hLA : 500 ≤ Real.log (4 * B : ℕ) := hL.trans (Real.log_le_log (Nat.cast_pos.mpr hBpos) hBA)
  obtain ⟨p, hp, ho, hb, hv⟩ :=
    LLS.exists_odd_prime_ne_one_le_twoPoleRetained_even
      (NumberTheory.complexQuadraticCharacter n hn)
      (NumberTheory.complexQuadraticCharacter_isQuadratic n hn)
      (NumberTheory.complexQuadraticCharacter_isEven n hn)
      (NumberTheory.complexQuadraticCharacter_ne_one_of_not_square n hn hns)
      (show 2 ∣ 4 * n from ⟨2 * n, by ring⟩) (Nat.mul_le_mul_left 4 hnB) hGRH hLA
  have hlog : Real.log (4 * B : ℕ) ≤ Real.log B + 7 / 5 := by
    rw [LLS.log_original_quadratic_level hBpos]
    have he : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num only, Real.log_pow]
      norm_num only [Nat.cast_ofNat]
    rw [he]
    linarith only [Real.log_two_lt_d9]
  have hr : 0 ≤ (500 / 821 : ℝ) * Real.log (4 * B : ℕ) + 61 / 5 := by linarith only [hLA]
  have hu :
    (500 / 821 : ℝ) * Real.log (4 * B : ℕ) + 61 / 5 ≤
      (500 / 821 : ℝ) * (Real.log B + 7 / 5) + 61 / 5 := by
    linarith only [hlog]
  have hs := mul_self_le_mul_self hr hu
  refine ⟨p, hp, ho, ?_, ?_⟩
  · dsimp only [retainedScaleTwoPoleNeOneRadius]
    nlinarith only [hb, hs]
  · intro hj
    let : NeZero p := ⟨hp.ne_zero⟩
    have hg : (n : ℤ).gcd p = 1 := by
      by_contra h
      have hz := jacobiSym.eq_zero_iff_not_coprime.mpr h
      rw [hj] at hz
      exact one_ne_zero hz
    have hc : Nat.Coprime n p := by exact_mod_cast hg
    apply hv
    rw [NumberTheory.complexQuadraticCharacter_apply_odd_prime n hn hp ho hc.symm, hj]
    exact Int.cast_one

/-- Under the same common-ambient assumptions, the least odd-prime non-one Jacobi
witness for n is bounded by the two-pole radius at B. Apply leastness to the
constructed prime. This is the input to the full finite-maximum theorem. -/
theorem primeNeOneWitness_cast_le_retainedScaleTwoPole_ambient {n B : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hnB : n ≤ B) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 500 ≤ Real.log B) (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤ retainedScaleTwoPoleNeOneRadius (Real.log B) := by
  obtain ⟨p, hp, ho, hb, hv⟩ :=
    exists_odd_prime_ne_one_le_retainedScaleTwoPole_ambient hn hns hnB hGRH hL
  exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hb

/-- Under GRH with log B at least 500, QNeOne(B) is bounded by the affine two-pole
radius. Apply the common-ambient theorem to every admissible n at most B, including
small n. No finite-input certificate or separate small-range bound is needed. -/
theorem QNeOne_le_retainedScaleTwoPole {B : ℕ} (hL : 500 ≤ Real.log B)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (QNeOne B : ℝ) ≤ retainedScaleTwoPoleNeOneRadius (Real.log B) := by
  apply QNeOne_cast_le_of_forall (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 99 / 40) (sq_nonneg _))
  intro n hn
  have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
  exact
    primeNeOneWitness_cast_le_retainedScaleTwoPole_ambient ha.odd ha.not_isSquare ha.le hGRH hL
      (NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
        (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare ha.odd ha.not_isSquare))

/-- For real L at least 500, the odd non-one two-pole radius is strictly below L
squared. Bound its affine root by 1271L/2000 and compare rational squares.
This distinguishes the strict logarithmic-square improvement from applicability. -/
theorem retainedScaleTwoPoleNeOneRadius_lt_log_square {L : ℝ} (hL : 500 ≤ L) :
    retainedScaleTwoPoleNeOneRadius L < L ^ 2 := by
  have hr : 0 ≤ (500 / 821 : ℝ) * (L + 7 / 5) + 61 / 5 := by linarith only [hL]
  have hu : (500 / 821 : ℝ) * (L + 7 / 5) + 61 / 5 ≤ (1271 / 2000 : ℝ) * L := by linarith only [hL]
  have hs := mul_self_le_mul_self hr hu
  have hsq : 0 < L ^ 2 := sq_pos_of_pos (by linarith only [hL])
  dsimp only [retainedScaleTwoPoleNeOneRadius]
  nlinarith only [hs, hsq]

/-- For odd nonsquare n under GRH with log n at least 500, an odd prime non-one
Jacobi witness lies below the affine two-pole radius at n. Specialize the common
ambient endpoint to B=n. Character value zero remains an allowed witness. -/
theorem exists_prime_ne_one_witness_le_retainedScaleTwoPole {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 500 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧ (p : ℝ) ≤ retainedScaleTwoPoleNeOneRadius (Real.log n) ∧ jacobiSym n p ≠ 1 := by
  exact exists_odd_prime_ne_one_le_retainedScaleTwoPole_ambient hn hns le_rfl hGRH hL

/-- Under the same pointwise assumptions, bound the least odd-prime non-one Jacobi
witness by the affine two-pole radius. Specialize the common ambient leastness
interface. This is the pointwise companion of the full QNeOne bound. -/
theorem primeNeOneWitness_cast_le_retainedScaleTwoPole {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 500 ≤ Real.log n)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤ retainedScaleTwoPoleNeOneRadius (Real.log n) := by
  exact primeNeOneWitness_cast_le_retainedScaleTwoPole_ambient hn hns le_rfl hGRH hL hw

end PseudoPrime.PseudoSquare
