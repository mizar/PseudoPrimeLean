/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ElevenFourthsLogShift
public import PseudoPrime.LLS.OddEndpointLogShiftSeparation
public import PseudoPrime.PseudoSquare.Bounds.OddEndpointBranchPolynomials

/-! # Odd non-one Jacobi witnesses with logarithmic correction eleven fourths -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- For positive n with log n>=128, both conductor-branch polynomials are
positive at y=log n-log log n+11/4. Use tangent coupling, rational upper bounds
for log two and both costs, and the continuous shifted polynomial certificates. -/
theorem elevenFourthsRoot_branch_polynomials_pos {n : ℕ} (hnpos : 0 < n)
    (hL : 128 ≤ Real.log (n : ℝ)) :
    let y := Real.log (n : ℝ) - Real.log (Real.log (n : ℝ)) + 11 / 4
    (0 <
        LLS.PaperStatements.oddEndpointTwoCostPolynomial (Real.log ((4 * n : ℕ) : ℝ)) (2096 / 1831)
          y (Real.log y) (Real.log 2) ((2 * Real.log y) ^ 2 / 2)) ∧
      (0 <
        LLS.PaperStatements.oddEndpointTwoCostPolynomial (Real.log (n : ℝ)) (2096 / 1831) y
          (Real.log y) ((4 / 3 : ℝ) * Real.log 2)
          ((2 * Real.log y) ^ 2 / 2 + Real.log 2 * (2 * Real.log y - Real.log 2))) := by
  let L := Real.log (n : ℝ)
  let y := L - Real.log L + 11 / 4
  have hy : 120 ≤ y := Analysis.elevenFourthsRoot_ge_120 hL
  have hy0 : 0 < y := by linarith only [hy]
  have hy1 : 1 ≤ y := by linarith only [hy]
  have hz : 19 / 4 ≤ Real.log y := Analysis.log_ge_nineteen_fourths_of_ge_120 hy
  have hz0 : 0 ≤ Real.log y := by linarith only [hz]
  have ht := Analysis.elevenFourthsRoot_tangent_coupling hL hy0
  have hb : Real.log (2 : ℝ) ≤ 7 / 10 := by linarith only [Real.log_two_lt_d9]
  have hq : Real.log ((4 * n : ℕ) : ℝ) ≤ L + 7 / 5 := by
    rw [Nat.cast_mul, Nat.cast_ofNat,
      Real.log_mul (by norm_num only : (4 : ℝ) ≠ 0) (Nat.cast_ne_zero.mpr hnpos.ne')]
    have he : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num only, Real.log_pow]
      norm_num only [Nat.cast_ofNat]
    rw [he]
    linarith only [hb]
  have hc : (4 / 3 : ℝ) * Real.log 2 ≤ 14 / 15 := by linarith only [hb]
  have hD :
    (2 * Real.log y) ^ 2 / 2 + Real.log 2 * (2 * Real.log y - Real.log 2) ≤
      2 * (Real.log y) ^ 2 + 7 / 5 * Real.log y := by
    have hm := mul_nonneg hz0 (sub_nonneg.mpr hb)
    nlinarith only [hm, sq_nonneg (Real.log 2)]
  constructor
  · have hp := LLS.PaperStatements.oddEndpoint_branch_0_polynomial_pos hy hz ht
    have hm :=
      LLS.PaperStatements.oddEndpointTwoCostPolynomial_antitone_inputs (P := (2096 / 1831 : ℝ))
        (y := y) (z := Real.log y) (D₁ := 2 * (Real.log y) ^ 2) hy1 hz0 hq hb (le_refl _)
    have he : (2 * Real.log y) ^ 2 / 2 = 2 * (Real.log y) ^ 2 := by ring
    rw [he]
    exact hp.trans_le hm
  · have hp := LLS.PaperStatements.oddEndpoint_branch_1_polynomial_pos hy hz ht
    have hm :=
      LLS.PaperStatements.oddEndpointTwoCostPolynomial_antitone_inputs (L₁ := L) (L₂ := L) (P :=
        (2096 / 1831 : ℝ)) (y := y) (z := Real.log y) hy1 hz0 (le_refl _) hc hD
    exact hp.trans_le hm

/-- For odd nonsquare n under GRH and log n>=128, an odd-prime non-one Jacobi
witness is at most (log n-log log n+11/4)^2. Apply the two positive branch
polynomials to the existing witness criterion; no finite input check is used. -/
theorem exists_odd_prime_jacobi_ne_one_le_elevenFourths_log_shift {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 128 ≤ Real.log (n : ℝ)) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        (p : ℝ) ≤ (Real.log n - Real.log (Real.log n) + 11 / 4) ^ 2 ∧ jacobiSym n p ≠ 1 := by
  have hp := elevenFourthsRoot_branch_polynomials_pos hn.pos hL
  exact
    exists_odd_prime_jacobi_ne_one_of_branch_polynomials_pos hn hns hGRH
      (by linarith only [Analysis.elevenFourthsRoot_ge_120 hL]) hp.1 hp.2

/-- Under the same assumptions, the least odd-prime non-one Jacobi witness
satisfies the eleven-fourths logarithmic-shift bound. Apply leastness to the
constructed witness; the nonempty-set input defines the least witness. -/
theorem primeNeOneWitness_cast_le_elevenFourths_log_shift {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 128 ≤ Real.log (n : ℝ))
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤
      (Real.log n - Real.log (Real.log n) + 11 / 4) ^ 2 := by
  obtain ⟨p, hp, ho, hpx, hv⟩ :=
    exists_odd_prime_jacobi_ne_one_le_elevenFourths_log_shift hn hns hGRH hL
  exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hpx

/-- For B>0 under GRH with log B>=128, the finite maximum QNeOne(B) satisfies
the eleven-fourths logarithmic-shift bound. The two polynomial conditions at B
control all admissible inputs via conductor-level monotonicity. -/
theorem QNeOne_cast_le_elevenFourths_log_shift {B : ℕ} (hB : 0 < B)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 128 ≤ Real.log (B : ℝ)) :
    (QNeOne B : ℝ) ≤ (Real.log B - Real.log (Real.log B) + 11 / 4) ^ 2 := by
  have hp := elevenFourthsRoot_branch_polynomials_pos hB hL
  exact
    QNeOne_cast_le_of_branch_polynomials_pos hGRH
      (by linarith only [Analysis.elevenFourthsRoot_ge_120 hL]) hp.1 hp.2

/-- For L>=128, the new squared radius is strictly smaller than the previous
correction-three squared radius. Both roots are positive by the radius height
bound, so reducing the additive constant by one quarter reduces the square. -/
theorem elevenFourths_log_shift_sq_lt_previous {L : ℝ} (hL : 128 ≤ L) :
    (L - Real.log L + 11 / 4) ^ 2 < (L - Real.log L + 3) ^ 2 := by
  have hy := Analysis.elevenFourthsRoot_ge_120 hL
  nlinarith only [hy]

/-- For L>=128, the eleven-fourths logarithmic-shift square is strictly below
L^2. The root is positive and log L>11/4, giving a root strictly below L. -/
theorem elevenFourths_log_shift_sq_lt_log_sq {L : ℝ} (hL : 128 ≤ L) :
    (L - Real.log L + 11 / 4) ^ 2 < L ^ 2 := by
  have hy := Analysis.elevenFourthsRoot_ge_120 hL
  have hz := Analysis.log_ge_nineteen_fourths_of_ge_120 (by linarith only [hL] : 120 ≤ L)
  have hdiff : L - Real.log L + 11 / 4 < L := by linarith only [hz]
  exact sq_lt_sq₀ (by linarith only [hy]) (by linarith only [hL]) |>.mpr hdiff

/-- For 128<=L<=384, the new logarithmic-shift square is also below
the coefficient-99/100 square. Bound the root by L-2 and use L^2<=384*L.
This compares against the existing large-scale quadratic coefficient bound. -/
theorem elevenFourths_log_shift_sq_lt_nearSquare {L : ℝ} (hL : 128 ≤ L) (hL384 : L ≤ 384) :
    (L - Real.log L + 11 / 4) ^ 2 < (99 / 100 : ℝ) * L ^ 2 := by
  have hy := Analysis.elevenFourthsRoot_ge_120 hL
  have hz := Analysis.log_ge_nineteen_fourths_of_ge_120 (by linarith only [hL] : 120 ≤ L)
  have hroot : L - Real.log L + 11 / 4 ≤ L - 2 := by linarith only [hz]
  have hs := (sq_le_sq₀ (by linarith only [hy]) (by linarith only [hL] : 0 ≤ L - 2)).mpr hroot
  have hm := mul_nonneg (by linarith only [hL] : 0 ≤ L) (sub_nonneg.mpr hL384)
  nlinarith only [hs, hm, hL]

end PseudoPrime.PseudoSquare
