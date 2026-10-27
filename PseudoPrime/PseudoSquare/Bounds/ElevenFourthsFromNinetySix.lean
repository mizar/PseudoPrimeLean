/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ElevenFourthsLowerStart
public import PseudoPrime.LLS.OddEndpointLowerLogShiftSeparation
public import PseudoPrime.PseudoSquare.Bounds.OddEndpointBranchPolynomials

/-! # Eleven-fourths logarithmic-shift witnesses from logarithmic input ninety-six -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- For positive n and log n>=96, both conductor-branch polynomials are
positive at the eleven-fourths root. For y<120 use the coupled lower logarithm;
for y>=120 reuse the previous halfline certificate. Exact costs follow by monotonicity. -/
theorem elevenFourthsRoot_branch_polynomials_pos_from_96 {n : ℕ} (hnpos : 0 < n)
    (hL : 96 ≤ Real.log (n : ℝ)) :
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
  have hy : 94 ≤ y := Analysis.elevenFourthsRoot_ge_94 hL
  have hy0 : 0 < y := by linarith only [hy]
  have hy1 : 1 ≤ y := by linarith only [hy]
  have hz0 : 0 ≤ Real.log y := Real.log_nonneg hy1
  have ht :=
    Analysis.elevenFourthsRoot_tangent_coupling_of_pos
      (by linarith only [hL] : 0 < Real.log (n : ℝ)) hy0
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
  · have hp :
      0 <
        LLS.PaperStatements.oddEndpointTwoCostPolynomial (L + 7 / 5) (2096 / 1831) y (Real.log y)
          (7 / 10) (2 * (Real.log y) ^ 2) := by
      by_cases h120 : 120 ≤ y
      · exact
          LLS.PaperStatements.oddEndpoint_branch_0_polynomial_pos h120
            (Analysis.log_ge_nineteen_fourths_of_ge_120 h120) ht
      · exact
          LLS.PaperStatements.oddEndpoint_lower_branch_0_polynomial_pos hy
            (Analysis.log_lower_coupling_of_94_le_le_120 hy (le_of_not_ge h120)) ht
    have hm :=
      LLS.PaperStatements.oddEndpointTwoCostPolynomial_antitone_inputs (P := (2096 / 1831 : ℝ))
        (y := y) (z := Real.log y) (D₁ := 2 * (Real.log y) ^ 2) hy1 hz0 hq hb (le_refl _)
    have he : (2 * Real.log y) ^ 2 / 2 = 2 * (Real.log y) ^ 2 := by ring
    rw [he]
    exact hp.trans_le hm
  · have hp :
      0 <
        LLS.PaperStatements.oddEndpointTwoCostPolynomial (L) (2096 / 1831) y (Real.log y) (14 / 15)
          (2 * (Real.log y) ^ 2 + 7 / 5 * Real.log y) := by
      by_cases h120 : 120 ≤ y
      · exact
          LLS.PaperStatements.oddEndpoint_branch_1_polynomial_pos h120
            (Analysis.log_ge_nineteen_fourths_of_ge_120 h120) ht
      · exact
          LLS.PaperStatements.oddEndpoint_lower_branch_1_polynomial_pos hy
            (Analysis.log_lower_coupling_of_94_le_le_120 hy (le_of_not_ge h120)) ht
    have hm :=
      LLS.PaperStatements.oddEndpointTwoCostPolynomial_antitone_inputs (L₁ := L) (L₂ := L) (P :=
        (2096 / 1831 : ℝ)) (y := y) (z := Real.log y) hy1 hz0 (le_refl _) hc hD
    exact hp.trans_le hm

/-- For odd nonsquare n under GRH with log n>=96, an odd-prime non-one Jacobi
witness is at most (log n-log log n+11/4)^2. Apply both branch polynomials
to the existing witness criterion, without finite enumeration of inputs. -/
theorem exists_odd_prime_jacobi_ne_one_le_elevenFourths_log_shift_from_96 {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 96 ≤ Real.log (n : ℝ)) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        (p : ℝ) ≤ (Real.log n - Real.log (Real.log n) + 11 / 4) ^ 2 ∧ jacobiSym n p ≠ 1 := by
  have hp := elevenFourthsRoot_branch_polynomials_pos_from_96 hn.pos hL
  exact
    exists_odd_prime_jacobi_ne_one_of_branch_polynomials_pos hn hns hGRH
      (by linarith only [Analysis.elevenFourthsRoot_ge_94 hL]) hp.1 hp.2

/-- Under the same assumptions, the least odd-prime non-one witness satisfies
the eleven-fourths shift bound from log n>=96. The nonempty-set input defines
the least witness; apply leastness to the prime provided by the existence theorem. -/
theorem primeNeOneWitness_cast_le_elevenFourths_log_shift_from_96 {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 96 ≤ Real.log (n : ℝ)) (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤
      (Real.log n - Real.log (Real.log n) + 11 / 4) ^ 2 := by
  obtain ⟨p, hp, ho, hpx, hv⟩ :=
    exists_odd_prime_jacobi_ne_one_le_elevenFourths_log_shift_from_96 hn hns hGRH hL
  exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hpx

/-- For positive B under GRH with log B>=96, the finite maximum QNeOne(B)
satisfies the eleven-fourths shift bound. Polynomial conditions at 4*B and B
control every admissible input through the existing level-monotone criterion. -/
theorem QNeOne_cast_le_elevenFourths_log_shift_from_96 {B : ℕ} (hB : 0 < B)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 96 ≤ Real.log (B : ℝ)) :
    (QNeOne B : ℝ) ≤ (Real.log B - Real.log (Real.log B) + 11 / 4) ^ 2 := by
  have hp := elevenFourthsRoot_branch_polynomials_pos_from_96 hB hL
  exact
    QNeOne_cast_le_of_branch_polynomials_pos hGRH
      (by linarith only [Analysis.elevenFourthsRoot_ge_94 hL]) hp.1 hp.2

/-- At L>=96, reducing correction three to eleven fourths strictly reduces
the squared radius. Positivity of the new radius follows from its lower bound 94. -/
theorem elevenFourths_log_shift_sq_lt_previous_from_96 {L : ℝ} (hL : 96 ≤ L) :
    (L - Real.log L + 11 / 4) ^ 2 < (L - Real.log L + 3) ^ 2 := by
  have hy := Analysis.elevenFourthsRoot_ge_94 hL
  nlinarith only [hy]

/-- At L>=96, the eleven-fourths shift square is below L^2. Use the positive
radius and a certified logarithm lower bound at 96 to show that the radius is below L. -/
theorem elevenFourths_log_shift_sq_lt_log_sq_from_96 {L : ℝ} (hL : 96 ≤ L) :
    (L - Real.log L + 11 / 4) ^ 2 < L ^ 2 := by
  have hy := Analysis.elevenFourthsRoot_ge_94 hL
  have h96 :=
    Analysis.log_lower_coupling_of_94_le_le_120 (by norm_num only : (94 : ℝ) ≤ 96)
      (by norm_num only : (96 : ℝ) ≤ 120)
  have hz := h96.trans (Real.log_le_log (by norm_num only : (0 : ℝ) < 96) hL)
  have hdiff : L - Real.log L + 11 / 4 < L := by linarith only [hz]
  exact sq_lt_sq₀ (by linarith only [hy]) (by linarith only [hL]) |>.mpr hdiff

end PseudoPrime.PseudoSquare
