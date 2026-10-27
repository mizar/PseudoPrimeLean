/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.OddEndpointTwoCostPolynomial
public import PseudoPrime.PseudoSquare.Bounds.OddEndpointConductorBranches

/-! # Polynomial sufficient conditions for odd-prime non-one Jacobi bounds -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- For odd nonsquare n under GRH and y>=8, positivity of both conductor-branch
polynomials gives an odd non-one Jacobi prime at most y^2. Convert each polynomial
to a negative endpoint limit and apply the correlated conductor criterion. -/
theorem exists_odd_prime_jacobi_ne_one_of_branch_polynomials_pos {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ}
    (hy : 8 ≤ y)
    (hzero :
      0 <
        LLS.PaperStatements.oddEndpointTwoCostPolynomial (Real.log ((4 * n : ℕ) : ℝ)) (2096 / 1831)
          y (Real.log y) (Real.log 2) ((2 * Real.log y) ^ 2 / 2))
    (hnonzero :
      0 <
        LLS.PaperStatements.oddEndpointTwoCostPolynomial (Real.log (n : ℝ)) (2096 / 1831) y
          (Real.log y) ((4 / 3 : ℝ) * Real.log 2)
          ((2 * Real.log y) ^ 2 / 2 + Real.log 2 * (2 * Real.log y - Real.log 2))) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ y ^ 2 ∧ jacobiSym n p ≠ 1 := by
  have hy1 : 1 < y := by linarith only [hy]
  have hy64 : 64 ≤ y ^ 2 := by nlinarith only [hy]
  have h0 :=
    LLS.PaperStatements.oddEndpointTwoCostLimit_neg_of_rational_polynomial_pos (4 * n) hy1 hzero
  have h1 :=
    LLS.PaperStatements.oddEndpointTwoCostLimit_neg_of_rational_polynomial_pos n hy1 hnonzero
  apply
    exists_odd_prime_jacobi_ne_one_of_conductor_branch_limits_neg hn hns hGRH
      (by linarith only [hy64]) hy64 (le_refl _)
  · simpa only [Real.log_pow, Nat.cast_ofNat] using h0
  · simpa only [Real.log_pow, Nat.cast_ofNat] using h1

/-- Under the same branch polynomial conditions, the least odd-prime non-one
Jacobi witness is at most y^2. The nonempty-set argument defines the existing
least witness; leastness transfers the constructed prime bound. -/
theorem primeNeOneWitness_cast_le_of_branch_polynomials_pos {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 8 ≤ y)
    (hzero :
      0 <
        LLS.PaperStatements.oddEndpointTwoCostPolynomial (Real.log ((4 * n : ℕ) : ℝ)) (2096 / 1831)
          y (Real.log y) (Real.log 2) ((2 * Real.log y) ^ 2 / 2))
    (hnonzero :
      0 <
        LLS.PaperStatements.oddEndpointTwoCostPolynomial (Real.log (n : ℝ)) (2096 / 1831) y
          (Real.log y) ((4 / 3 : ℝ) * Real.log 2)
          ((2 * Real.log y) ^ 2 / 2 + Real.log 2 * (2 * Real.log y - Real.log 2)))
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤ y ^ 2 := by
  obtain ⟨p, hp, ho, hpx, hv⟩ :=
    exists_odd_prime_jacobi_ne_one_of_branch_polynomials_pos hn hns hGRH hy hzero hnonzero
  exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hpx

/-- Under GRH and positive branch polynomials at 4*B and B, QNeOne(B)<=y^2
for y>=8. Convert both polynomial certificates to the existing finite-maximum
endpoint criterion. This does not enumerate the admissible inputs. -/
theorem QNeOne_cast_le_of_branch_polynomials_pos {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 8 ≤ y)
    (hzero :
      0 <
        LLS.PaperStatements.oddEndpointTwoCostPolynomial (Real.log ((4 * B : ℕ) : ℝ)) (2096 / 1831)
          y (Real.log y) (Real.log 2) ((2 * Real.log y) ^ 2 / 2))
    (hnonzero :
      0 <
        LLS.PaperStatements.oddEndpointTwoCostPolynomial (Real.log (B : ℝ)) (2096 / 1831) y
          (Real.log y) ((4 / 3 : ℝ) * Real.log 2)
          ((2 * Real.log y) ^ 2 / 2 + Real.log 2 * (2 * Real.log y - Real.log 2))) :
    (QNeOne B : ℝ) ≤ y ^ 2 := by
  have hy1 : 1 < y := by linarith only [hy]
  have hy64 : 64 ≤ y ^ 2 := by nlinarith only [hy]
  have h0 :=
    LLS.PaperStatements.oddEndpointTwoCostLimit_neg_of_rational_polynomial_pos (4 * B) hy1 hzero
  have h1 :=
    LLS.PaperStatements.oddEndpointTwoCostLimit_neg_of_rational_polynomial_pos B hy1 hnonzero
  apply
    QNeOne_cast_le_of_conductor_branch_limits_neg hGRH (by linarith only [hy64]) hy64 (le_refl _)
  · simpa only [Real.log_pow, Nat.cast_ofNat] using h0
  · simpa only [Real.log_pow, Nat.cast_ofNat] using h1

end PseudoPrime.PseudoSquare
