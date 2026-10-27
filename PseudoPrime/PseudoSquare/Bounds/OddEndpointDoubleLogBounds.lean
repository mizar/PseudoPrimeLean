/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.OddEndpointDoubleLogRoot
public import PseudoPrime.PseudoSquare.Bounds.OddEndpointBranchPolynomials

/-! # Odd-prime Jacobi non-one bounds with a double-logarithm correction -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- For log B>=96, both actual Jacobi conductor-branch polynomials are positive
at the double-logarithm root. Substitute b=log two in the correlated scalar theorem
and rewrite log(4B) exactly. This supplies a common endpoint even for small inputs n<=B. -/
theorem doubleLogNeOne_branch_polynomials {B : ℕ} (hL : 96 ≤ Real.log B) :
    let y := LLS.PaperStatements.oddEndpointDoubleLogRoot (Real.log B)
    0 <
        LLS.PaperStatements.oddEndpointTwoCostPolynomial (Real.log (4 * B : ℕ)) (2096 / 1831) y
          (Real.log y) (Real.log 2) ((2 * Real.log y) ^ 2 / 2) ∧
      0 <
        LLS.PaperStatements.oddEndpointTwoCostPolynomial (Real.log B) (2096 / 1831) y (Real.log y)
          ((4 / 3 : ℝ) * Real.log 2)
          ((2 * Real.log y) ^ 2 / 2 + Real.log 2 * (2 * Real.log y - Real.log 2)) := by
  let y := LLS.PaperStatements.oddEndpointDoubleLogRoot (Real.log B)
  have hB : 0 < B :=
    Nat.pos_of_ne_zero
      (by
        intro hz
        rw [hz, Nat.cast_zero, Real.log_zero] at hL
        norm_num only at hL)
  have he : Real.log (4 * B : ℕ) = Real.log B + 2 * Real.log 2 := by
    rw [Nat.cast_mul, Nat.cast_ofNat,
      Real.log_mul (by norm_num only : (4 : ℝ) ≠ 0) (Nat.cast_ne_zero.mpr hB.ne'),
      show (4 : ℝ) = 2 ^ 2 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    ring
  have hp :=
    LLS.PaperStatements.oddEndpoint_doubleLog_branch_polynomials_pos hL
      (by linarith only [Real.log_two_lt_d9] : Real.log 2 ≤ (7 / 10 : ℝ))
  rw [← he] at hp
  have hD : (2 * Real.log y) ^ 2 / 2 = 2 * (Real.log y) ^ 2 := by ring
  dsimp only
  rw [hD]
  exact hp

/-- For L>=96, the double-logarithm squared root is strictly below L^2.
Use root positivity and a logarithm lower bound from sixty-four. This certifies a strict
log-square upper bound for the same odd-prime witness, without taking a minimum. -/
theorem doubleLogNeOneRoot_sq_lt_log_sq {L : ℝ} (hL : 96 ≤ L) :
    (LLS.PaperStatements.oddEndpointDoubleLogRoot L) ^ 2 < L ^ 2 := by
  have hd := LLS.PaperStatements.oddEndpointDoubleLogRoot_data hL
  have hlog :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 64) (by linarith only [hL] : (64 : ℝ) ≤ L)
  rw [show (64 : ℝ) = 2 ^ 6 by norm_num only, Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hr : LLS.PaperStatements.oddEndpointDoubleLogRoot L < L := by
    dsimp only [LLS.PaperStatements.oddEndpointDoubleLogRoot]
    linarith only [hlog, Real.log_two_gt_d9]
  have hp :=
    mul_pos (sub_pos.mpr hr)
      (show 0 < L + LLS.PaperStatements.oddEndpointDoubleLogRoot L by linarith only [hd.1, hr])
  nlinarith only [hp]

/-- For L>=96 and log L>19/4, the new squared root is strictly below
(L-log L+11/4)^2. Compare positive roots using the exact correction difference.
This identifies the improvement interval over the previous logarithmic formula. -/
theorem doubleLogNeOneRoot_sq_lt_elevenFourths {L : ℝ} (hL : 96 ≤ L) (hlog : 19 / 4 < Real.log L) :
    (LLS.PaperStatements.oddEndpointDoubleLogRoot L) ^ 2 < (L - Real.log L + 11 / 4) ^ 2 := by
  have hd := LLS.PaperStatements.oddEndpointDoubleLogRoot_data hL
  have hr : LLS.PaperStatements.oddEndpointDoubleLogRoot L < L - Real.log L + 11 / 4 := by
    dsimp only [LLS.PaperStatements.oddEndpointDoubleLogRoot]
    linarith only [hlog]
  have hp :=
    mul_pos (sub_pos.mpr hr)
      (show 0 < L - Real.log L + 11 / 4 + LLS.PaperStatements.oddEndpointDoubleLogRoot L by
        linarith only [hd.1, hr])
  nlinarith only [hp]

/-- For odd nonsquare n under GRH with log n>=96, an odd-prime non-one
Jacobi witness lies through (log n-2log log n+15/2)^2 and strictly below (log n)^2.
Insert both certified branch polynomials into the existing arithmetic consumer.
Divisors of n remain allowed zero witnesses; two is excluded. -/
theorem exists_prime_ne_one_witness_le_doubleLog_and_lt_log_sq {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 96 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        (p : ℝ) ≤ (Real.log n - 2 * Real.log (Real.log n) + 15 / 2) ^ 2 ∧
        (p : ℝ) < (Real.log n) ^ 2 ∧ jacobiSym n p ≠ 1 := by
  have hd := LLS.PaperStatements.oddEndpointDoubleLogRoot_data hL
  obtain ⟨hzero, hnonzero⟩ := doubleLogNeOne_branch_polynomials hL
  obtain ⟨p, hp, ho, hb, hv⟩ :=
    exists_odd_prime_jacobi_ne_one_of_branch_polynomials_pos hn hns hGRH (by linarith only [hd.1])
      hzero hnonzero
  have hs := doubleLogNeOneRoot_sq_lt_log_sq hL
  have hlt := hb.trans_lt hs
  dsimp only [LLS.PaperStatements.oddEndpointDoubleLogRoot] at hb
  exact ⟨p, hp, ho, hb, hlt, hv⟩

/-- Under the odd-nonsquare GRH and logarithmic-size assumptions, the least
odd-prime non-one Jacobi witness has the double-logarithm bound.
Apply leastness to the constructed witness. This is the pointwise record interface. -/
theorem primeNeOneWitness_cast_le_doubleLog {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 96 ≤ Real.log n)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤
      (Real.log n - 2 * Real.log (Real.log n) + 15 / 2) ^ 2 := by
  obtain ⟨p, hp, ho, hb, _, hv⟩ :=
    exists_prime_ne_one_witness_le_doubleLog_and_lt_log_sq hn hns hGRH hL
  exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hb

/-- Under GRH and log B>=96, QNeOne(B) is at most the double-logarithm square.
Apply the common branch polynomial certificate to the full finite maximum,
including all smaller admissible inputs. No finite input enumeration is used. -/
theorem QNeOne_le_doubleLog {B : ℕ} (hL : 96 ≤ Real.log B)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (QNeOne B : ℝ) ≤ (Real.log B - 2 * Real.log (Real.log B) + 15 / 2) ^ 2 := by
  have hd := LLS.PaperStatements.oddEndpointDoubleLogRoot_data hL
  obtain ⟨hzero, hnonzero⟩ := doubleLogNeOne_branch_polynomials hL
  have hb := QNeOne_cast_le_of_branch_polynomials_pos hGRH (by linarith only [hd.1]) hzero hnonzero
  dsimp only [LLS.PaperStatements.oddEndpointDoubleLogRoot] at hb
  exact hb

end PseudoPrime.PseudoSquare
