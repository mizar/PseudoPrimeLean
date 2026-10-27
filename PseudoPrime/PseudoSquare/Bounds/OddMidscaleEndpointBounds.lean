/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.OddMidscaleEndpointRadius
public import PseudoPrime.PseudoSquare.Bounds.SharpOddEndpointDoubleLogBounds

/-! # Odd-prime non-one Jacobi witnesses at intermediate logarithmic scales -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- At 3259/25<=log B<=16277/100, both actual Jacobi conductor-branch
polynomials are positive at the affine odd-prime radius. Use the generic
branch transfer with b=log 2 and rewrite log(4B) exactly. The common ambient
level also permits a bound for every admissible input n<=B. -/
theorem oddMidscaleNeOne_branch_polynomials {B : ℕ} (hlo : 3259 / 25 ≤ Real.log B)
    (hhi : Real.log B ≤ 16277 / 100) :
    let y := LLS.PaperStatements.oddMidscaleEndpointRadius (Real.log B)
    0 <
        LLS.PaperStatements.oddEndpointTwoCostPolynomial (Real.log (4 * B : ℕ)) (2096 / 1831) y
          (Real.log y) (Real.log 2) ((2 * Real.log y) ^ 2 / 2) ∧
      0 <
        LLS.PaperStatements.oddEndpointTwoCostPolynomial (Real.log B) (2096 / 1831) y (Real.log y)
          ((4 / 3 : ℝ) * Real.log 2)
          ((2 * Real.log y) ^ 2 / 2 + Real.log 2 * (2 * Real.log y - Real.log 2)) := by
  let y := LLS.PaperStatements.oddMidscaleEndpointRadius (Real.log B)
  have hd := LLS.PaperStatements.oddMidscaleEndpointRadius_data hlo hhi
  have hB : 0 < B :=
    Nat.pos_of_ne_zero
      (by
        intro hz
        rw [hz, Nat.cast_zero, Real.log_zero] at hlo
        norm_num only at hlo)
  have he : Real.log (4 * B : ℕ) = Real.log B + 2 * Real.log 2 := by
    rw [Nat.cast_mul, Nat.cast_ofNat,
      Real.log_mul (by norm_num only : (4 : ℝ) ≠ 0) (Nat.cast_ne_zero.mpr hB.ne'),
      show (4 : ℝ) = 2 ^ 2 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    ring
  have hp :=
    LLS.PaperStatements.oddEndpoint_branches_pos_of_zero_pos (by linarith only [hd.1] : 2 ≤ y)
      (by linarith only [Real.log_two_lt_d9] : Real.log 2 ≤ (7 / 10 : ℝ)) hd.2.2
  rw [← he] at hp
  have hD : (2 * Real.log y) ^ 2 / 2 = 2 * (Real.log y) ^ 2 := by ring
  dsimp only
  rw [hD]
  exact hp

/-- Under GRH for an odd nonsquare n in the certified logarithmic interval,
there is an odd prime non-one Jacobi witness through the squared affine radius.
Apply the two actual conductor-branch certificates. Divisors of n remain
permitted zero witnesses, and prime 2 is excluded. -/
theorem exists_prime_ne_one_witness_le_oddMidscale {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hlo : 3259 / 25 ≤ Real.log n)
    (hhi : Real.log n ≤ 16277 / 100) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        (p : ℝ) ≤ (LLS.PaperStatements.oddMidscaleEndpointRadius (Real.log n)) ^ 2 ∧
        jacobiSym n p ≠ 1 := by
  have hd := LLS.PaperStatements.oddMidscaleEndpointRadius_data hlo hhi
  obtain ⟨hzero, hnonzero⟩ := oddMidscaleNeOne_branch_polynomials hlo hhi
  exact
    exists_odd_prime_jacobi_ne_one_of_branch_polynomials_pos hn hns hGRH (by linarith only [hd.1])
      hzero hnonzero

/-- For an odd nonsquare n in the certified logarithmic interval under GRH,
the least odd-prime non-one witness obeys the affine-radius bound. Transfer
the constructed witness by leastness; hw is the existing nonempty-set input. -/
theorem primeNeOneWitness_cast_le_oddMidscale {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hlo : 3259 / 25 ≤ Real.log n)
    (hhi : Real.log n ≤ 16277 / 100) (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤
      (LLS.PaperStatements.oddMidscaleEndpointRadius (Real.log n)) ^ 2 := by
  obtain ⟨p, hp, ho, hb, hv⟩ := exists_prime_ne_one_witness_le_oddMidscale hn hns hGRH hlo hhi
  exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hb

/-- Under GRH with 3259/25<=log B<=16277/100, the finite maximum QNeOne(B)
is at most the squared affine radius. Apply the common ambient branch
polynomials to every admissible input up to B, without finite enumeration. -/
theorem QNeOne_le_oddMidscale {B : ℕ} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : 3259 / 25 ≤ Real.log B) (hhi : Real.log B ≤ 16277 / 100) :
    (QNeOne B : ℝ) ≤ (LLS.PaperStatements.oddMidscaleEndpointRadius (Real.log B)) ^ 2 := by
  have hd := LLS.PaperStatements.oddMidscaleEndpointRadius_data hlo hhi
  obtain ⟨hzero, hnonzero⟩ := oddMidscaleNeOne_branch_polynomials hlo hhi
  exact QNeOne_cast_le_of_branch_polynomials_pos hGRH (by linarith only [hd.1]) hzero hnonzero

end PseudoPrime.PseudoSquare
