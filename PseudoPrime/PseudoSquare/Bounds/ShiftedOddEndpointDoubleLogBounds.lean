/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ShiftedOddEndpointDoubleLogRoot
public import PseudoPrime.LLS.SharpOddEndpointWitness
public import PseudoPrime.PseudoSquare.Bounds.OddEndpointConductorBranches
public import PseudoPrime.PseudoSquare.Bounds.SharpOddEndpointDoubleLogBounds

/-! # Non-one odd-prime Jacobi bounds retaining the half-log-two shift -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

open AnalyticNumberTheory.Arithmetic in
/-- If the primitive value at two is zero and all odd primes through x are
trivial, the logarithmic defect is at most half the square of log x-log 2/2.
Reduce to the exact powers-of-two sum and retain its affine half-step shift.
This supplies the zero branch in the improved non-one witness comparison. -/
theorem log_defect_le_shifted_half_sq_of_two_zero {N : ℕ} (χ : DirichletCharacter ℂ N) {x : ℝ}
    (hx : 2 ≤ x) (h2 : χ.primitiveCharacter 2 = 0)
    (ht : ∀ p : ℕ, p.Prime → Odd p → (p : ℝ) ≤ x → χ.primitiveCharacter p = 1) :
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum x -
        (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ.primitiveCharacter).re ≤
      (Real.log x - Real.log 2 / 2) ^ 2 / 2 := by
  have hx1 : 1 ≤ x := (by norm_num only : (1 : ℝ) ≤ 2).trans hx
  have ho :
    ∀ {k p : ℕ},
      k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊ →
        p ∈ Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ → p.Prime → Odd p → χ.primitiveCharacter p = 1 := by
    intro k p hk hp hprime hodd
    exact
      ht p hprime hodd
        (LLS.PaperStatements.cast_le_of_mem_root_cutoff hx1 (Finset.mem_Icc.mp hk).1 hp)
  rw [logWeightedMangoldtSum_sub_characterLogWeightedSum_re_eq_twoAdicCorrection_of_eq_one x χ hx
      ho]
  exact
    twoAdicLogCorrection_le_shifted_half_log_sq_of_apply_two_eq_zero x χ
      ((by norm_num only : (0 : ℝ) < 2).trans_le hx).ne' h2

/-- Under GRH, negative endpoint limits in the zero and nonzero branches
give an odd non-one Jacobi prime. The zero branch retains the half-log-two
shift; the nonzero branch uses the uniform sharp half-square defect.
The conductor bounds remain correlated with the primitive value at two. -/
theorem exists_odd_prime_jacobi_ne_one_of_shifted_conductor_branch_limits_neg {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x Y : ℝ}
    (hx : 1 < x) (hY : 64 ≤ Y) (hYx : Y ≤ x)
    (hzero :
      LLS.PaperStatements.oddEndpointTwoCostLimit (4 * n) x Y (Real.log 2)
          ((Real.log x - Real.log 2 / 2) ^ 2 / 2) <
        0)
    (hnonzero :
      LLS.PaperStatements.oddEndpointTwoCostLimit n x Y ((4 / 3 : ℝ) * Real.log 2)
          ((Real.log x) ^ 2 / 2) <
        0) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ x ∧ jacobiSym n p ≠ 1 := by
  let _ : NeZero (4 * n) := ⟨Nat.mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  let χ := NumberTheory.complexQuadraticCharacter n hn
  let _ : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hne : χ.primitiveCharacter ≠ 1 :=
    NumberTheory.primitiveQuadraticCharacter_ne_one_of_not_square n hn hns
  have hq : 2 ≤ χ.conductor :=
    (Nat.two_le_iff _).mpr
      ⟨χ.conductor_ne_zero, fun he ↦ hne (DirichletCharacter.level_one' χ.primitiveCharacter he)⟩
  have hquad : χ.primitiveCharacter.IsQuadratic :=
    NumberTheory.isQuadratic_primitiveCharacter χ
      (NumberTheory.complexQuadraticCharacter_isQuadratic n hn)
  have hx2 : 2 ≤ x := by linarith only [hY, hYx]
  have hex : ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ x ∧ χ.primitiveCharacter p ≠ 1 := by
    by_cases h2 : χ.primitiveCharacter 2 = 0
    · have hqle := Nat.le_of_dvd (NeZero.pos (4 * n)) χ.conductor_dvd_level
      have hm :=
        LLS.PaperStatements.oddEndpointTwoCostLimit_mono_level (c := Real.log 2) (D :=
          (Real.log x - Real.log 2 / 2) ^ 2 / 2) (Nat.pos_of_ne_zero χ.conductor_ne_zero) hqle hx.le
          hY
      have hC :
        LLS.PaperStatements.quadraticTwoReciprocalCost (χ.primitiveCharacter 2) ≤ Real.log 2 := by
        rw [LLS.PaperStatements.quadraticTwoReciprocalCost, ite_eq_left h2]
      exact
        LLS.PaperStatements.exists_odd_prime_of_twoCostLimit_neg_of_defect_bound χ hq hne hquad hGRH
          hx hY hYx hC (fun ht ↦ log_defect_le_shifted_half_sq_of_two_zero χ hx2 h2 ht)
          (hm.trans_lt hzero)
    · have hqle := NumberTheory.primitiveQuadratic_conductor_le_of_two_ne_zero hn h2
      have hm :=
        LLS.PaperStatements.oddEndpointTwoCostLimit_mono_level (c := (4 / 3 : ℝ) * Real.log 2) (D :=
          (Real.log x) ^ 2 / 2) (Nat.pos_of_ne_zero χ.conductor_ne_zero) hqle hx.le hY
      exact
        LLS.PaperStatements.exists_odd_prime_of_sharp_twoCostLimit_neg χ hq hne hquad hGRH hx hY hYx
          (LLS.PaperStatements.quadraticTwoReciprocalCost_le_four_thirds _) (hm.trans_lt hnonzero)
  obtain ⟨p, hp, ho, hb, hv⟩ := hex
  exact
    ⟨p, hp, ho, hb, NumberTheory.jacobi_ne_one_of_primitiveQuadraticCharacter_ne_one hn hp ho hv⟩

/-- For an odd nonsquare n≤B under GRH and log B≥96, a non-one odd prime
lies below the squared 37/5 radius at B. Combine the two rational polynomial
certificates, monotonicity in the conductor, and the shifted arithmetic bounds.
Using B as a common scale makes the finite-maximum theorem available. -/
theorem exists_prime_ne_one_le_shiftedDoubleLog_of_le {n B : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 96 ≤ Real.log B)
    (hnB : n ≤ B) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        jacobiSym n p ≠ 1 ∧
        (p : ℝ) ≤ (LLS.PaperStatements.shiftedOddEndpointDoubleLogRoot (Real.log B)) ^ 2 := by
  let y := LLS.PaperStatements.shiftedOddEndpointDoubleLogRoot (Real.log B)
  have hd := LLS.PaperStatements.shiftedOddEndpointDoubleLogRoot_data hL
  have hy1 : 1 < y := by linarith only [hd.1]
  have h64 : 64 ≤ y ^ 2 := by nlinarith only [hd.1]
  have hx : 1 < y ^ 2 := by linarith only [h64]
  have hB : 0 < B := hn.pos.trans_le hnB
  have hlog4 : Real.log (4 * B : ℕ) = Real.log B + 2 * Real.log 2 := by
    rw [Nat.cast_mul, Nat.cast_ofNat,
      Real.log_mul (by norm_num only : (4 : ℝ) ≠ 0) (Nat.cast_ne_zero.mpr hB.ne'),
      show (4 : ℝ) = 2 ^ 2 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    ring
  have hp :=
    LLS.PaperStatements.shiftedOddEndpoint_doubleLog_branch_polynomials_pos hL
      (show (69 / 100 : ℝ) ≤ Real.log 2 by linarith only [Real.log_two_gt_d9])
      (show Real.log 2 ≤ (7 / 10 : ℝ) by linarith only [Real.log_two_lt_d9])
  rw [← hlog4] at hp
  have h0 :=
    LLS.PaperStatements.oddEndpointTwoCostLimit_neg_of_rational_polynomial_pos (4 * B) hy1 hp.1
  have h1 := LLS.PaperStatements.oddEndpointTwoCostLimit_neg_of_rational_polynomial_pos B hy1 hp.2
  have hm0 :=
    LLS.PaperStatements.oddEndpointTwoCostLimit_mono_level (c := Real.log 2) (D :=
      (2 * Real.log y - Real.log 2 / 2) ^ 2 / 2) (Nat.mul_pos (by decide : 0 < 4) hn.pos)
      (Nat.mul_le_mul_left 4 hnB) hx.le h64
  have hm1 :=
    LLS.PaperStatements.oddEndpointTwoCostLimit_mono_level (c := (4 / 3 : ℝ) * Real.log 2) (D :=
      2 * (Real.log y) ^ 2) hn.pos hnB hx.le h64
  have hz :
    LLS.PaperStatements.oddEndpointTwoCostLimit (4 * n) (y ^ 2) (y ^ 2) (Real.log 2)
        ((Real.log (y ^ 2) - Real.log 2 / 2) ^ 2 / 2) <
      0 := by
    simpa only [Real.log_pow, Nat.cast_ofNat] using hm0.trans_lt h0
  have hne :
    LLS.PaperStatements.oddEndpointTwoCostLimit n (y ^ 2) (y ^ 2) ((4 / 3 : ℝ) * Real.log 2)
        ((Real.log (y ^ 2)) ^ 2 / 2) <
      0 := by
    have he : (Real.log (y ^ 2)) ^ 2 / 2 = 2 * (Real.log y) ^ 2 := by
      rw [Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      ring
    rw [he]
    exact hm1.trans_lt h1
  obtain ⟨p, hp, ho, hb, hv⟩ :=
    exists_odd_prime_jacobi_ne_one_of_shifted_conductor_branch_limits_neg hn hns hGRH hx h64
      (le_refl _) hz hne
  exact ⟨p, hp, ho, hv, hb⟩

/-- Under GRH for an odd nonsquare input with log n≥96, the least odd-prime
non-one Jacobi witness is bounded by the squared 37/5 radius. Apply leastness
to the prime witness supplied by the shifted conductor-branch comparison. -/
theorem primeNeOneWitness_cast_le_shiftedDoubleLog {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 96 ≤ Real.log n)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤
      (Real.log n - 2 * Real.log (Real.log n) + 37 / 5) ^ 2 := by
  obtain ⟨p, hp, ho, hv, hb⟩ :=
    exists_prime_ne_one_le_shiftedDoubleLog_of_le hn hns hGRH hL (le_refl n)
  exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hb

/-- Under GRH and log B≥96, the same radius bounds QNeOne(B), including all
smaller admissible inputs. Use the common scale B and leastness at each input.
No finite input enumeration or endpoint certificate is needed. -/
theorem QNeOne_le_shiftedDoubleLog {B : ℕ} (hL : 96 ≤ Real.log B)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (QNeOne B : ℝ) ≤ (Real.log B - 2 * Real.log (Real.log B) + 37 / 5) ^ 2 := by
  apply QNeOne_cast_le_of_forall (sq_nonneg _)
  intro n hn
  have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
  obtain ⟨p, hp, ho, hv, hb⟩ :=
    exists_prime_ne_one_le_shiftedDoubleLog_of_le ha.odd ha.not_isSquare hGRH hL ha.le
  exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n _ ⟨hp, ho, hv⟩)).trans hb

/-- On L≥96 the squared 37/5 radius is strictly below the previous 149/20
radius squared. The new root is at least 94 and the difference is exactly 1/20.
This proves improvement for the same witness on the entire application range. -/
theorem shiftedDoubleLogRoot_sq_lt_sharp {L : ℝ} (hL : 96 ≤ L) :
    (LLS.PaperStatements.shiftedOddEndpointDoubleLogRoot L) ^ 2 <
      (LLS.PaperStatements.sharpOddEndpointDoubleLogRoot L) ^ 2 := by
  have hd := LLS.PaperStatements.shiftedOddEndpointDoubleLogRoot_data hL
  have he :
    LLS.PaperStatements.sharpOddEndpointDoubleLogRoot L =
      LLS.PaperStatements.shiftedOddEndpointDoubleLogRoot L + 1 / 20 := by
    dsimp only [LLS.PaperStatements.sharpOddEndpointDoubleLogRoot,
      LLS.PaperStatements.shiftedOddEndpointDoubleLogRoot]
    ring
  rw [he]
  nlinarith only [hd.1]

/-- The squared 37/5 radius is strictly below L² on L≥96. Compare it first
with the previous certified radius and reuse its strict log-square comparison. -/
theorem shiftedDoubleLogRoot_sq_lt_log_sq {L : ℝ} (hL : 96 ≤ L) :
    (LLS.PaperStatements.shiftedOddEndpointDoubleLogRoot L) ^ 2 < L ^ 2 := by
  exact (shiftedDoubleLogRoot_sq_lt_sharp hL).trans (sharpDoubleLogNeOneRoot_sq_lt_log_sq hL)

/-- On L≥96 the 37/5 squared radius improves the 11/4 single-log radius
whenever log L exceeds 93/20. Compare the positive roots using their exact
additive difference. This identifies the improved entrance in the table. -/
theorem shiftedDoubleLogRoot_sq_lt_elevenFourths {L : ℝ} (hL : 96 ≤ L)
    (hlog : 93 / 20 < Real.log L) :
    (LLS.PaperStatements.shiftedOddEndpointDoubleLogRoot L) ^ 2 <
      (L - Real.log L + 11 / 4) ^ 2 := by
  have hd := LLS.PaperStatements.shiftedOddEndpointDoubleLogRoot_data hL
  have hr : LLS.PaperStatements.shiftedOddEndpointDoubleLogRoot L < L - Real.log L + 11 / 4 := by
    dsimp only [LLS.PaperStatements.shiftedOddEndpointDoubleLogRoot]
    linarith only [hlog]
  have hm :=
    mul_pos (sub_pos.mpr hr)
      (show 0 < L - Real.log L + 11 / 4 + LLS.PaperStatements.shiftedOddEndpointDoubleLogRoot L by
        linarith only [hd.1, hr])
  nlinarith only [hm]

end PseudoPrime.PseudoSquare
