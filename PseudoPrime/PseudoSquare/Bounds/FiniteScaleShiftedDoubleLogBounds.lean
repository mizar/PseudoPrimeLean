/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.FiniteScaleShiftedDoubleLogRoot
public import PseudoPrime.PseudoSquare.Bounds.ShiftedOddEndpointDoubleLogBounds

/-! # Odd-prime non-one Jacobi witnesses from log scale fifty -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- Under GRH, every odd nonsquare n≤B has a non-one odd prime witness
below the squared 37/5 radius at B, provided log B≥50. The conductor-branch
polynomials are now certified from radius 49. A common ambient scale
allows finite maxima without enumerating small inputs. -/
theorem exists_prime_ne_one_le_shiftedDoubleLog_from_fifty_of_le {n B : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 50 ≤ Real.log B) (hnB : n ≤ B) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        jacobiSym n p ≠ 1 ∧
        (p : ℝ) ≤ (LLS.PaperStatements.shiftedOddEndpointDoubleLogRoot (Real.log B)) ^ 2 := by
  let y := LLS.PaperStatements.shiftedOddEndpointDoubleLogRoot (Real.log B)
  have hd := LLS.PaperStatements.shiftedOddEndpointDoubleLogRoot_data_from_fifty hL
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
    LLS.PaperStatements.shiftedOddEndpoint_doubleLog_branch_polynomials_pos_from_fifty hL
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

/-- Under GRH for an odd nonsquare input with log n≥50, the least odd-prime
non-one Jacobi witness is bounded by the squared 37/5 radius. Apply leastness
to the prime witness supplied by the shifted conductor-branch comparison. -/
theorem primeNeOneWitness_cast_le_shiftedDoubleLog_from_fifty {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 50 ≤ Real.log n) (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤
      (Real.log n - 2 * Real.log (Real.log n) + 37 / 5) ^ 2 := by
  obtain ⟨p, hp, ho, hv, hb⟩ :=
    exists_prime_ne_one_le_shiftedDoubleLog_from_fifty_of_le hn hns hGRH hL (le_refl n)
  exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hb

/-- Under GRH and log B≥50, the same radius bounds QNeOne(B), including all
smaller admissible inputs. Use the common scale B and leastness at each input.
No finite input enumeration or endpoint certificate is needed. -/
theorem QNeOne_le_shiftedDoubleLog_from_fifty {B : ℕ} (hL : 50 ≤ Real.log B)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (QNeOne B : ℝ) ≤ (Real.log B - 2 * Real.log (Real.log B) + 37 / 5) ^ 2 := by
  apply QNeOne_cast_le_of_forall (sq_nonneg _)
  intro n hn
  have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
  obtain ⟨p, hp, ho, hv, hb⟩ :=
    exists_prime_ne_one_le_shiftedDoubleLog_from_fifty_of_le ha.odd ha.not_isSquare hGRH hL ha.le
  exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n _ ⟨hp, ho, hv⟩)).trans hb

/-- For L≥50 the 37/5 squared radius is strictly below L². Use log 48
as an exact lower certificate for log L and the positive root bound 49.
This comparison concerns the same non-one odd-prime witness range. -/
theorem shiftedDoubleLogRoot_sq_lt_log_sq_from_fifty {L : ℝ} (hL : 50 ≤ L) :
    (LLS.PaperStatements.shiftedOddEndpointDoubleLogRoot L) ^ 2 < L ^ 2 := by
  have hlog : (37 / 10 : ℝ) < Real.log L := by
    have hh :=
      Real.log_le_log (by norm_num only : (0 : ℝ) < 2 ^ 4 * 3)
        (by linarith only [hL] : (2 : ℝ) ^ 4 * 3 ≤ L)
    rw [Real.log_mul (by norm_num only : (2 : ℝ) ^ 4 ≠ 0) (by norm_num only : (3 : ℝ) ≠ 0),
      Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith only [hh, Real.log_two_gt_d9, Real.log_three_gt_d9]
  have hd := (LLS.PaperStatements.shiftedOddEndpointDoubleLogRoot_data_from_fifty hL).1
  have hroot : LLS.PaperStatements.shiftedOddEndpointDoubleLogRoot L < L := by
    dsimp only [LLS.PaperStatements.shiftedOddEndpointDoubleLogRoot]
    linarith only [hlog]
  have hy : 0 ≤ LLS.PaperStatements.shiftedOddEndpointDoubleLogRoot L := by linarith only [hd]
  simpa only [pow_two] using mul_self_lt_mul_self hy hroot

/-- On L≥50 with log L>22/5, the 37/5 squared radius is strictly below
the previous L-log L+3 squared radius. Compare their positive roots by the
exact difference log L-22/5; this identifies the new best interval entrance. -/
theorem shiftedDoubleLogRoot_sq_lt_log_shift_from_fifty {L : ℝ} (hL : 50 ≤ L)
    (hlog : (22 / 5 : ℝ) < Real.log L) :
    (LLS.PaperStatements.shiftedOddEndpointDoubleLogRoot L) ^ 2 < (L - Real.log L + 3) ^ 2 := by
  have hd := (LLS.PaperStatements.shiftedOddEndpointDoubleLogRoot_data_from_fifty hL).1
  have hroot : LLS.PaperStatements.shiftedOddEndpointDoubleLogRoot L < L - Real.log L + 3 := by
    dsimp only [LLS.PaperStatements.shiftedOddEndpointDoubleLogRoot]
    linarith only [hlog]
  have hy : 0 ≤ LLS.PaperStatements.shiftedOddEndpointDoubleLogRoot L := by linarith only [hd]
  simpa only [pow_two] using mul_self_lt_mul_self hy hroot

end PseudoPrime.PseudoSquare
