/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.EulerLocalCorrectionBounds
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Explicit integral budgets for Euler correction tails

An all-integer tail bounds an injectively indexed rational-prime tail.
Prime-ideal norm multiplicities must be counted separately.
The exponents are those of the correction factor on page 7 of A Short Proof of the QRH.
No zero-free-region assertion is used.
-/

@[expose] public section

namespace PseudoPrime.Analysis.EulerCorrectionBounds

/-- The local majorant from the short QRH manuscript, as an explicit function of the
positive norm q. It is used only after local norm hypotheses have been checked. -/
noncomputable def correctionMajorant (q : ℝ) : ℝ :=
  4 * (q ^ (-2 : ℝ) + q ^ (-(23 / 12) : ℝ) + q ^ (-(5 / 2) : ℝ))

/-- The explicit integral upper bound for the majorant tail above a positive cutoff.
It bounds the sum over all integers; repeated norms require a multiplicity bound. -/
noncomputable def correctionTailBudget (x : ℝ) : ℝ :=
  4 * (x ^ (-1 : ℝ) + (12 / 11) * x ^ (-(11 / 12) : ℝ) + (2 / 3) * x ^ (-(3 / 2) : ℝ))

/-- Nonnegative bases give nonnegative local majorants. This also bounds the zero
deviation of deleted factors and supplies the hypotheses for multiplicity summation. -/
theorem correctionMajorant_nonneg {q : ℝ} (hq : 0 ≤ q) : 0 ≤ correctionMajorant q := by
  exact
    mul_nonneg (by norm_num only)
      (add_nonneg (add_nonneg (Real.rpow_nonneg hq _) (Real.rpow_nonneg hq _))
        (Real.rpow_nonneg hq _))

/-- Every shifted real power series of exponent less than minus one is summable.
Use the p-series criterion before comparing actual local deviations with this tail. -/
theorem summable_rpow_tail (N : ℕ) {a : ℝ} (ha : a < -1) :
    Summable (fun n : ℕ ↦ ((n + N + 1 : ℕ) : ℝ) ^ a) := by
  simpa only [Nat.add_assoc] using
    (summable_nat_add_iff (N + 1)).mpr (Real.summable_nat_rpow.mpr ha)

/-- For positive cutoff N and a < -1, the shifted power tail is at most its explicit
improper integral. Monotonicity and the integral test retain every numerical constant. -/
theorem rpow_tail_le (N : ℕ) (hN : 0 < N) {a : ℝ} (ha : a < -1) :
    ∑' n : ℕ, ((n + N + 1 : ℕ) : ℝ) ^ a ≤ -(N : ℝ) ^ (a + 1) / (a + 1) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hanti : AntitoneOn (fun x : ℝ ↦ x ^ a) (Set.Ici (N : ℝ)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (hNr.trans_le hx) hxy (ha.le.trans (by norm_num only))
  have h :=
    hanti.tsum_comp_add_le_integral N (integrableOn_Ioi_rpow_of_lt ha hNr)
      (fun x hx ↦ Real.rpow_nonneg (le_of_lt (hNr.trans hx)) a)
  rw [integral_Ioi_rpow_of_lt ha hNr] at h
  exact h

/-- The correction majorant is summable over all integers above any natural cutoff.
Sum the three convergent power tails and retain the coefficient four. -/
theorem summable_correctionMajorant_tail (N : ℕ) :
    Summable (fun n : ℕ ↦ correctionMajorant (n + N + 1 : ℕ)) := by
  exact
    Summable.mul_left 4
      (((summable_rpow_tail N (by norm_num only : (-2 : ℝ) < -1)).add
            (summable_rpow_tail N (by norm_num only : (-(23 / 12) : ℝ) < -1))).add
        (summable_rpow_tail N (by norm_num only : (-(5 / 2) : ℝ) < -1)))

/-- The all-integer correction tail is at most correctionTailBudget N for N > 0.
Evaluate the three power integrals exactly, without a prime-density assumption. -/
theorem correctionMajorant_tail_le (N : ℕ) (hN : 0 < N) :
    ∑' n : ℕ, correctionMajorant (n + N + 1 : ℕ) ≤ correctionTailBudget N := by
  have h2 := rpow_tail_le N hN (by norm_num only : (-2 : ℝ) < -1)
  have h23 := rpow_tail_le N hN (by norm_num only : (-(23 / 12) : ℝ) < -1)
  have h5 := rpow_tail_le N hN (by norm_num only : (-(5 / 2) : ℝ) < -1)
  simp only [correctionMajorant, tsum_mul_left,
    ((summable_rpow_tail N (by norm_num only : (-2 : ℝ) < -1)).add
            (summable_rpow_tail N (by norm_num only : (-(23 / 12) : ℝ) < -1))).tsum_add
        (summable_rpow_tail N (by norm_num only : (-(5 / 2) : ℝ) < -1)),
    (summable_rpow_tail N (by norm_num only : (-2 : ℝ) < -1)).tsum_add
        (summable_rpow_tail N (by norm_num only : (-(23 / 12) : ℝ) < -1)),
    correctionTailBudget]
  norm_num only at h2 h23 h5
  linarith only [h2, h23, h5]

/-- A base at least four and exponent at most minus one half give a value at most
one half. This checks the two local denominators from the manuscript's power bounds. -/
theorem rpow_le_half {q a : ℝ} (hq : 4 ≤ q) (ha : a ≤ -(1 / 2 : ℝ)) : q ^ a ≤ 1 / 2 := by
  have hq1 : 1 ≤ q := le_trans (by norm_num only) hq
  have h :=
    (Real.rpow_le_rpow_of_exponent_le hq1 ha).trans
      (Real.rpow_le_rpow_of_nonpos (by norm_num only : (0 : ℝ) < 4) hq
        (by norm_num only : -(1 / 2 : ℝ) ≤ 0))
  norm_num only [Real.rpow_neg, ← Real.sqrt_eq_rpow] at h
  exact h

/-- For q ≥ 4 and the manuscript's local power bounds, the actual rational correction
has error at most correctionMajorant q. No hypothesis about zeros is needed. -/
theorem norm_localCorrection_sub_one_le_correctionMajorant {q : ℝ} {D R : ℂ} (hq : 4 ≤ q)
    (hD : ‖D‖ ≤ q ^ (-(11 / 12) : ℝ)) (hR : ‖R‖ ≤ q ^ (-(5 / 2) : ℝ)) :
    ‖localCorrection q⁻¹ D R - 1‖ ≤ correctionMajorant q := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num only) hq
  have ht : q⁻¹ ≤ 1 / 2 := by
    have h :=
      one_div_le_one_div_of_le (by norm_num only : (0 : ℝ) < 2) (le_trans (by norm_num only) hq)
    norm_num only [one_div] at h
    exact h
  have h :=
    norm_localCorrection_sub_one_le_majorant (inv_nonneg.mpr hq0.le) ht
      (hD.trans (rpow_le_half hq (by norm_num only)))
      (hR.trans (rpow_le_half hq (by norm_num only))) hD hR
  have hs : q⁻¹ ^ 2 = q ^ (-2 : ℝ) := by rw [Real.rpow_neg hq0.le, Real.rpow_two, inv_pow]
  have hm : q⁻¹ * q ^ (-(11 / 12) : ℝ) = q ^ (-(23 / 12) : ℝ) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hq0]
    norm_num only
  simpa only [hs, hm, correctionMajorant] using h

/-- Any complex factor family whose deviations are bounded by the integer-tail majorant
has a nonzero infinite product with explicit inverse bound when the integral budget is small.
This is the interface for separately verified local factors and norm multiplicities. -/
theorem correction_tprod_inverse_of_tail (N : ℕ) (hN : 0 < N) (f : ℕ → ℂ) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hf : ∀ n, ‖f n - 1‖ ≤ correctionMajorant (n + N + 1 : ℕ))
    (hB : correctionTailBudget N ≤ Real.log (1 + δ)) :
    (∏' n, f n) ≠ 0 ∧ ‖(∏' n, f n)⁻¹‖ ≤ (1 - δ)⁻¹ := by
  have hs :=
    Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) hf (summable_correctionMajorant_tail N)
  have hsum :=
    (Summable.tsum_le_tsum hf hs (summable_correctionMajorant_tail N)).trans
      ((correctionMajorant_tail_le N hN).trans hB)
  have h := inverse_tprod_bound (fun n ↦ f n - 1) hs hδ0 hδ1 hsum
  simpa only [← add_sub_assoc, add_sub_cancel_left] using h

/-- Deleting any selection of factors preserves the integer-tail inverse bound.
Only retained factors need local error estimates; deleted factors contribute zero error. -/
theorem masked_correction_tprod_inverse_of_tail (N : ℕ) (hN : 0 < N) (keep : ℕ → Prop)
    [DecidablePred keep] (f : ℕ → ℂ) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hf : ∀ n, keep n → ‖f n - 1‖ ≤ correctionMajorant (n + N + 1 : ℕ))
    (hB : correctionTailBudget N ≤ Real.log (1 + δ)) :
    (∏' n, if keep n then f n else 1) ≠ 0 ∧ ‖(∏' n, if keep n then f n else 1)⁻¹‖ ≤ (1 - δ)⁻¹ := by
  apply correction_tprod_inverse_of_tail N hN _ hδ0 hδ1 _ hB
  intro n
  split_ifs with hn
  · exact hf n hn
  · rw [sub_self, norm_zero]
    exact correctionMajorant_nonneg (Nat.cast_nonneg _)

/-- For a cutoff at least three, the manuscript's local power bounds on all retained
integer norms imply the actual masked correction product is nonzero with explicit inverse.
The only remaining numerical premise is the displayed integral budget. -/
theorem local_correction_tprod_inverse_of_tail (N : ℕ) (hN : 3 ≤ N) (keep : ℕ → Prop)
    [DecidablePred keep] (D R : ℕ → ℂ) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hD : ∀ n, keep n → ‖D n‖ ≤ ((n + N + 1 : ℕ) : ℝ) ^ (-(11 / 12) : ℝ))
    (hR : ∀ n, keep n → ‖R n‖ ≤ ((n + N + 1 : ℕ) : ℝ) ^ (-(5 / 2) : ℝ))
    (hB : correctionTailBudget N ≤ Real.log (1 + δ)) :
    (∏' n, if keep n then localCorrection ((n + N + 1 : ℕ) : ℝ)⁻¹ (D n) (R n) else 1) ≠ 0 ∧
      ‖(∏' n, if keep n then localCorrection ((n + N + 1 : ℕ) : ℝ)⁻¹ (D n) (R n) else 1)⁻¹‖ ≤
        (1 - δ)⁻¹ := by
  apply
    masked_correction_tprod_inverse_of_tail N (lt_of_lt_of_le (by norm_num only : 0 < 3) hN) keep _
      hδ0 hδ1 _ hB
  intro n hn
  apply norm_localCorrection_sub_one_le_correctionMajorant _ (hD n hn) (hR n hn)
  exact_mod_cast Nat.succ_le_succ (hN.trans (Nat.le_add_left N n))

/-- A finite set of slots for each integer norm preserves summability of the majorant.
The slot type records possible prime-ideal norm multiplicities explicitly. -/
theorem summable_correctionMajorant_multiplicity_tail {κ : Type*} [Finite κ] (N : ℕ) :
    Summable (fun j : κ × ℕ ↦ correctionMajorant (j.2 + N + 1 : ℕ)) := by
  let : Fintype κ := Fintype.ofFinite κ
  exact
    (summable_prod_of_nonneg
          (fun j ↦ correctionMajorant_nonneg (Nat.cast_nonneg (j.2 + N + 1)))).mpr
      ⟨fun _ ↦ summable_correctionMajorant_tail N, (hasSum_fintype _).summable⟩

/-- For a finite number of slots per norm, the infinite product is nonzero with explicit
inverse bound when cardinality times the integral budget is small.
An application to prime ideals must separately identify the factors with these slots. -/
theorem correction_tprod_inverse_of_multiplicity_tail {κ : Type*} [Fintype κ] (N : ℕ) (hN : 0 < N)
    (f : κ × ℕ → ℂ) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hf : ∀ j, ‖f j - 1‖ ≤ correctionMajorant (j.2 + N + 1 : ℕ))
    (hB : (Fintype.card κ : ℝ) * correctionTailBudget N ≤ Real.log (1 + δ)) :
    (∏' j, f j) ≠ 0 ∧ ‖(∏' j, f j)⁻¹‖ ≤ (1 - δ)⁻¹ := by
  have ha := summable_correctionMajorant_multiplicity_tail (κ := κ) N
  have hs := Summable.of_nonneg_of_le (fun j ↦ norm_nonneg _) hf ha
  have hsum := Summable.tsum_le_tsum hf hs ha
  have heq :
    ∑' j : κ × ℕ, correctionMajorant (j.2 + N + 1 : ℕ) =
      (Fintype.card κ : ℝ) * ∑' n : ℕ, correctionMajorant (n + N + 1 : ℕ) := by
    rw [ha.tsum_prod]
    change ∑' _ : κ, (∑' n : ℕ, correctionMajorant (n + N + 1 : ℕ)) = _
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [heq] at hsum
  have hbudget :=
    mul_le_mul_of_nonneg_left (correctionMajorant_tail_le N hN)
      (Nat.cast_nonneg (Fintype.card κ) : (0 : ℝ) ≤ Fintype.card κ)
  have h := inverse_tprod_bound (fun j ↦ f j - 1) hs hδ0 hδ1 (hsum.trans (hbudget.trans hB))
  simpa only [← add_sub_assoc, add_sub_cancel_left] using h

end PseudoPrime.Analysis.EulerCorrectionBounds
