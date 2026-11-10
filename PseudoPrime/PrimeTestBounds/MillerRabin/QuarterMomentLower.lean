/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentRows

/-! # Lower finite Mangoldt moment certificates -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A certified prime-power row and nonnegative rational lower endpoint for
its inverse power give a lower bound for its Mangoldt logarithmic moment.
The row certificate supplies a lower bound for the prime logarithm. -/
theorem quarter_moment_row_lower (r : EulerCenterRow) (hc : eulerCenterRowCheck r = true) (k : ℕ)
    {u : ℚ} (hu0 : 0 ≤ u)
    (hu :
      AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck (r.p ^ (r.k + 1) : ℕ) u 1 79 50 =
        true)
    (hlo : 0 ≤ r.lo) :
    (((r.lo * ((r.k + 1 : ℕ) * r.lo) ^ k * u : ℚ) : ℝ)) ≤
      quarterMangoldtMoment k (r.p ^ (r.k + 1)) := by
  have hlog := (checked_row_log_bounds hc).1
  have hlo0 : (0 : ℝ) ≤ r.lo := by exact_mod_cast hlo
  have huR : (0 : ℝ) ≤ u := by exact_mod_cast hu0
  have hmul := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (r.k + 1) : (0 : ℝ) ≤ (r.k + 1 : ℕ))
  have hpower := (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound hu).1
  norm_num only [Rat.cast_natCast] at hpower
  have hlogpow : (r.k + 1 : ℕ) * (r.lo : ℝ) ≤ Real.log ((r.p ^ (r.k + 1) : ℕ) : ℝ) := by
    simpa only [Nat.cast_pow, Real.log_pow, Nat.cast_add, Nat.cast_one] using hmul
  have hterm :=
    mul_le_mul hlog (pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) hlo0) hlogpow k)
      (pow_nonneg (mul_nonneg (Nat.cast_nonneg _) hlo0) k) (Real.log_natCast_nonneg r.p)
  have hlog0 : 0 ≤ Real.log r.p := Real.log_natCast_nonneg r.p
  have hlogpow0 : 0 ≤ Real.log ((r.p ^ (r.k + 1) : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have h := mul_le_mul hterm hpower huR (mul_nonneg hlog0 (pow_nonneg hlogpow0 k))
  simpa only [quarterMangoldtMoment, checked_row_mangoldt_eq_log hc, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_natCast, Rat.cast_add, Rat.cast_one] using h

/-- Check nonnegative rational lower power endpoints against matching rows.
The Boolean list check rejects unequal lengths and is used by separate
finite certificates for the reflected Euler lower moments. -/
def quarterMomentLowerCheck : List EulerCenterRow → List ℚ → Bool
  | [], [] => true
  | r :: rows, u :: us =>
    decide (0 ≤ r.lo) && decide (0 ≤ u) &&
      AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck (r.p ^ (r.k + 1) : ℕ) u 1 79 50 &&
      quarterMomentLowerCheck rows us
  | _, _ => false

/-- A successful lower endpoint check provides the rowwise conditions needed
for the finite moment comparison. The proof follows the two aligned lists. -/
theorem quarter_moment_lower_check_sound {rows : List EulerCenterRow} {us : List ℚ}
    (hc : quarterMomentLowerCheck rows us = true) :
    List.Forall₂
      (fun r u ↦
        0 ≤ r.lo ∧
          0 ≤ u ∧
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck (r.p ^ (r.k + 1) : ℕ) u 1 79
              50 =
            true)
      rows us := by
  induction rows generalizing us with
  | nil =>
    cases us with
    | nil => exact List.Forall₂.nil
    | cons u us => simp only [quarterMomentLowerCheck, Bool.false_eq_true] at hc
  | cons r rows ih =>
    cases us with
    | nil => simp only [quarterMomentLowerCheck, Bool.false_eq_true] at hc
    | cons u us =>
      have h := Bool.and_eq_true_iff.mp hc
      have h' := Bool.and_eq_true_iff.mp h.1
      have h'' := Bool.and_eq_true_iff.mp h'.1
      exact List.Forall₂.cons ⟨of_decide_eq_true h''.1, of_decide_eq_true h''.2, h'.2⟩ (ih h.2)

/-- Independently checked lower endpoints bound the sum of moment rows.
The row list and endpoint list must have the same length. -/
theorem quarter_moment_rows_lower {rows : List EulerCenterRow} {us : List ℚ} (k : ℕ)
    (hc : rows.all eulerCenterRowCheck = true)
    (hu :
      List.Forall₂
        (fun r u ↦
          0 ≤ r.lo ∧
            0 ≤ u ∧
            AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck (r.p ^ (r.k + 1) : ℕ) u 1 79
                50 =
              true)
        rows us) :
    (((List.zipWith (fun r u ↦ r.lo * (((r.k + 1 : ℕ) : ℚ) * r.lo) ^ k * u) rows us).sum : ℚ) : ℝ) ≤
      (rows.map (fun r ↦ quarterMangoldtMoment k (r.p ^ (r.k + 1)))).sum := by
  induction hu with
  | nil => simp only [List.zipWith_nil_left, List.sum_nil, Rat.cast_zero, List.map_nil, le_refl]
  | @cons r u rows us hrow htail
    ih =>
    have hc' := Bool.and_eq_true_iff.mp hc
    have h := quarter_moment_row_lower r hc'.1 k hrow.2.1 hrow.2.2 hrow.1
    simpa only [List.zipWith_cons_cons, List.sum_cons, Rat.cast_add, List.map_cons] using
      add_le_add h (ih hc'.2)

/-- Checked prime-power rows supply a lower bound for the finite moment
prefix. The exact support identity excludes every non-prime-power index. -/
theorem quarter_moment_prefix_lower {B : ℕ} (hB : B ≤ 50000) (us : List ℚ) (k : ℕ)
    (hu :
      List.Forall₂
        (fun r u ↦
          0 ≤ r.lo ∧
            0 ≤ u ∧
            AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck (r.p ^ (r.k + 1) : ℕ) u 1 79
                50 =
              true)
        (centerRowsBelow B) us) :
    (((List.zipWith (fun r u ↦ r.lo * (((r.k + 1 : ℕ) : ℚ) * r.lo) ^ k * u) (centerRowsBelow B)
              us).sum :
          ℚ) :
        ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 B, quarterMangoldtMoment k n := by
  have hz : ∀ n, ¬IsPrimePow n → quarterMangoldtMoment k n = 0 := by
    intro n hn
    simp only [quarterMangoldtMoment, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn, zero_mul]
  rw [centerRowsBelow_sum _ hz hB]
  exact quarter_moment_rows_lower k (centerRowsBelow_check B) hu

end PseudoPrime.PrimeTestBounds.MillerRabin
