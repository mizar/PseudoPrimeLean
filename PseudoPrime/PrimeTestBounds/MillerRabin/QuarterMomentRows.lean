/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterReflectedMoments
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowArithmetic
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerCutoffRows
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.TruncatedEulerCertificates3

/-! # Finite Mangoldt moment row certificates -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A checked prime-power row and a rational upper power endpoint bound any
nonnegative logarithmic Mangoldt moment. The existing row provides both the
prime-base logarithm and the prime-power identity. -/
theorem quarter_moment_row_upper (r : EulerCenterRow) (hc : eulerCenterRowCheck r = true) (k : ℕ)
    {u : ℚ}
    (hu :
      AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck (r.p ^ (r.k + 1) : ℕ) 0 u 79 50 =
        true) :
    quarterMangoldtMoment k (r.p ^ (r.k + 1)) ≤
      ((r.hi * ((r.k + 1 : ℕ) * r.hi) ^ k * u : ℚ) : ℝ) := by
  have hlog := (checked_row_log_bounds hc).2
  have hlog0 : 0 ≤ Real.log r.p := Real.log_natCast_nonneg r.p
  have hhi0 : (0 : ℝ) ≤ r.hi := hlog0.trans hlog
  have hmul := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (r.k + 1) : (0 : ℝ) ≤ (r.k + 1 : ℕ))
  have hpower := (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound hu).2
  norm_num only [Rat.cast_natCast] at hpower
  have hbase : 0 ≤ Real.log ((r.p ^ (r.k + 1) : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have hlogpow : Real.log ((r.p ^ (r.k + 1) : ℕ) : ℝ) ≤ (r.k + 1 : ℕ) * (r.hi : ℝ) := by
    simpa only [Nat.cast_pow, Real.log_pow, Nat.cast_add, Nat.cast_one] using hmul
  have hterm := mul_le_mul hlog (pow_le_pow_left₀ hbase hlogpow k) (pow_nonneg hbase k) hhi0
  have hp0 : 0 ≤ ((r.p ^ (r.k + 1) : ℕ) : ℝ) ^ (-(79 / 50 : ℝ)) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hupper0 : 0 ≤ (r.hi : ℝ) * ((r.k + 1 : ℕ) * (r.hi : ℝ)) ^ k :=
    mul_nonneg hhi0 (pow_nonneg (mul_nonneg (Nat.cast_nonneg _) hhi0) k)
  have h := mul_le_mul hterm hpower hp0 hupper0
  simpa only [quarterMangoldtMoment, checked_row_mangoldt_eq_log hc, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_natCast, Rat.cast_add, Rat.cast_one] using h

/-- Check a list of rational power endpoints against the corresponding
prime-power rows. Unequal list lengths are rejected. -/
def quarterMomentPowerCheck : List EulerCenterRow → List ℚ → Bool
  | [], [] => true
  | r :: rows, u :: us =>
    AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck (r.p ^ (r.k + 1) : ℕ) 0 u 79 50 &&
      quarterMomentPowerCheck rows us
  | _, _ => false

/-- A successful list check supplies all rowwise rational power certificates. -/
theorem quarter_moment_power_check_sound {rows : List EulerCenterRow} {us : List ℚ}
    (hc : quarterMomentPowerCheck rows us = true) :
    List.Forall₂
      (fun r u ↦
        AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck (r.p ^ (r.k + 1) : ℕ) 0 u 79 50 =
          true)
      rows us := by
  induction rows generalizing us with
  | nil =>
    cases us with
    | nil => exact List.Forall₂.nil
    | cons u us => simp only [quarterMomentPowerCheck, Bool.false_eq_true] at hc
  | cons r rows ih =>
    cases us with
    | nil => simp only [quarterMomentPowerCheck, Bool.false_eq_true] at hc
    | cons u us =>
      have h := Bool.and_eq_true_iff.mp hc
      exact List.Forall₂.cons h.1 (ih h.2)

/-- The checked row bounds combine over two aligned lists without repeating
the prime-power row certificates. The second list contains power endpoints. -/
theorem quarter_moment_rows_upper {rows : List EulerCenterRow} {us : List ℚ} (k : ℕ)
    (hc : rows.all eulerCenterRowCheck = true)
    (hu :
      List.Forall₂
        (fun r u ↦
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck (r.p ^ (r.k + 1) : ℕ) 0 u 79
              50 =
            true)
        rows us) :
    (rows.map (fun r ↦ quarterMangoldtMoment k (r.p ^ (r.k + 1)))).sum ≤
      (((List.zipWith (fun r u ↦ r.hi * (((r.k + 1 : ℕ) : ℚ) * r.hi) ^ k * u) rows us).sum : ℚ) :
        ℝ) := by
  induction hu with
  | nil => simp only [List.zipWith_nil_left, List.sum_nil, Rat.cast_zero, List.map_nil, le_refl]
  | @cons r u rows us hrow htail
    ih =>
    have hc' := Bool.and_eq_true_iff.mp hc
    have h := quarter_moment_row_upper r hc'.1 k hrow
    simpa only [List.zipWith_cons_cons, List.sum_cons, Rat.cast_add, List.map_cons] using
      add_le_add h (ih hc'.2)

/-- Exact prime-power support and independently checked endpoints bound the
finite Mangoldt moment prefix at any cutoff through 50000. -/
theorem quarter_moment_prefix_upper {B : ℕ} (hB : B ≤ 50000) (us : List ℚ) (k : ℕ)
    (hu :
      List.Forall₂
        (fun r u ↦
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck (r.p ^ (r.k + 1) : ℕ) 0 u 79
              50 =
            true)
        (centerRowsBelow B) us) :
    (∑ n ∈ Finset.Ioc 0 B, quarterMangoldtMoment k n) ≤
      (((List.zipWith (fun r u ↦ r.hi * (((r.k + 1 : ℕ) : ℚ) * r.hi) ^ k * u) (centerRowsBelow B)
              us).sum :
          ℚ) :
        ℝ) := by
  have hz : ∀ n, ¬IsPrimePow n → quarterMangoldtMoment k n = 0 := by
    intro n hn
    simp only [quarterMangoldtMoment, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn, zero_mul]
  rw [centerRowsBelow_sum _ hz hB]
  exact quarter_moment_rows_upper k (centerRowsBelow_check B) hu

end PseudoPrime.PrimeTestBounds.MillerRabin
