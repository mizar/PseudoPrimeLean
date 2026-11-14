/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridLogArithmetic

/-! # Shared logarithm checks for the low-zero endpoint calculation -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Check that the existing rational logarithm approximation is within
`1/200000000` of the exact logarithm. The Taylor interval is checked by
exact rational arithmetic and can be reused for all 58 endpoint heights. -/
def endpointLogCheck (n : ℕ) : Bool :=
  decide (0 ≤ gridLogApprox n ∧ gridLogApprox n ≤ 7) &&
    Analysis.rationalLogIntervalCheck n (Nat.log2 n + 1) 32 (gridLogApprox n - 1 / 200000000)
      (gridLogApprox n + 1 / 200000000)

set_option maxRecDepth 4096 in
-- The finite decision traverses 128 rational logarithm certificates.
set_option maxHeartbeats 0 in
-- The kernel verifies every Taylor interval without a numerical table.
/-- The strengthened logarithm check succeeds for every integer from 1
through 128, covering the finite Euler–Maclaurin approximation. -/
theorem endpoint_log_checks : ∀ n ∈ Finset.Icc (1 : ℕ) 128, endpointLogCheck n = true := by
  have h : ∀ i : Fin 128, endpointLogCheck (1 + i.val) = true := by decide +kernel
  intro n hn
  have hn1 := (Finset.mem_Icc.mp hn).1
  have hn2 := (Finset.mem_Icc.mp hn).2
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn1
  have hlt : n - 1 < 128 := lt_of_lt_of_le (Nat.sub_lt hnpos Nat.zero_lt_one) hn2
  have heq : 1 + (n - 1) = n := by rw [Nat.add_comm, Nat.sub_add_cancel hn1]
  simpa only [Fin.val_mk, heq] using h ⟨n - 1, hlt⟩

/-- A successful strengthened check bounds the error between `log n` and
its shared rational approximation by `1/200000000`. -/
theorem endpoint_log_error (n : ℕ) (h : endpointLogCheck n = true) :
    |Real.log n - (gridLogApprox n : ℝ)| ≤ 1 / 200000000 := by
  have hh := Bool.and_eq_true_iff.mp h
  have hl := Analysis.rationalLogIntervalCheck_sound hh.2
  simp only [Rat.cast_natCast, Rat.cast_sub, Rat.cast_add, Rat.cast_div, Rat.cast_one,
    Rat.cast_ofNat] at hl
  apply abs_le.mpr
  constructor <;> linarith only [hl.1, hl.2]

/-- A successful endpoint logarithm check also places the rational value in
`[0,7]`, the range required by the rounded power evaluator. -/
theorem endpoint_log_range (n : ℕ) (h : endpointLogCheck n = true) :
    0 ≤ gridLogApprox n ∧ gridLogApprox n ≤ 7 := by
  exact of_decide_eq_true (Bool.and_eq_true_iff.mp h).1

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
