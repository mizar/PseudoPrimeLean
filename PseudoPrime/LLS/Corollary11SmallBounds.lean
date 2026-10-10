/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Corollary11Small
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! Logarithmic bounds used to convert the finite Jacobi certificates into
the strict bound in LLS Corollary 1.1. -/

@[expose] public section

namespace PseudoPrime.LLS

-- set_option linter.style.setOption false
-- set_option profiler true

/-- The logarithm of 6 splits into the two logarithms with explicit numerical estimates. -/
theorem log_six_eq : Real.log 6 = Real.log 2 + Real.log 3 := by
  have h6 := Real.log_mul (by norm_num only : (2 : ℝ) ≠ 0) (by norm_num only : (3 : ℝ) ≠ 0)
  norm_num only at h6
  exact h6

/-- For a modulus at least 5, the logarithmic square exceeds 2.
The explicit lower estimate for `log 5` supplies the numerical margin. -/
theorem two_lt_log_sq {q : ℕ} (hq : 5 ≤ q) : 2 < (Real.log q) ^ 2 := by
  have hlog : Real.log 5 ≤ Real.log q := Real.log_le_log (by norm_num only) (Nat.cast_le.mpr hq)
  nlinarith only [hlog, Real.log_five_gt_d9, sq_nonneg (Real.log q - 1.6)]

/-- For a modulus at least 7, the logarithmic square exceeds 3.
The identity `log 6 = log 2 + log 3` supplies the numerical margin. -/
theorem three_lt_log_sq {q : ℕ} (hq : 7 ≤ q) : 3 < (Real.log q) ^ 2 := by
  have hlog : Real.log 6 ≤ Real.log q :=
    Real.log_le_log (by norm_num only) (Nat.cast_le.mpr (Nat.le_trans (by decide : 6 ≤ 7) hq))
  nlinarith only [hlog, log_six_eq, Real.log_two_gt_d9, Real.log_three_gt_d9,
    sq_nonneg (Real.log q - 1.78)]

/-- For a modulus at least 23, the logarithmic square exceeds 7.
Comparison with `log 16 = 4 * log 2` supplies the numerical margin. -/
theorem seven_lt_log_sq {q : ℕ} (hq : 23 ≤ q) : 7 < (Real.log q) ^ 2 := by
  have hlog : Real.log 16 ≤ Real.log q :=
    Real.log_le_log (by norm_num only) (Nat.cast_le.mpr (Nat.le_trans (by decide : 16 ≤ 23) hq))
  have hb := Real.log_pow (2 : ℝ) 4
  norm_num only at hb
  nlinarith only [hlog, hb, Real.log_two_gt_d9, sq_nonneg (Real.log q - 2.76)]

/-- For a modulus at least 311, the logarithmic square exceeds 17.
Comparison with `log 256 = 8 * log 2` supplies the numerical margin. -/
theorem seventeen_lt_log_sq {q : ℕ} (hq : 311 ≤ q) : 17 < (Real.log q) ^ 2 := by
  have hlog : Real.log 256 ≤ Real.log q :=
    Real.log_le_log (by norm_num only) (Nat.cast_le.mpr (Nat.le_trans (by decide : 256 ≤ 311) hq))
  have hb := Real.log_pow (2 : ℝ) 8
  norm_num only at hb
  nlinarith only [hlog, hb, Real.log_two_gt_d9, sq_nonneg (Real.log q - 5.52)]

/-- A natural witness below its interval cap satisfies the strict logarithmic-square bound
for every modulus at least 5. This connects the finite certificates to the paper bound. -/
theorem smallNonresidue_lt_log_sq {q n : ℕ} (hq : 5 ≤ q) (hn : n < smallNonresidueCap q) :
    (n : ℝ) < (Real.log q) ^ 2 := by
  by_cases h7 : q < 7
  · simp only [smallNonresidueCap, ite_eq_left h7] at hn
    exact lt_of_le_of_lt (Nat.cast_le.mpr (Nat.le_of_lt_succ hn)) (two_lt_log_sq hq)
  by_cases h23 : q < 23
  · simp only [smallNonresidueCap, ite_eq_right h7, ite_eq_left h23] at hn
    exact
      lt_of_le_of_lt (Nat.cast_le.mpr (Nat.le_of_lt_succ hn))
        (three_lt_log_sq (Nat.le_of_not_gt h7))
  by_cases h311 : q < 311
  · simp only [smallNonresidueCap, ite_eq_right h7, ite_eq_right h23, ite_eq_left h311] at hn
    exact
      lt_of_le_of_lt (Nat.cast_le.mpr (Nat.le_of_lt_succ hn))
        (seven_lt_log_sq (Nat.le_of_not_gt h23))
  simp only [smallNonresidueCap, ite_eq_right h7, ite_eq_right h23, ite_eq_right h311] at hn
  exact
    lt_of_le_of_lt (Nat.cast_le.mpr (Nat.le_of_lt_succ hn))
      (seventeen_lt_log_sq (Nat.le_of_not_gt h311))

/-- Every prime between 5 and 2999 has a positive nonsquare strictly below its
logarithmic square. The exhaustive Jacobi certificate supplies the witness. -/
theorem exists_positive_nonsquare_lt_log_sq_small {q : ℕ} (hp : q.Prime) (h5 : 5 ≤ q)
    (hq : q < 3000) : ∃ n : ℕ, 0 < n ∧ ¬IsSquare (n : ZMod q) ∧ (n : ℝ) < (Real.log q) ^ 2 :=
  Exists.elim (exists_smallNonresidue hp h5 hq)
    (fun n hn ↦
      ⟨n, hn.1,
        Eq.mp (congrArg (fun a : ZMod q ↦ ¬IsSquare a) (Int.cast_natCast n))
          (ZMod.nonsquare_of_jacobiSym_eq_neg_one hn.2.2),
        smallNonresidue_lt_log_sq h5 hn.2.1⟩)

end PseudoPrime.LLS
