/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The greatest odd prime below a real cutoff, and basic log positivity

This file defines the greatest odd prime not exceeding a real cutoff, with value `0` when
there is none, and proves its floor and comparison bounds. It also proves positivity of
`log q` and `loglog q` for natural `q ≥ 3000`.
-/

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- The greatest odd prime not exceeding a real cutoff, or `0` if the set is empty. -/
noncomputable def greatestOddPrimeLE (R : ℝ) : ℕ := by
  classical exact Nat.findGreatest (fun p => p.Prime ∧ Odd p) ⌊R⌋₊

/-- Every odd prime below the real cutoff is below `greatestOddPrimeLE`. -/
theorem le_greatestOddPrimeLE {p : ℕ} {R : ℝ} (hp : p.Prime) (hpodd : Odd p) (hpR : (p : ℝ) ≤ R) :
    p ≤ greatestOddPrimeLE R := by
  classical
  unfold greatestOddPrimeLE
  exact Nat.le_findGreatest (Nat.le_floor hpR) ⟨hp, hpodd⟩

/-- The greatest odd-prime cutoff does not exceed its natural floor. -/
theorem greatestOddPrimeLE_le_floor (R : ℝ) : greatestOddPrimeLE R ≤ ⌊R⌋₊ := by
  classical
  unfold greatestOddPrimeLE
  exact Nat.findGreatest_le _

/-- A nonnegative real cutoff bounds the cast of its greatest odd prime. -/
theorem greatestOddPrimeLE_cast_le {R : ℝ} (hR : 0 ≤ R) : (greatestOddPrimeLE R : ℝ) ≤ R := by
  have hfloor : (greatestOddPrimeLE R : ℝ) ≤ (⌊R⌋₊ : ℝ) := by
    exact_mod_cast greatestOddPrimeLE_le_floor R
  exact hfloor.trans (Nat.floor_le hR)

/-- For a natural `q ≥ 3000`, both `log q` and `loglog q` are positive. -/
theorem log_log_pos_of_le {q : ℕ} (hq : 3000 ≤ q) :
    0 < Real.log (q : ℝ) ∧ 0 < Real.log (Real.log (q : ℝ)) := by
  have hqreal : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  have hx : 0 < Real.log (q : ℝ) := Real.log_pos hqreal
  have hone : (1 : ℝ) < Real.log (q : ℝ) := by
    have hlog3000 : (1 : ℝ) < Real.log 3000 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num only)]
      exact Real.exp_one_lt_three.trans (by norm_num only)
    exact hlog3000.trans_le (Real.log_le_log (by norm_num only) (by exact_mod_cast hq))
  exact ⟨hx, Real.log_pos hone⟩

end PseudoPrime.AnalyticNumberTheory.Arithmetic
