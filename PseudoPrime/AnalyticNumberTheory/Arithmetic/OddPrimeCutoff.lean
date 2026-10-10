/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The greatest odd prime below a real cutoff, and basic log positivity

This file defines the greatest odd prime not exceeding a real cutoff, with value `0` when
there is none, and proves its floor and comparison bounds. It also proves positivity of
`log q` and `loglog q` for natural `q ≥ 3000`.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For real `R`, the greatest odd prime at most its natural floor, returning zero if none
exists. For nonnegative `R` this is the greatest odd prime not exceeding `R`.
The bounded natural search supplies an odd-prime cutoff for finite arithmetic bounds. -/
noncomputable def greatestOddPrimeLE (R : ℝ) : ℕ := by
  classical exact Nat.findGreatest (fun p => p.Prime ∧ Odd p) ⌊R⌋₊

/-- If prime `p` is odd and `(p : ℝ) ≤ R`, then `p ≤ greatestOddPrimeLE R`.
The real comparison puts `p` below the natural floor and `Nat.le_findGreatest` applies.
This includes every admissible odd prime in the cutoff. -/
theorem le_greatestOddPrimeLE {p : ℕ} {R : ℝ} (hp : p.Prime) (hpodd : Odd p) (hpR : (p : ℝ) ≤ R) :
    p ≤ greatestOddPrimeLE R := by
  classical
  unfold greatestOddPrimeLE
  exact Nat.le_findGreatest (Nat.le_floor hpR) ⟨hp, hpodd⟩

/-- For every real `R`, `greatestOddPrimeLE R ≤ floor R` follows from the finite search
range. This is the natural bound used to compare the chosen cutoff with its real argument. -/
theorem greatestOddPrimeLE_le_floor (R : ℝ) : greatestOddPrimeLE R ≤ ⌊R⌋₊ := by
  classical
  unfold greatestOddPrimeLE
  exact Nat.findGreatest_le _

/-- For `R ≥ 0`, the real cast of `greatestOddPrimeLE R` is at most `R`.
Cast the finite-search bound and use `floor R ≤ R`. Nonnegativity also handles the zero
fallback value and is needed for this real bound. -/
theorem greatestOddPrimeLE_cast_le {R : ℝ} (hR : 0 ≤ R) : (greatestOddPrimeLE R : ℝ) ≤ R := by
  have hfloor : (greatestOddPrimeLE R : ℝ) ≤ (⌊R⌋₊ : ℝ) := by
    exact_mod_cast greatestOddPrimeLE_le_floor R
  exact hfloor.trans (Nat.floor_le hR)

/-- For natural `q ≥ 3000`, both `log q` and `log (log q)` are positive.
Use `exp 1 < 3 < 3000` to show `log 3000 > 1`, then monotonicity transfers this to `q`.
These signs justify multiplication and denominator cancellation in elementary factor-count bounds.
-/
theorem log_log_pos_of_le {q : ℕ} (hq : 3000 ≤ q) :
    0 < Real.log (q : ℝ) ∧ 0 < Real.log (Real.log (q : ℝ)) := by
  have hqreal : (1 : ℝ) < q := by exact_mod_cast ((by decide : 1 < 3000).trans_le hq)
  have hx : 0 < Real.log (q : ℝ) := Real.log_pos hqreal
  have hone : (1 : ℝ) < Real.log (q : ℝ) := by
    have hlog3000 : (1 : ℝ) < Real.log 3000 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num only)]
      exact Real.exp_one_lt_three.trans (by norm_num only)
    exact hlog3000.trans_le (Real.log_le_log (by norm_num only) (by exact_mod_cast hq))
  exact ⟨hx, Real.log_pos hone⟩

end PseudoPrime.AnalyticNumberTheory.Arithmetic
