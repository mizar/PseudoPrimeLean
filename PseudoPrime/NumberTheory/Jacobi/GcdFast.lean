/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Jacobi.Gcd

/-! # Fuel-free shared Jacobi and gcd execution -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Jacobi.Gcd

/-- Complete the shared trajectory without computing a fuel budget.
Each nonterminal round strictly decreases the numerator. A zero accumulated sign
still runs to completion, since the final denominator supplies the exact gcd.
The fuel-based `runFuel` remains available independently. -/
def runFast (st : State) : ℤ × ℕ :=
  if _hm : st.m = 0 then (if st.c = 1 then st.sign else 0, st.c) else runFast (step st)
termination_by st.m
decreasing_by
  simpa only [step, _hm, ite_false, Nat.snd_maxPowDvdDiv] using
    (Nat.mod_lt st.c (TwoAdic.oddPart_pos st.m _hm)).trans_le (TwoAdic.oddPart_le st.m _hm)

/-- At an odd denominator, fuel-free completion returns the accumulated symbol and gcd.
Function induction follows the decreasing numerator; each round preserves both values.
No coprimality or nonzero-sign assumption is required. -/
theorem runFast_spec (st : State) (hc : Odd st.c) :
    runFast st = (st.sign * jacobiSym (st.m : ℤ) st.c, Nat.gcd st.c st.m) := by
  induction st using runFast.induct with
  | case1 st hm =>
    rw [runFast, dite_eq_left hm]
    simp only [hm, Nat.cast_zero, terminal_value st.c hc, mul_ite, mul_one, mul_zero,
      Nat.gcd_zero_right]
  | case2 st hm ih =>
    rw [runFast, dite_eq_right hm, ih (step_odd st hc)]
    exact Prod.ext (step_value st hc) (step_gcd st hc)

/-- An initial remainder retains the original Jacobi value and gcd at an odd denominator.
Apply fuel-free correctness and the two remainder identities. This is the interface
used to restore signs and common powers of two for integer inputs. -/
theorem runFast_normalized (A N : ℕ) (s : ℤ) (hN : Odd N) :
    runFast ⟨N, A % N, s⟩ = (s * jacobiSym (A : ℤ) N, Nat.gcd A N) := by
  rw [runFast_spec _ hN]
  exact
    Prod.ext
      (show s * jacobiSym ((A % N : ℕ) : ℤ) N = s * jacobiSym (A : ℤ) N by
        rw [Int.natCast_emod, ← jacobiSym.mod_left])
      ((Nat.gcd_comm N (A % N)).trans ((Nat.gcd_rec N A).symm.trans (Nat.gcd_comm N A)))

end PseudoPrime.NumberTheory.Jacobi.Gcd
