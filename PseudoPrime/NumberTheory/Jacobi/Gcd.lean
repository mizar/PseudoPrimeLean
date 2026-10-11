/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Jacobi.Fuel
public import PseudoPrime.NumberTheory.Jacobi.Sign

/-!
# Simultaneous Jacobi and gcd rounds

The state stores denominator, numerator and accumulated sign. Odd denominators
permit removing numerator powers of two while preserving the exact gcd.
A zero accumulated sign does not stop the gcd trajectory.
-/

@[expose] public section

namespace PseudoPrime.NumberTheory.Jacobi.Gcd

/-- State of the shared Jacobi-and-gcd trajectory.
`c` is the denominator, `m` the numerator, and `sign` an arbitrary accumulated integer.
Correctness requires odd `c`; stopping is determined solely by `m = 0`.
The state represents `sign * jacobiSym m c` and `Nat.gcd c m`. -/
structure State where
  c : ℕ
  m : ℕ
  sign : ℤ

/-- One shared round, retaining a terminal state unchanged.
For nonzero `m`, one maximal-power decomposition supplies exponent and odd quotient.
The factor-two and reciprocity signs update the coefficient; swapping and taking the
remainder update the two gcd operands. Sign zero still performs the full arithmetic round. -/
def step (st : State) : State :=
  if st.m = 0 then st
  else
    let (e, d) := Nat.maxPowDvdDiv 2 st.m
    let factor : ℤ := twoPowerSign st.c e * (if d % 4 = 3 ∧ st.c % 4 = 3 then -1 else 1)
    ⟨d, st.c % d, st.sign * factor⟩

/-- Run at most the supplied number of batched rounds.
Terminal states return immediately, so excess fuel incurs no further rounds.
No gcd or Jacobi specification is evaluated by this execution procedure. -/
def run : ℕ → State → State
  | 0, st => st
  | fuel + 1, st => if st.m = 0 then st else run fuel (step st)

/-- Extract a symbol and exact final denominator when the fuel reaches a terminal state.
`none` means exhaustion; a successful zero symbol is distinct and retains its gcd.
Termination is free even at fuel zero. -/
def runFuel (fuel : ℕ) (st : State) : Option (ℤ × ℕ) :=
  let out := run fuel st
  if out.m = 0 then some (if out.c = 1 then out.sign else 0, out.c) else none

/-- An odd denominator remains odd after a shared round.
A terminal state is unchanged; otherwise maximal two-power extraction supplies an odd quotient.
This preserves the domain on which the symbol and gcd step identities are valid. -/
theorem step_odd (st : State) (hc : Odd st.c) : Odd (step st).c := by
  exact
    if hm : st.m = 0 then (show Odd (step st).c by simpa only [step, hm, ite_true] using hc)
    else
      (show Odd (step st).c by
        simpa only [step, hm, ite_false, Nat.snd_maxPowDvdDiv] using
          Nat.odd_iff.mpr (TwoAdic.oddPart_odd st.m hm))

/-- A shared round preserves the exact gcd when its denominator is odd.
Remove the coprime two-power, then apply Euclidean remainder invariance and symmetry.
No coprimality between the two operands is assumed. -/
theorem step_gcd (st : State) (hc : Odd st.c) :
    Nat.gcd (step st).c (step st).m = Nat.gcd st.c st.m := by
  exact
    if hm : st.m = 0 then
      (show Nat.gcd (step st).c (step st).m = _ by simp only [step, hm, ite_true])
    else
      (show Nat.gcd (step st).c (step st).m = _ by
        simpa only [step, hm, ite_false, Nat.snd_maxPowDvdDiv] using
          (Nat.gcd_comm (Nat.divMaxPow st.m 2) (st.c % Nat.divMaxPow st.m 2)).trans
            ((Nat.gcd_rec (Nat.divMaxPow st.m 2) st.c).symm.trans
              ((Nat.gcd_comm _ _).trans (TwoAdic.gcd_oddPart_right st.c st.m hc))))

/-- A shared round preserves the accumulated Jacobi value at every odd denominator.
Factor-two removal, reciprocity and remainder invariance give the batched sign identity.
The accumulated sign may be zero; the gcd trajectory still continues in that case. -/
theorem step_value (st : State) (hc : Odd st.c) :
    (step st).sign * jacobiSym ((step st).m : ℤ) (step st).c =
      st.sign * jacobiSym (st.m : ℤ) st.c := by
  exact
    if hm : st.m = 0 then
      (show (step st).sign * jacobiSym ((step st).m : ℤ) (step st).c = _ by
        simp only [step, hm, ite_true])
    else
      (show (step st).sign * jacobiSym ((step st).m : ℤ) (step st).c = _
        by
        simp only [step, hm, ite_false, Nat.snd_maxPowDvdDiv, Nat.fst_maxPowDvdDiv, twoPowerSign_eq]
        change
          (st.sign * jacobiRoundSign st.m st.c) *
              jacobiSym ((st.c % Nat.divMaxPow st.m 2 : ℕ) : ℤ) (Nat.divMaxPow st.m 2) =
            _
        rw [mul_assoc, jacobiRoundSign_mul st.m st.c hm (Nat.odd_iff.mp hc)])

/-- Every caller budget preserves oddness, exact gcd and accumulated Jacobi value.
Induction applies the three shared-step identities; termination retains the state.
The result holds independently of whether the budget suffices for completion. -/
theorem run_invariants (fuel : ℕ) (st : State) (hc : Odd st.c) :
    Odd (run fuel st).c ∧
      Nat.gcd (run fuel st).c (run fuel st).m = Nat.gcd st.c st.m ∧
      (run fuel st).sign * jacobiSym ((run fuel st).m : ℤ) (run fuel st).c =
        st.sign * jacobiSym (st.m : ℤ) st.c := by
  induction fuel generalizing st with
  | zero => exact ⟨hc, rfl, rfl⟩
  | succ fuel ih =>
    exact
      if hm : st.m = 0 then
        (show _ by
          simpa only [run, hm, ite_true] using
            And.intro hc
              (And.intro (Eq.refl (Nat.gcd st.c st.m))
                (Eq.refl (st.sign * jacobiSym (st.m : ℤ) st.c))))
      else
        (show _ by
          simpa only [run, hm, ite_false] using
            And.intro (ih (step st) (step_odd st hc)).1
              (And.intro ((ih (step st) (step_odd st hc)).2.1.trans (step_gcd st hc))
                ((ih (step st) (step_odd st hc)).2.2.trans (step_value st hc))))

/-- A nonterminal result supplies the abstract divisor-reducing Euclidean trajectory.
At each round the positive odd quotient is at most the previous numerator.
No parity assumption is required for this termination interface. -/
theorem run_nonterminal_divisionNonstop (fuel : ℕ) (st : State) (h : (run fuel st).m ≠ 0) :
    Euclid.divisionNonstop fuel st.c st.m := by
  induction fuel generalizing st with
  | zero => exact h
  | succ fuel ih =>
    exact
      if hm : st.m = 0 then
        (show _ by
          simp only [run, hm, ite_true] at h; exact False.elim (h rfl))
      else
        (show _ by
          simp only [run, hm, ite_false] at h
          exact
            ⟨Nat.divMaxPow st.m 2, TwoAdic.oddPart_pos st.m hm, TwoAdic.oddPart_le st.m hm,
              (show Euclid.divisionNonstop fuel (Nat.divMaxPow st.m 2) (st.c % Nat.divMaxPow st.m 2)
                by simpa only [step, hm, ite_false, Nat.snd_maxPowDvdDiv] using ih (step st) h)⟩)

/-- An odd terminal denominator gives Jacobi value one exactly at denominator one.
Specialize the certified reference recursion at numerator zero.
This identifies the symbol returned by a terminal shared state. -/
theorem terminal_value (c : ℕ) (hc : Odd c) : jacobiSym (0 : ℤ) c = (if c = 1 then 1 else 0) := by
  have h := jacobiNat_eq 0 c (Nat.odd_iff.mp hc)
  rw [jacobiNat] at h
  simp only [Nat.cast_zero, ↓reduceDIte] at h
  exact h.symm

/-- Every successful caller budget returns the exact symbol and gcd at an odd denominator.
Use the arbitrary-budget invariants and the terminal symbol identity.
No fuel lower bound and no coprimality assumption are required. -/
theorem runFuel_sound (fuel : ℕ) (st : State) (hc : Odd st.c) {z : ℤ} {g : ℕ}
    (h : runFuel fuel st = some (z, g)) :
    z = st.sign * jacobiSym (st.m : ℤ) st.c ∧ g = Nat.gcd st.c st.m := by
  have hi := run_invariants fuel st hc
  dsimp only [runFuel] at h
  exact
    if ht : (run fuel st).m = 0 then
      (show _ by
        rw [ite_eq_left ht] at h
        have hp := Prod.mk.inj (Option.some.inj h)
        have hv := hi.2.2
        rw [ht, Nat.cast_zero, terminal_value _ hi.1, mul_ite, mul_one, mul_zero] at hv
        exact
          ⟨hp.1.symm.trans hv,
            hp.2.symm.trans
              (show (run fuel st).c = Nat.gcd st.c st.m by
                simpa only [ht, Nat.gcd_zero_right] using hi.2.1)⟩)
    else
      (show _ by
        rw [ite_eq_right ht] at h; cases h)

/-- Projecting the shared kernel gives the old batched symbol computation at every budget.
The equality follows from the recursive updates, without requiring an odd denominator.
Thus both execution procedures exhaust fuel together, even outside the Jacobi correctness domain. -/
theorem runFuel_fst (fuel : ℕ) (st : State) :
    (runFuel fuel st).map Prod.fst =
      (jacobiNatBatchedFuel fuel st.m st.c).map (fun j ↦ st.sign * j) := by
  induction fuel generalizing st with
  | zero =>
    by_cases hm : st.m = 0 <;>
      simp only [runFuel, run, jacobiNatBatchedFuel, hm, ite_true, ite_false, Option.map_some,
        Option.map_none, mul_ite, mul_one, mul_zero]
    rfl
  | succ fuel ih =>
    exact
      if hm : st.m = 0 then
        (show _ by
          simp only [runFuel, run, jacobiNatBatchedFuel, hm, ite_true, Option.map_some, mul_ite,
            mul_one, mul_zero])
      else
        (show _ by
          rw [runFuel, run, ite_eq_right hm]
          change (runFuel fuel (step st)).map Prod.fst = _
          rw [ih]
          simp only [jacobiNatBatchedFuel, hm, ite_false, Option.map_map, step,
            Nat.fst_maxPowDvdDiv, Nat.snd_maxPowDvdDiv, twoPowerSign_eq, jacobiRoundSign,
            Function.comp_def, mul_assoc]
          rfl)

/-- Exhaustion yields a divisor-reducing nonterminal trajectory at the supplied budget.
A terminal shared state would return `some`; exhaustion therefore gives a nonterminal result.
Apply the shared run trajectory directly, without using the reference symbol recursion.
No oddness assumption is needed for this termination interface. -/
theorem runFuel_none_nonstop (fuel : ℕ) (st : State) (h : runFuel fuel st = none) :
    Euclid.divisionNonstop fuel st.c st.m := by
  apply run_nonterminal_divisionNonstop fuel st
  intro hm
  simp only [runFuel, hm, ite_true, Option.some_ne_none] at h

/-- Any budget at least the Fibonacci step bound prevents exhaustion.
A nonterminal result would give a forbidden divisor-reducing trajectory.
The termination statement does not require an odd denominator. -/
theorem runFuel_ne_none (fuel : ℕ) (st : State) (hf : Euclid.stepBound st.m ≤ fuel) :
    runFuel fuel st ≠ none := by
  intro h
  exact
    Euclid.not_divisionNonstop_of_lt_fib st.c st.m fuel
      ((Euclid.lt_fib_stepBound st.m).trans_le (Nat.fib_mono (Nat.add_le_add_right hf 2)))
      (runFuel_none_nonstop fuel st h)

/-- A sufficient budget returns the accumulated symbol and exact gcd.
Termination excludes `none`, and arbitrary-budget soundness identifies both components.
This is the total-result interface used by input normalization. -/
theorem runFuel_eq (fuel : ℕ) (st : State) (hc : Odd st.c) (hf : Euclid.stepBound st.m ≤ fuel) :
    runFuel fuel st = some (st.sign * jacobiSym (st.m : ℤ) st.c, Nat.gcd st.c st.m) := by
  cases he : runFuel fuel st with
  | none => exact False.elim (runFuel_ne_none fuel st hf he)
  | some p =>
    have h := runFuel_sound fuel st hc he
    exact congrArg some (Prod.ext h.1 h.2)

/-- Remainder normalization preserves the symbol and gcd at an odd denominator.
The Fibonacci budget for the normalized numerator suffices; remainder identities recover
both original values. The accumulated coefficient may be zero. -/
theorem runFuel_normalized (A N : ℕ) (s : ℤ) (hN : Odd N) :
    runFuel (Euclid.stepBound (A % N)) ⟨N, A % N, s⟩ =
      some (s * jacobiSym (A : ℤ) N, Nat.gcd A N) := by
  rw [runFuel_eq (Euclid.stepBound (A % N)) ⟨N, A % N, s⟩ hN (Nat.le_refl _)]
  exact
    congrArg some
      (Prod.ext
        (show s * jacobiSym ((A % N : ℕ) : ℤ) N = s * jacobiSym (A : ℤ) N by
          rw [Int.natCast_emod, ← jacobiSym.mod_left])
        ((Nat.gcd_comm N (A % N)).trans ((Nat.gcd_rec N A).symm.trans (Nat.gcd_comm N A))))

/-- The binary-logarithm budget is sufficient for every state, without oddness assumptions.
The Fibonacci bound lies below this budget; the existing termination theorem excludes failure.
This offers a simple caller budget independently of the tighter executable Fibonacci bound. -/
theorem runFuel_ne_none_log2 (st : State) : runFuel (2 * (st.m + 1).log2 + 1) st ≠ none := by
  exact runFuel_ne_none _ st (Euclid.stepBound_le_log2 st.m)

/-- The normalized Fibonacci budget is bounded using the positive denominator alone.
The remainder is at most `N - 1`; monotonicity and the binary-logarithm bound apply there.
This bounds batched rounds, excluding the initial remainder and two-adic extraction costs. -/
theorem normalizedFuel_le_log2 (A N : ℕ) (hN : 0 < N) :
    Euclid.stepBound (A % N) ≤ 2 * N.log2 + 1 := by
  have h :=
    (Euclid.stepBound_mono (Nat.le_pred_of_lt (Nat.mod_lt A hN))).trans
      (Euclid.stepBound_le_log2 (N - 1))
  rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hN)] at h
  exact h

end PseudoPrime.NumberTheory.Jacobi.Gcd
