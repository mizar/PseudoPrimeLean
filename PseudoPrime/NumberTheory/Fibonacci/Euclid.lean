/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.GCD.Basic
import PseudoPrime.NumberTheory.Fibonacci.Greatest

/-!
# Euclidean iteration and the least stopping time

The state is preserved once its second component becomes zero. Fibonacci lower bounds for
nontermination give sufficient fuel, correctness of a bounded gcd implementation, and a natural-
number binary-logarithm bound on the number of iterations.
-/

namespace PseudoPrime.NumberTheory.Euclid

/--
Perform one Euclidean update on natural inputs. If `m = 0`, preserve the terminal state;
otherwise return `(m, c % m)`. This defines stopping times and remainder invariants.
-/
def step (c m : Nat) : Nat × Nat :=
  if m = 0 then (c, 0) else (m, c % m)

/--
Perform `k` Euclidean updates from `(c, m)`. Each update applies `step`, and terminal states
remain unchanged. A zero second component indicates that the fuel was sufficient.
-/
def run : Nat → Nat → Nat → Nat × Nat
  | 0, c, m => (c, m)
  | k + 1, c, m =>
    let p := step c m;
    run k p.1 p.2

/--
With zero fuel, return the initial state. This unfolds the execution definition.
-/
@[simp]
theorem run_zero (c m : Nat) : run 0 c m = (c, m) :=
  rfl

/--
A zero second component remains terminal for all fuel values, by induction.
-/
@[simp]
theorem run_second_zero (k c : Nat) : run k c 0 = (c, 0) := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [run, step, ↓reduceIte] using ih

/--
Execution with fuel `i + j` is execution with fuel `j` from the state reached after `i` updates.
Induction on `i` proves the identity used for terminal stability.
-/
theorem run_add (i j c m : Nat) : run (i + j) c m = run j (run i c m).1 (run i c m).2 := by
  induction i generalizing c m with
  | zero => simp only [Nat.zero_add, run]
  | succ i ih => simpa only [Nat.succ_add, run] using ih (step c m).1 (step c m).2

/--
After reaching a terminal state, both components remain unchanged.
-/
theorem run_stable (c m i j : Nat) (hij : i ≤ j) (hz : (run i c m).2 = 0) :
    run j c m = run i c m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  rw [run_add, hz, run_second_zero]
  exact (Prod.ext rfl hz.symm)

/--
If execution is nonterminal at time `j`, it is nonterminal at every earlier time `i <= j`.
Terminal stability proves this fact, used in the Fibonacci induction.
-/
theorem run_nonzero_of_le (c m i j : Nat) (hij : i ≤ j) (hj : (run j c m).2 ≠ 0) :
    (run i c m).2 ≠ 0 := by
  intro hi
  exact
    hj
      (by
        rw [run_stable c m i j hij hi]; exact hi)

/--
Transfer nontermination to the state after one update.
-/
theorem run_stay_tail (c m k : Nat) (hm : m ≠ 0) (h : ∀ i, i ≤ k + 1 → (run i c m).2 ≠ 0) :
    ∀ i, i ≤ k → (run i m (c % m)).2 ≠ 0 := by
  intro i hi
  simpa only [run, step, ite_eq_right hm] using h (i + 1) (Nat.succ_le_succ hi)

/--
The initial second component provides sufficient fuel for termination.
-/
theorem run_stops_of_le (c m fuel : Nat) (h : m ≤ fuel) : (run fuel c m).2 = 0 := by
  induction fuel generalizing c m with
  | zero =>
    have hm : m = 0 := Nat.eq_zero_of_le_zero h
    subst m
    rfl
  | succ fuel ih =>
    by_cases hm : m = 0
    · subst m
      exact congrArg Prod.snd (run_second_zero (fuel + 1) c)
    · have hmod := Nat.mod_lt c (Nat.pos_of_ne_zero hm)
      simpa only [run, step, ite_eq_right hm] using
        ih m (c % m) (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hmod h))

/--
The least number of updates at which the second component becomes zero.
-/
def stoppingTime (c m : Nat) : Nat :=
  Nat.find (⟨m, run_stops_of_le c m m le_rfl⟩ : ∃ k, (run k c m).2 = 0)

/--
The second component is zero at the least stopping time, by the specification of `Nat.find`.
-/
theorem stoppingTime_spec (c m : Nat) : (run (stoppingTime c m) c m).2 = 0 := by
  unfold stoppingTime
  exact Nat.find_spec (p := fun k => (run k c m).2 = 0) _

/--
The stopping time is at most `k` exactly when execution is terminal after `k` updates. Terminal
stability and minimality connect fuel to the stopping time.
-/
theorem stoppingTime_le_iff (c m k : Nat) : stoppingTime c m ≤ k ↔ (run k c m).2 = 0 := by
  constructor
  · intro hk
    rw [run_stable c m _ k hk (stoppingTime_spec c m)]
    exact stoppingTime_spec c m
  · intro hk
    unfold stoppingTime
    exact Nat.find_min' _ hk

/--
The initial second component bounds the stopping time. This gives existence before the sharper
Fibonacci bound is derived.
-/
theorem stoppingTime_le_second (c m : Nat) : stoppingTime c m ≤ m :=
  (stoppingTime_le_iff c m m).2 (run_stops_of_le c m m le_rfl)

end PseudoPrime.NumberTheory.Euclid

namespace PseudoPrime.NumberTheory.Euclid

/--
For `m > 0` and `m <= c`, the sum of `m` and the remainder is at most `c`. The quotient is at
least one, allowing Fibonacci lower bounds to propagate backwards.
-/
theorem add_mod_le (c m : ℕ) (hm : 0 < m) (hmc : m ≤ c) : m + c % m ≤ c := by
  have hq : 1 ≤ c / m := Nat.div_pos hmc hm
  have hmul : m ≤ m * (c / m) := by simpa only [mul_one] using Nat.mul_le_mul_left m hq
  exact (Nat.add_le_add_right hmul _).trans_eq ((Nat.add_comm _ _).trans (Nat.mod_add_div c m))

/--
Nontermination after `k` updates implies that the initial second component is at least `fib (k +
2)`. If `m < c`, the first component is at least `fib (k + 3)`. Induction uses the quotient and
remainder identity; subsequent stopping bounds consume the bound on the second component.
-/
theorem fib_lower (c m k : ℕ) (h : (run k c m).2 ≠ 0) :
    Nat.fib (k + 2) ≤ m ∧ (m < c → Nat.fib (k + 3) ≤ c) := by
  induction k generalizing c m with
  | zero =>
    have hm : 0 < m := Nat.pos_of_ne_zero h
    constructor
    · simpa only [Nat.zero_add, Nat.fib_two] using Nat.succ_le_of_lt hm
    · intro hmc
      simpa only [Nat.zero_add, Nat.fib_add_two, Nat.fib_one, Nat.fib_zero, Nat.reduceAdd] using
        Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hm) hmc)
  | succ k ih =>
    have hm : m ≠ 0 := run_nonzero_of_le c m 0 (k + 1) (Nat.zero_le _) h
    have ht : (run k m (c % m)).2 ≠ 0 := by simpa only [run, step, ite_eq_right hm] using h
    have hb := ih m (c % m) ht
    have hr : c % m < m := Nat.mod_lt c (Nat.pos_of_ne_zero hm)
    constructor
    · simpa only [Nat.add_assoc] using hb.2 hr
    · intro hmc
      have hs := add_mod_le c m (Nat.pos_of_ne_zero hm) (Nat.le_of_lt hmc)
      have hf := Nat.fib_add_two (n := k + 2)
      have hsum := (Nat.add_le_add hb.1 (hb.2 hr)).trans ((Nat.add_comm (c % m) m).trans_le hs)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using hf.trans_le hsum

/--
If the second component is below `fib (k + 2)`, execution terminates within `k` updates. The
nontermination lower bound gives a contradiction, with no ordering assumption on the initial
inputs.
-/
theorem run_stops_of_lt_fib (c m k : ℕ) (h : m < Nat.fib (k + 2)) : (run k c m).2 = 0 := by
  by_contra hn
  exact (Nat.not_lt_of_ge (fib_lower c m k hn).1) h

/--
A Fibonacci threshold bounds the least stopping time.
-/
theorem stoppingTime_le_of_lt_fib (c m k : ℕ) (h : m < Nat.fib (k + 2)) : stoppingTime c m ≤ k :=
  (stoppingTime_le_iff c m k).2 (run_stops_of_lt_fib c m k h)

/--
Compute sufficient Euclidean fuel from the initial second component `m`. Subtract one from the
fast greatest Fibonacci index. Natural subtraction gives zero when `m = 0`.
-/
def stepBound (m : ℕ) : ℕ :=
  PseudoPrime.NumberTheory.Fibonacci.greatestFibBinary m - 1

/--
Transfer executable fuel computation to the mathlib greatest-index specification.
-/
theorem stepBound_eq (m : ℕ) : stepBound m = Nat.greatestFib m - 1 :=
  congrArg (fun k : ℕ ↦ k - 1) (PseudoPrime.NumberTheory.Fibonacci.greatestFibBinary_spec m)

/--
A positive second component gives positive fuel, using `fib 2 = 1`.
-/
theorem stepBound_pos (m : ℕ) (hm : 0 < m) : 0 < stepBound m := by
  have hg : 2 ≤ Nat.greatestFib m :=
    (Nat.le_greatestFib).2 (by simpa only [Nat.fib_two] using Nat.succ_le_of_lt hm)
  rw [stepBound_eq]
  exact Nat.sub_pos_iff_lt.mpr (Nat.lt_of_lt_of_le (by decide : 1 < 2) hg)

/--
The Fibonacci threshold corresponding to the computed fuel exceeds the initial second component.
Handle zero separately and use the greatest-index interval specification for positive inputs.
-/
theorem lt_fib_stepBound (m : ℕ) : m < Nat.fib (stepBound m + 2) := by
  by_cases hm : m = 0
  · subst m
    simp only [stepBound_eq, Nat.fib_pos, lt_add_iff_pos_left, add_pos_iff, tsub_pos_iff_lt,
      zero_lt_two, or_true]
  have hg : 1 ≤ Nat.greatestFib m :=
    (Nat.le_greatestFib).2
      (by simpa only [Nat.fib_one] using Nat.succ_le_of_lt (Nat.pos_of_ne_zero hm))
  have heq : Nat.greatestFib m - 1 + 2 = Nat.greatestFib m + 1 := by
    calc
      _ = (Nat.greatestFib m - 1 + 1) + 1 := by ring
      _ = _ := congrArg (fun k : ℕ ↦ k + 1) (Nat.sub_add_cancel hg)
  rw [stepBound_eq, heq]
  exact Nat.lt_fib_greatestFib_add_one m

/--
For every initial first component `c`, the stopping time is at most the computed fuel.
-/
theorem stoppingTime_le_stepBound (c m : ℕ) : stoppingTime c m ≤ stepBound m :=
  stoppingTime_le_of_lt_fib c m (stepBound m) (lt_fib_stepBound m)

/--
The computed fuel guarantees termination of the executable Euclidean iteration.
-/
theorem run_stops_stepBound (c m : ℕ) : (run (stepBound m) c m).2 = 0 :=
  (stoppingTime_le_iff c m (stepBound m)).1 (stoppingTime_le_stepBound c m)

end PseudoPrime.NumberTheory.Euclid

namespace PseudoPrime.NumberTheory.Euclid

/--
One remainder update preserves the gcd, including terminal states. This connects to correctness
of the bounded gcd implementation.
-/
theorem step_gcd (c m : ℕ) : Nat.gcd (step c m).1 (step c m).2 = Nat.gcd c m := by
  by_cases hm : m = 0
  · subst m
    rfl
  · simp only [step, ite_eq_right hm]
    exact (Nat.gcd_comm _ _).trans ((Nat.gcd_rec m c).symm.trans (Nat.gcd_comm _ _))

/--
Execution preserves the gcd for every fuel value `k`.
-/
theorem run_gcd (k c m : ℕ) : Nat.gcd (run k c m).1 (run k c m).2 = Nat.gcd c m := by
  induction k generalizing c m with
  | zero => rfl
  | succ k ih => exact (ih (step c m).1 (step c m).2).trans (step_gcd c m)

/--
Compute the gcd using Fibonacci fuel. Return the first component of the terminal state;
`gcdBounded_eq` proves agreement with the ordinary gcd.
-/
def gcdBounded (c m : ℕ) : ℕ :=
  (run (stepBound m) c m).1

/--
The bounded implementation agrees with `Nat.gcd` on all inputs. Termination makes the second
component zero, and gcd preservation gives the result.
-/
theorem gcdBounded_eq (c m : ℕ) : gcdBounded c m = Nat.gcd c m := by
  have h := run_gcd (stepBound m) c m
  rw [run_stops_stepBound, Nat.gcd_zero_right] at h
  exact h

/--
A second component below a Fibonacci threshold and sufficient fuel imply termination. This can
be used after a separate comparison with Jacobi iteration counts.
-/
theorem run_stops_of_fuel_bound (c m k fuel : ℕ) (hm : m < Nat.fib (k + 2)) (hk : k ≤ fuel) :
    (run fuel c m).2 = 0 :=
  (stoppingTime_le_iff c m fuel).1 ((stoppingTime_le_of_lt_fib c m k hm).trans hk)

end PseudoPrime.NumberTheory.Euclid

namespace PseudoPrime.NumberTheory.Euclid

/--
Fibonacci fuel is at most `2 * log2 (m + 1) + 1`. Transfer the integer logarithmic greatest-
index bound through natural subtraction.
-/
theorem stepBound_le_log2 (m : ℕ) : stepBound m ≤ 2 * (m + 1).log2 + 1 := by
  rw [stepBound_eq]
  have hs :=
    Nat.sub_le_sub_right
      (Nat.le_of_lt_succ (PseudoPrime.NumberTheory.Fibonacci.greatestFib_lt_log2 m)) 1
  exact hs.trans_eq (Nat.add_sub_cancel (2 * (m + 1).log2 + 1) 1)

/--
A natural binary-logarithm bound on the stopping time for every first component.
-/
theorem stoppingTime_le_log2 (c m : ℕ) : stoppingTime c m ≤ 2 * (m + 1).log2 + 1 :=
  (stoppingTime_le_stepBound c m).trans (stepBound_le_log2 m)

end PseudoPrime.NumberTheory.Euclid

namespace PseudoPrime.NumberTheory.Euclid

/--
The remainder of adjacent Fibonacci values is the preceding value. Indices start at `k + 3` to
avoid the final pair of equal values `1, 1`.
-/
theorem fib_pair_mod (k : ℕ) : Nat.fib (k + 4) % Nat.fib (k + 3) = Nat.fib (k + 2) := by
  have hlt := Nat.fib_lt_fib_succ (Nat.le_add_left 2 k)
  rw [show k + 4 = (k + 2) + 2 from rfl, Nat.fib_add_two, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt hlt

/--
Starting from adjacent Fibonacci values, `k` updates reach `(2, 1)`. Repeatedly use the
preceding-value remainder identity.
-/
theorem run_fib_pair (k : ℕ) : run k (Nat.fib (k + 3)) (Nat.fib (k + 2)) = (2, 1) := by
  induction k with
  | zero => decide
  | succ k
    ih =>
    have hm : Nat.fib (k + 3) ≠ 0 := Nat.ne_of_gt (Nat.fib_pos.mpr (Nat.zero_lt_succ (k + 2)))
    simpa only [Nat.add_assoc, run, step, ite_eq_right hm, fib_pair_mod] using ih

/--
The computed fuel for the Fibonacci second component is `k + 1`. The greatest-index
specification shows that the bound is sharp on this input.
-/
theorem stepBound_fib (k : ℕ) : stepBound (Nat.fib (k + 2)) = k + 1 := by
  rw [stepBound_eq,
    Nat.greatestFib_fib
      (Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : 1 < 2) (Nat.le_add_left 2 k)))]
  exact Nat.add_sub_cancel (k + 1) 1

/--
Adjacent Fibonacci inputs attain the computed fuel bound as their exact stopping time.
Nontermination after `k` updates and the general upper bound prove equality.
-/
theorem stoppingTime_fib_pair (k : ℕ) :
    stoppingTime (Nat.fib (k + 3)) (Nat.fib (k + 2)) = k + 1 := by
  apply Nat.le_antisymm
  · exact (stoppingTime_le_stepBound _ _).trans_eq (stepBound_fib k)
  · apply Nat.succ_le_of_lt
    apply Nat.lt_of_not_ge
    intro h
    have hz := (stoppingTime_le_iff _ _ k).1 h
    simp only [run_fib_pair, Nat.reduceEqDiff] at hz

end PseudoPrime.NumberTheory.Euclid

namespace PseudoPrime.NumberTheory.Euclid

/--
A divisor-reducing transition relation that remains nonterminal after `k` divisions. Each update
chooses a positive `d <= m` and moves to `(d, c % d)`; zero updates require `m != 0`. The odd
part after Jacobi factor-two removal may serve as `d`. This relation records nontermination
only, not sign updates or gcd preservation.
-/
def divisionNonstop : ℕ → ℕ → ℕ → Prop
  | 0, _c, m => m ≠ 0
  | k + 1, c, m => ∃ d, 0 < d ∧ d ≤ m ∧ divisionNonstop k d (c % d)

/--
Reducing the divisor at each update preserves the Fibonacci nontermination lower bound.
Inductively add the bounds for the remainder and any positive `d <= m`. This supports bounds on
Jacobi reciprocity exchanges.
-/
theorem divisionNonstop_fib_lower (c m k : ℕ) (h : divisionNonstop k c m) :
    Nat.fib (k + 2) ≤ m ∧ (m < c → Nat.fib (k + 3) ≤ c) := by
  induction k generalizing c m with
  | zero => exact fib_lower c m 0 h
  | succ k ih =>
    obtain ⟨d, hdpos, hdm, ht⟩ := h
    have hb := ih d (c % d) ht
    have hr := Nat.mod_lt c hdpos
    constructor
    · simpa only [Nat.add_assoc] using (hb.2 hr).trans hdm
    · intro hmc
      have hs := add_mod_le c d hdpos (hdm.trans (Nat.le_of_lt hmc))
      have hsum := (Nat.add_le_add hb.1 (hb.2 hr)).trans ((Nat.add_comm (c % d) d).trans_le hs)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using (Nat.fib_add_two (n := k + 2)).trans_le hsum

/--
No divisor-reducing nonterminal trajectory exceeds the Fibonacci threshold.
-/
theorem not_divisionNonstop_of_lt_fib (c m k : ℕ) (hm : m < Nat.fib (k + 2)) :
    ¬divisionNonstop k c m := fun h ↦ (Nat.not_lt_of_ge (divisionNonstop_fib_lower c m k h).1) hm

/--
Fast Euclidean fuel also suffices for divisor-reducing transitions. This is the interface for
mapping Jacobi odd-part division trajectories to the transition relation.
-/
theorem not_divisionNonstop_stepBound (c m : ℕ) : ¬divisionNonstop (stepBound m) c m :=
  not_divisionNonstop_of_lt_fib c m (stepBound m) (lt_fib_stepBound m)

end PseudoPrime.NumberTheory.Euclid
