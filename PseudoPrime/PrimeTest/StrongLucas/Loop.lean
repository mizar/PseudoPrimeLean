/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.StrongLucas.Spec
public import PseudoPrime.PrimeTest.Lucas.UVQ

/-! # Shared Strong Lucas doubling scan -/

@[expose] public section

namespace PseudoPrime.PrimeTest

/-- Scan consecutive Lucas doubling states. The inputs represent V and Q^m;
zero is checked before updating, and the last failed check performs no doubling. -/
def lucasVScan (n : ℕ) (v q : ZMod n) : ℕ → Bool
  | 0 => false
  | s + 1 =>
    (v == 0) ||
      (match s with
      | 0 => false
      | k + 1 => lucasVScan n (v ^ 2 - 2 * q) (q ^ 2) (k + 1))

/--
A scan of length `s + 1` checks the current `v` for zero, then scans the doubled state.
For arbitrary modular `v`, `q`, the tail uses `(v^2 - 2q, q^2)` for `s` checks.
Case analysis on `s` proves the equation by reflexivity, including the optimized zero-tail case.
This equation exposes the recursive invariant used to characterize all tested Lucas indices.
-/
theorem lucasVScan_step (n : ℕ) (v q : ZMod n) (s : ℕ) :
    lucasVScan n v q (s + 1) = ((v == 0) || lucasVScan n (v ^ 2 - 2 * q) (q ^ 2) s) := by
  cases s <;> rfl

/--
Squaring the modular image of `Q^d` equals the image of `Q^(2d)`.
The signed integer parameter `Q`, natural modulus `n`, and exponent `d` are arbitrary.
The proof rewrites integer casting, powers, and exponent multiplication.
It maintains the shared `Q`-power component in the Lucas doubling scan invariant.
-/
theorem lucasQPow_double (n : ℕ) (Q : ℤ) (d : ℕ) :
    (lucasQPow Q d : ZMod n) ^ 2 = (lucasQPow Q (2 * d) : ZMod n) := by
  simp only [lucasQPow, Int.cast_pow, pow_mul, Nat.mul_comm 2 d]

/-- Starting from index d, the scan checks exactly V at d * 2^r for r < s.
The proof transports both state components through the Lucas doubling identity. -/
theorem lucasVScan_spec (n : ℕ) (P Q : ℤ) (d s : ℕ) :
    lucasVScan n (lucasVZMod n P Q d) (lucasQPow Q d) s = true ↔
      ∃ r < s, lucasVZMod n P Q (d * 2 ^ r) = 0 := by
  induction s generalizing d with
  | zero => simp only [lucasVScan, Bool.false_eq_true, Nat.not_lt_zero, false_and, exists_false]
  | succ s
    ih =>
    rw [lucasVScan_step, Bool.or_eq_true, beq_iff_eq, ← lucasVZMod_two_mul, lucasQPow_double, ih,
      Nat.exists_lt_succ_left]
    simp only [pow_zero, mul_one, pow_succ]
    have heq : ∀ r : ℕ, 2 * d * 2 ^ r = d * (2 ^ r * 2) := by
      intro r
      ring
    simp only [heq]

/--
Binary modular exponentiation at `d` equals the cast of the signed integer power `Q^d`.
For arbitrary natural `n`, `d` and integer `Q`, induction uses the zero and successor equations
of `npowBinRec` and preservation of powers by casts. This connects executable initialization
of the scan's `Q` component to the mathematical doubling invariant.
-/
theorem lucasQPow_binRec (n : ℕ) (Q : ℤ) (d : ℕ) :
    npowBinRec d (Q : ZMod n) = (lucasQPow Q d : ZMod n) := by
  induction d with
  | zero => simp only [npowBinRec_zero, lucasQPow, pow_zero, Int.cast_one]
  | succ d ih =>
    rw [npowBinRec_succ, ih]
    simp only [lucasQPow, pow_succ, Int.cast_mul, Int.cast_pow]

/--
Strong Lucas execution with binary initialization and a shared `V`, `Q` doubling scan.
For natural `n` and integer `D`, `P`, `Q`, compute the selected odd part `d` and exponent `s`;
accept `U_d = 0` or scan the next `s` prescribed `V` indices using one evolving state.
This total entry also covers zero and even moduli. The odd-modulus `UVQ` entry uses it as a
fallback, and the all-input equality preserves the original finite-index Strong specification.
-/
def strongLucasWithParamsLoop (n : ℕ) (D P Q : ℤ) : Bool :=
  let d := strongLucasOddPart n D
  let s := strongLucasTwoAdicExponent n D
  (lucasUZModFast n P Q d == 0) ||
    lucasVScan n (lucasVZModFast n P Q d) (npowBinRec d (Q : ZMod n)) s

/-- The doubling implementation equals the existing fixed-parameter test for
all inputs. The finite scan invariant aligns its checks with List.range. -/
theorem strongLucasWithParamsLoop_eq (n : ℕ) (D P Q : ℤ) :
    strongLucasWithParamsLoop n D P Q = strongLucasWithParams n D P Q := by
  apply Bool.eq_iff_iff.mpr
  simp only [strongLucasWithParamsLoop, strongLucasWithParams, Bool.or_eq_true, beq_iff_eq,
    lucasVZModFast_eq_lucasVZMod, lucasQPow_binRec, lucasVScan_spec, List.any_eq_true,
    List.mem_range]

/-- For odd n, initialize U, V, and Q^d together and then scan only V and Q.
The fallback preserves the total fixed-parameter API outside the odd domain. -/
def strongLucasWithParamsUVQ (n : ℕ) (D P Q : ℤ) : Bool :=
  if Odd n then
    let x := lucasUVQ n P Q (strongLucasOddPart n D)
    (x.u == 0) || lucasVScan n x.v x.qk (strongLucasTwoAdicExponent n D)
  else strongLucasWithParamsLoop n D P Q

/-- The binary triple initializer and doubling scan preserve the original
test on all inputs. Odd inputs use the triple invariant; other inputs use
the already verified total fallback. No discriminant hypothesis is needed. -/
theorem strongLucasWithParamsUVQ_eq (n : ℕ) (D P Q : ℤ) :
    strongLucasWithParamsUVQ n D P Q = strongLucasWithParams n D P Q := by
  by_cases hn : Odd n
  · simp only [strongLucasWithParamsUVQ, ite_eq_left hn, lucasUVQ_eq n hn, lucasUVQSpec]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, beq_iff_eq, lucasVScan_spec, strongLucasWithParams,
      List.any_eq_true, List.mem_range, lucasUZModFast_eq_lucasUZMod, lucasVZModFast_eq_lucasVZMod]
  · rw [strongLucasWithParamsUVQ, ite_eq_right hn, strongLucasWithParamsLoop_eq]

end PseudoPrime.PrimeTest
