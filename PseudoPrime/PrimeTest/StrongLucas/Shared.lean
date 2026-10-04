/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import PseudoPrime.PrimeTest.StrongLucas.Loop
import PseudoPrime.PrimeTest.LucasV.Defs
import PseudoPrime.PrimeTest.EulerJacobi.Defs

/-! # Shared strengthened Lucas scan and Euler bridge -/

namespace PseudoPrime.PrimeTest

/-- The shared scan result. strongOk records the initial U check and all
visited V checks; v is the next doubled V, and qk retains the pre-final
Q power. These components feed the strengthened fixed-parameter tests. -/
structure LucasStrengthenedState (n : ℕ) where
  strongOk : Bool
  v : ZMod n
  qk : ZMod n

/-- Scan the strong V range and retain the final Lucas-V and half-index Q
power. Check V before doubling. With one check remaining, double V only;
otherwise square Q and recurse. U is used only to initialize ok. -/
def lucasStrengthenedScan (n : ℕ) (v q : ZMod n) (ok : Bool) : ℕ → LucasStrengthenedState n
  | 0 => ⟨ok, v, q⟩
  | s + 1 =>
    let nextOk := ok || (v == 0)
    let nextV := v ^ 2 - 2 * q
    match s with
    | 0 => ⟨nextOk, nextV, q⟩
    | k + 1 => lucasStrengthenedScan n nextV (q ^ 2) nextOk (k + 1)

/-- The accumulated flag equals the initial flag or the ordinary strong
scan. Boolean associativity aligns the finite recursive checks. -/
theorem lucasStrengthenedScan_strong (n : ℕ) (v q : ZMod n) (ok : Bool) (s : ℕ) :
    (lucasStrengthenedScan n v q ok s).strongOk = (ok || lucasVScan n v q s) := by
  induction s generalizing v q ok with
  | zero => simp only [lucasStrengthenedScan, lucasVScan, Bool.or_false]
  | succ s ih =>
    cases s with
    | zero => simp only [lucasStrengthenedScan, lucasVScan, Bool.or_false]
    | succ s => simp only [lucasStrengthenedScan, lucasVScan, ih, Bool.or_assoc]

/-- From index d, the terminal V represents d * 2^s for any scan length.
The last V doubling is included even when only one check remains. -/
theorem lucasStrengthenedScan_v (n : ℕ) (P Q : ℤ) (d s : ℕ) (ok : Bool) :
    (lucasStrengthenedScan n (lucasVZMod n P Q d) (lucasQPow Q d) ok s).v =
      lucasVZMod n P Q (d * 2 ^ s) := by
  induction s generalizing d ok with
  | zero => simp only [lucasStrengthenedScan, pow_zero, mul_one]
  | succ s ih =>
    cases s with
    | zero =>
      simp only [lucasStrengthenedScan, Nat.zero_add, pow_one]
      rw [Nat.mul_comm d 2, lucasVZMod_two_mul]
    | succ s =>
      simp only [lucasStrengthenedScan]
      rw [← lucasVZMod_two_mul, lucasQPow_double, ih]
      congr 1
      rw [pow_succ]
      ring

/-- For s + 1 checks, terminal Q represents d * 2^s. The final Q square
is omitted, so this exponent is half the exponent of terminal V. -/
theorem lucasStrengthenedScan_qk (n : ℕ) (P Q : ℤ) (d s : ℕ) (ok : Bool) :
    (lucasStrengthenedScan n (lucasVZMod n P Q d) (lucasQPow Q d) ok (s + 1)).qk =
      (lucasQPow Q (d * 2 ^ s) : ZMod n) := by
  induction s generalizing d ok with
  | zero => simp only [lucasStrengthenedScan, pow_zero, mul_one]
  | succ s ih =>
    simp only [lucasStrengthenedScan]
    rw [← lucasVZMod_two_mul, lucasQPow_double, ih]
    congr 2
    rw [pow_succ]
    ring

/-- Initialize all Lucas components once at the odd part, then scan V and Q.
The initial U zero check supplies strongOk; correctness uses odd n. -/
def lucasStrengthenedState (n : ℕ) (D P Q : ℤ) : LucasStrengthenedState n :=
  let x := lucasUVQ n P Q (strongLucasOddPart n D)
  lucasStrengthenedScan n x.v x.qk (x.u == 0) (strongLucasTwoAdicExponent n D)

/-- For odd n, the shared flag equals the existing strong test for all
signed parameters. The ordinary scan contract proves the equality. -/
theorem lucasStrengthenedState_strong (n : ℕ) (hn : Odd n) (D P Q : ℤ) :
    (lucasStrengthenedState n D P Q).strongOk = strongLucasWithParams n D P Q := by
  rw [← strongLucasWithParamsUVQ_eq]
  simp only [lucasStrengthenedState, strongLucasWithParamsUVQ, ite_eq_left hn,
    lucasStrengthenedScan_strong]

/-- For odd n, terminal V has the selected Lucas index. The two-adic
factorization connects the scan invariant to the existing sequence. -/
theorem lucasStrengthenedState_v (n : ℕ) (hn : Odd n) (D P Q : ℤ) :
    (lucasStrengthenedState n D P Q).v = lucasVZMod n P Q (lucasProbablePrimeIndex n D) := by
  simp only [lucasStrengthenedState, lucasUVQ_eq n hn, lucasUVQSpec, lucasStrengthenedScan_v,
    strongLucasOddPart, strongLucasTwoAdicExponent, Nat.divMaxPow_mul_pow_padicValNat]

/-- Share Strong and final V on odd inputs with Jacobi discriminant -1.
Keep the original Euler condition. Other inputs use the original
component composition, preserving the total fixed-parameter API. -/
def strengthenedLucasShared (n : ℕ) (D P Q : ℤ) : Bool :=
  if Odd n ∧ jacobiSym D n = -1 then
    let x := lucasStrengthenedState n D P Q
    x.strongOk && ((x.v == 2 * (Q : ZMod n)) && eulerJacobiWithIntBase n Q)
  else strongLucasWithParamsUVQ n D P Q && (lucasVWithParams n D P Q && eulerJacobiWithIntBase n Q)

/-- The shared Strong and V implementation preserves every input's Boolean
result. The selected-index identity supplies the Lucas-V comparison. -/
theorem strengthenedLucasShared_eq (n : ℕ) (D P Q : ℤ) :
    strengthenedLucasShared n D P Q =
      (strongLucasWithParams n D P Q &&
        (lucasVWithParams n D P Q && eulerJacobiWithIntBase n Q)) := by
  by_cases h : Odd n ∧ jacobiSym D n = -1
  · simp only [strengthenedLucasShared, ite_eq_left h, lucasStrengthenedState_strong n h.1,
      lucasStrengthenedState_v n h.1, lucasProbablePrimeIndex_of_jacobi_eq_neg_one h.2]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, beq_iff_eq, lucasVWithParams, decide_eq_true_eq, h.2, true_and,
      lucasVZModFast_eq_lucasVZMod]
  · rw [strengthenedLucasShared, ite_eq_right h, strongLucasWithParamsUVQ_eq]

/-- When at least one strong check occurs, terminal Q has half the selected
index. The final-iteration invariant and index factorization prove this. -/
theorem lucasStrengthenedState_qk (n : ℕ) (hn : Odd n) (D P Q : ℤ)
    (hspos : 1 ≤ strongLucasTwoAdicExponent n D) :
    (lucasStrengthenedState n D P Q).qk =
      (lucasQPow Q (lucasProbablePrimeIndex n D / 2) : ZMod n) := by
  have hd :
    strongLucasOddPart n D * 2 ^ strongLucasTwoAdicExponent n D = lucasProbablePrimeIndex n D :=
    Nat.divMaxPow_mul_pow_padicValNat 2 _
  cases hs : strongLucasTwoAdicExponent n D with
  | zero =>
    rw [hs] at hspos
    exact (Nat.not_succ_le_zero 0 hspos).elim
  | succ
    s =>
    simp only [lucasStrengthenedState, lucasUVQ_eq n hn, lucasUVQSpec, hs, lucasStrengthenedScan_qk]
    rw [← hd, hs, pow_succ, ← Nat.mul_assoc, Nat.mul_div_cancel _ (by decide : 0 < 2)]

/-- Odd n and Jacobi discriminant -1 give at least one strong check.
The selected index n + 1 is positive and divisible by two. -/
theorem strongLucasTwoAdicExponent_pos (n : ℕ) (hn : Odd n) (D : ℤ) (hD : jacobiSym D n = -1) :
    1 ≤ strongLucasTwoAdicExponent n D := by
  rw [strongLucasTwoAdicExponent, lucasProbablePrimeIndex_of_jacobi_eq_neg_one hD]
  exact
    one_le_padicValNat_of_dvd (Nat.succ_ne_zero n)
      (even_iff_two_dvd.mp (hn.add_odd (show Odd (1 : ℕ) from ⟨0, rfl⟩)))

/-- For odd n, the half exponent of n + 1 is one more than n / 2.
The division formula and odd remainder justify the Euler exponent shift. -/
theorem lucasOdd_half_succ (n : ℕ) (hn : Odd n) : (n + 1) / 2 = n / 2 + 1 := by
  rw [Nat.add_div (by decide : 0 < 2), Nat.odd_iff.mp hn]
  rfl

/-- Coprimality of the signed Q magnitude and n makes Q a modular unit.
The natAbs is used only for the gcd guard, retaining the signed base. -/
theorem lucasQ_isUnit_of_coprime (n : ℕ) (Q : ℤ) (h : Nat.Coprime Q.natAbs n) :
    IsUnit (Q : ZMod n) := by
  rw [ZMod.coe_int_isUnit_iff_isCoprime, Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs]
  change Nat.Coprime n Q.natAbs
  exact h.symm

/-- For odd n, Jacobi discriminant -1, and coprime Q, the terminal Q
comparison equals the original Euler condition. Shift the exponent by
one and cancel the modular unit Q. -/
theorem lucasStrengthenedState_euler (n : ℕ) (hn : Odd n) (D P Q : ℤ) (hD : jacobiSym D n = -1)
    (hQ : Nat.Coprime Q.natAbs n) :
    ((lucasStrengthenedState n D P Q).qk == (Q : ZMod n) * (jacobiSym Q n : ZMod n)) =
      eulerJacobiWithIntBase n Q := by
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, lucasStrengthenedState_qk n hn D P Q (strongLucasTwoAdicExponent_pos n hn D hD)]
  simp only [lucasProbablePrimeIndex_of_jacobi_eq_neg_one hD, lucasQPow, Int.cast_pow,
    eulerJacobiWithIntBase, decide_eq_true_eq]
  rw [lucasOdd_half_succ n hn, pow_succ, mul_comm _ (Q : ZMod n),
    (lucasQ_isUnit_of_coprime n Q hQ).mul_right_inj]

/-- Use the shared half-index Q power for Euler when the modulus is odd,
the discriminant Jacobi value is -1, and Q is coprime to n. The fallback
keeps the original Euler computation, while still sharing Strong and V
in its eligible domain. This preserves all totalized inputs. -/
def strengthenedLucasSharedEuler (n : ℕ) (D P Q : ℤ) : Bool :=
  if Odd n ∧ jacobiSym D n = -1 ∧ Nat.Coprime Q.natAbs n then
    let x := lucasStrengthenedState n D P Q
    x.strongOk && ((x.v == 2 * (Q : ZMod n)) && (x.qk == (Q : ZMod n) * (jacobiSym Q n : ZMod n)))
  else strengthenedLucasShared n D P Q

/-- The fully shared eligible branch and its fallback equal the existing
Strong, Lucas-V, and Euler conjunction on every input. The explicit gcd
guard supplies the unit cancellation needed by the Euler bridge. -/
theorem strengthenedLucasSharedEuler_eq (n : ℕ) (D P Q : ℤ) :
    strengthenedLucasSharedEuler n D P Q =
      (strongLucasWithParams n D P Q &&
        (lucasVWithParams n D P Q && eulerJacobiWithIntBase n Q)) := by
  by_cases h : Odd n ∧ jacobiSym D n = -1 ∧ Nat.Coprime Q.natAbs n
  · have hg : Odd n ∧ jacobiSym D n = -1 := ⟨h.1, h.2.1⟩
    simp only [strengthenedLucasSharedEuler, ite_eq_left h,
      lucasStrengthenedState_euler n h.1 D P Q h.2.1 h.2.2]
    rw [← strengthenedLucasShared_eq, strengthenedLucasShared, ite_eq_left hg]
  · rw [strengthenedLucasSharedEuler, ite_eq_right h, strengthenedLucasShared_eq]

/-- A valid Jacobi -1 discriminant prevents Q from being zero modulo n.
If Q were zero, the discriminant would be the square of P. This fact is
valid without primality and supplies the prime-modulus gcd bridge. -/
theorem lucasQ_ne_zero_of_discriminant (n : ℕ) (D P Q : ℤ) (hdisc : D = P * P - 4 * Q)
    (hD : jacobiSym D n = -1) : (Q : ZMod n) ≠ 0 := by
  intro hzero
  apply lucasDiscriminant_not_isSquare_of_jacobi_neg_one hD
  refine ⟨(P : ZMod n), ?_⟩
  simp only [hdisc, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, hzero, mul_zero, sub_zero]

/-- For a prime modulus, valid Jacobi -1 parameters have coprime Q.
Nonzero Q is a field unit, and the integer gcd criterion recovers the
executable natAbs coprimality guard. -/
theorem lucasQ_coprime_of_prime (n : ℕ) (hn : n.Prime) (D P Q : ℤ) (hdisc : D = P * P - 4 * Q)
    (hD : jacobiSym D n = -1) : Nat.Coprime Q.natAbs n := by
  let : Fact n.Prime := ⟨hn⟩
  have hunit : IsUnit (Q : ZMod n) :=
    isUnit_iff_ne_zero.mpr (lucasQ_ne_zero_of_discriminant n D P Q hdisc hD)
  rw [ZMod.coe_int_isUnit_iff_isCoprime, Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs] at hunit
  change Nat.Coprime n Q.natAbs at hunit
  exact hunit.symm

/-- Every odd prime with valid Jacobi -1 parameters uses the fully shared
Euler branch. The coprimality theorem discharges the executable gcd guard,
so the fallback does not handle these prime inputs. -/
theorem strengthenedLucasSharedEuler_prime_branch (n : ℕ) (hn : n.Prime) (hodd : Odd n) (D P Q : ℤ)
    (hdisc : D = P * P - 4 * Q) (hD : jacobiSym D n = -1) :
    strengthenedLucasSharedEuler n D P Q =
      (let x := lucasStrengthenedState n D P Q
       x.strongOk &&
        ((x.v == 2 * (Q : ZMod n)) && (x.qk == (Q : ZMod n) * (jacobiSym Q n : ZMod n)))) := by
  rw [strengthenedLucasSharedEuler,
    ite_eq_left
      (show Odd n ∧ jacobiSym D n = -1 ∧ Nat.Coprime Q.natAbs n from
        ⟨hodd, hD, lucasQ_coprime_of_prime n hn D P Q hdisc hD⟩)]

end PseudoPrime.PrimeTest
