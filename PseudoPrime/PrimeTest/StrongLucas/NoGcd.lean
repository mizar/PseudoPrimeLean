/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.StrongLucas.Shared

/-! # Lucas-V acceptance and gcd-free shared strengthened execution -/

@[expose] public section

namespace PseudoPrime.PrimeTest

/-- If Q vanishes modulo n, every positive-index V value is the corresponding power of P.
The recurrence discards its Q term; induction supplies the prime-factor contradiction. -/
theorem lucasVZMod_succ_of_q_zero (n : ℕ) (P Q : ℤ) (hQ : (Q : ZMod n) = 0) (k : ℕ) :
    lucasVZMod n P Q (k + 1) = (P : ZMod n) ^ (k + 1) := by
  induction k with
  | zero => simp only [Nat.zero_add, lucasVZMod, lucasV_one, pow_one]
  | succ k ih =>
    change (lucasV P Q (k + 2) : ZMod n) = (P : ZMod n) ^ (k + 1 + 1)
    rw [lucasV_succ_succ, Int.cast_sub, Int.cast_mul, Int.cast_mul, hQ, zero_mul, sub_zero]
    change (P : ZMod n) * lucasVZMod n P Q (k + 1) = _
    rw [ih]
    exact (pow_succ' (P : ZMod n) (k + 1)).symm

end PseudoPrime.PrimeTest

namespace PseudoPrime.PrimeTest

/-- At a prime divisor of n where Q vanishes, a valid Jacobi -1 discriminant forces P nonzero.
Map the discriminant unit to the prime field and use the discriminant equation. -/
theorem lucasP_ne_zero_of_prime_dvd_q (n p : ℕ) (hp : p.Prime) (hpn : p ∣ n) (D P Q : ℤ)
    (hdisc : D = P * P - 4 * Q) (hD : jacobiSym D n = -1) (hQ : (Q : ZMod p) = 0) :
    (P : ZMod p) ≠ 0 := by
  let : Fact p.Prime := ⟨hp⟩
  have hu := (lucasDiscriminant_isUnit_of_jacobi_neg_one hD).map (ZMod.castHom hpn (ZMod p))
  simp only [map_intCast] at hu
  intro hzero
  apply hu.ne_zero
  simp only [hdisc, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, hzero, hQ, mul_zero, sub_zero]

/-- A Lucas-V acceptance equation excludes every common prime divisor of Q and n.
At that divisor V is a nonzero power of P, whereas the accepted right side is zero. -/
theorem lucasV_q_no_common_prime (n p : ℕ) (hp : p.Prime) (hpn : p ∣ n) (D P Q : ℤ)
    (hdisc : D = P * P - 4 * Q) (hD : jacobiSym D n = -1)
    (hV : lucasVZMod n P Q (n + 1) = 2 * (Q : ZMod n)) (hpQ : p ∣ Q.natAbs) : False := by
  let : Fact p.Prime := ⟨hp⟩
  have hQ : (Q : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd Q p).mpr (Int.natCast_dvd.mpr hpQ)
  have hv := congrArg (ZMod.castHom hpn (ZMod p)) hV
  simp only [lucasVZMod, map_intCast, map_mul, map_ofNat, hQ, mul_zero] at hv
  change lucasVZMod p P Q (n + 1) = 0 at hv
  rw [lucasVZMod_succ_of_q_zero p P Q hQ n] at hv
  exact pow_ne_zero (n + 1) (lucasP_ne_zero_of_prime_dvd_q n p hp hpn D P Q hdisc hD hQ) hv

/-- Valid Jacobi -1 parameters satisfying the Lucas-V acceptance equation have coprime Q and n.
This holds for composite moduli too; a prime divisor of a nontrivial gcd gives a contradiction. -/
theorem lucasV_q_coprime (n : ℕ) (D P Q : ℤ) (hdisc : D = P * P - 4 * Q) (hD : jacobiSym D n = -1)
    (hV : lucasVZMod n P Q (n + 1) = 2 * (Q : ZMod n)) : Nat.Coprime Q.natAbs n := by
  by_contra hcop
  obtain ⟨p, hp, hpg⟩ :=
    Nat.exists_prime_and_dvd
      (show Nat.gcd Q.natAbs n ≠ 1 from fun h ↦ hcop (Nat.coprime_iff_gcd_eq_one.mpr h))
  exact
    lucasV_q_no_common_prime n p hp (Nat.dvd_trans hpg (Nat.gcd_dvd_right _ _)) D P Q hdisc hD hV
      (Nat.dvd_trans hpg (Nat.gcd_dvd_left _ _))

end PseudoPrime.PrimeTest

namespace PseudoPrime.PrimeTest

/-- Passing the shared terminal V comparison supplies coprimality without a runtime gcd test.
The state invariant transports the Lucas-V acceptance equation to the arithmetic theorem. -/
theorem lucasStrengthenedState_v_q_coprime (n : ℕ) (hn : Odd n) (param : LucasParams)
    (hD : jacobiSym param.D n = -1)
    (hV : (lucasStrengthenedState n param.D param.P param.Q).v = 2 * (param.Q : ZMod n)) :
    Nat.Coprime param.Q.natAbs n := by
  apply lucasV_q_coprime n param.D param.P param.Q param.discr hD
  rw [← lucasProbablePrimeIndex_of_jacobi_eq_neg_one hD, ← lucasStrengthenedState_v n hn]
  exact hV

/-- Evaluate valid Lucas parameters without a gcd guard on the shared Euler branch.
Odd moduli with Jacobi -1 use Strong, terminal V, and half-index Q; other inputs retain fallback.
The discriminant invariant is carried by param, and terminal V supplies the cancellation premise. -/
def strengthenedLucasSharedEulerValid (n : ℕ) (param : LucasParams) : Bool :=
  if Odd n ∧ jacobiSym param.D n = -1 then
    let x := lucasStrengthenedState n param.D param.P param.Q
    x.strongOk &&
      ((x.v == 2 * (param.Q : ZMod n)) &&
        (x.qk == (param.Q : ZMod n) * (jacobiSym param.Q n : ZMod n)))
  else strengthenedLucasSharedEuler n param.D param.P param.Q

/-- Removing the gcd guard preserves every result for proof-carrying valid parameters.
A failed V comparison rejects both computations; a passed one supplies Q's unit cancellation. -/
theorem strengthenedLucasSharedEulerValid_eq (n : ℕ) (param : LucasParams) :
    strengthenedLucasSharedEulerValid n param =
      strengthenedLucasSharedEuler n param.D param.P param.Q := by
  by_cases hg : Odd n ∧ jacobiSym param.D n = -1
  · rw [strengthenedLucasSharedEuler_eq, ← strengthenedLucasShared_eq]
    simp only [strengthenedLucasSharedEulerValid, strengthenedLucasShared, ite_eq_left hg]
    by_cases hV : (lucasStrengthenedState n param.D param.P param.Q).v = 2 * (param.Q : ZMod n)
    · rw [lucasStrengthenedState_euler n hg.1 param.D param.P param.Q hg.2
          (lucasStrengthenedState_v_q_coprime n hg.1 param hg.2 hV)]
    · apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, beq_iff_eq, hV, false_and, and_false]
  · rw [strengthenedLucasSharedEulerValid, ite_eq_right hg]

end PseudoPrime.PrimeTest
