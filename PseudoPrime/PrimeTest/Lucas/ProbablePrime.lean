/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.Lucas.Params
public import PseudoPrime.PrimeTest.Lucas.Fast
public import PseudoPrime.PrimeTest.Lucas.Spec
public import Mathlib.Data.ZMod.Units
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# Lucas probable-prime specification

The initial Lucas interface covers the Selfridge branch `(D / n) = -1`, for
which the tested index is `n + 1`.  Other Jacobi values use the `n - 1`
fallback so that the executable index remains total; stronger admissibility
conditions are imposed by the later prime-completeness theorems.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest

/--
If jacobiSym D n=-1, D is nonsquare in ZMod n, without a primality assumption.
Apply the Jacobi nonsquare theorem; this excludes a degenerate discriminant
in Lucas parameter and cancellation arguments.
-/
theorem lucasDiscriminant_not_isSquare_of_jacobi_neg_one {D : ℤ} {n : ℕ}
    (hjacobi : jacobiSym D n = -1) : ¬IsSquare (D : ZMod n) := by
  exact ZMod.nonsquare_of_jacobiSym_eq_neg_one hjacobi

/--
A Jacobi -1 discriminant is nonzero in ZMod n for any natural modulus.
Otherwise zero itself witnesses a square, contradicting the nonsquare theorem.
This supplies a nondegeneracy premise in Lucas arithmetic.
-/
theorem lucasDiscriminant_ne_zero_of_jacobi_neg_one {D : ℤ} {n : ℕ} (hjacobi : jacobiSym D n = -1) :
    (D : ZMod n) ≠ 0 := by
  intro hzero
  apply lucasDiscriminant_not_isSquare_of_jacobi_neg_one hjacobi
  refine ⟨0, ?_⟩
  simp only [hzero, zero_mul]

/--
A Jacobi -1 discriminant is a unit in ZMod n, including composite moduli.
Exclude n=0, then a nontrivial gcd would force the Jacobi symbol to vanish.
The integer coprimality criterion transports the result to the modular unit interface.
-/
theorem lucasDiscriminant_isUnit_of_jacobi_neg_one {D : ℤ} {n : ℕ} (hjacobi : jacobiSym D n = -1) :
    IsUnit (D : ZMod n) := by
  rw [ZMod.coe_int_isUnit_iff_isCoprime, Int.isCoprime_iff_gcd_eq_one]
  rcases eq_or_ne n 0 with hn | hn
  · subst n
    rw [jacobiSym.zero_right] at hjacobi
    norm_num only at hjacobi
  · have hcop : D.gcd n = 1 := by
      by_contra hcop
      have hzero : jacobiSym D n = 0 := (@jacobiSym.eq_zero_iff_not_coprime D n ⟨hn⟩).2 hcop
      rw [hzero] at hjacobi
      norm_num only at hjacobi
    simpa only [Int.gcd_comm] using hcop

/--
Select n+1 when jacobiSym D n=-1, and the truncated natural difference n-1 otherwise.
This total index is used by ordinary and Strong Lucas tests. The fallback covers all
other Jacobi values and is not itself an admissibility guarantee.
-/
def lucasProbablePrimeIndex (n : ℕ) (D : ℤ) : ℕ :=
  if jacobiSym D n = -1 then n + 1 else n - 1

/--
The proof-side Lucas-U condition U_k(P,Q)=0 modulo n for proof-carrying Lucas parameters,
where k is lucasProbablePrimeIndex n D. The record ensures D=P*P-4*Q, but this predicate
adds no primality or Jacobi guard; prime completeness uses separate assumptions.
-/
def IsLucasProbablePrime (n : ℕ) (param : LucasParams) : Prop :=
  lucasUZMod n param.P param.Q (lucasProbablePrimeIndex n param.D) = 0

/--
Test whether the fast modular U at the selected Lucas index is zero.
The signed D,P,Q are unrestricted here; no discriminant, Jacobi or small-input guard
is performed. This fixed-parameter component is connected to the parameter-record specification.
-/
def lucasWithParams (n : ℕ) (D P Q : ℤ) : Bool :=
  decide (lucasUZModFast n P Q (lucasProbablePrimeIndex n D) = 0)

/--
Assuming D=P*P-4*Q, the fixed-parameter Boolean pass is equivalent to IsLucasProbablePrime
for the corresponding parameter record. Unfold the test and rewrite fast U to its specification.
This links executable acceptance with the proof-side congruence, not with primality itself.
-/
theorem lucasWithParams_eq_true_iff (n : ℕ) (D P Q : ℤ) (hdisc : D = P * P - 4 * Q) :
    lucasWithParams n D P Q = true ↔
      IsLucasProbablePrime n (LucasParams.ofDiscriminant D P Q hdisc) := by
  simp only [lucasWithParams, IsLucasProbablePrime, LucasParams.ofDiscriminant, decide_eq_true_eq,
    lucasUZModFast_eq_lucasUZMod]

/--
When jacobiSym D n=-1, the selected Lucas index is exactly n+1.
Unfold the branch definition; this specializes Selfridge and shared terminal-scan formulas.
-/
theorem lucasProbablePrimeIndex_of_jacobi_eq_neg_one {n : ℕ} {D : ℤ}
    (hjacobi : jacobiSym D n = -1) : lucasProbablePrimeIndex n D = n + 1 := by
  simp only [lucasProbablePrimeIndex, hjacobi, ite_true]

/--
When jacobiSym D n differs from -1, the total selected index is n-1.
Unfold the alternate branch; the natural subtraction covers small inputs as well.
This supplies the complementary branch of fixed-parameter correctness proofs.
-/
theorem lucasProbablePrimeIndex_of_jacobi_ne_neg_one {n : ℕ} {D : ℤ}
    (hjacobi : jacobiSym D n ≠ -1) : lucasProbablePrimeIndex n D = n - 1 := by
  simp only [lucasProbablePrimeIndex, hjacobi, ite_false]

end PseudoPrime.PrimeTest
