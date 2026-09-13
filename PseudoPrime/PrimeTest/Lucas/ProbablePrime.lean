/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import PseudoPrime.PrimeTest.Lucas.Params
import PseudoPrime.PrimeTest.Lucas.Fast
import PseudoPrime.PrimeTest.Lucas.Spec
import Mathlib.Data.ZMod.Units
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# Lucas probable-prime specification

The initial Lucas interface covers the Selfridge branch `(D / n) = -1`, for
which the tested index is `n + 1`.  Other Jacobi values use the `n - 1`
fallback so that the executable index remains total; stronger admissibility
conditions are imposed by the later prime-completeness theorems.
-/

namespace PseudoPrime.PrimeTest

/-- A Jacobi `-1` discriminant is nonsquare modulo any modulus. -/
theorem lucasDiscriminant_not_isSquare_of_jacobi_neg_one {D : ℤ} {n : ℕ}
    (hjacobi : jacobiSym D n = -1) : ¬IsSquare (D : ZMod n) := by
  exact ZMod.nonsquare_of_jacobiSym_eq_neg_one hjacobi

/-- A Jacobi `-1` discriminant is nonzero modulo the modulus. -/
theorem lucasDiscriminant_ne_zero_of_jacobi_neg_one {D : ℤ} {n : ℕ} (hjacobi : jacobiSym D n = -1) :
    (D : ZMod n) ≠ 0 := by
  intro hzero
  apply lucasDiscriminant_not_isSquare_of_jacobi_neg_one hjacobi
  refine ⟨0, ?_⟩
  simp only [hzero, zero_mul]

/-- A Jacobi `-1` discriminant is a unit modulo the modulus. -/
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

/-- The Lucas index selected from the Jacobi value of the discriminant. -/
def lucasProbablePrimeIndex (n : ℕ) (D : ℤ) : ℕ :=
  if jacobiSym D n = -1 then n + 1 else n - 1

/-- The Lucas `U` congruence used by the probable-prime specification. -/
def IsLucasProbablePrime (n : ℕ) (param : LucasParams) : Prop :=
  lucasUZMod n param.P param.Q (lucasProbablePrimeIndex n param.D) = 0

/-- The executable Lucas probable-prime test for explicit integer parameters. -/
def lucasWithParams (n : ℕ) (D P Q : ℤ) : Bool :=
  decide (lucasUZModFast n P Q (lucasProbablePrimeIndex n D) = 0)

/-- The executable Lucas test is equivalent to its proof-carrying specification. -/
theorem lucasWithParams_eq_true_iff (n : ℕ) (D P Q : ℤ) (hdisc : D = P * P - 4 * Q) :
    lucasWithParams n D P Q = true ↔
      IsLucasProbablePrime n (LucasParams.ofDiscriminant D P Q hdisc) := by
  simp only [lucasWithParams, IsLucasProbablePrime, LucasParams.ofDiscriminant, decide_eq_true_eq,
    lucasUZModFast_eq_lucasUZMod]

/-- In the Selfridge Jacobi branch, the Lucas index is `n + 1`. -/
theorem lucasProbablePrimeIndex_of_jacobi_eq_neg_one {n : ℕ} {D : ℤ}
    (hjacobi : jacobiSym D n = -1) : lucasProbablePrimeIndex n D = n + 1 := by
  simp only [lucasProbablePrimeIndex, hjacobi, ite_true]

/-- For a Jacobi value different from `-1`, the total executable index is `n - 1`. -/
theorem lucasProbablePrimeIndex_of_jacobi_ne_neg_one {n : ℕ} {D : ℤ}
    (hjacobi : jacobiSym D n ≠ -1) : lucasProbablePrimeIndex n D = n - 1 := by
  simp only [lucasProbablePrimeIndex, hjacobi, ite_false]

end PseudoPrime.PrimeTest
