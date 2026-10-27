/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.CommonSignLegendre
public import PseudoPrime.NumberTheory.QuadraticCharacterConductor
public import PseudoPrime.NumberTheory.SubgroupAnnihilator

/-! # Paired quadratic annihilator characters for the common-sign subgroup

Lift the local Jacobi numerator characters to the ambient modulus.
Their products annihilate the actual sign subgroup and have exact pairwise
prime-product conductors; no analytic results are imported.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest

/-- At two odd prime factors, the product of the lifted local quadratic
characters belongs to the annihilator of the actual common-sign subgroup when
the exponent is an odd multiple of both local half exponents. Evaluate the
characters on unit representatives and apply the paired Legendre identity.
This constructs the annihilator members used in the three-prime branch. -/
theorem paired_quadraticCharacter_mem_signSubgroup_annihilator {n p q E kp kq : ℕ} [NeZero n]
    [Fact p.Prime] [Fact q.Prime] [Fact (2 < p)] [Fact (2 < q)] (hpOdd : Odd p) (hqOdd : Odd q)
    (hpn : p ∣ n) (hqn : q ∣ n) (hkp : Odd kp) (hkq : Odd kq) (hEp : E = (p / 2) * kp)
    (hEq : E = (q / 2) * kq) :
    (NumberTheory.complexJacobiNumeratorCharacter p hpOdd).changeLevel hpn *
        (NumberTheory.complexJacobiNumeratorCharacter q hqOdd).changeLevel hqn ∈
      NumberTheory.subgroupAnnihilator (signSubgroup n E) := by
  apply (NumberTheory.mem_subgroupAnnihilator_iff _ _).mpr
  intro u hu
  rw [MulChar.mul_apply, DirichletCharacter.changeLevel_eq_cast_of_dvd,
    DirichletCharacter.changeLevel_eq_cast_of_dvd, ZMod.cast_eq_val, ZMod.cast_eq_val]
  have hpval :
    NumberTheory.complexJacobiNumeratorCharacter p hpOdd ((u : ZMod n).val : ZMod p) =
      (legendreSym p (((u : ZMod n).val : ℕ) : ℤ) : ℂ) := by
    simpa only [Int.cast_natCast, ← jacobiSym.legendreSym.to_jacobiSym] using
      NumberTheory.complexJacobiNumeratorCharacter_apply_int p hpOdd (((u : ZMod n).val : ℕ) : ℤ)
  have hqval :
    NumberTheory.complexJacobiNumeratorCharacter q hqOdd ((u : ZMod n).val : ZMod q) =
      (legendreSym q (((u : ZMod n).val : ℕ) : ℤ) : ℂ) := by
    simpa only [Int.cast_natCast, ← jacobiSym.legendreSym.to_jacobiSym] using
      NumberTheory.complexJacobiNumeratorCharacter_apply_int q hqOdd (((u : ZMod n).val : ℕ) : ℤ)
  rw [hpval, hqval, ← Int.cast_mul,
    legendre_pair_mul_eq_one_on_signSubgroup hpn hqn hkp hkq hEp hEq u hu, Int.cast_one]

/-- The product of two lifted local quadratic characters at distinct odd primes
has exact conductor p*q. Each local character is primitive at its prime level,
changing levels preserves conductors, and the coprime conductor product formula
is exact. This supplies the three pairwise conductors for the Gaussian branch. -/
theorem paired_quadraticCharacter_conductor {n p q : ℕ} [NeZero n] [Fact p.Prime] [Fact q.Prime]
    (hpOdd : Odd p) (hqOdd : Odd q) (hpn : p ∣ n) (hqn : q ∣ n) (hpq : p ≠ q) :
    ((NumberTheory.complexJacobiNumeratorCharacter p hpOdd).changeLevel hpn *
          (NumberTheory.complexJacobiNumeratorCharacter q hqOdd).changeLevel hqn).conductor =
      p * q := by
  have hp : Nat.Prime p := Fact.out
  have hq : Nat.Prime q := Fact.out
  have hpc := NumberTheory.complexJacobiNumeratorCharacter_isPrimitive p hpOdd hp.squarefree
  have hqc := NumberTheory.complexJacobiNumeratorCharacter_isPrimitive q hqOdd hq.squarefree
  have hcop : Nat.Coprime p q :=
    (hp.coprime_iff_not_dvd).mpr (fun h ↦ hpq ((Nat.dvd_prime hq).mp h |>.resolve_left hp.ne_one))
  have hcp :
    ((NumberTheory.complexJacobiNumeratorCharacter p hpOdd).changeLevel hpn).conductor = p :=
    (DirichletCharacter.conductor_changeLevel _ _).trans hpc
  have hcq :
    ((NumberTheory.complexJacobiNumeratorCharacter q hqOdd).changeLevel hqn).conductor = q :=
    (DirichletCharacter.conductor_changeLevel _ _).trans hqc
  rw [NumberTheory.conductor_mul_of_coprime]
  · rw [hcp, hcq]
  · rw [hcp, hcq]
    exact hcop

/-- Under the local half-exponent odd-multiple conditions, the actual
common-sign annihilator contains a character with conductor p*q. Package the
lifted quadratic product with its proved membership and exact conductor.
This avoids passing externally supplied characters to the three-prime MR branch. -/
theorem exists_paired_sign_annihilator_with_conductor {n p q E kp kq : ℕ} [NeZero n] [Fact p.Prime]
    [Fact q.Prime] [Fact (2 < p)] [Fact (2 < q)] (hpOdd : Odd p) (hqOdd : Odd q) (hpn : p ∣ n)
    (hqn : q ∣ n) (hkp : Odd kp) (hkq : Odd kq) (hEp : E = (p / 2) * kp) (hEq : E = (q / 2) * kq)
    (hpq : p ≠ q) :
    ∃ a : NumberTheory.subgroupAnnihilator (signSubgroup n E), a.val.conductor = p * q := by
  refine
    ⟨⟨_,
        paired_quadraticCharacter_mem_signSubgroup_annihilator hpOdd hqOdd hpn hqn hkp hkq hEp hEq⟩,
      ?_⟩
  exact paired_quadraticCharacter_conductor hpOdd hqOdd hpn hqn hpq

end PseudoPrime.PrimeTest
