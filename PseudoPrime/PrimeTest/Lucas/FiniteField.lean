/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
Authors: Mizar
-/

import PseudoPrime.PrimeTest.Lucas.Defs
import PseudoPrime.PrimeTest.Lucas.Spec
import PseudoPrime.PrimeTest.StrongLucas.Defs
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.AdjoinRoot

/-!
# Finite-field Lucas identities

This file isolates the algebraic part of Lucas prime completeness.  The
construction of a quadratic extension and the proof that Frobenius exchanges
its two roots are kept separate from this identity.
-/

namespace PseudoPrime.PrimeTest

/-- The quadratic polynomial whose roots have Lucas parameters `P` and `Q`. -/
noncomputable def lucasQuadraticPolynomial {K : Type*} [CommRing K] (P Q : K) : Polynomial K :=
  Polynomial.X ^ 2 - Polynomial.C P * Polynomial.X + Polynomial.C Q

/-- The canonical root of `lucasQuadraticPolynomial` satisfies its equation. -/
theorem adjoinRoot_lucasQuadratic_root_eq_zero {K : Type*} [CommRing K] (P Q : K) :
    (AdjoinRoot.root (lucasQuadraticPolynomial P Q)) ^ 2 -
          (P : AdjoinRoot (lucasQuadraticPolynomial P Q)) *
            AdjoinRoot.root (lucasQuadraticPolynomial P Q) +
        (Q : AdjoinRoot (lucasQuadraticPolynomial P Q)) =
      0 := by
  have h := AdjoinRoot.eval₂_root (lucasQuadraticPolynomial P Q)
  rw [lucasQuadraticPolynomial, Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_X] at h
  simp only [Polynomial.eval₂_C] at h
  exact h

/-- A nonsquare discriminant makes the Lucas quadratic polynomial irreducible. -/
theorem lucasQuadraticPolynomial_irreducible_of_not_isSquare {K : Type*} [Field K] (P Q : K)
    (hdisc : ¬IsSquare (P * P - 4 * Q)) : Irreducible (lucasQuadraticPolynomial P Q) := by
  have hdeg := Polynomial.isMonicOfDegree_sub_add_two P Q
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [lucasQuadraticPolynomial, hdeg.natDegree_eq]
    decide
  · intro x hx
    apply hdisc
    refine ⟨2 * x - P, ?_⟩
    change (lucasQuadraticPolynomial P Q).eval x = 0 at hx
    simp only [lucasQuadraticPolynomial, Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X] at hx
    calc
      P * P - 4 * Q = (2 * x - P) ^ 2 - 4 * (x ^ 2 - P * x + Q) := by ring
      _ = (2 * x - P) ^ 2 := by rw [hx, mul_zero, sub_zero]
      _ = (2 * x - P) * (2 * x - P) := by rw [pow_two]

/-- A nonsquare discriminant equips the quadratic `AdjoinRoot` with a field structure. -/
theorem adjoinRoot_lucasQuadratic_isField_of_not_isSquare {K : Type*} [Field K] (P Q : K)
    (hdisc : ¬IsSquare (P * P - 4 * Q)) : IsField (AdjoinRoot (lucasQuadraticPolynomial P Q)) := by
  have hI : Fact (Irreducible (lucasQuadraticPolynomial P Q)) :=
    ⟨lucasQuadraticPolynomial_irreducible_of_not_isSquare P Q hdisc⟩
  exact AdjoinRoot.isField_iff_irreducible.mpr hI.out

/-- The standard root and its trace-complement have Lucas sum and product. -/
theorem adjoinRoot_lucasQuadratic_roots {K : Type*} [Field K] (P Q : K)
    (hdisc : ¬IsSquare (P * P - 4 * Q)) :
    ∃ α β : AdjoinRoot (lucasQuadraticPolynomial P Q), α + β = P ∧ α * β = Q := by
  have hI : Fact (Irreducible (lucasQuadraticPolynomial P Q)) :=
    ⟨lucasQuadraticPolynomial_irreducible_of_not_isSquare P Q hdisc⟩
  let α : AdjoinRoot (lucasQuadraticPolynomial P Q) :=
    AdjoinRoot.root (lucasQuadraticPolynomial P Q)
  let β : AdjoinRoot (lucasQuadraticPolynomial P Q) := P - α
  refine ⟨α, β, ?_, ?_⟩
  · dsimp [β]
    ring
  · have hroot := adjoinRoot_lucasQuadratic_root_eq_zero P Q
    dsimp [α, β]
    calc
      AdjoinRoot.root (lucasQuadraticPolynomial P Q) *
            ((AdjoinRoot.of (lucasQuadraticPolynomial P Q)) P -
              AdjoinRoot.root (lucasQuadraticPolynomial P Q)) =
          (AdjoinRoot.of (lucasQuadraticPolynomial P Q)) Q -
            (AdjoinRoot.root (lucasQuadraticPolynomial P Q) ^ 2 -
                (AdjoinRoot.of (lucasQuadraticPolynomial P Q)) P *
                  AdjoinRoot.root (lucasQuadraticPolynomial P Q) +
              (AdjoinRoot.of (lucasQuadraticPolynomial P Q)) Q) :=
        by ring
      _ = (AdjoinRoot.of (lucasQuadraticPolynomial P Q)) Q := by rw [hroot, sub_zero]

/-- Closed-form identity for the Lucas `U` sequence at two formal roots. -/
theorem lucasU_root_difference_mul {K : Type*} [CommRing K] (P Q : ℤ) (α β : K) (hsum : α + β = P)
    (hprod : α * β = Q) : ∀ k : ℕ, (α - β) * (lucasU P Q k : K) = α ^ k - β ^ k := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero => simp only [lucasU_zero, Int.cast_zero, mul_zero, pow_zero, sub_self]
  | one => simp only [lucasU_one, Int.cast_one, mul_one, pow_one]
  | more k hk
    hk1 =>
    have hrec :
      (lucasU P Q (k + 2) : K) =
        (P : K) * (lucasU P Q (k + 1) : K) - (Q : K) * (lucasU P Q k : K) := by
      rw [lucasU_succ_succ]
      simp only [Int.cast_sub, Int.cast_mul]
    rw [hrec]
    rw [show (P : K) = α + β by exact_mod_cast hsum.symm,
      show (Q : K) = α * β by exact_mod_cast hprod.symm]
    calc
      (α - β) * ((α + β) * (lucasU P Q (k + 1) : K) - (α * β) * (lucasU P Q k : K)) =
          (α - β) * ((α + β) * (lucasU P Q (k + 1) : K)) -
            (α - β) * ((α * β) * (lucasU P Q k : K)) :=
        by ring
      _ = α ^ (k + 2) - β ^ (k + 2) := by
        calc
          (α - β) * ((α + β) * (lucasU P Q (k + 1) : K)) -
                (α - β) * ((α * β) * (lucasU P Q k : K)) =
              (α + β) * ((α - β) * (lucasU P Q (k + 1) : K)) -
                (α * β) * ((α - β) * (lucasU P Q k : K)) :=
            by ring
          _ = α ^ (k + 2) - β ^ (k + 2) := by
            rw [hk1, hk]
            ring

/-- The companion closed form expresses `V` as the sum of the two powers. -/
theorem lucasV_root_sum {K : Type*} [CommRing K] (P Q : ℤ) (α β : K) (hsum : α + β = P)
    (hprod : α * β = Q) : ∀ k : ℕ, (lucasV P Q k : K) = α ^ k + β ^ k := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero =>
    simp only [lucasV_zero, Int.cast_ofNat, pow_zero]
    norm_num only
  | one =>
    simp only [lucasV_one, pow_one]
    exact hsum.symm
  | more k hk hk1 =>
    rw [lucasV_succ_succ]
    simp only [Int.cast_sub, Int.cast_mul]
    rw [hk, hk1, show (P : K) = α + β by exact_mod_cast hsum.symm,
      show (Q : K) = α * β by exact_mod_cast hprod.symm]
    ring

/-- Frobenius exchange gives the Lucas `V` value `2 * Q` at `p + 1`. -/
theorem lucasV_add_one_eq_two_mul_of_root_frobenius_swap {K : Type*} [CommRing K] (p : ℕ) (P Q : ℤ)
    (α β : K) (hsum : α + β = P) (hprod : α * β = Q) (hα : α ^ p = β) (hβ : β ^ p = α) :
    (lucasV P Q (p + 1) : K) = 2 * (Q : K) := by
  rw [lucasV_root_sum P Q α β hsum hprod (p + 1), pow_add, pow_add, hα, hβ, pow_one, pow_one]
  rw [mul_comm β α, show α * β = (Q : K) by exact hprod]
  ring

/-- The square of the root difference is the discriminant `P^2 - 4 * Q`. -/
theorem lucasRoot_difference_sq_eq_discriminant {K : Type*} [CommRing K] (P Q : ℤ) (α β : K)
    (hsum : α + β = P) (hprod : α * β = Q) : (α - β) ^ 2 = (P * P - 4 * Q : ℤ) := by
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_ofNat]
  rw [show (P : K) = α + β by exact hsum.symm, show (Q : K) = α * β by exact hprod.symm]
  ring

/-- A nonsquare discriminant separates the two roots in a field. -/
theorem lucasRoot_difference_ne_zero_of_not_isSquare {K : Type*} [Field K] (P Q : ℤ) (α β : K)
    (hsum : α + β = P) (hprod : α * β = Q) (hdisc : ¬IsSquare (P * P - 4 * Q : K)) : α - β ≠ 0 := by
  intro hdiff
  apply hdisc
  refine ⟨0, ?_⟩
  have hsq := lucasRoot_difference_sq_eq_discriminant P Q α β hsum hprod
  rw [hdiff] at hsq
  norm_num only at hsq ⊢
  simpa only [Int.cast_sub, Int.cast_mul, Int.cast_ofNat] using hsq.symm

/-- A root of the quadratic with coefficients `P, Q` is one of two known roots. -/
theorem quadratic_root_eq_other_of_ne {K : Type*} [Field K] (P Q : ℤ) (α β x : K) (hsum : α + β = P)
    (hprod : α * β = Q) (hroot : x ^ 2 - (P : K) * x + (Q : K) = 0) (hne : x - α ≠ 0) : x = β := by
  have hfactor : (x - α) * (x - β) = 0 := by
    rw [show (P : K) = α + β by exact hsum.symm, show (Q : K) = α * β by exact hprod.symm] at hroot
    calc
      (x - α) * (x - β) = x ^ 2 - (α + β) * x + α * β := by ring
      _ = 0 := hroot
  exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left hne)

/-- A non-fixed Frobenius root is the other root of the quadratic. -/
theorem frobenius_root_eq_other_of_quadratic_root {K : Type*} [Field K] (p : ℕ) (P Q : ℤ) (α β : K)
    (hsum : α + β = P) (hprod : α * β = Q) (hroot : (α ^ p) ^ 2 - (P : K) * α ^ p + (Q : K) = 0)
    (hne : α ^ p - α ≠ 0) : α ^ p = β := by
  exact quadratic_root_eq_other_of_ne P Q α β (α ^ p) hsum hprod hroot hne

/-- In characteristic `p`, the Frobenius image of a quadratic root is again a root. -/
theorem frobenius_pow_is_quadratic_root {K : Type*} [Field K] (p : ℕ) [CharP K p] [Fact p.Prime]
    (P Q α : K) (hP : P ^ p = P) (hQ : Q ^ p = Q) (hroot : α ^ 2 - P * α + Q = 0) :
    (α ^ p) ^ 2 - P * α ^ p + Q = 0 := by
  have hp := congrArg (fun z : K => z ^ p) hroot
  rw [add_pow_char, sub_pow_char] at hp
  rw [← pow_mul, mul_pow, hP, hQ] at hp
  have hp0 : p ≠ 0 := (Fact.out : Nat.Prime p).ne_zero
  simpa only [pow_mul, Nat.mul_comm, pow_two, zero_pow hp0] using hp

/-- The canonical `AdjoinRoot` root has a Frobenius image satisfying the quadratic equation. -/
theorem adjoinRoot_lucasQuadratic_frobenius_root {K : Type*} [Field K] (p : ℕ) [CharP K p]
    [Fact p.Prime] (P Q : K) (hdisc : ¬IsSquare (P * P - 4 * Q)) (hP : P ^ p = P) (hQ : Q ^ p = Q) :
    (AdjoinRoot.root (lucasQuadraticPolynomial P Q) ^ p) ^ 2 -
          (P : AdjoinRoot (lucasQuadraticPolynomial P Q)) *
            AdjoinRoot.root (lucasQuadraticPolynomial P Q) ^ p +
        (Q : AdjoinRoot (lucasQuadraticPolynomial P Q)) =
      0 := by
  have hI : Fact (Irreducible (lucasQuadraticPolynomial P Q)) :=
    ⟨lucasQuadraticPolynomial_irreducible_of_not_isSquare P Q hdisc⟩
  let E := AdjoinRoot (lucasQuadraticPolynomial P Q)
  have hchar : Function.Injective (algebraMap K E) := by
    rw [AdjoinRoot.algebraMap_eq]
    exact AdjoinRoot.coe_injective'
  have hcharP : CharP E p := charP_of_injective_algebraMap hchar p
  have hP' :
    (P : AdjoinRoot (lucasQuadraticPolynomial P Q)) ^ p =
      (P : AdjoinRoot (lucasQuadraticPolynomial P Q)) := by
    simpa only [map_pow] using
      congrArg (fun z : K => (z : AdjoinRoot (lucasQuadraticPolynomial P Q))) hP
  have hQ' :
    (Q : AdjoinRoot (lucasQuadraticPolynomial P Q)) ^ p =
      (Q : AdjoinRoot (lucasQuadraticPolynomial P Q)) := by
    simpa only [map_pow] using
      congrArg (fun z : K => (z : AdjoinRoot (lucasQuadraticPolynomial P Q))) hQ
  exact
    frobenius_pow_is_quadratic_root p (P : AdjoinRoot (lucasQuadraticPolynomial P Q))
      (Q : AdjoinRoot (lucasQuadraticPolynomial P Q))
      (AdjoinRoot.root (lucasQuadraticPolynomial P Q)) hP' hQ'
      (adjoinRoot_lucasQuadratic_root_eq_zero P Q)

/-- If the canonical root is not Frobenius-fixed, its image is the trace-complement root. -/
theorem adjoinRoot_lucasQuadratic_frobenius_eq_complement {K : Type*} [Field K] (p : ℕ) [CharP K p]
    [Fact p.Prime] (P Q : K) (hdisc : ¬IsSquare (P * P - 4 * Q)) (hP : P ^ p = P) (hQ : Q ^ p = Q)
    (hne :
      (AdjoinRoot.root (lucasQuadraticPolynomial P Q)) ^ p -
          AdjoinRoot.root (lucasQuadraticPolynomial P Q) ≠
        0) :
    (AdjoinRoot.root (lucasQuadraticPolynomial P Q)) ^ p =
      (P : AdjoinRoot (lucasQuadraticPolynomial P Q)) -
        AdjoinRoot.root (lucasQuadraticPolynomial P Q) := by
  have hI : Fact (Irreducible (lucasQuadraticPolynomial P Q)) :=
    ⟨lucasQuadraticPolynomial_irreducible_of_not_isSquare P Q hdisc⟩
  have hroot := adjoinRoot_lucasQuadratic_frobenius_root p P Q hdisc hP hQ
  have hprod :
    AdjoinRoot.root (lucasQuadraticPolynomial P Q) *
        ((P : AdjoinRoot (lucasQuadraticPolynomial P Q)) -
          AdjoinRoot.root (lucasQuadraticPolynomial P Q)) =
      (Q : AdjoinRoot (lucasQuadraticPolynomial P Q)) := by
    calc
      _ =
          (Q : AdjoinRoot (lucasQuadraticPolynomial P Q)) -
            (AdjoinRoot.root (lucasQuadraticPolynomial P Q) ^ 2 -
                (P : AdjoinRoot (lucasQuadraticPolynomial P Q)) *
                  AdjoinRoot.root (lucasQuadraticPolynomial P Q) +
              (Q : AdjoinRoot (lucasQuadraticPolynomial P Q))) :=
        by ring
      _ = (Q : AdjoinRoot (lucasQuadraticPolynomial P Q)) := by
        rw [adjoinRoot_lucasQuadratic_root_eq_zero P Q, sub_zero]
  have hfactor :
    ((AdjoinRoot.root (lucasQuadraticPolynomial P Q)) ^ p -
          AdjoinRoot.root (lucasQuadraticPolynomial P Q)) *
        ((AdjoinRoot.root (lucasQuadraticPolynomial P Q)) ^ p -
          ((P : AdjoinRoot (lucasQuadraticPolynomial P Q)) -
            AdjoinRoot.root (lucasQuadraticPolynomial P Q))) =
      0 := by
    calc
      _ =
          (AdjoinRoot.root (lucasQuadraticPolynomial P Q) ^ p) ^ 2 -
              (P : AdjoinRoot (lucasQuadraticPolynomial P Q)) *
                AdjoinRoot.root (lucasQuadraticPolynomial P Q) ^ p +
            AdjoinRoot.root (lucasQuadraticPolynomial P Q) *
              ((P : AdjoinRoot (lucasQuadraticPolynomial P Q)) -
                AdjoinRoot.root (lucasQuadraticPolynomial P Q)) :=
        by ring
      _ =
          (AdjoinRoot.root (lucasQuadraticPolynomial P Q) ^ p) ^ 2 -
              (P : AdjoinRoot (lucasQuadraticPolynomial P Q)) *
                AdjoinRoot.root (lucasQuadraticPolynomial P Q) ^ p +
            (Q : AdjoinRoot (lucasQuadraticPolynomial P Q)) :=
        by rw [hprod]
      _ = 0 := hroot
  exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left hne)

/-- If the canonical root is not Frobenius-fixed, Frobenius exchanges both roots. -/
theorem adjoinRoot_lucasQuadratic_frobenius_swap {K : Type*} [Field K] (p : ℕ) [CharP K p]
    [Fact p.Prime] (P Q : K) (hdisc : ¬IsSquare (P * P - 4 * Q)) (hP : P ^ p = P) (hQ : Q ^ p = Q)
    (hne :
      (AdjoinRoot.root (lucasQuadraticPolynomial P Q)) ^ p -
          AdjoinRoot.root (lucasQuadraticPolynomial P Q) ≠
        0) :
    (AdjoinRoot.root (lucasQuadraticPolynomial P Q)) ^ p =
        (P : AdjoinRoot (lucasQuadraticPolynomial P Q)) -
          AdjoinRoot.root (lucasQuadraticPolynomial P Q) ∧
      ((P : AdjoinRoot (lucasQuadraticPolynomial P Q)) -
            AdjoinRoot.root (lucasQuadraticPolynomial P Q)) ^
          p =
        AdjoinRoot.root (lucasQuadraticPolynomial P Q) := by
  have hα := adjoinRoot_lucasQuadratic_frobenius_eq_complement p P Q hdisc hP hQ hne
  constructor
  · exact hα
  · have hP' :
      (P : AdjoinRoot (lucasQuadraticPolynomial P Q)) ^ p =
        (P : AdjoinRoot (lucasQuadraticPolynomial P Q)) := by
      simpa only [map_pow] using
        congrArg (fun z : K => (z : AdjoinRoot (lucasQuadraticPolynomial P Q))) hP
    have hI : Fact (Irreducible (lucasQuadraticPolynomial P Q)) :=
      ⟨lucasQuadraticPolynomial_irreducible_of_not_isSquare P Q hdisc⟩
    let E := AdjoinRoot (lucasQuadraticPolynomial P Q)
    have hchar : Function.Injective (algebraMap K E) := by
      rw [AdjoinRoot.algebraMap_eq]
      exact AdjoinRoot.coe_injective'
    have hcharP : CharP E p := charP_of_injective_algebraMap hchar p
    rw [sub_pow_char, hP', hα]
    ring

/-- A nonsquare quadratic over `ZMod p` has a canonical root not fixed by Frobenius. -/
theorem adjoinRoot_lucasQuadratic_frobenius_ne_self_of_not_isSquare (p : ℕ) [Fact p.Prime]
    (P Q : ZMod p) (hdisc : ¬IsSquare (P * P - 4 * Q)) :
    (AdjoinRoot.root (lucasQuadraticPolynomial P Q)) ^ p -
        AdjoinRoot.root (lucasQuadraticPolynomial P Q) ≠
      0 := by
  intro hzero
  have hfixed :
    (AdjoinRoot.root (lucasQuadraticPolynomial P Q)) ^ p =
      AdjoinRoot.root (lucasQuadraticPolynomial P Q) :=
    sub_eq_zero.mp hzero
  have hI : Irreducible (lucasQuadraticPolynomial P Q) :=
    lucasQuadraticPolynomial_irreducible_of_not_isSquare P Q hdisc
  let _ : Fact (Irreducible (lucasQuadraticPolynomial P Q)) := ⟨hI⟩
  have hdiv :
    lucasQuadraticPolynomial P Q ∣ Polynomial.X ^ (Nat.card (ZMod p)) ^ 1 - Polynomial.X := by
    have hfa :
      Polynomial.aeval (AdjoinRoot.root (lucasQuadraticPolynomial P Q))
          (lucasQuadraticPolynomial P Q) =
        0 :=
      AdjoinRoot.eval₂_root (lucasQuadraticPolynomial P Q)
    apply (hI.dvd_iff_aeval_eq_zero hfa).mp
    rw [Polynomial.aeval_sub, Polynomial.aeval_X_pow, pow_one, Nat.card_eq_fintype_card, ZMod.card,
      Polynomial.aeval_X, hfixed, sub_self]
  have hdeg : (lucasQuadraticPolynomial P Q).natDegree = 2 := by
    exact (Polynomial.isMonicOfDegree_sub_add_two P Q).natDegree_eq
  have htwo : (2 : ℕ) ∣ 1 := by
    rw [← hdeg]
    exact (hI.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X).mpr hdiv
  exact (by decide : ¬(2 : ℕ) ∣ 1) htwo

/-- Over `ZMod p`, a nonsquare quadratic has Frobenius exchanging its two roots. -/
theorem adjoinRoot_lucasQuadratic_frobenius_swap_of_not_isSquare (p : ℕ) [Fact p.Prime]
    (P Q : ZMod p) (hdisc : ¬IsSquare (P * P - 4 * Q)) :
    (AdjoinRoot.root (lucasQuadraticPolynomial P Q)) ^ p =
        (P : AdjoinRoot (lucasQuadraticPolynomial P Q)) -
          AdjoinRoot.root (lucasQuadraticPolynomial P Q) ∧
      ((P : AdjoinRoot (lucasQuadraticPolynomial P Q)) -
            AdjoinRoot.root (lucasQuadraticPolynomial P Q)) ^
          p =
        AdjoinRoot.root (lucasQuadraticPolynomial P Q) := by
  exact
    adjoinRoot_lucasQuadratic_frobenius_swap p P Q hdisc (ZMod.pow_card P) (ZMod.pow_card Q)
      (adjoinRoot_lucasQuadratic_frobenius_ne_self_of_not_isSquare p P Q hdisc)

/-- The `ZMod p` Frobenius exchange gives the Lucas `U` zero identity. -/
theorem lucasU_add_one_eq_zero_of_adjoinRoot_frobenius_swap (p : ℕ) [Fact p.Prime] (P Q : ℤ)
    (hdisc : ¬IsSquare ((P : ZMod p) * (P : ZMod p) - 4 * (Q : ZMod p))) :
    (lucasU P Q (p + 1) : AdjoinRoot (lucasQuadraticPolynomial (P : ZMod p) (Q : ZMod p))) = 0 := by
  let E := AdjoinRoot (lucasQuadraticPolynomial (P : ZMod p) (Q : ZMod p))
  have hI : Irreducible (lucasQuadraticPolynomial (P : ZMod p) (Q : ZMod p)) :=
    lucasQuadraticPolynomial_irreducible_of_not_isSquare (P : ZMod p) (Q : ZMod p) hdisc
  let _ : Fact (Irreducible (lucasQuadraticPolynomial (P : ZMod p) (Q : ZMod p))) := ⟨hI⟩
  let α : E := AdjoinRoot.root (lucasQuadraticPolynomial (P : ZMod p) (Q : ZMod p))
  let β : E := (P : ZMod p) - α
  have hcast (z : ℤ) : (z : E) = ((z : ZMod p) : E) := by
    change (z : E) = algebraMap (ZMod p) E (z : ZMod p)
    exact (map_intCast (algebraMap (ZMod p) E) z).symm
  have hswap :=
    adjoinRoot_lucasQuadratic_frobenius_swap_of_not_isSquare p (P : ZMod p) (Q : ZMod p) hdisc
  have hα : α ^ p = β := by simpa only [α, β] using hswap.1
  have hβ : β ^ p = α := by simpa only [α, β] using hswap.2
  have hsum : α + β = (P : E) := by
    dsimp [β]
    rw [hcast P]
    ring
  have hprod : α * β = (Q : E) := by
    dsimp [α, β]
    have hroot := adjoinRoot_lucasQuadratic_root_eq_zero (P : ZMod p) (Q : ZMod p)
    have hrootE : α ^ 2 - (P : E) * α + (Q : E) = 0 := by
      simpa only [α, hcast P, hcast Q] using hroot
    calc
      AdjoinRoot.root (lucasQuadraticPolynomial (P : ZMod p) (Q : ZMod p)) *
            ((P : ZMod p) - AdjoinRoot.root (lucasQuadraticPolynomial (P : ZMod p) (Q : ZMod p))) =
          (Q : E) -
            (AdjoinRoot.root (lucasQuadraticPolynomial (P : ZMod p) (Q : ZMod p)) ^ 2 -
                (P : E) * AdjoinRoot.root (lucasQuadraticPolynomial (P : ZMod p) (Q : ZMod p)) +
              (Q : E)) :=
        by
        rw [hcast P]; ring
      _ = (Q : E) := by rw [hrootE, sub_zero]
  have hne : α ^ p - α ≠ 0 := by
    simpa only [α] using
      (adjoinRoot_lucasQuadratic_frobenius_ne_self_of_not_isSquare p (P : ZMod p) (Q : ZMod p)
        hdisc)
  have hαβ : α - β ≠ 0 := by
    intro hzero
    apply hne
    exact sub_eq_zero.mpr (hα.trans (sub_eq_zero.mp hzero).symm)
  have hclosed := lucasU_root_difference_mul P Q α β hsum hprod (p + 1)
  have hpow : α ^ (p + 1) - β ^ (p + 1) = 0 := by
    rw [pow_add, pow_add, hα, hβ]
    ring
  rw [hpow] at hclosed
  exact (mul_eq_zero.mp hclosed).resolve_left hαβ

/-- The Frobenius exchange identity in the executable `ZMod` Lucas-U representation. -/
theorem lucasUZMod_prime_eq_zero (p : ℕ) [Fact p.Prime] (P Q : ℤ)
    (hdisc : ¬IsSquare ((P : ZMod p) * (P : ZMod p) - 4 * (Q : ZMod p))) :
    lucasUZMod p P Q (p + 1) = 0 := by
  rw [lucasUZMod_eq_cast]
  let E := AdjoinRoot (lucasQuadraticPolynomial (P : ZMod p) (Q : ZMod p))
  have hI : Irreducible (lucasQuadraticPolynomial (P : ZMod p) (Q : ZMod p)) :=
    lucasQuadraticPolynomial_irreducible_of_not_isSquare (P : ZMod p) (Q : ZMod p) hdisc
  let _ : Fact (Irreducible (lucasQuadraticPolynomial (P : ZMod p) (Q : ZMod p))) := ⟨hI⟩
  have hinj : Function.Injective (algebraMap (ZMod p) E) := by
    rw [AdjoinRoot.algebraMap_eq]
    exact AdjoinRoot.coe_injective'
  apply hinj
  have hU := lucasU_add_one_eq_zero_of_adjoinRoot_frobenius_swap p P Q hdisc
  simpa only [map_intCast, map_zero] using hU

/-- The `ZMod p` Frobenius exchange gives the Lucas `V` value `2 * Q`. -/
theorem lucasV_add_one_eq_two_mul_of_adjoinRoot_frobenius_swap (p : ℕ) [Fact p.Prime] (P Q : ℤ)
    (hdisc : ¬IsSquare ((P : ZMod p) * (P : ZMod p) - 4 * (Q : ZMod p))) :
    (lucasV P Q (p + 1) : AdjoinRoot (lucasQuadraticPolynomial (P : ZMod p) (Q : ZMod p))) =
      2 * (Q : AdjoinRoot (lucasQuadraticPolynomial (P : ZMod p) (Q : ZMod p))) := by
  let E := AdjoinRoot (lucasQuadraticPolynomial (P : ZMod p) (Q : ZMod p))
  have hI : Irreducible (lucasQuadraticPolynomial (P : ZMod p) (Q : ZMod p)) :=
    lucasQuadraticPolynomial_irreducible_of_not_isSquare (P : ZMod p) (Q : ZMod p) hdisc
  let _ : Fact (Irreducible (lucasQuadraticPolynomial (P : ZMod p) (Q : ZMod p))) := ⟨hI⟩
  let α : E := AdjoinRoot.root (lucasQuadraticPolynomial (P : ZMod p) (Q : ZMod p))
  let β : E := (P : ZMod p) - α
  have hcast (z : ℤ) : (z : E) = ((z : ZMod p) : E) := by
    change (z : E) = algebraMap (ZMod p) E (z : ZMod p)
    exact (map_intCast (algebraMap (ZMod p) E) z).symm
  have hswap :=
    adjoinRoot_lucasQuadratic_frobenius_swap_of_not_isSquare p (P : ZMod p) (Q : ZMod p) hdisc
  have hα : α ^ p = β := by simpa only [α, β] using hswap.1
  have hβ : β ^ p = α := by simpa only [α, β] using hswap.2
  have hsum : α + β = (P : E) := by
    dsimp [β]
    rw [hcast P]
    ring
  have hprod : α * β = (Q : E) := by
    dsimp [α, β]
    have hroot := adjoinRoot_lucasQuadratic_root_eq_zero (P : ZMod p) (Q : ZMod p)
    have hrootE : α ^ 2 - (P : E) * α + (Q : E) = 0 := by
      simpa only [α, hcast P, hcast Q] using hroot
    calc
      AdjoinRoot.root (lucasQuadraticPolynomial (P : ZMod p) (Q : ZMod p)) *
            ((P : ZMod p) - AdjoinRoot.root (lucasQuadraticPolynomial (P : ZMod p) (Q : ZMod p))) =
          (Q : E) -
            (AdjoinRoot.root (lucasQuadraticPolynomial (P : ZMod p) (Q : ZMod p)) ^ 2 -
                (P : E) * AdjoinRoot.root (lucasQuadraticPolynomial (P : ZMod p) (Q : ZMod p)) +
              (Q : E)) :=
        by
        rw [hcast P]; ring
      _ = (Q : E) := by rw [hrootE, sub_zero]
  exact lucasV_add_one_eq_two_mul_of_root_frobenius_swap p P Q α β hsum hprod hα hβ

/-- The Frobenius exchange identity in the executable `ZMod` Lucas-V representation. -/
theorem lucasVZMod_prime_eq_two_mul (p : ℕ) [Fact p.Prime] (P Q : ℤ)
    (hdisc : ¬IsSquare ((P : ZMod p) * (P : ZMod p) - 4 * (Q : ZMod p))) :
    lucasVZMod p P Q (p + 1) = 2 * (Q : ZMod p) := by
  rw [lucasVZMod_eq_cast]
  let E := AdjoinRoot (lucasQuadraticPolynomial (P : ZMod p) (Q : ZMod p))
  have hI : Irreducible (lucasQuadraticPolynomial (P : ZMod p) (Q : ZMod p)) :=
    lucasQuadraticPolynomial_irreducible_of_not_isSquare (P : ZMod p) (Q : ZMod p) hdisc
  let _ : Fact (Irreducible (lucasQuadraticPolynomial (P : ZMod p) (Q : ZMod p))) := ⟨hI⟩
  have hinj : Function.Injective (algebraMap (ZMod p) E) := by
    rw [AdjoinRoot.algebraMap_eq]
    exact AdjoinRoot.coe_injective'
  apply hinj
  have hV := lucasV_add_one_eq_two_mul_of_adjoinRoot_frobenius_swap p P Q hdisc
  have htwo : algebraMap (ZMod p) E (2 : ZMod p) = (2 : E) := map_natCast (algebraMap (ZMod p) E) 2
  rw [map_mul, htwo]
  simpa only [map_intCast] using hV

/-- Frobenius exchange of two roots forces the Lucas `U` test at `p + 1`. -/
theorem lucasU_add_one_eq_zero_of_root_frobenius_swap {K : Type*} [Field K] (p : ℕ) (P Q : ℤ)
    (α β : K) (hsum : α + β = P) (hprod : α * β = Q) (hαβ : α - β ≠ 0) (hα : α ^ p = β)
    (hβ : β ^ p = α) : (lucasU P Q (p + 1) : K) = 0 := by
  have hclosed := lucasU_root_difference_mul P Q α β hsum hprod (p + 1)
  have hpow : α ^ (p + 1) - β ^ (p + 1) = 0 := by
    rw [pow_add, pow_add, hα, hβ]
    ring
  rw [hpow] at hclosed
  exact (mul_eq_zero.mp hclosed).resolve_left hαβ

end PseudoPrime.PrimeTest
