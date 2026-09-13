/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import PseudoPrime.PrimeTest.Selfridge.MethodAStarIdentities
import PseudoPrime.PrimeTest.Selfridge.MethodAStar
import PseudoPrime.PrimeTest.Lucas.ProbablePrime
import PseudoPrime.PrimeTest.BPSW.Defs

/-!
# Strong Lucas equivalence of Selfridge Method A and Method A*

The exceptional `D = 5` branch is handled in `ZMod n` using the integer
identities from `MethodAStarIdentities`.  The proof does not assume that `n` is
prime: the factor `5` is cancelled only after proving that it is a unit.
-/

namespace PseudoPrime.PrimeTest

private theorem unit_mul_zero_iff {R : Type} [CommMonoidWithZero R] {a b : R} (h : IsUnit a) :
    a * b = 0 ↔ b = 0 := by
  obtain ⟨u, hu⟩ := h
  rw [← hu, mul_comm]
  exact Units.mul_left_eq_zero u

private theorem lucasUZMod_methodAStar_odd_zero_iff {n m : ℕ} (hunit : IsUnit (5 : ZMod n)) :
    lucasUZMod n 5 5 (2 * m + 1) = 0 ↔ lucasVZMod n 1 (-1) (2 * m + 1) = 0 := by
  change (lucasU 5 5 (2 * m + 1) : ZMod n) = 0 ↔ (lucasV 1 (-1) (2 * m + 1) : ZMod n) = 0
  have h := congrArg (fun z : ℤ => (z : ZMod n)) (lucasU_methodAStar_odd m)
  simp only [Int.cast_mul, Int.cast_pow] at h
  norm_num at h ⊢
  rw [h]
  exact unit_mul_zero_iff (hunit.pow m)

private theorem lucasVZMod_methodAStar_odd_zero_iff {n m : ℕ} (hunit : IsUnit (5 : ZMod n)) :
    lucasVZMod n 5 5 (2 * m + 1) = 0 ↔ lucasUZMod n 1 (-1) (2 * m + 1) = 0 := by
  change (lucasV 5 5 (2 * m + 1) : ZMod n) = 0 ↔ (lucasU 1 (-1) (2 * m + 1) : ZMod n) = 0
  have h := congrArg (fun z : ℤ => (z : ZMod n)) (lucasV_methodAStar_odd m)
  simp only [Int.cast_mul, Int.cast_pow] at h
  norm_num at h ⊢
  rw [h]
  exact unit_mul_zero_iff (hunit.pow (m + 1))

private theorem lucasVZMod_methodAStar_even_zero_iff {n k : ℕ} (hunit : IsUnit (5 : ZMod n)) :
    lucasVZMod n 5 5 (2 * k) = 0 ↔ lucasVZMod n 1 (-1) (2 * k) = 0 := by
  change (lucasV 5 5 (2 * k) : ZMod n) = 0 ↔ (lucasV 1 (-1) (2 * k) : ZMod n) = 0
  have h := congrArg (fun z : ℤ => (z : ZMod n)) (lucasV_methodAStar_even k)
  simp only [Int.cast_mul, Int.cast_pow] at h
  norm_num at h ⊢
  rw [h]
  exact unit_mul_zero_iff (hunit.pow k)

private theorem strongLucas_condition_methodAStar_iff {n m s : ℕ} (hs : 0 < s)
    (hunit : IsUnit (5 : ZMod n)) :
    (lucasUZMod n 1 (-1) (2 * m + 1) = 0 ∨
        ∃ r ∈ List.range s, lucasVZMod n 1 (-1) ((2 * m + 1) * 2 ^ r) = 0) ↔
      (lucasUZMod n 5 5 (2 * m + 1) = 0 ∨
        ∃ r ∈ List.range s, lucasVZMod n 5 5 ((2 * m + 1) * 2 ^ r) = 0) := by
  constructor
  · intro h
    rcases h with hu | ⟨r, hr, hv⟩
    · right
      refine ⟨0, List.mem_range.mpr hs, ?_⟩
      simpa only [pow_zero, Nat.mul_one] using (lucasVZMod_methodAStar_odd_zero_iff hunit).mpr hu
    · cases r with
      | zero =>
        left
        apply (lucasUZMod_methodAStar_odd_zero_iff hunit).mpr
        simpa only [pow_zero, Nat.mul_one] using hv
      | succ r =>
        right
        refine ⟨r + 1, hr, ?_⟩
        have heven := lucasVZMod_methodAStar_even_zero_iff (n := n) (k := (2 * m + 1) * 2 ^ r) hunit
        have hv' : lucasVZMod n 1 (-1) (2 * ((2 * m + 1) * 2 ^ r)) = 0 := by
          simpa only [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hv
        simpa only [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using heven.mpr hv'
  · intro h
    rcases h with hu | ⟨r, hr, hv⟩
    · right
      refine ⟨0, List.mem_range.mpr hs, ?_⟩
      simpa only [pow_zero, Nat.mul_one] using (lucasUZMod_methodAStar_odd_zero_iff hunit).mp hu
    · cases r with
      | zero =>
        left
        apply (lucasVZMod_methodAStar_odd_zero_iff hunit).mp
        simpa only [pow_zero, Nat.mul_one] using hv
      | succ r =>
        right
        refine ⟨r + 1, hr, ?_⟩
        have heven := lucasVZMod_methodAStar_even_zero_iff (n := n) (k := (2 * m + 1) * 2 ^ r) hunit
        have hv' : lucasVZMod n 5 5 (2 * ((2 * m + 1) * 2 ^ r)) = 0 := by
          simpa only [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hv
        simpa only [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using heven.mp hv'

private theorem isStrongLucas_methodAStar_params_iff {n : ℕ}
    (hindex : lucasProbablePrimeIndex n 5 = n + 1) (hd : Odd (oddPart (n + 1)))
    (hs : 0 < twoAdicExponent (n + 1)) (hunit : IsUnit (5 : ZMod n)) :
    IsStrongLucasProbablePrime n ⟨5, 1, -1, by norm_num⟩ ↔
      IsStrongLucasProbablePrime n ⟨5, 5, 5, by norm_num⟩ := by
  change
    (lucasUZMod n 1 (-1) (oddPart (lucasProbablePrimeIndex n 5)) = 0 ∨
        ∃ r ∈ List.range (twoAdicExponent (lucasProbablePrimeIndex n 5)),
          lucasVZMod n 1 (-1) (oddPart (lucasProbablePrimeIndex n 5) * 2 ^ r) = 0) ↔
      (lucasUZMod n 5 5 (oddPart (lucasProbablePrimeIndex n 5)) = 0 ∨
        ∃ r ∈ List.range (twoAdicExponent (lucasProbablePrimeIndex n 5)),
          lucasVZMod n 5 5 (oddPart (lucasProbablePrimeIndex n 5) * 2 ^ r) = 0)
  simp only [hindex]
  rcases hd with ⟨m, hm⟩
  rw [hm]
  exact strongLucas_condition_methodAStar_iff hs hunit

private theorem oddPart_succ_odd_of_odd {n : ℕ} (_hn : Odd n) : Odd (oddPart (n + 1)) := by
  apply oddPart_odd
  omega

private theorem twoAdicExponent_succ_pos_of_odd {n : ℕ} (hn : Odd n) :
    0 < twoAdicExponent (n + 1) := by
  by_contra hs
  have hs0 : twoAdicExponent (n + 1) = 0 := Nat.eq_zero_of_not_pos hs
  have hfac := twoAdicPart_mul_oddPart (n + 1)
  rw [hs0, pow_zero, one_mul] at hfac
  have hd := oddPart_odd (show n + 1 ≠ 0 by omega)
  rw [hfac] at hd
  rcases hn with ⟨k, hk⟩
  rcases hd with ⟨l, hl⟩
  omega

/-- The two parameterized Strong Lucas tests agree in the exceptional D = 5 branch. -/
theorem strongLucasMethodAStar_eq_methodA_of_five {n : ℕ} (hmod : (1 - (5 : ℤ)) % 4 = 0)
    (hindex : lucasProbablePrimeIndex n 5 = n + 1) (hd : Odd (oddPart (n + 1)))
    (hs : 0 < twoAdicExponent (n + 1)) (hunit : IsUnit (5 : ZMod n)) :
    strongLucasMethodAStar n 5 hmod = strongLucasMethodA n 5 hmod := by
  have hspecA := strongLucasWithParams_eq_true_iff n 5 1 (-1) (by norm_num)
  have hspecAStar := strongLucasWithParams_eq_true_iff n 5 5 5 (by norm_num)
  have hprop := isStrongLucas_methodAStar_params_iff hindex hd hs hunit
  have htrue : strongLucasWithParams n 5 5 5 = true ↔ strongLucasWithParams n 5 1 (-1) = true := by
    rw [hspecAStar, hspecA]
    simpa only [LucasParams.ofDiscriminant] using hprop.symm
  change strongLucasWithParams n 5 5 5 = strongLucasWithParams n 5 1 (-1)
  cases hA : strongLucasWithParams n 5 5 5 with
  | false =>
    cases hB : strongLucasWithParams n 5 1 (-1) with
    | false => rfl
    | true =>
      exfalso
      have hh := htrue
      rw [hA, hB] at hh
      exact Bool.false_ne_true (hh.mpr rfl)
  | true =>
    cases hB : strongLucasWithParams n 5 1 (-1) with
    | false =>
      exfalso
      have hh := htrue
      rw [hA, hB] at hh
      exact Bool.false_ne_true (hh.mp rfl)
    | true => rfl

/-- Method A and Method A* have the same Strong Lucas result, including D = 5. -/
theorem strongLucasMethodAStar_eq_methodA {n : ℕ} (hn : Odd n) {D : ℤ} (hmod : (1 - D) % 4 = 0)
    (hjacobi : jacobiSym D n = -1) :
    strongLucasMethodAStar n D hmod = strongLucasMethodA n D hmod := by
  by_cases hD : D = 5
  · subst D
    have hunit : IsUnit (5 : ZMod n) := by
      have h := lucasDiscriminant_isUnit_of_jacobi_neg_one hjacobi
      norm_num at h ⊢
      exact h
    exact
      strongLucasMethodAStar_eq_methodA_of_five hmod
        (lucasProbablePrimeIndex_of_jacobi_eq_neg_one hjacobi) (oddPart_succ_odd_of_odd hn)
        (twoAdicExponent_succ_pos_of_odd hn) hunit
  · exact strongLucasMethodAStar_eq_methodA_of_ne_five n hmod hD

/-- The converse orientation of the Method A / Method A* Strong Lucas equivalence. -/
theorem strongLucasMethodA_eq_methodAStar {n : ℕ} (hn : Odd n) {D : ℤ} (hmod : (1 - D) % 4 = 0)
    (hjacobi : jacobiSym D n = -1) :
    strongLucasMethodA n D hmod = strongLucasMethodAStar n D hmod := by
  exact (strongLucasMethodAStar_eq_methodA hn hmod hjacobi).symm

/-- The BPSW composition inherits the D = 5 Method A / A* Strong Lucas equality. -/
theorem bailliePSWWithParams_methodAStar_eq_methodA_of_five {n : ℕ} (hn : Odd n)
    (hjacobi : jacobiSym 5 n = -1) :
    bailliePSWWithParams n 5 5 5 = bailliePSWWithParams n 5 1 (-1) := by
  have hsl := strongLucasMethodAStar_eq_methodA hn (by norm_num) hjacobi
  change strongLucasWithParams n 5 5 5 = strongLucasWithParams n 5 1 (-1) at hsl
  change
    (strongMillerRabinBase2WithPrecheck n && strongLucasWithParams n 5 5 5) =
      (strongMillerRabinBase2WithPrecheck n && strongLucasWithParams n 5 1 (-1))
  rw [hsl]

end PseudoPrime.PrimeTest
