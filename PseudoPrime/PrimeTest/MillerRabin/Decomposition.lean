/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.PrimeTest.MillerRabin.Spec
import Mathlib.Tactic.Ring
import Mathlib.Tactic

/-!
# Arbitrary decompositions for the strong Miller–Rabin condition
-/

namespace PseudoPrime.PrimeTest

/--
The strong-test acceptance condition for an explicit decomposition `n - 1 = 2^s * d` and a
residue `x`. Acceptance means either the odd-part power is one or an indicated repeated square is
minus one.
-/
def StrongMillerRabinPass (n s d : ℕ) (x : ZMod n) : Prop :=
  x ^ d = 1 ∨ ∃ j : ℕ, j < s ∧ x ^ (2 ^ j * d) = -1

/-- Every accepted residue satisfies the Fermat power equation for the supplied decomposition. -/
theorem strongMillerRabinPass_pow_decomp {n s d : ℕ} {x : ZMod n}
    (hdecomp : n - 1 = 2 ^ s * d)
    (hpass : StrongMillerRabinPass n s d x) :
    x ^ (n - 1) = 1 := by
  rcases hpass with hodd | ⟨j, hj, hneg⟩
  · calc
      x ^ (n - 1) = x ^ (2 ^ s * d) := by rw [hdecomp]
      _ = (x ^ d) ^ (2 ^ s) := by rw [Nat.mul_comm, pow_mul]
      _ = 1 := by rw [hodd, one_pow]
  · have hexp : (2 ^ j * d) * 2 ^ (s - j) = 2 ^ s * d := by
      calc
        (2 ^ j * d) * 2 ^ (s - j) = 2 ^ j * 2 ^ (s - j) * d := by ring
        _ = 2 ^ (j + (s - j)) * d := by rw [Nat.pow_add]
        _ = 2 ^ s * d := by rw [Nat.add_sub_of_le hj.le]
    have hpositive : 0 < s - j := Nat.sub_pos_of_lt hj
    have heven : Even (2 ^ (s - j)) :=
      (show Even 2 from ⟨1, by rfl⟩).pow_of_ne_zero (Nat.ne_of_gt hpositive)
    calc
      x ^ (n - 1) = x ^ (2 ^ s * d) := by rw [hdecomp]
      _ = x ^ ((2 ^ j * d) * 2 ^ (s - j)) := by rw [hexp]
      _ = (x ^ (2 ^ j * d)) ^ (2 ^ (s - j)) := by rw [pow_mul]
      _ = (-1) ^ (2 ^ (s - j)) := by rw [hneg]
      _ = 1 := heven.neg_one_pow

/-- A residue accepted under a positive exponent decomposition is a unit modulo `n`. -/
theorem strongMillerRabinPass_isUnit {n s d : ℕ} {x : ZMod n}
    (hn : 1 < n)
    (hdecomp : n - 1 = 2 ^ s * d)
    (hpass : StrongMillerRabinPass n s d x) :
    IsUnit x := by
  have hpow := strongMillerRabinPass_pow_decomp hdecomp hpass
  rw [isUnit_iff_exists]
  refine ⟨x ^ (n - 2), ?_, ?_⟩
  · rw [mul_comm x (x ^ (n - 2)), ← pow_succ]
    rw [show n - 2 + 1 = n - 1 by omega, hpow]
  · rw [← pow_succ, show n - 2 + 1 = n - 1 by omega, hpow]

/--
Failure of the arbitrary-decomposition pass condition is exactly the two witness inequalities.
-/
theorem not_strongMillerRabinPass_iff {n s d : ℕ} {x : ZMod n} :
    ¬ StrongMillerRabinPass n s d x ↔
      x ^ d ≠ 1 ∧ ∀ j : ℕ, j < s → x ^ (2 ^ j * d) ≠ -1 := by
  constructor
  · intro hfail
    constructor
    · intro hone
      exact hfail (Or.inl hone)
    · intro j hj hminus
      exact hfail (Or.inr ⟨j, hj, hminus⟩)
  · rintro ⟨hone, hminus⟩ (hpass | ⟨j, hj, hpass⟩)
    · exact hone hpass
    · exact hminus j hj hpass

/--
The existing Miller–Rabin specification is the arbitrary-decomposition pass predicate at the
computed odd part and two-adic exponent.
-/
theorem isStrongMillerRabinProbablePrime_iff_pass {n a : ℕ} :
    IsStrongMillerRabinProbablePrime n a ↔
      StrongMillerRabinPass n (twoAdicExponent (n - 1)) (oddPart (n - 1)) (a : ZMod n) := by
  change ((a : ZMod n) ^ oddPart (n - 1) = 1 ∨
      ∃ r ∈ List.range (twoAdicExponent (n - 1)),
        (a : ZMod n) ^ (oddPart (n - 1) * 2 ^ r) = (n - 1 : ZMod n)) ↔
    ((a : ZMod n) ^ oddPart (n - 1) = 1 ∨
      ∃ r, r < twoAdicExponent (n - 1) ∧
        (a : ZMod n) ^ (2 ^ r * oddPart (n - 1)) = -1)
  constructor
  · rintro (hodd | ⟨r, hr, hpow⟩)
    · exact Or.inl hodd
    · right
      refine ⟨r, List.mem_range.mp hr, ?_⟩
      rw [Nat.mul_comm] at hpow
      rw [ZMod.natCast_self, zero_sub] at hpow
      exact hpow
  · rintro (hodd | ⟨r, hr, hpow⟩)
    · exact Or.inl hodd
    · right
      refine ⟨r, List.mem_range.mpr hr, ?_⟩
      rw [Nat.mul_comm, hpow, ZMod.natCast_self, zero_sub]

/-- An odd factorization of `m` by a power of two is its computed maximal-power decomposition. -/
theorem twoAdicExponent_eq_and_oddPart_eq_of_decomp {m s d : ℕ}
    (hm : m ≠ 0)
    (hdecomp : m = 2 ^ s * d)
    (hdOdd : Odd d) :
    twoAdicExponent m = s ∧ oddPart m = d := by
  have hdvd : ¬2 ∣ d := by
    intro hdiv
    exact (Nat.not_even_iff_odd.mpr hdOdd) (even_iff_two_dvd.mpr hdiv)
  have hmax := Nat.maxPowDvdDiv_of_pow_mul_eq hm hdecomp.symm hdvd
  constructor
  · change padicValNat 2 m = s
    calc
      padicValNat 2 m = (Nat.maxPowDvdDiv 2 m).1 :=
        (Nat.fst_maxPowDvdDiv 2 m).symm
      _ = s := congrArg Prod.fst hmax
  · change Nat.divMaxPow m 2 = d
    calc
      Nat.divMaxPow m 2 = (Nat.maxPowDvdDiv 2 m).2 :=
        (Nat.snd_maxPowDvdDiv 2 m).symm
      _ = d := congrArg Prod.snd hmax

/-- Any admissible odd decomposition agrees with the computed Miller–Rabin decomposition. -/
theorem strongMillerRabinPass_iff_computed {n s d : ℕ} {x : ZMod n}
    (hn : 1 < n)
    (hdecomp : n - 1 = 2 ^ s * d)
    (hdOdd : Odd d) :
    StrongMillerRabinPass n s d x ↔
      StrongMillerRabinPass n (twoAdicExponent (n - 1)) (oddPart (n - 1)) x := by
  have hm : n - 1 ≠ 0 := Nat.sub_ne_zero_of_lt hn
  obtain ⟨hs, hd⟩ := twoAdicExponent_eq_and_oddPart_eq_of_decomp hm hdecomp hdOdd
  rw [← hs, ← hd]

/-- The executable test accepts exactly the pass predicate for any admissible decomposition. -/
theorem strongMillerRabinWithBase_eq_true_iff_pass_decomp {n s d a : ℕ}
    (hn : 1 < n)
    (hdecomp : n - 1 = 2 ^ s * d)
    (hdOdd : Odd d) :
    strongMillerRabinWithBase n a = true ↔
      StrongMillerRabinPass n s d (a : ZMod n) := by
  exact (strongMillerRabinWithBase_eq_true_iff).trans
    (isStrongMillerRabinProbablePrime_iff_pass.trans
      (strongMillerRabinPass_iff_computed hn hdecomp hdOdd).symm)

/-- A prime base dividing `n` cannot satisfy any admissible strong-test pass condition. -/
theorem strongMillerRabinPass_not_of_prime_dvd {n s d p : ℕ}
    (hn : 1 < n)
    (hdecomp : n - 1 = 2 ^ s * d)
    (hp : Nat.Prime p)
    (hdiv : p ∣ n) :
    ¬ StrongMillerRabinPass n s d (p : ZMod n) := by
  intro hpass
  have hunit := strongMillerRabinPass_isUnit hn hdecomp hpass
  have hcop : Nat.Coprime p n := (ZMod.isUnit_iff_coprime p n).mp hunit
  exact (hp.coprime_iff_not_dvd.mp hcop) hdiv

/-- Every modulus greater than one has a prime factor that fails the strong-test conditions. -/
theorem exists_prime_factor_strongMillerRabin_witness {n s d : ℕ}
    (hn : 1 < n)
    (hdecomp : n - 1 = 2 ^ s * d) :
    ∃ p : ℕ, Nat.Prime p ∧ p ∣ n ∧
      (p : ZMod n) ^ d ≠ 1 ∧
      ∀ j : ℕ, j < s → (p : ZMod n) ^ (2 ^ j * d) ≠ -1 := by
  obtain ⟨p, hp, hdiv⟩ := Nat.exists_prime_and_dvd (Nat.ne_of_gt hn)
  refine ⟨p, hp, hdiv, ?_⟩
  exact (not_strongMillerRabinPass_iff.mp
    (strongMillerRabinPass_not_of_prime_dvd hn hdecomp hp hdiv))

/-- Boolean rejection is equivalent to failure of the arbitrary-decomposition pass predicate. -/
theorem strongMillerRabinWithBase_eq_false_iff_not_pass_decomp {n s d a : ℕ}
    (hn : 1 < n)
    (hdecomp : n - 1 = 2 ^ s * d)
    (hdOdd : Odd d) :
    strongMillerRabinWithBase n a = false ↔
      ¬ StrongMillerRabinPass n s d (a : ZMod n) := by
  constructor
  · intro hfalse hpass
    have htrue := (strongMillerRabinWithBase_eq_true_iff_pass_decomp hn hdecomp hdOdd).2 hpass
    rw [hfalse] at htrue
    cases htrue
  · intro hnot
    cases htest : strongMillerRabinWithBase n a with
    | false => rfl
    | true => exact False.elim (hnot
        ((strongMillerRabinWithBase_eq_true_iff_pass_decomp hn hdecomp hdOdd).1 htest))

end PseudoPrime.PrimeTest
