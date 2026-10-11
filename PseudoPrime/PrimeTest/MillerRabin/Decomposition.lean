/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.Spec
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic

/-!
# Canonical decomposition for the strong Miller–Rabin condition
-/

@[expose] public section

namespace PseudoPrime.PrimeTest

/-- For `1 < n` and odd `n`, the canonical decomposition of `n - 1` has a positive
two-adic exponent, an odd residual factor, and product `n - 1`. The proof obtains positivity
from `2 ∣ n - 1`; later pass and subgroup proofs use all three facts. -/
theorem odd_sub_canonical_decomp {n : ℕ} (hn : 1 < n) (hnOdd : Odd n) :
    0 < padicValNat 2 (n - 1) ∧
      Odd (Nat.divMaxPow (n - 1) 2) ∧
      n - 1 = 2 ^ padicValNat 2 (n - 1) * Nat.divMaxPow (n - 1) 2 := by
  have hne : n - 1 ≠ 0 := Nat.sub_ne_zero_of_lt hn
  have htwo : 2 ∣ n - 1 := even_iff_two_dvd.mp (Nat.Odd.sub_odd hnOdd odd_one)
  exact
    ⟨one_le_padicValNat_of_dvd hne htwo, oddPart_odd hne,
      (Nat.pow_padicValNat_mul_divMaxPow 2 (n - 1)).symm⟩

/-- The strong Miller–Rabin pass condition using `s = padicValNat 2 (n - 1)` and
`d = Nat.divMaxPow (n - 1) 2`. A residue passes when `x^d = 1` or one of the `s`
repeated-square powers is `-1`. This is the proof-side predicate for the public base test. -/
def StrongMillerRabinPass (n : ℕ) (x : ZMod n) : Prop :=
  x ^ Nat.divMaxPow (n - 1) 2 = 1 ∨
    ∃ j : ℕ, j < padicValNat 2 (n - 1) ∧ x ^ (2 ^ j * Nat.divMaxPow (n - 1) 2) = -1

/-- For `1 < n` and odd `n`, a canonical strong-test pass satisfies `x^(n - 1) = 1`.
The initial-one branch raises to `2^s`; a minus-one branch raises to the remaining even power.
The unit and subgroup results consume this Fermat equation. -/
theorem strongMillerRabinPass_pow {n : ℕ} {x : ZMod n} (hn : 1 < n) (hnOdd : Odd n)
    (hpass : StrongMillerRabinPass n x) : x ^ (n - 1) = 1 := by
  rcases hSdPair : Nat.maxPowDvdDiv 2 (n - 1) with ⟨s, d⟩
  have hdecomp := (odd_sub_canonical_decomp hn hnOdd).2.2
  simp only [StrongMillerRabinPass, padicValNat, Nat.divMaxPow, hSdPair] at hdecomp hpass
  rw [hdecomp]
  rcases hpass with hodd | ⟨j, hj, hneg⟩
  · rw [Nat.mul_comm, pow_mul, hodd, one_pow]
  · rw [← pow_mul_pow_sub 2 hj.le, Nat.mul_right_comm, pow_mul, hneg]
    exact
      ((show Even 2 from ⟨1, rfl⟩).pow_of_ne_zero (Nat.ne_of_gt (Nat.sub_pos_of_lt hj))).neg_one_pow

/-- For `1 < n` and odd `n`, a passing residue is a unit modulo `n`.
Its inverse is witnessed by `x^(n - 2)` using `strongMillerRabinPass_pow`;
the subgroup and prime-factor results use this unit representative. -/
theorem strongMillerRabinPass_isUnit {n : ℕ} {x : ZMod n} (hn : 1 < n) (hnOdd : Odd n)
    (hpass : StrongMillerRabinPass n x) : IsUnit x := by
  have hpow := strongMillerRabinPass_pow hn hnOdd hpass
  have hsub : n - 2 + 1 = n - 1 := by
    have hpos : 0 < n - 1 := Nat.sub_pos_of_lt hn
    have hle : 1 ≤ n - 1 := Nat.succ_le_iff.mpr hpos
    calc
      n - 2 + 1 = (n - 1) - 1 + 1 := by rw [Nat.sub_sub]
      _ = n - 1 := Nat.sub_add_cancel hle
  rw [isUnit_iff_exists]
  refine ⟨x ^ (n - 2), ?_, ?_⟩
  · rw [mul_comm x (x ^ (n - 2)), ← pow_succ]
    rw [hsub, hpow]
  · rw [← pow_succ, hsub, hpow]

/-- Failure of the canonical strong test is the pair of inequalities `x^d ≠ 1` and
`x^(2^j d) ≠ -1` for every `j < s`, with `s, d` computed from `n - 1`.
This logical equivalence supplies the proof-side witness condition. -/
theorem not_strongMillerRabinPass_iff {n : ℕ} {x : ZMod n} :
    ¬StrongMillerRabinPass n x ↔
      x ^ Nat.divMaxPow (n - 1) 2 ≠ 1 ∧
        ∀ j : ℕ, j < padicValNat 2 (n - 1) → x ^ (2 ^ j * Nat.divMaxPow (n - 1) 2) ≠ -1 := by
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

/-- The existing `IsStrongMillerRabinProbablePrime` specification equals the canonical
pass predicate. The proof converts `List.range` membership into `r < s`, commutes
`d * 2^r` to `2^r * d`, and identifies the residue of `n - 1` with `-1`. -/
theorem isStrongMillerRabinProbablePrime_iff_pass {n a : ℕ} :
    IsStrongMillerRabinProbablePrime n a ↔ StrongMillerRabinPass n (a : ZMod n) := by
  simp only [IsStrongMillerRabinProbablePrime, StrongMillerRabinPass, Nat.fst_maxPowDvdDiv,
    Nat.snd_maxPowDvdDiv, zmodPowProof_eq_pow, List.mem_range, ZMod.natCast_self, zero_sub,
    Nat.mul_comm]

/-- The executable single-base test returns `true` exactly when its residue satisfies the
canonical proof-side pass predicate. This composes the existing Boolean specification with
`isStrongMillerRabinProbablePrime_iff_pass`. -/
theorem strongMillerRabinWithBase_eq_true_iff_pass {n a : ℕ} :
    strongMillerRabinWithBase n a = true ↔ StrongMillerRabinPass n (a : ZMod n) :=
  strongMillerRabinWithBase_eq_true_iff.trans isStrongMillerRabinProbablePrime_iff_pass

/-- If `1 < n` is odd and prime `p` divides `n`, the residue of `p` fails the canonical
strong test. A pass would make it a unit and hence coprime to `n`, contradicting `p ∣ n`.
This supplies the small-factor witness branch. -/
theorem strongMillerRabinPass_not_of_prime_dvd {n p : ℕ} (hn : 1 < n) (hnOdd : Odd n)
    (hp : Nat.Prime p) (hdiv : p ∣ n) : ¬StrongMillerRabinPass n (p : ZMod n) := by
  intro hpass
  have hunit := strongMillerRabinPass_isUnit hn hnOdd hpass
  have hcop : Nat.Coprime p n := (ZMod.isUnit_iff_coprime p n).mp hunit
  exact (hp.coprime_iff_not_dvd.mp hcop) hdiv

/-- Every odd `n > 1` has a prime divisor whose residue violates both canonical pass
branches. Choose a prime factor and apply `strongMillerRabinPass_not_of_prime_dvd`, then
expand the negated pass condition. This is the unbounded factor-witness interface. -/
theorem exists_prime_factor_strongMillerRabin_witness {n : ℕ} (hn : 1 < n) (hnOdd : Odd n) :
    let (s, d) := Nat.maxPowDvdDiv 2 (n - 1)
    ∃ p : ℕ,
      Nat.Prime p ∧
        p ∣ n ∧ (p : ZMod n) ^ d ≠ 1 ∧ ∀ j : ℕ, j < s → (p : ZMod n) ^ (2 ^ j * d) ≠ -1 := by
  obtain ⟨p, hp, hdiv⟩ := Nat.exists_prime_and_dvd (Nat.ne_of_gt hn)
  refine ⟨p, hp, hdiv, ?_⟩
  exact not_strongMillerRabinPass_iff.mp (strongMillerRabinPass_not_of_prime_dvd hn hnOdd hp hdiv)

/-- The executable single-base test returns `false` exactly when the canonical pass
predicate fails. The proof uses the accepted-case equivalence and Boolean case analysis;
finite certificates and explicit witness bounds consume this rejection interface. -/
theorem strongMillerRabinWithBase_eq_false_iff_not_pass {n a : ℕ} :
    strongMillerRabinWithBase n a = false ↔ ¬StrongMillerRabinPass n (a : ZMod n) := by
  constructor
  · intro hfalse hpass
    have htrue :=
      strongMillerRabinWithBase_eq_true_iff.mpr
        (isStrongMillerRabinProbablePrime_iff_pass.mpr hpass)
    rw [hfalse] at htrue
    cases htrue
  · intro hnot
    cases htest : strongMillerRabinWithBase n a with
    | false => rfl
    | true =>
      exact
        False.elim
          (hnot
            (isStrongMillerRabinProbablePrime_iff_pass.mp
              (strongMillerRabinWithBase_eq_true_iff.mp htest)))

end PseudoPrime.PrimeTest
