/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.PrimeProductMultisetCounting
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeProductCountingBounds

/-! # MR witnesses from products with repeated prime factors -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- If every ambient MR pass maps into `H`, the repeated-prime product count
and the bound `B ^ k < q` yield a rejecting prime from `S` when the count exceeds
`card H`. Apply the subgroup criterion and the given inclusion of passes. -/
theorem exists_prime_witness_of_multichoose {n q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (S : Finset ℕ) (k B : ℕ) (hB : 1 ≤ B) (hprime : ∀ p ∈ S, Nat.Prime p) (hbound : ∀ p ∈ S, p ≤ B)
    (hsize : B ^ k < q) (hcount : Nat.card H < Nat.choose (S.card + k) k)
    (hpass :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
          ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (a : ZMod q)) :
    ∃ p : ℕ, p.Prime ∧ p ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, _, hp, hb, hout⟩ :=
    NumberTheory.exists_prime_outside_of_multichoose H S k B hB hprime hbound hsize hcount
  exact ⟨p, hp, hb, fun hyes ↦ hout (hpass p hyes)⟩

/-- For an odd input divisible by an odd prime power, a repeated-prime product
count exceeding `p - 1` supplies a rejecting prime. Bound the local Fermat kernel
by its exact gcd cardinality and transport ambient MR passes into that kernel. -/
theorem exists_prime_primePow_multichoose {n p a : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hp2 : p ≠ 2) (ha : 0 < a) (hdiv : p ^ a ∣ n) (S : Finset ℕ) (k B : ℕ) (hB : 1 ≤ B)
    (hprime : ∀ r ∈ S, Nat.Prime r) (hbound : ∀ r ∈ S, r ≤ B) (hsize : B ^ k < p ^ a)
    (hcount : p - 1 < Nat.choose (S.card + k) k) :
    ∃ r : ℕ, r.Prime ∧ r ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let : NeZero (p ^ a) := ⟨pow_ne_zero a hp.ne_zero⟩
  let H := (powMonoidHom (n - 1) : (ZMod (p ^ a))ˣ →* (ZMod (p ^ a))ˣ).ker
  have hcard : Nat.card H < Nat.choose (S.card + k) k := by
    rw [card_local_fermat_kernel_prime_pow hn hp hp2 ha hdiv]
    exact (Nat.gcd_le_left (n - 1) (Nat.sub_pos_of_lt hp.one_lt)).trans_lt hcount
  obtain ⟨r, _, hr, hb, hout⟩ :=
    NumberTheory.exists_prime_outside_of_multichoose H S k B hB hprime hbound hsize hcard
  exact ⟨r, hr, hb, fun hrp ↦ hout (PrimeTest.strongMR_local_divisorKernel hn ho hdiv hrp)⟩

/-- For an odd prime power dividing the odd input, a repeated-prime product
count exceeding the exact local kernel size `gcd (p - 1) (n - 1)` yields an MR
rejecting prime. Preserve the gcd rather than replacing it by `p - 1`; the
sharper form is needed when a second prime factor controls the kernel. -/
theorem exists_prime_primePow_multichoose_gcd {n p a : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hp2 : p ≠ 2) (ha : 0 < a) (hdiv : p ^ a ∣ n) (S : Finset ℕ) (k B : ℕ) (hB : 1 ≤ B)
    (hprime : ∀ r ∈ S, Nat.Prime r) (hbound : ∀ r ∈ S, r ≤ B) (hsize : B ^ k < p ^ a)
    (hcount : (p - 1).gcd (n - 1) < Nat.choose (S.card + k) k) :
    ∃ r : ℕ, r.Prime ∧ r ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let : NeZero (p ^ a) := ⟨pow_ne_zero a hp.ne_zero⟩
  apply
    exists_prime_witness_of_multichoose
      (powMonoidHom (n - 1) : (ZMod (p ^ a))ˣ →* (ZMod (p ^ a))ˣ).ker S k B hB hprime hbound hsize
  · rw [card_local_fermat_kernel_prime_pow hn hp hp2 ha hdiv]
    exact hcount
  · exact fun r hr ↦ PrimeTest.strongMR_local_divisorKernel hn ho hdiv hr

end PseudoPrime.PrimeTestBounds.MillerRabin
