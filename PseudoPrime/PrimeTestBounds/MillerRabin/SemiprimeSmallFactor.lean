/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.SmallPrimeSubgroup
public import PseudoPrime.NumberTheory.UnitPowerCardinality
public import PseudoPrime.NumberTheory.UnitPowerKernelProperness
public import PseudoPrime.PrimeTest.MillerRabin.LocalFermatKernel

/-! # Small-factor semiprime witnesses -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- If an odd product of distinct ordered primes has larger factor below
`(B+1)²`, one prime at most `B` rejects the original input. Otherwise its
proper local Fermat kernel would contain all small primes and minus one,
contradicting the subgroup-generation theorem. -/
theorem semiprime_small_factor_witness {n p q B : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q) (hB : 0 < B) (hsize : q < (B + 1) ^ 2) :
    ∃ r : ℕ, r.Prime ∧ r ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let : Fact q.Prime := ⟨hq⟩
  have hqn : q ∣ n := hprod ▸ dvd_mul_left q p
  have hbad : ¬q - 1 ∣ n - 1 := by
    rw [hprod]
    exact NumberTheory.not_sub_one_dvd_prime_mul_sub_one_of_lt hp hq hpq
  let H := (powMonoidHom (n - 1) : (ZMod q)ˣ →* (ZMod q)ˣ).ker
  have hproper : H ≠ ⊤ := NumberTheory.local_prime_powerKernel_ne_top_of_not_dvd hbad
  have hneg : (-1 : (ZMod q)ˣ) ∈ H := by
    change (-1 : (ZMod q)ˣ) ^ (n - 1) = 1
    exact (Nat.Odd.sub_odd ho odd_one).neg_one_pow
  by_contra hnone
  have hmem : ∀ r : ℕ, r.Prime → r ≤ B → ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (r : ZMod q) := by
    intro r hr hrB
    have hpass : PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
      by_contra hf
      exact hnone ⟨r, hr, hrB, hf⟩
    exact PrimeTest.strongMR_local_divisorKernel hn ho hqn hpass
  exact hproper (NumberTheory.subgroup_eq_top_of_small_primes hq hB hsize H hneg hmem)

end PseudoPrime.PrimeTestBounds.MillerRabin
