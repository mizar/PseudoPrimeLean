/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.WitnessSubgroupCardinality

/-! # Local power kernels for the non-Korselt MR branch

The exponent is the ambient predecessor n-1, not the local predecessor p-1.
A prime's cyclic unit group detects properness, and every ambient strong pass
reduces into the local power kernel.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest

/-- At a prime p, the E-power kernel is proper if p-1 does not divide E.
A full kernel would annihilate every unit, forcing the cyclic group exponent
p-1 to divide E. This is the local non-Korselt subgroup for MR. -/
theorem local_prime_powerKernel_ne_top_of_not_dvd {p E : ℕ} [Fact p.Prime] (hdiv : ¬p - 1 ∣ E) :
    (powMonoidHom E : (ZMod p)ˣ →* (ZMod p)ˣ).ker ≠ ⊤ := by
  intro htop
  have hall : ∀ u : (ZMod p)ˣ, u ^ E = 1 := by
    intro u
    exact MonoidHom.mem_ker.mp (htop.symm ▸ Subgroup.mem_top u)
  have hexp := Monoid.exponent_dvd_of_forall_pow_eq_one hall
  rw [IsCyclic.exponent_eq_card, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
    Nat.totient_prime (Fact.out : p.Prime)] at hexp
  exact hdiv hexp

/-- Every strong MR pass modulo odd n>1 reduces into the (n-1)-power
kernel modulo a prime factor p. Map unitness and the Fermat power identity
through the canonical reduction, then choose the local unit representative.
This supplies local subgroup containment with the ambient exponent preserved. -/
theorem strongMillerRabinPass_mem_local_prime_powerKernel {n p a : ℕ} [Fact p.Prime] (hn : 1 < n)
    (hnOdd : Odd n) (hpn : p ∣ n) (hpass : StrongMillerRabinPass n (a : ZMod n)) :
    ∃ u : (ZMod p)ˣ,
      u ∈ (powMonoidHom (n - 1) : (ZMod p)ˣ →* (ZMod p)ˣ).ker ∧ (u : ZMod p) = (a : ZMod p) := by
  let f := ZMod.castHom hpn (ZMod p)
  have hunit := f.isUnit_map (strongMillerRabinPass_isUnit hn hnOdd hpass)
  rw [map_natCast] at hunit
  have hpow := congrArg f (strongMillerRabinPass_pow hn hnOdd hpass)
  rw [map_pow, map_one, map_natCast] at hpow
  refine ⟨hunit.unit, ?_, hunit.unit_spec⟩
  change hunit.unit ^ (n - 1) = 1
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, hunit.unit_spec, Units.val_one]
  exact hpow

/-- Every ambient strong MR pass reduces into the ambient-predecessor
power kernel at any nonzero divisor modulus q. Preserve unitness and the
Fermat identity through the canonical reduction. This includes prime-square
moduli for the finite-index square-factor branch. -/
theorem strongMillerRabinPass_mem_local_divisor_powerKernel {n q a : ℕ} [NeZero q] (hn : 1 < n)
    (hnOdd : Odd n) (hqn : q ∣ n) (hpass : StrongMillerRabinPass n (a : ZMod n)) :
    ∃ u : (ZMod q)ˣ,
      u ∈ (powMonoidHom (n - 1) : (ZMod q)ˣ →* (ZMod q)ˣ).ker ∧ (u : ZMod q) = (a : ZMod q) := by
  let f := ZMod.castHom hqn (ZMod q)
  have hunit := f.isUnit_map (strongMillerRabinPass_isUnit hn hnOdd hpass)
  rw [map_natCast] at hunit
  have hpow := congrArg f (strongMillerRabinPass_pow hn hnOdd hpass)
  rw [map_pow, map_one, map_natCast] at hpow
  refine ⟨hunit.unit, ?_, hunit.unit_spec⟩
  change hunit.unit ^ (n - 1) = 1
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, hunit.unit_spec, Units.val_one]
  exact hpow

end PseudoPrime.PrimeTest
