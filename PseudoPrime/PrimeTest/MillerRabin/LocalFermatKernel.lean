/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.WitnessSubgroupCardinality

/-! # Local power-kernel transfer for strong MR passes

The exponent is the ambient predecessor n-1, not the local predecessor p-1.
Every ambient strong pass reduces into the local power kernel.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest

/-- Every ambient strong MR pass reduces into the ambient-predecessor
power kernel at any nonzero divisor modulus q. Preserve unitness and the
Fermat identity through the canonical reduction. This includes prime-square
moduli for the finite-index square-factor branch. -/
theorem strongMR_local_divisorKernel {n q a : ℕ} [NeZero q] (hn : 1 < n) (hnOdd : Odd n)
    (hqn : q ∣ n) (hpass : StrongMillerRabinPass n (a : ZMod n)) :
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

/-- Every strong MR pass modulo odd n>1 reduces into the (n-1)-power
kernel modulo a prime factor p. Map unitness and the Fermat power identity
through the canonical reduction, then choose the local unit representative.
This supplies local subgroup containment with the ambient exponent preserved. -/
theorem strongMR_local_primeKernel {n p a : ℕ} [Fact p.Prime] (hn : 1 < n) (hnOdd : Odd n)
    (hpn : p ∣ n) (hpass : StrongMillerRabinPass n (a : ZMod n)) :
    ∃ u : (ZMod p)ˣ,
      u ∈ (powMonoidHom (n - 1) : (ZMod p)ˣ →* (ZMod p)ˣ).ker ∧ (u : ZMod p) = (a : ZMod p) := by
  let : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  exact strongMR_local_divisorKernel hn hnOdd hpn hpass

end PseudoPrime.PrimeTest
