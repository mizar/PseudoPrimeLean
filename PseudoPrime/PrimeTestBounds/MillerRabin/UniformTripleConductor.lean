/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.UniformKorseltSubgroup
public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaSignedPrefixBounds

/-! # Conductor and parity data for uniform Korselt triples -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Three distinct odd primes satisfying the Korselt divisibility conditions and
equal predecessor two-adic valuations determine one subgroup with index four,
strong-pass containment, conductor-log sum `2 * log n`, and even annihilator
characters. The existing conductor data and the negative-one pass give these
properties for the same subgroup. -/
theorem uniformTriple_even_conductor {n p q r : ℕ} [NeZero n] (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) (hpOdd : Odd p) (hqOdd : Odd q) (hrOdd : Odd r) (hpq : p ≠ q) (hpr : p ≠ r)
    (hqr : q ≠ r) (hn : n = p * q * r) (hpdiv : p - 1 ∣ n - 1) (hqdiv : q - 1 ∣ n - 1)
    (hrdiv : r - 1 ∣ n - 1) (hpv : padicValNat 2 (p - 1) = padicValNat 2 (q - 1))
    (hprv : padicValNat 2 (p - 1) = padicValNat 2 (r - 1)) :
    ∃ H : Subgroup (ZMod n)ˣ,
      H.index = 4 ∧
        (∀ z : ZMod n,
          PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z) ∧
        LLS.PaperStatements.subgroupConductorLogSum H = 2 * Real.log n ∧
        (∀ χ : NumberTheory.subgroupAnnihilator H, χ.val.Even) := by
  have hn1 : 1 < n :=
    hn ▸
      hp.one_lt.trans_le
        ((Nat.le_mul_of_pos_right p hq.pos).trans (Nat.le_mul_of_pos_right (p * q) hr.pos))
  have hodd : Odd n := hn ▸ (hpOdd.mul hqOdd).mul hrOdd
  obtain ⟨H, hi, hpass, hcond⟩ :=
    three_prime_korselt_conductor_subgroup_data hp hq hr hpOdd hqOdd hrOdd hpq hpr hqr hn hpdiv
      hqdiv hrdiv hpv hprv
  exact ⟨H, hi, hpass, hcond, annihilator_even_of_containing_strong_passes hn1 hodd H hpass⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
