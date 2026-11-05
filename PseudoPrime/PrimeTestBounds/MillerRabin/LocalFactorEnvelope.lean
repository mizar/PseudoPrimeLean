/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.LocalEnvelopeContinuous
public import PseudoPrime.PrimeTestBounds.MillerRabin.MarkedFactorLogBounds

/-! # Common local envelope for a non-Korselt prime factor -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, an odd `n > 1` with a prime divisor `r` violating the Korselt
divisibility condition has a rejecting prime within the common local envelope
at any scale at least `log r`. Oddness excludes `r = 2` and `r = 3`; the local
power kernel is then proper and contains every strong passing residue. This
connects the common envelope to factor-type coverage. -/
theorem exists_prime_reject_nonKorselt_local {n r : ℕ} (hn : 1 < n) (ho : Odd n) (hr : r.Prime)
    (hrn : r ∣ n) (hbad : ¬r - 1 ∣ n - 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {s : ℝ} (hs : Real.log r ≤ s) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ localFullEnvelope s ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hr3 : r ≠ 3 := by
    intro he
    apply hbad
    have ht : 2 ∣ n - 1 := even_iff_two_dvd.mp (Nat.Odd.sub_odd ho odd_one)
    simpa only [he, show (3 - 1 : ℕ) = 2 by decide] using ht
  have hr5 := hr.five_le_of_ne_two_of_ne_three (ho.ne_two_of_dvd_nat hrn) hr3
  let : Fact r.Prime := ⟨hr⟩
  let : NeZero r := ⟨hr.ne_zero⟩
  exact
    exists_prime_reject_local_full hn ho hr5 hrn (powMonoidHom (n - 1) : (ZMod r)ˣ →* (ZMod r)ˣ).ker
      (NumberTheory.local_prime_powerKernel_ne_top_of_not_dvd hbad)
      (fun a ha ↦ PrimeTest.strongMR_local_primeKernel hn ho hrn ha) hGRH hs

end PseudoPrime.PrimeTestBounds.MillerRabin
