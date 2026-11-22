/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.PrimeBases
public import Mathlib.Algebra.IsPrimePow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.ByContra

/-! # Completeness bounds for the shared segmented sieve -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- A composite from two through one million has a marked base whose square
is at most the composite, so starting the sieve at its square suffices. -/
theorem composite_has_base {n : ℕ} (hl : 2 ≤ n) (hu : n ≤ 1000000) (hc : ¬n.Prime) :
    ∃ p, baseHas p = true ∧ p ^ 2 ≤ n ∧ p ∣ n := by
  have hp := Nat.minFac_prime (show n ≠ 1 by linarith only [hl])
  have hs := Nat.minFac_sq_le_self (show 0 < n by linarith only [hl]) hc
  have hb : n.minFac < 1001 := by
    by_contra! hh
    exact (by decide : ¬1001 ^ 2 ≤ 1000000) ((Nat.pow_le_pow_left hh 2).trans (hs.trans hu))
  exact ⟨_, (baseHas_iff _).2 ⟨hb, hp⟩, hs, Nat.minFac_dvd n⟩

/-- Each nonprime prime power through one million occurs among the small prime
bases and exponents two through nineteen. -/
theorem composite_power_range {n : ℕ} (hn : n ≤ 1000000) (hc : ¬n.Prime) (hp : IsPrimePow n) :
    ∃ p k : ℕ, p ≤ 1000 ∧ 2 ≤ k ∧ k < 20 ∧ p.Prime ∧ p ^ k = n := by
  obtain ⟨p, k, hpr, hk, he⟩ := (isPrimePow_nat_iff n).mp hp
  have hk' : 2 ≤ k := by
    by_contra! h
    have hk1 : k = 1 := by linarith only [hk, h]
    exact hc ((by simpa only [hk1, pow_one] using he : p = n) ▸ hpr)
  have hsq := (Nat.pow_le_pow_right hpr.pos hk').trans (he.le.trans hn)
  have hb : p ≤ 1000 := by
    by_contra! hh
    exact (by decide : ¬1001 ^ 2 ≤ 1000000) ((Nat.pow_le_pow_left hh 2).trans hsq)
  have ht : k < 20 := by
    by_contra! hh
    exact
      (by decide : ¬2 ^ 20 ≤ 1000000)
        (((Nat.pow_le_pow_left hpr.two_le 20).trans (Nat.pow_le_pow_right hpr.pos hh)).trans
          (he.le.trans hn))
  exact ⟨p, k, hb, hk', ht, hpr, he⟩

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
