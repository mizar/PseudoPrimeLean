/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.Walk
import Mathlib.Algebra.BigOperators.Group.List.Lemmas

/-! # Scalar coprimality tests for high joint certificate segments -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- Product of the primes through 1000 for scalar coprimality tests above that cutoff. -/
def baseProduct : ℕ :=
  basePrimes.toList.prod

private theorem not_dvd_product {n : ℕ} (hp : n.Prime) (xs : List ℕ)
    (hr : ∀ q ∈ xs, 0 < q ∧ q < n) : ¬n ∣ xs.prod := by
  induction xs with
  | nil => exact hp.not_dvd_one
  | cons q qs ih =>
    intro hd
    rcases hp.dvd_mul.mp (show n ∣ q * qs.prod from hd) with h | h
    · have hq := hr q List.mem_cons_self
      exact (Nat.not_le_of_lt hq.2) (Nat.le_of_dvd hq.1 h)
    · exact ih (fun v hv ↦ hr v (List.mem_cons_of_mem q hv)) h

/-- Above 1000, an integer through one million is prime precisely when it is coprime
to the shared product: every composite has a prime divisor at most its square root. -/
theorem gcd_one_iff {n : ℕ} (hl : 1000 < n) (hu : n ≤ 1000000) :
    n.gcd baseProduct = 1 ↔ n.Prime := by
  constructor
  · intro hg
    by_contra hp
    obtain ⟨p, hm, _, hd⟩ := composite_has_base (by linarith only [hl]) hu hp
    have hb : p ∣ baseProduct :=
      List.dvd_prod (Array.mem_toList_iff.mpr (Array.contains_iff_mem.mp hm))
    exact ((baseHas_iff p).mp hm).2.not_dvd_one (hg ▸ Nat.dvd_gcd hd hb)
  · intro hp
    apply hp.coprime_iff_not_dvd.mpr
    apply not_dvd_product hp
    intro q hq
    have h := (baseHas_iff q).mp (Array.contains_iff_mem.mpr (Array.mem_toList_iff.mp hq))
    exact ⟨h.2.pos, Nat.lt_of_lt_of_le h.1 hl⟩

/-- Use one gcd per query on the high segment and the shared exceptional-power lookup.
Outside its certified interval the original selector supplies the value. -/
def gcdStep (a b : ℕ) (s : Edge) : Edge :=
  if 1000 < s.n ∧ s.n ≤ 1000000 ∧ a ≤ s.n ∧ s.n < b then
    advance certifiedTicks s (if s.n.gcd baseProduct = 1 then s.n else powerAt a b s.n)
  else segmentStep a b s

/-- Replacing the sieve query with the scalar gcd test preserves each update exactly. -/
theorem gcdStep_eq (a b : ℕ) : gcdStep a b = segmentStep a b := by
  funext s
  unfold gcdStep
  split
  next ht =>
    obtain ⟨hl, hu, ha, hb⟩ := ht
    have hb' : ¬b ≤ 101 := by linarith only [hl, hb]
    rw [segmentStep, ite_eq_right hb', markerAt]
    by_cases hp : s.n.Prime
    · rw [ite_eq_left ((gcd_one_iff hl hu).2 hp), ite_eq_left ((sieveFlag_iff ha hb hu).2 hp)]
    · rw [ite_eq_right (fun h ↦ hp ((gcd_one_iff hl hu).1 h)),
        ite_eq_right (fun h ↦ hp ((sieveFlag_iff ha hb hu).1 h))]
  next => rfl

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
