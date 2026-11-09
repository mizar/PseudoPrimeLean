/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed1849
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed1849Count
public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedSemiprimeCount
public import PseudoPrime.PrimeTestBounds.MillerRabin.SemiprimeCoreSupplies

/-! # Grouped weighted prime supply through 1409 -/

@[expose] public section

-- The finite supply contains more than two hundred labels.
set_option maxRecDepth 32768

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Retain the 149 extra labels at most 1409 and the original supply through 373. -/
def target028Seed1409Primes : List ℕ :=
  primeSeed1849Extra.drop 60 ++ primeSeed373Primes

/-- All 149 additional labels use the already certified common weight 76. -/
def target028Seed1409Weights : List ℕ :=
  List.replicate 149 76 ++ primeSeed373Weights

/-- The reduced labels are distinct, with the existing positive weights. -/
theorem target028_seed1409_labels :
    target028Seed1409Primes.Nodup ∧
      target028Seed1409Primes.map primeSeed1849Weight = target028Seed1409Weights ∧
      ∀ p ∈ target028Seed1409Primes, 0 < primeSeed1849Weight p := by
  decide +kernel

/-- Every reduced label occurs in the certified supply through 1849. -/
theorem target028_seed1409_subset : ∀ p ∈ target028Seed1409Primes, p ∈ primeSeed1849Primes := by
  intro p hp
  simp only [target028Seed1409Primes, primeSeed1849Primes, List.mem_append] at hp ⊢
  exact hp.imp List.mem_of_mem_drop id

/-- The reduced labels are prime and at most 1409; the bound is checked
finitely and primality is inherited from the larger certified supply. -/
theorem target028_seed1409_supply : ∀ p ∈ target028Seed1409Primes, p.Prime ∧ p ≤ 1409 := by
  have hbound : ∀ p ∈ target028Seed1409Primes, p ≤ 1409 := by decide +kernel
  intro p hp
  exact ⟨(primeSeed1849_prime_supply p (target028_seed1409_subset p hp)).1, hbound p hp⟩

/-- The 149 equal-weight labels multiply the existing base count by a
multichoose factor at the extended budget. -/
theorem target028_seed1409_count (A k : ℕ) (hA : A ≤ 500) :
    Nat.choose (149 + k) k * primeSeed373Row14.getD A 0 ≤
      weightedPrimeCount id target028Seed1409Weights (A + k * 76) := by
  have hb := primeSeed373_count_lower A hA
  have hg := weightedPrimeCount_group_lower 76 A 149 k primeSeed373Weights (by decide)
  exact (Nat.mul_le_mul_left (Nat.choose (149 + k) k) hb).trans hg

/-- The grouped supply yields a semiprime witness when its cutoff, count,
and local envelope are below the requested bound. -/
theorem exists_prime_reject_semiprime_seed1409 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (A k : ℕ) (hA : A ≤ 500)
    {D X : ℝ} (hD : D ≤ Real.log ((Nat.choose (149 + k) k * primeSeed373Row14.getD A 0 : ℕ) : ℝ))
    (hB : (1409 : ℝ) ≤ X)
    (hlocal : localFullEnvelope (max (((A + k * 76 : ℕ) : ℝ) / 10) (Real.log n - D)) ≤ X) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact
    exists_prime_reject_semiprime_count_lower hn ho hp hq hpq hprod hGRH target028Seed1409Primes
      target028Seed1409Weights 1409 (A + k * 76) primeSeed1849Weight 10 (by norm_num only)
      target028_seed1409_labels.1 (fun r hr ↦ (target028_seed1409_supply r hr).1)
      (fun r hr ↦ (target028_seed1409_supply r hr).2) target028_seed1409_labels.2.2
      (fun r hr ↦ primeSeed1849_weight_bounds r (target028_seed1409_subset r hr))
      target028_seed1409_labels.2.1 (Nat.choose (149 + k) k * primeSeed373Row14.getD A 0)
      (target028_seed1409_count A k hA) hD hB hlocal

end PseudoPrime.PrimeTestBounds.MillerRabin
