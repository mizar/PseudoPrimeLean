/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.HeilbronnSmoothExtraction
public import PseudoPrime.NumberTheory.PrimeProductSubgroupCounting

/-! # Squarefree prime products as distinct smooth integers -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- If S consists of primes at most B and B^s<=k, its s-subsets give distinct
(B+1)-smooth integers up to k. Use prime-product injectivity without any modular reduction. -/
theorem choose_le_smoothNumbersUpTo_card {S : Finset ℕ} {B k s : ℕ} (hprime : ∀ q ∈ S, q.Prime)
    (hbound : ∀ q ∈ S, q ≤ B) (hsize : B ^ s ≤ k) :
    Nat.choose S.card s ≤ (Nat.smoothNumbersUpTo k (B + 1)).card := by
  classical
  rw [← Finset.card_powersetCard]
  apply Finset.card_le_card_of_injOn (fun T : Finset ℕ ↦ T.prod id)
  · intro T hT
    have ht := Finset.mem_powersetCard.mp hT
    apply Nat.mem_smoothNumbersUpTo.mpr
    refine ⟨?_, Nat.mem_smoothNumbers'.mpr ?_⟩
    · have h := Finset.prod_le_prod (fun q hq ↦ hbound q (ht.1 hq))
      rw [Finset.prod_const, ht.2] at h
      exact h.trans hsize
    · intro q hq hqd
      obtain ⟨r, hr, hqr⟩ := hq.prime.dvd_finsetProd_iff id |>.mp hqd
      have he : r = q := ((hprime r (ht.1 hr)).dvd_iff_eq hq.ne_one).mp hqr
      exact he ▸ Nat.lt_succ_of_le (hbound r (ht.1 hr))
  · intro T hT U hU he
    exact
      NumberTheory.prime_finset_product_injective
        (fun q hq ↦ hprime q ((Finset.mem_powersetCard.mp hT).1 hq))
        (fun q hq ↦ hprime q ((Finset.mem_powersetCard.mp hU).1 hq)) he

end PseudoPrime.NumberTheory.Heilbronn
