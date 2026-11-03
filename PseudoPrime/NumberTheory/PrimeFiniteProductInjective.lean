/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.Nat.Prime.Basic

/-! # Injectivity of products of finite sets of primes -/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- Equal products of finite sets of primes have equal supports. Prime divisibility
and primality identify each factor. Used to distinguish squarefree products in counting. -/
theorem prime_finset_product_injective {S T : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (hT : ∀ p ∈ T, Nat.Prime p) (he : S.prod id = T.prod id) : S = T := by
  have hsub :
    ∀ (U V : Finset ℕ),
      (∀ p ∈ U, Nat.Prime p) → (∀ p ∈ V, Nat.Prime p) → U.prod id = V.prod id → U ⊆ V := by
    intro U V hU hV hprod p hp
    have hd : p ∣ V.prod id := hprod ▸ Finset.dvd_prod_of_mem id hp
    obtain ⟨r, hr, hpr⟩ := (hU p hp).prime.dvd_finsetProd_iff id |>.mp hd
    exact ((hV r hr).dvd_iff_eq (hU p hp).ne_one).mp hpr ▸ hr
  exact Finset.Subset.antisymm (hsub S T hS hT he) (hsub T S hT hS he.symm)

end PseudoPrime.NumberTheory
