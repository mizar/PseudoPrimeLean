/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedCountWitness

/-! # Prime-power witnesses directly from weighted count tables -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- An odd input divisible by an odd prime power has a bounded rejecting prime
when a checked weighted count table has more than `p - 1` products and its
budget is below the logarithm of the power. The kernel uses the original input. -/
theorem exists_prime_reject_prime_pow_table {n p a : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hp2 : p ≠ 2) (ha : 0 < a) (hdiv : p ^ a ∣ n) (xs weights : List ℕ) (B budget N : ℕ) (w : ℕ → ℕ)
    (d : ℝ) (hd : 0 < d) (hnodup : xs.Nodup) (hprime : ∀ r ∈ xs, r.Prime) (hcut : ∀ r ∈ xs, r ≤ B)
    (hwpos : ∀ r ∈ xs, 0 < w r) (hw : ∀ r ∈ xs, Real.log r ≤ (w r : ℝ) / d)
    (he : xs.map w = weights) (hN : budget ≤ N) (row : Array ℕ) (rows : List (Array ℕ))
    (hcheck : weightedPrimeTableCheck N weights (row :: rows) = true)
    (hbudget : (budget : ℝ) / d < Real.log ((p ^ a : ℕ) : ℝ)) (hcount : p - 1 < row.getD budget 0) :
    ∃ r : ℕ, r.Prime ∧ r ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let : NeZero (p ^ a) := ⟨pow_ne_zero a hp.ne_zero⟩
  let H := (powMonoidHom (n - 1) : (ZMod (p ^ a))ˣ →* (ZMod (p ^ a))ˣ).ker
  have hcard : Nat.card H < row.getD budget 0 := by
    change Nat.card (powMonoidHom (n - 1) : (ZMod (p ^ a))ˣ →* (ZMod (p ^ a))ˣ).ker < _
    rw [NumberTheory.card_local_fermat_kernel_prime_pow hn hp hp2 ha hdiv]
    exact (Nat.gcd_le_left (n - 1) (Nat.sub_pos_of_lt hp.one_lt)).trans_lt hcount
  exact
    exists_prime_reject_of_weight_table H xs weights B budget N w d hd (pow_pos hp.pos a) hnodup
      hprime hcut hwpos hw he hbudget hN row rows hcheck hcard
      (fun r hr ↦ PrimeTest.strongMR_local_divisorKernel hn ho hdiv hr)

end PseudoPrime.PrimeTestBounds.MillerRabin
