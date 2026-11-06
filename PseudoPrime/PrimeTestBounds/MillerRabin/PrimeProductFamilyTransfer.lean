/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.PrimeProductFamilyCounting
public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedPrimeFamily
public import PseudoPrime.PrimeTest.MillerRabin.LocalFermatKernel
public import PseudoPrime.NumberTheory.AmbientFermatKernel
public import PseudoPrime.NumberTheory.ProductFermatKernel

/-! # Transfer of selected repeated-product counts to MR witnesses -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A finite family of prime multisets whose products lie below the local
modulus yields an MR rejecting prime when its cardinality exceeds that of a
subgroup containing all local passing residues. The count allows repeated
factors and arbitrary selection, including selection by grouped weights. -/
theorem exists_prime_reject_of_multiset_family {n q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (S : Finset ℕ) (F : Finset (Multiset ℕ)) (B : ℕ) (hsub : ∀ T ∈ F, ∀ p ∈ T, p ∈ S)
    (hprime : ∀ p ∈ S, Nat.Prime p) (hbound : ∀ p ∈ S, p ≤ B) (hsize : ∀ T ∈ F, T.prod < q)
    (hcount : Nat.card H < F.card)
    (hpass :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
          ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (a : ZMod q)) :
    ∃ p : ℕ, p.Prime ∧ p ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  classical
  by_contra hnone
  have hmem : ∀ p ∈ S, ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (p : ZMod q) := by
    intro p hp
    apply hpass
    by_contra hf
    exact hnone ⟨p, hprime p hp, hbound p hp, hf⟩
  exact
    (not_lt_of_ge (NumberTheory.prime_multiset_family_le_card H S F hsub hprime hsize hmem)) hcount

/-- If a weight-selected prime-multiset family exceeds the local subgroup
cardinality and its cost budget lies below the logarithm of the modulus, it
contains enough distinct products to force an MR rejecting prime. The weights
can vary across the prime supply. -/
theorem exists_prime_reject_of_weighted_family {n q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (S : Finset ℕ) (F : Finset (Multiset ℕ)) (B budget : ℕ) (w : ℕ → ℕ) (d : ℝ) (hd : 0 < d)
    (hq : 0 < q) (hsub : ∀ T ∈ F, ∀ p ∈ T, p ∈ S) (hprime : ∀ p ∈ S, Nat.Prime p)
    (hbound : ∀ p ∈ S, p ≤ B) (hw : ∀ p ∈ S, Real.log p ≤ (w p : ℝ) / d)
    (hcost : ∀ T ∈ F, (T.map w).sum ≤ budget) (hbudget : (budget : ℝ) / d < Real.log q)
    (hcount : Nat.card H < F.card)
    (hpass :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
          ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (a : ZMod q)) :
    ∃ p : ℕ, p.Prime ∧ p ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply exists_prime_reject_of_multiset_family H S F B hsub hprime hbound
  · intro T hT
    exact
      NumberTheory.multiset_prod_lt_of_weight T w d budget q hd hq
        (fun p hp ↦ (hprime p (hsub T hT p hp)).pos) (fun p hp ↦ hw p (hsub T hT p hp)) (hcost T hT)
        hbudget
  · exact hcount
  · exact hpass

/-- The complete positive-weight family forces a rejecting prime whenever its
cardinality exceeds the local subgroup and its budget is below the logarithm
of the modulus. The family membership theorem supplies all support and cost
conditions required by the weighted transfer. -/
theorem exists_prime_reject_of_weight_budget {n q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (S : Finset ℕ) (B budget : ℕ) (w : ℕ → ℕ) (d : ℝ) (hd : 0 < d) (hq : 0 < q)
    (hp : ∀ p ∈ S, Nat.Prime p) (hbound : ∀ p ∈ S, p ≤ B) (hwpos : ∀ p ∈ S, 1 ≤ w p)
    (hw : ∀ p ∈ S, Real.log p ≤ (w p : ℝ) / d) (hbudget : (budget : ℝ) / d < Real.log q)
    (hcount : Nat.card H < (weightedPrimeFamily S w budget).card)
    (hpass :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
          ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (a : ZMod q)) :
    ∃ p : ℕ, p.Prime ∧ p ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    exists_prime_reject_of_weighted_family H S (weightedPrimeFamily S w budget) B budget w d hd hq
  · intro T hT
    exact (mem_weightedPrimeFamily S w budget hwpos T).mp hT |>.1
  · exact hp
  · exact hbound
  · exact hw
  · intro T hT
    exact (mem_weightedPrimeFamily S w budget hwpos T).mp hT |>.2
  · exact hbudget
  · exact hcount
  · exact hpass

/-- A weighted family of fixed-length padded prime multisets gives the same
local counting criterion as the unpadded family. Removing padding preserves
its cardinality, so a certified count can feed the rejecting-prime transfer. -/
theorem exists_prime_reject_of_padded_family {n q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (S : Finset ℕ) (k : ℕ) (G : Finset (Sym (Option ↥S) k)) (B budget : ℕ) (w : ℕ → ℕ) (d : ℝ)
    (hd : 0 < d) (hq : 0 < q) (hp : ∀ p ∈ S, Nat.Prime p) (hbound : ∀ p ∈ S, p ≤ B)
    (hw : ∀ p ∈ S, Real.log p ≤ (w p : ℝ) / d)
    (hcost :
      ∀ t ∈ G,
        ((((t.map (fun x ↦ x.elim 1 Subtype.val)).filterNe 1).2 : Multiset ℕ).map w).sum ≤ budget)
    (hbudget : (budget : ℝ) / d < Real.log q) (hcount : Nat.card H < G.card)
    (hpass :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
          ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (a : ZMod q)) :
    ∃ p : ℕ, p.Prime ∧ p ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨F, hcard, hsub, hrepr⟩ := NumberTheory.exists_prime_family_of_padded S k G hp
  apply exists_prime_reject_of_weighted_family H S F B budget w d hd hq hsub hp hbound hw
  · intro T hT
    obtain ⟨t, ht, rfl⟩ := hrepr T hT
    exact hcost t ht
  · exact hbudget
  · exact hcard ▸ hcount
  · exact hpass

/-- For an odd input divisible by an odd prime power, a family of prime
multisets with products below that power yields a rejecting prime when its
size exceeds `p - 1`. The ambient Fermat kernel has at most that cardinality. -/
theorem exists_prime_reject_prime_pow_family {n p a : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hp2 : p ≠ 2) (ha : 0 < a) (hdiv : p ^ a ∣ n) (S : Finset ℕ) (F : Finset (Multiset ℕ)) (B : ℕ)
    (hsub : ∀ T ∈ F, ∀ r ∈ T, r ∈ S) (hprime : ∀ r ∈ S, Nat.Prime r) (hbound : ∀ r ∈ S, r ≤ B)
    (hsize : ∀ T ∈ F, T.prod < p ^ a) (hcount : p - 1 < F.card) :
    ∃ r : ℕ, r.Prime ∧ r ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let : NeZero (p ^ a) := ⟨pow_ne_zero a hp.ne_zero⟩
  apply
    exists_prime_reject_of_multiset_family
      (powMonoidHom (n - 1) : (ZMod (p ^ a))ˣ →* (ZMod (p ^ a))ˣ).ker S F B hsub hprime hbound hsize
  · rw [NumberTheory.card_local_fermat_kernel_prime_pow hn hp hp2 ha hdiv]
    exact (Nat.gcd_le_left (n - 1) (Nat.sub_pos_of_lt hp.one_lt)).trans_lt hcount
  · exact fun r hr ↦ PrimeTest.strongMR_local_divisorKernel hn ho hdiv hr

/-- For an odd input divisible by an odd prime power, a weighted family whose
budget lies below the logarithm of the power gives a rejecting prime when the
family has more than `p - 1` elements. This uses the original input's Fermat
kernel and applies in particular to every input divisible by `p²`. -/
theorem exists_prime_reject_prime_pow_weighted {n p a : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hp2 : p ≠ 2) (ha : 0 < a) (hdiv : p ^ a ∣ n) (S : Finset ℕ) (F : Finset (Multiset ℕ))
    (B budget : ℕ) (w : ℕ → ℕ) (d : ℝ) (hd : 0 < d) (hsub : ∀ T ∈ F, ∀ r ∈ T, r ∈ S)
    (hprime : ∀ r ∈ S, Nat.Prime r) (hbound : ∀ r ∈ S, r ≤ B)
    (hw : ∀ r ∈ S, Real.log r ≤ (w r : ℝ) / d) (hcost : ∀ T ∈ F, (T.map w).sum ≤ budget)
    (hbudget : (budget : ℝ) / d < Real.log ((p ^ a : ℕ) : ℝ)) (hcount : p - 1 < F.card) :
    ∃ r : ℕ, r.Prime ∧ r ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let : NeZero (p ^ a) := ⟨pow_ne_zero a hp.ne_zero⟩
  apply
    exists_prime_reject_of_weighted_family
      (powMonoidHom (n - 1) : (ZMod (p ^ a))ˣ →* (ZMod (p ^ a))ˣ).ker S F B budget w d hd
      (pow_pos hp.pos a) hsub hprime hbound hw hcost hbudget
  · rw [NumberTheory.card_local_fermat_kernel_prime_pow hn hp hp2 ha hdiv]
    exact (Nat.gcd_le_left (n - 1) (Nat.sub_pos_of_lt hp.one_lt)).trans_lt hcount
  · exact fun r hr ↦ PrimeTest.strongMR_local_divisorKernel hn ho hdiv hr

/-- A logarithmic lower certificate for a natural count implies that the
count exceeds `p - 1` whenever it is at least `log p`. Positivity excludes the
zero-count case before logarithmic monotonicity is inverted. -/
theorem pred_lt_count_of_log {p C : ℕ} (hp : p.Prime) {D : ℝ} (hpD : Real.log p ≤ D)
    (hD : D ≤ Real.log (C : ℝ)) : p - 1 < C := by
  have hpos : 0 < C := by
    by_contra h
    have hz : C = 0 := Nat.eq_zero_of_not_pos h
    rw [hz, Nat.cast_zero, Real.log_zero] at hD
    have hpLog : 0 < Real.log p := Real.log_pos (Nat.one_lt_cast.mpr hp.one_lt)
    exact (not_le_of_gt hpLog) (hpD.trans hD)
  have hle : p ≤ C := by
    exact_mod_cast
      (Real.log_le_log_iff (Nat.cast_pos.mpr hp.pos) (Nat.cast_pos.mpr hpos)).mp (hpD.trans hD)
  exact (Nat.sub_lt hp.pos (by decide : 0 < 1)).trans_le hle

/-- A weighted family with a logarithmic count certificate gives a rejecting
prime for every odd input divisible by the indicated odd prime power. The
budget is strictly below the power's logarithm, while the count certificate
reaches the logarithm of the underlying prime. -/
theorem exists_prime_reject_prime_pow_log_count {n p a : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hp2 : p ≠ 2) (ha : 0 < a) (hdiv : p ^ a ∣ n) (S : Finset ℕ) (F : Finset (Multiset ℕ))
    (B budget : ℕ) (w : ℕ → ℕ) (d : ℝ) (hd : 0 < d) (hsub : ∀ T ∈ F, ∀ r ∈ T, r ∈ S)
    (hprime : ∀ r ∈ S, Nat.Prime r) (hbound : ∀ r ∈ S, r ≤ B)
    (hw : ∀ r ∈ S, Real.log r ≤ (w r : ℝ) / d) (hcost : ∀ T ∈ F, (T.map w).sum ≤ budget)
    (hbudget : (budget : ℝ) / d < Real.log ((p ^ a : ℕ) : ℝ)) {D : ℝ} (hpD : Real.log p ≤ D)
    (hD : D ≤ Real.log (F.card : ℝ)) :
    ∃ r : ℕ, r.Prime ∧ r ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) :=
  exists_prime_reject_prime_pow_weighted hn ho hp hp2 ha hdiv S F B budget w d hd hsub hprime hbound
    hw hcost hbudget (pred_lt_count_of_log hp hpD hD)

/-- A weighted family of repeated prime products yields an MR rejecting
prime for `n = p * q` when its budget is below `log q` and its count exceeds
`p`. The ambient Fermat kernel modulo `q` has cardinality at most `p - 1`. -/
theorem exists_prime_reject_semiprime_weighted {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hprod : n = p * q) (S : Finset ℕ) (F : Finset (Multiset ℕ)) (B budget : ℕ)
    (w : ℕ → ℕ) (d : ℝ) (hd : 0 < d) (hsub : ∀ T ∈ F, ∀ r ∈ T, r ∈ S)
    (hprime : ∀ r ∈ S, Nat.Prime r) (hbound : ∀ r ∈ S, r ≤ B)
    (hw : ∀ r ∈ S, Real.log r ≤ (w r : ℝ) / d) (hcost : ∀ T ∈ F, (T.map w).sum ≤ budget)
    (hbudget : (budget : ℝ) / d < Real.log q) (hcount : p < F.card) :
    ∃ r : ℕ, r.Prime ∧ r ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hqn : q ∣ n := hprod ▸ dvd_mul_left q p
  have hq2 : q ≠ 2 := ho.ne_two_of_dvd_nat hqn
  let : NeZero (q ^ 1) := ⟨pow_ne_zero 1 hq.ne_zero⟩
  have hqpow : q ^ 1 ∣ n := by simpa only [pow_one] using hqn
  have hcard :
    Nat.card (powMonoidHom (n - 1) : (ZMod (q ^ 1))ˣ →* (ZMod (q ^ 1))ˣ).ker < F.card := by
    rw [NumberTheory.card_local_fermat_kernel_prime_pow hn hq hq2 (by decide : 0 < 1) hqpow, hprod,
      Nat.mul_comm p q]
    exact
      (NumberTheory.gcd_predecessor_product_le_cofactor hq.pos hp.one_lt).trans_lt
        ((Nat.sub_le p 1).trans_lt hcount)
  exact
    exists_prime_reject_of_weighted_family _ S F B budget w d hd (pow_pos hq.pos 1) hsub hprime
      hbound hw hcost (by simpa only [pow_one] using hbudget) hcard
      (fun a ha ↦ PrimeTest.strongMR_local_divisorKernel hn ho hqpow ha)

end PseudoPrime.PrimeTestBounds.MillerRabin
