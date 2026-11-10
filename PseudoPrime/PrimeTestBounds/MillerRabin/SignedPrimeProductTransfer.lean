/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.SignedPrimeProductCounting
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeProductFamilyTransfer

/-! # Signed weighted prime-product transfers to MR witnesses -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- If twice a prime-multiset family's size exceeds a local subgroup
containing minus one, then one supplied prime rejects the original input.
The products must be less than half the local modulus so both signs are
distinct. -/
theorem exists_prime_reject_of_signed_family {n q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (S : Finset ℕ) (F : Finset (Multiset ℕ)) (B : ℕ) (hneg : (-1 : (ZMod q)ˣ) ∈ H)
    (hsub : ∀ T ∈ F, ∀ p ∈ T, p ∈ S) (hprime : ∀ p ∈ S, Nat.Prime p) (hbound : ∀ p ∈ S, p ≤ B)
    (hsize : ∀ T ∈ F, 2 * T.prod < q) (hcount : Nat.card H < 2 * F.card)
    (hpass :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
          ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (a : ZMod q)) :
    ∃ p : ℕ, p.Prime ∧ p ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_contra hnone
  have hmem : ∀ p ∈ S, ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (p : ZMod q) := by
    intro p hp
    apply hpass
    by_contra hf
    exact hnone ⟨p, hprime p hp, hbound p hp, hf⟩
  exact
    (not_lt_of_ge (NumberTheory.signed_prime_family_le_card H S F hneg hsub hprime hsize hmem))
      hcount

/-- A logarithmic weighted budget below `log q - log 2` puts every product
strictly below half the modulus. Combined with signed subgroup counting, a
family larger than half the subgroup forces a rejecting supplied prime. -/
theorem exists_prime_reject_signed_weighted {n q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (S : Finset ℕ) (F : Finset (Multiset ℕ)) (B budget : ℕ) (w : ℕ → ℕ) (d : ℝ) (hd : 0 < d)
    (hq : 0 < q) (hneg : (-1 : (ZMod q)ˣ) ∈ H) (hsub : ∀ T ∈ F, ∀ p ∈ T, p ∈ S)
    (hprime : ∀ p ∈ S, Nat.Prime p) (hbound : ∀ p ∈ S, p ≤ B)
    (hw : ∀ p ∈ S, Real.log p ≤ (w p : ℝ) / d) (hcost : ∀ T ∈ F, (T.map w).sum ≤ budget)
    (hbudget : Real.log 2 + (budget : ℝ) / d < Real.log q) (hcount : Nat.card H < 2 * F.card)
    (hpass :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
          ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (a : ZMod q)) :
    ∃ p : ℕ, p.Prime ∧ p ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply exists_prime_reject_of_signed_family H S F B hneg hsub hprime hbound
  · intro T hT
    have hpos : 0 < T.prod := Multiset.prod_pos (fun p hp ↦ (hprime p (hsub T hT p hp)).pos)
    have hl :=
      NumberTheory.log_multiset_prod_le_weight T w d (fun p hp ↦ (hprime p (hsub T hT p hp)).pos)
        (fun p hp ↦ hw p (hsub T hT p hp))
    have hc : ((T.map w).sum : ℝ) ≤ budget := Nat.cast_le.mpr (hcost T hT)
    have hwbound := div_le_div_of_nonneg_right hc hd.le
    have he : Real.log ((2 * T.prod : ℕ) : ℝ) = Real.log 2 + Real.log (T.prod : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_ofNat,
        Real.log_mul (by norm_num only : (2 : ℝ) ≠ 0)
          (Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hpos))]
    have hlog : Real.log ((2 * T.prod : ℕ) : ℝ) < Real.log (q : ℝ) := by
      rw [he]
      linarith only [hl, hwbound, hbudget]
    exact_mod_cast
      (Real.log_lt_log_iff (Nat.cast_pos.mpr (Nat.mul_pos (by decide) hpos))
            (Nat.cast_pos.mpr hq)).mp
        hlog
  · exact hcount
  · exact hpass

/-- For an odd semiprime `n = p*q`, a signed weighted family modulo `q`
forces a rejecting prime when twice its cardinality exceeds `p - 1`.
The ambient predecessor is even, so its local Fermat kernel contains `-1`,
and its cardinality is at most `p - 1`. -/
theorem exists_prime_reject_semiprime_signed {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hprod : n = p * q) (S : Finset ℕ) (F : Finset (Multiset ℕ)) (B budget : ℕ)
    (w : ℕ → ℕ) (d : ℝ) (hd : 0 < d) (hsub : ∀ T ∈ F, ∀ r ∈ T, r ∈ S) (hprime : ∀ r ∈ S, r.Prime)
    (hbound : ∀ r ∈ S, r ≤ B) (hw : ∀ r ∈ S, Real.log r ≤ (w r : ℝ) / d)
    (hcost : ∀ T ∈ F, (T.map w).sum ≤ budget) (hbudget : Real.log 2 + (budget : ℝ) / d < Real.log q)
    (hcount : p - 1 < 2 * F.card) :
    ∃ r : ℕ, r.Prime ∧ r ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hqn : q ∣ n := hprod ▸ dvd_mul_left q p
  have hq2 : q ≠ 2 := ho.ne_two_of_dvd_nat hqn
  let : NeZero (q ^ 1) := ⟨pow_ne_zero 1 hq.ne_zero⟩
  have hqpow : q ^ 1 ∣ n := by simpa only [pow_one] using hqn
  let H := (powMonoidHom (n - 1) : (ZMod (q ^ 1))ˣ →* (ZMod (q ^ 1))ˣ).ker
  have hneg : (-1 : (ZMod (q ^ 1))ˣ) ∈ H := by
    change (-1 : (ZMod (q ^ 1))ˣ) ^ (n - 1) = 1
    exact (Nat.Odd.sub_odd ho odd_one).neg_one_pow
  have hcard : Nat.card H < 2 * F.card := by
    dsimp only [H]
    rw [NumberTheory.card_local_fermat_kernel_prime_pow hn hq hq2 (by decide : 0 < 1) hqpow, hprod,
      Nat.mul_comm p q]
    exact (NumberTheory.gcd_predecessor_product_le_cofactor hq.pos hp.one_lt).trans_lt hcount
  apply
    exists_prime_reject_signed_weighted H S F B budget w d hd (pow_pos hq.pos 1) hneg hsub hprime
      hbound hw hcost
  · simpa only [pow_one] using hbudget
  · exact hcard
  · exact fun r hr ↦ PrimeTest.strongMR_local_divisorKernel hn ho hqpow hr

/-- For an odd input divisible by an odd prime power, a signed weighted
family forces a rejecting prime when twice its cardinality exceeds `p - 1`.
The original input's even predecessor makes the local Fermat kernel contain
minus one, and its cardinality is at most `p - 1`. -/
theorem exists_prime_reject_prime_pow_signed {n p a : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hp2 : p ≠ 2) (ha : 0 < a) (hdiv : p ^ a ∣ n) (S : Finset ℕ) (F : Finset (Multiset ℕ))
    (B budget : ℕ) (w : ℕ → ℕ) (d : ℝ) (hd : 0 < d) (hsub : ∀ T ∈ F, ∀ r ∈ T, r ∈ S)
    (hprime : ∀ r ∈ S, r.Prime) (hbound : ∀ r ∈ S, r ≤ B) (hw : ∀ r ∈ S, Real.log r ≤ (w r : ℝ) / d)
    (hcost : ∀ T ∈ F, (T.map w).sum ≤ budget)
    (hbudget : Real.log 2 + (budget : ℝ) / d < Real.log ((p ^ a : ℕ) : ℝ))
    (hcount : p - 1 < 2 * F.card) :
    ∃ r : ℕ, r.Prime ∧ r ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let : NeZero (p ^ a) := ⟨pow_ne_zero a hp.ne_zero⟩
  let H := (powMonoidHom (n - 1) : (ZMod (p ^ a))ˣ →* (ZMod (p ^ a))ˣ).ker
  have hneg : (-1 : (ZMod (p ^ a))ˣ) ∈ H := by
    change (-1 : (ZMod (p ^ a))ˣ) ^ (n - 1) = 1
    exact (Nat.Odd.sub_odd ho odd_one).neg_one_pow
  have hcard : Nat.card H < 2 * F.card := by
    dsimp only [H]
    rw [NumberTheory.card_local_fermat_kernel_prime_pow hn hp hp2 ha hdiv]
    exact (Nat.gcd_le_left (n - 1) (Nat.sub_pos_of_lt hp.one_lt)).trans_lt hcount
  exact
    exists_prime_reject_signed_weighted H S F B budget w d hd (pow_pos hp.pos a) hneg hsub hprime
      hbound hw hcost hbudget hcard
      (fun r hr ↦ PrimeTest.strongMR_local_divisorKernel hn ho hdiv hr)

/-- A signed weighted-family cell reduces the semiprime witness problem to
its small-local-modulus branch. Above the displayed logarithmic threshold,
the budget puts both signs below `q` and twice the family count exceeds the
ambient local Fermat kernel. -/
theorem exists_prime_reject_signed_cell {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hprod : n = p * q) (S : Finset ℕ) (F : Finset (Multiset ℕ)) (B budget : ℕ)
    (w : ℕ → ℕ) (d : ℝ) (hd : 0 < d) (hsub : ∀ T ∈ F, ∀ r ∈ T, r ∈ S) (hprime : ∀ r ∈ S, r.Prime)
    (hbound : ∀ r ∈ S, r ≤ B) (hw : ∀ r ∈ S, Real.log r ≤ (w r : ℝ) / d)
    (hcost : ∀ T ∈ F, (T.map w).sum ≤ budget) {A D X : ℝ} (hA : Real.log 2 + (budget : ℝ) / d ≤ A)
    (hD : D ≤ Real.log ((2 * F.card : ℕ) : ℝ)) (hB : (B : ℝ) ≤ X)
    (hlocal :
      Real.log q ≤ max A (Real.log n - D) →
        ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n)) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases hsmall : Real.log q ≤ max A (Real.log n - D)
  · exact hlocal hsmall
  · have hqbig : max A (Real.log n - D) < Real.log q := lt_of_not_ge hsmall
    have hbudget : Real.log 2 + (budget : ℝ) / d < Real.log q :=
      hA.trans_lt ((le_max_left _ _).trans_lt hqbig)
    have hlog : Real.log n = Real.log p + Real.log q := by
      rw [hprod, Nat.cast_mul,
        Real.log_mul (Nat.cast_ne_zero.mpr hp.ne_zero) (Nat.cast_ne_zero.mpr hq.ne_zero)]
    have hpLog : Real.log p < Real.log ((2 * F.card : ℕ) : ℝ) := by
      have hh := (le_max_right A (Real.log n - D)).trans_lt hqbig
      linarith only [hlog, hh, hD]
    have hFpos : 0 < 2 * F.card := by
      by_contra h
      have hz : 2 * F.card = 0 := Nat.eq_zero_of_not_pos h
      rw [hz, Nat.cast_zero, Real.log_zero] at hpLog
      exact (not_lt_of_ge (Real.log_natCast_nonneg p)) hpLog
    have hpCount : p < 2 * F.card := by
      exact_mod_cast
        (Real.log_lt_log_iff (Nat.cast_pos.mpr hp.pos) (Nat.cast_pos.mpr hFpos)).mp hpLog
    obtain ⟨r, hr, hb, hf⟩ :=
      exists_prime_reject_semiprime_signed hn ho hp hq hprod S F B budget w d hd hsub hprime hbound
        hw hcost hbudget ((Nat.sub_le p 1).trans_lt hpCount)
    exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hB, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
