/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedSemiprimeLower

/-! # Semiprime witnesses from numerical count lower bounds -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, a numerical lower bound for a weighted count yields a
semiprime rejecting prime when the cutoff and local envelope fit. The large
factor case compares the lower count to the original-input Fermat kernel. -/
theorem exists_prime_reject_semiprime_count_lower {n p q : ℕ} (hn : 1 < n) (ho : Odd n)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (xs weights : List ℕ)
    (B budget : ℕ) (w : ℕ → ℕ) (d : ℝ) (hd : 0 < d) (hnodup : xs.Nodup) (hprime : ∀ r ∈ xs, r.Prime)
    (hcut : ∀ r ∈ xs, r ≤ B) (hwpos : ∀ r ∈ xs, 0 < w r) (hw : ∀ r ∈ xs, Real.log r ≤ (w r : ℝ) / d)
    (he : xs.map w = weights) (C : ℕ) (hrow : C ≤ weightedPrimeCount id weights budget) {D X : ℝ}
    (hD : D ≤ Real.log (C : ℝ)) (hB : (B : ℝ) ≤ X)
    (hlocal : localFullEnvelope (max ((budget : ℝ) / d) (Real.log n - D)) ≤ X) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hqn : q ∣ n := hprod ▸ dvd_mul_left q p
  have hq2 : q ≠ 2 := ho.ne_two_of_dvd_nat hqn
  have hbad : ¬q - 1 ∣ n - 1 := by
    rw [hprod]
    exact NumberTheory.not_sub_one_dvd_prime_mul_sub_one_of_lt hp hq hpq
  by_cases hsmall : Real.log q ≤ max ((budget : ℝ) / d) (Real.log n - D)
  · obtain ⟨r, hr, hb, hf⟩ := exists_prime_reject_nonKorselt_local hn ho hq hqn hbad hGRH hsmall
    exact ⟨r, hr, hb.trans hlocal, hf⟩
  · have hqbig := lt_of_not_ge hsmall
    have hsize : (budget : ℝ) / d < Real.log q := (le_max_left _ _).trans_lt hqbig
    have hlog : Real.log n = Real.log p + Real.log q := by
      rw [hprod, Nat.cast_mul,
        Real.log_mul (Nat.cast_ne_zero.mpr hp.ne_zero) (Nat.cast_ne_zero.mpr hq.ne_zero)]
    have hpLog : Real.log p < Real.log (C : ℝ) := by
      have hh := (le_max_right ((budget : ℝ) / d) (Real.log n - D)).trans_lt hqbig
      linarith only [hlog, hh, hD]
    have hcountpos : 0 < C := by
      by_contra h
      have hz : C = 0 := Nat.eq_zero_of_not_pos h
      rw [hz, Nat.cast_zero, Real.log_zero] at hpLog
      exact (not_lt_of_ge (Real.log_natCast_nonneg p)) hpLog
    have hpCount : p < C := by
      exact_mod_cast
        (Real.log_lt_log_iff (Nat.cast_pos.mpr hp.pos) (Nat.cast_pos.mpr hcountpos)).mp hpLog
    let : NeZero (q ^ 1) := ⟨pow_ne_zero 1 hq.ne_zero⟩
    let H := (powMonoidHom (n - 1) : (ZMod (q ^ 1))ˣ →* (ZMod (q ^ 1))ˣ).ker
    have hqpow : q ^ 1 ∣ n := by simpa only [pow_one] using hqn
    have hcard : Nat.card H < C := by
      change Nat.card (powMonoidHom (n - 1) : (ZMod (q ^ 1))ˣ →* (ZMod (q ^ 1))ˣ).ker < _
      rw [NumberTheory.card_local_fermat_kernel_prime_pow hn hq hq2 (by decide : 0 < 1) hqpow,
        hprod, Nat.mul_comm p q]
      exact
        (NumberTheory.gcd_predecessor_product_le_cofactor hq.pos hp.one_lt).trans_lt
          ((Nat.sub_le p 1).trans_lt hpCount)
    obtain ⟨r, hr, hb, hf⟩ :=
      exists_prime_reject_of_weight_list H xs weights B budget w d hd (pow_pos hq.pos 1) hnodup
        hprime hcut hwpos hw he (by simpa only [pow_one] using hsize) (hcard.trans_le hrow)
        (fun r hr ↦ PrimeTest.strongMR_local_divisorKernel hn ho hqpow hr)
    exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hB, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
