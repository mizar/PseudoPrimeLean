/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSurplusLocal
public import PseudoPrime.PrimeTestBounds.MillerRabin.ReducedContourBounds

/-! # All-factor reduction for surplus Gaussian cutoffs -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH from logarithmic scale 280, reduce either clipped surplus cutoff to
the large-index and uniform three-factor branches. The local subgroup case is
covered by the quadratic radius budget and the existing local witness. -/
theorem jointSurplus_reduce_branches {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (280 : ℝ) ≤ Real.log n)
    {rho R : ℝ} (hrho : 130 ≤ rho) (hR : 29 ≤ R)
    (hlarge :
      1000000000000 ≤ (PrimeTest.fermatSubgroup n).index →
        ∃ p : ℕ,
          p.Prime ∧
            (p : ℝ) ≤ (21 / 10 : ℝ) * (jointSurplusRadius rho R (Real.log n)) ^ 2 ∧
            ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n))
    (htriple :
      Squarefree n →
        n.primeFactors.card = 3 →
        (∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1) →
        (∀ p q : ℕ,
          p.Prime → q.Prime → p ∣ n → q ∣ n → padicValNat 2 (p - 1) = padicValNat 2 (q - 1)) →
        ∃ p : ℕ,
          p.Prime ∧
            (p : ℝ) ≤ (21 / 10 : ℝ) * (jointSurplusRadius rho R (Real.log n)) ^ 2 ∧
            ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n)) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (21 / 10 : ℝ) * (jointSurplusRadius rho R (Real.log n)) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  by_cases hi : (PrimeTest.fermatSubgroup n).index ≤ 10 ^ 12
  · have h36 : 10 ^ 36 ≤ n :=
      decimal_le_of_log_upper (Nat.zero_lt_of_lt hn)
        (by
          norm_num only [Nat.cast_ofNat]; linarith only [hL])
    have hJ : (10 ^ 12 : ℕ) ^ 3 ≤ n := by simpa only [← pow_mul, Nat.reduceMul] using h36
    rcases
      localSubgroup_or_uniformKorseltTriple hn ho hc (PrimeTest.fermatSubgroup n) le_rfl
        (by norm_num only : 1 ≤ 10 ^ 12) hJ hi with
      hl | ht
    · obtain ⟨q, hq, hqn, hsize, K, hK, hpass⟩ := hl
      have hqp : 0 < q := (by norm_num only : 0 < 2).trans_le hq
      let : NeZero q := ⟨hqp.ne'⟩
      obtain ⟨p, hp, hb, hr⟩ :=
        exists_prime_witness_le_local_subgroup_envelope hn ho hq hqn K hK hpass hGRH
      exact
        ⟨p, hp,
          hb.trans
            (jointSurplus_local_cutoff (Nat.zero_lt_of_lt hn) hqp hsize (Real.log_natCast_nonneg n)
              hrho hR),
          hr⟩
    · exact htriple ht.1 ht.2.1 ht.2.2.1 ht.2.2.2
  · exact hlarge (by exact_mod_cast (lt_of_not_ge hi).le)

end PseudoPrime.PrimeTestBounds.MillerRabin
