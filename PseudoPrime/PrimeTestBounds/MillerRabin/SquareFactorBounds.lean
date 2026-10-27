/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.SquareFactorLocalBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.LocalSubgroupBounds

/-! # Coefficient 0.283 for the finite-index prime-square divisor branch -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH for odd n≥10^141, a prime-square divisor gives a failing
prime base at most (283/1000)log(n)² if an ambient subgroup within the Fermat
subgroup has index at most 10^9. Bound p by the local and ambient indices,
prove the prime-square kernel is proper, and apply the local LLS envelope.
No external local-size, local properness or pass-containment premise remains. -/
theorem exists_prime_witness_le_0283_of_square_factor_small_index {n p : ℕ} [NeZero n]
    (hnOdd : Odd n) (hp : p.Prime) (hsq : p ^ 2 ∣ n) (H : Subgroup (ZMod n)ˣ)
    (hH : H ≤ PrimeTest.fermatSubgroup n) (hi : H.index ≤ 10 ^ 9)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 10 ^ 142 ≤ n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (282924 / 1000000 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  have hn1 : 1 < n := lt_of_lt_of_le (by decide : 1 < 10 ^ 142) hn
  have hpn : p ∣ n := dvd_trans ⟨p, by rw [pow_two]⟩ hsq
  have hp2 := hnOdd.ne_two_of_dvd_nat hpn
  let K := (powMonoidHom (n - 1) : (ZMod (p ^ 2))ˣ →* (ZMod (p ^ 2))ˣ).ker
  have hlow := PrimeTest.prime_le_local_square_powerKernel_index hn1 hp hp2 hsq
  have hup := PrimeTest.local_divisor_powerKernel_index_le_of_le_fermat hsq H hH
  have hpsmall : p ≤ 10 ^ 9 := hlow.trans (hup.trans hi)
  have hproper : K ≠ ⊤ := by
    intro ht
    change p ≤ K.index at hlow
    rw [ht, Subgroup.index_top] at hlow
    exact (not_le_of_gt hp.one_lt) hlow
  have hq2 : 2 ≤ p ^ 2 := hp.two_le.trans (Nat.le_self_pow (by decide : 2 ≠ 0) p)
  have hn141 : 10 ^ 141 ≤ n := (by norm_num only : 10 ^ 141 ≤ 10 ^ 142).trans hn
  exact
    exists_prime_witness_le_0283_of_local_subgroup hnOdd hq2 hsq K hproper
      (fun a ha ↦ PrimeTest.strongMillerRabinPass_mem_local_divisor_powerKernel hn1 hnOdd hsq ha)
      hGRH hn (PrimeTest.local_prime_square_size_of_finite_index hpsmall hn141)

end PseudoPrime.PrimeTestBounds.MillerRabin
