/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.FromLLS
public import PseudoPrime.Analysis.MRLocalCutoffNumerics
public import PseudoPrime.PrimeTest.MillerRabin.LocalFermatKernel
public import PseudoPrime.PrimeTest.MillerRabin.LocalFermatIndexSize

/-! # Local divisor subgroup bounds for coefficient 0.283

A proper subgroup at a divisor modulus supplies an ambient MR witness.
The explicit finite-index size bound q²≤10^9*n gives coefficient 283/1000
at n≥10^141, including small local moduli through prime-factor witnesses.
-/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, a proper subgroup at a divisor modulus q≥2 containing every
ambient strong-pass image gives a failing prime base at most max(3000,log(q)²).
If the local modulus or a prime divisor is small, use that ambient prime divisor;
otherwise apply LLS S2 and exclude passage by the local containment premise.
This is the local-to-global witness bridge used by the finite-index branches. -/
theorem exists_prime_witness_le_local_subgroup_envelope {n q : ℕ} [NeZero q] (hn : 1 < n)
    (hnOdd : Odd n) (hq : 2 ≤ q) (hqn : q ∣ n) (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hpass :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
          ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (a : ZMod q))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ max 3000 ((Real.log q) ^ 2) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases hlarge : 3000 ≤ q
  · by_cases hsmall : ∃ p : ℕ, p.Prime ∧ (p : ℝ) < (Real.log q) ^ 2 ∧ p ∣ q
    · obtain ⟨p, hp, hb, hd⟩ := hsmall
      exact
        ⟨p, hp, hb.le.trans (le_max_right _ _),
          PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn hnOdd hp (dvd_trans hd hqn)⟩
    · have hno : ∀ p : ℕ, p.Prime → (p : ℝ) < (Real.log q) ^ 2 → ¬p ∣ q := by
        intro p hp hb hd
        exact hsmall ⟨p, hp, hb, hd⟩
      obtain ⟨p, hp, hb, hout⟩ := LLS.llsTheorem11S2_of_grh hGRH q hlarge hno H hH
      refine ⟨p, hp, hb.trans (le_max_right _ _), ?_⟩
      intro hyes
      exact hout (hpass p hyes)
  · obtain ⟨p, hp, hd⟩ :=
      Nat.exists_prime_and_dvd (Nat.ne_of_gt (lt_of_lt_of_le (by decide : 1 < 2) hq))
    have hpq := Nat.le_of_dvd (NeZero.pos q) hd
    have hb : (p : ℝ) ≤ 3000 := Nat.cast_le.mpr (hpq.trans (Nat.le_of_lt (lt_of_not_ge hlarge)))
    exact
      ⟨p, hp, hb.trans (le_max_left _ _),
        PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn hnOdd hp (dvd_trans hd hqn)⟩

/-- For odd n≥10^141, a proper local subgroup at q dividing n gives a failing
prime base at most (283/1000)log(n)² if q²≤10^9*n and all strong passes reduce
into the subgroup. Combine the local LLS envelope with the strict numerical bound.
This retains the arithmetic size and containment inputs for branch classification. -/
theorem exists_prime_witness_le_0283_of_local_subgroup {n q : ℕ} [NeZero q] (hnOdd : Odd n)
    (hq : 2 ≤ q) (hqn : q ∣ n) (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hpass :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
          ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (a : ZMod q))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 10 ^ 142 ≤ n)
    (hsize : q ^ 2 ≤ 10 ^ 9 * n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (282924 / 1000000 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hn1 : 1 < n := lt_of_lt_of_le (by decide : 1 < 10 ^ 142) hn
  obtain ⟨p, hp, hb, hfail⟩ :=
    exists_prime_witness_le_local_subgroup_envelope hn1 hnOdd hq hqn H hH hpass hGRH
  exact
    ⟨p, hp, (hb.trans_lt (Analysis.mr_local_envelope_lt_of_square_le hn (NeZero.pos q) hsize)).le,
      hfail⟩

/-- A non-Korselt prime factor p with p²≤10^9*n gives coefficient 283/1000
for a failing prime base under GRH when odd n≥10^141. The local (n-1)-power
kernel is proper and contains every strong-pass reduction, so no supplied
subgroup or containment premise remains. The finite-index classification must
still derive the arithmetic size bound from its global index condition. -/
theorem exists_prime_witness_le_0283_of_non_korselt_prime_factor {n p : ℕ} [Fact p.Prime]
    (hnOdd : Odd n) (hpn : p ∣ n) (hdiv : ¬p - 1 ∣ n - 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 10 ^ 142 ≤ n)
    (hsize : p ^ 2 ≤ 10 ^ 9 * n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (282924 / 1000000 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hn1 : 1 < n := lt_of_lt_of_le (by decide : 1 < 10 ^ 142) hn
  exact
    exists_prime_witness_le_0283_of_local_subgroup hnOdd (Fact.out : p.Prime).two_le hpn
      (powMonoidHom (n - 1) : (ZMod p)ˣ →* (ZMod p)ˣ).ker
      (PrimeTest.local_prime_powerKernel_ne_top_of_not_dvd hdiv)
      (fun a ha ↦ PrimeTest.strongMillerRabinPass_mem_local_prime_powerKernel hn1 hnOdd hpn ha) hGRH
      hn hsize

/-- Under GRH for odd n≥10^141, a non-Korselt prime factor gives coefficient
283/1000 whenever an ambient subgroup contained in the Fermat subgroup has
index at most 10^9. Derive the cofactor positivity, compare local and ambient
indices, and obtain the local prime-square size bound internally.
This completes the local analytic transfer for the finite-index non-Korselt branch. -/
theorem exists_prime_witness_le_0283_of_non_korselt_small_index {n p : ℕ} [Fact p.Prime]
    (hnOdd : Odd n) (hpn : p ∣ n) (hdiv : ¬p - 1 ∣ n - 1) (H : Subgroup (ZMod n)ˣ)
    (hH : H ≤ PrimeTest.fermatSubgroup n) (hi : H.index ≤ 10 ^ 9)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 10 ^ 142 ≤ n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (282924 / 1000000 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  obtain ⟨m, rfl⟩ := hpn
  have hnpos : 0 < p * m := lt_of_lt_of_le (pow_pos (by decide : (0 : ℕ) < 10) 142) hn
  let : NeZero (p * m) := ⟨Nat.ne_zero_of_lt hnpos⟩
  have hmpos : 0 < m :=
    Nat.pos_of_ne_zero (fun hm ↦ (Nat.ne_zero_of_lt hnpos) (by rw [hm, mul_zero]))
  have hmne : m ≠ 1 := by
    intro hm
    exact hdiv (by simpa only [hm, mul_one] using (dvd_refl (p - 1)))
  have hm1 : 1 < m := lt_of_le_of_ne (Nat.succ_le_of_lt hmpos) (Ne.symm hmne)
  have hs := PrimeTest.prime_factor_square_le_local_powerKernel_index_mul (p := p) hm1
  have hlocal := PrimeTest.local_powerKernel_index_le_of_le_fermat (dvd_mul_right p m) H hH
  have hsize := hs.trans (Nat.mul_le_mul_right (p * m) (hlocal.trans hi))
  exact
    exists_prime_witness_le_0283_of_non_korselt_prime_factor hnOdd (dvd_mul_right p m) hdiv hGRH hn
      hsize

end PseudoPrime.PrimeTestBounds.MillerRabin
