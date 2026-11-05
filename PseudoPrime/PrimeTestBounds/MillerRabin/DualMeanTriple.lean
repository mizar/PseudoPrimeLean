/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.DualMeanRepeated
public import PseudoPrime.PrimeTestBounds.MillerRabin.ReducedGaussianBounds

/-! # Gaussian triple witness for the two-cell mean bridge -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational Gaussian profile certifies the uniform three-factor branch at
the squared radius for the mean bridge, from logarithmic scale 81000. -/
noncomputable def dualMeanGaussian : ReducedGaussianProfile where
  C := (647 / 1000 : ℝ) ^ 2
  T := 81000
  gamma := 22323 / 50000
  v := 284
  entry := by norm_num only
  gammaLower := by norm_num only
  lower := by norm_num only
  upper := by norm_num only
  fourth := by norm_num only [and_self]
  margin := by norm_num only

/-- Under GRH, a squarefree odd modulus with three prime factors has a rejecting
prime below coefficient 4187/10000 from scale 81000. Local witnesses cover
nonuniform cases and the certified Gaussian profile handles the uniform case. -/
theorem dualMean_squarefreeThree {n : ℕ} (hn : 1 < n) (ho : Odd n) (hsf : Squarefree n)
    (hcard : n.primeFactors.card = 3) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (81000 : ℝ) ≤ Real.log n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4187 / 10000 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hc : 3 ≤ n.primeFactors.card := hcard.ge
  by_cases hlocal :
    (∃ r ∈ n.primeFactors, ∃ s ∈ n.primeFactors, padicValNat 2 (s - 1) < padicValNat 2 (r - 1)) ∨
      ∃ r ∈ n.primeFactors, ¬r - 1 ∣ n - 1
  · obtain ⟨r, hr, hf, hb, _⟩ :=
      exists_leastWitness_le_local_factor_coefficient hn ho hc hlocal hGRH
    have hcoeff : (4 : ℝ) / ((n.primeFactors.card : ℝ) + 1) ^ 2 ≤ (4187 / 10000 : ℝ) := by
      rw [hcard]
      norm_num only [Nat.cast_ofNat]
    exact ⟨r, hr, hb.trans (mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)), hf⟩
  · have hK : ∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1 := by
      intro p hp hpn
      by_contra hbad
      apply hlocal
      right
      exact ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpn, Nat.ne_zero_of_lt hn⟩, hbad⟩
    have hU :
      ∀ p q : ℕ,
        p.Prime → q.Prime → p ∣ n → q ∣ n → padicValNat 2 (p - 1) = padicValNat 2 (q - 1) := by
      intro p q hp hq hpn hqn
      by_contra hne
      have hpMem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpn, Nat.ne_zero_of_lt hn⟩
      have hqMem : q ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hqn, Nat.ne_zero_of_lt hn⟩
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact hlocal (Or.inl ⟨q, hqMem, p, hpMem, hlt⟩)
      · exact hlocal (Or.inl ⟨p, hpMem, q, hqMem, hgt⟩)
    obtain ⟨r, hr, hb, hf⟩ :=
      reducedGaussian_cardWitness dualMeanGaussian ho hsf hcard hK hU hGRH hL
    have hc : (647 / 1000 : ℝ) ^ 2 ≤ 4187 / 10000 := by norm_num only
    exact ⟨r, hr, hb.trans (mul_le_mul_of_nonneg_right hc (sq_nonneg _)), hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
