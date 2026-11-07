/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaFixed92Combined2
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaFixed92Gap3

/-! # Shared-scale Gamma interval coverage, block 3 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, a uniform Korselt triple in grouped Gamma cells 172 to 175
has a rejecting prime inside the `3/10` cutoff. The shared-scale gap yields
an actual witness below 1609, and the left endpoint bounds that cutoff. -/
theorem uniform_gamma_fixed92_172 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (18308695566133 / 250000000000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (gammaFixed92Cell172Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (1609 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 18308695566133 / 250000000000)]
  obtain ⟨l, hl, hb, hf⟩ :=
    uniformKorselt_reject_gamma hn ho hu hGRH (X := (1609 : ℝ)) (x := (gammaMainCell92Scale : ℝ))
      (by norm_num only [gammaMainCell92Scale, Rat.cast_div, Rat.cast_ofNat]) (Finset.Ioc 0 1609)
      (by
        intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
      (by norm_num only) (gammaFixed92Cell172_gap hGRH.riemann hhi)
  exact ⟨l, hl, hb.trans hcut, hf⟩

/-- Under GRH, a uniform Korselt triple in grouped Gamma cells 176 to 176
has a rejecting prime inside the `3/10` cutoff. The shared-scale gap yields
an actual witness below 1627, and the left endpoint bounds that cutoff. -/
theorem uniform_gamma_fixed92_176 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (73643284373617 / 1000000000000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (gammaFixed92Cell176Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (1627 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 73643284373617 / 1000000000000)]
  obtain ⟨l, hl, hb, hf⟩ :=
    uniformKorselt_reject_gamma hn ho hu hGRH (X := (1627 : ℝ)) (x := (gammaMainCell92Scale : ℝ))
      (by norm_num only [gammaMainCell92Scale, Rat.cast_div, Rat.cast_ofNat]) (Finset.Ioc 0 1627)
      (by
        intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
      (by norm_num only) (gammaFixed92Cell176_gap hGRH.riemann hhi)
  exact ⟨l, hl, hb.trans hcut, hf⟩

/-- Under GRH, all odd composites from logarithmic scale 8 through this
block's last endpoint have a rejecting prime within the `3/10` cutoff.
Adjacent closed intervals connect the new witnesses to the preceding block. -/
theorem exists_reject_03_fixed92_block3 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ (gammaFixed92Cell176Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  by_cases hu : UniformKorseltTriple n
  · by_cases hprev : Real.log n ≤ (gammaFixed92Cell168Right : ℝ)
    · exact exists_reject_03_fixed92_block2 hn ho hc hGRH hL hprev
    · by_cases h172 : Real.log n ≤ (gammaFixed92Cell172Right : ℝ)
      · apply uniform_gamma_fixed92_172 hn ho hu hGRH _ h172
        have h := le_of_not_ge hprev
        norm_num only [gammaFixed92Cell168Right, Rat.cast_div, Rat.cast_ofNat] at h
        exact h
      · apply uniform_gamma_fixed92_176 hn ho hu hGRH _ hU
        have h := le_of_not_ge h172
        norm_num only [gammaFixed92Cell172Right, Rat.cast_div, Rat.cast_ofNat] at h
        exact h
  · exact exists_prime_reject_03_nonuniform_log8 hn ho hc hu hGRH hL

end PseudoPrime.PrimeTestBounds.MillerRabin
