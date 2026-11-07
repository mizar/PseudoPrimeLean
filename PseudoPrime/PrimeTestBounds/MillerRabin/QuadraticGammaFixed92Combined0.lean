/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaFixed17Combined
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaFixed92Gap0

/-! # Shared-scale Gamma interval coverage, block 0 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, a uniform Korselt triple in grouped Gamma cells 52 to 52
has a rejecting prime inside the `3/10` cutoff. The shared-scale gap yields
an actual witness below 797, and the left endpoint bounds that cutoff. -/
theorem uniform_gamma_fixed92_52 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (51542862422131 / 1000000000000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (gammaFixed92Cell52Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (797 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 51542862422131 / 1000000000000)]
  obtain ⟨l, hl, hb, hf⟩ :=
    uniformKorselt_reject_gamma hn ho hu hGRH (X := (797 : ℝ)) (x := (gammaMainCell92Scale : ℝ))
      (by norm_num only [gammaMainCell92Scale, Rat.cast_div, Rat.cast_ofNat]) (Finset.Ioc 0 797)
      (by
        intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
      (by norm_num only) (gammaFixed92Cell52_gap hGRH.riemann hhi)
  exact ⟨l, hl, hb.trans hcut, hf⟩

/-- Under GRH, a uniform Korselt triple in grouped Gamma cells 53 to 53
has a rejecting prime inside the `3/10` cutoff. The shared-scale gap yields
an actual witness below 809, and the left endpoint bounds that cutoff. -/
theorem uniform_gamma_fixed92_53 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (519294393063 / 10000000000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (gammaFixed92Cell53Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (809 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 519294393063 / 10000000000)]
  obtain ⟨l, hl, hb, hf⟩ :=
    uniformKorselt_reject_gamma hn ho hu hGRH (X := (809 : ℝ)) (x := (gammaMainCell92Scale : ℝ))
      (by norm_num only [gammaMainCell92Scale, Rat.cast_div, Rat.cast_ofNat]) (Finset.Ioc 0 809)
      (by
        intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
      (by norm_num only) (gammaFixed92Cell53_gap hGRH.riemann hhi)
  exact ⟨l, hl, hb.trans hcut, hf⟩

/-- Under GRH, a uniform Korselt triple in grouped Gamma cells 54 to 57
has a rejecting prime inside the `3/10` cutoff. The shared-scale gap yields
an actual witness below 811, and the left endpoint bounds that cutoff. -/
theorem uniform_gamma_fixed92_54 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (3249599334277 / 62500000000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (gammaFixed92Cell54Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (811 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 3249599334277 / 62500000000)]
  obtain ⟨l, hl, hb, hf⟩ :=
    uniformKorselt_reject_gamma hn ho hu hGRH (X := (811 : ℝ)) (x := (gammaMainCell92Scale : ℝ))
      (by norm_num only [gammaMainCell92Scale, Rat.cast_div, Rat.cast_ofNat]) (Finset.Ioc 0 811)
      (by
        intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
      (by norm_num only) (gammaFixed92Cell54_gap hGRH.riemann hhi)
  exact ⟨l, hl, hb.trans hcut, hf⟩

/-- Under GRH, a uniform Korselt triple in grouped Gamma cells 58 to 63
has a rejecting prime inside the `3/10` cutoff. The shared-scale gap yields
an actual witness below 829, and the left endpoint bounds that cutoff. -/
theorem uniform_gamma_fixed92_58 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (13141854257803 / 250000000000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (gammaFixed92Cell58Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (829 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 13141854257803 / 250000000000)]
  obtain ⟨l, hl, hb, hf⟩ :=
    uniformKorselt_reject_gamma hn ho hu hGRH (X := (829 : ℝ)) (x := (gammaMainCell92Scale : ℝ))
      (by norm_num only [gammaMainCell92Scale, Rat.cast_div, Rat.cast_ofNat]) (Finset.Ioc 0 829)
      (by
        intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
      (by norm_num only) (gammaFixed92Cell58_gap hGRH.riemann hhi)
  exact ⟨l, hl, hb.trans hcut, hf⟩

/-- Under GRH, a uniform Korselt triple in grouped Gamma cells 64 to 70
has a rejecting prime inside the `3/10` cutoff. The shared-scale gap yields
an actual witness below 863, and the left endpoint bounds that cutoff. -/
theorem uniform_gamma_fixed92_64 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (3352160373053 / 62500000000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (gammaFixed92Cell64Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (863 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 3352160373053 / 62500000000)]
  obtain ⟨l, hl, hb, hf⟩ :=
    uniformKorselt_reject_gamma hn ho hu hGRH (X := (863 : ℝ)) (x := (gammaMainCell92Scale : ℝ))
      (by norm_num only [gammaMainCell92Scale, Rat.cast_div, Rat.cast_ofNat]) (Finset.Ioc 0 863)
      (by
        intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
      (by norm_num only) (gammaFixed92Cell64_gap hGRH.riemann hhi)
  exact ⟨l, hl, hb.trans hcut, hf⟩

/-- Under GRH, all odd composites from logarithmic scale 8 through this
block's last endpoint have a rejecting prime within the `3/10` cutoff.
Adjacent closed intervals connect the new witnesses to the preceding block. -/
theorem exists_reject_03_fixed92_block0 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ (gammaFixed92Cell64Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  by_cases hu : UniformKorseltTriple n
  · by_cases hprev : Real.log n ≤ (gammaFixed17Cell51Right : ℝ)
    · exact exists_reject_03_low_shared_cells hn ho hc hGRH hL hprev
    · by_cases h52 : Real.log n ≤ (gammaFixed92Cell52Right : ℝ)
      · apply uniform_gamma_fixed92_52 hn ho hu hGRH _ h52
        have h := le_of_not_ge hprev
        norm_num only [gammaFixed17Cell51Right, Rat.cast_div, Rat.cast_ofNat] at h
        exact h
      · by_cases h53 : Real.log n ≤ (gammaFixed92Cell53Right : ℝ)
        · apply uniform_gamma_fixed92_53 hn ho hu hGRH _ h53
          have h := le_of_not_ge h52
          norm_num only [gammaFixed92Cell52Right, Rat.cast_div, Rat.cast_ofNat] at h
          exact h
        · by_cases h54 : Real.log n ≤ (gammaFixed92Cell54Right : ℝ)
          · apply uniform_gamma_fixed92_54 hn ho hu hGRH _ h54
            have h := le_of_not_ge h53
            norm_num only [gammaFixed92Cell53Right, Rat.cast_div, Rat.cast_ofNat] at h
            exact h
          · by_cases h58 : Real.log n ≤ (gammaFixed92Cell58Right : ℝ)
            · apply uniform_gamma_fixed92_58 hn ho hu hGRH _ h58
              have h := le_of_not_ge h54
              norm_num only [gammaFixed92Cell54Right, Rat.cast_div, Rat.cast_ofNat] at h
              exact h
            · apply uniform_gamma_fixed92_64 hn ho hu hGRH _ hU
              have h := le_of_not_ge h58
              norm_num only [gammaFixed92Cell58Right, Rat.cast_div, Rat.cast_ofNat] at h
              exact h
  · exact exists_prime_reject_03_nonuniform_log8 hn ho hc hu hGRH hL

end PseudoPrime.PrimeTestBounds.MillerRabin
