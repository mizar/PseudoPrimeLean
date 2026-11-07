/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaEighteenCells
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaFixed17Gap0
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaFixed17Gap1

/-! # Shared-scale Gamma interval coverage -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, a uniform Korselt triple in grouped Gamma cells 18 to 20
has a rejecting prime inside the `3/10` cutoff. The shared-scale gap yields
an actual witness below 587, and the left endpoint bounds that cutoff. -/
theorem uniform_gamma_fixed17_18 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (4423422506009 / 100000000000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (gammaFixed17Cell18Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (587 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 4423422506009 / 100000000000)]
  obtain ⟨l, hl, hb, hf⟩ :=
    uniformKorselt_reject_gamma hn ho hu hGRH (X := (587 : ℝ)) (x := (gammaMainCell17Scale : ℝ))
      (by norm_num only [gammaMainCell17Scale, Rat.cast_div, Rat.cast_ofNat]) (Finset.Ioc 0 587)
      (by
        intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
      (by norm_num only) (gammaFixed17Cell18_gap hGRH.riemann hhi)
  exact ⟨l, hl, hb.trans hcut, hf⟩

/-- Under GRH, a uniform Korselt triple in grouped Gamma cells 21 to 24
has a rejecting prime inside the `3/10` cutoff. The shared-scale gap yields
an actual witness below 601, and the left endpoint bounds that cutoff. -/
theorem uniform_gamma_fixed17_21 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (22379305917149 / 500000000000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (gammaFixed17Cell21Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (601 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 22379305917149 / 500000000000)]
  obtain ⟨l, hl, hb, hf⟩ :=
    uniformKorselt_reject_gamma hn ho hu hGRH (X := (601 : ℝ)) (x := (gammaMainCell17Scale : ℝ))
      (by norm_num only [gammaMainCell17Scale, Rat.cast_div, Rat.cast_ofNat]) (Finset.Ioc 0 601)
      (by
        intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
      (by norm_num only) (gammaFixed17Cell21_gap hGRH.riemann hhi)
  exact ⟨l, hl, hb.trans hcut, hf⟩

/-- Under GRH, a uniform Korselt triple in grouped Gamma cells 25 to 29
has a rejecting prime inside the `3/10` cutoff. The shared-scale gap yields
an actual witness below 619, and the left endpoint bounds that cutoff. -/
theorem uniform_gamma_fixed17_25 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (11355982270739 / 250000000000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (gammaFixed17Cell25Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (619 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 11355982270739 / 250000000000)]
  obtain ⟨l, hl, hb, hf⟩ :=
    uniformKorselt_reject_gamma hn ho hu hGRH (X := (619 : ℝ)) (x := (gammaMainCell17Scale : ℝ))
      (by norm_num only [gammaMainCell17Scale, Rat.cast_div, Rat.cast_ofNat]) (Finset.Ioc 0 619)
      (by
        intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
      (by norm_num only) (gammaFixed17Cell25_gap hGRH.riemann hhi)
  exact ⟨l, hl, hb.trans hcut, hf⟩

/-- Under GRH, a uniform Korselt triple in grouped Gamma cells 30 to 34
has a rejecting prime inside the `3/10` cutoff. The shared-scale gap yields
an actual witness below 647, and the left endpoint bounds that cutoff. -/
theorem uniform_gamma_fixed17_30 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (46439925351649 / 1000000000000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (gammaFixed17Cell30Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (647 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 46439925351649 / 1000000000000)]
  obtain ⟨l, hl, hb, hf⟩ :=
    uniformKorselt_reject_gamma hn ho hu hGRH (X := (647 : ℝ)) (x := (gammaMainCell17Scale : ℝ))
      (by norm_num only [gammaMainCell17Scale, Rat.cast_div, Rat.cast_ofNat]) (Finset.Ioc 0 647)
      (by
        intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
      (by norm_num only) (gammaFixed17Cell30_gap hGRH.riemann hhi)
  exact ⟨l, hl, hb.trans hcut, hf⟩

/-- Under GRH, a uniform Korselt triple in grouped Gamma cells 35 to 38
has a rejecting prime inside the `3/10` cutoff. The shared-scale gap yields
an actual witness below 677, and the left endpoint bounds that cutoff. -/
theorem uniform_gamma_fixed17_35 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (1187609644061 / 25000000000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (gammaFixed17Cell35Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (677 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 1187609644061 / 25000000000)]
  obtain ⟨l, hl, hb, hf⟩ :=
    uniformKorselt_reject_gamma hn ho hu hGRH (X := (677 : ℝ)) (x := (gammaMainCell17Scale : ℝ))
      (by norm_num only [gammaMainCell17Scale, Rat.cast_div, Rat.cast_ofNat]) (Finset.Ioc 0 677)
      (by
        intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
      (by norm_num only) (gammaFixed17Cell35_gap hGRH.riemann hhi)
  exact ⟨l, hl, hb.trans hcut, hf⟩

/-- Under GRH, a uniform Korselt triple in grouped Gamma cells 39 to 42
has a rejecting prime inside the `3/10` cutoff. The shared-scale gap yields
an actual witness below 709, and the left endpoint bounds that cutoff. -/
theorem uniform_gamma_fixed17_39 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (2430706344529 / 50000000000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (gammaFixed17Cell39Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (709 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 2430706344529 / 50000000000)]
  obtain ⟨l, hl, hb, hf⟩ :=
    uniformKorselt_reject_gamma hn ho hu hGRH (X := (709 : ℝ)) (x := (gammaMainCell17Scale : ℝ))
      (by norm_num only [gammaMainCell17Scale, Rat.cast_div, Rat.cast_ofNat]) (Finset.Ioc 0 709)
      (by
        intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
      (by norm_num only) (gammaFixed17Cell39_gap hGRH.riemann hhi)
  exact ⟨l, hl, hb.trans hcut, hf⟩

/-- Under GRH, a uniform Korselt triple in grouped Gamma cells 43 to 45
has a rejecting prime inside the `3/10` cutoff. The shared-scale gap yields
an actual witness below 733, and the left endpoint bounds that cutoff. -/
theorem uniform_gamma_fixed17_43 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (49430085305747 / 1000000000000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (gammaFixed17Cell43Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (733 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 49430085305747 / 1000000000000)]
  obtain ⟨l, hl, hb, hf⟩ :=
    uniformKorselt_reject_gamma hn ho hu hGRH (X := (733 : ℝ)) (x := (gammaMainCell17Scale : ℝ))
      (by norm_num only [gammaMainCell17Scale, Rat.cast_div, Rat.cast_ofNat]) (Finset.Ioc 0 733)
      (by
        intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
      (by norm_num only) (gammaFixed17Cell43_gap hGRH.riemann hhi)
  exact ⟨l, hl, hb.trans hcut, hf⟩

/-- Under GRH, a uniform Korselt triple in grouped Gamma cells 46 to 48
has a rejecting prime inside the `3/10` cutoff. The shared-scale gap yields
an actual witness below 751, and the left endpoint bounds that cutoff. -/
theorem uniform_gamma_fixed17_46 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (6254165278703 / 125000000000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (gammaFixed17Cell46Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (751 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 6254165278703 / 125000000000)]
  obtain ⟨l, hl, hb, hf⟩ :=
    uniformKorselt_reject_gamma hn ho hu hGRH (X := (751 : ℝ)) (x := (gammaMainCell17Scale : ℝ))
      (by norm_num only [gammaMainCell17Scale, Rat.cast_div, Rat.cast_ofNat]) (Finset.Ioc 0 751)
      (by
        intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
      (by norm_num only) (gammaFixed17Cell46_gap hGRH.riemann hhi)
  exact ⟨l, hl, hb.trans hcut, hf⟩

/-- Under GRH, a uniform Korselt triple in grouped Gamma cells 49 to 50
has a rejecting prime inside the `3/10` cutoff. The shared-scale gap yields
an actual witness below 769, and the left endpoint bounds that cutoff. -/
theorem uniform_gamma_fixed17_49 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (50629372239179 / 1000000000000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (gammaFixed17Cell49Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (769 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 50629372239179 / 1000000000000)]
  obtain ⟨l, hl, hb, hf⟩ :=
    uniformKorselt_reject_gamma hn ho hu hGRH (X := (769 : ℝ)) (x := (gammaMainCell17Scale : ℝ))
      (by norm_num only [gammaMainCell17Scale, Rat.cast_div, Rat.cast_ofNat]) (Finset.Ioc 0 769)
      (by
        intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
      (by norm_num only) (gammaFixed17Cell49_gap hGRH.riemann hhi)
  exact ⟨l, hl, hb.trans hcut, hf⟩

/-- Under GRH, a uniform Korselt triple in grouped Gamma cells 51 to 51
has a rejecting prime inside the `3/10` cutoff. The shared-scale gap yields
an actual witness below 787, and the left endpoint bounds that cutoff. -/
theorem uniform_gamma_fixed17_51 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (51218486246017 / 1000000000000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (gammaFixed17Cell51Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (787 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 51218486246017 / 1000000000000)]
  obtain ⟨l, hl, hb, hf⟩ :=
    uniformKorselt_reject_gamma hn ho hu hGRH (X := (787 : ℝ)) (x := (gammaMainCell17Scale : ℝ))
      (by norm_num only [gammaMainCell17Scale, Rat.cast_div, Rat.cast_ofNat]) (Finset.Ioc 0 787)
      (by
        intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
      (by norm_num only) (gammaFixed17Cell51_gap hGRH.riemann hhi)
  exact ⟨l, hl, hb.trans hcut, hf⟩

/-- Under GRH, every odd composite from logarithmic scale 8 through the
last shared-scale interval has a rejecting prime within the `3/10` cutoff.
Ten overlapping intervals connect to the preceding eighteen-cell bound. -/
theorem exists_reject_03_low_shared_cells {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ (gammaFixed17Cell51Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  by_cases hu : UniformKorseltTriple n
  · by_cases h17 : Real.log n ≤ (gammaCell17Right : ℝ)
    · exact exists_reject_03_low_eighteen_cells hn ho hc hGRH hL h17
    · by_cases h18 : Real.log n ≤ (gammaFixed17Cell18Right : ℝ)
      · apply uniform_gamma_fixed17_18 hn ho hu hGRH _ h18
        have h := le_of_not_ge h17
        norm_num only [gammaCell17Right, Rat.cast_div, Rat.cast_ofNat] at h
        exact h
      · by_cases h21 : Real.log n ≤ (gammaFixed17Cell21Right : ℝ)
        · apply uniform_gamma_fixed17_21 hn ho hu hGRH _ h21
          have h := le_of_not_ge h18
          norm_num only [gammaFixed17Cell18Right, Rat.cast_div, Rat.cast_ofNat] at h
          exact h
        · by_cases h25 : Real.log n ≤ (gammaFixed17Cell25Right : ℝ)
          · apply uniform_gamma_fixed17_25 hn ho hu hGRH _ h25
            have h := le_of_not_ge h21
            norm_num only [gammaFixed17Cell21Right, Rat.cast_div, Rat.cast_ofNat] at h
            exact h
          · by_cases h30 : Real.log n ≤ (gammaFixed17Cell30Right : ℝ)
            · apply uniform_gamma_fixed17_30 hn ho hu hGRH _ h30
              have h := le_of_not_ge h25
              norm_num only [gammaFixed17Cell25Right, Rat.cast_div, Rat.cast_ofNat] at h
              exact h
            · by_cases h35 : Real.log n ≤ (gammaFixed17Cell35Right : ℝ)
              · apply uniform_gamma_fixed17_35 hn ho hu hGRH _ h35
                have h := le_of_not_ge h30
                norm_num only [gammaFixed17Cell30Right, Rat.cast_div, Rat.cast_ofNat] at h
                exact h
              · by_cases h39 : Real.log n ≤ (gammaFixed17Cell39Right : ℝ)
                · apply uniform_gamma_fixed17_39 hn ho hu hGRH _ h39
                  have h := le_of_not_ge h35
                  norm_num only [gammaFixed17Cell35Right, Rat.cast_div, Rat.cast_ofNat] at h
                  exact h
                · by_cases h43 : Real.log n ≤ (gammaFixed17Cell43Right : ℝ)
                  · apply uniform_gamma_fixed17_43 hn ho hu hGRH _ h43
                    have h := le_of_not_ge h39
                    norm_num only [gammaFixed17Cell39Right, Rat.cast_div, Rat.cast_ofNat] at h
                    exact h
                  · by_cases h46 : Real.log n ≤ (gammaFixed17Cell46Right : ℝ)
                    · apply uniform_gamma_fixed17_46 hn ho hu hGRH _ h46
                      have h := le_of_not_ge h43
                      norm_num only [gammaFixed17Cell43Right, Rat.cast_div, Rat.cast_ofNat] at h
                      exact h
                    · by_cases h49 : Real.log n ≤ (gammaFixed17Cell49Right : ℝ)
                      · apply uniform_gamma_fixed17_49 hn ho hu hGRH _ h49
                        have h := le_of_not_ge h46
                        norm_num only [gammaFixed17Cell46Right, Rat.cast_div, Rat.cast_ofNat] at h
                        exact h
                      · apply uniform_gamma_fixed17_51 hn ho hu hGRH _ hU
                        have h := le_of_not_ge h49
                        norm_num only [gammaFixed17Cell49Right, Rat.cast_div, Rat.cast_ofNat] at h
                        exact h
  · exact exists_prime_reject_03_nonuniform_log8 hn ho hc hu hGRH hL

end PseudoPrime.PrimeTestBounds.MillerRabin
