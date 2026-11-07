/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaFixed92Combined0
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaFixed92Gap1

/-! # Shared-scale Gamma interval coverage, block 1 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, a uniform Korselt triple in grouped Gamma cells 71 to 79
has a rejecting prime inside the `3/10` cutoff. The shared-scale gap yields
an actual witness below 919, and the left endpoint bounds that cutoff. -/
theorem uniform_gamma_fixed92_71 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (13836846943337 / 250000000000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (gammaFixed92Cell71Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (919 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 13836846943337 / 250000000000)]
  obtain ⟨l, hl, hb, hf⟩ :=
    uniformKorselt_reject_gamma hn ho hu hGRH (X := (919 : ℝ)) (x := (gammaMainCell92Scale : ℝ))
      (by norm_num only [gammaMainCell92Scale, Rat.cast_div, Rat.cast_ofNat]) (Finset.Ioc 0 919)
      (by
        intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
      (by norm_num only) (gammaFixed92Cell71_gap hGRH.riemann hhi)
  exact ⟨l, hl, hb.trans hcut, hf⟩

/-- Under GRH, a uniform Korselt triple in grouped Gamma cells 80 to 92
has a rejecting prime inside the `3/10` cutoff. The shared-scale gap yields
an actual witness below 977, and the left endpoint bounds that cutoff. -/
theorem uniform_gamma_fixed92_80 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (57067211835403 / 1000000000000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (gammaFixed92Cell80Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (977 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 57067211835403 / 1000000000000)]
  obtain ⟨l, hl, hb, hf⟩ :=
    uniformKorselt_reject_gamma hn ho hu hGRH (X := (977 : ℝ)) (x := (gammaMainCell92Scale : ℝ))
      (by norm_num only [gammaMainCell92Scale, Rat.cast_div, Rat.cast_ofNat]) (Finset.Ioc 0 977)
      (by
        intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
      (by norm_num only) (gammaFixed92Cell80_gap hGRH.riemann hhi)
  exact ⟨l, hl, hb.trans hcut, hf⟩

/-- Under GRH, a uniform Korselt triple in grouped Gamma cells 93 to 106
has a rejecting prime inside the `3/10` cutoff. The shared-scale gap yields
an actual witness below 1051, and the left endpoint bounds that cutoff. -/
theorem uniform_gamma_fixed92_93 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (29594481467553 / 500000000000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (gammaFixed92Cell93Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (1051 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 29594481467553 / 500000000000)]
  obtain ⟨l, hl, hb, hf⟩ :=
    uniformKorselt_reject_gamma hn ho hu hGRH (X := (1051 : ℝ)) (x := (gammaMainCell92Scale : ℝ))
      (by norm_num only [gammaMainCell92Scale, Rat.cast_div, Rat.cast_ofNat]) (Finset.Ioc 0 1051)
      (by
        intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
      (by norm_num only) (gammaFixed92Cell93_gap hGRH.riemann hhi)
  exact ⟨l, hl, hb.trans hcut, hf⟩

/-- Under GRH, a uniform Korselt triple in grouped Gamma cells 107 to 120
has a rejecting prime inside the `3/10` cutoff. The shared-scale gap yields
an actual witness below 1153, and the left endpoint bounds that cutoff. -/
theorem uniform_gamma_fixed92_107 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (61994623422789 / 1000000000000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (gammaFixed92Cell107Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (1153 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 61994623422789 / 1000000000000)]
  obtain ⟨l, hl, hb, hf⟩ :=
    uniformKorselt_reject_gamma hn ho hu hGRH (X := (1153 : ℝ)) (x := (gammaMainCell92Scale : ℝ))
      (by norm_num only [gammaMainCell92Scale, Rat.cast_div, Rat.cast_ofNat]) (Finset.Ioc 0 1153)
      (by
        intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
      (by norm_num only) (gammaFixed92Cell107_gap hGRH.riemann hhi)
  exact ⟨l, hl, hb.trans hcut, hf⟩

/-- Under GRH, a uniform Korselt triple in grouped Gamma cells 121 to 133
has a rejecting prime inside the `3/10` cutoff. The shared-scale gap yields
an actual witness below 1259, and the left endpoint bounds that cutoff. -/
theorem uniform_gamma_fixed92_121 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (16195421163609 / 250000000000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (gammaFixed92Cell121Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (1259 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 16195421163609 / 250000000000)]
  obtain ⟨l, hl, hb, hf⟩ :=
    uniformKorselt_reject_gamma hn ho hu hGRH (X := (1259 : ℝ)) (x := (gammaMainCell92Scale : ℝ))
      (by norm_num only [gammaMainCell92Scale, Rat.cast_div, Rat.cast_ofNat]) (Finset.Ioc 0 1259)
      (by
        intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
      (by norm_num only) (gammaFixed92Cell121_gap hGRH.riemann hhi)
  exact ⟨l, hl, hb.trans hcut, hf⟩

/-- Under GRH, all odd composites from logarithmic scale 8 through this
block's last endpoint have a rejecting prime within the `3/10` cutoff.
Adjacent closed intervals connect the new witnesses to the preceding block. -/
theorem exists_reject_03_fixed92_block1 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ (gammaFixed92Cell121Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  by_cases hu : UniformKorseltTriple n
  · by_cases hprev : Real.log n ≤ (gammaFixed92Cell64Right : ℝ)
    · exact exists_reject_03_fixed92_block0 hn ho hc hGRH hL hprev
    · by_cases h71 : Real.log n ≤ (gammaFixed92Cell71Right : ℝ)
      · apply uniform_gamma_fixed92_71 hn ho hu hGRH _ h71
        have h := le_of_not_ge hprev
        norm_num only [gammaFixed92Cell64Right, Rat.cast_div, Rat.cast_ofNat] at h
        exact h
      · by_cases h80 : Real.log n ≤ (gammaFixed92Cell80Right : ℝ)
        · apply uniform_gamma_fixed92_80 hn ho hu hGRH _ h80
          have h := le_of_not_ge h71
          norm_num only [gammaFixed92Cell71Right, Rat.cast_div, Rat.cast_ofNat] at h
          exact h
        · by_cases h93 : Real.log n ≤ (gammaFixed92Cell93Right : ℝ)
          · apply uniform_gamma_fixed92_93 hn ho hu hGRH _ h93
            have h := le_of_not_ge h80
            norm_num only [gammaFixed92Cell80Right, Rat.cast_div, Rat.cast_ofNat] at h
            exact h
          · by_cases h107 : Real.log n ≤ (gammaFixed92Cell107Right : ℝ)
            · apply uniform_gamma_fixed92_107 hn ho hu hGRH _ h107
              have h := le_of_not_ge h93
              norm_num only [gammaFixed92Cell93Right, Rat.cast_div, Rat.cast_ofNat] at h
              exact h
            · apply uniform_gamma_fixed92_121 hn ho hu hGRH _ hU
              have h := le_of_not_ge h107
              norm_num only [gammaFixed92Cell107Right, Rat.cast_div, Rat.cast_ofNat] at h
              exact h
  · exact exists_prime_reject_03_nonuniform_log8 hn ho hc hu hGRH hL

end PseudoPrime.PrimeTestBounds.MillerRabin
