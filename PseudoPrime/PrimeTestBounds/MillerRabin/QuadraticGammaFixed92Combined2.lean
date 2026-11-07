/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaFixed92Combined1
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaFixed92Gap2

/-! # Shared-scale Gamma interval coverage, block 2 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, a uniform Korselt triple in grouped Gamma cells 134 to 144
has a rejecting prime inside the `3/10` cutoff. The shared-scale gap yields
an actual witness below 1331, and the left endpoint bounds that cutoff. -/
theorem uniform_gamma_fixed92_134 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (13321661558029 / 200000000000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (gammaFixed92Cell134Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (1331 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 13321661558029 / 200000000000)]
  obtain ⟨l, hl, hb, hf⟩ :=
    uniformKorselt_reject_gamma hn ho hu hGRH (X := (1331 : ℝ)) (x := (gammaMainCell92Scale : ℝ))
      (by norm_num only [gammaMainCell92Scale, Rat.cast_div, Rat.cast_ofNat]) (Finset.Ioc 0 1331)
      (by
        intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
      (by norm_num only) (gammaFixed92Cell134_gap hGRH.riemann hhi)
  exact ⟨l, hl, hb.trans hcut, hf⟩

/-- Under GRH, a uniform Korselt triple in grouped Gamma cells 145 to 155
has a rejecting prime inside the `3/10` cutoff. The shared-scale gap yields
an actual witness below 1433, and the left endpoint bounds that cutoff. -/
theorem uniform_gamma_fixed92_145 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (34556716665023 / 500000000000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (gammaFixed92Cell145Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (1433 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 34556716665023 / 500000000000)]
  obtain ⟨l, hl, hb, hf⟩ :=
    uniformKorselt_reject_gamma hn ho hu hGRH (X := (1433 : ℝ)) (x := (gammaMainCell92Scale : ℝ))
      (by norm_num only [gammaMainCell92Scale, Rat.cast_div, Rat.cast_ofNat]) (Finset.Ioc 0 1433)
      (by
        intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
      (by norm_num only) (gammaFixed92Cell145_gap hGRH.riemann hhi)
  exact ⟨l, hl, hb.trans hcut, hf⟩

/-- Under GRH, a uniform Korselt triple in grouped Gamma cells 156 to 162
has a rejecting prime inside the `3/10` cutoff. The shared-scale gap yields
an actual witness below 1493, and the left endpoint bounds that cutoff. -/
theorem uniform_gamma_fixed92_156 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (70545493595741 / 1000000000000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (gammaFixed92Cell156Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (1493 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 70545493595741 / 1000000000000)]
  obtain ⟨l, hl, hb, hf⟩ :=
    uniformKorselt_reject_gamma hn ho hu hGRH (X := (1493 : ℝ)) (x := (gammaMainCell92Scale : ℝ))
      (by norm_num only [gammaMainCell92Scale, Rat.cast_div, Rat.cast_ofNat]) (Finset.Ioc 0 1493)
      (by
        intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
      (by norm_num only) (gammaFixed92Cell156_gap hGRH.riemann hhi)
  exact ⟨l, hl, hb.trans hcut, hf⟩

/-- Under GRH, a uniform Korselt triple in grouped Gamma cells 163 to 167
has a rejecting prime inside the `3/10` cutoff. The shared-scale gap yields
an actual witness below 1553, and the left endpoint bounds that cutoff. -/
theorem uniform_gamma_fixed92_163 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (8993632006407 / 125000000000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (gammaFixed92Cell163Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (1553 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 8993632006407 / 125000000000)]
  obtain ⟨l, hl, hb, hf⟩ :=
    uniformKorselt_reject_gamma hn ho hu hGRH (X := (1553 : ℝ)) (x := (gammaMainCell92Scale : ℝ))
      (by norm_num only [gammaMainCell92Scale, Rat.cast_div, Rat.cast_ofNat]) (Finset.Ioc 0 1553)
      (by
        intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
      (by norm_num only) (gammaFixed92Cell163_gap hGRH.riemann hhi)
  exact ⟨l, hl, hb.trans hcut, hf⟩

/-- Under GRH, a uniform Korselt triple in grouped Gamma cells 168 to 171
has a rejecting prime inside the `3/10` cutoff. The shared-scale gap yields
an actual witness below 1583, and the left endpoint bounds that cutoff. -/
theorem uniform_gamma_fixed92_168 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (72640668132023 / 1000000000000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (gammaFixed92Cell168Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (1583 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 72640668132023 / 1000000000000)]
  obtain ⟨l, hl, hb, hf⟩ :=
    uniformKorselt_reject_gamma hn ho hu hGRH (X := (1583 : ℝ)) (x := (gammaMainCell92Scale : ℝ))
      (by norm_num only [gammaMainCell92Scale, Rat.cast_div, Rat.cast_ofNat]) (Finset.Ioc 0 1583)
      (by
        intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
      (by norm_num only) (gammaFixed92Cell168_gap hGRH.riemann hhi)
  exact ⟨l, hl, hb.trans hcut, hf⟩

/-- Under GRH, all odd composites from logarithmic scale 8 through this
block's last endpoint have a rejecting prime within the `3/10` cutoff.
Adjacent closed intervals connect the new witnesses to the preceding block. -/
theorem exists_reject_03_fixed92_block2 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ (gammaFixed92Cell168Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  by_cases hu : UniformKorseltTriple n
  · by_cases hprev : Real.log n ≤ (gammaFixed92Cell121Right : ℝ)
    · exact exists_reject_03_fixed92_block1 hn ho hc hGRH hL hprev
    · by_cases h134 : Real.log n ≤ (gammaFixed92Cell134Right : ℝ)
      · apply uniform_gamma_fixed92_134 hn ho hu hGRH _ h134
        have h := le_of_not_ge hprev
        norm_num only [gammaFixed92Cell121Right, Rat.cast_div, Rat.cast_ofNat] at h
        exact h
      · by_cases h145 : Real.log n ≤ (gammaFixed92Cell145Right : ℝ)
        · apply uniform_gamma_fixed92_145 hn ho hu hGRH _ h145
          have h := le_of_not_ge h134
          norm_num only [gammaFixed92Cell134Right, Rat.cast_div, Rat.cast_ofNat] at h
          exact h
        · by_cases h156 : Real.log n ≤ (gammaFixed92Cell156Right : ℝ)
          · apply uniform_gamma_fixed92_156 hn ho hu hGRH _ h156
            have h := le_of_not_ge h145
            norm_num only [gammaFixed92Cell145Right, Rat.cast_div, Rat.cast_ofNat] at h
            exact h
          · by_cases h163 : Real.log n ≤ (gammaFixed92Cell163Right : ℝ)
            · apply uniform_gamma_fixed92_163 hn ho hu hGRH _ h163
              have h := le_of_not_ge h156
              norm_num only [gammaFixed92Cell156Right, Rat.cast_div, Rat.cast_ofNat] at h
              exact h
            · apply uniform_gamma_fixed92_168 hn ho hu hGRH _ hU
              have h := le_of_not_ge h163
              norm_num only [gammaFixed92Cell163Right, Rat.cast_div, Rat.cast_ofNat] at h
              exact h
  · exact exists_prime_reject_03_nonuniform_log8 hn ho hc hu hGRH hL

end PseudoPrime.PrimeTestBounds.MillerRabin
