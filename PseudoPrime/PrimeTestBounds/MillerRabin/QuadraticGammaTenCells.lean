/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaUniformTransfer
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaCell3Gap
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaCell4Gap
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaCell5Gap
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaCell6Gap
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaCell7Gap
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaCell8Gap
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaCell9Gap

/-! # Finite Gamma cells three through nine -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, a uniform Korselt triple in Gamma cell 3 has a
rejecting prime within the coefficient `3/10` cutoff. The certified gap
supplies the witness at cutoff 491, which the left endpoint bounds. -/
theorem uniform_gamma_cell3 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (40455737129197 / 1000000000000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (gammaCell3Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (491 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 40455737129197 / 1000000000000)]
  obtain ⟨l, hl, hb, hf⟩ :=
    uniformKorselt_reject_gamma hn ho hu hGRH (X := (491 : ℝ)) (x := (gammaMainCell3Scale : ℝ))
      (by norm_num only [gammaMainCell3Scale, Rat.cast_div, Rat.cast_ofNat]) (Finset.Ioc 0 491)
      (by
        intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
      (by norm_num only) (gammaCell3_gap hGRH.riemann hhi)
  exact ⟨l, hl, hb.trans hcut, hf⟩

/-- Under GRH, a uniform Korselt triple in Gamma cell 4 has a
rejecting prime within the coefficient `3/10` cutoff. The certified gap
supplies the witness at cutoff 499, which the left endpoint bounds. -/
theorem uniform_gamma_cell4 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (5097997973061 / 125000000000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (gammaCell4Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (499 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 5097997973061 / 125000000000)]
  obtain ⟨l, hl, hb, hf⟩ :=
    uniformKorselt_reject_gamma hn ho hu hGRH (X := (499 : ℝ)) (x := (gammaMainCell4Scale : ℝ))
      (by norm_num only [gammaMainCell4Scale, Rat.cast_div, Rat.cast_ofNat]) (Finset.Ioc 0 499)
      (by
        intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
      (by norm_num only) (gammaCell4_gap hGRH.riemann hhi)
  exact ⟨l, hl, hb.trans hcut, hf⟩

/-- Under GRH, a uniform Korselt triple in Gamma cell 5 has a
rejecting prime within the coefficient `3/10` cutoff. The certified gap
supplies the witness at cutoff 503, which the left endpoint bounds. -/
theorem uniform_gamma_cell5 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (5118390046359 / 125000000000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (gammaCell5Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (503 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 5118390046359 / 125000000000)]
  obtain ⟨l, hl, hb, hf⟩ :=
    uniformKorselt_reject_gamma hn ho hu hGRH (X := (503 : ℝ)) (x := (gammaMainCell5Scale : ℝ))
      (by norm_num only [gammaMainCell5Scale, Rat.cast_div, Rat.cast_ofNat]) (Finset.Ioc 0 503)
      (by
        intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
      (by norm_num only) (gammaCell5_gap hGRH.riemann hhi)
  exact ⟨l, hl, hb.trans hcut, hf⟩

/-- Under GRH, a uniform Korselt triple in Gamma cell 6 has a
rejecting prime within the coefficient `3/10` cutoff. The certified gap
supplies the witness at cutoff 509, which the left endpoint bounds. -/
theorem uniform_gamma_cell6 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (2574413363597 / 62500000000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (gammaCell6Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (509 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 2574413363597 / 62500000000)]
  obtain ⟨l, hl, hb, hf⟩ :=
    uniformKorselt_reject_gamma hn ho hu hGRH (X := (509 : ℝ)) (x := (gammaMainCell6Scale : ℝ))
      (by norm_num only [gammaMainCell6Scale, Rat.cast_div, Rat.cast_ofNat]) (Finset.Ioc 0 509)
      (by
        intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
      (by norm_num only) (gammaCell6_gap hGRH.riemann hhi)
  exact ⟨l, hl, hb.trans hcut, hf⟩

/-- Under GRH, a uniform Korselt triple in Gamma cell 7 has a
rejecting prime within the coefficient `3/10` cutoff. The certified gap
supplies the witness at cutoff 512, which the left endpoint bounds. -/
theorem uniform_gamma_cell7 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (20655911179773 / 500000000000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (gammaCell7Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (512 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 20655911179773 / 500000000000)]
  obtain ⟨l, hl, hb, hf⟩ :=
    uniformKorselt_reject_gamma hn ho hu hGRH (X := (512 : ℝ)) (x := (gammaMainCell7Scale : ℝ))
      (by norm_num only [gammaMainCell7Scale, Rat.cast_div, Rat.cast_ofNat]) (Finset.Ioc 0 512)
      (by
        intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
      (by norm_num only) (gammaCell7_gap hGRH.riemann hhi)
  exact ⟨l, hl, hb.trans hcut, hf⟩

/-- Under GRH, a uniform Korselt triple in Gamma cell 8 has a
rejecting prime within the coefficient `3/10` cutoff. The certified gap
supplies the witness at cutoff 521, which the left endpoint bounds. -/
theorem uniform_gamma_cell8 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (20836666400043 / 500000000000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (gammaCell8Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (521 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 20836666400043 / 500000000000)]
  obtain ⟨l, hl, hb, hf⟩ :=
    uniformKorselt_reject_gamma hn ho hu hGRH (X := (521 : ℝ)) (x := (gammaMainCell8Scale : ℝ))
      (by norm_num only [gammaMainCell8Scale, Rat.cast_div, Rat.cast_ofNat]) (Finset.Ioc 0 521)
      (by
        intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
      (by norm_num only) (gammaCell8_gap hGRH.riemann hhi)
  exact ⟨l, hl, hb.trans hcut, hf⟩

/-- Under GRH, a uniform Korselt triple in Gamma cell 9 has a
rejecting prime within the coefficient `3/10` cutoff. The certified gap
supplies the witness at cutoff 523, which the left endpoint bounds. -/
theorem uniform_gamma_cell9 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (2609577711687 / 62500000000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (gammaCell9Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (523 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 2609577711687 / 62500000000)]
  obtain ⟨l, hl, hb, hf⟩ :=
    uniformKorselt_reject_gamma hn ho hu hGRH (X := (523 : ℝ)) (x := (gammaMainCell9Scale : ℝ))
      (by norm_num only [gammaMainCell9Scale, Rat.cast_div, Rat.cast_ofNat]) (Finset.Ioc 0 523)
      (by
        intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
      (by norm_num only) (gammaCell9_gap hGRH.riemann hhi)
  exact ⟨l, hl, hb.trans hcut, hf⟩

/-- Under GRH, the first ten Gamma cells and the low bridge provide a
`3/10` rejecting-prime witness for every odd composite through the last
cell endpoint. Consecutive certified endpoints cover the entire interval. -/
theorem exists_reject_03_low_ten_cells {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ (gammaCell9Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  by_cases hu : UniformKorseltTriple n
  · by_cases h2 : Real.log n ≤ (gammaThirdRight : ℝ)
    · exact exists_reject_03_low_three_cells hn ho hc hGRH hL h2
    · by_cases h3 : Real.log n ≤ (gammaCell3Right : ℝ)
      · apply uniform_gamma_cell3 hn ho hu hGRH _ h3
        have h := le_of_not_ge h2
        norm_num only [gammaThirdRight, Rat.cast_div, Rat.cast_ofNat] at h
        exact h
      · by_cases h4 : Real.log n ≤ (gammaCell4Right : ℝ)
        · apply uniform_gamma_cell4 hn ho hu hGRH _ h4
          have h := le_of_not_ge h3
          norm_num only [gammaCell3Right, Rat.cast_div, Rat.cast_ofNat] at h
          exact h
        · by_cases h5 : Real.log n ≤ (gammaCell5Right : ℝ)
          · apply uniform_gamma_cell5 hn ho hu hGRH _ h5
            have h := le_of_not_ge h4
            norm_num only [gammaCell4Right, Rat.cast_div, Rat.cast_ofNat] at h
            exact h
          · by_cases h6 : Real.log n ≤ (gammaCell6Right : ℝ)
            · apply uniform_gamma_cell6 hn ho hu hGRH _ h6
              have h := le_of_not_ge h5
              norm_num only [gammaCell5Right, Rat.cast_div, Rat.cast_ofNat] at h
              exact h
            · by_cases h7 : Real.log n ≤ (gammaCell7Right : ℝ)
              · apply uniform_gamma_cell7 hn ho hu hGRH _ h7
                have h := le_of_not_ge h6
                norm_num only [gammaCell6Right, Rat.cast_div, Rat.cast_ofNat] at h
                exact h
              · by_cases h8 : Real.log n ≤ (gammaCell8Right : ℝ)
                · apply uniform_gamma_cell8 hn ho hu hGRH _ h8
                  have h := le_of_not_ge h7
                  norm_num only [gammaCell7Right, Rat.cast_div, Rat.cast_ofNat] at h
                  exact h
                · apply uniform_gamma_cell9 hn ho hu hGRH _ hU
                  have h := le_of_not_ge h8
                  norm_num only [gammaCell8Right, Rat.cast_div, Rat.cast_ofNat] at h
                  exact h
  · exact exists_prime_reject_03_nonuniform_log8 hn ho hc hu hGRH hL

end PseudoPrime.PrimeTestBounds.MillerRabin
