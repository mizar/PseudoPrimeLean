/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaFourteenCells
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaCell14Gap
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaCell15Gap
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaCell16Gap
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaCell17Gap

/-! # Finite Gamma cells fourteen through seventeen -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, a uniform Korselt triple in Gamma cell 14 has a
rejecting prime within the coefficient `3/10` cutoff. The certified gap
supplies the witness at cutoff 563, which the left endpoint bounds. -/
theorem uniform_gamma_cell14 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (21660255461713 / 500000000000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (gammaCell14Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (563 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 21660255461713 / 500000000000)]
  obtain ⟨l, hl, hb, hf⟩ :=
    uniformKorselt_reject_gamma hn ho hu hGRH (X := (563 : ℝ)) (x := (gammaMainCell14Scale : ℝ))
      (by norm_num only [gammaMainCell14Scale, Rat.cast_div, Rat.cast_ofNat]) (Finset.Ioc 0 563)
      (by
        intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
      (by norm_num only) (gammaCell14_gap hGRH.riemann hhi)
  exact ⟨l, hl, hb.trans hcut, hf⟩

/-- Under GRH, a uniform Korselt triple in Gamma cell 15 has a
rejecting prime within the coefficient `3/10` cutoff. The certified gap
supplies the witness at cutoff 569, which the left endpoint bounds. -/
theorem uniform_gamma_cell15 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (43550736694879 / 1000000000000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (gammaCell15Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (569 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 43550736694879 / 1000000000000)]
  obtain ⟨l, hl, hb, hf⟩ :=
    uniformKorselt_reject_gamma hn ho hu hGRH (X := (569 : ℝ)) (x := (gammaMainCell15Scale : ℝ))
      (by norm_num only [gammaMainCell15Scale, Rat.cast_div, Rat.cast_ofNat]) (Finset.Ioc 0 569)
      (by
        intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
      (by norm_num only) (gammaCell15_gap hGRH.riemann hhi)
  exact ⟨l, hl, hb.trans hcut, hf⟩

/-- Under GRH, a uniform Korselt triple in Gamma cell 16 has a
rejecting prime within the coefficient `3/10` cutoff. The certified gap
supplies the witness at cutoff 571, which the left endpoint bounds. -/
theorem uniform_gamma_cell16 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (43627208635591 / 1000000000000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (gammaCell16Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (571 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 43627208635591 / 1000000000000)]
  obtain ⟨l, hl, hb, hf⟩ :=
    uniformKorselt_reject_gamma hn ho hu hGRH (X := (571 : ℝ)) (x := (gammaMainCell16Scale : ℝ))
      (by norm_num only [gammaMainCell16Scale, Rat.cast_div, Rat.cast_ofNat]) (Finset.Ioc 0 571)
      (by
        intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
      (by norm_num only) (gammaCell16_gap hGRH.riemann hhi)
  exact ⟨l, hl, hb.trans hcut, hf⟩

/-- Under GRH, a uniform Korselt triple in Gamma cell 17 has a
rejecting prime within the coefficient `3/10` cutoff. The certified gap
supplies the witness at cutoff 577, which the left endpoint bounds. -/
theorem uniform_gamma_cell17 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (43855824394639 / 1000000000000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (gammaCell17Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (577 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 43855824394639 / 1000000000000)]
  obtain ⟨l, hl, hb, hf⟩ :=
    uniformKorselt_reject_gamma hn ho hu hGRH (X := (577 : ℝ)) (x := (gammaMainCell17Scale : ℝ))
      (by norm_num only [gammaMainCell17Scale, Rat.cast_div, Rat.cast_ofNat]) (Finset.Ioc 0 577)
      (by
        intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
      (by norm_num only) (gammaCell17_gap hGRH.riemann hhi)
  exact ⟨l, hl, hb.trans hcut, hf⟩

/-- Under GRH, the first eighteen Gamma cells and the low bridge provide a
`3/10` rejecting-prime witness for every odd composite through the last
cell endpoint. Consecutive certified endpoints cover the entire interval. -/
theorem exists_reject_03_low_eighteen_cells {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ (gammaCell17Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  by_cases hu : UniformKorseltTriple n
  · by_cases h13 : Real.log n ≤ (gammaCell13Right : ℝ)
    · exact exists_reject_03_low_fourteen_cells hn ho hc hGRH hL h13
    · by_cases h14 : Real.log n ≤ (gammaCell14Right : ℝ)
      · apply uniform_gamma_cell14 hn ho hu hGRH _ h14
        have h := le_of_not_ge h13
        norm_num only [gammaCell13Right, Rat.cast_div, Rat.cast_ofNat] at h
        exact h
      · by_cases h15 : Real.log n ≤ (gammaCell15Right : ℝ)
        · apply uniform_gamma_cell15 hn ho hu hGRH _ h15
          have h := le_of_not_ge h14
          norm_num only [gammaCell14Right, Rat.cast_div, Rat.cast_ofNat] at h
          exact h
        · by_cases h16 : Real.log n ≤ (gammaCell16Right : ℝ)
          · apply uniform_gamma_cell16 hn ho hu hGRH _ h16
            have h := le_of_not_ge h15
            norm_num only [gammaCell15Right, Rat.cast_div, Rat.cast_ofNat] at h
            exact h
          · apply uniform_gamma_cell17 hn ho hu hGRH _ hU
            have h := le_of_not_ge h16
            norm_num only [gammaCell16Right, Rat.cast_div, Rat.cast_ofNat] at h
            exact h
  · exact exists_prime_reject_03_nonuniform_log8 hn ho hc hu hGRH hL

end PseudoPrime.PrimeTestBounds.MillerRabin
