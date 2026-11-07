/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaTenCells
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaCell10Gap
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaCell11Gap
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaCell12Gap
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaCell13Gap

/-! # Finite Gamma cells ten through thirteen -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, a uniform Korselt triple in Gamma cell 10 has a
rejecting prime within the coefficient `3/10` cutoff. The certified gap
supplies the witness at cutoff 529, which the left endpoint bounds. -/
theorem uniform_gamma_cell10 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (41992062742063 / 1000000000000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (gammaCell10Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (529 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 41992062742063 / 1000000000000)]
  obtain ⟨l, hl, hb, hf⟩ :=
    uniformKorselt_reject_gamma hn ho hu hGRH (X := (529 : ℝ)) (x := (gammaMainCell10Scale : ℝ))
      (by norm_num only [gammaMainCell10Scale, Rat.cast_div, Rat.cast_ofNat]) (Finset.Ioc 0 529)
      (by
        intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
      (by norm_num only) (gammaCell10_gap hGRH.riemann hhi)
  exact ⟨l, hl, hb.trans hcut, hf⟩

/-- Under GRH, a uniform Korselt triple in Gamma cell 11 has a
rejecting prime within the coefficient `3/10` cutoff. The certified gap
supplies the witness at cutoff 541, which the left endpoint bounds. -/
theorem uniform_gamma_cell11 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (42465672411177 / 1000000000000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (gammaCell11Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (541 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 42465672411177 / 1000000000000)]
  obtain ⟨l, hl, hb, hf⟩ :=
    uniformKorselt_reject_gamma hn ho hu hGRH (X := (541 : ℝ)) (x := (gammaMainCell11Scale : ℝ))
      (by norm_num only [gammaMainCell11Scale, Rat.cast_div, Rat.cast_ofNat]) (Finset.Ioc 0 541)
      (by
        intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
      (by norm_num only) (gammaCell11_gap hGRH.riemann hhi)
  exact ⟨l, hl, hb.trans hcut, hf⟩

/-- Under GRH, a uniform Korselt triple in Gamma cell 12 has a
rejecting prime within the coefficient `3/10` cutoff. The certified gap
supplies the witness at cutoff 547, which the left endpoint bounds. -/
theorem uniform_gamma_cell12 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (42700507413067 / 1000000000000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (gammaCell12Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (547 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 42700507413067 / 1000000000000)]
  obtain ⟨l, hl, hb, hf⟩ :=
    uniformKorselt_reject_gamma hn ho hu hGRH (X := (547 : ℝ)) (x := (gammaMainCell12Scale : ℝ))
      (by norm_num only [gammaMainCell12Scale, Rat.cast_div, Rat.cast_ofNat]) (Finset.Ioc 0 547)
      (by
        intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
      (by norm_num only) (gammaCell12_gap hGRH.riemann hhi)
  exact ⟨l, hl, hb.trans hcut, hf⟩

/-- Under GRH, a uniform Korselt triple in Gamma cell 13 has a
rejecting prime within the coefficient `3/10` cutoff. The certified gap
supplies the witness at cutoff 557, which the left endpoint bounds. -/
theorem uniform_gamma_cell13 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (21544527534079 / 500000000000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (gammaCell13Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (557 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 21544527534079 / 500000000000)]
  obtain ⟨l, hl, hb, hf⟩ :=
    uniformKorselt_reject_gamma hn ho hu hGRH (X := (557 : ℝ)) (x := (gammaMainCell13Scale : ℝ))
      (by norm_num only [gammaMainCell13Scale, Rat.cast_div, Rat.cast_ofNat]) (Finset.Ioc 0 557)
      (by
        intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
      (by norm_num only) (gammaCell13_gap hGRH.riemann hhi)
  exact ⟨l, hl, hb.trans hcut, hf⟩

/-- Under GRH, the first fourteen Gamma cells and the low bridge provide a
`3/10` rejecting-prime witness for every odd composite through the last
cell endpoint. Consecutive certified endpoints cover the entire interval. -/
theorem exists_reject_03_low_fourteen_cells {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ (gammaCell13Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  by_cases hu : UniformKorseltTriple n
  · by_cases h9 : Real.log n ≤ (gammaCell9Right : ℝ)
    · exact exists_reject_03_low_ten_cells hn ho hc hGRH hL h9
    · by_cases h10 : Real.log n ≤ (gammaCell10Right : ℝ)
      · apply uniform_gamma_cell10 hn ho hu hGRH _ h10
        have h := le_of_not_ge h9
        norm_num only [gammaCell9Right, Rat.cast_div, Rat.cast_ofNat] at h
        exact h
      · by_cases h11 : Real.log n ≤ (gammaCell11Right : ℝ)
        · apply uniform_gamma_cell11 hn ho hu hGRH _ h11
          have h := le_of_not_ge h10
          norm_num only [gammaCell10Right, Rat.cast_div, Rat.cast_ofNat] at h
          exact h
        · by_cases h12 : Real.log n ≤ (gammaCell12Right : ℝ)
          · apply uniform_gamma_cell12 hn ho hu hGRH _ h12
            have h := le_of_not_ge h11
            norm_num only [gammaCell11Right, Rat.cast_div, Rat.cast_ofNat] at h
            exact h
          · apply uniform_gamma_cell13 hn ho hu hGRH _ hU
            have h := le_of_not_ge h12
            norm_num only [gammaCell12Right, Rat.cast_div, Rat.cast_ofNat] at h
            exact h
  · exact exists_prime_reject_03_nonuniform_log8 hn ho hc hu hGRH hL

end PseudoPrime.PrimeTestBounds.MillerRabin
