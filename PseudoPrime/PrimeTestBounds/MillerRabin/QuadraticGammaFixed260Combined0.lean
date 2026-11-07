/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaFixed92Combined3
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaFixed260Gap0

/-! # Shared-scale Gamma interval coverage, block 3 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, a uniform Korselt triple in grouped Gamma cells 177 to 185
has a rejecting prime inside the `3/10` cutoff. The shared-scale gap yields
an actual witness below 1637, and the left endpoint bounds that cutoff. -/
theorem uniform_gamma_fixed260_177 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (73869253865643 / 1000000000000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (gammaFixed260Cell177Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (1637 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 73869253865643 / 1000000000000)]
  obtain ⟨l, hl, hb, hf⟩ :=
    uniformKorselt_reject_gamma hn ho hu hGRH (X := (1637 : ℝ)) (x := (gammaMainCell260Scale : ℝ))
      (by norm_num only [gammaMainCell260Scale, Rat.cast_div, Rat.cast_ofNat]) (Finset.Ioc 0 1637)
      (by
        intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
      (by norm_num only) (gammaFixed260Cell177_gap hGRH.riemann hhi)
  exact ⟨l, hl, hb.trans hcut, hf⟩

/-- Under GRH, a uniform Korselt triple in grouped Gamma cells 186 to 197
has a rejecting prime inside the `3/10` cutoff. The shared-scale gap yields
an actual witness below 1709, and the left endpoint bounds that cutoff. -/
theorem uniform_gamma_fixed260_186 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (37738132792531 / 500000000000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (gammaFixed260Cell186Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (1709 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 37738132792531 / 500000000000)]
  obtain ⟨l, hl, hb, hf⟩ :=
    uniformKorselt_reject_gamma hn ho hu hGRH (X := (1709 : ℝ)) (x := (gammaMainCell260Scale : ℝ))
      (by norm_num only [gammaMainCell260Scale, Rat.cast_div, Rat.cast_ofNat]) (Finset.Ioc 0 1709)
      (by
        intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
      (by norm_num only) (gammaFixed260Cell186_gap hGRH.riemann hhi)
  exact ⟨l, hl, hb.trans hcut, hf⟩

/-- Under GRH, a uniform Korselt triple in grouped Gamma cells 198 to 214
has a rejecting prime inside the `3/10` cutoff. The shared-scale gap yields
an actual witness below 1801, and the left endpoint bounds that cutoff. -/
theorem uniform_gamma_fixed260_198 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (77481180510711 / 1000000000000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (gammaFixed260Cell198Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (1801 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 77481180510711 / 1000000000000)]
  obtain ⟨l, hl, hb, hf⟩ :=
    uniformKorselt_reject_gamma hn ho hu hGRH (X := (1801 : ℝ)) (x := (gammaMainCell260Scale : ℝ))
      (by norm_num only [gammaMainCell260Scale, Rat.cast_div, Rat.cast_ofNat]) (Finset.Ioc 0 1801)
      (by
        intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
      (by norm_num only) (gammaFixed260Cell198_gap hGRH.riemann hhi)
  exact ⟨l, hl, hb.trans hcut, hf⟩

/-- Under GRH, a uniform Korselt triple in grouped Gamma cells 215 to 237
has a rejecting prime inside the `3/10` cutoff. The shared-scale gap yields
an actual witness below 1933, and the left endpoint bounds that cutoff. -/
theorem uniform_gamma_fixed260_215 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (80270376436973 / 1000000000000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (gammaFixed260Cell215Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (1933 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 80270376436973 / 1000000000000)]
  obtain ⟨l, hl, hb, hf⟩ :=
    uniformKorselt_reject_gamma hn ho hu hGRH (X := (1933 : ℝ)) (x := (gammaMainCell260Scale : ℝ))
      (by norm_num only [gammaMainCell260Scale, Rat.cast_div, Rat.cast_ofNat]) (Finset.Ioc 0 1933)
      (by
        intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
      (by norm_num only) (gammaFixed260Cell215_gap hGRH.riemann hhi)
  exact ⟨l, hl, hb.trans hcut, hf⟩

/-- Under GRH, the shared-scale intervals extend the existing `3/10` witness
coverage through this block's final endpoint. -/
theorem exists_reject_03_fixed260_block0 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ (gammaFixed260Cell215Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  by_cases hu : UniformKorseltTriple n
  · by_cases hprev : Real.log n ≤ (gammaFixed92Cell176Right : ℝ)
    · exact exists_reject_03_fixed92_block3 hn ho hc hGRH hL hprev
    · by_cases h177 : Real.log n ≤ (gammaFixed260Cell177Right : ℝ)
      · apply uniform_gamma_fixed260_177 hn ho hu hGRH _ h177
        have h := le_of_not_ge hprev
        norm_num only [gammaFixed92Cell176Right, Rat.cast_div, Rat.cast_ofNat] at h
        exact h
      · by_cases h186 : Real.log n ≤ (gammaFixed260Cell186Right : ℝ)
        · apply uniform_gamma_fixed260_186 hn ho hu hGRH _ h186
          have h := le_of_not_ge h177
          norm_num only [gammaFixed260Cell177Right, Rat.cast_div, Rat.cast_ofNat] at h
          exact h
        · by_cases h198 : Real.log n ≤ (gammaFixed260Cell198Right : ℝ)
          · apply uniform_gamma_fixed260_198 hn ho hu hGRH _ h198
            have h := le_of_not_ge h186
            norm_num only [gammaFixed260Cell186Right, Rat.cast_div, Rat.cast_ofNat] at h
            exact h
          · apply uniform_gamma_fixed260_215 hn ho hu hGRH _ hU
            have h := le_of_not_ge h198
            norm_num only [gammaFixed260Cell198Right, Rat.cast_div, Rat.cast_ofNat] at h
            exact h
  · exact exists_prime_reject_03_nonuniform_log8 hn ho hc hu hGRH hL

end PseudoPrime.PrimeTestBounds.MillerRabin
