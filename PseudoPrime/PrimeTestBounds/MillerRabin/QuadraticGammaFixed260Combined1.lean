/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaFixed260Combined0
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaFixed260Gap1

/-! # Shared-scale Gamma interval coverage, block 3 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, a uniform Korselt triple in grouped Gamma cells 238 to 267
has a rejecting prime inside the `3/10` cutoff. The shared-scale gap yields
an actual witness below 2099, and the left endpoint bounds that cutoff. -/
theorem uniform_gamma_fixed260_238 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (10455759975567 / 125000000000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (gammaFixed260Cell238Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (2099 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 10455759975567 / 125000000000)]
  obtain ⟨l, hl, hb, hf⟩ :=
    uniformKorselt_reject_gamma hn ho hu hGRH (X := (2099 : ℝ)) (x := (gammaMainCell260Scale : ℝ))
      (by norm_num only [gammaMainCell260Scale, Rat.cast_div, Rat.cast_ofNat]) (Finset.Ioc 0 2099)
      (by
        intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
      (by norm_num only) (gammaFixed260Cell238_gap hGRH.riemann hhi)
  exact ⟨l, hl, hb.trans hcut, hf⟩

/-- Under GRH, a uniform Korselt triple in grouped Gamma cells 268 to 299
has a rejecting prime inside the `3/10` cutoff. The shared-scale gap yields
an actual witness below 2311, and the left endpoint bounds that cutoff. -/
theorem uniform_gamma_fixed260_268 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (87768635248211 / 1000000000000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (gammaFixed260Cell268Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (2311 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 87768635248211 / 1000000000000)]
  obtain ⟨l, hl, hb, hf⟩ :=
    uniformKorselt_reject_gamma hn ho hu hGRH (X := (2311 : ℝ)) (x := (gammaMainCell260Scale : ℝ))
      (by norm_num only [gammaMainCell260Scale, Rat.cast_div, Rat.cast_ofNat]) (Finset.Ioc 0 2311)
      (by
        intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
      (by norm_num only) (gammaFixed260Cell268_gap hGRH.riemann hhi)
  exact ⟨l, hl, hb.trans hcut, hf⟩

/-- Under GRH, a uniform Korselt triple in grouped Gamma cells 300 to 334
has a rejecting prime inside the `3/10` cutoff. The shared-scale gap yields
an actual witness below 2557, and the left endpoint bounds that cutoff. -/
theorem uniform_gamma_fixed260_300 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (92321900615907 / 1000000000000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (gammaFixed260Cell300Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (2557 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 92321900615907 / 1000000000000)]
  obtain ⟨l, hl, hb, hf⟩ :=
    uniformKorselt_reject_gamma hn ho hu hGRH (X := (2557 : ℝ)) (x := (gammaMainCell260Scale : ℝ))
      (by norm_num only [gammaMainCell260Scale, Rat.cast_div, Rat.cast_ofNat]) (Finset.Ioc 0 2557)
      (by
        intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
      (by norm_num only) (gammaFixed260Cell300_gap hGRH.riemann hhi)
  exact ⟨l, hl, hb.trans hcut, hf⟩

/-- Under GRH, a uniform Korselt triple in grouped Gamma cells 335 to 356
has a rejecting prime inside the `3/10` cutoff. The shared-scale gap yields
an actual witness below 2809, and the left endpoint bounds that cutoff. -/
theorem uniform_gamma_fixed260_335 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (4838215924629 / 50000000000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (gammaFixed260Cell335Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (2809 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 4838215924629 / 50000000000)]
  obtain ⟨l, hl, hb, hf⟩ :=
    uniformKorselt_reject_gamma hn ho hu hGRH (X := (2809 : ℝ)) (x := (gammaMainCell260Scale : ℝ))
      (by norm_num only [gammaMainCell260Scale, Rat.cast_div, Rat.cast_ofNat]) (Finset.Ioc 0 2809)
      (by
        intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
      (by norm_num only) (gammaFixed260Cell335_gap hGRH.riemann hhi)
  exact ⟨l, hl, hb.trans hcut, hf⟩

/-- Under GRH, the shared-scale intervals extend the existing `3/10` witness
coverage through this block's final endpoint. -/
theorem exists_reject_03_fixed260_block1 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ (gammaFixed260Cell335Right : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  by_cases hu : UniformKorseltTriple n
  · by_cases hprev : Real.log n ≤ (gammaFixed260Cell215Right : ℝ)
    · exact exists_reject_03_fixed260_block0 hn ho hc hGRH hL hprev
    · by_cases h238 : Real.log n ≤ (gammaFixed260Cell238Right : ℝ)
      · apply uniform_gamma_fixed260_238 hn ho hu hGRH _ h238
        have h := le_of_not_ge hprev
        norm_num only [gammaFixed260Cell215Right, Rat.cast_div, Rat.cast_ofNat] at h
        exact h
      · by_cases h268 : Real.log n ≤ (gammaFixed260Cell268Right : ℝ)
        · apply uniform_gamma_fixed260_268 hn ho hu hGRH _ h268
          have h := le_of_not_ge h238
          norm_num only [gammaFixed260Cell238Right, Rat.cast_div, Rat.cast_ofNat] at h
          exact h
        · by_cases h300 : Real.log n ≤ (gammaFixed260Cell300Right : ℝ)
          · apply uniform_gamma_fixed260_300 hn ho hu hGRH _ h300
            have h := le_of_not_ge h268
            norm_num only [gammaFixed260Cell268Right, Rat.cast_div, Rat.cast_ofNat] at h
            exact h
          · apply uniform_gamma_fixed260_335 hn ho hu hGRH _ hU
            have h := le_of_not_ge h300
            norm_num only [gammaFixed260Cell300Right, Rat.cast_div, Rat.cast_ofNat] at h
            exact h
  · exact exists_prime_reject_03_nonuniform_log8 hn ho hc hu hGRH hL

end PseudoPrime.PrimeTestBounds.MillerRabin
