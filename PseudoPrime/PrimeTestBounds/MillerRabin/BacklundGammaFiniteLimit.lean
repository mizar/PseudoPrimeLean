/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.BacklundGammaCellIntegral
public import PseudoPrime.AnalyticNumberTheory.Gamma.EndpointLimits
public import PseudoPrime.AnalyticNumberTheory.Gamma.StirlingCell
public import PseudoPrime.AnalyticNumberTheory.Gamma.EulerLogPartial

/-! # Passage from finite Gamma identities to the remainder -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- If the finite Euler–Maclaurin imaginary identity holds at every natural
cutoff, its limit identifies the imaginary Gamma remainder with the complex
kernel integral. The proof combines the correction-series, kernel-integral
and harmonic-phase limits, without evaluating a real Stirling constant. -/
theorem gamma_remainder_im_of_finite {a y : ℝ} (ha : 0 < a)
    (h :
      ∀ N : ℕ,
        (AnalyticNumberTheory.Gamma.backlundGammaPartial ((a : ℂ) + (y : ℂ) * Complex.I) N -
              AnalyticNumberTheory.Gamma.backlundStirlingMain ((a : ℂ) + (y : ℂ) * Complex.I) -
              ∫ u in (0 : ℝ)..(N : ℝ), backlundGammaComplexKernel a y u).im =
          y * ((harmonic N : ℝ) - Real.eulerMascheroniConstant) -
            (AnalyticNumberTheory.Gamma.backlundStirlingMain
                ((N : ℂ) + ((a : ℂ) + (y : ℂ) * Complex.I))).im) :
    (AnalyticNumberTheory.Gamma.logGammaSeries ((a : ℂ) + (y : ℂ) * Complex.I) -
          AnalyticNumberTheory.Gamma.backlundStirlingMain ((a : ℂ) + (y : ℂ) * Complex.I) -
          ∫ u in Set.Ioi (0 : ℝ), backlundGammaComplexKernel a y u).im =
      0 := by
  let z : ℂ := (a : ℂ) + (y : ℂ) * Complex.I
  have hz : 0 < z.re := by
    simpa only [z, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero] using ha
  have hgp := AnalyticNumberTheory.Gamma.gamma_partial_tendsto hz
  have hi :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi 0
      (backlundGammaComplexKernel_integrable (y := y) ha) tendsto_natCast_atTop_atTop
  have ht := (hgp.sub_const (AnalyticNumberTheory.Gamma.backlundStirlingMain z)).sub hi
  have him := (Complex.imCLM.continuous.tendsto _).comp ht
  simp only [Function.comp_def, Complex.imCLM_apply] at him
  have hr := AnalyticNumberTheory.Gamma.gamma_harmonic_phase_tendsto hz
  have hzi : z.im = y := by
    simp only [z, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
  rw [hzi] at hr
  change
    Filter.Tendsto
      (fun n : ℕ ↦
        y * ((harmonic n : ℝ) - Real.eulerMascheroniConstant) -
          (AnalyticNumberTheory.Gamma.backlundStirlingMain ((n : ℂ) + z)).im)
      Filter.atTop (nhds 0) at hr
  have he :
    (fun n : ℕ ↦
        (AnalyticNumberTheory.Gamma.backlundGammaPartial z n -
            AnalyticNumberTheory.Gamma.backlundStirlingMain z -
            ∫ u in (0 : ℝ)..(n : ℝ), backlundGammaComplexKernel a y u).im) =ᶠ[Filter.atTop]
      (fun n : ℕ ↦
        y * ((harmonic n : ℝ) - Real.eulerMascheroniConstant) -
          (AnalyticNumberTheory.Gamma.backlundStirlingMain ((n : ℂ) + z)).im) :=
    Filter.Eventually.of_forall h
  exact tendsto_nhds_unique him (hr.congr' he.symm)

/-- The finite Euler–Maclaurin imaginary identity at each required height
and natural cutoff. This proposition states the remaining finite identity;
it is not itself a proof of that identity. -/
def BacklundGammaFiniteIdentity : Prop :=
  ∀ t : ℝ,
    2 * Real.pi * Real.exp 1 ≤ t →
      ∀ N : ℕ,
        let z : ℂ := ((1 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I
        (AnalyticNumberTheory.Gamma.backlundGammaPartial z N -
              AnalyticNumberTheory.Gamma.backlundStirlingMain z -
              ∫ u in (0 : ℝ)..(N : ℝ), backlundGammaComplexKernel (1 / 4) (t / 2) u).im =
          (t / 2) * ((harmonic N : ℝ) - Real.eulerMascheroniConstant) -
            (AnalyticNumberTheory.Gamma.backlundStirlingMain ((N : ℂ) + z)).im

/-- The finite imaginary identity implies the complex Gamma representation
required by the zero-count argument. Its real constant may depend on the
height and is chosen as the real part of the difference. -/
theorem gamma_complex_identity_of_finite (h : BacklundGammaFiniteIdentity) :
    BacklundGammaComplexIdentity := by
  intro t ht
  let z : ℂ := ((1 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I
  let r : ℂ := ∫ u in Set.Ioi (0 : ℝ), backlundGammaComplexKernel (1 / 4) (t / 2) u
  have him :
    (AnalyticNumberTheory.Gamma.logGammaSeries z -
          AnalyticNumberTheory.Gamma.backlundStirlingMain z -
          r).im =
      0 :=
    gamma_remainder_im_of_finite (by norm_num only) (h t ht)
  refine
    ⟨(AnalyticNumberTheory.Gamma.logGammaSeries z -
          AnalyticNumberTheory.Gamma.backlundStirlingMain z -
          r).re,
      ?_⟩
  change
    AnalyticNumberTheory.Gamma.logGammaSeries z -
        AnalyticNumberTheory.Gamma.backlundStirlingMain z =
      ((AnalyticNumberTheory.Gamma.logGammaSeries z -
              AnalyticNumberTheory.Gamma.backlundStirlingMain z -
              r).re :
          ℂ) +
        r
  apply Complex.ext
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.sub_re]
    ring
  · simp only [Complex.add_im, Complex.ofReal_im, zero_add]
    simpa only [Complex.sub_im, sub_eq_zero] using him

/-- Under GRH, the normalized zero-count identity and the finite Gamma
identity imply the least-prime `3/11` witness bound for odd composites.
The limiting and real-constant steps are discharged internally. -/
theorem three_eleven_least_of_gamma_finite {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hV : EulerRiemannVonMangoldt)
    (hI : BacklundGammaFiniteIdentity) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ max 2 ((3 / 11 : ℝ) * Real.log n ^ 2) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  exact three_eleven_least_of_gamma_complex hn ho hc hGRH hV (gamma_complex_identity_of_finite hI)

end PseudoPrime.PrimeTestBounds.MillerRabin
