/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ExponentialRampSummation
public import PseudoPrime.NumberTheory.ResidueSubgroup
public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaSignedPrefixBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaPolynomialBudget
public import PseudoPrime.LLS.ClippedLogShiftPrincipalBounds
public import PseudoPrime.LLS.ClippedAffineWitnessBounds
public import PseudoPrime.LLS.GammaCheckpoint1000
public import PseudoPrime.LLS.QuadraticGammaSmoothedNumerics

/-! # Clipped-log Gamma comparison radius -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Extend the corrected arithmetic error constantly beyond the ramp support by
clamping its argument to the interval $[0,99/40]$. The extension is continuous,
so the variation functional can use the support-only continuity estimate. -/
noncomputable def gammaClippedErrorExtension (x u : ℝ) : ℝ :=
  PseudoPrime.LLS.clippedShiftError x (max 0 (min u (99 / 40 : ℝ)))

/-- For positive scale, the clamped corrected error is continuous on the whole
real line. Compose its continuity on the compact support with the continuous clamp. -/
theorem gammaClippedErrorExtension_continuous {x : ℝ} (hx : 0 < x) :
    Continuous (gammaClippedErrorExtension x) := by
  have hc : Continuous (fun u : ℝ => max 0 (min u (99 / 40 : ℝ))) :=
    continuous_const.max (continuous_id.min continuous_const)
  have hm : ∀ u : ℝ, max 0 (min u (99 / 40 : ℝ)) ∈ Set.Icc 0 (99 / 40 : ℝ) := by
    intro u
    constructor
    · exact le_max_left _ _
    · apply max_le
      · norm_num only
      · exact min_le_right _ _
  have hf := PseudoPrime.LLS.clippedShiftError_continuousOn hx (99 / 40)
  have hcomp :
    ContinuousOn (fun u : ℝ => PseudoPrime.LLS.clippedShiftError x (max 0 (min u (99 / 40 : ℝ))))
      Set.univ := by
    apply hf.comp hc.continuousOn
    intro u hu
    exact hm u
  exact continuousOn_univ.mp (show ContinuousOn (gammaClippedErrorExtension x) Set.univ from hcomp)

/-- On the ramp support, the clamped corrected error agrees with the original
corrected error. This lets the global variation functional use the compact RH bound. -/
theorem gammaClippedErrorExtension_eqOn {x : ℝ} :
    Set.EqOn (gammaClippedErrorExtension x) (PseudoPrime.LLS.clippedShiftError x)
      (Set.Icc 0 (99 / 40 : ℝ)) := by
  intro u hu
  dsimp only [gammaClippedErrorExtension]
  rw [min_eq_left hu.2, max_eq_right hu.1]

/-- Under RH, the variation of the corrected ramp error is bounded by the
compact envelope and the clipped endpoint increment. The support-only continuity
is handled by the clamped extension. -/
theorem gammaClippedError_variation_bound (hRH : RiemannHypothesis) {x h : ℝ} (hx : 1 ≤ x)
    (hh : 0 < h) (hhx : h ≤ x) :
    |PseudoPrime.LLS.exponentialRampVariationFunctional (PseudoPrime.LLS.clippedShiftError x)| ≤
      (3 / 2) * ((63 / 800 : ℝ) * Real.sqrt x + 21 / 20) +
        42 * (PseudoPrime.LLS.logShiftRampIncrement x h + 1 / 200) := by
  have hbound :
    ∀ u ∈ Set.Icc 0 (99 / 40 : ℝ),
      |gammaClippedErrorExtension x u| ≤ (63 / 800 : ℝ) * Real.sqrt x + 21 / 20 := by
    intro u hu
    rw [gammaClippedErrorExtension_eqOn hu]
    exact PseudoPrime.LLS.clippedShiftError_compact_le hRH hx hu.1 hu.2
  have hx0 : 0 < x := by linarith only [hx]
  have hleft :
    gammaClippedErrorExtension x (99 / 40) = PseudoPrime.LLS.clippedShiftError x (99 / 40) :=
    gammaClippedErrorExtension_eqOn ⟨by norm_num only, le_rfl⟩
  have hright :
    gammaClippedErrorExtension x (247 / 100) = PseudoPrime.LLS.clippedShiftError x (247 / 100) :=
    gammaClippedErrorExtension_eqOn ⟨by norm_num only, by norm_num only⟩
  have hinc := PseudoPrime.LLS.clippedShiftError_increment_le hRH hx hh hhx
  have hD :
    |gammaClippedErrorExtension x (99 / 40) - gammaClippedErrorExtension x (247 / 100)| ≤
      PseudoPrime.LLS.logShiftRampIncrement x h + 1 / 200 := by
    rw [hleft, hright]
    exact hinc
  have hv :=
    LLS.expRampVariation_abs_le_of_increment (gammaClippedErrorExtension_continuous hx0) hbound hD
  rw [LLS.exponentialRampVariationFunctional_congr gammaClippedErrorExtension_eqOn] at hv
  exact hv

/-- Extend the logarithmic atom by the same clamp as the corrected error. Its
global continuity permits linearity of the variation functional. -/
noncomputable def gammaClippedAtomExtension (x u : ℝ) : ℝ :=
  Analysis.positiveLogRatio (1 / x) (max 0 (min u (99 / 40 : ℝ)))

/-- For positive scale, the clamped logarithmic atom is continuous everywhere. -/
theorem gammaClippedAtomExtension_continuous {x : ℝ} (hx : 0 < x) :
    Continuous (gammaClippedAtomExtension x) := by
  have hc : Continuous (fun u : ℝ => max 0 (min u (99 / 40 : ℝ))) :=
    continuous_const.max (continuous_id.min continuous_const)
  exact (Analysis.positiveLogRatio_continuous (one_div_pos.mpr hx)).comp hc

/-- On the ramp support, the clamped atom equals the original logarithmic atom. -/
theorem gammaClippedAtomExtension_eqOn {x : ℝ} :
    Set.EqOn (gammaClippedAtomExtension x) (Analysis.positiveLogRatio (1 / x))
      (Set.Icc 0 (99 / 40 : ℝ)) := by
  intro u hu
  dsimp only [gammaClippedAtomExtension]
  rw [min_eq_left hu.2, max_eq_right hu.1]

/-- Extend the original arithmetic error by subtracting the atom correction from
the continuous corrected extension. On the support this recovers $S(xu)-xu$. -/
noncomputable def gammaClippedRawErrorExtension (x u : ℝ) : ℝ :=
  gammaClippedErrorExtension x u - Real.log (2 * Real.pi) * gammaClippedAtomExtension x u

/-- The raw error extension is continuous because both terms are continuous. -/
theorem gammaClippedRawErrorExtension_continuous {x : ℝ} (hx : 0 < x) :
    Continuous (gammaClippedRawErrorExtension x) := by
  exact
    (gammaClippedErrorExtension_continuous hx).sub
      (continuous_const.mul (gammaClippedAtomExtension_continuous hx))

/-- On the ramp support, the raw extension equals the uncorrected smoothed error. -/
theorem gammaClippedRawErrorExtension_eqOn {x : ℝ} :
    Set.EqOn (gammaClippedRawErrorExtension x)
      (fun u ↦ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u)
      (Set.Icc 0 (99 / 40 : ℝ)) := by
  intro u hu
  dsimp only [gammaClippedRawErrorExtension]
  rw [gammaClippedErrorExtension_eqOn hu, gammaClippedAtomExtension_eqOn hu]
  dsimp only [PseudoPrime.LLS.clippedShiftError]
  ring

/-- For continuous functions, the ramp variation functional is additive under
subtraction. Split the two smooth integrals and retain the signed endpoint jumps. -/
private theorem gammaClippedVariationFunctional_sub (f g : ℝ → ℝ) (hf : Continuous f)
    (hg : Continuous g) :
    LLS.exponentialRampVariationFunctional (fun u ↦ f u - g u) =
      LLS.exponentialRampVariationFunctional f - LLS.exponentialRampVariationFunctional g := by
  let Q1 : ℝ → ℝ := fun u ↦ (u - 1) * Real.exp (-u)
  let Q2 : ℝ → ℝ := fun u ↦
    Real.exp (-u) * ((u - 1) * ((99 / 40 - u) / (1 / 200)) + (2 * u - 1) / (1 / 200))
  have hQ1 : Continuous Q1 := by
    dsimp only [Q1]
    exact (continuous_id.sub continuous_const).mul (Real.continuous_exp.comp continuous_id.neg)
  have hQ2 : Continuous Q2 := by
    dsimp only [Q2]
    exact
      (Real.continuous_exp.comp continuous_id.neg).mul
        (((continuous_id.sub continuous_const).mul
              ((continuous_const.sub continuous_id).div_const (1 / 200))).add
          ((continuous_const.mul continuous_id).sub continuous_const |>.div_const (1 / 200)))
  have hInt (Q : ℝ → ℝ) (hQ : Continuous Q) (a b : ℝ) :
    (∫ u in a..b, (f u - g u) * Q u) = (∫ u in a..b, f u * Q u) - ∫ u in a..b, g u * Q u := by
    simp only [sub_mul]
    exact
      intervalIntegral.integral_sub ((hf.mul hQ).intervalIntegrable a b)
        ((hg.mul hQ).intervalIntegrable a b)
  simp only [LLS.exponentialRampVariationFunctional]
  rw [hInt Q1 hQ1 0 (247 / 100), hInt Q2 hQ2 (247 / 100) (99 / 40)]
  ring

/-- The variation functional commutes with multiplication by a real constant. -/
private theorem gammaClippedVariationFunctional_const_mul (c : ℝ) (f : ℝ → ℝ) :
    LLS.exponentialRampVariationFunctional (fun u ↦ c * f u) =
      c * LLS.exponentialRampVariationFunctional f := by
  simp only [LLS.exponentialRampVariationFunctional, mul_assoc, intervalIntegral.integral_const_mul]
  ring

/-- The variation functional of the logarithmic atom at $1/x$ is $e^{-1/x}$.
Use the exact atom-to-ramp-kernel identity and the left branch of the ramp weight. -/
theorem gammaClippedAtom_variation_eq_exp {x : ℝ} (hx : 1 ≤ x) :
    LLS.exponentialRampVariationFunctional (Analysis.positiveLogRatio (1 / x)) =
      Real.exp (-(1 / x)) := by
  have hx0 : 0 < x := by linarith only [hx]
  have hv : 0 < 1 / x := one_div_pos.mpr hx0
  have hleft : 1 / x ≤ (247 / 100 : ℝ) := by
    have hle : 1 / x ≤ 1 := (div_le_iff₀ hx0).mpr (by linarith only [hx])
    exact hle.trans (by norm_num only)
  change LLS.exponentialRampLogKernel (1 / x) = Real.exp (-(1 / x))
  rw [LLS.exponentialRampLogKernel_eq_weight hv,
    Analysis.exponentialRampWeight_eq_exp_of_le_left hleft]

/-- The uncorrected ramp error functional is the corrected error functional minus
the exact logarithmic atom. Use the continuous extensions and support congruence. -/
theorem gammaClippedRawError_variation_eq {x : ℝ} (hx : 1 ≤ x) :
    LLS.exponentialRampVariationFunctional
        (fun u ↦ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) =
      LLS.exponentialRampVariationFunctional (PseudoPrime.LLS.clippedShiftError x) -
        Real.log (2 * Real.pi) * Real.exp (-(1 / x)) := by
  have hx0 : 0 < x := by linarith only [hx]
  have hAtomCont := gammaClippedAtomExtension_continuous hx0
  have hRawCont := gammaClippedRawErrorExtension_continuous hx0
  have hSub :=
    gammaClippedVariationFunctional_sub (gammaClippedErrorExtension x)
      (fun u ↦ Real.log (2 * Real.pi) * gammaClippedAtomExtension x u)
      (gammaClippedErrorExtension_continuous hx0) (continuous_const.mul hAtomCont)
  have hScale :=
    gammaClippedVariationFunctional_const_mul (Real.log (2 * Real.pi)) (gammaClippedAtomExtension x)
  have hClip :=
    LLS.exponentialRampVariationFunctional_congr (gammaClippedErrorExtension_eqOn (x := x))
  have hRaw :=
    LLS.exponentialRampVariationFunctional_congr (gammaClippedRawErrorExtension_eqOn (x := x))
  have hAtom :=
    LLS.exponentialRampVariationFunctional_congr (gammaClippedAtomExtension_eqOn (x := x))
  calc
    _ = LLS.exponentialRampVariationFunctional (gammaClippedRawErrorExtension x) := hRaw.symm
    _ =
        LLS.exponentialRampVariationFunctional (gammaClippedErrorExtension x) -
          LLS.exponentialRampVariationFunctional
            (fun u ↦ Real.log (2 * Real.pi) * gammaClippedAtomExtension x u) :=
      by
      change
        LLS.exponentialRampVariationFunctional
            (fun u ↦
              gammaClippedErrorExtension x u -
                Real.log (2 * Real.pi) * gammaClippedAtomExtension x u) =
          _
      exact hSub
    _ =
        LLS.exponentialRampVariationFunctional (gammaClippedErrorExtension x) -
          Real.log (2 * Real.pi) *
            LLS.exponentialRampVariationFunctional (gammaClippedAtomExtension x) :=
      by rw [hScale]
    _ =
        LLS.exponentialRampVariationFunctional (PseudoPrime.LLS.clippedShiftError x) -
          Real.log (2 * Real.pi) *
            LLS.exponentialRampVariationFunctional (Analysis.positiveLogRatio (1 / x)) :=
      by rw [hClip, hAtom]
    _ =
        LLS.exponentialRampVariationFunctional (PseudoPrime.LLS.clippedShiftError x) -
          Real.log (2 * Real.pi) * Real.exp (-(1 / x)) :=
      by rw [gammaClippedAtom_variation_eq_exp hx]

/-- For $r\ge1$, the actual normalized ramp Mangoldt sum has the clipped-log
lower bound from analysis11. The exact logarithmic atom correction is included. -/
theorem gammaClippedRampSum_lower (hRH : RiemannHypothesis) {r : ℝ} (hr : 1 ≤ r) :
    ((293 / 320 : ℝ) - 231 / 49400) * r - 386043 / 395200 - 13 / r ≤
      LLS.exponentialRampMangoldtSum (r ^ 2) / r := by
  have hx : 1 ≤ r ^ 2 := by nlinarith only [hr]
  have hr0 : 0 < r := by linarith only [hr]
  have hx0 : 0 < r ^ 2 := by positivity
  have hs : Real.sqrt (r ^ 2) = r := Real.sqrt_sq (by linarith only [hr])
  have hnorm := LLS.expRampMangoldt_div_sqrt_eq_main_add_error hx0
  rw [hs] at hnorm
  have hvar :=
    gammaClippedError_variation_bound hRH hx (by positivity : 0 < r ^ 2 / 20)
      (by nlinarith only [hr] : r ^ 2 / 20 ≤ r ^ 2)
  rw [hs] at hvar
  have hraw := gammaClippedRawError_variation_eq hx
  have hcoeff :
    (3 / 2 : ℝ) * ((63 / 800 : ℝ) * r + 21 / 20) +
        42 * (PseudoPrime.LLS.logShiftRampIncrement (r ^ 2) (r ^ 2 / 20) + 1 / 200) =
      (231 / 49400 : ℝ) * r ^ 2 + (386043 / 395200 : ℝ) * r +
        (63 / 40 + 42 * (101 * (21 / 20) + Real.log (2 * Real.pi)) / 494 + 42 / 200) := by
    dsimp only [PseudoPrime.LLS.logShiftRampIncrement, PseudoPrime.LLS.logShiftRampEnvelope]
    rw [Real.sqrt_sq (by linarith only [hr])]
    field_simp [pow_ne_zero 2 hr0.ne']
    ring_nf
  have hc0 : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by nlinarith only [Real.pi_gt_three] : 1 ≤ 2 * Real.pi)
  have hc2 : Real.log (2 * Real.pi) ≤ 2 := by
    linarith only [PseudoPrime.Analysis.log_two_mul_pi_lt.le]
  have he0 : 0 ≤ Real.exp (-(1 / r ^ 2)) := (Real.exp_pos _).le
  have he1 : Real.exp (-(1 / r ^ 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (one_div_nonneg.mpr (sq_nonneg r)))
  have hAtom : Real.log (2 * Real.pi) * Real.exp (-(1 / r ^ 2)) ≤ 2 := by
    calc
      Real.log (2 * Real.pi) * Real.exp (-(1 / r ^ 2)) ≤ Real.log (2 * Real.pi) * 1 :=
        mul_le_mul_of_nonneg_left he1 hc0
      _ = Real.log (2 * Real.pi) := by ring
      _ ≤ 2 := hc2
  have hconstant :
    63 / 40 + 42 * (101 * (21 / 20) + Real.log (2 * Real.pi)) / 494 + 42 / 200 +
        Real.log (2 * Real.pi) * Real.exp (-(1 / r ^ 2)) ≤
      13 := by
    nlinarith only [hc2, hAtom]
  have hvariation :
    -((231 / 49400 : ℝ) * r ^ 2) - (386043 / 395200 : ℝ) * r - 13 ≤
      LLS.exponentialRampVariationFunctional
        (fun u ↦
          AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (r ^ 2 * u) - r ^ 2 * u) := by
    rw [hraw]
    have hlow := (abs_le.mp hvar).1
    rw [hcoeff] at hlow
    linarith only [hlow, hconstant]
  have hmass :
    (293 / 320 : ℝ) ≤ ∫ u in (0 : ℝ)..(99 / 40), PseudoPrime.Analysis.exponentialRampWeight u := by
    have hm := PseudoPrime.LLS.gamma_ramp_mass_lower
    nlinarith only [hm]
  have hmassR := mul_le_mul_of_nonneg_right hmass (sq_nonneg r)
  have hnormMul :
    LLS.exponentialRampMangoldtSum (r ^ 2) =
      ((∫ u in (0 : ℝ)..(99 / 40), PseudoPrime.Analysis.exponentialRampWeight u) * r +
          LLS.exponentialRampVariationFunctional
              (fun u ↦
                AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (r ^ 2 * u) - r ^ 2 * u) /
            r) *
        r := by
    calc
      _ = (LLS.exponentialRampMangoldtSum (r ^ 2) / r) * r := by field_simp [hr0.ne']
      _ = _ := congrArg (fun z : ℝ ↦ z * r) hnorm
  apply (le_div_iff₀ hr0).2
  rw [hnormMul]
  field_simp [hr0.ne']
  nlinarith only [hmassR, hvariation]

/-- Combine the new clipped-log ramp lower bound with the existing principal cap.
This is the index-four margin used by the scalar Gamma branch. -/
theorem gammaClippedFourTRamp_lower (hRH : RiemannHypothesis) {r : ℝ} (hr : 1 ≤ r) :
    (87069 / 98800 : ℝ) * r - 15138157 / 11856000 - 49 / (3 * r) ≤
      (4 * (LLS.exponentialRampMangoldtSum (r ^ 2) / r) -
          (∑' k : ℕ,
              LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) (r ^ 2)
                k).re) /
        3 := by
  have hr0 : 0 < r := by linarith only [hr]
  have hx : 1 ≤ r ^ 2 := by nlinarith only [hr]
  have hs : Real.sqrt (r ^ 2) = r := Real.sqrt_sq (by linarith only [hr])
  let T := LLS.exponentialRampMangoldtSum (r ^ 2) / r
  let P :=
    (∑' k : ℕ,
        LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) k).re
  have hT := gammaClippedRampSum_lower hRH hr
  have hcap := LLS.clippedShiftError_twentieth_width_cap hr0
  have hcapDiv := div_le_div_of_nonneg_right hcap hr0.le
  rw [add_div] at hcapDiv
  have hcapEq :
    ((231 / 24700 : ℝ) * r ^ 2 + (7417297 / 3952000 : ℝ) * r + 27) / r =
      (231 / 24700 : ℝ) * r + 7417297 / 3952000 + 27 / r := by
    field_simp (disch := exact hr0.ne')
  rw [hcapEq] at hcapDiv
  have herr :
    (LLS.clippedShiftPrincipalErrorNumerator (r ^ 2) (r ^ 2 / 20) +
          Real.log (2 * Real.pi) * Real.exp (-(1 / r ^ 2))) /
        r ≤
      (231 / 24700 : ℝ) * r + 7417297 / 3952000 + 23 / r := by
    have hsum : 4 / r + 23 / r = 27 / r := by ring
    linarith only [hcapDiv, hsum]
  have hmass := LLS.clippedShiftPrincipalLower_ge_mass133 (r ^ 2) (r ^ 2 / 20)
  rw [hs] at hmass
  have hprincipal :
    (133 / 160 - 231 / 24700 : ℝ) * r - 7417297 / 3952000 - 23 / r ≤
      LLS.clippedShiftPrincipalLower (r ^ 2) (r ^ 2 / 20) := by
    linarith only [hmass, herr]
  have hh : 0 < r ^ 2 / 20 := by positivity
  have hhx : r ^ 2 / 20 ≤ r ^ 2 := by nlinarith only [hr]
  have hactual := LLS.clippedShiftPrincipalLower_le_actual hRH hx hh hhx
  rw [hs] at hactual
  have hprincipalActual :
    (133 / 160 - 231 / 24700 : ℝ) * r - 7417297 / 3952000 - 23 / r ≤ 2 * T - P :=
    hprincipal.trans hactual
  have hT' : ((293 / 320 : ℝ) - 231 / 49400) * r - 386043 / 395200 - 13 / r ≤ T := by
    dsimp only [T]
    exact hT
  have hcoeff :
    (2 * ((293 / 320 : ℝ) - 231 / 49400) + (133 / 160 - 231 / 24700)) / 3 =
      (87069 / 98800 : ℝ) := by
    norm_num only
  have hconst :
    (2 * (386043 / 395200 : ℝ) + 7417297 / 3952000) / 3 = (15138157 / 11856000 : ℝ) := by
    norm_num only
  have hrecip : (2 * (13 : ℝ) + 23) / 3 = (49 / 3 : ℝ) := by norm_num only
  have hrecipDiv : (2 * (13 / r) + 23 / r) / 3 = 49 / (3 * r) := by
    field_simp (disch := exact hr0.ne')
    ring
  change (87069 / 98800 : ℝ) * r - 15138157 / 11856000 - 49 / (3 * r) ≤ (4 * T - P) / 3
  nlinarith only [hT', hprincipalActual, hcoeff, hconst, hrecip, hrecipDiv]

/-- For an exponent at least one hundred, the normalized signed main term
dominates the affine margin needed by the medium-range Gamma cutoff. The proof
combines the ramp sum and index-four bounds, then uses the coefficient margins
at exponent one hundred. -/
theorem gammaClippedNormalizedMain_lower_index100 (hRH : RiemannHypothesis) {r k : ℝ} (hr : 1 ≤ r)
    (hk : 100 ≤ k) :
    (91 / 100 : ℝ) * r - 1 - 14 / r ≤
      (k * (LLS.exponentialRampMangoldtSum (r ^ 2) / r) -
          (∑' j : ℕ,
              LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) (r ^ 2)
                j).re) /
        (k - 1) := by
  let T : ℝ := LLS.exponentialRampMangoldtSum (r ^ 2) / r
  let P : ℝ :=
    (∑' j : ℕ,
        LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) j).re
  let aT : ℝ := 293 / 320 - 231 / 49400
  let bT : ℝ := 386043 / 395200
  let aJ : ℝ := 133 / 160 - 231 / 24700
  let bJ : ℝ := 7417297 / 3952000
  have hT := gammaClippedRampSum_lower hRH hr
  have hQ := gammaClippedFourTRamp_lower hRH hr
  have hT' : aT * r - bT - 13 / r ≤ T := by
    dsimp only [aT, bT, T]
    exact hT
  have hQ' : (87069 / 98800 : ℝ) * r - 15138157 / 11856000 - 49 / (3 * r) ≤ (4 * T - P) / 3 := by
    dsimp only [T, P]
    exact hQ
  have hw : 0 ≤ k - 4 := by linarith only [hk]
  have htw := mul_le_mul_of_nonneg_left hT' hw
  have hqw := mul_le_mul_of_nonneg_left hQ' (by norm_num only : (0 : ℝ) ≤ 3)
  have hcomb :
    (k - 4) * (aT * r - bT - 13 / r) +
        3 * ((87069 / 98800 : ℝ) * r - 15138157 / 11856000 - 49 / (3 * r)) ≤
      k * T - P := by
    have heq : (k - 4) * T + (4 * T - P) = k * T - P := by ring
    nlinarith only [htw, hqw, heq]
  have hqa : 3 * (87069 / 98800 : ℝ) = 2 * aT + aJ := by norm_num only [aT, aJ]
  have hqb : 3 * (15138157 / 11856000 : ℝ) = 2 * bT + bJ := by norm_num only [bT, bJ]
  have hqr : 3 * (49 / 3 : ℝ) = 2 * 13 + 23 := by norm_num only
  have hmulA : (k - 100) * (91 / 100 : ℝ) ≤ (k - 100) * aT := by
    have hm : 0 ≤ k - 100 := by linarith only [hk]
    have ha : (91 / 100 : ℝ) ≤ aT := by norm_num only [aT]
    exact mul_le_mul_of_nonneg_left ha hm
  have hanchorA : 99 * (91 / 100 : ℝ) ≤ 98 * aT + aJ := by norm_num only [aT, aJ]
  have hcoef : (k - 1) * (91 / 100 : ℝ) ≤ (k - 2) * aT + aJ := by
    have heq : k - 1 = (k - 100) + 99 ∧ k - 2 = (k - 100) + 98 := by constructor <;> ring
    rcases heq with ⟨h1, h2⟩
    rw [h1, h2]
    linarith only [hmulA, hanchorA]
  have hmulB : (k - 100) * (1 - bT) ≥ 0 := by
    have hm : 0 ≤ k - 100 := by linarith only [hk]
    have hb : bT ≤ 1 := by norm_num only [bT]
    exact mul_nonneg hm (by linarith only [hb])
  have hanchorB : 98 * bT + bJ ≤ 99 := by norm_num only [bT, bJ]
  have hconst : (k - 2) * bT + bJ ≤ k - 1 := by
    have heq : k - 1 = (k - 100) + 99 ∧ k - 2 = (k - 100) + 98 := by constructor <;> ring
    rcases heq with ⟨h1, h2⟩
    rw [h1, h2]
    nlinarith only [hmulB, hanchorB]
  have hrec : (k - 2) * 13 + 23 ≤ 14 * (k - 1) := by nlinarith only [hk]
  have hrpos : 0 < r := by linarith only [hr]
  have hidentity :
    (k - 4) * (aT * r - bT - 13 / r) +
        3 * ((87069 / 98800 : ℝ) * r - 15138157 / 11856000 - 49 / (3 * r)) =
      ((k - 2) * aT + aJ) * r - ((k - 2) * bT + bJ) - ((k - 2) * 13 + 23) / r := by
    have ha : (k - 4) * aT + 3 * (87069 / 98800 : ℝ) = (k - 2) * aT + aJ := by
      rw [hqa]
      ring
    have hb : (k - 4) * bT + 3 * (15138157 / 11856000 : ℝ) = (k - 2) * bT + bJ := by
      rw [hqb]
      ring
    have hc : (k - 4) * 13 + 3 * (49 / 3 : ℝ) = (k - 2) * 13 + 23 := by
      rw [hqr]
      ring
    calc
      _ =
          ((k - 4) * aT + 3 * (87069 / 98800 : ℝ)) * r -
            ((k - 4) * bT + 3 * (15138157 / 11856000 : ℝ)) -
            ((k - 4) * 13 + 3 * (49 / 3 : ℝ)) / r :=
        by ring
      _ = _ := by rw [ha, hb, hc]
  rw [hidentity] at hcomb
  have hinv : 0 < 1 / r := one_div_pos.mpr hrpos
  have hc1 := mul_le_mul_of_nonneg_right hcoef hrpos.le
  have hc2 := mul_le_mul_of_nonneg_right hrec hinv.le
  have hc3 : ((k - 2) * 13 + 23) / r ≤ 14 * (k - 1) * (1 / r) := by
    have heq : ((k - 2) * 13 + 23) / r = ((k - 2) * 13 + 23) * (1 / r) := by ring
    rw [heq]
    nlinarith only [hc2]
  have hb1 : -((k - 2) * bT + bJ) ≥ -(k - 1) := by linarith only [hconst]
  have hshift :
    (k - 1) * ((91 / 100 : ℝ) * r - 1 - 14 / r) ≤
      ((k - 2) * aT + aJ) * r - ((k - 2) * bT + bJ) - ((k - 2) * 13 + 23) / r := by
    have heq :
      (k - 1) * ((91 / 100 : ℝ) * r - 1 - 14 / r) =
        (k - 1) * (91 / 100 : ℝ) * r - (k - 1) - 14 * (k - 1) * (1 / r) := by
      field_simp
    rw [heq]
    have hc3' : 14 * (k - 1) * (1 / r) ≥ ((k - 2) * 13 + 23) / r := by linarith only [hc3]
    have hA : 0 ≤ (((k - 2) * aT + aJ) - (k - 1) * (91 / 100 : ℝ)) * r :=
      mul_nonneg (sub_nonneg.mpr hcoef) hrpos.le
    have hB : 0 ≤ (k - 1) - ((k - 2) * bT + bJ) := sub_nonneg.mpr hconst
    have hC : 0 ≤ 14 * (k - 1) * (1 / r) - ((k - 2) * 13 + 23) / r := sub_nonneg.mpr hc3'
    have hdecomp :
      (((k - 2) * aT + aJ) * r - ((k - 2) * bT + bJ) - ((k - 2) * 13 + 23) / r) -
          ((k - 1) * (91 / 100 : ℝ) * r - (k - 1) - 14 * (k - 1) * (1 / r)) =
        (((k - 2) * aT + aJ) - (k - 1) * (91 / 100 : ℝ)) * r + ((k - 1) - ((k - 2) * bT + bJ)) +
          (14 * (k - 1) * (1 / r) - ((k - 2) * 13 + 23) / r) := by
      ring
    have hnonneg := add_nonneg hA (add_nonneg hB hC)
    linarith only [hdecomp, hnonneg]
  have hnum := hshift.trans hcomb
  apply (le_div_iff₀ (by linarith only [hk] : 0 < k - 1)).2
  linarith only [hnum]

/-- A pass-containing subgroup of index at least one hundred turns a strict
normalized Gamma margin into a rejecting prime base. The subgroup average keeps
the full index, allowing the stronger exponent-dependent scalar bound to apply. -/
theorem exists_prime_witness_of_gamma_index100_gap {n : ℕ} [NeZero n] (hn : 1 < n) (hnOdd : Odd n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hQ : 20000 ≤ n)
    (H : Subgroup (ZMod n)ˣ) (hidx : 100 ≤ H.index)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    {r b : ℝ} (hr : 1 ≤ r) (hx : 2 ≤ r ^ 2) (hb : 0 ≤ b) (hbX : b ≤ (99 / 40 : ℝ) * r ^ 2)
    (hgap : gammaSignedPrefixMRBudget n n (r ^ 2) b < (91 / 100 : ℝ) * r - 1 - 14 / r) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (99 / 40 : ℝ) * r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_contra hnone
  have hpass :
    ∀ p : ℕ,
      p.Prime →
        (p : ℝ) ≤ (99 / 40 : ℝ) * r ^ 2 → PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
    intro p hp hpbound
    by_contra hreject
    exact hnone ⟨p, hp, hpbound, hreject⟩
  have hsmall :
    ∀ p : ℕ, p.Prime → (p : ℝ) ≤ (99 / 40 : ℝ) * r ^ 2 → NumberTheory.residueInSubgroup n H p :=
    fun p hp hpb ↦ hHpass (p : ZMod n) (hpass p hp hpb)
  have hu :=
    LLS.PaperStatements.gamma_primitive_average_re_le_even_prime_prefix hQ le_rfl H hGRH
      (fun χ ↦ annihilator_even_of_containing_strong_passes hn hnOdd H hHpass χ) hx hb
      (fun p hp hpb ↦ hsmall p hp (hpb.trans hbX))
  have hramp :=
    LLS.PaperStatements.gamma_ramp_subgroup_comparison H (by positivity : 0 < r ^ 2)
      (fun p hp _ hpb ↦ hsmall p hp hpb)
  have hz := commonExpSum_zero_of_prime_passes hn hnOdd hpass (r ^ 2)
  rw [hz, zero_div, mul_zero, add_zero] at hramp
  have hrpos : 0 < r := by linarith only [hr]
  have hsqrt : Real.sqrt (r ^ 2) = r := Real.sqrt_sq hrpos.le
  rw [hsqrt] at hramp
  let k : ℝ := H.index
  have hk : 100 ≤ k := by
    dsimp only [k]
    exact_mod_cast hidx
  have hscalar := gammaClippedNormalizedMain_lower_index100 hGRH.riemann hr hk
  let T : ℝ := LLS.exponentialRampMangoldtSum (r ^ 2) / r
  let P : ℝ :=
    (∑' j : ℕ,
        LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) j).re
  have haverage : k * T ≤ P + (k - 1) * gammaSignedPrefixMRBudget n n (r ^ 2) b := by
    dsimp only [k, T, P, gammaSignedPrefixMRBudget] at hramp hu ⊢
    nlinarith only [hramp, hu]
  have hnorm : (k * T - P) / (k - 1) ≤ gammaSignedPrefixMRBudget n n (r ^ 2) b := by
    apply (div_le_iff₀ (by linarith only [hk] : (0 : ℝ) < k - 1)).2
    linarith only [haverage]
  dsimp only [T, P] at hnorm
  have hbound := hscalar.trans hnorm
  exact (not_lt_of_ge hbound) hgap

/-- The scalar signed-prefix gap for a prefix credit $C$. It combines the clipped-log
index-four ramp margin with the common signed budget after the prefix deduction. -/
noncomputable def gammaClippedPrefixGap (L C r : ℝ) : ℝ :=
  (87069 / 98800 : ℝ) * r - (11783423 / 25000000 : ℝ) * L - (143420077 / 11856000 - 2 * C) -
    ((7 / 6 : ℝ) * L + 190 / 3) / r

/-- The positive quadratic root for an arbitrary retained-prefix credit. -/
noncomputable def gammaClippedPrefixRoot (L C : ℝ) : ℝ :=
  ((11783423 / 25000000 : ℝ) * L + (143420077 / 11856000 - 2 * C) +
      Real.sqrt
        (((11783423 / 25000000 : ℝ) * L + (143420077 / 11856000 - 2 * C)) ^ 2 +
          4 * (87069 / 98800 : ℝ) * ((7 / 6 : ℝ) * L + 190 / 3))) /
    (2 * (87069 / 98800 : ℝ))

/-- The radius and witness bound associated with any cutoff and prefix credit. -/
noncomputable def gammaClippedPrefixRadius (L b C : ℝ) : ℝ :=
  max (Real.sqrt ((40 / 99 : ℝ) * b)) (gammaClippedPrefixRoot L C)

noncomputable def gammaClippedPrefixBound (L b C : ℝ) : ℝ :=
  (99 / 40 : ℝ) * (gammaClippedPrefixRadius L b C) ^ 2

/-- The parameterized positive root is positive for the two retained-prefix
credits whenever their constant offset is nonnegative and $L\ge120$. -/
theorem gammaClippedPrefixRoot_pos {L C : ℝ} (hL : 120 ≤ L)
    (hD : 0 ≤ 143420077 / 11856000 - 2 * C) : 0 < gammaClippedPrefixRoot L C := by
  have hL0 : 0 < L := by linarith only [hL]
  have hB : 0 < (11783423 / 25000000 : ℝ) * L + (143420077 / 11856000 - 2 * C) := by
    have hmul := mul_pos (by norm_num only : (0 : ℝ) < 11783423 / 25000000) hL0
    linarith only [hmul, hD]
  have hA : 0 < (7 / 6 : ℝ) * L + 190 / 3 := by
    apply add_pos
    · exact mul_pos (by norm_num only) hL0
    · norm_num only
  have hK : 0 < (87069 / 98800 : ℝ) := by norm_num only
  have hdisc :
    0 <
      ((11783423 / 25000000 : ℝ) * L + (143420077 / 11856000 - 2 * C)) ^ 2 +
        4 * (87069 / 98800 : ℝ) * ((7 / 6 : ℝ) * L + 190 / 3) := by
    apply add_pos
    · exact sq_pos_of_pos hB
    · exact mul_pos (mul_pos (by norm_num only) hK) hA
  dsimp only [gammaClippedPrefixRoot]
  apply div_pos
  · exact add_pos hB (Real.sqrt_pos.mpr hdisc)
  · exact mul_pos (by norm_num only) hK

/-- The parameterized positive root makes its prefix gap vanish. -/
theorem gammaClippedPrefixGap_root_eq_zero {L C : ℝ} (hL : 120 ≤ L)
    (hD : 0 ≤ 143420077 / 11856000 - 2 * C) :
    gammaClippedPrefixGap L C (gammaClippedPrefixRoot L C) = 0 := by
  let b : ℝ := (11783423 / 25000000 : ℝ) * L + (143420077 / 11856000 - 2 * C)
  let A : ℝ := (7 / 6 : ℝ) * L + 190 / 3
  let K : ℝ := 87069 / 98800
  let disc : ℝ := b ^ 2 + 4 * K * A
  let r : ℝ := (b + Real.sqrt disc) / (2 * K)
  have hB : 0 < b := by
    dsimp only [b]
    have hL0 : 0 < L := by linarith only [hL]
    have hmul := mul_pos (by norm_num only : (0 : ℝ) < 11783423 / 25000000) hL0
    linarith only [hmul, hD]
  have hA : 0 < A := by
    dsimp only [A]
    positivity
  have hK : 0 < K := by norm_num only [K]
  have hdisc : 0 < disc := by
    dsimp only [disc]
    positivity
  have hs : (Real.sqrt disc) ^ 2 = disc := Real.sq_sqrt hdisc.le
  have hr : 0 < r := by
    dsimp only [r]
    exact div_pos (add_pos hB (Real.sqrt_pos.mpr hdisc)) (mul_pos (by norm_num only) hK)
  have hrEq : gammaClippedPrefixRoot L C = r := by
    dsimp only [gammaClippedPrefixRoot, r, disc, b, A, K]
  have hquad : K * r ^ 2 - b * r - A = 0 := by
    dsimp only [r]
    have hK0 : K ≠ 0 := ne_of_gt hK
    field_simp [hK0]
    dsimp only [disc] at hs
    nlinarith only [hs]
  have hmul : gammaClippedPrefixGap L C r * r = 0 := by
    rw [gammaClippedPrefixGap]
    dsimp only [A, b, K] at hquad ⊢
    field_simp
    nlinarith only [hquad]
  rw [hrEq]
  exact (mul_eq_zero.mp hmul).resolve_right hr.ne'

/-- Every radius at least the parameterized positive root satisfies its scalar
prefix condition. -/
theorem gammaClippedPrefixGap_nonneg_of_root_le {L C r : ℝ} (hL : 120 ≤ L)
    (hD : 0 ≤ 143420077 / 11856000 - 2 * C) (hr : gammaClippedPrefixRoot L C ≤ r) :
    0 ≤ gammaClippedPrefixGap L C r := by
  let rho := gammaClippedPrefixRoot L C
  have hrho : 0 < rho := gammaClippedPrefixRoot_pos hL hD
  have hr' : 0 < r := lt_of_lt_of_le hrho hr
  have hL0 : 0 < L := by linarith only [hL]
  have hA : 0 < (7 / 6 : ℝ) * L + 190 / 3 := by
    apply add_pos
    · exact mul_pos (by norm_num only) hL0
    · norm_num only
  have hK : 0 < (87069 / 98800 : ℝ) := by norm_num only
  have hid :
    gammaClippedPrefixGap L C r - gammaClippedPrefixGap L C rho =
      ((87069 / 98800 : ℝ) + ((7 / 6 : ℝ) * L + 190 / 3) / (r * rho)) * (r - rho) := by
    simp only [gammaClippedPrefixGap]
    field_simp [hr'.ne', hrho.ne']
    ring_nf
  have hdiff : 0 ≤ ((87069 / 98800 : ℝ) + ((7 / 6 : ℝ) * L + 190 / 3) / (r * rho)) * (r - rho) := by
    apply mul_nonneg
    · exact add_nonneg hK.le (div_nonneg hA.le (mul_nonneg hr'.le hrho.le))
    · exact sub_nonneg.mpr hr
  have hroot : gammaClippedPrefixGap L C rho = 0 := by
    dsimp only [rho]
    exact gammaClippedPrefixGap_root_eq_zero hL hD
  rw [hroot] at hid
  linarith only [hid, hdiff]

/-- Convert a nonnegative clipped-log scalar gap into an actual prime MR witness.
The caller supplies the prefix credit and its cutoff condition; the proof uses the
existing all-input subgroup consumer and the $x\ge2$ interface. -/
theorem exists_prime_witness_of_gammaClippedPrefixGap {n : ℕ} [NeZero n] (hn : 1 < n)
    (hnOdd : Odd n) (hnComposite : ¬n.Prime) (hn9 : n ≠ 9)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hQ : 20000 ≤ n) {L C r b : ℝ}
    (hlog : Real.log n = L) (hr : 1 ≤ r) (hx : 2 ≤ r ^ 2) (hb : 0 ≤ b)
    (hbX : b ≤ (99 / 40 : ℝ) * r ^ 2)
    (hprefix : C ≤ ∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight k)
    (hgap : 0 ≤ gammaClippedPrefixGap L C r) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (99 / 40 : ℝ) * r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hr0 : 0 < r := by linarith only [hr]
  have hs : Real.sqrt (r ^ 2) = r := Real.sqrt_sq (by linarith only [hr])
  have hbudget := gammaSignedPrefixMRBudget_lt_precise_common_cost hGRH.riemann n n (r ^ 2) b
  have hbudget' :
    gammaSignedPrefixMRBudget n n (r ^ 2) b <
      (11783423 / 25000000 : ℝ) * Real.log n + 541 / 50 - 2 * C +
        ((7 / 6 : ℝ) * Real.log n + 4) / Real.sqrt (r ^ 2) +
        43 * (r ^ 2) ^ (-9 / 16 : ℝ) := by
    dsimp only [gammaSignedPrefixMRBudget] at hbudget ⊢
    linarith only [hbudget, hprefix]
  have hpow :=
    LLS.PaperStatements.rpow_neg_nine_sixteenths_le_div_scale_sqrt (a := 1) (by norm_num only)
      (by
        norm_num only; exact (by nlinarith only [hr] : 1 ≤ r ^ 2))
  have htail := mul_le_mul_of_nonneg_left hpow (by norm_num only : (0 : ℝ) ≤ 43)
  rw [hs] at htail
  have htail' : 43 * (r ^ 2) ^ (-9 / 16 : ℝ) ≤ 43 / r := by
    calc
      _ ≤ 43 * (1 / r) := by simpa only [one_mul] using htail
      _ = 43 / r := by ring
  have hbudgetUpper :
    gammaSignedPrefixMRBudget n n (r ^ 2) b <
      (11783423 / 25000000 : ℝ) * L + 541 / 50 - 2 * C + ((7 / 6 : ℝ) * L + 47) / r := by
    rw [hlog, hs] at hbudget'
    have hpole : ((7 / 6 : ℝ) * L + 4) / r + 43 / r = ((7 / 6 : ℝ) * L + 47) / r := by ring
    linarith only [hbudget', htail', hpole]
  have hfour := gammaClippedFourTRamp_lower hGRH.riemann hr
  have hscalar := hgap
  dsimp only [gammaClippedPrefixGap] at hscalar
  have hconstant : (15138157 / 11856000 : ℝ) + 541 / 50 = 143420077 / 11856000 := by norm_num only
  have hrecipSum : ((7 / 6 : ℝ) * L + 47) / r + 49 / (3 * r) = ((7 / 6 : ℝ) * L + 190 / 3) / r := by
    field_simp (disch := exact hr0.ne')
    ring
  have hbelow :
    (11783423 / 25000000 : ℝ) * L + 541 / 50 - 2 * C + ((7 / 6 : ℝ) * L + 47) / r ≤
      (87069 / 98800 : ℝ) * r - 15138157 / 11856000 - 49 / (3 * r) := by
    linarith only [hscalar, hconstant, hrecipSum, hr0]
  have hbudgetGap :
    gammaSignedPrefixMRBudget n n (r ^ 2) b <
      (4 * (LLS.exponentialRampMangoldtSum (r ^ 2) / r) -
          (∑' k : ℕ,
              LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) (r ^ 2)
                k).re) /
        3 := by
    exact lt_of_lt_of_le (lt_of_lt_of_le hbudgetUpper hbelow) hfour
  have hbudgetGap' :
    gammaSignedPrefixMRBudget n n (r ^ 2) b <
      (4 * (LLS.exponentialRampMangoldtSum (r ^ 2) / Real.sqrt (r ^ 2)) -
          (∑' k : ℕ,
              LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) (r ^ 2)
                k).re) /
        3 := by
    simpa only [hs] using hbudgetGap
  exact
    exists_prime_signedPrefix_allInputs_GRH hn hnOdd hnComposite hn9 hGRH hQ hx hb hbX hbudgetGap'

/-- A retained-prefix lower bound yields a prime rejecting base below the
parameterized clipped-log bound. -/
theorem exists_prime_witness_le_gammaClippedPrefixBound {n : ℕ} (hn : 1 < n) (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 120 ≤ Real.log n) {b C : ℝ} (hb : 1000 ≤ b) (hD : 0 ≤ 143420077 / 11856000 - 2 * C)
    (hprefix : C ≤ ∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight k) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ gammaClippedPrefixBound (Real.log n) b C ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨hnOdd.pos.ne'⟩
  let L : ℝ := Real.log n
  let r : ℝ := gammaClippedPrefixRadius L b C
  have hQ : 20000 ≤ n := by
    by_contra hQ
    have hnR : (n : ℝ) ≤ 46000 := by exact_mod_cast (show n ≤ 46000 by omega)
    have hnPos : 0 < n := by omega
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hnPos
    have hlog := Real.log_le_log hn0 hnR
    linarith only [hlog, LLS.log_46000_lt_eleven, hL]
  have hn9 : n ≠ 9 := by omega
  have harg : 0 ≤ (40 / 99 : ℝ) * b := by positivity
  have hcut : 2 ≤ Real.sqrt ((40 / 99 : ℝ) * b) := by
    apply (Real.le_sqrt (by norm_num only) harg).mpr
    nlinarith only [hb]
  have hr : 2 ≤ r := by
    dsimp only [r, gammaClippedPrefixRadius]
    exact hcut.trans (le_max_left _ _)
  have hx : 2 ≤ r ^ 2 := by
    have hsq := sq_nonneg (r - 2)
    nlinarith only [hr, hsq]
  have hbX : b ≤ (99 / 40 : ℝ) * r ^ 2 := by
    let s : ℝ := Real.sqrt ((40 / 99 : ℝ) * b)
    have hs : 0 ≤ s := Real.sqrt_nonneg _
    have hle : s ≤ r := by
      dsimp only [s, r, gammaClippedPrefixRadius]
      exact le_max_left _ _
    have hprod := mul_nonneg (sub_nonneg.mpr hle) (add_nonneg hs (le_trans hs hle))
    have hsquare : s ^ 2 = (40 / 99 : ℝ) * b := by
      dsimp only [s]
      exact Real.sq_sqrt harg
    have hrad2 : (40 / 99 : ℝ) * b ≤ r ^ 2 := by
      dsimp only [s] at hprod hsquare
      nlinarith only [hprod, hsquare]
    have hscale := mul_le_mul_of_nonneg_left hrad2 (by norm_num only : (0 : ℝ) ≤ 99 / 40)
    dsimp only [r, gammaClippedPrefixRadius] at hscale ⊢
    nlinarith only [hscale]
  have hgap : 0 ≤ gammaClippedPrefixGap L C r := by
    dsimp only [r, gammaClippedPrefixRadius]
    exact gammaClippedPrefixGap_nonneg_of_root_le hL hD (le_max_right _ _)
  have hr1 : 1 ≤ r := by linarith only [hr]
  obtain ⟨p, hp, hpbound, hreject⟩ :=
    exists_prime_witness_of_gammaClippedPrefixGap hn hnOdd hnComposite hn9 hGRH hQ rfl hr1 hx
      (by linarith only [hb]) hbX hprefix hgap
  refine ⟨p, hp, ?_, hreject⟩
  simpa only [gammaClippedPrefixBound] using hpbound

/-- The positive quadratic root of the clipped-log scalar condition. It solves
the equality obtained by multiplying the gap by the radius. -/
noncomputable def gammaClippedScalarRoot (L : ℝ) : ℝ :=
  ((11783423 / 25000000 : ℝ) * L + (143420077 / 11856000 - 2 * (203 / 50 : ℝ)) +
      Real.sqrt
        (((11783423 / 25000000 : ℝ) * L + (143420077 / 11856000 - 2 * (203 / 50 : ℝ))) ^ 2 +
          4 * (87069 / 98800 : ℝ) * ((7 / 6 : ℝ) * L + 190 / 3))) /
    (2 * (87069 / 98800 : ℝ))

/-- The radius for the first retained prefix. It is the larger of the prefix cutoff
radius and the positive root of the clipped-log scalar condition. -/
noncomputable def gammaClippedRadius1000 (L : ℝ) : ℝ :=
  max (Real.sqrt ((40 / 99 : ℝ) * 1000)) (gammaClippedScalarRoot L)

/-- The resulting first-prefix witness bound. -/
noncomputable def gammaClippedBound1000 (L : ℝ) : ℝ :=
  (99 / 40 : ℝ) * (gammaClippedRadius1000 L) ^ 2

/-- For every odd composite input with log at least 120, the first clipped-log
prefix yields an actual prime Miller--Rabin rejecting base within its stated bound. -/
theorem exists_prime_witness_le_gammaClippedBound1000 {n : ℕ} (hn : 1 < n) (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 120 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ gammaClippedBound1000 (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hprefix := LLS.gamma_prefix1000_lower_halfline hGRH.riemann (le_refl (1000 : ℝ))
  have hD : 0 ≤ 143420077 / 11856000 - 2 * (203 / 50 : ℝ) := by norm_num only
  obtain ⟨p, hp, hpbound, hreject⟩ :=
    exists_prime_witness_le_gammaClippedPrefixBound hn hnOdd hnComposite hGRH hL
      (by norm_num only : (1000 : ℝ) ≤ 1000) hD hprefix
  refine ⟨p, hp, ?_, hreject⟩
  simpa only [gammaClippedPrefixBound, gammaClippedPrefixRadius, gammaClippedPrefixRoot,
    gammaClippedBound1000, gammaClippedRadius1000, gammaClippedScalarRoot] using hpbound

noncomputable def gammaClippedBound50000 (L : ℝ) : ℝ :=
  gammaClippedPrefixBound L 50000 (28493 / 5000)

theorem exists_prime_witness_le_gammaClippedBound50000 {n : ℕ} (hn : 1 < n) (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 120 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ gammaClippedBound50000 (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hprefix := LLS.gamma_prefix50000_lower_asymmetric hGRH.riemann (le_refl (50000 : ℝ))
  have hD : 0 ≤ 143420077 / 11856000 - 2 * (28493 / 5000 : ℝ) := by norm_num only
  obtain ⟨p, hp, hpbound, hreject⟩ :=
    exists_prime_witness_le_gammaClippedPrefixBound hn hnOdd hnComposite hGRH hL
      (by norm_num only : (1000 : ℝ) ≤ 50000) hD hprefix
  exact ⟨p, hp, hpbound, hreject⟩

/-- The pointwise minimum of the two retained-prefix witness bounds. -/
noncomputable def gammaClippedUpper (L : ℝ) : ℝ :=
  min (gammaClippedBound1000 L) (gammaClippedBound50000 L)

/-- Every odd composite with logarithm at least 120 has a prime rejecting base
bounded by the pointwise minimum of the two retained-prefix estimates. -/
theorem exists_prime_witness_le_gammaClippedUpper {n : ℕ} (hn : 1 < n) (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 120 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ gammaClippedUpper (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases h : gammaClippedBound1000 (Real.log n) ≤ gammaClippedBound50000 (Real.log n)
  · obtain ⟨p, hp, hpbound, hreject⟩ :=
      exists_prime_witness_le_gammaClippedBound1000 hn hnOdd hnComposite hGRH hL
    refine ⟨p, hp, ?_, hreject⟩
    simpa only [gammaClippedUpper, min_eq_left h] using hpbound
  · have hlt : gammaClippedBound50000 (Real.log n) < gammaClippedBound1000 (Real.log n) :=
      lt_of_not_ge h
    obtain ⟨p, hp, hpbound, hreject⟩ :=
      exists_prime_witness_le_gammaClippedBound50000 hn hnOdd hnComposite hGRH hL
    refine ⟨p, hp, ?_, hreject⟩
    simpa only [gammaClippedUpper, min_eq_right (le_of_lt hlt)] using hpbound

/-- The least prime rejecting base obeys the same pointwise minimum bound. -/
theorem exists_least_prime_witness_le_gammaClippedUpper {n : ℕ} (hn : 1 < n) (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 120 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ gammaClippedUpper (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  classical
  let : NeZero n := ⟨hnOdd.pos.ne'⟩
  obtain ⟨p, hp, hpbound, hreject⟩ :=
    exists_prime_witness_le_gammaClippedUpper hn hnOdd hnComposite hGRH hL
  let hex : ∃ q : ℕ, q.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) := ⟨p, hp, hreject⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, ?_, (Nat.find_spec hex).2, ?_⟩
  · exact (Nat.cast_le.mpr (Nat.find_min' hex ⟨hp, hreject⟩)).trans hpbound
  · intro q hq hqReject
    exact Nat.find_min' hex ⟨hq, hqReject⟩

/-- A nonnegative scalar gap forces the radius to lie at or beyond the positive
quadratic root. -/
theorem gammaClippedPrefixRoot_le_of_gap_nonneg {L C r : ℝ} (hL : 120 ≤ L)
    (hD : 0 ≤ 143420077 / 11856000 - 2 * C) (hr : 0 < r) (hgap : 0 ≤ gammaClippedPrefixGap L C r) :
    gammaClippedPrefixRoot L C ≤ r := by
  by_contra hnot
  have hlt : r < gammaClippedPrefixRoot L C := lt_of_not_ge hnot
  let rho := gammaClippedPrefixRoot L C
  have hrho : 0 < rho := gammaClippedPrefixRoot_pos hL hD
  have hL0 : 0 < L := by linarith only [hL]
  have hA : 0 < (7 / 6 : ℝ) * L + 190 / 3 := by
    apply add_pos
    · exact mul_pos (by norm_num only) hL0
    · norm_num only
  have hK : 0 < (87069 / 98800 : ℝ) := by norm_num only
  have hid :
    gammaClippedPrefixGap L C rho - gammaClippedPrefixGap L C r =
      ((87069 / 98800 : ℝ) + ((7 / 6 : ℝ) * L + 190 / 3) / (r * rho)) * (rho - r) := by
    simp only [gammaClippedPrefixGap]
    field_simp [hr.ne', hrho.ne']
    ring_nf
  have hdiff : 0 < ((87069 / 98800 : ℝ) + ((7 / 6 : ℝ) * L + 190 / 3) / (r * rho)) * (rho - r) := by
    apply mul_pos
    · exact add_pos hK (div_pos hA (mul_pos hr hrho))
    · exact sub_pos.mpr hlt
  have hroot : gammaClippedPrefixGap L C rho = 0 := by
    dsimp only [rho]
    exact gammaClippedPrefixGap_root_eq_zero hL hD
  rw [hroot] at hid
  linarith only [hid, hdiff, hgap]

/-- An affine test radius preserves a nonnegative scalar gap from its anchor when
both its linear and reciprocal increment coefficients are nonnegative. -/
theorem gammaClippedPrefixGap_affine_nonneg {L L₀ C a t : ℝ} (hLL₀ : L₀ ≤ L) (ha : 0 ≤ a)
    (hr₀ : 0 < a * L₀ + t) (hslope : 0 ≤ (87069 / 98800 : ℝ) * a - 11783423 / 25000000)
    (hrecip : 0 ≤ a * (190 / 3 : ℝ) - (7 / 6 : ℝ) * t)
    (hanchor : 0 ≤ gammaClippedPrefixGap L₀ C (a * L₀ + t)) :
    0 ≤ gammaClippedPrefixGap L C (a * L + t) := by
  let r := a * L + t
  let r₀ := a * L₀ + t
  have hdelta : 0 ≤ L - L₀ := by linarith only [hLL₀]
  have hr0 : 0 < r₀ := hr₀
  have hrEq : r = r₀ + a * (L - L₀) := by
    dsimp only [r, r₀]
    ring
  have hr : 0 < r := by
    rw [hrEq]
    positivity
  have hrExpr : 0 < a * L + t := by simpa only [r] using hr
  have hr0Expr : 0 < a * L₀ + t := by simpa only [r₀] using hr0
  have hid :
    gammaClippedPrefixGap L C r - gammaClippedPrefixGap L₀ C r₀ =
      ((87069 / 98800 : ℝ) * a - 11783423 / 25000000) * (L - L₀) +
        (a * (190 / 3 : ℝ) - (7 / 6 : ℝ) * t) * (L - L₀) / (r * r₀) := by
    dsimp only [r, r₀]
    simp only [gammaClippedPrefixGap]
    field_simp [hrExpr.ne', hr0Expr.ne']
    ring_nf
  have hlinear := mul_nonneg hslope hdelta
  have hfrac : 0 ≤ (a * (190 / 3 : ℝ) - (7 / 6 : ℝ) * t) * (L - L₀) / (r * r₀) := by
    apply div_nonneg
    · exact mul_nonneg hrecip hdelta
    · exact mul_nonneg hr.le hr0.le
  have hstep : 0 ≤ gammaClippedPrefixGap L C r - gammaClippedPrefixGap L₀ C r₀ := by
    rw [hid]
    exact add_nonneg hlinear hfrac
  change 0 ≤ gammaClippedPrefixGap L C r
  have hstep' : 0 ≤ gammaClippedPrefixGap L C r - gammaClippedPrefixGap L₀ C (a * L₀ + t) := by
    simpa only [r₀] using hstep
  linarith only [hanchor, hstep']

/-- Above the anchor, a test radius with smaller linear coefficient has a
negative scalar gap when its constant offset is positive. -/
theorem gammaClippedPrefixGap_neg_of_scale {L C c : ℝ} (hL : 0 < L)
    (hD : 0 < 143420077 / 11856000 - 2 * C) (hc : 0 < c)
    (hslope : (87069 / 98800 : ℝ) * c - 11783423 / 25000000 < 0) :
    gammaClippedPrefixGap L C (c * L) < 0 := by
  have hL0 : 0 < L := hL
  have hA : 0 < (7 / 6 : ℝ) * L + 190 / 3 := by positivity
  have hr : 0 < c * L := mul_pos hc hL0
  have hslopeTerm : ((87069 / 98800 : ℝ) * c - 11783423 / 25000000) * L < 0 :=
    mul_neg_of_neg_of_pos hslope hL0
  have hrecip : 0 < ((7 / 6 : ℝ) * L + 190 / 3) / (c * L) := div_pos hA hr
  have hgapEq :
    gammaClippedPrefixGap L C (c * L) =
      ((87069 / 98800 : ℝ) * c - 11783423 / 25000000) * L - (143420077 / 11856000 - 2 * C) -
        ((7 / 6 : ℝ) * L + 190 / 3) / (c * L) := by
    simp only [gammaClippedPrefixGap]
    ring
  rw [hgapEq]
  linarith only [hslopeTerm, hD, hrecip]

/-- From $L=300$ onward the Gamma minimum is at least $0.7L^2$. This lower
comparison lets the classified Gaussian estimate take over at its entrance. -/
theorem gammaClippedUpper_ge_sevenTenths_sq {L : ℝ} (hL : 300 ≤ L) :
    (7 / 10 : ℝ) * L ^ 2 ≤ gammaClippedUpper L := by
  let c : ℝ := 133 / 250
  have hC1 : 0 < 143420077 / 11856000 - 2 * (203 / 50 : ℝ) := by norm_num only
  have hC2 : 0 < 143420077 / 11856000 - 2 * (28493 / 5000 : ℝ) := by norm_num only
  have hc : 0 < c := by norm_num only [c]
  have hslope : (87069 / 98800 : ℝ) * c - 11783423 / 25000000 < 0 := by norm_num only [c]
  have hLpos : 0 < L := by linarith only [hL]
  have hgap1 := gammaClippedPrefixGap_neg_of_scale hLpos hC1 hc hslope
  have hgap2 := gammaClippedPrefixGap_neg_of_scale hLpos hC2 hc hslope
  have hL120 : 120 ≤ L := le_trans (by norm_num only) hL
  have hroot1 : c * L ≤ gammaClippedPrefixRoot L (203 / 50) := by
    by_contra hnot
    have hlt : gammaClippedPrefixRoot L (203 / 50) < c * L := lt_of_not_ge hnot
    have hnonneg := gammaClippedPrefixGap_nonneg_of_root_le hL120 hC1.le hlt.le
    linarith only [hgap1, hnonneg]
  have hroot2 : c * L ≤ gammaClippedPrefixRoot L (28493 / 5000) := by
    by_contra hnot
    have hlt : gammaClippedPrefixRoot L (28493 / 5000) < c * L := lt_of_not_ge hnot
    have hnonneg := gammaClippedPrefixGap_nonneg_of_root_le hL120 hC2.le hlt.le
    linarith only [hgap2, hnonneg]
  have hrad1 : c * L ≤ gammaClippedRadius1000 L := by
    dsimp only [gammaClippedRadius1000]
    exact
      le_trans (by simpa only [c, gammaClippedPrefixRoot, gammaClippedScalarRoot] using hroot1)
        (le_max_right _ _)
  have hrad2 : c * L ≤ gammaClippedPrefixRadius L 50000 (28493 / 5000) := by
    exact le_trans hroot2 (le_max_right _ _)
  have hrad1Nonneg : 0 ≤ gammaClippedRadius1000 L := by
    dsimp only [gammaClippedRadius1000]
    exact le_trans (Real.sqrt_nonneg _) (le_max_left _ _)
  have hrad2Nonneg : 0 ≤ gammaClippedPrefixRadius L 50000 (28493 / 5000) := by
    dsimp only [gammaClippedPrefixRadius]
    exact le_trans (Real.sqrt_nonneg _) (le_max_left _ _)
  have hcL : 0 ≤ c * L := by positivity
  have hsq1 := (sq_le_sq₀ hcL hrad1Nonneg).mpr hrad1
  have hsq2 := (sq_le_sq₀ hcL hrad2Nonneg).mpr hrad2
  have hscale1 := mul_le_mul_of_nonneg_left hsq1 (by norm_num only : (0 : ℝ) ≤ 99 / 40)
  have hscale2 := mul_le_mul_of_nonneg_left hsq2 (by norm_num only : (0 : ℝ) ≤ 99 / 40)
  have hbound1 : (99 / 40 : ℝ) * (c * L) ^ 2 ≤ gammaClippedBound1000 L := by
    dsimp only [gammaClippedBound1000]
    exact hscale1
  have hbound2 : (99 / 40 : ℝ) * (c * L) ^ 2 ≤ gammaClippedBound50000 L := by
    simpa only [gammaClippedBound50000, gammaClippedPrefixBound] using hscale2
  have hcoef : (7 / 10 : ℝ) ≤ (99 / 40) * c ^ 2 := by norm_num only [c]
  have hcoefL := mul_le_mul_of_nonneg_right hcoef (sq_nonneg L)
  have hbase : ((99 / 40 : ℝ) * c ^ 2) * L ^ 2 = (99 / 40 : ℝ) * (c * L) ^ 2 := by ring
  have hfirst : (7 / 10 : ℝ) * L ^ 2 ≤ gammaClippedBound1000 L := by
    calc
      _ ≤ ((99 / 40 : ℝ) * c ^ 2) * L ^ 2 := hcoefL
      _ = (99 / 40 : ℝ) * (c * L) ^ 2 := hbase
      _ ≤ gammaClippedBound1000 L := hbound1
  have hsecond : (7 / 10 : ℝ) * L ^ 2 ≤ gammaClippedBound50000 L := by
    calc
      _ ≤ ((99 / 40 : ℝ) * c ^ 2) * L ^ 2 := hcoefL
      _ = (99 / 40 : ℝ) * (c * L) ^ 2 := hbase
      _ ≤ gammaClippedBound50000 L := hbound2
  exact le_min hfirst hsecond

end PseudoPrime.PrimeTestBounds.MillerRabin
