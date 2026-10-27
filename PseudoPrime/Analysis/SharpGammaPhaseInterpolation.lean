/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.SharpGammaLogSquareMoment
public import PseudoPrime.Analysis.Phase64MomentInterpolation

/-! # Parameterized Gamma interpolation and a doubled ordinate mesh -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: a positive scale, any certified logarithmic second-moment cap C,
and a comparison function whose quadratic correction is concave on an interval.
Claim: endpoint gap c loses at most (MR+C)*(b-a)^2/8 inside the interval.
Proof: use the actual positive cosine integral and integrate concavity.
Role: keep the analytic moment cost parameterized for different finite scales and kernels. -/
theorem gammaPhase_gap_lower_on_interval_of_moment {x : ℝ} (hx : 0 < x) {C : ℝ}
    (hMoment : (∫ u : ℝ in Set.Ioi 0, gammaHalfDensity u * (Real.log (u * x)) ^ 2) ≤ C)
    {a b MR c t : ℝ} (hab : a < b) (hMR : 0 ≤ MR) {R : ℝ → ℝ}
    (hR : ConcaveOn ℝ (Set.Icc a b) (fun z ↦ R z - MR / 2 * z ^ 2))
    (ha : c ≤ R a + (Complex.Gamma ((1 / 2 : ℂ) + Complex.I * a) * (x : ℂ) ^ (Complex.I * a)).re)
    (hb : c ≤ R b + (Complex.Gamma ((1 / 2 : ℂ) + Complex.I * b) * (x : ℂ) ^ (Complex.I * b)).re)
    (ht : t ∈ Set.Icc a b) :
    c - (MR + C) * (b - a) ^ 2 / 8 ≤
      R t + (Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) * (x : ℂ) ^ (Complex.I * t)).re := by
  have hw : MeasureTheory.IntegrableOn gammaHalfDensity (Set.Ioi 0) :=
    integrable_gammaPower (by norm_num only : (-1 : ℝ) < -1 / 2)
  have hl :
    MeasureTheory.AEStronglyMeasurable (fun u : ℝ ↦ Real.log (u * x))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    (Real.measurable_log.comp (measurable_id.mul_const x)).aestronglyMeasurable
  have hw0 : ∀ᵐ u ∂(MeasureTheory.volume.restrict (Set.Ioi 0)), 0 ≤ gammaHalfDensity u :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
      (fun u hu ↦ gammaHalfDensity_nonneg hu.le)
  rw [gammaHalf_phase_re_eq_cosineIntegral hx a] at ha
  rw [gammaHalf_phase_re_eq_cosineIntegral hx b] at hb
  rw [gammaHalf_phase_re_eq_cosineIntegral hx t]
  exact
    cosineIntegral_gap_lower_on_interval hw hl hw0 (integrable_gammaHalf_logSquare hx) hab hMR hR
      hMoment ha hb ht

/-- Input: positive scale with |log x|<=8 and endpoint gaps at least c.
Claim: the phase64 gap loses at most 408*(b-a)^2/8 on the full interval.
Proof: combine the sharper moment cap364 and resolvent curvature44.
Role: permit a coarser ordinate cover without weakening the actual phase conclusion. -/
theorem phase64_gap_lower_on_interval_sharp {x : ℝ} (hx : 0 < x) (hlog : |Real.log x| ≤ 8)
    {a b c t : ℝ} (hab : a < b)
    (ha :
      c ≤
        finiteSignedResolvent phaseResolvent64Coefficients a +
          (Complex.Gamma ((1 / 2 : ℂ) + Complex.I * a) * (x : ℂ) ^ (Complex.I * a)).re)
    (hb :
      c ≤
        finiteSignedResolvent phaseResolvent64Coefficients b +
          (Complex.Gamma ((1 / 2 : ℂ) + Complex.I * b) * (x : ℂ) ^ (Complex.I * b)).re)
    (ht : t ∈ Set.Icc a b) :
    c - 408 * (b - a) ^ 2 / 8 ≤
      finiteSignedResolvent phaseResolvent64Coefficients t +
        (Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) * (x : ℂ) ^ (Complex.I * t)).re := by
  have h :=
    gammaPhase_gap_lower_on_interval_of_moment hx (sharpGammaHalf_logSquareMoment_le_364 hx hlog)
      hab (finiteResolventCurvatureCost_nonneg _ phase64_scales_pos)
      (concaveOn_finiteSignedResolvent_quadratic _ phase64_scales_pos a b) ha hb ht
  have hm := mul_le_mul_of_nonneg_right phase64_curvature_cost_le_44 (sq_nonneg (b - a))
  nlinarith only [h, hm]

/-- Input: a scale with |log x|<=8, endpoints at distance at most 1/1000 and gap1/10000.
Claim: the actual gap is at least49/1000000 throughout the interval.
Proof: substitute the doubled mesh width into the sharper interpolation loss.
Role: halve the required endpoint density in finite spectral certification. -/
theorem phase64_gap_lower_on_millistep {x : ℝ} (hx : 0 < x) (hlog : |Real.log x| ≤ 8) {a b t : ℝ}
    (hab : a < b) (hwidth : b - a ≤ 1 / 1000)
    (ha :
      (1 / 10000 : ℝ) ≤
        finiteSignedResolvent phaseResolvent64Coefficients a +
          (Complex.Gamma ((1 / 2 : ℂ) + Complex.I * a) * (x : ℂ) ^ (Complex.I * a)).re)
    (hb :
      (1 / 10000 : ℝ) ≤
        finiteSignedResolvent phaseResolvent64Coefficients b +
          (Complex.Gamma ((1 / 2 : ℂ) + Complex.I * b) * (x : ℂ) ^ (Complex.I * b)).re)
    (ht : t ∈ Set.Icc a b) :
    (49 / 1000000 : ℝ) ≤
      finiteSignedResolvent phaseResolvent64Coefficients t +
        (Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) * (x : ℂ) ^ (Complex.I * t)).re := by
  have h := phase64_gap_lower_on_interval_sharp hx hlog hab ha hb ht
  have hs := mul_self_le_mul_self (sub_nonneg.mpr hab.le) hwidth
  nlinarith only [h, hs]

/-- Input: a positive bounded scale, rounded endpoint margins, and a finite cover of [-5,5]
with mesh at most1/1000. Claim: the actual signed Gamma phase is bounded at every ordinate.
Proof: use the sharper moment interpolation inside the cover and the proved norm tail outside.
Role: reduce finite endpoint obligations while preserving the global analytic majorant. -/
theorem phase64_signed_phase_le_of_rounded_cover_sharp {ι : Type*} {x : ℝ} (hx : 0 < x)
    (hlog : |Real.log x| ≤ 8) {G : ℕ} (hG : 0 < G) (S : Finset ι) (a b : ι → ℚ)
    (hvalid :
      ∀ i ∈ S,
        (a i : ℝ) < b i ∧
          (b i : ℝ) - a i ≤ 1 / 1000 ∧
          |(a i : ℝ)| ≤ 5 ∧
          |(b i : ℝ)| ≤ 5 ∧
          (1 / 10000 : ℝ) + ((1 / 25000 : ℝ) + 32768 / (G : ℝ)) ≤ roundedPhase64Gap G x (a i) ∧
          (1 / 10000 : ℝ) + ((1 / 25000 : ℝ) + 32768 / (G : ℝ)) ≤ roundedPhase64Gap G x (b i))
    (hcover : ∀ t : ℝ, |t| ≤ 5 → ∃ i ∈ S, t ∈ Set.Icc (a i : ℝ) (b i : ℝ)) (t : ℝ) :
    -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) * (x : ℂ) ^ (Complex.I * t)).re ≤
      finiteSignedResolvent phaseResolvent64Coefficients t := by
  apply phase64_signed_phase_le_of_low hx _ t
  intro u hu
  obtain ⟨i, hi, hui⟩ := hcover u hu
  obtain ⟨hab, hw, ha5, hb5, ha, hb⟩ := hvalid i hi
  have hA := phase64_actual_gap_ge_of_rounded_node hx hG (a i) ha5 ha
  have hB := phase64_actual_gap_ge_of_rounded_node hx hG (b i) hb5 hb
  have hg := phase64_gap_lower_on_millistep (t := u) hx hlog hab hw
  simp only [Complex.ofReal_ratCast] at hg
  have h := hg hA hB hui
  linarith only [h]

end PseudoPrime.Analysis
