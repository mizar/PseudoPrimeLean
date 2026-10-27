/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.FiniteResolventCurvature
public import PseudoPrime.Analysis.GammaPhaseMomentInterpolation
public import PseudoPrime.Analysis.PhaseResolvent64ExpTail
public import PseudoPrime.Analysis.RoundedGammaPhase

/-! # Continuous Gamma phase bounds from rounded interval endpoints -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: a node in the phase64 coefficient list.
Claim: its real scale is positive. Proof: apply the certified half-line node check.
Role: discharge positivity for the curvature cost and concavity theorems. -/
theorem phase64_scales_pos (ab : ℚ × ℚ) (hab : ab ∈ phaseResolvent64Coefficients) :
    0 < (ab.1 : ℝ) := by
  have h := (finiteSignedPhaseNodeCheck_sound _ phaseResolvent64_node_check).1 ab hab
  exact Rat.cast_pos.mpr (lt_trans (by norm_num only : (0 : ℚ) < 1 / 2) h)

/-- Claim: the total absolute curvature cost of the phase64 resolvent is at most 44.
Proof: evaluate the finite rational expression exactly.
Role: combine rational curvature with the Gamma logarithmic moment cost. -/
theorem phase64_curvature_cost_le_44 :
    finiteResolventCurvatureCost phaseResolvent64Coefficients ≤ 44 := by
  norm_num only [finiteResolventCurvatureCost, phaseResolvent64Coefficients, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil]

/-- Input: a positive scale with |log x|<=8 and endpoint gaps at least c on [a,b].
Claim: the actual signed Gamma gap is at least c-1068*(b-a)^2/8 throughout [a,b].
Proof: combine the Gamma moment bound 1024 and the resolvent curvature bound 44.
Role: control all ordinates between certified nodes. -/
theorem phase64_gap_lower_on_interval {x : ℝ} (hx : 0 < x) (hlog : |Real.log x| ≤ 8) {a b c t : ℝ}
    (hab : a < b)
    (ha :
      c ≤
        finiteSignedResolvent phaseResolvent64Coefficients a +
          (Complex.Gamma ((1 / 2 : ℂ) + Complex.I * a) * (x : ℂ) ^ (Complex.I * a)).re)
    (hb :
      c ≤
        finiteSignedResolvent phaseResolvent64Coefficients b +
          (Complex.Gamma ((1 / 2 : ℂ) + Complex.I * b) * (x : ℂ) ^ (Complex.I * b)).re)
    (ht : t ∈ Set.Icc a b) :
    c - 1068 * (b - a) ^ 2 / 8 ≤
      finiteSignedResolvent phaseResolvent64Coefficients t +
        (Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) * (x : ℂ) ^ (Complex.I * t)).re := by
  have h :=
    gammaPhase_gap_lower_on_interval hx hlog hab
      (finiteResolventCurvatureCost_nonneg _ phase64_scales_pos)
      (concaveOn_finiteSignedResolvent_quadratic _ phase64_scales_pos a b) ha hb ht
  have hm := mul_le_mul_of_nonneg_right phase64_curvature_cost_le_44 (sq_nonneg (b - a))
  nlinarith only [h, hm]

/-- Input: endpoint gaps at least 1/10000, width at most 1/2000, and |log x|<=8.
Claim: the actual Gamma gap is at least 533/8000000 on the entire interval.
Proof: substitute the mesh width into the continuous interpolation loss.
Role: provide an explicit positive margin without ordinate enumeration. -/
theorem phase64_gap_lower_on_small_interval {x : ℝ} (hx : 0 < x) (hlog : |Real.log x| ≤ 8)
    {a b t : ℝ} (hab : a < b) (hwidth : b - a ≤ 1 / 2000)
    (ha :
      (1 / 10000 : ℝ) ≤
        finiteSignedResolvent phaseResolvent64Coefficients a +
          (Complex.Gamma ((1 / 2 : ℂ) + Complex.I * a) * (x : ℂ) ^ (Complex.I * a)).re)
    (hb :
      (1 / 10000 : ℝ) ≤
        finiteSignedResolvent phaseResolvent64Coefficients b +
          (Complex.Gamma ((1 / 2 : ℂ) + Complex.I * b) * (x : ℂ) ^ (Complex.I * b)).re)
    (ht : t ∈ Set.Icc a b) :
    (533 / 8000000 : ℝ) ≤
      finiteSignedResolvent phaseResolvent64Coefficients t +
        (Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) * (x : ℂ) ^ (Complex.I * t)).re := by
  have h := phase64_gap_lower_on_interval hx hlog hab ha hb ht
  have hs := mul_self_le_mul_self (sub_nonneg.mpr hab.le) hwidth
  nlinarith only [h, hs]

/-- Input: a rounding denominator, real scale and rational ordinate.
Output: the rational resolvent plus the rounded Gamma coefficient phase.
Definition: the remaining transcendental factor is exp(i*t*log(256*x)).
Role: express endpoint certificate obligations independently of actual Gamma values. -/
noncomputable def roundedPhase64Gap (G : ℕ) (x : ℝ) (t : ℚ) : ℝ :=
  finiteSignedResolvent phaseResolvent64Coefficients (t : ℝ) +
    (roundedGamma256Coefficient G t *
        Complex.exp (Complex.I * (((t : ℝ) * Real.log (256 * x) : ℝ) : ℂ))).re

/-- Input: a positive scale, a positive rounding denominator and a node in [-5,5].
Claim: a rounded gap exceeding c by the certified approximation error gives actual gap c.
Proof: use the rounded Gamma phase error 1/25000+32768/G.
Role: transfer executable node evaluations to actual analytic endpoints. -/
theorem phase64_actual_gap_ge_of_rounded_node {x : ℝ} (hx : 0 < x) {G : ℕ} (hG : 0 < G) (t : ℚ)
    (ht : |(t : ℝ)| ≤ 5) {c : ℝ}
    (hc : c + ((1 / 25000 : ℝ) + 32768 / (G : ℝ)) ≤ roundedPhase64Gap G x t) :
    c ≤
      finiteSignedResolvent phaseResolvent64Coefficients (t : ℝ) +
        (Complex.Gamma ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) *
            (x : ℂ) ^ (Complex.I * (t : ℂ))).re := by
  have h := neg_re_Gamma_phase_le_roundedCoefficient hx hG t ht
  dsimp only [roundedPhase64Gap] at hc
  linarith only [h, hc]

/-- Input: two rational endpoints in [-5,5] at distance at most 1/2000,
positive scale with |log x|<=8, and rounded gaps including the full error allowance.
Claim: the actual signed Gamma gap is at least 533/8000000 between the endpoints.
Proof: transfer both node bounds and apply moment-controlled interpolation.
Role: turn finite rounded endpoint certificates into continuous analytic bounds. -/
theorem phase64_gap_lower_of_rounded_endpoints {x : ℝ} (hx : 0 < x) (hlog : |Real.log x| ≤ 8)
    {G : ℕ} (hG : 0 < G) {a b : ℚ} (hab : (a : ℝ) < b) (hwidth : (b : ℝ) - a ≤ 1 / 2000)
    (ha5 : |(a : ℝ)| ≤ 5) (hb5 : |(b : ℝ)| ≤ 5)
    (ha : (1 / 10000 : ℝ) + ((1 / 25000 : ℝ) + 32768 / (G : ℝ)) ≤ roundedPhase64Gap G x a)
    (hb : (1 / 10000 : ℝ) + ((1 / 25000 : ℝ) + 32768 / (G : ℝ)) ≤ roundedPhase64Gap G x b) {t : ℝ}
    (ht : t ∈ Set.Icc (a : ℝ) (b : ℝ)) :
    (533 / 8000000 : ℝ) ≤
      finiteSignedResolvent phaseResolvent64Coefficients t +
        (Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) * (x : ℂ) ^ (Complex.I * t)).re := by
  have hA := phase64_actual_gap_ge_of_rounded_node hx hG a ha5 ha
  have hB := phase64_actual_gap_ge_of_rounded_node hx hG b hb5 hb
  have h := phase64_gap_lower_on_small_interval (t := t) hx hlog hab hwidth
  simp only [Complex.ofReal_ratCast] at h
  exact h hA hB ht

/-- Input: a finite rational interval cover of [-5,5], mesh at most 1/2000,
and certified rounded endpoint gaps at a positive scale with |log x|<=8.
Claim: the actual negative Gamma phase is bounded by the phase64 resolvent at every ordinate.
Proof: interpolate inside the cover and use the established Gamma norm bound outside it.
Role: supply the global phase hypothesis for arithmetic-sum witness bounds. -/
theorem phase64_signed_phase_le_of_rounded_cover {ι : Type*} {x : ℝ} (hx : 0 < x)
    (hlog : |Real.log x| ≤ 8) {G : ℕ} (hG : 0 < G) (S : Finset ι) (a b : ι → ℚ)
    (hvalid :
      ∀ i ∈ S,
        (a i : ℝ) < b i ∧
          (b i : ℝ) - a i ≤ 1 / 2000 ∧
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
  have h := phase64_gap_lower_of_rounded_endpoints hx hlog hG hab hw ha5 hb5 ha hb hui
  linarith only [h]

end PseudoPrime.Analysis
