/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.GeneralValueCriteria

/-!
# Signed logarithmic improvements for the degree-one endpoint

The logarithmic deficit measures the improvement needed beyond the ideal cutoff majorant.
Bounds retaining a signed gain imply the exact endpoint when that gain covers both the
deficit and the remaining logarithmic error. This criterion does not prove such gains.
-/

@[expose] public section

namespace PseudoPrime.LLS.Extensions.GeneralLFunction

/-- The degree-one endpoint before its norm or reciprocal prefactor.
For `t=log log C`, it is `2(t-log 2+1/2)`. It is positive above `log 2-1/2`.
This common factor is used to compare logarithmic cutoff bounds with the public endpoint. -/
noncomputable def degreeOneEndpointFactor (t : ℝ) : ℝ :=
  2 * (t - (Real.log 2 - 1 / 2))

/-- The logarithmic excess of the ideal cutoff majorant over the degree-one endpoint.
The arguments are `t=log log C` and the positive half-logarithmic cutoff `z=log x/2`.
Above the endpoint's positivity threshold this excess is strictly positive; a signed
improvement must cover it in addition to the error retained in a logarithmic estimate. -/
noncomputable def degreeOneCutoffLogDeficit (t z : ℝ) : ℝ :=
  Real.log (idealDegreeOneValueUpper t z) - Real.log (degreeOneEndpointFactor t)

/-- Above the endpoint threshold, its scalar factor is positive.
The claim follows from positivity of the two factors. This justifies logarithm inversion
when converting signed cutoff bounds into the public degree-one value bound. -/
theorem degreeOneEndpointFactor_pos {t : ℝ} (ht : Real.log 2 - 1 / 2 < t) :
    0 < degreeOneEndpointFactor t := by exact mul_pos (by norm_num only) (sub_pos.mpr ht)

/-- For a positive half-logarithmic cutoff and a positive endpoint, the logarithmic
deficit is strictly positive. Apply strict monotonicity of the logarithm to the
previously proved strict cutoff comparison. Even a zero-error estimate needs a signed gain. -/
theorem degreeOneCutoffLogDeficit_pos {t z : ℝ} (ht : Real.log 2 - 1 / 2 < t) (hz : 0 < z) :
    0 < degreeOneCutoffLogDeficit t z := by
  exact
    sub_pos.mpr
      (Real.log_lt_log (degreeOneEndpointFactor_pos ht) (idealDegreeOneValueUpper_gt_endpoint t hz))

/-- A logarithmic estimate with prefactor `P>0`, error `b` and signed gain `g` implies
the exact degree-one endpoint if the gain covers the cutoff deficit plus `b`.
Exponentiate after subtracting the full deficit. No sign assumption on the error is needed;
this separates the required signed analytic improvement from scalar exponentiation. -/
theorem le_degreeOneEndpoint_of_signed_log_gain {v P t z b g : ℝ} (hP : 0 < P)
    (ht : Real.log 2 - 1 / 2 < t)
    (hv : Real.log v ≤ Real.log P + Real.log (idealDegreeOneValueUpper t z) + b - g)
    (hg : degreeOneCutoffLogDeficit t z + b ≤ g) : v ≤ P * degreeOneEndpointFactor t := by
  have hl : Real.log v ≤ Real.log P + Real.log (degreeOneEndpointFactor t) := by
    dsimp only [degreeOneCutoffLogDeficit] at hg
    linarith only [hv, hg]
  have he := (Real.le_exp_log v).trans (Real.exp_le_exp.mpr hl)
  rw [Real.exp_add, Real.exp_log hP, Real.exp_log (degreeOneEndpointFactor_pos ht)] at he
  exact he

/-- The signed cutoff input sufficient for the public degree-one endpoint.
For each member of the conductor-filter family, choose a positive half-logarithmic cutoff,
two logarithmic errors and two signed gains. Each gain must cover its error plus the
ideal cutoff deficit. The bounds concern the value norm and reciprocal norm separately;
the existence of such estimates is the remaining analytic input, not a proved property. -/
def DegreeOneSignedCutoffBounds : Prop :=
  ∀ᶠ f : FixedDegreeFamily 1 in conductorFilter 1,
    let t := Real.log (Real.log f.val.analyticConductor)
    ∃ z bU bR gU gR : ℝ,
      0 < z ∧
        Real.log 2 - 1 / 2 < t ∧
        Real.log ‖f.val.L 1‖ ≤
          Real.eulerMascheroniConstant + Real.log (idealDegreeOneValueUpper t z) + bU - gU ∧
        Real.log (1 / ‖f.val.L 1‖) ≤
          Real.log (6 * Real.exp Real.eulerMascheroniConstant / Real.pi ^ 2) +
              Real.log (idealDegreeOneValueUpper t z) +
              bR -
            gR ∧
        degreeOneCutoffLogDeficit t z + bU ≤ gU ∧ degreeOneCutoffLogDeficit t z + bR ≤ gR

/-- Convert a signed logarithmic norm estimate into the public degree-one upper bound.
The Euler prefactor is positive; the scalar conversion supplies the endpoint factor. -/
private theorem value_bound_of_signed_gain {v t z b g : ℝ} (ht : Real.log 2 - 1 / 2 < t)
    (hv :
      Real.log v ≤ Real.eulerMascheroniConstant + Real.log (idealDegreeOneValueUpper t z) + b - g)
    (hg : degreeOneCutoffLogDeficit t z + b ≤ g) :
    v ≤ 2 * Real.exp Real.eulerMascheroniConstant * (t - (Real.log 2 - 1 / 2)) := by
  have hn :=
    le_degreeOneEndpoint_of_signed_log_gain (Real.exp_pos Real.eulerMascheroniConstant) ht
      (by simpa only [Real.log_exp] using hv) hg
  convert hn using 1
  dsimp only [degreeOneEndpointFactor]
  ring

/-- Convert a signed logarithmic reciprocal estimate into the public degree-one lower bound.
The square-correction prefactor is positive; normalize the endpoint's factor two. -/
private theorem reciprocal_bound_of_signed_gain {v t z b g : ℝ} (ht : Real.log 2 - 1 / 2 < t)
    (hv :
      Real.log v ≤
        Real.log (6 * Real.exp Real.eulerMascheroniConstant / Real.pi ^ 2) +
            Real.log (idealDegreeOneValueUpper t z) +
            b -
          g)
    (hg : degreeOneCutoffLogDeficit t z + b ≤ g) :
    v ≤ 12 * Real.exp Real.eulerMascheroniConstant / Real.pi ^ 2 * (t - (Real.log 2 - 1 / 2)) := by
  have hn :=
    le_degreeOneEndpoint_of_signed_log_gain
      (div_pos (mul_pos (by norm_num only) (Real.exp_pos Real.eulerMascheroniConstant))
        (sq_pos_of_pos Real.pi_pos))
      ht hv hg
  convert hn using 1
  dsimp only [degreeOneEndpointFactor]
  ring

/-- Signed cutoff estimates covering both logarithmic deficits give the degree-one endpoint.
Apply the scalar conversion with the Euler prefactor and the square-correction prefactor,
then rearrange the common factor two. This connects the signed analytic input to the
existing criterion for the unchanged general L-value proposition. -/
theorem degreeOne_bounds_of_signed_cutoff (h : DegreeOneSignedCutoffBounds) :
    DegreeOneValueBounds := by
  filter_upwards [h] with f hf
  obtain ⟨z, bU, bR, gU, gR, _, ht, hU, hR, hgU, hgR⟩ := hf
  exact ⟨value_bound_of_signed_gain ht hU hgU, reciprocal_bound_of_signed_gain ht hR hgR⟩

/-- With nonnegative logarithmic error, every gain covering the cutoff deficit is positive.
Use positivity of the deficit and monotonicity under addition of the error. This rules out
obtaining the endpoint merely by reducing nonnegative errors, without a signed improvement. -/
theorem signed_cutoff_gain_pos {t z b g : ℝ} (ht : Real.log 2 - 1 / 2 < t) (hz : 0 < z) (hb : 0 ≤ b)
    (hg : degreeOneCutoffLogDeficit t z + b ≤ g) : 0 < g := by
  exact lt_of_lt_of_le (degreeOneCutoffLogDeficit_pos ht hz) ((le_add_of_nonneg_right hb).trans hg)

end PseudoPrime.LLS.Extensions.GeneralLFunction
