/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.ConductorCutoffBounds
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeSumBounds

/-! Uniform vanishing of the general L-value truncation error at conductor cutoffs. -/

@[expose] public section

namespace PseudoPrime.LLS.Extensions.GeneralLFunction

/-- For positive degree, conductor above one and cutoff above one, express the uniform
truncation error using reciprocal cutoff, square-root and logarithm scales.
Substitute `log C = 2d sqrt x` and `x = (sqrt x)^2`, then clear nonzero denominators.
This identity separates all terms whose fixed-degree limits must vanish. -/
theorem truncatedConductorErrorBound_eq_scaled (f : GeneralLFunction) {d : ℕ} (hd : 0 < d)
    (hdegree : f.degree = d) (hC : 1 < f.analyticConductor)
    (hx : 1 < valueCutoff d f.analyticConductor) :
    let x := valueCutoff d f.analyticConductor
    let r := Real.sqrt x
    let l := Real.log x
    let u := (34 / 7 : ℝ) * (d : ℝ) + (d : ℝ) * zeroMassDegreeBound / r
    let z :=
      (d : ℝ) *
          (2 * AnalyticNumberTheory.Gamma.digammaLogErrorBound + 3 * |zeroMassDegreeBound| +
            2 * (1 + AnalyticNumberTheory.Gamma.reciprocalGammaTailBound) +
            2 * (Real.log 4 + 4)) +
        (116 / 7 : ℝ) * (d : ℝ)
    f.truncatedConductorErrorBound x =
      u / (2 * r * l) + u / l ^ 2 + 2 * (d : ℝ) / (x * l ^ 2) + (d : ℝ) / (r * l) +
        (d : ℝ) * AnalyticNumberTheory.Gamma.digammaLogErrorBound / (2 * x * l) +
        u / (r * l) +
        (d : ℝ) / x +
        (d : ℝ) * AnalyticNumberTheory.Gamma.reciprocalGammaTailBound / (x * l) +
        2 * (d : ℝ) * (AnalyticNumberTheory.Arithmetic.reciprocalMangoldtSum x / (r * l)) +
        z / (r * l) := by
  dsimp only
  have hx0 := zero_lt_one.trans hx
  have hr := (Real.sqrt_pos.mpr hx0).ne'
  have hl := (Real.log_pos hx).ne'
  have hrel :
    Real.log f.analyticConductor = 2 * (d : ℝ) * Real.sqrt (valueCutoff d f.analyticConductor) := by
    rw [sqrt_valueCutoff hd hC.le, mul_div_cancel₀]
    exact (mul_pos (by norm_num only : (0 : ℝ) < 2) (Nat.cast_pos.mpr hd)).ne'
  unfold truncatedConductorErrorBound
  rw [hdegree, abs_of_pos (Real.log_pos hC), hrel]
  generalize hxdef : valueCutoff d f.analyticConductor = x at *
  generalize hrdef : Real.sqrt x = r at *
  have hsquare : r ^ 2 = x := by
    rw [← hrdef]
    exact Real.sq_sqrt hx0.le
  rw [← hsquare]
  rw [← hsquare] at hl
  field_simp (disch := simp only [hr, hl, ne_eq, not_false_eq_true])
  ring

/-- For positive fixed degree, the full conductor-centered truncation error at the common
cutoff tends to zero uniformly on the conductor filter. Expand the error into reciprocal
scales and the scaled Mangoldt majorant, and take their limits term by term.
This leaves the quantitative arithmetic main-term estimates as separate analytic inputs. -/
theorem tendsto_truncatedConductorErrorBound_at_valueCutoff {d : ℕ} (hd : 0 < d) :
    Filter.Tendsto
      (fun f : FixedDegreeFamily d ↦
        f.val.truncatedConductorErrorBound (valueCutoff d f.val.analyticConductor))
      (conductorFilter d) (nhds 0) := by
  have hi := (tendsto_valueCutoff_atTop hd).inv_tendsto_atTop
  have hr := (Real.tendsto_sqrt_atTop.comp (tendsto_valueCutoff_atTop hd)).inv_tendsto_atTop
  have hl := (tendsto_log_valueCutoff_atTop hd).inv_tendsto_atTop
  have hp :=
    AnalyticNumberTheory.Arithmetic.tendsto_reciprocalMangoldtSum_scaled.comp
      (tendsto_valueCutoff_atTop hd)
  have hu := (hr.const_mul ((d : ℝ) * zeroMassDegreeBound)).const_add ((34 / 7 : ℝ) * (d : ℝ))
  let z :=
    (d : ℝ) *
        (2 * AnalyticNumberTheory.Gamma.digammaLogErrorBound + 3 * |zeroMassDegreeBound| +
          2 * (1 + AnalyticNumberTheory.Gamma.reciprocalGammaTailBound) +
          2 * (Real.log 4 + 4)) +
      (116 / 7 : ℝ) * (d : ℝ)
  have hsum :=
    (hu.mul ((hr.const_mul (1 / 2 : ℝ)).mul hl)).add (hu.mul (hl.mul hl)) |>.add
                    (((hi.mul (hl.mul hl)).const_mul (2 * (d : ℝ)))) |>.add
                  ((hr.mul hl).const_mul (d : ℝ)) |>.add
                (((hi.const_mul (1 / 2 : ℝ)).mul hl).const_mul
                  ((d : ℝ) * AnalyticNumberTheory.Gamma.digammaLogErrorBound)) |>.add
              (hu.mul (hr.mul hl)) |>.add
            (hi.const_mul (d : ℝ)) |>.add
          ((hi.mul hl).const_mul
            ((d : ℝ) * AnalyticNumberTheory.Gamma.reciprocalGammaTailBound)) |>.add
        (hp.const_mul (2 * (d : ℝ))) |>.add
      ((hr.mul hl).const_mul z)
  simp only [mul_zero, add_zero] at hsum
  apply hsum.congr'
  have hC :
    Filter.Tendsto (fun f : FixedDegreeFamily d ↦ f.val.analyticConductor) (conductorFilter d)
      Filter.atTop :=
    Filter.tendsto_comap
  filter_upwards [hC.eventually (Filter.eventually_gt_atTop (1 : ℝ)),
    (tendsto_valueCutoff_atTop hd).eventually (Filter.eventually_gt_atTop (1 : ℝ))] with f hCf hxf
  rw [truncatedConductorErrorBound_eq_scaled f.val hd f.property.1 hCf hxf]
  dsimp only [z]
  simp only [div_eq_mul_inv, mul_inv_rev, pow_two, Pi.inv_apply, Function.comp_apply]
  ring

/-- For positive fixed degree and any positive epsilon, sufficiently large conductor gives
upper bounds for the L-value and its reciprocal with exponent `d Q(x) + epsilon`.
The reciprocal bound retains the factor `(6 / pi^2)^d`. Absorb the leading conductor term,
full truncation error and square loss using their uniform zero limits.
This reduces both final value estimates to the same arithmetic majorant. -/
theorem eventually_norm_L_one_and_reciprocal_le_arithmetic_majorant {d : ℕ} (hd : 0 < d) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ f : FixedDegreeFamily d in conductorFilter d,
      let x := valueCutoff d f.val.analyticConductor
      ‖f.val.L 1‖ ≤
          Real.exp ((d : ℝ) * AnalyticNumberTheory.Arithmetic.truncatedMangoldtMajorant x + ε) ∧
        1 / ‖f.val.L 1‖ ≤
          (6 / Real.pi ^ 2) ^ d *
            Real.exp
              ((d : ℝ) * AnalyticNumberTheory.Arithmetic.truncatedMangoldtMajorant x + ε) := by
  have he :=
    (tendsto_conductor_term_at_valueCutoff hd).add
        (tendsto_truncatedConductorErrorBound_at_valueCutoff hd) |>.add
      ((tendsto_squareLoss_at_valueCutoff hd).const_mul (d : ℝ))
  simp only [add_zero, mul_zero] at he
  filter_upwards [eventually_norm_L_one_and_reciprocal_le_valueCutoff hd,
    he.eventually (gt_mem_nhds hε)] with f hb heps
  dsimp only at hb ⊢
  have hs : 0 ≤ (d : ℝ) * (3 / (2 * Real.sqrt (valueCutoff d f.val.analyticConductor))) :=
    mul_nonneg (Nat.cast_nonneg d)
      (div_nonneg (by norm_num only : (0 : ℝ) ≤ 3)
        (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) (Real.sqrt_nonneg _)))
  refine
    ⟨hb.1.trans (Real.exp_le_exp.mpr ?_),
      hb.2.trans
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
          (pow_nonneg (div_nonneg (by norm_num only : (0 : ℝ) ≤ 6) (sq_nonneg Real.pi)) d))⟩
  · linarith only [heps, hs]
  · linarith only [heps]

end PseudoPrime.LLS.Extensions.GeneralLFunction
