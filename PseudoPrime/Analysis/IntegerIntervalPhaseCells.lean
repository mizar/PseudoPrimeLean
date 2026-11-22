/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.IntegerIntervalPhase
public import PseudoPrime.Analysis.TrigonometricLinearError

/-! # Quadratic phase-cell certificates -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Check that a nonnegative integer radius at positive scale G has
quadratic remainder at most error/G. The cross-product inequality avoids
rational division in the executable checker and is used for phase cells. -/
def phaseRadiusCheck (G radius error : ℤ) : Bool :=
  decide (0 < G ∧ 0 ≤ radius ∧ 0 ≤ error ∧ radius ^ 2 ≤ 2 * error * G)

/-- A successful integer radius check controls the sharp quadratic phase
remainder at every displacement in the radius. All rounding information
is reduced to the checked integer cross-product inequality. -/
theorem phaseRadiusCheck_sound {G radius error : ℤ} (h : phaseRadiusCheck G radius error = true)
    {d : ℝ} (hd : |d| ≤ (radius : ℝ) / G) : d ^ 2 / 2 ≤ (error : ℝ) / G := by
  have hc := of_decide_eq_true h
  have hg : 0 < (G : ℝ) := by exact_mod_cast hc.1
  have hb : (radius : ℝ) ^ 2 ≤ 2 * (error : ℝ) * G := by exact_mod_cast hc.2.2.2
  have he : ((radius : ℝ) / G) ^ 2 / 2 ≤ (error : ℝ) / G := by
    have heq : ((radius : ℝ) / G) ^ 2 / 2 = (radius : ℝ) ^ 2 / (2 * (G : ℝ) ^ 2) := by ring
    rw [heq]
    apply (div_le_div_iff₀ (mul_pos (by norm_num only) (sq_pos_of_pos hg)) hg).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hb hg.le]
  have hp := pow_le_pow_left₀ (abs_nonneg d) hd 2
  rw [sq_abs] at hp
  exact (div_le_div_of_nonneg_right hp (by norm_num only)).trans he

/-- A certified center phase and checked products enclose the linearized
phase at x. Widen both coordinates by the sharp quadratic error to obtain
containment for exp(i*x) throughout a phase cell, preserving first-order cancellation. -/
theorem phase_cell_contains {C S D SD CD : IntegerInterval} {G error : ℤ} {c x : ℝ}
    (hc : complexIntervalContains C S G (Complex.exp ((c : ℂ) * Complex.I)))
    (hd : D.Contains G (x - c))
    (hsd : integerProductCheck G S.lower S.upper D.lower D.upper SD.lower SD.upper = true)
    (hcd : integerProductCheck G C.lower C.upper D.lower D.upper CD.lower CD.upper = true)
    (he : (x - c) ^ 2 / 2 ≤ (error : ℝ) / G) :
    complexIntervalContains ((C.add SD.neg).widen error) ((S.add CD).widen error) G
      (Complex.exp ((x : ℂ) * Complex.I)) := by
  have hcos := hc.1
  have hsin := hc.2
  rw [Complex.exp_ofReal_mul_I_re] at hcos
  rw [Complex.exp_ofReal_mul_I_im] at hsin
  have hsd' := IntegerInterval.product_contains hsd hsin hd
  have hcd' := IntegerInterval.product_contains hcd hcos hd
  have hc' := IntegerInterval.add_contains hcos (IntegerInterval.neg_contains hsd')
  have hs' := IntegerInterval.add_contains hsin hcd'
  have ec : |Real.cos x - (Real.cos c + -(Real.sin c * (x - c)))| ≤ (error : ℝ) / G := by
    have h := (cos_linear_error c x).trans he
    convert h using 1
    congr 1
    ring
  have es : |Real.sin x - (Real.sin c + Real.cos c * (x - c))| ≤ (error : ℝ) / G := by
    have h := (sin_linear_error c x).trans he
    convert h using 1
    congr 1
    ring
  constructor
  · rw [Complex.exp_ofReal_mul_I_re]
    exact IntegerInterval.widen_contains hc' ec
  · rw [Complex.exp_ofReal_mul_I_im]
    exact IntegerInterval.widen_contains hs' es

/-- A successful integer radius check supplies the phase-cell remainder
automatically. Together with center and product certificates, it certifies
every phase in the specified radius without list indexing or point sampling. -/
theorem phase_cell_radius_contains {C S D SD CD : IntegerInterval} {G radius error : ℤ} {c x : ℝ}
    (hc : complexIntervalContains C S G (Complex.exp ((c : ℂ) * Complex.I)))
    (hd : D.Contains G (x - c))
    (hsd : integerProductCheck G S.lower S.upper D.lower D.upper SD.lower SD.upper = true)
    (hcd : integerProductCheck G C.lower C.upper D.lower D.upper CD.lower CD.upper = true)
    (hr : phaseRadiusCheck G radius error = true) (hx : |x - c| ≤ (radius : ℝ) / G) :
    complexIntervalContains ((C.add SD.neg).widen error) ((S.add CD).widen error) G
      (Complex.exp ((x : ℂ) * Complex.I)) := by
  exact phase_cell_contains hc hd hsd hcd (phaseRadiusCheck_sound hr hx)

end PseudoPrime.Analysis
