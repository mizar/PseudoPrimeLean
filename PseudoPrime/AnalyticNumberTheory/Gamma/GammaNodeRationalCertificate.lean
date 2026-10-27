/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Gamma.DigammaRationalCertificate
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Tactic

/-! # Fixed rational certificates for the signed even Gamma nodes -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Gamma

/-- Exact rational reduction certifies the digamma interval at node 0.
The length-128 reciprocal prefix and length-12 logarithm series are checked
in the kernel, including their certified remainder allowances. -/
theorem gamma_digamma_node_0_check :
    rationalDigammaIntervalCheck (21 / 40 : ℚ) 128 7 12 (-9225799 / 5000000 : ℚ)
        (-9225761 / 5000000 : ℚ) =
      true := by
  decide +kernel

/-- The checked rational interval encloses the actual real digamma value
at signed even Gamma node 0. This is the analytic consequence of the certificate. -/
theorem gamma_digamma_node_0_bounds :
    ((-9225799 / 5000000 : ℚ) : ℝ) ≤ (Complex.digamma (21 / 40 : ℚ)).re ∧
      (Complex.digamma (21 / 40 : ℚ)).re ≤ ((-9225761 / 5000000 : ℚ) : ℝ) := by
  exact rationalDigammaIntervalCheck_sound gamma_digamma_node_0_check

/-- Exact rational reduction certifies the digamma interval at node 1.
The length-128 reciprocal prefix and length-12 logarithm series are checked
in the kernel, including their certified remainder allowances. -/
theorem gamma_digamma_node_1_check :
    rationalDigammaIntervalCheck (13 / 20 : ℚ) 128 7 12 (-85647 / 62500 : ℚ)
        (-3425861 / 2500000 : ℚ) =
      true := by
  decide +kernel

/-- The checked rational interval encloses the actual real digamma value
at signed even Gamma node 1. This is the analytic consequence of the certificate. -/
theorem gamma_digamma_node_1_bounds :
    ((-85647 / 62500 : ℚ) : ℝ) ≤ (Complex.digamma (13 / 20 : ℚ)).re ∧
      (Complex.digamma (13 / 20 : ℚ)).re ≤ ((-3425861 / 2500000 : ℚ) : ℝ) := by
  exact rationalDigammaIntervalCheck_sound gamma_digamma_node_1_check

/-- Exact rational reduction certifies the digamma interval at node 2.
The length-128 reciprocal prefix and length-12 logarithm series are checked
in the kernel, including their certified remainder allowances. -/
theorem gamma_digamma_node_2_check :
    rationalDigammaIntervalCheck (3 / 4 : ℚ) 128 7 12 (-5429317 / 5000000 : ℚ)
        (-5429279 / 5000000 : ℚ) =
      true := by
  decide +kernel

/-- The checked rational interval encloses the actual real digamma value
at signed even Gamma node 2. This is the analytic consequence of the certificate. -/
theorem gamma_digamma_node_2_bounds :
    ((-5429317 / 5000000 : ℚ) : ℝ) ≤ (Complex.digamma (3 / 4 : ℚ)).re ∧
      (Complex.digamma (3 / 4 : ℚ)).re ≤ ((-5429279 / 5000000 : ℚ) : ℝ) := by
  exact rationalDigammaIntervalCheck_sound gamma_digamma_node_2_check

/-- Exact rational reduction certifies the digamma interval at node 3.
The length-128 reciprocal prefix and length-12 logarithm series are checked
in the kernel, including their certified remainder allowances. -/
theorem gamma_digamma_node_3_check :
    rationalDigammaIntervalCheck (11 / 10 : ℚ) 128 7 12 (-169503 / 400000 : ℚ)
        (-4237499 / 10000000 : ℚ) =
      true := by
  decide +kernel

/-- The checked rational interval encloses the actual real digamma value
at signed even Gamma node 3. This is the analytic consequence of the certificate. -/
theorem gamma_digamma_node_3_bounds :
    ((-169503 / 400000 : ℚ) : ℝ) ≤ (Complex.digamma (11 / 10 : ℚ)).re ∧
      (Complex.digamma (11 / 10 : ℚ)).re ≤ ((-4237499 / 10000000 : ℚ) : ℝ) := by
  exact rationalDigammaIntervalCheck_sound gamma_digamma_node_3_check

/-- Exact rational reduction certifies the digamma interval at node 4.
The length-128 reciprocal prefix and length-12 logarithm series are checked
in the kernel, including their certified remainder allowances. -/
theorem gamma_digamma_node_4_check :
    rationalDigammaIntervalCheck (7 / 5 : ℚ) 128 7 12 (-613871 / 10000000 : ℚ)
        (-122759 / 2000000 : ℚ) =
      true := by
  decide +kernel

/-- The checked rational interval encloses the actual real digamma value
at signed even Gamma node 4. This is the analytic consequence of the certificate. -/
theorem gamma_digamma_node_4_bounds :
    ((-613871 / 10000000 : ℚ) : ℝ) ≤ (Complex.digamma (7 / 5 : ℚ)).re ∧
      (Complex.digamma (7 / 5 : ℚ)).re ≤ ((-122759 / 2000000 : ℚ) : ℝ) := by
  exact rationalDigammaIntervalCheck_sound gamma_digamma_node_4_check

/-- Exact rational reduction certifies the digamma interval at node 5.
The length-128 reciprocal prefix and length-12 logarithm series are checked
in the kernel, including their certified remainder allowances. -/
theorem gamma_digamma_node_5_check :
    rationalDigammaIntervalCheck (37 / 20 : ℚ) 128 7 12 (128479 / 400000 : ℚ) (64241 / 200000 : ℚ) =
      true := by
  decide +kernel

/-- The checked rational interval encloses the actual real digamma value
at signed even Gamma node 5. This is the analytic consequence of the certificate. -/
theorem gamma_digamma_node_5_bounds :
    ((128479 / 400000 : ℚ) : ℝ) ≤ (Complex.digamma (37 / 20 : ℚ)).re ∧
      (Complex.digamma (37 / 20 : ℚ)).re ≤ ((64241 / 200000 : ℚ) : ℝ) := by
  exact rationalDigammaIntervalCheck_sound gamma_digamma_node_5_check

/-- Exact rational reduction certifies the digamma interval at node 6.
The length-128 reciprocal prefix and length-12 logarithm series are checked
in the kernel, including their certified remainder allowances. -/
theorem gamma_digamma_node_6_check :
    rationalDigammaIntervalCheck (5 / 2 : ℚ) 128 7 12 (7031541 / 10000000 : ℚ)
        (109869 / 156250 : ℚ) =
      true := by
  decide +kernel

/-- The checked rational interval encloses the actual real digamma value
at signed even Gamma node 6. This is the analytic consequence of the certificate. -/
theorem gamma_digamma_node_6_bounds :
    ((7031541 / 10000000 : ℚ) : ℝ) ≤ (Complex.digamma (5 / 2 : ℚ)).re ∧
      (Complex.digamma (5 / 2 : ℚ)).re ≤ ((109869 / 156250 : ℚ) : ℝ) := by
  exact rationalDigammaIntervalCheck_sound gamma_digamma_node_6_check

/-- Exact rational reduction certifies the digamma interval at node 7.
The length-128 reciprocal prefix and length-12 logarithm series are checked
in the kernel, including their certified remainder allowances. -/
theorem gamma_digamma_node_7_check :
    rationalDigammaIntervalCheck (15 / 4 : ℚ) 128 7 12 (11825349 / 10000000 : ℚ)
        (5912711 / 5000000 : ℚ) =
      true := by
  decide +kernel

/-- The checked rational interval encloses the actual real digamma value
at signed even Gamma node 7. This is the analytic consequence of the certificate. -/
theorem gamma_digamma_node_7_bounds :
    ((11825349 / 10000000 : ℚ) : ℝ) ≤ (Complex.digamma (15 / 4 : ℚ)).re ∧
      (Complex.digamma (15 / 4 : ℚ)).re ≤ ((5912711 / 5000000 : ℚ) : ℝ) := by
  exact rationalDigammaIntervalCheck_sound gamma_digamma_node_7_check

/-- The logarithm of the rational lower pi endpoint lies in the
stated rational interval. Exact Taylor reduction proves the certificate in the kernel. -/
theorem gamma_log_pi_lower_check :
    Analysis.rationalLogIntervalCheck (157079632679489661923 / 50000000000000000000 : ℚ) 2 24
        (286182471 / 250000000 : ℚ) (35772809 / 31250000 : ℚ) =
      true := by
  decide +kernel

/-- The logarithm of the rational upper pi endpoint lies in the
stated rational interval. Exact Taylor reduction proves the certificate in the kernel. -/
theorem gamma_log_pi_upper_check :
    Analysis.rationalLogIntervalCheck (314159265358979323847 / 100000000000000000000 : ℚ) 2 24
        (286182471 / 250000000 : ℚ) (35772809 / 31250000 : ℚ) =
      true := by
  decide +kernel

/-- The two rational pi endpoints and logarithm monotonicity enclose log pi.
The interval is used with both signs in the signed Gamma-factor sum. -/
theorem gamma_log_pi_bounds :
    ((286182471 / 250000000 : ℚ) : ℝ) ≤ Real.log Real.pi ∧
      Real.log Real.pi ≤ ((35772809 / 31250000 : ℚ) : ℝ) := by
  have hl := Analysis.rationalLogIntervalCheck_sound gamma_log_pi_lower_check
  have hu := Analysis.rationalLogIntervalCheck_sound gamma_log_pi_upper_check
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hl hu ⊢
  have hp : (157079632679489661923 / 50000000000000000000 : ℝ) ≤ Real.pi := by
    convert Real.pi_gt_d20.le using 1
    norm_num only
  have hq : Real.pi ≤ (314159265358979323847 / 100000000000000000000 : ℝ) := by
    convert Real.pi_lt_d20.le using 1
    norm_num only
  exact
    ⟨hl.1.trans (Real.log_le_log (by norm_num only) hp),
      (Real.log_le_log Real.pi_pos hq).trans hu.2⟩

end PseudoPrime.AnalyticNumberTheory.Gamma
