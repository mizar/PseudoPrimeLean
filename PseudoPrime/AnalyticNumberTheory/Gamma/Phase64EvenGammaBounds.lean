/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Gamma.SignedGammaIntervalBounds
public import PseudoPrime.Analysis.Phase64DyadicEulerBounds

/-! # Certified even Gamma correction for the first phase candidate -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Gamma

/-- The positive real digamma argument (1/2+a)/2 associated with an even
Gamma-factor resolvent node. Rational arithmetic supplies its certificate input. -/
def phase64DigammaNode (a : ℚ) : ℚ :=
  (1 / 2 + a) / 2

/-- The rational signed even-Gamma allowance at one phase node, using a
length-64 reciprocal prefix and a length-20 logarithm series. Existing certified
log-pi endpoints select the upper allowance according to coefficient sign. -/
def phase64GammaNodeUpper (ab : ℚ × ℚ) : ℚ :=
  signedGammaNodeUpper ab.2 (rationalDigammaLower (phase64DigammaNode ab.1) 64 6 20)
    (rationalDigammaUpper (phase64DigammaNode ab.1) 64 6 20) (286182471 / 250000000)
    (35772809 / 31250000)

/-- All ten phase digamma nodes are at least one half and the translated
logarithm displacement is below one. Kernel rational arithmetic checks these
analytic admissibility conditions for the computed enclosures. -/
theorem phase64_gamma_node_checks :
    Analysis.phaseResolvent64Coefficients.Forall
      (fun ab ↦
        (1 / 2 : ℚ) ≤ phase64DigammaNode ab.1 ∧
          |1 - (phase64DigammaNode ab.1 + 64) / 2 ^ 6| < 1) := by
  decide +kernel

/-- The signed rational Gamma allowances for the new phase list sum to at
most -1499/1000. Exact kernel arithmetic evaluates the computed reciprocal and
logarithm prefixes, with no table of assumed digamma values. -/
theorem phase64_gamma_rational_upper_check :
    (Analysis.phaseResolvent64Coefficients.map phase64GammaNodeUpper).sum ≤ (-1499 / 1000 : ℚ) := by
  decide +kernel

/-- At every phase node, the actual signed even-Gamma logarithmic derivative
is bounded by its computed rational allowance. Apply the proved digamma
trapezoid enclosure and the generic sign-sensitive Gamma comparison. -/
theorem phase64_gamma_node_le (ab : ℚ × ℚ) (hab : ab ∈ Analysis.phaseResolvent64Coefficients) :
    (ab.2 : ℝ) * (logDeriv Complex.Gammaℝ (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re ≤
      (phase64GammaNodeUpper ab : ℝ) := by
  have hc := List.forall_iff_forall_mem.mp phase64_gamma_node_checks ab hab
  have hd := rationalDigammaBounds_sound hc.1 64 6 20 hc.2
  have he : ((phase64DigammaNode ab.1 : ℚ) : ℂ) = (((((1 / 2 : ℝ) + (ab.1 : ℝ)) / 2) : ℝ) : ℂ) := by
    norm_num only [phase64DigammaNode, Rat.cast_div, Rat.cast_add, Rat.cast_ofNat, Rat.cast_one,
      Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_ratCast, Complex.ofReal_one,
      Complex.ofReal_ofNat]
  rw [he] at hd
  simpa only [phase64GammaNodeUpper, Complex.ofReal_add] using
    signed_gamma_node_upper (Analysis.phase64_node_exponents_pos ab hab) ab.2 _ _ _ _ hd
      gamma_log_pi_bounds

/-- The signed even-Gamma correction of the new phase coefficient list is
at most -1499/1000. Sum the actual node bounds and the exact rational certificate.
This discharges the Gamma-factor numerical obligation for the first-cell budget. -/
theorem phase64_even_gamma_correction_le :
    (Analysis.phaseResolvent64Coefficients.map
          (fun ab ↦
            (ab.2 : ℝ) * (logDeriv Complex.Gammaℝ (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum ≤
      (-1499 / 1000 : ℝ) := by
  have hs := List.sum_le_sum (fun ab hab ↦ phase64_gamma_node_le ab hab)
  have hc := (Rat.cast_le (K := ℝ)).mpr phase64_gamma_rational_upper_check
  norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_ofNat, Rat.cast_list_sum, List.map_map,
    Function.comp_def] at hc
  linarith only [hs, hc]

end PseudoPrime.AnalyticNumberTheory.Gamma
