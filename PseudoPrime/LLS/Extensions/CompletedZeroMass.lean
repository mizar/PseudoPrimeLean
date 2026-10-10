/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.EntireZeroMass
public import PseudoPrime.LLS.Extensions.PaperDefinitions

/-!
# Completed-zero mass for admissible general L-functions

Order-at-most-one growth and individual RH imply inverse-square zero mass
convergence, without a separate summability assumption.
-/

@[expose] public section

namespace PseudoPrime.LLS.Extensions.GeneralLFunction

/-- Individual RH excludes every completed zero off the critical line.
Apply the RH predicate to a hypothetical zero. This gives nonvanishing at zero and one. -/
theorem completed_ne_zero_of_re_ne_half {f : GeneralLFunction} (hRH : f.RiemannHypothesis) {z : ℂ}
    (hz : z.re ≠ 1 / 2) : f.completed z ≠ 0 := by
  intro hzero
  exact hz (hRH ⟨z, hzero⟩)

/-- For individual RH, each inverse-square zero mass is at most five times
its regularized weight. Critical-line zeros have norm at least one half;
compare the two denominators. This transfers regularized mass convergence. -/
theorem zeroMassTerm_le_regularWeight (f : GeneralLFunction) (hRH : f.RiemannHypothesis)
    (ρ : f.Zero) :
    f.zeroMassTerm ρ ≤ 5 * AnalyticNumberTheory.General.regularZeroWeight f.completed ρ := by
  have hr : (1 / 2 : ℝ) ≤ ‖(ρ : ℂ)‖ := by
    rw [← hRH ρ]
    exact Complex.re_le_norm _
  have hp : 0 < ‖(ρ : ℂ)‖ ^ 2 := sq_pos_of_pos (by linarith only [hr])
  have hq : 0 < 1 + ‖(ρ : ℂ)‖ ^ 2 := by linarith only [hp]
  have he : 1 ≤ 4 * ‖(ρ : ℂ)‖ ^ 2 := by nlinarith only [hr]
  have hi : (1 : ℝ) / ‖(ρ : ℂ)‖ ^ 2 ≤ 5 / (1 + ‖(ρ : ℂ)‖ ^ 2) :=
    (div_le_div_iff₀ hp hq).mpr (by linarith only [he])
  have hm :=
    mul_le_mul_of_nonneg_left hi
      (Nat.cast_nonneg (analyticOrderNatAt f.completed (ρ : ℂ)) : (0 : ℝ) ≤ _)
  change
    (analyticOrderNatAt f.completed (ρ : ℂ) : ℝ) / ‖(ρ : ℂ)‖ ^ 2 ≤
      5 * ((analyticOrderNatAt f.completed (ρ : ℂ) : ℝ) / (1 + ‖(ρ : ℂ)‖ ^ 2))
  convert hm using 1 <;> ring

/-- For admissible f satisfying individual RH, the completed-zero mass series
is summable. Choose growth exponent three halves, apply Jensen and dyadic shell
convergence, then compare critical-line inverse-square weights.
This discharges the convergence clause in the generalized Lemma 2.5. -/
theorem summable_zeroMassTerm_of_admissible (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) : Summable f.zeroMassTerm := by
  have hF : Differentiable ℂ f.completed := hf.2.2.2.2.2.2.2.1
  have horder : AnalyticNumberTheory.General.HasOrderAtMostOne f.completed := hf.2.2.2.2.2.2.2.2.1
  have h0 : f.completed 0 ≠ 0 :=
    completed_ne_zero_of_re_ne_half hRH (by norm_num only [Complex.zero_re])
  obtain ⟨C, hC, hg⟩ :=
    AnalyticNumberTheory.General.exists_global_exponential_bound_of_orderAtMostOne hF.continuous
      horder (show (1 : ℝ) < 3 / 2 by norm_num only)
  have hs :=
    AnalyticNumberTheory.General.summable_regularZeroWeight hF h0 hC
      (show (0 : ℝ) ≤ 3 / 2 by norm_num only) (show (3 / 2 : ℝ) < 2 by norm_num only) hg
  exact
    Summable.of_nonneg_of_le (fun ρ ↦ div_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
      (zeroMassTerm_le_regularWeight f hRH) ((hs.subtype {z : ℂ | f.completed z = 0}).mul_left 5)

end PseudoPrime.LLS.Extensions.GeneralLFunction
