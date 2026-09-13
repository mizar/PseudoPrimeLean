/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.RiemannXi.ZeroMassBounds
import PseudoPrime.Analysis.NumericalLogBounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ConductorPrimeFactors
import PseudoPrime.LLS.Lemma21
import PseudoPrime.Analysis.RealLog
import PseudoPrime.Analysis.LogarithmicRatios

/-!
# Elementary numerical reductions for LLS Part 1

This file proves the numerical comparisons used in Section 3.1 of Lamzouri--Li--Soundararajan,
including `llsTheorem11S1ComparisonUpperSimplification` and `llsTheorem11S1NumericalSeparation`.
It consumes the foundation's conductor, prime-factor, and logarithmic-ratio estimates.
The independent Q-ne-one numerical envelopes are defined in `LLS/Extensions/QNeOneNumerics.lean`.
-/

namespace PseudoPrime.LLS

/--
The remaining one-variable coefficient condition for eliminating the conductor from the upper
bound.  It is separated from the algebraic tradeoff so its proof can use only real
analysis at the Part 1 radius.
-/
def LLSPart1TradeoffCondition : Prop :=
  ∀ q : ℕ,
    3000 ≤ q →
      (Real.log ((llsTheorem11S1RadiusRoot q) ^ 2)) ^ 2 ≤
        Real.log 2 *
          (2 * llsTheorem11S1RadiusRoot q + 2 + 2 * Real.log ((llsTheorem11S1RadiusRoot q) ^ 2))

/-- The comparison upper bound after replacing the conductor by the full level. -/
noncomputable def llsPart1FullLevelUpperBound (q : ℕ) : ℝ :=
  let x := (llsTheorem11S1RadiusRoot q) ^ 2
  (2 * llsTheorem11S1RadiusRoot q + 2 + Real.log x) *
        (Real.log q / 2 + 2 / 5 - llsAuxiliaryTerm q) +
      (Real.log q - Real.log Real.pi) * Real.log x / 2 -
    11 / 4

/-- The intermediate upper expression on line 794 of the LLS v3 source. -/
noncomputable def llsPart1IntermediateUpperBound (q : ℕ) : ℝ :=
  let y := llsTheorem11S1RadiusRoot q
  y * (Real.log q + 4 / 5 - 2 * llsAuxiliaryTerm q) + Real.log (y ^ 2) * Real.log q + Real.log q -
    39 / 20

/-- The one-variable lower-minus-upper margin left after expanding the definition of `B(q)`. -/
noncomputable def llsPart1SeparationMargin (y : ℝ) : ℝ :=
  y * (6 / 5 - 2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass) -
        2 * Real.log (2 * Real.pi) * Real.log y +
      19 / 20 -
    2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass

/--
The coefficient condition removes all conductor dependence from the comparison upper bound.

This specializes `DirichletLFunction.conductor_primeFactor_tradeoff` using the exact logarithmic
level split and the
proved `ω ≤ log(q / conductor) / log 2` estimate.
-/
theorem llsTheorem11S1ComparisonUpperBound_le_fullLevel (htradeoff : LLSPart1TradeoffCondition)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : 3000 ≤ q) :
    llsTheorem11S1ComparisonUpperBound χ ≤ llsPart1FullLevelUpperBound q := by
  have homega :=
    AnalyticNumberTheory.DirichletLFunction.card_primeFactors_quotient_le_log_div_log_two
      χ
  rw [AnalyticNumberTheory.DirichletLFunction.log_quotient_eq_log_level_sub_log_conductor
      χ] at homega
  have hcore :=
    AnalyticNumberTheory.DirichletLFunction.conductor_primeFactor_tradeoff
      (Real.log_pos one_lt_two)
      (AnalyticNumberTheory.DirichletLFunction.log_conductor_le_log_level χ) homega
      (htradeoff q hq) (root := llsTheorem11S1RadiusRoot q) (logWeight :=
      Real.log ((llsTheorem11S1RadiusRoot q) ^ 2)) (offset := 2 / 5 - llsAuxiliaryTerm q) (piLog :=
      Real.log Real.pi)
  have hconductor : (χ.conductor : ℝ) ≠ 0 := by
    exact_mod_cast (AnalyticNumberTheory.DirichletLFunction.conductor_pos χ).ne'
  rw [llsTheorem11S1ComparisonUpperBound, llsTheorem11S1PrimitiveUpperBound,
    llsPart1FullLevelUpperBound, Real.log_div hconductor Real.pi_ne_zero] at ⊢
  nlinarith only [hcore]

/-- The square root parameter of the Part 1 radius is strictly greater than `8` for `q ≥ 3000`. -/
theorem eight_lt_llsTheorem11S1RadiusRoot {q : ℕ} (hq : 3000 ≤ q) :
    (8 : ℝ) < llsTheorem11S1RadiusRoot q := by
  exact
    (Analysis.eight_lt_log_level hq).trans_le
      (le_add_of_nonneg_right (llsCorrectionTerm_nonneg q))

/-- At the Part 1 radius, the inverse-square factor is uniformly bounded by `64 / 49`. -/
theorem llsPart1RadiusInverseSq_le_sixtyFour_div_fortyNine {q : ℕ} (hq : 3000 ≤ q) :
    (1 - 1 / llsTheorem11S1RadiusRoot q)⁻¹ ^ 2 ≤ (64 / 49 : ℝ) := by
  have hr : (8 : ℝ) ≤ llsTheorem11S1RadiusRoot q := (eight_lt_llsTheorem11S1RadiusRoot hq).le
  have hrpos : 0 < llsTheorem11S1RadiusRoot q := by linarith
  have hden : 0 < 1 - 1 / llsTheorem11S1RadiusRoot q := by
    rw [sub_pos, div_lt_one hrpos]
    linarith
  have hinv : 1 / llsTheorem11S1RadiusRoot q ≤ (1 / 8 : ℝ) := by
    apply (div_le_iff₀ hrpos).2
    calc
      (1 : ℝ) = (1 / 8) * 8 := by norm_num only
      _ ≤ (1 / 8) * llsTheorem11S1RadiusRoot q := mul_le_mul_of_nonneg_left hr (by norm_num only)
  have hden_lower : (7 / 8 : ℝ) ≤ 1 - 1 / llsTheorem11S1RadiusRoot q := by linarith
  have hsq : (7 / 8 : ℝ) ^ 2 ≤ (1 - 1 / llsTheorem11S1RadiusRoot q) ^ 2 := by
    nlinarith only [hden_lower, sq_nonneg ((1 - 1 / llsTheorem11S1RadiusRoot q) - 7 / 8)]
  have hden' : 0 < 1 - (llsTheorem11S1RadiusRoot q)⁻¹ := by simpa only [sub_pos, one_div] using hden
  have hsq' : (7 / 8 : ℝ) ^ 2 ≤ (1 - (llsTheorem11S1RadiusRoot q)⁻¹) ^ 2 := by
    simpa only [one_div] using hsq
  rw [inv_pow, one_div]
  rw [inv_eq_one_div]
  apply (div_le_iff₀ (sq_pos_of_pos hden')).2
  nlinarith only [hsq']

/-- The full-level expression is bounded by line 794 of the LLS v3 calculation. -/
theorem llsPart1FullLevelUpperBound_le_intermediate {q : ℕ} (hq : 3000 ≤ q) :
    llsPart1FullLevelUpperBound q ≤ llsPart1IntermediateUpperBound q := by
  have hy : 1 < llsTheorem11S1RadiusRoot q :=
    (eight_lt_llsTheorem11S1RadiusRoot hq).trans' (by norm_num only)
  have hlogX : 0 ≤ Real.log ((llsTheorem11S1RadiusRoot q) ^ 2) :=
    Real.log_nonneg (by nlinarith only [hy])
  have hlogPi : (4 / 5 : ℝ) < Real.log Real.pi := by
    have hlogThreePi :=
      Real.strictMonoOn_log (by norm_num only [Set.mem_Ioi]) Real.pi_pos Real.pi_gt_three
    exact (show (4 / 5 : ℝ) < Real.log 3 by linarith [Real.log_three_gt_d9]).trans hlogThreePi
  have haux := llsAuxiliaryTerm_nonneg q
  rw [llsPart1FullLevelUpperBound, llsPart1IntermediateUpperBound]
  nlinarith only [mul_nonneg hlogX (sub_nonneg.mpr hlogPi.le), mul_nonneg haux hlogX, hy, hlogX,
    hlogPi, haux]

/-- Line 795 of the LLS v3 source bounds the intermediate expression by `llsTheorem11S1UpperBound`.
-/
theorem llsPart1IntermediateUpperBound_le_upper {q : ℕ} (hq : 3000 ≤ q) :
    llsPart1IntermediateUpperBound q ≤ llsTheorem11S1UpperBound q := by
  have hlogQ : (8 : ℝ) < Real.log q := Analysis.eight_lt_log_level hq
  have hroot : Real.log q ≤ llsTheorem11S1RadiusRoot q :=
    le_add_of_nonneg_right (llsCorrectionTerm_nonneg q)
  have hratio :=
    Analysis.strictAntiOn_logLinearRatio.antitoneOn
      (by
        simp only [Set.mem_Ici]; exact hlogQ.le)
      (by
        simp only [Set.mem_Ici]; exact hlogQ.le.trans hroot)
      hroot
  have hmul := mul_le_mul_of_nonneg_right hratio (show 0 ≤ Real.log (q : ℝ) by linarith)
  have hratioQ :
    Analysis.logLinearRatio (Real.log q) * Real.log q =
      2 * Real.log (Real.log q) + 1 := by
    rw [Analysis.logLinearRatio]
    field_simp [hlogQ.ne']
  have hrootPos : 0 < llsTheorem11S1RadiusRoot q := by linarith
  have hleft :
    Analysis.logLinearRatio (llsTheorem11S1RadiusRoot q) * Real.log q =
      ((2 * Real.log (llsTheorem11S1RadiusRoot q) + 1) * Real.log q) /
        llsTheorem11S1RadiusRoot q := by
    rw [Analysis.logLinearRatio]
    ring
  rw [hleft, hratioQ] at hmul
  have hscaled := (div_le_iff₀ hrootPos).mp hmul
  rw [llsPart1IntermediateUpperBound, llsTheorem11S1UpperBound, Real.log_pow] at ⊢
  norm_num only [Nat.cast_ofNat]
  nlinarith only [hscaled]

/-- Expanding `B(q)` reduces lower-minus-upper separation to a function of the radius alone. -/
theorem llsPart1SeparationMargin_le_lower_sub_upper {q : ℕ} (hq : 3000 ≤ q) :
    llsPart1SeparationMargin (llsTheorem11S1RadiusRoot q) ≤
      llsTheorem11S1LowerBound q - llsTheorem11S1UpperBound q := by
  have hy : 0 < llsTheorem11S1RadiusRoot q :=
    (eight_lt_llsTheorem11S1RadiusRoot hq).trans' (by norm_num only)
  have hcorrection :
    2 * Real.log (Real.log q) + 3 +
          2 * q.primeFactors.card * (Real.log (Real.log q)) ^ 2 / Real.log q -
        2 * llsAuxiliaryTerm q ≤
      llsCorrectionTerm q := by
    rw [llsCorrectionTerm]
    exact le_max_right 0 _
  have hscaled := mul_le_mul_of_nonneg_left hcorrection hy.le
  rw [llsTheorem11S1RadiusRoot] at hscaled
  rw [llsPart1SeparationMargin, llsTheorem11S1LowerBound, llsTheorem11S1UpperBound,
    llsTheorem11S1RadiusRoot, Real.log_pow] at ⊢
  norm_num only [Nat.cast_ofNat]
  nlinarith only [hscaled]

/--
The universal one-variable inequality remaining in the conductor tradeoff.

This statement is independent of characters and arithmetic data. The proof below controls the
derivative of its margin and uses four tangent-line certificates on `[12,16]`.
-/
def LLSTradeoffRadiusInequality : Prop :=
  ∀ y : ℝ, 8 ≤ y → (Real.log (y ^ 2)) ^ 2 ≤ Real.log 2 * (2 * y + 2 + 2 * Real.log (y ^ 2))

/--
The margin of the universal conductor-tradeoff inequality after replacing `log(y²)` by `2 log y`.

Nonnegativity of this function on `[8, ∞)` is equivalent to `LLSTradeoffRadiusInequality`.
-/
noncomputable def llsTradeoffMargin (y : ℝ) : ℝ :=
  Real.log 2 * (2 * y + 2 + 4 * Real.log y) - 4 * (Real.log y) ^ 2

/-- The radius inequality at a positive input is exactly nonnegativity of the tradeoff margin. -/
theorem tradeoff_radius_inequality_iff_margin_nonneg {y : ℝ} (hy : 0 < y) :
    (Real.log (y ^ 2)) ^ 2 ≤ Real.log 2 * (2 * y + 2 + 2 * Real.log (y ^ 2)) ↔
      0 ≤ llsTradeoffMargin y := by
  rw [Analysis.log_sq_eq_two_mul_log hy, llsTradeoffMargin]
  constructor <;> intro h <;> nlinarith only [h]

/-- The universal radius statement is equivalent to margin nonnegativity on `[8, ∞)`. -/
theorem tradeoffRadiusInequality_iff_margin :
    LLSTradeoffRadiusInequality ↔ ∀ y : ℝ, 8 ≤ y → 0 ≤ llsTradeoffMargin y := by
  constructor
  · intro h y hy
    exact (tradeoff_radius_inequality_iff_margin_nonneg (by linarith)).mp (h y hy)
  · intro h y hy
    exact (tradeoff_radius_inequality_iff_margin_nonneg (by linarith)).mpr (h y hy)

/-- The numerator controlling the sign of the derivative of `llsTradeoffMargin`. -/
noncomputable def llsTradeoffDerivNumerator (y : ℝ) : ℝ :=
  2 * Real.log 2 * y + 4 * Real.log 2 - 8 * Real.log y

/-- The derivative of the tradeoff margin at a positive input. -/
theorem hasDerivAt_llsTradeoffMargin {y : ℝ} (hy : 0 < y) :
    HasDerivAt llsTradeoffMargin (llsTradeoffDerivNumerator y / y) y := by
  unfold llsTradeoffMargin llsTradeoffDerivNumerator
  have hraw :=
    (((((hasDerivAt_id y).const_mul 2).add_const 2).add
              (Real.hasDerivAt_log hy.ne' |>.const_mul 4)).const_mul
          (Real.log 2)).sub
      ((Real.hasDerivAt_log hy.ne').pow 2 |>.const_mul 4)
  apply (hraw.congr_of_eventuallyEq ?_).congr_deriv
  · field_simp [hy.ne']
    ring
  · filter_upwards with z
    simp only [Pi.add_apply, Pi.sub_apply, Pi.pow_apply, id_eq]

/-- The derivative of the numerator controlling the margin derivative. -/
theorem hasDerivAt_llsTradeoffDerivNumerator {y : ℝ} (hy : 0 < y) :
    HasDerivAt llsTradeoffDerivNumerator (2 * Real.log 2 - 8 / y) y := by
  unfold llsTradeoffDerivNumerator
  have hraw :=
    (((hasDerivAt_id y).const_mul (2 * Real.log 2)).add_const (4 * Real.log 2)).sub
      (Real.hasDerivAt_log hy.ne' |>.const_mul 8)
  apply (hraw.congr_of_eventuallyEq ?_).congr_deriv
  · rw [div_eq_mul_inv]
    ring
  · filter_upwards with z
    simp only [Pi.sub_apply, id_eq]

/-- The derivative numerator is strictly increasing on `[8, ∞)`. -/
theorem strictMonoOn_llsTradeoffDerivNumerator :
    StrictMonoOn llsTradeoffDerivNumerator (Set.Ici 8) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 8)
  · intro y hy
    simp only [Set.mem_Ici] at hy
    exact (hasDerivAt_llsTradeoffDerivNumerator (by linarith)).continuousAt.continuousWithinAt
  · intro y hy
    simp only [interior_Ici, Set.mem_Ioi] at hy
    rw [(hasDerivAt_llsTradeoffDerivNumerator (by linarith)).deriv]
    have hdiv : 8 / y ≤ (1 : ℝ) := by
      apply (div_le_one (by linarith)).mpr
      exact hy.le
    have hlog : (1 : ℝ) < 2 * Real.log 2 := by linarith only [Real.log_two_gt_d9]
    linarith

/-- The derivative numerator is negative at `12`. -/
theorem llsTradeoffDerivNumerator_twelve_neg : llsTradeoffDerivNumerator 12 < 0 := by
  have hlogTwo := Real.log_two_lt_d9
  have hlogThree := Real.log_three_gt_d9
  rw [llsTradeoffDerivNumerator, show (12 : ℝ) = 3 * 4 by norm_num only,
    Real.log_mul (by norm_num only) (by norm_num only), Real.log_four_eq]
  linarith only [hlogTwo, hlogThree]

/-- The derivative numerator is positive at `16`. -/
theorem llsTradeoffDerivNumerator_sixteen_pos : 0 < llsTradeoffDerivNumerator 16 := by
  rw [llsTradeoffDerivNumerator, show (16 : ℝ) = 2 ^ 4 by norm_num only, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  nlinarith only [Real.log_pos one_lt_two]

/-- The tradeoff margin is strictly decreasing on `[8, 12]`. -/
theorem strictAntiOn_llsTradeoffMargin_Icc : StrictAntiOn llsTradeoffMargin (Set.Icc 8 12) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc 8 12)
  · intro y hy
    simp only [Set.mem_Icc] at hy
    exact (hasDerivAt_llsTradeoffMargin (by linarith)).continuousAt.continuousWithinAt
  · intro y hy
    simp only [interior_Icc, Set.mem_Ioo] at hy
    rw [(hasDerivAt_llsTradeoffMargin (by linarith)).deriv]
    have hnum : llsTradeoffDerivNumerator y < 0 :=
      (strictMonoOn_llsTradeoffDerivNumerator
            (by
              simp only [Set.mem_Ici]; linarith)
            (by
              simp only [Set.mem_Ici]; norm_num only)
            hy.2).trans
        llsTradeoffDerivNumerator_twelve_neg
    exact div_neg_of_neg_of_pos hnum (by linarith)

/-- The tradeoff margin is strictly increasing on `[16, ∞)`. -/
theorem strictMonoOn_llsTradeoffMargin_Ici : StrictMonoOn llsTradeoffMargin (Set.Ici 16) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 16)
  · intro y hy
    simp only [Set.mem_Ici] at hy
    exact (hasDerivAt_llsTradeoffMargin (by linarith)).continuousAt.continuousWithinAt
  · intro y hy
    simp only [interior_Ici, Set.mem_Ioi] at hy
    rw [(hasDerivAt_llsTradeoffMargin (by linarith)).deriv]
    have hnum : 0 < llsTradeoffDerivNumerator y :=
      llsTradeoffDerivNumerator_sixteen_pos.trans
        (strictMonoOn_llsTradeoffDerivNumerator
          (by
            simp only [Set.mem_Ici]; norm_num only)
          (by
            simp only [Set.mem_Ici]; linarith)
          hy)
    exact div_pos hnum (by linarith)

/-- The compact-interval margin condition used to prove the universal radius inequality. -/
def LLSTradeoffCoreInterval : Prop :=
  ∀ y : ℝ, y ∈ Set.Icc 12 16 → 0 ≤ llsTradeoffMargin y

/-- Nonnegativity on `[12, 16]` implies the universal tradeoff radius inequality. -/
theorem tradeoffRadiusInequality_of_coreInterval (hcore : LLSTradeoffCoreInterval) :
    LLSTradeoffRadiusInequality := by
  rw [tradeoffRadiusInequality_iff_margin]
  intro y hy
  by_cases hy12 : y ≤ 12
  · exact
      (hcore 12
            (by
              simp only [Set.mem_Icc]; constructor <;> norm_num only)).trans
        (strictAntiOn_llsTradeoffMargin_Icc.antitoneOn
          (by
            simp only [Set.mem_Icc]; exact ⟨hy, hy12⟩)
          (by
            simp only [Set.mem_Icc]; constructor <;> norm_num only)
          hy12)
  by_cases hy16 : y ≤ 16
  · exact
      hcore y
        (by
          simp only [Set.mem_Icc]; constructor <;> linarith)
  · exact
      (hcore 16
            (by
              simp only [Set.mem_Icc]; constructor <;> norm_num only)).trans
        (strictMonoOn_llsTradeoffMargin_Ici.monotoneOn
          (by
            simp only [Set.mem_Ici]; norm_num only)
          (by
            simp only [Set.mem_Ici]; linarith)
          (by linarith))

/--
A compact-interval certificate for nonnegativity of the tradeoff margin.

For `a ≤ y`, an upper certificate `log y ≤ U` is enough because the quadratic logarithmic part
`4 log 2 * t - 4t²` is decreasing once `log 2 ≤ 2t`.  The last hypothesis is then a single
endpoint-style arithmetic certificate independent of `y`.
-/
theorem llsTradeoffMargin_nonneg_of_log_upper {a y U : ℝ} (hay : a ≤ y) (hy : 12 ≤ y)
    (hlogUpper : Real.log y ≤ U) (hcertificate : 0 ≤ Real.log 2 * (2 * a + 2 + 4 * U) - 4 * U ^ 2) :
    0 ≤ llsTradeoffMargin y := by
  have hlogTwo : Real.log 2 ≤ 2 * Real.log y := Analysis.log_two_le_two_mul_log hy
  have hfactorLeft : 0 ≤ U - Real.log y := sub_nonneg.mpr hlogUpper
  have hfactorRight : 0 ≤ U + Real.log y - Real.log 2 := by linarith
  have hquadratic :
    4 * Real.log 2 * U - 4 * U ^ 2 ≤ 4 * Real.log 2 * Real.log y - 4 * (Real.log y) ^ 2 := by
    nlinarith only [mul_nonneg hfactorLeft hfactorRight]
  rw [llsTradeoffMargin]
  have hlogTwoPos : 0 < Real.log 2 := Real.log_pos one_lt_two
  nlinarith only [hcertificate, hquadratic, mul_nonneg hlogTwoPos.le (sub_nonneg.mpr hay)]

/--
A tangent-line certificate for tradeoff-margin nonnegativity at a point `y ≥ a ≥ 12`.

Compared with a constant logarithm upper bound, this preserves the correlation between `y` and
`log y`.  The remaining certificate is a quadratic inequality in `y` after choosing a rational
upper bound `L` for `log a`.
-/
theorem llsTradeoffMargin_nonneg_of_log_tangent {a y L : ℝ} (ha : 12 ≤ a) (hay : a ≤ y)
    (hlogBase : Real.log a ≤ L)
    (hcertificate :
      0 ≤ Real.log 2 * (2 * y + 2 + 4 * (L + (y - a) / a)) - 4 * (L + (y - a) / a) ^ 2) :
    0 ≤ llsTradeoffMargin y := by
  have hapos : 0 < a := by linarith
  have hypos : 0 < y := hapos.trans_le hay
  have hshift : Real.log a + (y - a) / a ≤ L + (y - a) / a := by linarith
  have hlogUpper : Real.log y ≤ L + (y - a) / a :=
    (Analysis.log_le_log_add_sub_div hapos hypos).trans hshift
  exact llsTradeoffMargin_nonneg_of_log_upper le_rfl (ha.trans hay) hlogUpper hcertificate

/-- The tradeoff margin is nonnegative on the first unit subinterval `[12, 13]`. -/
theorem llsTradeoffMargin_nonneg_on_twelve_thirteen :
    ∀ y ∈ Set.Icc (12 : ℝ) 13, 0 ≤ llsTradeoffMargin y := by
  intro y hy
  apply
    llsTradeoffMargin_nonneg_of_log_tangent (a := 12) (L := 248491 / 100000) (by norm_num only) hy.1
      Analysis.log_twelve_le
  have hlogTwo := Real.log_two_gt_d9
  have hinterval : 0 ≤ (y - 12) * (13 - y) := mul_nonneg (sub_nonneg.mpr hy.1) (sub_nonneg.mpr hy.2)
  have hcoefficient : 0 ≤ 2 * y + 2 + 4 * ((248491 : ℝ) / 100000 + (y - 12) / 12) := by
    norm_num only at ⊢
    linarith only [hy.1]
  have hmul := mul_le_mul_of_nonneg_right hlogTwo.le hcoefficient
  norm_num only at hlogTwo hmul ⊢
  nlinarith only [hinterval, hmul]

/-- The tradeoff margin is nonnegative on the second unit subinterval `[13, 14]`. -/
theorem llsTradeoffMargin_nonneg_on_thirteen_fourteen :
    ∀ y ∈ Set.Icc (13 : ℝ) 14, 0 ≤ llsTradeoffMargin y := by
  intro y hy
  apply
    llsTradeoffMargin_nonneg_of_log_tangent (a := 13) (L := 256825 / 100000) (by norm_num only) hy.1
      Analysis.log_thirteen_le
  have hlogTwo := Real.log_two_gt_d9
  have hinterval : 0 ≤ (y - 13) * (14 - y) := mul_nonneg (sub_nonneg.mpr hy.1) (sub_nonneg.mpr hy.2)
  have hcoefficient : 0 ≤ 2 * y + 2 + 4 * ((256825 : ℝ) / 100000 + (y - 13) / 13) := by
    norm_num only at ⊢
    linarith only [hy.1]
  have hmul := mul_le_mul_of_nonneg_right hlogTwo.le hcoefficient
  norm_num only at hlogTwo hmul ⊢
  nlinarith only [hinterval, hmul]

/-- The tradeoff margin is nonnegative on the third unit subinterval `[14, 15]`. -/
theorem llsTradeoffMargin_nonneg_on_fourteen_fifteen :
    ∀ y ∈ Set.Icc (14 : ℝ) 15, 0 ≤ llsTradeoffMargin y := by
  intro y hy
  apply
    llsTradeoffMargin_nonneg_of_log_tangent (a := 14) (L := 264518 / 100000) (by norm_num only) hy.1
      Analysis.log_fourteen_le
  have hlogTwo := Real.log_two_gt_d9
  have hinterval : 0 ≤ (y - 14) * (15 - y) := mul_nonneg (sub_nonneg.mpr hy.1) (sub_nonneg.mpr hy.2)
  have hcoefficient : 0 ≤ 2 * y + 2 + 4 * ((264518 : ℝ) / 100000 + (y - 14) / 14) := by
    norm_num only at ⊢
    linarith only [hy.1]
  have hmul := mul_le_mul_of_nonneg_right hlogTwo.le hcoefficient
  norm_num only at hlogTwo hmul ⊢
  nlinarith only [hinterval, hmul]

/-- The tradeoff margin is nonnegative on the fourth unit subinterval `[15, 16]`. -/
theorem llsTradeoffMargin_nonneg_on_fifteen_sixteen :
    ∀ y ∈ Set.Icc (15 : ℝ) 16, 0 ≤ llsTradeoffMargin y := by
  intro y hy
  apply
    llsTradeoffMargin_nonneg_of_log_tangent (a := 15) (L := 271661 / 100000) (by norm_num only) hy.1
      Analysis.log_fifteen_le
  have hlogTwo := Real.log_two_gt_d9
  have hinterval : 0 ≤ (y - 15) * (16 - y) := mul_nonneg (sub_nonneg.mpr hy.1) (sub_nonneg.mpr hy.2)
  have hcoefficient : 0 ≤ 2 * y + 2 + 4 * ((271661 : ℝ) / 100000 + (y - 15) / 15) := by
    norm_num only at ⊢
    linarith only [hy.1]
  have hmul := mul_le_mul_of_nonneg_right hlogTwo.le hcoefficient
  norm_num only at hlogTwo hmul ⊢
  nlinarith only [hinterval, hmul]

/-- The four tangent certificates prove the complete compact-interval obligation. -/
theorem llsTradeoffCoreInterval : LLSTradeoffCoreInterval := by
  intro y hy
  by_cases hy13 : y ≤ 13
  · exact llsTradeoffMargin_nonneg_on_twelve_thirteen y ⟨hy.1, hy13⟩
  by_cases hy14 : y ≤ 14
  · exact llsTradeoffMargin_nonneg_on_thirteen_fourteen y ⟨by linarith, hy14⟩
  by_cases hy15 : y ≤ 15
  · exact llsTradeoffMargin_nonneg_on_fourteen_fifteen y ⟨by linarith, hy15⟩
  exact llsTradeoffMargin_nonneg_on_fifteen_sixteen y ⟨by linarith, hy.2⟩

/-- The LLS radius inequality, discharged entirely by kernel-checked analytic certificates. -/
theorem llsTradeoffRadiusInequality : LLSTradeoffRadiusInequality :=
  tradeoffRadiusInequality_of_coreInterval llsTradeoffCoreInterval

/-- The universal radius inequality implies the Part 1 tradeoff condition. -/
theorem llsPart1TradeoffCondition_of_radius_inequality (hradius : LLSTradeoffRadiusInequality) :
    LLSPart1TradeoffCondition := by
  intro q hq
  exact hradius (llsTheorem11S1RadiusRoot q) (eight_lt_llsTheorem11S1RadiusRoot hq).le

/-- The conductor tradeoff condition required by LLS Part 1. -/
theorem llsPart1TradeoffCondition : LLSPart1TradeoffCondition :=
  llsPart1TradeoffCondition_of_radius_inequality llsTradeoffRadiusInequality

/-- The complete algebraic and numerical comparison-upper simplification for LLS Part 1. -/
theorem llsPart1ComparisonUpperSimplification : llsTheorem11S1ComparisonUpperSimplification := by
  intro q _ χ hq
  exact
    (llsTheorem11S1ComparisonUpperBound_le_fullLevel llsPart1TradeoffCondition χ hq).trans
      ((llsPart1FullLevelUpperBound_le_intermediate hq).trans
        (llsPart1IntermediateUpperBound_le_upper hq))

/-- The derivative of the one-variable separation margin at a positive input. -/
theorem hasDerivAt_llsPart1SeparationMargin {y : ℝ} (hy : 0 < y) :
    HasDerivAt llsPart1SeparationMargin
      (6 / 5 - 2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass -
        2 * Real.log (2 * Real.pi) / y)
      y := by
  unfold llsPart1SeparationMargin
  have hraw :=
    ((hasDerivAt_id y).mul_const
          (6 / 5 - 2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass)).sub
      (Real.hasDerivAt_log hy.ne' |>.const_mul (2 * Real.log (2 * Real.pi)))
  apply
    ((hraw.add_const (19 / 20)).sub_const
        (2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass)).congr_deriv
  rw [div_eq_mul_inv]
  ring

/-- The separation margin is strictly increasing on `[8, ∞)`. -/
theorem strictMonoOn_llsPart1SeparationMargin :
    StrictMonoOn llsPart1SeparationMargin (Set.Ici 8) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 8)
  · intro y hy
    simp only [Set.mem_Ici] at hy
    exact (hasDerivAt_llsPart1SeparationMargin (by linarith)).continuousAt.continuousWithinAt
  · intro y hy
    simp only [interior_Ici, Set.mem_Ioi] at hy
    rw [(hasDerivAt_llsPart1SeparationMargin (by linarith)).deriv]
    have hratio : 2 * Real.log (2 * Real.pi) / y < (1 / 2 : ℝ) := by
      rw [div_lt_iff₀ (by linarith)]
      nlinarith only [hy, Analysis.log_two_mul_pi_lt]
    linarith only [hratio,
      AnalyticNumberTheory.RiemannXi.riemannZeroMass_lt_three_twentieths]

/-- The one-variable separation margin is positive at its left endpoint. -/
theorem llsPart1SeparationMargin_eight_pos : 0 < llsPart1SeparationMargin 8 := by
  have hlogTwoPos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogTwoUpper := Real.log_two_lt_d9
  have hlogTwoPiPos : 0 < Real.log (2 * Real.pi) := by
    apply Real.log_pos
    linarith only [Real.pi_gt_three]
  have hproductStep : Real.log (2 * Real.pi) * Real.log 2 < (1839 / 1000 : ℝ) * Real.log 2 := by
    exact mul_lt_mul_of_pos_right Analysis.log_two_mul_pi_lt hlogTwoPos
  have hproduct :
    Real.log (2 * Real.pi) * Real.log 2 < (1839 / 1000 : ℝ) * (6931471808 / 10000000000 : ℝ) := by
    nlinarith only [hproductStep, hlogTwoUpper,
      mul_pos (show (0 : ℝ) < 1839 / 1000 by norm_num only) (sub_pos.mpr hlogTwoUpper)]
  rw [llsPart1SeparationMargin, show (8 : ℝ) = 2 ^ 3 by norm_num only, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  nlinarith only [hproduct,
    AnalyticNumberTheory.RiemannXi.riemannZeroMass_lt_three_twentieths]

/-- The separation margin is positive throughout the radius range used in LLS Part 1. -/
theorem llsPart1SeparationMargin_pos {y : ℝ} (hy : 8 ≤ y) : 0 < llsPart1SeparationMargin y :=
  llsPart1SeparationMargin_eight_pos.trans_le
    (strictMonoOn_llsPart1SeparationMargin.monotoneOn
      (by
        simp only [Set.mem_Ici]; norm_num only)
      (by
        simp only [Set.mem_Ici]; exact hy)
      hy)

/-- The explicit Part 1 upper bound is strictly below its lower bound for every `q ≥ 3000`. -/
theorem llsPart1NumericalSeparation : llsTheorem11S1NumericalSeparation := by
  intro q hq
  have hmargin := llsPart1SeparationMargin_pos (eight_lt_llsTheorem11S1RadiusRoot hq).le
  have hlower := llsPart1SeparationMargin_le_lower_sub_upper hq
  linarith

/-- The logarithmic common-factor error from Lemma 3.1 is bounded by the error term in `lower2`. -/
theorem llsPart1CommonFactorError_le {q : ℕ} (hq : 3000 ≤ q) :
    (1 / 2 : ℝ) * q.primeFactors.card * (Real.log ((llsTheorem11S1RadiusRoot q) ^ 2)) ^ 2 ≤
      llsTheorem11S1RadiusRoot q *
        (2 * q.primeFactors.card * (Real.log (Real.log q)) ^ 2 / Real.log q) := by
  have hlogQ : (8 : ℝ) < Real.log q := Analysis.eight_lt_log_level hq
  have hroot : Real.log q ≤ llsTheorem11S1RadiusRoot q :=
    le_add_of_nonneg_right (llsCorrectionTerm_nonneg q)
  have hratio :=
    Analysis.strictAntiOn_logSquareRatio.antitoneOn
      (by
        simp only [Set.mem_Ici]; exact hlogQ.le)
      (by
        simp only [Set.mem_Ici]; exact hlogQ.le.trans hroot)
      hroot
  rw [Analysis.logSquareRatio, Analysis.logSquareRatio] at hratio
  have hscaled := (div_le_iff₀ (by linarith [hlogQ, hroot])).mp hratio
  have hbase :
    (1 / 2 : ℝ) * (Real.log ((llsTheorem11S1RadiusRoot q) ^ 2)) ^ 2 ≤
      llsTheorem11S1RadiusRoot q * (2 * (Real.log (Real.log q)) ^ 2 / Real.log q) := by
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    ring_nf at hscaled ⊢
    linarith only [hscaled]
  calc
    (1 / 2 : ℝ) * q.primeFactors.card * (Real.log ((llsTheorem11S1RadiusRoot q) ^ 2)) ^ 2 =
        q.primeFactors.card * ((1 / 2 : ℝ) * (Real.log ((llsTheorem11S1RadiusRoot q) ^ 2)) ^ 2) :=
      by ring
    _ ≤
        q.primeFactors.card *
          (llsTheorem11S1RadiusRoot q * (2 * (Real.log (Real.log q)) ^ 2 / Real.log q)) :=
      mul_le_mul_of_nonneg_left hbase (Nat.cast_nonneg _)
    _ =
        llsTheorem11S1RadiusRoot q *
          (2 * q.primeFactors.card * (Real.log (Real.log q)) ^ 2 / Real.log q) :=
      by ring

/-- LLS Lemma 2.1 implies the complete weighted lower-bound responsibility in Part 1. -/
theorem llsPart1WeightedLowerBounds_of_riemann (h21 : LLSRiemannWeightedLowerBound) :
    llsTheorem11S1WeightedLowerBounds := by
  intro q _ χ hq hχ hsmall
  have hraw := llsPart1WeightedRawLower_of_riemann h21 χ hq hχ hsmall
  have herror := llsPart1CommonFactorError_le hq
  rw [llsTheorem11S1LowerBound]
  linarith only [hraw, herror]

/-- The two remaining analytic bounds imply LLS Theorem 1.1 Part 1. -/
theorem llsTheorem11S1Character_of_analytic_bounds (hlower : llsTheorem11S1WeightedLowerBounds)
    (hprimitive : llsTheorem11S1PrimitiveUpperBounds) : llsTheorem11S1Character :=
  llsTheorem11S1Character_of_staged_bounds hlower hprimitive llsPart1ComparisonUpperSimplification
    llsPart1NumericalSeparation

/-- The Riemann lower bound and primitive-character upper bound imply LLS Part 1. -/
theorem llsTheorem11S1Character_of_riemann_and_primitive (h21 : LLSRiemannWeightedLowerBound)
    (hprimitive : llsTheorem11S1PrimitiveUpperBounds) : llsTheorem11S1Character :=
  llsTheorem11S1Character_of_analytic_bounds (llsPart1WeightedLowerBounds_of_riemann h21) hprimitive

end PseudoPrime.LLS
