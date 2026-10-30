/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.MellinWeights

/-! # Mellin transforms and inversions of arbitrary logarithmic powers on (0,1] -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The n-th logarithmic weight on (0,1], obtained by n multiplications by -log u.
The zeroth weight is the indicator and higher weights equal (-log u)^n there.
Its transform and inverse powers provide the rational-pole kernel inversion base. -/
noncomputable def mellinLogPowerWeight : ℕ → ℝ → ℂ
  | 0 => mellinWeightZero
  | n + 1 => fun t ↦ -(Real.log t • mellinLogPowerWeight n t)

/-- Every logarithmic power weight is locally integrable on the positive half-line.
Inductively multiply the previous weight by the continuous logarithm and negate.
This supplies the local hypothesis for Mellin differentiation. -/
theorem locallyIntegrableOn_logPowerWeight (n : ℕ) :
    MeasureTheory.LocallyIntegrableOn (mellinLogPowerWeight n) (Set.Ioi 0) := by
  induction n with
  | zero => exact locallyIntegrableOn_mellinWeightZero
  | succ n ih =>
    exact
      (ih.continuousOn_smul isOpen_Ioi.isLocallyClosed
          (Real.continuousOn_log.mono (fun _ ht ↦ ne_of_gt ht))).neg

/-- For every n and real a, the logarithmic weight is O(t^(-a)) at infinity.
The base vanishes beyond one; logarithm multiplication preserves arbitrary polynomial
decay after increasing the auxiliary exponent. Mellin differentiation uses this bound. -/
theorem isBigO_top_logPowerWeight (n : ℕ) (a : ℝ) :
    Asymptotics.IsBigO Filter.atTop (mellinLogPowerWeight n) (fun t : ℝ ↦ t ^ (-a)) := by
  induction n generalizing a with
  | zero => exact isBigO_atTop_mellinWeightZero a
  | succ n ih =>
    exact (isBigO_rpow_top_log_smul (by linarith only : a < a + 1) (ih (a + 1))).neg_left

/-- For every n and b>0, the logarithmic weight is O(t^(-b)) near zero from the right.
The indicator is bounded by the negative power; each logarithm consumes half the
available exponent. This gives Mellin convergence on every positive real-part line. -/
theorem isBigO_zero_logPowerWeight (n : ℕ) {b : ℝ} (hb : 0 < b) :
    Asymptotics.IsBigO (nhdsWithin 0 (Set.Ioi 0)) (mellinLogPowerWeight n)
      (fun t : ℝ ↦ t ^ (-b)) := by
  induction n generalizing b with
  | zero =>
    apply Asymptotics.IsBigO.of_bound'
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num only)] with t ht
    have hw : mellinLogPowerWeight 0 t = 1 :=
      Set.indicator_of_mem (show t ∈ Set.Ioc (0 : ℝ) 1 from ⟨ht.1, ht.2.le⟩) (fun _ : ℝ ↦ (1 : ℂ))
    rw [hw, norm_one, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos ht.1 _)]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht.1 ht.2.le (neg_nonpos.mpr hb.le)
  | succ n ih =>
    exact
      (isBigO_rpow_zero_log_smul (by linarith only [hb] : b / 2 < b)
          (ih (by linarith only [hb] : 0 < b / 2))).neg_left

/-- Away from zero, n!/z^(n+1) has derivative -(n+1)!/z^(n+2).
Differentiate the reciprocal power and cancel equal nonzero powers explicitly.
This identifies the next logarithmic weight through Mellin differentiation. -/
theorem hasDerivAt_factorial_div_pow (n : ℕ) {s : ℂ} (hs : s ≠ 0) :
    HasDerivAt (fun z : ℂ ↦ (n.factorial : ℂ) / z ^ (n + 1))
      (-((n + 1).factorial : ℂ) / s ^ (n + 2)) s := by
  have hd :=
    (((hasDerivAt_id s).pow (n + 1)).inv (pow_ne_zero (n + 1) hs)).const_mul (n.factorial : ℂ)
  simp only [Pi.inv_apply, Pi.pow_apply, id_eq] at hd
  have hv :
    (n.factorial : ℂ) * (-(↑(n + 1) * s ^ (n + 1 - 1) * 1) / (s ^ (n + 1)) ^ 2) =
      -((n + 1).factorial : ℂ) / s ^ (n + 2) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    simp only [Nat.add_sub_cancel, mul_one]
    rw [← mul_div_assoc]
    apply (div_eq_div_iff (pow_ne_zero 2 (pow_ne_zero (n + 1) hs)) (pow_ne_zero (n + 2) hs)).mpr
    rw [← pow_mul, show (n + 1) * 2 = n + (n + 2) by ring, pow_add]
    ring
  rw [hv] at hd
  simpa only [div_eq_mul_inv] using hd

/-- For Re(s)>0, the n-th logarithmic weight is Mellin-convergent with transform
n!/s^(n+1). Induct using local integrability, endpoint power bounds and the derivative
of the previous transform. This generalizes the existing second-order inversion input. -/
theorem hasMellin_logPowerWeight (n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    HasMellin (mellinLogPowerWeight n) s ((n.factorial : ℂ) / s ^ (n + 1)) := by
  induction n generalizing s with
  | zero =>
    simpa only [mellinLogPowerWeight, mellinWeightZero, Nat.factorial_zero, Nat.cast_one, zero_add,
      pow_one] using hasMellin_one_Ioc hs
  | succ n
    ih =>
    obtain ⟨hconv, hd⟩ :=
      mellin_hasDerivAt_of_isBigO_rpow (locallyIntegrableOn_logPowerWeight n)
        (isBigO_top_logPowerWeight n (s.re + 1)) (by linarith only)
        (isBigO_zero_logPowerWeight n (by linarith only [hs] : 0 < s.re / 2))
        (by linarith only [hs])
    have hn : s ≠ 0 := fun h ↦ (by simpa only [h, Complex.zero_re] using hs : (0 : ℝ) < 0).false
    have he :
      ∀ᶠ z in nhds s, mellin (mellinLogPowerWeight n) z = (n.factorial : ℂ) / z ^ (n + 1) := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
      exact (ih hz).2
    have hv := hd.unique ((hasDerivAt_factorial_div_pow n hn).congr_of_eventuallyEq he)
    have hp :
      (fun t : ℝ ↦ (t : ℂ) ^ (s - 1) • mellinLogPowerWeight (n + 1) t) = fun t : ℝ ↦
        -((t : ℂ) ^ (s - 1) • (Real.log t • mellinLogPowerWeight n t)) := by
      funext t
      exact smul_neg _ _
    constructor
    · unfold MellinConvergent
      rw [hp]
      exact hconv.neg
    · unfold mellin
      rw [hp, MeasureTheory.integral_neg]
      change -mellin (fun t : ℝ ↦ Real.log t • mellinLogPowerWeight n t) s = _
      rw [hv, neg_div, neg_neg]

/-- At every real argument, the logarithmic weight is (-log u)^n times the base
indicator. Induction and scalar associativity prove the identity, including totalized
values outside the positive support. It supplies the real closed profile formula. -/
theorem logPowerWeight_eq_smul (n : ℕ) (u : ℝ) :
    mellinLogPowerWeight n u = (-Real.log u) ^ n • mellinWeightZero u := by
  induction n with
  | zero => exact (one_smul ℝ (mellinWeightZero u)).symm
  | succ n ih =>
    change -(Real.log u • mellinLogPowerWeight n u) = _
    rw [ih, ← neg_smul, smul_smul, pow_succ]
    congr 1
    exact mul_comm _ _

/-- For n>=1 and u>0, the logarithmic weight is the real cast of
(-log(min(u,1)))^n. Split at one; the upper branch vanishes because the power is
positive. The formula exposes continuity across the cutoff for Mellin inversion. -/
theorem logPowerWeight_eq_log_min {n : ℕ} (hn : 1 ≤ n) {u : ℝ} (hu : 0 < u) :
    mellinLogPowerWeight n u = (((-Real.log (min u 1)) ^ n : ℝ) : ℂ) := by
  rw [logPowerWeight_eq_smul, mellinWeightZero]
  by_cases h1 : u ≤ 1
  · rw [Set.indicator_of_mem (show u ∈ Set.Ioc (0 : ℝ) 1 from ⟨hu, h1⟩), min_eq_left h1,
      Complex.real_smul, mul_one]
  · rw [Set.indicator_of_notMem (fun h ↦ h1 h.2), smul_zero, min_eq_right (le_of_not_ge h1),
      Real.log_one, neg_zero, zero_pow (Nat.ne_zero_of_lt hn), Complex.ofReal_zero]

/-- For n>=1, the logarithmic weight is continuous at each positive argument.
Use the log-min formula on a positive neighborhood and continuity of min, log and
powers. This includes the upper support endpoint and enables pointwise inversion. -/
theorem continuousAt_logPowerWeight {n : ℕ} (hn : 1 ≤ n) {u : ℝ} (hu : 0 < u) :
    ContinuousAt (mellinLogPowerWeight n) u := by
  have hc : ContinuousAt (fun t : ℝ ↦ (((-Real.log (min t 1)) ^ n : ℝ) : ℂ)) u :=
    Complex.continuous_ofReal.continuousAt.comp
      (((continuous_id.min continuous_const).continuousAt.log
            (ne_of_gt (lt_min hu (by norm_num only)))).neg.pow
        n)
  have he : ∀ᶠ t : ℝ in nhds u, 0 < t := isOpen_Ioi.mem_nhds hu
  exact hc.congr_of_eventuallyEq (he.mono fun _ ht ↦ logPowerWeight_eq_log_min hn ht)

/-- For n>=1 and sigma>0, n!/(sigma+it)^(n+1) is integrable in t.
Factor off the existing integrable reciprocal square and bound the remaining
reciprocal power by sigma^(-(n-1)). This verifies absolute vertical integrability. -/
theorem integrable_factorial_div_pow {n : ℕ} (hn : 1 ≤ n) {σ : ℝ} (hσ : 0 < σ) :
    MeasureTheory.Integrable
      (fun y : ℝ ↦ (n.factorial : ℂ) / ((σ : ℂ) + y * Complex.I) ^ (n + 1)) := by
  have hne := ne_zero_add_mul_I_of_re_ne_zero hσ.ne'
  have hc : Continuous (fun y : ℝ ↦ ((σ : ℂ) + y * Complex.I)⁻¹) :=
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).inv₀ hne
  have hb : ∀ y : ℝ, ‖((σ : ℂ) + y * Complex.I)⁻¹‖ ≤ σ⁻¹ := by
    intro y
    rw [norm_inv]
    apply inv_anti₀ hσ
    have h := Complex.re_le_norm ((σ : ℂ) + y * Complex.I)
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      mul_zero, zero_mul, sub_zero, add_zero] using h
  have hi :=
    (verticalIntegrable_mellinLogKernel hσ.ne').mul_bdd (hc.pow (n - 1)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y ↦ by
        simp only [Pi.pow_apply]
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hb y) (n - 1))
  have he : n + 1 = 2 + (n - 1) := by linarith only [Nat.sub_add_cancel hn]
  apply (hi.const_mul (n.factorial : ℂ)).congr
  exact
    Filter.Eventually.of_forall fun y ↦ by
      simp only [inv_pow, Pi.pow_apply, he, pow_add, div_eq_mul_inv, mul_inv]

/-- For n>=1, sigma>0 and u>0, Mellin inversion of n!/z^(n+1) returns the
logarithmic weight. Apply the existing inversion theorem using the proved transform,
vertical integrability and cutoff continuity. This is the base for orders four and six. -/
theorem mellinInv_logPowerWeight {n : ℕ} (hn : 1 ≤ n) {σ u : ℝ} (hσ : 0 < σ) (hu : 0 < u) :
    mellinInv σ (fun z : ℂ ↦ (n.factorial : ℂ) / z ^ (n + 1)) u = mellinLogPowerWeight n u := by
  have hp (y : ℝ) :
    mellin (mellinLogPowerWeight n) ((σ : ℂ) + y * Complex.I) =
      (n.factorial : ℂ) / ((σ : ℂ) + y * Complex.I) ^ (n + 1) :=
    (hasMellin_logPowerWeight n
        (by
          simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
            Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero] using hσ)).2
  have hi : Complex.VerticalIntegrable (mellin (mellinLogPowerWeight n)) σ := by
    exact
      (integrable_factorial_div_pow hn hσ).congr (Filter.Eventually.of_forall fun y ↦ (hp y).symm)
  have hm :=
    mellinInv_mellin_eq σ (mellinLogPowerWeight n) hu
      (hasMellin_logPowerWeight n (by simpa only [Complex.ofReal_re] using hσ)).1 hi
      (continuousAt_logPowerWeight hn hu)
  rw [← hm]
  unfold mellinInv
  congr 1
  apply MeasureTheory.integral_congr_ae
  exact
    Filter.Eventually.of_forall fun y ↦
      congrArg (fun z : ℂ ↦ (u : ℂ) ^ (-((σ : ℂ) + y * Complex.I)) • z) (hp y).symm

end PseudoPrime.Analysis
