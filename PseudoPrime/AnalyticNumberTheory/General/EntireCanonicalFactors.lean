/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.EntireZeroMass
public import PseudoPrime.AnalyticNumberTheory.General.CanonicalDecomposition
public import PseudoPrime.Analysis.ComplexLogPrimitive

/-!
# Canonical decomposition estimates for entire functions

The norm bounds, finite logarithmic derivative identities and canonical correction
estimates use only entirety, nonvanishing at the center and a growth bound.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- For entire F and a zero-free sphere, the analytic factor in its extended
canonical decomposition has the same norm as F on the sphere. Boundary divisors
vanish and interior canonical factors have norm one. -/
theorem norm_canonical_factor_eq_on_zero_free_sphere {F : ℂ → ℂ} (hF : Differentiable ℂ F) {R : ℝ}
    (hR : 0 < R) {g : ℂ → ℂ} (D : Complex.ECanonicalDecomp (F) g R)
    (hzf : ∀ ρ : ℂ, ‖ρ‖ = R → F ρ ≠ 0) {w : ℂ} (hw : ‖w‖ = R) : ‖g w‖ = ‖F w‖ := by
  have hdiff := hF
  have hanalyticSphere : AnalyticOnNhd ℂ (F) (Metric.sphere (0 : ℂ) R) := fun z _ ↦
    hdiff.analyticAt z
  have hwmem : w ∈ Metric.closedBall (0 : ℂ) R := by rw [Metric.mem_closedBall, dist_zero_right, hw]
  have horderAt : ∀ i : ℂ, F i ≠ 0 → meromorphicOrderAt (F) i = 0 := by
    intro i hine
    rw [(hdiff.analyticAt i).meromorphicOrderAt_eq, analyticOrderAt_eq_zero.mpr (Or.inr hine)]
    rfl
  have horder := horderAt w (hzf w hw)
  have hlogeq := D.log_norm_eq hwmem horder hR
  have hspherezero :
    ∀ i : ℂ,
      ((MeromorphicOn.divisor (F) (Metric.sphere (0 : ℂ) R) i : ℤ) : ℝ) * Real.log ‖w - i‖ = 0 := by
    intro i
    by_cases hi : i ∈ Metric.sphere (0 : ℂ) R
    · have hine : ‖i‖ = R := by rwa [Metric.mem_sphere, dist_zero_right] at hi
      have hdiv0 : MeromorphicOn.divisor (F) (Metric.sphere (0 : ℂ) R) i = 0 := by
        rw [MeromorphicOn.divisor_apply hanalyticSphere.meromorphicOn hi, horderAt i (hzf i hine)]
        rfl
      simp only [hdiv0, Int.cast_zero, zero_mul]
    · have hdiv0 : MeromorphicOn.divisor (F) (Metric.sphere (0 : ℂ) R) i = 0 :=
        (MeromorphicOn.divisor (F) (Metric.sphere (0 : ℂ) R)).apply_eq_zero_of_notMem hi
      simp only [hdiv0, Int.cast_zero, zero_mul]
  have hballzero :
    ∀ i : ℂ,
      ((MeromorphicOn.divisor (F) (Metric.ball (0 : ℂ) R) i : ℤ) : ℝ) *
          Real.log ‖Complex.canonicalFactor R i w‖ =
        0 := by
    intro i
    by_cases hi0 : MeromorphicOn.divisor (F) (Metric.ball (0 : ℂ) R) i = 0
    · simp only [hi0, Int.cast_zero, zero_mul]
    · have hiball : i ∈ Metric.ball (0 : ℂ) R :=
        (MeromorphicOn.divisor (F) (Metric.ball (0 : ℂ) R)).supportWithinDomain hi0
      have hwsphere : w ∈ Metric.sphere (0 : ℂ) R := by
        rw [Metric.mem_sphere, dist_zero_right]
        exact hw
      rw [Complex.norm_canonicalFactor_eval_circle_eq_one hiball hwsphere, Real.log_one, mul_zero]
  rw [finsum_eq_zero_of_forall_eq_zero hballzero, finsum_eq_zero_of_forall_eq_zero hspherezero,
    sub_zero, zero_add] at hlogeq
  have hFw_ne := hzf w hw
  have hgw_ne := D.ne_zero w hwmem
  have hmtc_eq : meromorphicTrailingCoeffAt (F) w = F w :=
    (hdiff.analyticAt w).meromorphicTrailingCoeffAt_of_ne_zero hFw_ne
  rw [hmtc_eq] at hlogeq
  have :=
    Real.log_injOn_pos (Set.mem_Ioi.mpr (norm_pos_iff.mpr hgw_ne))
      (Set.mem_Ioi.mpr (norm_pos_iff.mpr hFw_ne)) hlogeq
  exact this

/-- For an entire function, a nonzero value has meromorphic order zero.
Convert to analytic order. This removes divisor terms at regular evaluation points. -/
theorem meromorphicOrderAt_eq_zero_of_entire_value_ne_zero {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {i : ℂ} (hi : F i ≠ 0) : meromorphicOrderAt (F) i = 0 := by
  have hdiff := hF
  rw [(hdiff.analyticAt i).meromorphicOrderAt_eq, analyticOrderAt_eq_zero.mpr (Or.inr hi)]
  rfl

/-- For entire F nonzero at zero and a positive radius with zero-free boundary,
the canonical analytic factor satisfies `norm (F 0) ≤ norm (g 0)`.
Interior divisor orders are nonnegative and the central canonical factors have norm
at least one. This gives the central lower bound used in logarithmic oscillation estimates. -/
theorem norm_canonical_factor_zero_ge {F : ℂ → ℂ} (h0 : F 0 ≠ 0) (hF : Differentiable ℂ F) {R : ℝ}
    (hR : 0 < R) {g : ℂ → ℂ} (D : Complex.ECanonicalDecomp (F) g R)
    (hzf : ∀ ρ : ℂ, ‖ρ‖ = R → F ρ ≠ 0) : ‖F 0‖ ≤ ‖g 0‖ := by
  have hdiff := hF
  have hanalyticBall : AnalyticOnNhd ℂ (F) (Metric.ball (0 : ℂ) R) := fun z _ ↦ hdiff.analyticAt z
  have hF0ne := h0
  have h0mem : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) R := by
    simp only [Metric.mem_closedBall, dist_self, hR.le]
  have horder0 := meromorphicOrderAt_eq_zero_of_entire_value_ne_zero hF hF0ne
  have hlogeq := D.log_norm_eq h0mem horder0 hR
  have hspherezero :
    ∀ i : ℂ,
      ((MeromorphicOn.divisor (F) (Metric.sphere (0 : ℂ) R) i : ℤ) : ℝ) * Real.log ‖(0 : ℂ) - i‖ =
        0 := by
    intro i
    by_cases hi : i ∈ Metric.sphere (0 : ℂ) R
    · have hine : ‖i‖ = R := by rwa [Metric.mem_sphere, dist_zero_right] at hi
      have hanalyticSphere : AnalyticOnNhd ℂ (F) (Metric.sphere (0 : ℂ) R) := fun z _ ↦
        hdiff.analyticAt z
      have hdiv0 : MeromorphicOn.divisor (F) (Metric.sphere (0 : ℂ) R) i = 0 := by
        rw [MeromorphicOn.divisor_apply hanalyticSphere.meromorphicOn hi,
          meromorphicOrderAt_eq_zero_of_entire_value_ne_zero hF (hzf i hine)]
        rfl
      simp only [hdiv0, Int.cast_zero, zero_mul]
    · have hdiv0 : MeromorphicOn.divisor (F) (Metric.sphere (0 : ℂ) R) i = 0 :=
        (MeromorphicOn.divisor (F) (Metric.sphere (0 : ℂ) R)).apply_eq_zero_of_notMem hi
      simp only [hdiv0, Int.cast_zero, zero_mul]
  have hballnonneg :
    ∀ i : ℂ,
      (0 : ℝ) ≤
        ((MeromorphicOn.divisor (F) (Metric.ball (0 : ℂ) R) i : ℤ) : ℝ) *
          Real.log ‖Complex.canonicalFactor R i 0‖ := by
    intro i
    by_cases hi0 : MeromorphicOn.divisor (F) (Metric.ball (0 : ℂ) R) i = 0
    · simp only [hi0, Int.cast_zero, zero_mul, Std.le_refl]
    · have hiball : i ∈ Metric.ball (0 : ℂ) R :=
        (MeromorphicOn.divisor (F) (Metric.ball (0 : ℂ) R)).supportWithinDomain hi0
      have hine0 : i ≠ 0 := by
        rintro rfl
        apply hi0
        rw [MeromorphicOn.divisor_apply hanalyticBall.meromorphicOn hiball, horder0]
        rfl
      have hnormlt : ‖i‖ < R := by rwa [Metric.mem_ball, dist_zero_right] at hiball
      have hnormeq : ‖Complex.canonicalFactor R i 0‖ = R / ‖i‖ := by
        rw [Complex.canonicalFactor_apply]
        simp only [mul_zero, sub_zero, zero_sub, norm_div, norm_mul, norm_neg, norm_pow]
        rw [Complex.norm_real, Real.norm_of_nonneg hR.le, sq, mul_div_mul_left R ‖i‖ hR.ne']
      have hge1 : (1 : ℝ) ≤ ‖Complex.canonicalFactor R i 0‖ := by
        rw [hnormeq, le_div_iff₀ (norm_pos_iff.mpr hine0)]
        simpa only [one_mul] using hnormlt.le
      have hlognn : (0 : ℝ) ≤ Real.log ‖Complex.canonicalFactor R i 0‖ := Real.log_nonneg hge1
      have hdivnn : (0 : ℝ) ≤ ((MeromorphicOn.divisor (F) (Metric.ball (0 : ℂ) R) i : ℤ) : ℝ) := by
        exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hanalyticBall i
      exact mul_nonneg hdivnn hlognn
  rw [finsum_eq_zero_of_forall_eq_zero hspherezero, sub_zero] at hlogeq
  have hballnn :
    (0 : ℝ) ≤
      ∑ᶠ i,
        ((MeromorphicOn.divisor (F) (Metric.ball (0 : ℂ) R) i : ℤ) : ℝ) *
          Real.log ‖Complex.canonicalFactor R i 0‖ :=
    finsum_nonneg hballnonneg
  have hmtc_eq : meromorphicTrailingCoeffAt (F) 0 = F 0 :=
    (hdiff.analyticAt 0).meromorphicTrailingCoeffAt_of_ne_zero hF0ne
  rw [hmtc_eq] at hlogeq
  have hg0_pos : (0 : ℝ) < ‖g 0‖ := norm_pos_iff.mpr (D.ne_zero 0 h0mem)
  have hF0_pos : (0 : ℝ) < ‖F 0‖ := norm_pos_iff.mpr hF0ne
  have hlog_le : Real.log ‖F 0‖ ≤ Real.log ‖g 0‖ := by
    rw [hlogeq]
    exact le_add_of_nonneg_left hballnn
  exact (Real.log_le_log_iff hF0_pos hg0_pos).mp hlog_le

/-- For entire F and a zero-free sphere, any boundary norm bound for F also
bounds its canonical analytic factor on the closed disk. Use boundary norm equality
and the maximum modulus principle. -/
theorem norm_canonical_factor_le_of_sphere_bound {F : ℂ → ℂ} (hF : Differentiable ℂ F) {R M : ℝ}
    (hR : 0 < R) {g : ℂ → ℂ} (D : Complex.ECanonicalDecomp F g R) (hzf : ∀ z : ℂ, ‖z‖ = R → F z ≠ 0)
    (hb : ∀ z : ℂ, ‖z‖ = R → ‖F z‖ ≤ M) {z : ℂ} (hz : z ∈ Metric.closedBall 0 R) : ‖g z‖ ≤ M := by
  have hc : closure (Metric.ball (0 : ℂ) R) = Metric.closedBall 0 R := closure_ball 0 hR.ne'
  have hd : DiffContOnCl ℂ g (Metric.ball 0 R) := by
    apply DifferentiableOn.diffContOnCl
    rw [hc]
    exact D.analyticOnNhd.differentiableOn
  have hf : frontier (Metric.ball (0 : ℂ) R) = Metric.sphere 0 R := frontier_ball 0 hR.ne'
  have hbound : ∀ w ∈ frontier (Metric.ball (0 : ℂ) R), ‖g w‖ ≤ M := by
    intro w hw
    rw [hf, Metric.mem_sphere, dist_zero_right] at hw
    rw [norm_canonical_factor_eq_on_zero_free_sphere hF hR D hzf hw]
    exact hb w hw
  exact Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hd hbound (hc ▸ hz)

/-- For entire F nonzero at zero and a zero-free sphere, an exponential boundary
bound controls the log-norm oscillation of its analytic factor from the center.
Combine the maximum modulus bound with the central norm lower bound. -/
theorem canonical_factor_log_oscillation_le {F : ℂ → ℂ} (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0)
    {R M : ℝ} (hR : 0 < R) {g : ℂ → ℂ} (D : Complex.ECanonicalDecomp F g R)
    (hzf : ∀ z : ℂ, ‖z‖ = R → F z ≠ 0) (hb : ∀ z : ℂ, ‖z‖ = R → ‖F z‖ ≤ Real.exp M) {z : ℂ}
    (hz : z ∈ Metric.closedBall 0 R) : Real.log ‖g z‖ - Real.log ‖g 0‖ ≤ M - Real.log ‖F 0‖ := by
  have hu := norm_canonical_factor_le_of_sphere_bound hF hR D hzf hb hz
  have hl := norm_canonical_factor_zero_ge h0 hF hR D hzf
  have hg0 : g 0 ≠ 0 := D.ne_zero 0 (Metric.mem_closedBall_self hR.le)
  have hlogu := Real.log_le_log (norm_pos_iff.mpr (D.ne_zero z hz)) hu
  rw [Real.log_exp] at hlogu
  have hlogl := Real.log_le_log (norm_pos_iff.mpr h0) hl
  linarith only [hlogu, hlogl]

/-- For an entire function nonzero at zero, a zero-free sphere of radius at least
one, and an exponential boundary bound, control the analytic factor's centered
logarithmic derivative in the half disk. Use a holomorphic logarithm,
Borel-Caratheodory, and a Cauchy derivative estimate. -/
theorem norm_centered_logDeriv_canonical_factor_le {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (h0 : F 0 ≠ 0) {R M : ℝ} (hR : 1 ≤ R) {g : ℂ → ℂ} (D : Complex.ECanonicalDecomp F g R)
    (hzf : ∀ z : ℂ, ‖z‖ = R → F z ≠ 0) (hb : ∀ z : ℂ, ‖z‖ = R → ‖F z‖ ≤ Real.exp M) {s : ℂ}
    (hs : ‖s‖ ≤ R / 2) :
    ‖logDeriv g s - logDeriv g 0‖ ≤ 192 * ‖s‖ * (M - Real.log ‖F 0‖ + 1) / R ^ 2 := by
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have ha : AnalyticOnNhd ℂ g (Metric.ball 0 R) := fun z hz ↦
    D.analyticOnNhd z (Metric.ball_subset_closedBall hz)
  have hn : ∀ z ∈ Metric.ball (0 : ℂ) R, g z ≠ 0 := fun z hz ↦
    D.ne_zero z (Metric.ball_subset_closedBall hz)
  obtain ⟨h, hh, hre⟩ := Analysis.exists_hasDerivAt_logDeriv_re_eq_log_norm hR0 ha hn
  have h0b : (0 : ℂ) ∈ Metric.ball 0 R := Metric.mem_ball_self hR0
  have hosc : ∀ z ∈ Metric.ball (0 : ℂ) R, (h z).re - (h 0).re ≤ M - Real.log ‖F 0‖ := by
    intro z hz
    rw [hre z hz, hre 0 h0b]
    exact canonical_factor_log_oscillation_le hF h0 hR0 D hzf hb (Metric.ball_subset_closedBall hz)
  have hnonneg : 0 ≤ M - Real.log ‖F 0‖ := by
    have hc := hosc 0 h0b
    rwa [sub_self] at hc
  let B := (h 0).re + (M - Real.log ‖F 0‖) + 1
  have hB0 : (h 0).re < B := by
    dsimp only [B]; linarith only [hnonneg]
  have hRe : ∀ z ∈ Metric.ball (0 : ℂ) R, (h z).re ≤ B := by
    intro z hz
    have ho := hosc z hz
    dsimp only [B]
    linarith only [ho]
  have h7 := norm_hasDerivAt_sub_le_of_re_le hR0 hh hB0 hRe hs
  have hB : B - (h 0).re = M - Real.log ‖F 0‖ + 1 := by
    dsimp only [B]; ring
  rw [hB] at h7
  let A : ℝ := M - Real.log ‖F 0‖ + 1
  have hApos : 0 < A := by
    dsimp only [A]; linarith only [hnonneg]
  have hsnn : 0 ≤ ‖s‖ := norm_nonneg s
  have hRs : R / 2 ≤ R - ‖s‖ := by linarith only [hs]
  have hRspos : 0 < R - ‖s‖ := lt_of_lt_of_le (half_pos hR0) hRs
  have hratio : (R + ‖s‖) / (R - ‖s‖) ^ 3 ≤ 12 / R ^ 2 := by
    rw [div_le_div_iff₀ (pow_pos hRspos 3) (sq_pos_of_pos hR0)]
    have h3 : (R / 2) ^ 3 ≤ (R - ‖s‖) ^ 3 := pow_le_pow_left₀ (half_pos hR0).le hRs 3
    have hstep1 : (R + ‖s‖) * R ^ 2 ≤ (3 / 2) * R * R ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith only [hs]) (sq_nonneg R)
    have hstep2 : (3 / 2 : ℝ) * R * R ^ 2 = 12 * (R ^ 3 / 8) := by ring
    have hstep3 : (12 : ℝ) * (R ^ 3 / 8) ≤ 12 * (R - ‖s‖) ^ 3 := by
      have heq : (R : ℝ) ^ 3 / 8 = (R / 2) ^ 3 := by ring
      rw [heq]
      exact mul_le_mul_of_nonneg_left h3 (by norm_num only : (0 : ℝ) ≤ 12)
    exact (hstep1.trans_eq hstep2).trans hstep3
  have hcrude : 16 * A * (R + ‖s‖) / (R - ‖s‖) ^ 3 * ‖s‖ ≤ 192 * ‖s‖ * A / R ^ 2 := by
    have hAnn : (0 : ℝ) ≤ 16 * A := mul_nonneg (by norm_num only : (0 : ℝ) ≤ 16) hApos.le
    have h1 := mul_le_mul_of_nonneg_left hratio hAnn
    calc
      _ = 16 * A * ((R + ‖s‖) / (R - ‖s‖) ^ 3) * ‖s‖ := by ring
      _ ≤ 16 * A * (12 / R ^ 2) * ‖s‖ := mul_le_mul_of_nonneg_right h1 hsnn
      _ = _ := by ring
  exact h7.trans hcrude

/-- For entire F on a zero-free sphere, its sphere-divisor factor is identically
one. Every boundary point has divisor zero, as do all points outside the sphere. -/
theorem sphereFactor_eq_one_of_zeroFree {F : ℂ → ℂ} (hF : Differentiable ℂ F) {R : ℝ}
    (hzf : ∀ ρ : ℂ, ‖ρ‖ = R → F ρ ≠ 0) :
    (∏ᶠ v : ℂ, (fun z : ℂ ↦ z - v) ^ (MeromorphicOn.divisor (F) (Metric.sphere (0 : ℂ) R) v)) =
      (1 : ℂ → ℂ) := by
  apply finprod_eq_one_of_forall_eq_one
  intro v
  have hdiff := hF
  by_cases hv : v ∈ Metric.sphere (0 : ℂ) R
  · have hvne : ‖v‖ = R := by rwa [Metric.mem_sphere, dist_zero_right] at hv
    have hanalyticSphere : AnalyticOnNhd ℂ (F) (Metric.sphere (0 : ℂ) R) := fun z _ ↦
      hdiff.analyticAt z
    have hdiv0 : MeromorphicOn.divisor (F) (Metric.sphere (0 : ℂ) R) v = 0 := by
      rw [MeromorphicOn.divisor_apply hanalyticSphere.meromorphicOn hv,
        meromorphicOrderAt_eq_zero_of_entire_value_ne_zero hF (hzf v hvne)]
      rfl
    rw [hdiv0]
    funext z
    simp only [Pi.pow_apply, zpow_ofNat, pow_zero, Pi.one_apply]
  · have hdiv0 : MeromorphicOn.divisor (F) (Metric.sphere (0 : ℂ) R) v = 0 :=
      (MeromorphicOn.divisor (F) (Metric.sphere (0 : ℂ) R)).apply_eq_zero_of_notMem hv
    rw [hdiv0]
    funext z
    simp only [Pi.pow_apply, zpow_ofNat, pow_zero, Pi.one_apply]

/-- For an entire F with a zero-free boundary sphere, the right side of its
extended canonical decomposition is meromorphic at every point of the closed disk.
Use meromorphicity of canonical factors and the vanishing sphere divisor. -/
theorem meromorphicAt_ecanonicalDecompRHS {F : ℂ → ℂ} (hF : Differentiable ℂ F) {R : ℝ} {g : ℂ → ℂ}
    (D : Complex.ECanonicalDecomp (F) g R) (hzf : ∀ ρ : ℂ, ‖ρ‖ = R → F ρ ≠ 0) {x : ℂ}
    (hx : x ∈ Metric.closedBall (0 : ℂ) R) :
    MeromorphicAt
      (((∏ᶠ u : ℂ,
            (Complex.canonicalFactor R u) ^
              (-MeromorphicOn.divisor (F) (Metric.ball (0 : ℂ) R) u)) *
          (∏ᶠ v : ℂ,
            (fun z : ℂ ↦ z - v) ^ (MeromorphicOn.divisor (F) (Metric.sphere (0 : ℂ) R) v))) •
        g)
      x := by
  have hprod :
    MeromorphicAt
      (∏ᶠ u : ℂ,
        (Complex.canonicalFactor R u) ^ (-MeromorphicOn.divisor (F) (Metric.ball (0 : ℂ) R) u))
      x :=
    MeromorphicAt.finprod (fun u ↦ (Complex.meromorphic_canonicalFactor R u x).zpow _)
  have hsphere1 := sphereFactor_eq_one_of_zeroFree hF hzf (R := R)
  have hgAt : MeromorphicAt g x := (D.analyticOnNhd x hx).meromorphicAt
  rw [hsphere1, mul_one]
  exact hprod.smul hgAt

/-- For entire F nonzero at a point in the closed disk, its canonical factor
product is analytic there. A divisor-supported factor cannot have its pole at
the evaluation point; integer powers preserve analyticity at nonzero factors. -/
theorem analyticAt_canonicalFactorProduct_of_entire_value_ne_zero {F : ℂ → ℂ}
    (hF : Differentiable ℂ F) {R : ℝ} {x : ℂ} (hxclosed : x ∈ Metric.closedBall (0 : ℂ) R)
    (hxne : F x ≠ 0) :
    AnalyticAt ℂ
      (∏ᶠ u : ℂ,
        (Complex.canonicalFactor R u) ^ (-MeromorphicOn.divisor (F) (Metric.ball (0 : ℂ) R) u))
      x := by
  apply analyticAt_finprod
  intro u
  by_cases hdu : MeromorphicOn.divisor (F) (Metric.ball (0 : ℂ) R) u = 0
  · rw [hdu, neg_zero, zpow_zero]
    exact analyticAt_const
  · have huball : u ∈ Metric.ball (0 : ℂ) R :=
      (MeromorphicOn.divisor (F) (Metric.ball (0 : ℂ) R)).supportWithinDomain hdu
    have huxne : u ≠ x := by
      rintro rfl
      apply hdu
      have hdiff := hF
      have hanalyticBall : AnalyticOnNhd ℂ (F) (Metric.ball (0 : ℂ) R) := fun z _ ↦
        hdiff.analyticAt z
      rw [MeromorphicOn.divisor_apply hanalyticBall.meromorphicOn huball,
        meromorphicOrderAt_eq_zero_of_entire_value_ne_zero hF hxne]
      rfl
    have hcfAt : AnalyticAt ℂ (Complex.canonicalFactor R u) x :=
      Complex.analyticOnNhd_canonicalFactor R u x huxne.symm
    have hcfne : Complex.canonicalFactor R u x ≠ 0 :=
      Complex.canonicalFactor_ne_zero huball hxclosed huxne.symm
    exact hcfAt.zpow hcfne

/-- For entire F with a zero-free boundary and a nonzero value in the closed disk,
its logarithmic derivative splits into the canonical product and analytic factor.
Upgrade codiscrete equality locally using meromorphicity and continuity, then differentiate. -/
theorem ecanonicalDecomp_logDeriv_eq_at {F : ℂ → ℂ} (hF : Differentiable ℂ F) {R : ℝ} (hR : 0 < R)
    {g : ℂ → ℂ} (D : Complex.ECanonicalDecomp (F) g R) (hzf : ∀ ρ : ℂ, ‖ρ‖ = R → F ρ ≠ 0) {x : ℂ}
    (hxclosed : x ∈ Metric.closedBall (0 : ℂ) R) (hxne : F x ≠ 0) :
    logDeriv (F) x =
      logDeriv
          (∏ᶠ u : ℂ,
            (Complex.canonicalFactor R u) ^ (-MeromorphicOn.divisor (F) (Metric.ball (0 : ℂ) R) u))
          x +
        logDeriv g x := by
  set P : ℂ → ℂ :=
    ∏ᶠ u : ℂ,
      (Complex.canonicalFactor R u) ^ (-MeromorphicOn.divisor (F) (Metric.ball (0 : ℂ) R) u) with
    hP_def
  have hdiff := hF
  have hFAt : MeromorphicAt (F) x := (hdiff.analyticAt x).meromorphicAt
  have hRHSAt := meromorphicAt_ecanonicalDecompRHS hF D hzf hxclosed
  have hFeqRHS :=
    hFAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect hRHSAt hxclosed
      (preperfect_closedBall hR) D.eventuallyEq
  have hsphere1 := sphereFactor_eq_one_of_zeroFree hF hzf (R := R)
  have hFeqPg : (F) =ᶠ[nhdsWithin x {x}ᶜ] (P * g) := by
    have hrw :
      (((P *
              (∏ᶠ v : ℂ,
                (fun z : ℂ ↦ z - v) ^ (MeromorphicOn.divisor (F) (Metric.sphere (0 : ℂ) R) v))) •
            g) :
          ℂ → ℂ) =
        P * g := by
      rw [hsphere1, mul_one]
      funext z
      simp only [Pi.smul_apply', smul_eq_mul, Pi.mul_apply]
    rwa [hrw] at hFeqRHS
  have hPAt : AnalyticAt ℂ P x :=
    analyticAt_canonicalFactorProduct_of_entire_value_ne_zero hF hxclosed hxne
  have hgxne : g x ≠ 0 := D.ne_zero x hxclosed
  have hPxne : P x ≠ 0 := by
    have hFxeqPg : (F) x = (P * g) x :=
      eq_of_eventuallyEq_nhdsNE_of_continuousAt (hdiff.analyticAt x).continuousAt
        (hPAt.continuousAt.mul (D.analyticOnNhd x hxclosed).continuousAt) hFeqPg
    intro hP0
    rw [show (P * g) x = P x * g x from rfl, hP0, zero_mul] at hFxeqPg
    exact hxne hFxeqPg
  have hlogDerivEq : logDeriv (F) =ᶠ[nhdsWithin x {x}ᶜ] logDeriv (P * g) :=
    logDeriv_congr_nhdsNE hFeqPg
  have hFContAt : ContinuousAt (logDeriv (F)) x := by
    have h1 : ContinuousAt (deriv (F)) x := (hdiff.deriv.analyticAt x).continuousAt
    exact h1.div (hdiff.analyticAt x).continuousAt hxne
  have hPgContAt : ContinuousAt (logDeriv (P * g)) x := by
    have hderivPg : ContinuousAt (deriv (P * g)) x := by
      have : AnalyticAt ℂ (deriv (P * g)) x := (hPAt.mul (D.analyticOnNhd x hxclosed)).deriv
      exact this.continuousAt
    have hPgcont : ContinuousAt (P * g) x :=
      hPAt.continuousAt.mul (D.analyticOnNhd x hxclosed).continuousAt
    have hPgne : (P * g) x ≠ 0 := mul_ne_zero hPxne hgxne
    exact hderivPg.div hPgcont hPgne
  have hval := eq_of_eventuallyEq_nhdsNE_of_continuousAt hFContAt hPgContAt hlogDerivEq
  rw [hval]
  exact
    logDeriv_mul x hPxne hgxne hPAt.differentiableAt (D.analyticOnNhd x hxclosed).differentiableAt

/-- A point in the ball divisor support of an entire function differs from every
point where that function is nonzero. Its positive order would otherwise contradict
regularity of the evaluation point. -/
theorem ne_of_mem_divisorBallSupport_of_entire_value_ne_zero {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {R : ℝ} {u x : ℂ} (hu : MeromorphicOn.divisor (F) (Metric.ball (0 : ℂ) R) u ≠ 0)
    (hxne : F x ≠ 0) : u ≠ x := by
  rintro rfl
  apply hu
  have hdiff := hF
  have huball : u ∈ Metric.ball (0 : ℂ) R :=
    (MeromorphicOn.divisor (F) (Metric.ball (0 : ℂ) R)).supportWithinDomain hu
  have hanalyticBall : AnalyticOnNhd ℂ (F) (Metric.ball (0 : ℂ) R) := fun z _ ↦ hdiff.analyticAt z
  rw [MeromorphicOn.divisor_apply hanalyticBall.meromorphicOn huball,
    meromorphicOrderAt_eq_zero_of_entire_value_ne_zero hF hxne]
  rfl

/-- For entire F nonzero at a closed-disk point, the logarithmic derivative of
its canonical product equals the finite divisor-weighted factor derivative sum.
Differentiate the finite product and its integer powers at regular factors. -/
theorem logDeriv_canonicalFactorProduct_eq_finsum_at {F : ℂ → ℂ} (hF : Differentiable ℂ F) {R : ℝ}
    {x : ℂ} (hxclosed : x ∈ Metric.closedBall (0 : ℂ) R) (hxne : F x ≠ 0) :
    logDeriv
        (∏ᶠ u : ℂ,
          (Complex.canonicalFactor R u) ^ (-MeromorphicOn.divisor (F) (Metric.ball (0 : ℂ) R) u))
        x =
      ∑ᶠ u : ℂ,
        ((-MeromorphicOn.divisor (F) (Metric.ball (0 : ℂ) R) u : ℤ) : ℂ) *
          logDeriv (Complex.canonicalFactor R u) x := by
  have hdiff := hF
  have hanalyticClosed : AnalyticOnNhd ℂ (F) (Metric.closedBall (0 : ℂ) R) := fun z _ ↦
    hdiff.analyticAt z
  have hfin := hanalyticClosed.meromorphicOn.divisor_ball_support_finite
  have hdfin :
    (Function.support
        (fun u : ℂ ↦ -MeromorphicOn.divisor (F) (Metric.ball (0 : ℂ) R) u)).Finite := by
    have hset :
      Function.support (fun u : ℂ ↦ -MeromorphicOn.divisor (F) (Metric.ball (0 : ℂ) R) u) =
        Function.support (MeromorphicOn.divisor (F) (Metric.ball (0 : ℂ) R)) := by
      ext u
      simp only [Function.mem_support]
      constructor
      · intro h hz
        apply h
        rw [hz, neg_zero]
      · intro h hz
        apply h
        exact neg_eq_zero.mp hz
    rw [hset]
    exact hfin
  -- key facts about each `i` in the (finite) support, bundled once
  have hkey : ∀ i ∈ hdfin.toFinset, i ≠ x ∧ i ∈ Metric.ball (0 : ℂ) R := by
    intro i hi
    rw [Set.Finite.mem_toFinset, Function.mem_support, ne_eq, neg_eq_zero] at hi
    have hine : i ≠ x := ne_of_mem_divisorBallSupport_of_entire_value_ne_zero hF hi hxne
    exact ⟨hine, (MeromorphicOn.divisor (F) (Metric.ball (0 : ℂ) R)).supportWithinDomain hi⟩
  have h0 :
    (∏ᶠ u : ℂ,
        (Complex.canonicalFactor R u) ^ (-MeromorphicOn.divisor (F) (Metric.ball (0 : ℂ) R) u)) =
      ∏ i ∈ hdfin.toFinset,
        (Complex.canonicalFactor R i) ^ (-MeromorphicOn.divisor (F) (Metric.ball (0 : ℂ) R) i) := by
    apply finprod_eq_prod_of_mulSupport_subset
    intro i hi
    simp only [Function.mem_mulSupport] at hi
    simp only [Set.Finite.coe_toFinset, Function.mem_support, ne_eq, neg_eq_zero]
    intro hi0
    exact
      hi
        (by
          rw [hi0]
          rfl)
  have hAnalyticAll : ∀ i ∈ hdfin.toFinset, AnalyticAt ℂ (Complex.canonicalFactor R i) x :=
    fun i hi ↦ Complex.analyticOnNhd_canonicalFactor R i x (hkey i hi).1.symm
  have hcfxne :
    ∀ i ∈ hdfin.toFinset,
      Complex.canonicalFactor R i x ^ (-MeromorphicOn.divisor (F) (Metric.ball (0 : ℂ) R) i) ≠ 0 :=
    fun i hi ↦
    zpow_ne_zero _ (Complex.canonicalFactor_ne_zero (hkey i hi).2 hxclosed (hkey i hi).1.symm)
  have hdAt :
    ∀ i ∈ hdfin.toFinset,
      DifferentiableAt ℂ
        (fun z ↦
          (Complex.canonicalFactor R i z) ^ (-MeromorphicOn.divisor (F) (Metric.ball (0 : ℂ) R) i))
        x :=
    fun i hi ↦
    (hAnalyticAll i hi).differentiableAt.zpow
      (Or.inl (Complex.canonicalFactor_ne_zero (hkey i hi).2 hxclosed (hkey i hi).1.symm))
  have hprodfun :
    (fun a ↦
        ∏ i ∈ hdfin.toFinset,
          (Complex.canonicalFactor R i a) ^
            (-MeromorphicOn.divisor (F) (Metric.ball (0 : ℂ) R) i)) =
      ∏ i ∈ hdfin.toFinset,
        (fun a ↦
          (Complex.canonicalFactor R i a) ^
            (-MeromorphicOn.divisor (F) (Metric.ball (0 : ℂ) R) i)) := by
    funext a
    rw [Finset.prod_apply]
  have hstep :
    logDeriv
        (fun a ↦
          ∏ i ∈ hdfin.toFinset,
            (Complex.canonicalFactor R i a) ^
              (-MeromorphicOn.divisor (F) (Metric.ball (0 : ℂ) R) i))
        x =
      ∑ i ∈ hdfin.toFinset,
        logDeriv
          (fun z ↦
            (Complex.canonicalFactor R i z) ^
              (-MeromorphicOn.divisor (F) (Metric.ball (0 : ℂ) R) i))
          x := by
    rw [hprodfun]
    exact logDeriv_prod hcfxne hdAt
  rw [h0, Finset.prod_fn]
  rw [show
      (fun a ↦
          ∏ i ∈ hdfin.toFinset,
            (Complex.canonicalFactor R i ^ (-MeromorphicOn.divisor (F) (Metric.ball (0 : ℂ) R) i))
              a) =
        (fun a ↦
          ∏ i ∈ hdfin.toFinset,
            (Complex.canonicalFactor R i a) ^
              (-MeromorphicOn.divisor (F) (Metric.ball (0 : ℂ) R) i))
      from rfl,
    hstep]
  have hsub :
    Function.support
        (fun i : ℂ ↦
          ((-MeromorphicOn.divisor (F) (Metric.ball (0 : ℂ) R) i : ℤ) : ℂ) *
            logDeriv (Complex.canonicalFactor R i) x) ⊆
      hdfin.toFinset := by
    intro i hi
    rw [Function.mem_support] at hi
    rw [Set.Finite.coe_toFinset, Function.mem_support]
    intro h0'
    apply hi
    rw [h0']
    simp only [Int.cast_zero, zero_mul]
  rw [show
      (∑ i ∈ hdfin.toFinset,
          logDeriv
            (fun z ↦
              (Complex.canonicalFactor R i z) ^
                (-MeromorphicOn.divisor (F) (Metric.ball (0 : ℂ) R) i))
            x) =
        ∑ i ∈ hdfin.toFinset,
          ((-MeromorphicOn.divisor (F) (Metric.ball (0 : ℂ) R) i : ℤ) : ℂ) *
            logDeriv (Complex.canonicalFactor R i) x
      from
      Finset.sum_congr rfl
        (fun i hi ↦ by rw [logDeriv_fun_zpow (hAnalyticAll i hi).differentiableAt, mul_comm])]
  exact (finsum_eq_sum_of_support_subset _ hsub).symm

/-- For entire F nonzero at zero and at the evaluation point, a zero-free sphere
allows the centered logarithmic derivative to split into the centered factor sum
and analytic factor derivative. Subtract the two regular-point identities. -/
theorem ecanonicalDecomp_centered_logDeriv_eq {F : ℂ → ℂ} (h0 : F 0 ≠ 0) (hF : Differentiable ℂ F)
    {R : ℝ} (hR : 0 < R) {g : ℂ → ℂ} (D : Complex.ECanonicalDecomp (F) g R)
    (hzf : ∀ ρ : ℂ, ‖ρ‖ = R → F ρ ≠ 0) {s : ℂ} (hsclosed : s ∈ Metric.closedBall (0 : ℂ) R)
    (hsne : F s ≠ 0) :
    logDeriv (F) s - logDeriv (F) 0 =
      ((∑ᶠ u : ℂ,
            ((-MeromorphicOn.divisor (F) (Metric.ball (0 : ℂ) R) u : ℤ) : ℂ) *
              logDeriv (Complex.canonicalFactor R u) s) -
          (∑ᶠ u : ℂ,
            ((-MeromorphicOn.divisor (F) (Metric.ball (0 : ℂ) R) u : ℤ) : ℂ) *
              logDeriv (Complex.canonicalFactor R u) 0)) +
        (logDeriv g s - logDeriv g 0) := by
  have h0closed : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) R := by
    simp only [Metric.mem_closedBall, dist_self, hR.le]
  have h0ne : F 0 ≠ 0 := h0
  have heqs := ecanonicalDecomp_logDeriv_eq_at hF hR D hzf hsclosed hsne
  have heq0 := ecanonicalDecomp_logDeriv_eq_at hF hR D hzf h0closed h0ne
  rw [logDeriv_canonicalFactorProduct_eq_finsum_at hF hsclosed hsne] at heqs
  rw [logDeriv_canonicalFactorProduct_eq_finsum_at hF h0closed h0ne] at heq0
  linear_combination heqs - heq0

/-- For entire F nonzero at zero with a global exponential power bound, the
finite canonical correction sum is bounded by twice the evaluation norm divided
by radius squared times the Jensen zero count. Bound each correction and sum
nonnegative divisor multiplicities. -/
theorem norm_canonicalCorrectionSum_le {F : ℂ → ℂ} (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0)
    {C r R : ℝ} (hC : 0 < C) (hR : 0 < R) (hg : ∀ z : ℂ, ‖F z‖ ≤ Real.exp (C * (‖z‖ + 1) ^ r))
    {s : ℂ} (hs : ‖s‖ ≤ R / 2) :
    ‖∑ᶠ ρ : ℂ,
          (MeromorphicOn.divisor F (Metric.ball 0 R) ρ : ℂ) *
            ((starRingEnd ℂ) ρ / ((R : ℂ) ^ 2 - (starRingEnd ℂ) ρ * s) -
              (starRingEnd ℂ) ρ / (R : ℂ) ^ 2)‖ ≤
      (2 * ‖s‖ / R ^ 2) * ((C * (2 * R + 1) ^ r - Real.log ‖F 0‖) / Real.log 2) := by
  have hdiff := hF
  have hanalyticClosed : AnalyticOnNhd ℂ (F) (Metric.closedBall (0 : ℂ) R) := fun z _ ↦
    hdiff.analyticAt z
  have hanalyticBall : AnalyticOnNhd ℂ (F) (Metric.ball (0 : ℂ) R) := fun z _ ↦ hdiff.analyticAt z
  set D := MeromorphicOn.divisor (F) (Metric.ball (0 : ℂ) R) with hD_def
  have hfin : (Function.support D).Finite :=
    hanalyticClosed.meromorphicOn.divisor_ball_support_finite
  have hDnonneg : ∀ ρ, (0 : ℤ) ≤ D ρ := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hanalyticBall
  have heqsum :
    (∑ᶠ ρ : ℂ,
        ((D ρ : ℤ) : ℂ) *
          ((starRingEnd ℂ) ρ / ((R : ℂ) ^ 2 - (starRingEnd ℂ) ρ * s) -
            (starRingEnd ℂ) ρ / (R : ℂ) ^ 2)) =
      ∑ ρ ∈ hfin.toFinset,
        ((D ρ : ℤ) : ℂ) *
          ((starRingEnd ℂ) ρ / ((R : ℂ) ^ 2 - (starRingEnd ℂ) ρ * s) -
            (starRingEnd ℂ) ρ / (R : ℂ) ^ 2) := by
    apply finsum_eq_sum_of_support_subset
    intro ρ hρ
    simp only [Function.mem_support, ne_eq] at hρ
    rw [Set.Finite.coe_toFinset, Function.mem_support]
    intro hD0
    apply hρ
    rw [hD0]
    simp only [Int.cast_zero, zero_mul]
  rw [heqsum]
  have hstep1 :
    ‖∑ ρ ∈ hfin.toFinset,
          ((D ρ : ℤ) : ℂ) *
            ((starRingEnd ℂ) ρ / ((R : ℂ) ^ 2 - (starRingEnd ℂ) ρ * s) -
              (starRingEnd ℂ) ρ / (R : ℂ) ^ 2)‖ ≤
      ∑ ρ ∈ hfin.toFinset, (D ρ : ℝ) * (2 * ‖s‖ / R ^ 2) := by
    calc
      ‖∑ ρ ∈ hfin.toFinset,
              ((D ρ : ℤ) : ℂ) *
                ((starRingEnd ℂ) ρ / ((R : ℂ) ^ 2 - (starRingEnd ℂ) ρ * s) -
                  (starRingEnd ℂ) ρ / (R : ℂ) ^ 2)‖ ≤
          ∑ ρ ∈ hfin.toFinset,
            ‖((D ρ : ℤ) : ℂ) *
                ((starRingEnd ℂ) ρ / ((R : ℂ) ^ 2 - (starRingEnd ℂ) ρ * s) -
                  (starRingEnd ℂ) ρ / (R : ℂ) ^ 2)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ ρ ∈ hfin.toFinset, (D ρ : ℝ) * (2 * ‖s‖ / R ^ 2) := by
        apply Finset.sum_le_sum
        intro ρ hρ
        rw [norm_mul]
        have hDcast : ‖((D ρ : ℤ) : ℂ)‖ = (D ρ : ℝ) := by
          rw [Complex.norm_intCast, abs_of_nonneg (by exact_mod_cast hDnonneg ρ)]
        rw [hDcast]
        apply mul_le_mul_of_nonneg_left _ (by exact_mod_cast hDnonneg ρ)
        rw [Set.Finite.mem_toFinset] at hρ
        have hρball : ρ ∈ Metric.ball (0 : ℂ) R := D.supportWithinDomain hρ
        exact norm_canonicalCorrection_le (by rwa [Metric.mem_ball, dist_zero_right] at hρball) hs
  have hstep2 :
    ∑ ρ ∈ hfin.toFinset, (D ρ : ℝ) * (2 * ‖s‖ / R ^ 2) =
      (2 * ‖s‖ / R ^ 2) * ∑ ρ ∈ hfin.toFinset, (D ρ : ℝ) := by
    rw [← Finset.sum_mul, mul_comm]
  have hdsum :
    (∑ ρ ∈ hfin.toFinset, (D ρ : ℝ)) ≤
      ∑ᶠ ρ : ℂ, (MeromorphicOn.divisor F (Metric.closedBall 0 R) ρ : ℝ) := by
    have he :
      ∀ ρ ∈ hfin.toFinset, (D ρ : ℝ) = (MeromorphicOn.divisor F (Metric.closedBall 0 R) ρ : ℝ) := by
      intro ρ hρ
      have hball : ρ ∈ Metric.ball (0 : ℂ) R := D.supportWithinDomain (hfin.mem_toFinset.mp hρ)
      dsimp only [D]
      rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hanalyticBall hball,
        MeromorphicOn.AnalyticOnNhd.divisor_apply hanalyticClosed
          (Metric.ball_subset_closedBall hball)]
    rw [Finset.sum_congr rfl he]
    exact sum_divisor_le_finsum hF R _
  have hj := jensen_count_le hF h0 hC hR hg
  have hpos : 0 ≤ 2 * ‖s‖ / R ^ 2 :=
    div_nonneg (mul_nonneg zero_le_two (norm_nonneg s)) (sq_nonneg R)
  exact (hstep1.trans_eq hstep2).trans (mul_le_mul_of_nonneg_left (hdsum.trans hj) hpos)

/-- An entire function nonzero at zero admits an extended canonical decomposition
on every closed disk. Connectedness makes all meromorphic orders finite, so the
canonical decomposition theorem applies. -/
theorem exists_ecanonicalDecomp_of_entire {F : ℂ → ℂ} (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0)
    (R : ℝ) : ∃ g, Complex.ECanonicalDecomp F g R := by
  have ha : AnalyticOnNhd ℂ F Set.univ := fun z _ ↦ hF.analyticAt z
  have ho : meromorphicOrderAt F 0 ≠ ⊤ := by
    rw [meromorphicOrderAt_eq_zero_of_entire_value_ne_zero hF h0]
    exact WithTop.coe_ne_top
  exact
    MeromorphicOn.exists_ecanonicalDecomp (fun z _ ↦ (hF.analyticAt z).meromorphicAt)
      (fun z ↦
        ha.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
          (Set.mem_univ z) (Set.mem_univ 0) ho)

/-- The finite-radius genus-one sum of ball divisor multiplicities times
1/(s-rho)+1/rho. It approximates the centered logarithmic derivative of an entire function. -/
noncomputable def truncatedGenusSum (F : ℂ → ℂ) (R : ℝ) (s : ℂ) : ℂ :=
  ∑ᶠ ρ : ℂ, (MeromorphicOn.divisor F (Metric.ball 0 R) ρ : ℂ) * (1 / (s - ρ) + 1 / ρ)

end PseudoPrime.AnalyticNumberTheory.General
