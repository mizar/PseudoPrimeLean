/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Pole regularization and circle-integral residue formulae

Fully generic complex-analysis facts about circle-integral residue formulae for simple, double,
and triple poles, and the corresponding `dslope` regularizations. These statements are independent
of any particular zeta or contour kernel, so they can be reused by analytic applications without
importing application-specific contour machinery.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- If `f` is analytic at `c`, its divided slope `dslope f c` is analytic at `c` as well.
The value at `c` is the derivative, so the apparent singularity in `(f z - f c)/(z - c)` is
removed. The proof shifts the local power series; this supports iterated pole regularization. -/
theorem AnalyticAt.dslope {f : ℂ → ℂ} {c : ℂ} (hf : AnalyticAt ℂ f c) :
    AnalyticAt ℂ (dslope f c) c := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩

/-- For `R > 0`, if `g` is complex differentiable on the closed disk and
`(z - c) * f z = g z` on its boundary, the circle integral of `f` is `2πi * g c`.
Nonvanishing of `z - c` on the circle identifies the integrand with the Cauchy kernel.
This computes the residue from an analytic regularization, without assuming a genuine pole. -/
theorem circleIntegral_eq_two_pi_I_mul_of_mul_sub_eq {f g : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hg : DifferentiableOn ℂ g (Metric.closedBall c R))
    (heq : ∀ z ∈ Metric.sphere c R, (z - c) * f z = g z) :
    (∮ z in C(c, R), f z) = 2 * Real.pi * Complex.I * g c := by
  calc
    (∮ z in C(c, R), f z) = ∮ z in C(c, R), (z - c)⁻¹ * g z := by
      apply circleIntegral.integral_congr hR.le
      intro z hz
      have hsub : z - c ≠ 0 := by
        intro hzero
        have hzc : z = c := sub_eq_zero.mp hzero
        rw [hzc, Metric.mem_sphere, dist_self] at hz
        exact hR.ne' hz.symm
      change f z = (z - c)⁻¹ * g z
      rw [← heq z hz]
      field_simp [hsub]
    _ = 2 * Real.pi * Complex.I * g c := by
      simpa only [smul_eq_mul] using hg.circleIntegral_sub_inv_smul (Metric.mem_ball_self hR)

/-- For analytic `g` at `c` and a punctured identity `(z - c) * f z = g z`, some `R > 0`
works simultaneously for every `0 < r ≤ R`: the circle integral is `2πi * g c`.
Choose `R` strictly inside both supporting neighborhoods, then apply the Cauchy formula
on each smaller disk. The uniform radius permits later contour constructions to shrink circles. -/
theorem exists_radius_forall_circleIntegral_eq_two_pi_I_mul {f g : ℂ → ℂ} {c : ℂ}
    (hg : AnalyticAt ℂ g c)
    (heq : Filter.EventuallyEq (nhdsWithin c ({c}ᶜ : Set ℂ)) (fun z ↦ (z - c) * f z) g) :
    ∃ R : ℝ,
      0 < R ∧ ∀ r : ℝ, 0 < r → r ≤ R → (∮ z in C(c, r), f z) = 2 * Real.pi * Complex.I * g c := by
  obtain ⟨rg, hrg, hganalytic⟩ := hg.exists_ball_analyticOnNhd
  have hevent : ∀ᶠ z in nhds c, z ∈ ({c}ᶜ : Set ℂ) → (z - c) * f z = g z :=
    eventuallyEq_nhdsWithin_iff.mp heq
  obtain ⟨re, hre, hball⟩ := Metric.mem_nhds_iff.mp hevent
  let R := min rg re / 2
  have hR : 0 < R := div_pos (lt_min hrg hre) (by norm_num only)
  have hRrg : R < rg := by
    dsimp only [R]
    linarith only [hrg, min_le_left rg re]
  have hRre : R < re := by
    dsimp only [R]
    linarith only [hre, min_le_right rg re]
  refine ⟨R, hR, ?_⟩
  intro r hr hrR
  have hrg' : r < rg := hrR.trans_lt hRrg
  have hre' : r < re := hrR.trans_lt hRre
  apply circleIntegral_eq_two_pi_I_mul_of_mul_sub_eq hr
  · exact hganalytic.differentiableOn.mono (Metric.closedBall_subset_ball hrg')
  · intro z hz
    apply hball (Metric.closedBall_subset_ball hre' (Metric.sphere_subset_closedBall hz))
    rw [Set.mem_compl_singleton_iff]
    intro hzc
    rw [hzc, Metric.mem_sphere, dist_self] at hz
    exact hr.ne' hz.symm

/-- If `R > 0`, `g` is complex differentiable on the closed disk, and
`(z - c)² * f z = g z` on its boundary, the circle integral of `f` is `2πi * deriv g c`.
The boundary identity reduces the integral to Cauchy's first-derivative formula.
This computes the residue of a regularized pole of order at most two. -/
theorem circleIntegral_eq_two_pi_I_mul_deriv_of_sq_mul_sub_eq {f g : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hg : DifferentiableOn ℂ g (Metric.closedBall c R))
    (heq : ∀ z ∈ Metric.sphere c R, (z - c) ^ 2 * f z = g z) :
    (∮ z in C(c, R), f z) = 2 * Real.pi * Complex.I * deriv g c := by
  calc
    (∮ z in C(c, R), f z) = ∮ z in C(c, R), (1 / (z - c) ^ 2) * g z := by
      apply circleIntegral.integral_congr hR.le
      intro z hz
      have hsub : z - c ≠ 0 := by
        intro hzero
        have hzc : z = c := sub_eq_zero.mp hzero
        rw [hzc, Metric.mem_sphere, dist_self] at hz
        exact hR.ne' hz.symm
      change f z = (1 / (z - c) ^ 2) * g z
      rw [← heq z hz]
      field_simp [hsub]
    _ = 2 * Real.pi * Complex.I * deriv g c := by
      simpa only [smul_eq_mul] using hg.deriv_eq_smul_circleIntegral hR

/-- For analytic `g` at `c` and a punctured identity `(z - c)² * f z = g z`, there is
`R > 0` such that every `0 < r ≤ R` gives circle integral `2πi * deriv g c`.
The common radius lies strictly inside the analytic and identity neighborhoods, so the
double-pole Cauchy formula applies after any shrink required by contour geometry. -/
theorem exists_radius_forall_circleIntegral_eq_two_pi_I_mul_deriv {f g : ℂ → ℂ} {c : ℂ}
    (hg : AnalyticAt ℂ g c)
    (heq : Filter.EventuallyEq (nhdsWithin c ({c}ᶜ : Set ℂ)) (fun z ↦ (z - c) ^ 2 * f z) g) :
    ∃ R : ℝ,
      0 < R ∧
        ∀ r : ℝ, 0 < r → r ≤ R → (∮ z in C(c, r), f z) = 2 * Real.pi * Complex.I * deriv g c := by
  obtain ⟨rg, hrg, hganalytic⟩ := hg.exists_ball_analyticOnNhd
  have hevent : ∀ᶠ z in nhds c, z ∈ ({c}ᶜ : Set ℂ) → (z - c) ^ 2 * f z = g z :=
    eventuallyEq_nhdsWithin_iff.mp heq
  obtain ⟨re, hre, hball⟩ := Metric.mem_nhds_iff.mp hevent
  let R := min rg re / 2
  have hR : 0 < R := div_pos (lt_min hrg hre) (by norm_num only)
  have hRrg : R < rg := by
    dsimp only [R]
    linarith only [hrg, min_le_left rg re]
  have hRre : R < re := by
    dsimp only [R]
    linarith only [hre, min_le_right rg re]
  refine ⟨R, hR, ?_⟩
  intro r hr hrR
  have hrg' : r < rg := hrR.trans_lt hRrg
  have hre' : r < re := hrR.trans_lt hRre
  apply circleIntegral_eq_two_pi_I_mul_deriv_of_sq_mul_sub_eq hr
  · exact hganalytic.differentiableOn.mono (Metric.closedBall_subset_ball hrg')
  · intro z hz
    apply hball (Metric.closedBall_subset_ball hre' (Metric.sphere_subset_closedBall hz))
    rw [Set.mem_compl_singleton_iff]
    intro hzc
    rw [hzc, Metric.mem_sphere, dist_self] at hz
    exact hr.ne' hz.symm

/--
If `h` is analytic at `c`, three successive divided slopes at `c` remain analytic there.
Applying the divided-slope analyticity lemma three times constructs the analytic remainder
used in the cubic Laurent square adapter.
-/
theorem analyticAt_dslope_dslope_dslope {h : ℂ → ℂ} {c : ℂ} (hh : AnalyticAt ℂ h c) :
    AnalyticAt ℂ (dslope (dslope (dslope h c) c) c) c := by
  exact AnalyticAt.dslope (AnalyticAt.dslope (AnalyticAt.dslope hh))

/--
For any function `h` and `z ≠ c`, the third divided slope is the remainder after subtracting
`h c`, `deriv h c * (z - c)`, and `dslope (dslope h c) c c * (z - c)²`, divided by `(z - c)³`.
Expanding divided slopes and clearing the nonzero denominator proves this algebraic identity;
analyticity is not assumed. It supplies the decomposition used by the triple-pole square adapter.
-/
theorem dslope_dslope_dslope_of_ne {h : ℂ → ℂ} {c z : ℂ} (hne : z ≠ c) :
    dslope (dslope (dslope h c) c) c z =
      (h z - h c - deriv h c * (z - c) - dslope (dslope h c) c c * (z - c) ^ 2) / (z - c) ^ 3 := by
  have hsub : z - c ≠ 0 := sub_ne_zero.mpr hne
  have hd1 : dslope h c z = (h z - h c) / (z - c) := by rw [dslope_of_ne h hne, slope_def_field]
  have hd1c : dslope h c c = deriv h c := dslope_same h c
  have hd2 : dslope (dslope h c) c z = (h z - h c - deriv h c * (z - c)) / (z - c) ^ 2 := by
    rw [dslope_of_ne (dslope h c) hne, slope_def_field, hd1, hd1c]
    field_simp [hsub]
  rw [dslope_of_ne (dslope (dslope h c) c) hne, slope_def_field, hd2]
  field_simp [hsub]

/--
On any set `S` avoiding `c`, an identity `(z - c)³ * f z = h z` expresses `f` as its three
principal terms plus the third divided slope of `h`. Expanding the divided-slope remainder
and clearing denominators proves the equality on `S`, without an analyticity assumption.
This separates the algebraic boundary identity from the radius-selection argument.
-/
theorem eqOn_cubicPrincipalParts_of_mul_eq {f h : ℂ → ℂ} {c : ℂ} {S : Set ℂ} (hne : ∀ z ∈ S, z ≠ c)
    (heq : ∀ z ∈ S, (z - c) ^ 3 * f z = h z) :
    Set.EqOn f
      (fun z ↦
        h c * (z - c)⁻¹ ^ 3 +
          (deriv h c * (z - c)⁻¹ ^ 2 +
            (dslope (dslope h c) c c * (z - c)⁻¹ + dslope (dslope (dslope h c) c) c z)))
      S := by
  intro z hz
  have hzc := hne z hz
  have hsub : z - c ≠ 0 := sub_ne_zero.mpr hzc
  have hrem := dslope_dslope_dslope_of_ne (h := h) hzc
  have hmul := heq z hz
  simp only
  rw [hrem]
  field_simp [hsub] at hmul ⊢
  linear_combination hmul

/--
Input/assumptions: `h : ℂ → ℂ` analytic at `c`.
Conclusion: `dslope (dslope h c) c c = iteratedDeriv 2 h c / 2`.
Content: `h`'s explicit Taylor-coefficient power series (`AnalyticAt.hasFPowerSeriesAt`,
`ofScalars ℂ (fun n ↦ iteratedDeriv n h c / n!)`) transforms under two nested `dslope`s into
`fslope^[2] p` (`has_fpower_series_iterate_dslope_fslope`, mathlib), whose value at `c` is its
zeroth coefficient (`HasFPowerSeriesAt.coeff_zero`), equal to `p.coeff 2`
(`FormalMultilinearSeries.coeff_iterate_fslope`) `= iteratedDeriv 2 h c / 2!`
(`FormalMultilinearSeries.coeff_ofScalars`).
Role: converts nested pole regularizations into second derivatives in residue formulae.
-/
theorem dslope_dslope_same_eq_iteratedDeriv_two_div_two {h : ℂ → ℂ} {c : ℂ}
    (hh : AnalyticAt ℂ h c) : dslope (dslope h c) c c = iteratedDeriv 2 h c / 2 := by
  have hp := hh.hasFPowerSeriesAt
  have hiter := hp.has_fpower_series_iterate_dslope_fslope 2
  have hswap : (Function.swap dslope c)^[2] h = dslope (dslope h c) c := rfl
  rw [hswap] at hiter
  have hcoeff0 := hiter.coeff_zero (1 : Fin 0 → ℂ)
  rw [show
      (FormalMultilinearSeries.fslope^[2]
            (FormalMultilinearSeries.ofScalars ℂ (fun n => iteratedDeriv n h c / n.factorial)))
          0 (1 : Fin 0 → ℂ) =
        (FormalMultilinearSeries.fslope^[2]
              (FormalMultilinearSeries.ofScalars ℂ
                (fun n => iteratedDeriv n h c / n.factorial))).coeff
          0
      from rfl,
    FormalMultilinearSeries.coeff_iterate_fslope 2 0,
    FormalMultilinearSeries.coeff_ofScalars] at hcoeff0
  rw [← hcoeff0]
  norm_num only

/-- If `2πi * f m` tends to `i * L` and `c ≤ Re (f m)` for every natural `m`, then
`c ≤ Re ((2π)⁻¹ • L)`. Multiplying the limit by `-i`, taking real parts, and dividing by the
nonzero real constant `2π` reduces the claim to preservation of a lower bound under limits.
This transfers finite residue-ledger inequalities to the normalized limiting contour value. -/
theorem re_inv_two_pi_smul_ge_of_tendsto_residueLedger {f : ℕ → ℂ} {L : ℂ} {c : ℝ}
    (hraw :
      Filter.Tendsto (fun m => (2 * Real.pi : ℝ) * Complex.I * f m) Filter.atTop
        (nhds (Complex.I • L)))
    (hbound : ∀ m : ℕ, c ≤ (f m).re) : c ≤ ((2 * Real.pi : ℝ)⁻¹ • L).re := by
  have hcancelI : (-Complex.I) * Complex.I = (1 : ℂ) := by
    rw [neg_mul, Complex.I_mul_I]
    ring
  have hstep1 := hraw.const_mul (-Complex.I)
  have hstep2 : Filter.Tendsto (fun m : ℕ => (2 * Real.pi : ℝ) * f m) Filter.atTop (nhds L) := by
    have heq_fun :
      ∀ m : ℕ, (-Complex.I) * ((2 * Real.pi : ℝ) * Complex.I * f m) = (2 * Real.pi : ℝ) * f m := by
      intro m
      have hswap :
        (-Complex.I) * ((2 * Real.pi : ℝ) * Complex.I * f m) =
          ((-Complex.I) * Complex.I) * ((2 * Real.pi : ℝ) * f m) := by
        push_cast
        ring
      rw [hswap, hcancelI, one_mul]
    have heq_lim : (-Complex.I) * (Complex.I • L) = L := by
      rw [smul_eq_mul, ← mul_assoc, hcancelI, one_mul]
    rw [← heq_lim]
    exact Filter.Tendsto.congr heq_fun hstep1
  have hstep3 :
    Filter.Tendsto (fun m : ℕ => (2 * Real.pi : ℝ) * (f m).re) Filter.atTop (nhds L.re) := by
    have h := (Complex.continuous_re.tendsto _).comp hstep2
    refine h.congr (fun m => ?_)
    exact Complex.re_ofReal_mul _ _
  have hstep4 :
    Filter.Tendsto (fun m : ℕ => (f m).re) Filter.atTop (nhds ((2 * Real.pi : ℝ)⁻¹ * L.re)) := by
    have h := hstep3.const_mul (2 * Real.pi : ℝ)⁻¹
    refine h.congr (fun m => ?_)
    field_simp [Real.pi_ne_zero]
  have hle := ge_of_tendsto hstep4 (Filter.Eventually.of_forall hbound)
  simpa only [mul_inv_rev, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_inv,
    Complex.ofReal_ofNat, Complex.mul_re, Complex.inv_re, Complex.ofReal_re, Complex.normSq_ofReal,
    div_self_mul_self', Complex.re_ofNat, Complex.normSq_ofNat, Complex.inv_im, Complex.ofReal_im,
    neg_zero, zero_div, Complex.im_ofNat, mul_zero, sub_zero, Complex.mul_im, zero_mul, add_zero,
    ge_iff_le] using hle

end PseudoPrime.AnalyticNumberTheory.General
