/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CanonicalDecomposition
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Meromorphic.LogDeriv
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Common canonical-decomposition lemmas

Generic estimates for canonical factors and holomorphic derivatives on disks. The centered
logarithmic-derivative identity separates a genus-one term from a radius-dependent correction;
the correction bound supports limiting Hadamard factorizations for entire functions.
-/

namespace PseudoPrime.AnalyticNumberTheory.General

/-- If `h' = F` on the disk of radius `R > 0` and `Re h ≤ M` with `Re h(0) < M`,
Borel–Carathéodory and a Cauchy estimate on `deriv F` bound `‖F s - F 0‖` for `‖s‖ ≤ R / 2`. -/
theorem norm_hasDerivAt_sub_le_of_re_le {h F : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hh' : ∀ w ∈ Metric.ball (0 : ℂ) R, HasDerivAt h (F w) w) {M : ℝ} (hM0 : (h 0).re < M)
    (hRe_le : ∀ w ∈ Metric.ball (0 : ℂ) R, (h w).re ≤ M) {s : ℂ} (hs : ‖s‖ ≤ R / 2) :
    ‖F s - F 0‖ ≤ 16 * (M - (h 0).re) * (R + ‖s‖) / (R - ‖s‖) ^ 3 * ‖s‖ := by
  set M' : ℝ := M - (h 0).re with hM'_def
  have hM'pos : 0 < M' := by
    rw [hM'_def]; exact sub_pos.mpr hM0
  have hDiffOn : DifferentiableOn ℂ h (Metric.ball (0 : ℂ) R) := fun w hw =>
    (hh' w hw).differentiableAt.differentiableWithinAt
  have hderivh : ∀ w ∈ Metric.ball (0 : ℂ) R, deriv h w = F w := fun w hw => (hh' w hw).deriv
  have hFDiffOn : DifferentiableOn ℂ F (Metric.ball (0 : ℂ) R) :=
    (hDiffOn.deriv Metric.isOpen_ball).congr (fun w hw => (hderivh w hw).symm)
  set hsf : ℂ → ℂ := fun w => h w - h 0 with hhsf_def
  have hsf_diffOn : DifferentiableOn ℂ hsf (Metric.ball (0 : ℂ) R) := hDiffOn.sub_const (h 0)
  have hsf0 : hsf 0 = 0 := by simp only [hhsf_def, sub_self]
  have hsf_bound : ∀ w ∈ Metric.ball (0 : ℂ) R, (hsf w).re ≤ M' := by
    intro w hw
    have := hRe_le w hw
    simp only [hhsf_def, Complex.sub_re, hM'_def]
    exact sub_le_sub_right this _
  have hBC : ∀ w ∈ Metric.ball (0 : ℂ) R, ‖hsf w‖ ≤ 2 * M' * ‖w‖ / (R - ‖w‖) := fun w hw =>
    Complex.borelCaratheodory_zero hM'pos hsf_diffOn (fun v hv => hsf_bound v hv) hR hw hsf0
  set d : ℝ := ‖s‖ with hd_def
  have hd0 : 0 ≤ d := norm_nonneg s
  have hdR2 : d ≤ R / 2 := hs
  have hdR : d < R := lt_of_le_of_lt hdR2 (half_lt_self hR)
  set r0 : ℝ := (R - d) / 2 with hr0_def
  have hr0pos : 0 < r0 := by
    rw [hr0_def]; exact div_pos (sub_pos.mpr hdR) zero_lt_two
  set ρ : ℝ := (R + d) / 2 with hρ_def
  have hρR : ρ < R := by
    rw [hρ_def]; linarith only [hdR]
  set C : ℝ := 2 * M' * ρ / (R - ρ) with hC_def
  have hunif : ∀ w0 : ℂ, ‖w0‖ ≤ d → ‖deriv F w0‖ ≤ 2 * C / r0 ^ 2 := by
    intro w0 hw0
    have hclose_mem : ∀ u : ℂ, dist u w0 ≤ r0 → u ∈ Metric.ball (0 : ℂ) R := by
      intro u hu
      have hle : ‖u‖ ≤ ‖w0‖ + dist u w0 := by
        have h := norm_add_le w0 (u - w0)
        simpa only [dist_eq_norm, ge_iff_le, add_sub_cancel] using h
      rw [Metric.mem_ball, dist_zero_right]
      have hle2 : ‖w0‖ + r0 ≤ ρ := by
        calc
          ‖w0‖ + r0 ≤ d + r0 := by simpa [add_comm] using add_le_add_right hw0 r0
          _ = ρ := by
            rw [hr0_def, hρ_def]; ring
      exact
        lt_of_le_of_lt
          (le_trans hle (le_trans (by simpa [add_comm] using add_le_add_right hu ‖w0‖) hle2)) hρR
    have hw0mem : w0 ∈ Metric.ball (0 : ℂ) R := by
      rw [Metric.mem_ball, dist_zero_right]
      exact lt_of_le_of_lt hw0 (lt_of_le_of_lt hdR2 (half_lt_self hR))
    have hf_diffOn : DifferentiableOn ℂ hsf (Metric.ball w0 r0) :=
      hsf_diffOn.mono (fun u hu => hclose_mem u (le_of_lt (Metric.mem_ball.mp hu)))
    have hf_diffContOnCl : DiffContOnCl ℂ hsf (Metric.ball w0 r0) := by
      constructor
      · exact hf_diffOn
      · have hDiffCl : DifferentiableOn ℂ hsf (closure (Metric.ball w0 r0)) :=
          hsf_diffOn.mono
            (fun u hu =>
              hclose_mem u (Metric.mem_closedBall.mp (Metric.closure_ball_subset_closedBall hu)))
        exact hDiffCl.continuousOn
    have hsphere_bound : ∀ u ∈ Metric.sphere w0 r0, ‖hsf u‖ ≤ C := by
      intro u hu
      have hu_dist : dist u w0 = r0 := Metric.mem_sphere.mp hu
      have hu_norm_le : ‖u‖ ≤ ρ := by
        have h := norm_add_le w0 (u - w0)
        have hle : ‖u‖ ≤ ‖w0‖ + dist u w0 := by simpa only [dist_eq_norm, add_sub_cancel] using h
        rw [hu_dist] at hle
        calc
          ‖u‖ ≤ ‖w0‖ + r0 := hle
          _ ≤ d + r0 := by simpa [add_comm] using add_le_add_right hw0 r0
          _ = ρ := by
            rw [hr0_def, hρ_def]; ring
      have hu_mem : u ∈ Metric.ball (0 : ℂ) R := hclose_mem u hu_dist.le
      have h1 : (0 : ℝ) < R - ρ := sub_pos.mpr hρR
      have h2 : (0 : ℝ) < R - ‖u‖ := by
        have h3 := Metric.mem_ball.mp hu_mem
        rw [dist_zero_right] at h3
        exact sub_pos.mpr h3
      have hmono : 2 * M' * ‖u‖ / (R - ‖u‖) ≤ C := by
        rw [hC_def, div_le_div_iff₀ h2 h1]
        have h3 : ‖u‖ * (R - ρ) ≤ ρ * (R - ρ) := mul_le_mul_of_nonneg_right hu_norm_le h1.le
        have hρnn : (0 : ℝ) ≤ ρ := by
          rw [hρ_def]; linarith
        have h4 : ρ * (R - ρ) ≤ ρ * (R - ‖u‖) :=
          mul_le_mul_of_nonneg_left (by linarith [hu_norm_le]) hρnn
        nlinarith only [h3, h4, hM'pos]
      exact (hBC u hu_mem).trans hmono
    have hcauchy :=
      Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (f := hsf) (c := w0) (R := r0)
        (C := C) 2 hr0pos hf_diffContOnCl hsphere_bound
    have hderiv_sub_const : ∀ w : ℂ, deriv hsf w = deriv h w := fun w => deriv_sub_const (h 0)
    have heventually : deriv hsf =ᶠ[nhds w0] F := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hw0mem] with w hw
      rw [hderiv_sub_const w, hderivh w hw]
    have hiter_eq : iteratedDeriv 2 hsf w0 = deriv F w0 := by
      rw [iteratedDeriv_succ, iteratedDeriv_one]
      exact heventually.deriv_eq
    rw [hiter_eq] at hcauchy
    simpa only [ge_iff_le, Nat.factorial_two, Nat.cast_ofNat] using hcauchy
  have hFdiffAt : ∀ x ∈ segment ℝ (0 : ℂ) s, DifferentiableAt ℂ F x := by
    intro x hx
    have hxnorm : ‖x‖ ≤ d := by
      obtain ⟨a, b, ha, hb, hab, hxab⟩ := hx
      rw [← hxab, hd_def]
      calc
        ‖a • (0 : ℂ) + b • s‖ = ‖b • s‖ := by rw [smul_zero, zero_add]
        _ = |b| * ‖s‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ ≤ ‖s‖ := by
          rw [abs_of_nonneg hb]
          have hb1 : b ≤ 1 := hab ▸ le_add_of_nonneg_left ha
          exact (mul_le_mul_of_nonneg_right hb1 (norm_nonneg s)).trans_eq (one_mul _)
    have hxmem : x ∈ Metric.ball (0 : ℂ) R := by
      rw [Metric.mem_ball, dist_zero_right]; linarith
    exact (hFDiffOn x hxmem).differentiableAt (Metric.isOpen_ball.mem_nhds hxmem)
  have hFbound : ∀ x ∈ segment ℝ (0 : ℂ) s, ‖deriv F x‖ ≤ 2 * C / r0 ^ 2 := by
    intro x hx
    obtain ⟨a, b, ha, hb, hab, hxab⟩ := hx
    apply hunif
    rw [← hxab]
    calc
      ‖a • (0 : ℂ) + b • s‖ = ‖b • s‖ := by rw [smul_zero, zero_add]
      _ = |b| * ‖s‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ‖s‖ := by
        rw [abs_of_nonneg hb]
        have hb1 : b ≤ 1 := hab ▸ le_add_of_nonneg_left ha
        exact (mul_le_mul_of_nonneg_right hb1 (norm_nonneg s)).trans_eq (one_mul _)
  have hmvt :=
    Convex.norm_image_sub_le_of_norm_deriv_le hFdiffAt hFbound (convex_segment (0 : ℂ) s)
      (left_mem_segment ℝ (0 : ℂ) s) (right_mem_segment ℝ (0 : ℂ) s)
  rw [sub_zero] at hmvt
  have hfactor : 2 * C / r0 ^ 2 = 16 * M' * (R + d) / (R - d) ^ 3 := by
    have hRd_pos : (0 : ℝ) < R - d := sub_pos.mpr hdR
    have hRd_ne : R - d ≠ 0 := hRd_pos.ne'
    rw [hC_def, hρ_def, hr0_def, show R - (R + d) / 2 = (R - d) / 2 from by ring]
    field_simp
    ring
  rw [hfactor] at hmvt
  rwa [hM'_def]

/-- The log-derivative of a canonical factor `Complex.canonicalFactor R w`, evaluated away from
its pole `z = w`. -/
theorem logDeriv_canonicalFactor {R : ℝ} {w z : ℂ} (hw : w ∈ Metric.ball (0 : ℂ) R)
    (hz : z ∈ Metric.closedBall (0 : ℂ) R) (hzw : z ≠ w) :
    logDeriv (Complex.canonicalFactor R w) z =
      -(starRingEnd ℂ) w / ((R : ℂ) ^ 2 - (starRingEnd ℂ) w * z) - 1 / (z - w) := by
  have hRpos : 0 < R := Metric.pos_of_mem_ball hw
  have hRne : (R : ℂ) ≠ 0 := by exact_mod_cast hRpos.ne'
  have hzwne : z - w ≠ 0 := sub_ne_zero.mpr hzw
  have hcfne := Complex.canonicalFactor_ne_zero hw hz hzw
  rw [Complex.canonicalFactor_apply] at hcfne
  obtain ⟨hNne, hDne⟩ := div_ne_zero_iff.mp hcfne
  have hNhd :
    HasDerivAt (fun z : ℂ => (R : ℂ) ^ 2 - (starRingEnd ℂ) w * z) (-(starRingEnd ℂ) w) z := by
    have h1 : HasDerivAt (fun z : ℂ => (starRingEnd ℂ) w * z) (starRingEnd ℂ w) z := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id z).const_mul (starRingEnd ℂ w)
    simpa only using h1.const_sub ((R : ℂ) ^ 2)
  have hDhd : HasDerivAt (fun z : ℂ => (R : ℂ) * (z - w)) (R : ℂ) z := by
    have h1 : HasDerivAt (fun z : ℂ => z - w) 1 z := (hasDerivAt_id z).sub_const w
    simpa only [mul_one] using h1.const_mul (R : ℂ)
  change
    logDeriv ((fun z : ℂ => (R : ℂ) ^ 2 - (starRingEnd ℂ) w * z) / (fun z : ℂ => (R : ℂ) * (z - w)))
        z =
      _
  rw [logDeriv_div z hNne hDne hNhd.differentiableAt hDhd.differentiableAt, logDeriv_apply,
    logDeriv_apply, hNhd.deriv, hDhd.deriv]
  congr 1
  rw [div_mul_eq_div_mul_one_div, div_self hRne, one_mul]

/-- The centered difference of a canonical factor's log-derivative, split into the genus-one term
`1/(s-w)+1/w` and the `R`-dependent canonical correction `w̄/(R²-w̄s) - w̄/R²`. -/
theorem centered_logDeriv_canonicalFactor {R : ℝ} {w s : ℂ} (hw : w ∈ Metric.ball (0 : ℂ) R)
    (hs : s ∈ Metric.closedBall (0 : ℂ) R) (hsw : s ≠ w) (hw0 : w ≠ 0) :
    logDeriv (Complex.canonicalFactor R w) s - logDeriv (Complex.canonicalFactor R w) 0 =
      -(1 / (s - w) + 1 / w) -
        ((starRingEnd ℂ) w / ((R : ℂ) ^ 2 - (starRingEnd ℂ) w * s) -
          (starRingEnd ℂ) w / (R : ℂ) ^ 2) := by
  have h0closed : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) R := by
    simp only [Metric.mem_closedBall, dist_self, (Metric.pos_of_mem_ball hw).le]
  have h0ne : (0 : ℂ) ≠ w := Ne.symm hw0
  rw [logDeriv_canonicalFactor hw hs hsw, logDeriv_canonicalFactor hw h0closed h0ne]
  simp only [mul_zero, sub_zero, zero_sub]
  ring

/-- `closedBall 0 R` (`R > 0`) is `Preperfect` (has no isolated points) — needed to upgrade
`ECanonicalDecomp.eventuallyEq`'s `codiscreteWithin` equality to an actual punctured-neighborhood
equality at any evaluation point in the ball. -/
theorem preperfect_closedBall {R : ℝ} (hR : 0 < R) : Preperfect (Metric.closedBall (0 : ℂ) R) := by
  rw [← closure_ball (0 : ℂ) hR.ne']
  exact Metric.isOpen_ball.perfect_closure.acc

/-- A punctured-neighborhood equality between two functions continuous at the puncture point
forces equality of their values there too. -/
theorem eq_of_eventuallyEq_nhdsNE_of_continuousAt {f g : ℂ → ℂ} {x : ℂ} (hf : ContinuousAt f x)
    (hg : ContinuousAt g x) (h : f =ᶠ[nhdsWithin x {x}ᶜ] g) : f x = g x := by
  have h1 : Filter.Tendsto f (nhdsWithin x {x}ᶜ) (nhds (f x)) := hf.continuousWithinAt
  have h2 : Filter.Tendsto g (nhdsWithin x {x}ᶜ) (nhds (g x)) := hg.continuousWithinAt
  exact tendsto_nhds_unique h1 (h2.congr' h.symm)

/-- The pointwise bound on the canonical correction term `ρ̄/(R²-ρ̄s) - ρ̄/R²`, using only
`‖ρ‖ < R` and `‖s‖ ≤ R/2`. -/
theorem norm_canonicalCorrection_le {R : ℝ} {ρ s : ℂ} (hρ : ‖ρ‖ < R) (hs : ‖s‖ ≤ R / 2) :
    ‖(starRingEnd ℂ) ρ / ((R : ℂ) ^ 2 - (starRingEnd ℂ) ρ * s) - (starRingEnd ℂ) ρ / (R : ℂ) ^ 2‖ ≤
      2 * ‖s‖ / R ^ 2 := by
  have hRpos : 0 < R := lt_of_le_of_lt (norm_nonneg ρ) hρ
  have hRne : (R : ℂ) ≠ 0 := by exact_mod_cast hRpos.ne'
  have hRsqNorm : ‖(R : ℂ) ^ 2‖ = R ^ 2 := by
    rw [show ((R : ℂ) ^ 2) = ((R ^ 2 : ℝ) : ℂ) from by
        push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg (sq_nonneg R)]
  have hbound : ‖(starRingEnd ℂ) ρ * s‖ ≤ R * (R / 2) := by
    rw [norm_mul, RCLike.norm_conj]
    exact mul_le_mul hρ.le hs (norm_nonneg s) hRpos.le
  have hdenom : R ^ 2 / 2 ≤ ‖(R : ℂ) ^ 2 - (starRingEnd ℂ) ρ * s‖ := by
    calc
      R ^ 2 / 2 = R ^ 2 - R * (R / 2) := by ring
      _ ≤ ‖(R : ℂ) ^ 2‖ - ‖(starRingEnd ℂ) ρ * s‖ := by
        rw [hRsqNorm]
        exact sub_le_sub_left hbound _
      _ ≤ ‖(R : ℂ) ^ 2 - (starRingEnd ℂ) ρ * s‖ := norm_sub_norm_le _ _
  have hdenompos : (0 : ℝ) < R ^ 2 / 2 := by positivity
  have hdenomne : (R : ℂ) ^ 2 - (starRingEnd ℂ) ρ * s ≠ 0 := by
    intro h
    rw [h, norm_zero] at hdenom
    exact (not_le_of_gt hdenompos) hdenom
  have heq :
    (starRingEnd ℂ) ρ / ((R : ℂ) ^ 2 - (starRingEnd ℂ) ρ * s) - (starRingEnd ℂ) ρ / (R : ℂ) ^ 2 =
      (starRingEnd ℂ) ρ * (starRingEnd ℂ) ρ * s /
        (((R : ℂ) ^ 2 - (starRingEnd ℂ) ρ * s) * (R : ℂ) ^ 2) := by
    field_simp [hdenomne, hRne]
    ring
  rw [heq]
  simp only [norm_div, norm_mul, RCLike.norm_conj, hRsqNorm]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : ‖ρ‖ * ‖ρ‖ * ‖s‖ * R ^ 2 ≤ R * R * ‖s‖ * R ^ 2 := by
    have hle : ‖ρ‖ * ‖ρ‖ ≤ R * R := mul_le_mul hρ.le hρ.le (norm_nonneg ρ) hRpos.le
    exact
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle (norm_nonneg s)) (by positivity)
  have h2 : R * R * ‖s‖ * R ^ 2 ≤ 2 * ‖s‖ * (R ^ 2 / 2 * R ^ 2) := by
    have heqRR : R * R = R ^ 2 := by ring
    rw [heqRR, show (2 : ℝ) * ‖s‖ * (R ^ 2 / 2 * R ^ 2) = R ^ 2 * ‖s‖ * R ^ 2 from by ring]
  calc
    ‖ρ‖ * ‖ρ‖ * ‖s‖ * R ^ 2 ≤ R * R * ‖s‖ * R ^ 2 := h1
    _ ≤ 2 * ‖s‖ * (R ^ 2 / 2 * R ^ 2) := h2
    _ ≤ 2 * ‖s‖ * (‖(R : ℂ) ^ 2 - (starRingEnd ℂ) ρ * s‖ * R ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_right hdenom (by positivity)

end PseudoPrime.AnalyticNumberTheory.General
