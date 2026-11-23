/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ComplexLogPrimitive
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Analytic.ChangeOrigin
public import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Convex
public import Mathlib.Topology.MetricSpace.Thickening

/-! # Bounds for logarithmic phases near a boundary zero -/

public section

namespace PseudoPrime.Analysis

/-- Two holomorphic logarithms with the same exponential on an open
preconnected set differ by a constant. Differentiating the exponential of
their difference proves that its derivative vanishes. -/
theorem log_exp_difference_constant {U : Set ℂ} (ho : IsOpen U) (hc : IsPreconnected U)
    {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (he : ∀ z ∈ U, Complex.exp (f z) = Complex.exp (g z)) {z w : ℂ} (hz : z ∈ U) (hw : w ∈ U) :
    f z - g z = f w - g w := by
  have hd : DifferentiableOn ℂ (fun x ↦ f x - g x) U := hf.sub hg
  have hzder : U.EqOn (deriv (fun x ↦ f x - g x)) 0 := by
    intro x hx
    have hder := ((hd x hx).differentiableAt (ho.mem_nhds hx)).hasDerivAt.cexp
    have hexp : (fun x ↦ Complex.exp (f x - g x)) =ᶠ[nhds x] (fun _ ↦ (1 : ℂ)) := by
      filter_upwards [ho.mem_nhds hx] with y hy
      rw [Complex.exp_sub, he y hy, div_self (Complex.exp_ne_zero _)]
    have hder' := hder.congr_of_eventuallyEq hexp.symm
    have hmul : Complex.exp (f x - g x) * deriv (fun x ↦ f x - g x) x = 0 := by
      simpa only [deriv_const] using hder'.deriv.symm
    exact (mul_eq_zero.mp hmul).resolve_left (Complex.exp_ne_zero _)
  exact ho.is_const_of_deriv_eq_zero hc hd hzder hz hw

/-- On an open preconnected set to the right of `c`, suppose the
exponential of a holomorphic function factors as `(z - c) ^ n * exp (g z)`.
If the imaginary part of `g` is bounded, then so is that of the original
logarithm. The principal logarithm of `z - c` has bounded argument, and
the two logarithms differ by a constant. -/
theorem local_log_im_bound {U : Set ℂ} (ho : IsOpen U) (hc : IsPreconnected U) {c : ℂ} {n : ℕ}
    {f g : ℂ → ℂ} {B : ℝ} {w : ℂ} (hw : w ∈ U) (hU : ∀ z ∈ U, c.re < z.re)
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (hexp : ∀ z ∈ U, Complex.exp (f z) = (z - c) ^ n * Complex.exp (g z))
    (hbound : ∀ z ∈ U, |(g z).im| ≤ B) : ∃ C : ℝ, ∀ z ∈ U, |(f z).im| ≤ C := by
  let p : ℂ → ℂ := fun z ↦ g z + (n : ℂ) * Complex.log (z - c)
  have hp : DifferentiableOn ℂ p U := by
    intro z hz
    have hzpos : 0 < (z - c).re := by
      simp only [Complex.sub_re]
      linarith only [hU z hz]
    have hslit : z - c ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hzpos)
    have hlog := (Complex.differentiableAt_log hslit).comp z (differentiableAt_id.sub_const c)
    exact ((hg z hz).add (hlog.differentiableWithinAt.const_mul (n : ℂ)))
  have heq : ∀ z ∈ U, Complex.exp (f z) = Complex.exp (p z) := by
    intro z hz
    have hzpos : 0 < (z - c).re := by
      simp only [Complex.sub_re]
      linarith only [hU z hz]
    have hne : z - c ≠ 0 := Complex.ne_zero_of_re_pos hzpos
    dsimp only [p]
    rw [Complex.exp_add, Complex.exp_natCast_mul, Complex.exp_log hne, mul_comm]
    exact hexp z hz
  refine ⟨|(f w - p w).im| + B + (n : ℝ) * Real.pi, ?_⟩
  intro z hz
  have hconst := log_exp_difference_constant ho hc hf hp heq hz hw
  have harg : |(Complex.log (z - c)).im| ≤ Real.pi := by
    rw [Complex.log_im]
    exact Complex.abs_arg_le_pi _
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hmul := mul_le_mul_of_nonneg_left harg hn
  have hreal := congrArg Complex.im hconst
  simp only [Complex.sub_im] at hreal
  have hpz : (p z).im = (g z).im + (n : ℝ) * (Complex.log (z - c)).im := by
    simp only [p, Complex.add_im, Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul,
      add_zero]
  rw [hpz] at hreal
  have htriangle := abs_add_le ((g z).im) ((n : ℝ) * (Complex.log (z - c)).im)
  have htriangle' := abs_add_le ((f w - p w).im) ((g z).im + (n : ℝ) * (Complex.log (z - c)).im)
  rw [abs_mul, abs_of_nonneg hn] at htriangle
  have hb := hbound z hz
  have he : (f z).im = (f w - p w).im + ((g z).im + (n : ℝ) * (Complex.log (z - c)).im) := by
    simp only [Complex.sub_im]
    linarith only [hreal]
  rw [he]
  linarith only [htriangle, htriangle', hmul, hb]

/-- A complex function analytic and nonzero at `c` has a holomorphic
logarithm on a disk around `c` whose imaginary part is bounded by `2π`.
Normalize the function by its center value so that its image lies in the
principal logarithm's slit plane. -/
theorem exists_bounded_local_log {h : ℂ → ℂ} {c : ℂ} (ha : AnalyticAt ℂ h c) (hne : h c ≠ 0) :
    ∃ r : ℝ,
      0 < r ∧
        ∃ g : ℂ → ℂ,
          DifferentiableOn ℂ g (Metric.ball c r) ∧
            (∀ z ∈ Metric.ball c r, Complex.exp (g z) = h z) ∧
            ∀ z ∈ Metric.ball c r, |(g z).im| ≤ 2 * Real.pi := by
  have hnorm : ContinuousAt (fun z ↦ h z / h c) c := ha.continuousAt.div_const _
  have hc : h c / h c ∈ Complex.slitPlane := by
    rw [div_self hne]
    exact Complex.one_mem_slitPlane
  have he : ∀ᶠ z in nhds c, h z / h c ∈ Complex.slitPlane :=
    hnorm (Complex.isOpen_slitPlane.mem_nhds hc)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (he.and ha.eventually_analyticAt)
  refine ⟨r, hr, fun z ↦ Complex.log (h z / h c) + Complex.log (h c), ?_, ?_, ?_⟩
  · intro z hz
    have hp := hball hz
    have hd : DifferentiableAt ℂ (fun z ↦ h z / h c) z := hp.2.differentiableAt.div_const _
    exact (((Complex.differentiableAt_log hp.1).comp z hd).add_const _).differentiableWithinAt
  · intro z hz
    have hp := hball hz
    have hq : h z / h c ≠ 0 := Complex.slitPlane_ne_zero hp.1
    rw [Complex.exp_add, Complex.exp_log hq, Complex.exp_log hne, div_mul_cancel₀ _ hne]
  · intro z hz
    simp only [Complex.add_im]
    have h1 : |(Complex.log (h z / h c)).im| ≤ Real.pi := by
      rw [Complex.log_im]
      exact Complex.abs_arg_le_pi _
    have h2 : |(Complex.log (h c)).im| ≤ Real.pi := by
      rw [Complex.log_im]
      exact Complex.abs_arg_le_pi _
    have h := abs_add_le (Complex.log (h z / h c)).im (Complex.log (h c)).im
    linarith only [h, h1, h2]

/-- Let `F` be analytic with finite order at `c`, and let `f` be a
holomorphic logarithm of `F` immediately to the right of `c`. On a small
right half-disk, the imaginary part of `f` is uniformly bounded. Factor
`F` at its finite-order zero and take a bounded local logarithm of the
nonvanishing factor. -/
theorem analytic_boundary_log_im_bound {F f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (ha : AnalyticAt ℂ F c) (horder : analyticOrderAt F c ≠ ⊤)
    (hf : ∀ z ∈ Metric.ball c R, c.re < z.re → DifferentiableAt ℂ f z)
    (hexp : ∀ z ∈ Metric.ball c R, c.re < z.re → Complex.exp (f z) = F z) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, ∀ z ∈ Metric.ball c r, c.re < z.re → |(f z).im| ≤ C := by
  obtain ⟨h, hha, hhne, heq⟩ := ha.analyticOrderAt_ne_top.mp horder
  have heq' : ∀ᶠ z in nhds c, F z = (z - c) ^ analyticOrderNatAt F c * h z := by
    filter_upwards [heq] with z hz
    simpa only [smul_eq_mul] using hz
  obtain ⟨r1, hr1, hball1⟩ := Metric.mem_nhds_iff.mp heq'
  obtain ⟨r2, hr2, g, hg, hge, hgb⟩ := exists_bounded_local_log hha hhne
  let r := min R (min r1 r2)
  have hr : 0 < r := lt_min hR (lt_min hr1 hr2)
  let U : Set ℂ := Metric.ball c r ∩ {z : ℂ | c.re < z.re}
  have ho : IsOpen U := Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)
  have hc : IsPreconnected U :=
    ((convex_ball c r).inter (convex_halfSpace_re_gt c.re)).isPreconnected
  have hrR : r ≤ R := min_le_left _ _
  have hr1' : r ≤ r1 := (min_le_right R (min r1 r2)).trans (min_le_left _ _)
  have hr2' : r ≤ r2 := (min_le_right R (min r1 r2)).trans (min_le_right _ _)
  have hfU : DifferentiableOn ℂ f U := by
    intro z hz
    exact (hf z ((Metric.ball_subset_ball hrR) hz.1) hz.2).differentiableWithinAt
  have hgU : DifferentiableOn ℂ g U := by
    intro z hz
    exact
      (hg z ((Metric.ball_subset_ball hr2') hz.1)).mono
        (fun _ hw ↦ (Metric.ball_subset_ball hr2') hw.1)
  have hU : ∀ z ∈ U, c.re < z.re := fun z hz ↦ hz.2
  have hexpU :
    ∀ z ∈ U, Complex.exp (f z) = (z - c) ^ analyticOrderNatAt F c * Complex.exp (g z) := by
    intro z hz
    rw [hexp z ((Metric.ball_subset_ball hrR) hz.1) hz.2,
      hball1 ((Metric.ball_subset_ball hr1') hz.1), hge z ((Metric.ball_subset_ball hr2') hz.1)]
  have hbU : ∀ z ∈ U, |(g z).im| ≤ 2 * Real.pi := by
    intro z hz
    exact hgb z ((Metric.ball_subset_ball hr2') hz.1)
  have hw : c + ((r / 2 : ℝ) : ℂ) ∈ U := by
    have hrhalf : 0 < r / 2 := by linarith only [hr]
    constructor
    · rw [Metric.mem_ball, dist_eq_norm]
      simp only [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrhalf]
      linarith only [hr]
    · simp only [Set.mem_ofPred_eq, Complex.add_re, Complex.ofReal_re]
      linarith only [hr]
  obtain ⟨C, hC⟩ := local_log_im_bound ho hc hw hU hfU hgU hexpU hbU
  exact ⟨r, hr, C, fun z hz hzre ↦ hC z ⟨hz, hzre⟩⟩

/-- Local right-side bounds near each point of a compact set combine into
one bound on a fixed positive-width neighborhood. A finite subcover and a
thickening of the compact set provide the common width and bound. -/
theorem compact_boundary_im_bound {K : Set ℂ} (hK : IsCompact K) {f : ℂ → ℂ}
    (hloc :
      ∀ c ∈ K, ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, ∀ z ∈ Metric.ball c r, 1 / 2 < z.re → |(f z).im| ≤ C) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ B : ℝ, ∀ z ∈ Metric.thickening δ K, 1 / 2 < z.re → |(f z).im| ≤ B := by
  classical
  have hh :
    ∀ c : K, ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, ∀ z ∈ Metric.ball (c : ℂ) r, 1 / 2 < z.re → |(f z).im| ≤ C :=
    fun c ↦ hloc c c.property
  choose r hr C hC using hh
  let A : K → Set ℂ := fun c ↦ Metric.ball c (r c)
  have hcover : K ⊆ ⋃ c : K, A c := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (hr ⟨x, hx⟩)⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover A (fun _ ↦ Metric.isOpen_ball) hcover
  let U : Set ℂ := ⋃ c ∈ s, A c
  have hU : IsOpen U := isOpen_iUnion fun c ↦ isOpen_iUnion fun _ ↦ Metric.isOpen_ball
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_thickening_subset_open hU hs
  refine ⟨δ, hδ, ∑ c ∈ s, |C c|, ?_⟩
  intro z hz hzre
  have hzU : z ∈ U := hδU hz
  obtain ⟨c, hc, hzc⟩ := Set.mem_iUnion₂.mp hzU
  have hbound := hC c z hzc hzre
  have hCabs : C c ≤ |C c| := le_abs_self _
  have hsum : |C c| ≤ ∑ c ∈ s, |C c| := Finset.single_le_sum (fun i hi ↦ abs_nonneg (C i)) hc
  linarith only [hbound, hCabs, hsum]

end PseudoPrime.Analysis
