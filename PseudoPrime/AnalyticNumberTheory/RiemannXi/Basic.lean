/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCount
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCounting

/-!
# The entire Riemann xi function

Define `ξ(s) = s(s-1)Λ₀(s)/2 + 1/2` using the entire regularization
`Λ₀(s) = Λ(s) + 1/s + 1/(1-s)`. Away from `0,1` this is the classical
`s(s-1)π^(-s/2)Γ(s/2)ζ(s)/2`; its values at both endpoints are `1/2`.
The factors `s(s-1)` cancel the completed zeta poles. At negative even integers,
Gamma's poles cancel zeta's trivial zeros (zero itself is not a zeta zero).

The algebraic numerator formula proves the xi/zeta zero correspondence away from
`1` and the trivial-zero locations. Local analytic factorization preserves zero
multiplicities in `Re s ≥ 0`, away from `1`. The functional equation and zeta's
zero-free regions give nonvanishing outside the critical strip.
-/

namespace PseudoPrime.AnalyticNumberTheory.RiemannXi

/-- The entire extension of `s(s-1)Λ(s)/2`, with value `1/2` at both `0` and `1`.
The definition uses the entire regularization `completedRiemannZeta₀`. -/
noncomputable def riemannXi (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta₀ s + 1 / 2

theorem differentiable_riemannXi :
    Differentiable ℂ riemannXi := by
  unfold riemannXi
  exact
    (((differentiable_const _).mul differentiable_id).mul
            (differentiable_id.sub (differentiable_const _)) |>.mul
          differentiable_completedZeta₀).add
      (differentiable_const _)

theorem riemannXi_one_sub (s : ℂ) :
    riemannXi (1 - s) = riemannXi s := by
  unfold riemannXi
  rw [show completedRiemannZeta₀ (1 - s) = completedRiemannZeta₀ s from
      (completedRiemannZeta₀_one_sub s)]
  ring

theorem riemannXi_zero : riemannXi 0 = 1 / 2 := by
  unfold riemannXi
  ring

theorem riemannXi_one : riemannXi 1 = 1 / 2 := by
  have h := riemannXi_one_sub 0
  simpa only [sub_zero, riemannXi_zero] using h

/-- `ξ` in terms of the numerator `N` from `riemannZeta_eq_mul_completedRiemannZeta₀`. -/
theorem riemannXi_eq {s : ℂ} (hs : s ≠ 1) :
    riemannXi s = (1 / 2 : ℂ) * (s - 1) * (s * completedRiemannZeta₀ s - 1 - s / (1 - s)) := by
  unfold riemannXi
  have h1s : (1 - s) ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
  field_simp [h1s]
  ring

/-- The denominator from `riemannZeta_eq_mul_completedRiemannZeta₀` is nonzero away from the
trivial-zero locations `s = -2(n+1)`. -/
theorem riemannZetaDenom_ne_zero {s : ℂ} (hs : ∀ n : ℕ, s ≠ -2 * (n + 1)) :
    (2 : ℂ) * (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2 + 1) ≠ 0 := by
  have hpiC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h1 : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hpiC)
  have h2 : Complex.Gamma (s / 2 + 1) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m hm
    apply hs m
    linear_combination 2 * hm
  exact mul_ne_zero (mul_ne_zero two_ne_zero h1) h2

/-- A ball whose radius does not exceed the positive real part of its complex center avoids all
nonpositive integer poles of `Gamma`. -/
theorem ball_avoids_Gamma_poles_of_re_pos {c : ℂ} {r : ℝ} (hr : 0 < r) (hrc : r ≤ c.re) :
    ∀ w ∈ Metric.ball c r, ∀ m : ℕ, w ≠ -m := by
  intro w hw m hwm
  rw [Metric.mem_ball, hwm, dist_eq_norm] at hw
  have habs := Complex.abs_re_le_norm (-(m : ℂ) - c)
  have hre : (-(m : ℂ) - c).re = -(m : ℝ) - c.re := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.natCast_re]
  rw [hre] at habs
  have hnonpos : -(m : ℝ) - c.re ≤ 0 := by
    exact
      add_nonpos (neg_nonpos.mpr (Nat.cast_nonneg (α := ℝ) m))
        (neg_nonpos.mpr (le_trans (le_of_lt hr) hrc))
  rw [abs_of_nonpos hnonpos] at habs
  nlinarith only [hw, habs, hrc, Nat.cast_nonneg (α := ℝ) m]

/-- Gamma is analytic at every complex point of positive real part. The proof uses the explicit
pole-avoiding ball above and mathlib's pointwise differentiability of Gamma off its poles. -/
theorem analyticAt_Gamma_of_re_pos {c : ℂ} (hc : 0 < c.re) : AnalyticAt ℂ Complex.Gamma c := by
  apply DifferentiableOn.analyticAt (s := Metric.ball c (c.re / 2))
  · intro w hw
    apply (Complex.differentiableAt_Gamma w ?_).differentiableWithinAt
    exact
      ball_avoids_Gamma_poles_of_re_pos
        (by linarith only [hc]) (by linarith only [hc]) w hw
  · exact Metric.ball_mem_nhds c (by linarith only [hc])

/-- The factor relating xi to zeta is analytic throughout `Re s ≥ 0`.
This statement asserts analyticity, not nonvanishing; the factor vanishes at `s = 1`. -/
theorem analyticAt_riemannXiZetaUnit {s : ℂ} (hs : 0 ≤ s.re) :
    AnalyticAt ℂ
      (fun z : ℂ =>
        (1 / 2 : ℂ) * (z - 1) * ((2 : ℂ) * (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2 + 1)))
      s := by
  have hpi : (Real.pi : ℂ) ∈ Complex.slitPlane := by exact Or.inl Real.pi_pos
  have hpow : AnalyticAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s := by
    have hlin : AnalyticAt ℂ (fun z : ℂ => -z / 2) s := by fun_prop
    exact analyticAt_const.cpow hlin hpi
  have hgamma : AnalyticAt ℂ (fun z : ℂ => Complex.Gamma (z / 2 + 1)) s := by
    have harg : AnalyticAt ℂ (fun z : ℂ => z / 2 + 1) s := by fun_prop
    convert
      (analyticAt_Gamma_of_re_pos ?_).comp_of_eq harg
        rfl using
      1
    · ext z
      rfl
    · simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re] at *
      nlinarith only [hs]
  exact
    ((analyticAt_const.mul (analyticAt_id.sub analyticAt_const)).mul
      ((analyticAt_const.mul hpow).mul hgamma))

/-- The Mellin-pole denominator is continuous at every point away from its trivial-zero
locations. -/
theorem continuousAt_riemannZetaDenom {s : ℂ} (hs : ∀ n : ℕ, s ≠ -2 * (n + 1)) :
    ContinuousAt (fun z : ℂ => (2 : ℂ) * (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2 + 1))
      s := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hpow : ContinuousAt (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s := by
    apply ContinuousAt.comp' (continuousAt_const_cpow hpi)
    exact continuousAt_id.neg.div_const 2
  have hgamma_arg : ∀ m : ℕ, s / 2 + 1 ≠ -m := by
    intro m hm
    apply hs m
    linear_combination 2 * hm
  have hgamma : ContinuousAt (fun z : ℂ => Complex.Gamma (z / 2 + 1)) s := by
    have harg : ContinuousAt (fun z : ℂ => z / 2 + 1) s :=
      (continuousAt_id.div_const 2).add continuousAt_const
    convert (Complex.continuousAt_Gamma (s / 2 + 1) hgamma_arg).comp_of_eq harg rfl using 1
    ext z
    rfl
  fun_prop

/-- Around every nontrivial point, the Mellin-pole denominator remains nonzero. -/
theorem eventually_riemannZetaDenom_ne_zero {s : ℂ} (hs : ∀ n : ℕ, s ≠ -2 * (n + 1)) :
    Filter.Eventually
      (fun z : ℂ => (2 : ℂ) * (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2 + 1) ≠ 0)
      (nhds s) := by
  exact
    (continuousAt_riemannZetaDenom hs).eventually_ne
      (riemannZetaDenom_ne_zero hs)

/-- Away from `s = 1` and wherever the Mellin-pole denominator is nonzero, `ξ` and `ζ` vanish
together. -/
theorem riemannXi_eq_zero_iff_of_denom_ne_zero {s : ℂ} (hs1 : s ≠ 1)
    (hd : (2 : ℂ) * (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2 + 1) ≠ 0) :
    riemannXi s = 0 ↔ riemannZeta s = 0 := by
  set N : ℂ := s * completedRiemannZeta₀ s - 1 - s / (1 - s) with hN_def
  have hXi : riemannXi s = (1 / 2 : ℂ) * (s - 1) * N := riemannXi_eq hs1
  have hZeta :
    riemannZeta s = N / ((2 : ℂ) * (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2 + 1)) :=
    riemannZeta_eq_mul_completedRiemannZeta₀ s
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  rw [hXi, hZeta, div_eq_zero_iff]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · norm_num only at h2
      · exact absurd h2 hs1'
    · left; exact h1
  · rintro (h | h)
    · rw [h, mul_zero]
    · exact absurd h hd

/-- Away from the pole and the gamma denominator zeros, `ξ` is an explicit nonzero factor
times `ζ`. This is the pointwise input for the local analytic-order comparison at a
nontrivial zero. -/
theorem riemannXi_eq_mul_riemannZeta_of_denom_ne_zero {s : ℂ} (hs1 : s ≠ 1)
    (hd : (2 : ℂ) * (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2 + 1) ≠ 0) :
    riemannXi s =
      ((1 / 2 : ℂ) * (s - 1) * ((2 : ℂ) * (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2 + 1))) *
        riemannZeta s := by
  set N : ℂ := s * completedRiemannZeta₀ s - 1 - s / (1 - s) with hN_def
  set D : ℂ := (2 : ℂ) * (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2 + 1) with hD_def
  have hxi : riemannXi s = (1 / 2 : ℂ) * (s - 1) * N := riemannXi_eq hs1
  have hzeta : riemannZeta s = N / D := by
    simpa only [hD_def] using riemannZeta_eq_mul_completedRiemannZeta₀ s
  have hD : D ≠ 0 := by simpa only [hD_def] using hd
  have hN : riemannZeta s * D = N := (eq_div_iff hD).mp hzeta
  rw [hxi, ← hN]
  simp only [hD_def]
  ring

/-- Near a point away from `1` and the trivial-zero locations, the xi/zeta factorization holds
as an `EventuallyEq`. This is the form consumed by `analyticOrderAt_congr`. -/
theorem riemannXi_eventuallyEq_mul_riemannZeta {s : ℂ} (hs1 : s ≠ 1)
    (hs : ∀ n : ℕ, s ≠ -2 * (n + 1)) :
    Filter.EventuallyEq (nhds s) riemannXi
      (fun z : ℂ =>
        ((1 / 2 : ℂ) * (z - 1) * ((2 : ℂ) * (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2 + 1))) *
          riemannZeta z) := by
  filter_upwards [eventually_ne_nhds hs1,
    eventually_riemannZetaDenom_ne_zero hs] with z hz1
    hzD
  exact
    riemannXi_eq_mul_riemannZeta_of_denom_ne_zero hz1 hzD

/-- For `Re s ≥ 0` and `s ≠ 1`, xi and zeta have the same analytic vanishing
order: their local factor is analytic and nonzero, hence has order zero. -/
theorem analyticOrderAt_riemannXi_eq_riemannZeta {s : ℂ} (hre : 0 ≤ s.re) (hs1 : s ≠ 1)
    (hs : ∀ n : ℕ, s ≠ -2 * (n + 1)) :
    analyticOrderAt riemannXi s = analyticOrderAt riemannZeta s := by
  let U : ℂ → ℂ := fun z =>
    (1 / 2 : ℂ) * (z - 1) * ((2 : ℂ) * (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2 + 1))
  have hUanalytic : AnalyticAt ℂ U s := analyticAt_riemannXiZetaUnit hre
  have hzeta : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s hs1
  have hUne : U s ≠ 0 := by
    unfold U
    exact
      mul_ne_zero (mul_ne_zero (by norm_num only) (sub_ne_zero.mpr hs1))
        (riemannZetaDenom_ne_zero hs)
  have hUorder : analyticOrderAt U s = 0 := hUanalytic.analyticOrderAt_eq_zero.mpr hUne
  have heq : riemannXi =ᶠ[nhds s] fun z => U z * riemannZeta z := by
    simpa only [U] using riemannXi_eventuallyEq_mul_riemannZeta hs1 hs
  have hmul :
    analyticOrderAt (fun z => U z * riemannZeta z) s =
      analyticOrderAt U s + analyticOrderAt riemannZeta s :=
    analyticOrderAt_mul hUanalytic hzeta
  rw [analyticOrderAt_congr heq, hmul, hUorder, zero_add]

theorem riemannXi_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    riemannXi s ≠ 0 := by
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hs
    simp only [Complex.one_re] at hs
    norm_num only at hs
  have hnt : ∀ n : ℕ, s ≠ -2 * (n + 1) := by
    intro n hcontra
    rw [hcontra] at hs
    simp only [Complex.neg_re, Complex.mul_re, Complex.re_ofNat, Complex.add_re, Complex.one_re,
      Complex.add_im, Complex.one_im, Complex.natCast_re, Complex.natCast_im] at hs
    nlinarith only [hs, Nat.cast_nonneg (α := ℝ) n]
  have hd := riemannZetaDenom_ne_zero hnt
  intro h
  exact
    riemannZeta_ne_zero_of_one_lt_re hs
      ((riemannXi_eq_zero_iff_of_denom_ne_zero hs1 hd).mp
        h)

/-- **`ξ` has no zeros left of the critical strip.** For `Re s < 0`, `ξ(s) = 0` either forces `s`
to satisfy `ζ(s) = 0` directly (once `s` avoids the trivial-zero locations, where
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.riemannZeta_ne_zero_of_re_neg` applies),
or — at a trivial-zero location `s = -2(n+1)` itself —
is ruled out via the functional equation `ξ(-2(n+1)) = ξ(1+2(n+1))`, landing back in the
`Re > 1` case already excluded. -/
theorem riemannXi_ne_zero_of_re_neg {s : ℂ} (hs : s.re < 0) :
    riemannXi s ≠ 0 := by
  by_cases hnt : ∀ n : ℕ, s ≠ -2 * (n + 1)
  · have hs1 : s ≠ 1 := by
      intro h
      rw [h] at hs
      simp only [Complex.one_re] at hs
      norm_num only at hs
    have hd := riemannZetaDenom_ne_zero hnt
    intro h
    exact
      RiemannZeta.riemannZeta_ne_zero_of_re_neg hs hnt
        ((riemannXi_eq_zero_iff_of_denom_ne_zero hs1
              hd).mp
          h)
  · push Not at hnt
    obtain ⟨n, hn⟩ := hnt
    rw [hn, ← riemannXi_one_sub]
    apply riemannXi_ne_zero_of_one_lt_re
    rw [show (1 : ℂ) - -2 * ((n : ℂ) + 1) = ((2 * n + 3 : ℕ) : ℂ) from by
        push_cast; ring]
    rw [Complex.natCast_re]
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) n]

end PseudoPrime.AnalyticNumberTheory.RiemannXi
