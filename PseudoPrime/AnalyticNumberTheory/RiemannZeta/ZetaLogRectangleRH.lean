/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaLogPhaseRH
import PseudoPrime.AnalyticNumberTheory.RiemannXi.HorizontalLogZetaRH
import Mathlib.Analysis.Complex.CauchyIntegral

/-! # Rectangle identity for the Euler-normalized zeta logarithm -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The boundary integral of a zeta logarithm on the upper strip vanishes
on every closed rectangle contained in the strip. This is the finite
rectangle identity preceding the critical-line boundary limit. -/
theorem zeta_log_rectangle_zero {f : ℂ → ℂ} {a b u v : ℝ} (ha : 1 / 2 < a) (hab : a ≤ b)
    (hb : b < 5 / 2) (hu : 1 < u) (huv : u ≤ v)
    (hf :
      ∀ z : ℂ, 1 / 2 < z.re → z.re < 5 / 2 → 1 < z.im → HasDerivAt f (logDeriv riemannZeta z) z) :
    (∫ x in a..b, f ((x : ℂ) + (u : ℂ) * Complex.I)) -
            (∫ x in a..b, f ((x : ℂ) + (v : ℂ) * Complex.I)) +
          Complex.I * (∫ y in u..v, f ((b : ℂ) + (y : ℂ) * Complex.I)) -
        Complex.I * (∫ y in u..v, f ((a : ℂ) + (y : ℂ) * Complex.I)) =
      0 := by
  let z : ℂ := (a : ℂ) + (u : ℂ) * Complex.I
  let w : ℂ := (b : ℂ) + (v : ℂ) * Complex.I
  have hzre : z.re = a := by
    simp only [z, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hzim : z.im = u := by
    simp only [z, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
  have hwre : w.re = b := by
    simp only [w, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hwim : w.im = v := by
    simp only [w, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
  have hd : DifferentiableOn ℂ f (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) := by
    intro s hs
    rw [Complex.mem_reProdIm, hzre, hwre, hzim, hwim, Set.uIcc_of_le hab, Set.uIcc_of_le huv] at hs
    exact
      (hf s (ha.trans_le hs.1.1) (hs.1.2.trans_lt hb)
          (hu.trans_le hs.2.1)).differentiableAt.differentiableWithinAt
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f z w hd
  simpa only [hzre, hwre, hzim, hwim, smul_eq_mul] using h

/-- A holomorphic function on the upper strip is interval integrable along
every horizontal segment contained in it. Continuity follows from the
pointwise complex derivative. -/
theorem zeta_log_horizontal_integrable {f : ℂ → ℂ} {a b t : ℝ} (ha : 1 / 2 < a) (hab : a ≤ b)
    (hb : b < 5 / 2) (ht : 1 < t)
    (hf :
      ∀ z : ℂ, 1 / 2 < z.re → z.re < 5 / 2 → 1 < z.im → HasDerivAt f (logDeriv riemannZeta z) z) :
    IntervalIntegrable (fun x : ℝ ↦ f ((x : ℂ) + (t : ℂ) * Complex.I)) MeasureTheory.volume a
      b := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hab]
  intro x hx
  have hlin : ContinuousAt (fun y : ℝ ↦ (y : ℂ) + (t : ℂ) * Complex.I) x :=
    (Complex.continuous_ofReal.add continuous_const).continuousAt
  have hzre : (((x : ℂ) + (t : ℂ) * Complex.I)).re = x := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hzim : (((x : ℂ) + (t : ℂ) * Complex.I)).im = t := by
    simp only [Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
  have hd :=
    hf ((x : ℂ) + (t : ℂ) * Complex.I)
      (by
        rw [hzre]; exact ha.trans_le hx.1)
      (by
        rw [hzre]; exact hx.2.trans_lt hb)
      (by
        rw [hzim]; exact ht)
  exact
    (ContinuousAt.comp (f := fun y : ℝ ↦ (y : ℂ) + (t : ℂ) * Complex.I) hd.continuousAt
        hlin).continuousWithinAt

/-- A holomorphic function on the upper strip is interval integrable along
every vertical segment contained in it. Continuity follows from the
pointwise complex derivative. -/
theorem zeta_log_vertical_integrable {f : ℂ → ℂ} {a u v : ℝ} (ha : 1 / 2 < a) (hb : a < 5 / 2)
    (hu : 1 < u) (huv : u ≤ v)
    (hf :
      ∀ z : ℂ, 1 / 2 < z.re → z.re < 5 / 2 → 1 < z.im → HasDerivAt f (logDeriv riemannZeta z) z) :
    IntervalIntegrable (fun y : ℝ ↦ f ((a : ℂ) + (y : ℂ) * Complex.I)) MeasureTheory.volume u
      v := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le huv]
  intro y hy
  have hlin : ContinuousAt (fun x : ℝ ↦ (a : ℂ) + (x : ℂ) * Complex.I) y :=
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousAt
  have hzre : (((a : ℂ) + (y : ℂ) * Complex.I)).re = a := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hzim : (((a : ℂ) + (y : ℂ) * Complex.I)).im = y := by
    simp only [Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
  have hd :=
    hf ((a : ℂ) + (y : ℂ) * Complex.I)
      (by
        rw [hzre]; exact ha)
      (by
        rw [hzre]; exact hb)
      (by
        rw [hzim]; exact hu.trans_le hy.1)
  exact
    (ContinuousAt.comp (f := fun x : ℝ ↦ (a : ℂ) + (x : ℂ) * Complex.I) hd.continuousAt
        hlin).continuousWithinAt

/-- On a rectangle inside the upper strip, the change in the horizontal
integral of the real part of a zeta logarithm equals the change between
the vertical integrals of its imaginary part. This is the real part of the
Cauchy boundary identity. -/
theorem zeta_log_rectangle_real {f : ℂ → ℂ} {a b u v : ℝ} (ha : 1 / 2 < a) (hab : a ≤ b)
    (hb : b < 5 / 2) (hu : 1 < u) (huv : u ≤ v)
    (hf :
      ∀ z : ℂ, 1 / 2 < z.re → z.re < 5 / 2 → 1 < z.im → HasDerivAt f (logDeriv riemannZeta z) z) :
    (∫ x in a..b, (f ((x : ℂ) + (v : ℂ) * Complex.I)).re) -
        (∫ x in a..b, (f ((x : ℂ) + (u : ℂ) * Complex.I)).re) =
      (∫ y in u..v, (f ((a : ℂ) + (y : ℂ) * Complex.I)).im) -
        (∫ y in u..v, (f ((b : ℂ) + (y : ℂ) * Complex.I)).im) := by
  have hv : 1 < v := hu.trans_le huv
  have ha' : 1 / 2 < b := ha.trans_le hab
  have hb' : a < 5 / 2 := hab.trans_lt hb
  have hiu := zeta_log_horizontal_integrable ha hab hb hu hf
  have hiv := zeta_log_horizontal_integrable ha hab hb hv hf
  have hia := zeta_log_vertical_integrable ha hb' hu huv hf
  have hib := zeta_log_vertical_integrable ha' hb hu huv hf
  have h := congrArg Complex.re (zeta_log_rectangle_zero ha hab hb hu huv hf)
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul,
    one_mul, zero_sub, Complex.zero_re] at h
  have hreU := Complex.reCLM.intervalIntegral_comp_comm hiu
  have hreV := Complex.reCLM.intervalIntegral_comp_comm hiv
  have himA := Complex.imCLM.intervalIntegral_comp_comm hia
  have himB := Complex.imCLM.intervalIntegral_comp_comm hib
  simp only [Complex.reCLM_apply] at hreU hreV
  simp only [Complex.imCLM_apply] at himA himB
  rw [← hreU, ← hreV, ← himA, ← himB] at h
  linarith only [h]

/-- For an Euler-normalized strip logarithm, the horizontal logarithmic
norm difference on a rectangle ending at real part two equals the
difference of its left imaginary-part integral and the Euler-log integral
at the right edge. This holds before taking the critical-line limit. -/
theorem zeta_log_rectangle_at_two {f : ℂ → ℂ} {a u v : ℝ} (ha : 1 / 2 < a) (ha2 : a ≤ 2)
    (hu : 1 < u) (huv : u ≤ v)
    (hf :
      ∀ z : ℂ,
        1 / 2 < z.re →
          z.re < 5 / 2 →
          1 < z.im →
          HasDerivAt f (logDeriv riemannZeta z) z ∧
            (f z).re = Real.log ‖riemannZeta z‖ ∧ (1 < z.re → f z = backlundZetaLog z)) :
    (∫ x in a..(2 : ℝ), Real.log ‖riemannZeta ((x : ℂ) + (v : ℂ) * Complex.I)‖) -
        (∫ x in a..(2 : ℝ), Real.log ‖riemannZeta ((x : ℂ) + (u : ℂ) * Complex.I)‖) =
      (∫ y in u..v, (f ((a : ℂ) + (y : ℂ) * Complex.I)).im) -
        (∫ y in u..v, (backlundZetaLog (((2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)).im) := by
  have hd :
    ∀ z : ℂ, 1 / 2 < z.re → z.re < 5 / 2 → 1 < z.im → HasDerivAt f (logDeriv riemannZeta z) z :=
    fun z h₁ h₂ h₃ ↦ (hf z h₁ h₂ h₃).1
  have h := zeta_log_rectangle_real ha ha2 (by norm_num only : (2 : ℝ) < 5 / 2) hu huv hd
  have hreal (t : ℝ) (ht : 1 < t) :
    (∫ x in a..(2 : ℝ), (f ((x : ℂ) + (t : ℂ) * Complex.I)).re) =
      ∫ x in a..(2 : ℝ), Real.log ‖riemannZeta ((x : ℂ) + (t : ℂ) * Complex.I)‖ := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le ha2] at hx
    have hs :=
      hf ((x : ℂ) + (t : ℂ) * Complex.I)
        (by
          simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
          exact ha.trans_le hx.1)
        (by
          simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
          linarith only [hx.2])
        (by
          simp only [Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im,
            Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
          exact ht)
    exact hs.2.1
  have hright :
    (∫ y in u..v, (f (((2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)).im) =
      ∫ y in u..v, (backlundZetaLog (((2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)).im := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le huv] at hy
    have hs :=
      hf (((2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)
        (by
          simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
          norm_num only)
        (by
          simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
          norm_num only)
        (by
          simp only [Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im,
            Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
          exact hu.trans_le hy.1)
    change
      (f (((2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)).im =
        (backlundZetaLog (((2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)).im
    rw [hs.2.2
        (by
          simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
          norm_num only)]
  rw [hreal v (hu.trans_le huv), hreal u hu, hright] at h
  exact h

/-- Under RH, a single Euler-normalized strip logarithm satisfies the finite
rectangle identity for all ordered heights above one and all left edges
strictly to the right of the critical line. Its boundary imaginary part
recovers the count-defined argument at almost every height at least 100. -/
theorem exists_zeta_log_rectangle_with_boundary (hRH : RiemannHypothesis) :
    ∃ f : ℂ → ℂ,
      (∀ a u v : ℝ,
          1 / 2 < a →
            a ≤ 2 →
            1 < u →
            u ≤ v →
            (∫ x in a..(2 : ℝ), Real.log ‖riemannZeta ((x : ℂ) + (v : ℂ) * Complex.I)‖) -
                (∫ x in a..(2 : ℝ), Real.log ‖riemannZeta ((x : ℂ) + (u : ℂ) * Complex.I)‖) =
              (∫ y in u..v, (f ((a : ℂ) + (y : ℂ) * Complex.I)).im) -
                (∫ y in u..v, (backlundZetaLog (((2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)).im)) ∧
        ∀ᵐ t : ℝ,
          100 ≤ t →
            Filter.Tendsto (fun a : ℝ ↦ (f ((a : ℂ) + (t : ℂ) * Complex.I)).im)
              (nhdsWithin (1 / 2 : ℝ) (Set.Ioi (1 / 2))) (nhds (Real.pi * zetaArgCount t)) := by
  obtain ⟨f, hf, hboundary⟩ := exists_strip_log_with_count_boundary hRH
  refine ⟨f, ?_, hboundary⟩
  intro a u v ha ha2 hu huv
  exact zeta_log_rectangle_at_two ha ha2 hu huv hf

/-- Under RH, at nonzero height the finite horizontal logarithmic integral
converges as its left endpoint approaches the critical line from the right.
The possible logarithmic singularity at the endpoint is integrable. -/
theorem tendsto_horizontal_logZeta_left (hRH : RiemannHypothesis) {t : ℝ} (ht : t ≠ 0) :
    Filter.Tendsto
      (fun a : ℝ ↦ ∫ x in a..(2 : ℝ), Real.log ‖riemannZeta ((x : ℂ) + (t : ℂ) * Complex.I)‖)
      (nhdsWithin (1 / 2 : ℝ) (Set.Ioi (1 / 2)))
      (nhds (∫ x in (1 / 2 : ℝ)..2, Real.log ‖riemannZeta ((x : ℂ) + (t : ℂ) * Complex.I)‖)) := by
  let g : ℝ → ℝ := fun x ↦ Real.log ‖riemannZeta ((x : ℂ) + (t : ℂ) * Complex.I)‖
  have hi :=
    (RiemannXi.intervalIntegrable_horizontal_logZeta hRH ht
          (show (0 : ℝ) ≤ 3 / 2 by norm_num only)).comp_add_right
      (-(1 / 2 : ℝ))
  have hig : IntervalIntegrable g MeasureTheory.volume (1 / 2) 2 := by
    convert hi using 1
    · funext x
      dsimp only [g]
      congr 2
      push_cast
      ring_nf
    · norm_num only
    · norm_num only
  have hmem : ∀ᶠ a : ℝ in nhdsWithin (1 / 2 : ℝ) (Set.Ioi (1 / 2)), a ∈ Set.uIcc (1 / 2) 2 := by
    have hlo : ∀ᶠ a : ℝ in nhdsWithin (1 / 2 : ℝ) (Set.Ioi (1 / 2)), 1 / 2 < a :=
      self_mem_nhdsWithin
    have hhi : ∀ᶠ a : ℝ in nhdsWithin (1 / 2 : ℝ) (Set.Ioi (1 / 2)), a < 2 :=
      (eventually_lt_nhds (by norm_num only : (1 / 2 : ℝ) < 2)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hlo, hhi] with a ha hb
    rw [Set.uIcc_of_le (by norm_num only : (1 / 2 : ℝ) ≤ 2)]
    exact ⟨ha.le, hb.le⟩
  have htend :
    Filter.Tendsto (fun a : ℝ ↦ a) (nhdsWithin (1 / 2 : ℝ) (Set.Ioi (1 / 2)))
      (nhdsWithin (1 / 2 : ℝ) (Set.uIcc (1 / 2) 2)) :=
    tendsto_nhdsWithin_iff.mpr ⟨Filter.tendsto_id.mono_left nhdsWithin_le_nhds, hmem⟩
  have hc := intervalIntegral.continuousOn_primitive_interval' hig (Set.right_mem_uIcc)
  have hlim := ((hc (1 / 2) Set.left_mem_uIcc).tendsto.comp htend).neg
  have he : (fun a : ℝ ↦ ∫ x in a..(2 : ℝ), g x) = (fun a : ℝ ↦ -(∫ x in (2 : ℝ)..a, g x)) := by
    funext a
    exact intervalIntegral.integral_symm 2 a
  change Filter.Tendsto (fun a : ℝ ↦ ∫ x in a..(2 : ℝ), g x) _ _
  rw [he]
  have hval : -(∫ x in (2 : ℝ)..(1 / 2 : ℝ), g x) = ∫ x in (1 / 2 : ℝ)..2, g x := by
    rw [intervalIntegral.integral_symm (1 / 2) 2, neg_neg]
  rw [← hval]
  exact hlim

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
