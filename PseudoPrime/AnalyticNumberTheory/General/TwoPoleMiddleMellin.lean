/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.TwoPoleMellinInversion
public import PseudoPrime.Analysis.TwoPoleAbsoluteResolventBounds

/-! # Mellin inversion on the open strip between two real poles -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- A Mellin transform at -s gives the same transform of the reciprocal-argument function
at s, including convergence. Use the power substitution by -1 and Mellin inversion symmetry.
This supplies the tail transform for weights on both sides of one. -/
theorem hasMellin_comp_inv_of_hasMellin {f : ℝ → ℂ} {s m : ℂ} (hf : HasMellin f (-s) m) :
    HasMellin (fun u ↦ f u⁻¹) s m := by
  have hc :=
    (MellinConvergent.comp_rpow (f := f) (s := s) (a := -1) (by norm_num only)).mpr
      (by simpa only [Complex.ofReal_neg, Complex.ofReal_one, div_neg, div_one] using hf.1)
  refine ⟨?_, ?_⟩
  · simpa only [Real.rpow_neg_one] using hc
  · rw [mellin_comp_inv]
    exact hf.2

/-- Almost-everywhere equal weights on the positive half-line have the same convergent
Mellin transform. Multiply the equality by the Mellin power and transfer integrability
and the integral. This permits endpoint-safe definitions of piecewise Mellin profiles. -/
theorem hasMellin_congr_ae {f g : ℝ → ℂ} {s m : ℂ} (hf : HasMellin f s m)
    (he : f =ᵐ[MeasureTheory.volume.restrict (Set.Ioi 0)] g) : HasMellin g s m := by
  have hp :
    (fun u : ℝ ↦ (u : ℂ) ^ (s - 1) • f u) =ᵐ[MeasureTheory.volume.restrict (Set.Ioi 0)]
      (fun u : ℝ ↦ (u : ℂ) ^ (s - 1) • g u) :=
    he.mono (fun u hu ↦ congrArg (fun z : ℂ ↦ (u : ℂ) ^ (s - 1) • z) hu)
  refine ⟨?_, ?_⟩
  · exact hf.1.congr hp
  · rw [mellin, ← MeasureTheory.integral_congr_ae hp]
    exact hf.2

/-- The real nonpositive profile -min(u^a,u^(a+h))/h on positive u, and zero otherwise.
For h>0 it has Mellin transform 1/((s+a)(s+a+h)) between the two poles.
The minimum chooses the continuous value at u=1, including the shared endpoint. -/
noncomputable def twoPoleMiddleWeight (a h u : ℝ) : ℂ :=
  if 0 < u then ((-min (u ^ a) (u ^ (a + h)) / h : ℝ) : ℂ) else 0

/-- For positive gap and 0<u<=1, the middle-strip profile is -u^(a+h)/h.
Compare the positive powers using u^h<=1. This is the branch used at inverse scales x>=1. -/
theorem twoPoleMiddleWeight_small {a h u : ℝ} (hh : 0 < h) (hu : 0 < u) (hu1 : u ≤ 1) :
    twoPoleMiddleWeight a h u = ((-u ^ (a + h) / h : ℝ) : ℂ) := by
  have hp : u ^ (a + h) ≤ u ^ a := by
    rw [Real.rpow_add hu]
    exact mul_le_of_le_one_right (Real.rpow_nonneg hu.le a) (Real.rpow_le_one hu.le hu1 hh.le)
  rw [twoPoleMiddleWeight, ite_eq_left hu, min_eq_right hp]

/-- For positive gap and u>=1, the middle-strip profile is -u^a/h.
Compare the powers using u^h>=1. This branch supplies the convergent Mellin tail. -/
theorem twoPoleMiddleWeight_large {a h u : ℝ} (hh : 0 < h) (hu : 1 ≤ u) :
    twoPoleMiddleWeight a h u = ((-u ^ a / h : ℝ) : ℂ) := by
  have hu0 : 0 < u := zero_lt_one.trans_le hu
  have hp : u ^ a ≤ u ^ (a + h) := by
    rw [Real.rpow_add hu0]
    exact le_mul_of_one_le_right (Real.rpow_nonneg hu0.le a) (Real.one_le_rpow hu hh.le)
  rw [twoPoleMiddleWeight, ite_eq_left hu0, min_eq_left hp]

/-- Away from the endpoint one, express the positive-argument middle profile as the sum
of a compact power indicator and a reciprocal-argument compact power indicator.
Compute both branches explicitly. Equality almost everywhere suffices for the transform. -/
theorem twoPoleMiddleWeight_eq_indicator_sum {a h u : ℝ} (hh : 0 < h) (hu : 0 < u) (hu1 : u ≠ 1) :
    twoPoleMiddleWeight a h u =
      -(h : ℂ)⁻¹ *
        (Set.indicator (Set.Ioc (0 : ℝ) 1) (fun t ↦ (t : ℂ) ^ ((a + h : ℝ) : ℂ)) u +
          Set.indicator (Set.Ioc (0 : ℝ) 1) (fun t ↦ (t : ℂ) ^ ((-a : ℝ) : ℂ)) u⁻¹) := by
  rcases lt_or_gt_of_ne hu1 with hsmall | hlarge
  · have hinv : 1 < u⁻¹ := by
      have hdiv : (1 : ℝ) < 1 / u := (lt_div_iff₀ hu).mpr (by simpa only [one_mul] using hsmall)
      simpa only [one_div] using hdiv
    have hn : u⁻¹ ∉ Set.Ioc (0 : ℝ) 1 := fun hmem ↦ (not_le_of_gt hinv) hmem.2
    rw [twoPoleMiddleWeight_small hh hu hsmall.le,
      Set.indicator_of_mem (show u ∈ Set.Ioc (0 : ℝ) 1 from ⟨hu, hsmall.le⟩),
      Set.indicator_of_notMem hn, add_zero, ← Complex.ofReal_cpow hu.le (a + h), Complex.ofReal_div,
      Complex.ofReal_neg]
    ring
  · have hinv : u⁻¹ ≤ 1 := by
      have hdiv : (1 : ℝ) / u ≤ 1 := (div_le_one hu).mpr hlarge.le
      simpa only [one_div] using hdiv
    have hn : u ∉ Set.Ioc (0 : ℝ) 1 := fun hmem ↦ (not_le_of_gt hlarge) hmem.2
    rw [twoPoleMiddleWeight_large hh hlarge.le, Set.indicator_of_notMem hn,
      Set.indicator_of_mem (show u⁻¹ ∈ Set.Ioc (0 : ℝ) 1 from ⟨inv_pos.mpr hu, hinv⟩), zero_add, ←
      Complex.ofReal_cpow (inv_pos.mpr hu).le (-a), Real.inv_rpow hu.le, Real.rpow_neg hu.le,
      inv_inv, Complex.ofReal_div, Complex.ofReal_neg]
    ring

/-- For h>0 and -a-h<Re(s)<-a, the middle profile has the same rational two-pole transform.
Combine the compact and reciprocal-tail transforms and transfer equality almost everywhere.
Both endpoint convergence inequalities are explicit; no contour theorem is assumed. -/
theorem hasMellin_twoPoleMiddleWeight {a h : ℝ} (hh : 0 < h) {s : ℂ} (hs : s.re + a < 0)
    (ht : 0 < s.re + a + h) :
    HasMellin (twoPoleMiddleWeight a h) s (Analysis.twoPoleFunction a (a + h) s) := by
  let f := Set.indicator (Set.Ioc (0 : ℝ) 1) (fun t ↦ (t : ℂ) ^ ((a + h : ℝ) : ℂ))
  let g := Set.indicator (Set.Ioc (0 : ℝ) 1) (fun t ↦ (t : ℂ) ^ ((-a : ℝ) : ℂ))
  have hf :=
    hasMellin_cpow_Ioc ((a + h : ℝ) : ℂ) (s := s)
      (by
        simp only [Complex.ofReal_re]; linarith only [ht])
  have hg0 :=
    hasMellin_cpow_Ioc ((-a : ℝ) : ℂ) (s := -s)
      (by
        simp only [Complex.neg_re, Complex.ofReal_re]; linarith only [hs])
  have hg := hasMellin_comp_inv_of_hasMellin hg0
  have hsum := hasMellin_add hf.1 hg.1
  rw [hf.2, hg.2] at hsum
  have hscaled := hasMellin_const_smul hsum.1 (-(h : ℂ)⁻¹)
  rw [hsum.2] at hscaled
  have ha0 : s + (a : ℂ) ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hr
    linarith only [hs, hr]
  have hb0 : s + ((a + h : ℝ) : ℂ) ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hr
    linarith only [ht, hr]
  have heq :
    -(h : ℂ)⁻¹ * (1 / (s + ((a + h : ℝ) : ℂ)) + 1 / (-s + ((-a : ℝ) : ℂ))) =
      Analysis.twoPoleFunction a (a + h) s := by
    unfold Analysis.twoPoleFunction
    simp only [Complex.ofReal_neg]
    have hneg : -s + -(a : ℂ) = -(s + (a : ℂ)) := by ring
    rw [hneg]
    field_simp [ha0, hb0, Complex.ofReal_ne_zero.mpr hh.ne']
    simp only [Complex.ofReal_add]
    ring
  simp only [smul_eq_mul] at hscaled
  rw [heq] at hscaled
  apply
    hasMellin_congr_ae (f := fun u : ℝ ↦ -(h : ℂ)⁻¹ * (f u + g u⁻¹))
      (by simpa only [smul_eq_mul] using hscaled)
  have hne : ∀ᵐ u : ℝ, u ≠ 1 := by
    rw [MeasureTheory.ae_iff]
    simp only [not_not, Set.ofPred_eq_eq_singleton, MeasureTheory.measure_singleton]
  have hpos : ∀ᵐ u : ℝ ∂MeasureTheory.volume.restrict (Set.Ioi 0), 0 < u :=
    MeasureTheory.ae_restrict_mem measurableSet_Ioi
  exact
    ((MeasureTheory.ae_restrict_of_ae hne).and hpos).mono
      (fun u hu ↦ (twoPoleMiddleWeight_eq_indicator_sum hh hu.2 hu.1).symm)

/-- The rational two-pole function is integrable on every vertical line avoiding the real
parts of both poles, with no sign condition on their shifted distances.
Use the absolute-product resolvent majorant and an integrable Cauchy density.
This discharges Mellin inversion on lines between the poles as well as outside them. -/
theorem verticalIntegrable_twoPoleFunction_of_ne {a b σ : ℝ} (ha : σ + a ≠ 0) (hb : σ + b ≠ 0) :
    Complex.VerticalIntegrable (Analysis.twoPoleFunction a b) σ := by
  have hA : 0 < |(σ + a) * (σ + b)| := abs_pos.mpr (mul_ne_zero ha hb)
  have hm : 0 < min |(σ + a) * (σ + b)| 1 := lt_min hA zero_lt_one
  have hline : Continuous (fun t : ℝ ↦ (σ : ℂ) + (t : ℂ) * Complex.I) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hza (t : ℝ) : (σ : ℂ) + (t : ℂ) * Complex.I + a ≠ 0 := by
    intro hz
    have hr := congrArg Complex.re hz
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero, Complex.zero_re] at hr
    exact ha hr
  have hzb (t : ℝ) : (σ : ℂ) + (t : ℂ) * Complex.I + b ≠ 0 := by
    intro hz
    have hr := congrArg Complex.re hz
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero, Complex.zero_re] at hr
    exact hb hr
  have hf :
    Continuous
      (fun t : ℝ ↦
        (1 : ℂ) / (((σ : ℂ) + (t : ℂ) * Complex.I + a) * ((σ : ℂ) + (t : ℂ) * Complex.I + b))) :=
    continuous_const.div ((hline.add_const (a : ℂ)).mul (hline.add_const (b : ℂ)))
      (fun t ↦ mul_ne_zero (hza t) (hzb t))
  unfold Complex.VerticalIntegrable
  apply
    MeasureTheory.Integrable.mono'
      (integrable_inv_one_add_sq.const_mul (min |(σ + a) * (σ + b)| 1)⁻¹)
  · exact hf.aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro t
    have he :
      Analysis.twoPoleFunction a b ((σ : ℂ) + (t : ℂ) * Complex.I) =
        Analysis.twoPoleFunction (σ + a) (σ + b) (Complex.I * t) := by
      unfold Analysis.twoPoleFunction
      simp only [Complex.ofReal_add]
      congr 1
      ring
    have hk :=
      Analysis.twoPoleFunction_norm_le_abs_resolvent (Real.sqrt_pos.mpr hA)
        (show (Real.sqrt |(σ + a) * (σ + b)|) ^ 2 ≤ |(σ + a) * (σ + b)| by rw [Real.sq_sqrt hA.le])
        (t := t)
    rw [Real.sq_sqrt hA.le] at hk
    rw [he]
    have hmul := mul_le_mul_of_nonneg_right (min_le_right |(σ + a) * (σ + b)| 1) (sq_nonneg t)
    have hd : min |(σ + a) * (σ + b)| 1 * (1 + t ^ 2) ≤ |(σ + a) * (σ + b)| + t ^ 2 := by
      nlinarith only [hmul, min_le_left |(σ + a) * (σ + b)| 1]
    have hden : 0 < min |(σ + a) * (σ + b)| 1 * (1 + t ^ 2) :=
      mul_pos hm (by linarith only [sq_nonneg t])
    have hbound := one_div_le_one_div_of_le hden hd
    have heq :
      1 / (min |(σ + a) * (σ + b)| 1 * (1 + t ^ 2)) =
        (min |(σ + a) * (σ + b)| 1)⁻¹ * (1 + t ^ 2)⁻¹ := by
      rw [one_div, mul_inv]
    exact hk.trans (hbound.trans_eq heq)

/-- At every positive argument the middle profile is continuous for arbitrary parameters.
The minimum of two continuous real powers agrees with its definition on the positive domain.
This includes the endpoint one required for pointwise Mellin inversion. -/
theorem continuousAt_twoPoleMiddleWeight {a h u : ℝ} (hu : 0 < u) :
    ContinuousAt (twoPoleMiddleWeight a h) u := by
  have heq :
    Set.EqOn (twoPoleMiddleWeight a h) (fun t : ℝ ↦ ((-min (t ^ a) (t ^ (a + h)) / h : ℝ) : ℂ))
      (Set.Ioi 0) := by
    intro t ht
    rw [twoPoleMiddleWeight, ite_eq_left (show 0 < t from ht)]
  refine (ContinuousOn.congr ?_ heq).continuousAt (isOpen_Ioi.mem_nhds hu)
  intro t ht
  have ha : ContinuousAt (fun z : ℝ ↦ z ^ a) t := continuousAt_id.rpow_const (Or.inl ht.ne')
  have hb : ContinuousAt (fun z : ℝ ↦ z ^ (a + h)) t := continuousAt_id.rpow_const (Or.inl ht.ne')
  exact
    (Complex.continuous_ofReal.continuousAt.comp ((ha.min hb).neg.div_const h)).continuousWithinAt

/-- For positive gap the middle profile has nonpositive real part at every real argument.
Both positive real powers are nonnegative, and outside the domain the value is zero.
This records the sign of the inverse kernel on the left contour. -/
theorem twoPoleMiddleWeight_nonpos {a h u : ℝ} (hh : 0 < h) :
    (twoPoleMiddleWeight a h u).re ≤ 0 := by
  by_cases hu : 0 < u
  · rw [twoPoleMiddleWeight, ite_eq_left hu, Complex.ofReal_re]
    exact
      div_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (le_min (Real.rpow_nonneg hu.le a) (Real.rpow_nonneg hu.le (a + h)))) hh.le
  · rw [twoPoleMiddleWeight, ite_eq_right hu, Complex.zero_re]

/-- For h>0, a line strictly between the two poles and positive x, inverse Mellin integration
returns the nonpositive middle profile. Use its forward transform, continuity and the
proved vertical integrability. This evaluates the actual left-line kernel without norms. -/
theorem mellinInv_twoPoleMiddleWeight {a h σ x : ℝ} (hh : 0 < h) (hσ : σ + a < 0)
    (hσh : 0 < σ + a + h) (hx : 0 < x) :
    mellinInv σ (Analysis.twoPoleFunction a (a + h)) x = twoPoleMiddleWeight a h x := by
  have hconv :=
    (hasMellin_twoPoleMiddleWeight hh (s := (σ : ℂ)) (by simpa only [Complex.ofReal_re] using hσ)
        (by simpa only [Complex.ofReal_re] using hσh)).1
  have hpoint (t : ℝ) :
    mellin (twoPoleMiddleWeight a h) ((σ : ℂ) + (t : ℂ) * Complex.I) =
      Analysis.twoPoleFunction a (a + h) ((σ : ℂ) + (t : ℂ) * Complex.I) :=
    (hasMellin_twoPoleMiddleWeight hh
        (show ((σ : ℂ) + (t : ℂ) * Complex.I).re + a < 0 by
          simpa only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] using hσ)
        (show 0 < ((σ : ℂ) + (t : ℂ) * Complex.I).re + a + h by
          simpa only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] using hσh)).2
  have hVI : Complex.VerticalIntegrable (mellin (twoPoleMiddleWeight a h)) σ := by
    have h :=
      verticalIntegrable_twoPoleFunction_of_ne hσ.ne (show σ + (a + h) ≠ 0 by linarith only [hσh])
    unfold Complex.VerticalIntegrable at h ⊢
    exact h.congr (Filter.Eventually.of_forall (fun t ↦ (hpoint t).symm))
  have hm :=
    mellinInv_mellin_eq σ (twoPoleMiddleWeight a h) hx hconv hVI
      (continuousAt_twoPoleMiddleWeight hx)
  have hfun :
    (fun t : ℝ ↦
        (x : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) •
          Analysis.twoPoleFunction a (a + h) ((σ : ℂ) + (t : ℂ) * Complex.I)) =
      (fun t : ℝ ↦
        (x : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) •
          mellin (twoPoleMiddleWeight a h) ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
    funext t
    rw [hpoint]
  rw [← hm]
  unfold mellinInv
  rw [hfun]

end PseudoPrime.AnalyticNumberTheory.General
