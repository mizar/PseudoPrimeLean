/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaFiniteEulerMaclaurin

/-! # Eighth-order Euler–Maclaurin bounds for zeta -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The second Bernoulli polynomial, used to rewrite the existing sawtooth
remainder before the first integration-by-parts step. -/
private noncomputable def bernoulliTwo (v : ℝ) : ℝ :=
  v ^ 2 - v + 1 / 6

/-- The third Bernoulli polynomial, whose derivative is three times the
second and whose integer-cell endpoint values vanish. -/
private noncomputable def bernoulliThree (v : ℝ) : ℝ :=
  v ^ 3 - (3 / 2) * v ^ 2 + (1 / 2) * v

/-- The fourth Bernoulli polynomial, whose equal nonzero endpoint values
produce the first higher-order endpoint correction. -/
private noncomputable def bernoulliFour (v : ℝ) : ℝ :=
  v ^ 4 - 2 * v ^ 3 + v ^ 2 - 1 / 30

/-- The fifth Bernoulli polynomial, whose endpoint values vanish. -/
private noncomputable def bernoulliFive (v : ℝ) : ℝ :=
  v ^ 5 - (5 / 2) * v ^ 4 + (5 / 3) * v ^ 3 - (1 / 6) * v

/-- The sixth Bernoulli polynomial, whose common endpoint value is `1/42`. -/
private noncomputable def bernoulliSix (v : ℝ) : ℝ :=
  v ^ 6 - 3 * v ^ 5 + (5 / 2) * v ^ 4 - (1 / 2) * v ^ 2 + 1 / 42

/-- The seventh Bernoulli polynomial, whose endpoint values vanish. -/
private noncomputable def bernoulliSeven (v : ℝ) : ℝ :=
  v ^ 7 - (7 / 2) * v ^ 6 + (7 / 2) * v ^ 5 - (7 / 6) * v ^ 3 + (1 / 6) * v

/-- The existing sawtooth is the centered second Bernoulli weight divided
by two. This is the starting identity for the higher-order remainder. -/
private theorem sawtooth_eq_bernoulli_two (x : ℝ) :
    zetaSawtooth x = (bernoulliTwo (Int.fract x) - 1 / 6) / 2 := by
  dsimp only [zetaSawtooth, bernoulliTwo]
  ring

/-- The second periodic Bernoulli weight has absolute value at most one.
The existing sharp sawtooth bound supplies this coarse integrability bound. -/
private theorem abs_periodic_bernoulli_two_le (x : ℝ) : |bernoulliTwo (Int.fract x)| ≤ 1 := by
  have he := sawtooth_eq_bernoulli_two x
  have hh := abs_le.mp (abs_zetaSawtooth_le x)
  apply abs_le.mpr
  constructor <;> linarith only [he, hh.1, hh.2]

/-- The second Bernoulli weight times `x^(-s-2)` is integrable from 128 to
infinity on the critical line. It is dominated by `x^(-5/2)`. -/
private theorem integrable_em2_tail {s : ℂ} (hs : s.re = 1 / 2) :
    MeasureTheory.IntegrableOn
      (fun x : ℝ ↦ (x : ℂ) ^ (-s - 2) * ((bernoulliTwo (Int.fract x) : ℝ) : ℂ))
      (Set.Ioi (128 : ℝ)) := by
  have hd : MeasureTheory.IntegrableOn (fun x : ℝ ↦ x ^ (-(5 / 2 : ℝ))) (Set.Ioi (128 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num only) (by norm_num only)
  refine MeasureTheory.Integrable.mono' hd ?_ ?_
  · have hc : ContinuousOn (fun x : ℝ ↦ (x : ℂ) ^ (-s - 2)) (Set.Ioi (128 : ℝ)) := by
      intro x hx
      have hx0 : 0 < x := lt_trans (by norm_num only) hx
      exact
        (Complex.continuousAt_ofReal_cpow_const x (-s - 2)
            (Or.inr (ne_of_gt hx0))).continuousWithinAt
    have h1 :
      MeasureTheory.AEStronglyMeasurable (fun x : ℝ ↦ (x : ℂ) ^ (-s - 2))
        (MeasureTheory.volume.restrict (Set.Ioi (128 : ℝ))) :=
      hc.aestronglyMeasurable measurableSet_Ioi
    have hb : Continuous bernoulliTwo :=
      ((continuous_id.pow 2).sub continuous_id).add continuous_const
    have h2 :
      MeasureTheory.AEStronglyMeasurable (fun x : ℝ ↦ ((bernoulliTwo (Int.fract x) : ℝ) : ℂ))
        (MeasureTheory.volume.restrict (Set.Ioi (128 : ℝ))) :=
      (Complex.continuous_ofReal.measurable.comp
          (hb.measurable.comp measurable_fract)).aestronglyMeasurable
    exact h1.mul h2
  · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with x hx
    have hx0 : 0 < x := lt_trans (by norm_num only) hx
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.norm_real, Real.norm_eq_abs]
    have he : (-s - 2).re = -(5 / 2 : ℝ) := by
      simp only [Complex.sub_re, Complex.neg_re, Complex.re_ofNat, hs]
      norm_num only
    rw [he]
    have hb := abs_periodic_bernoulli_two_le x
    have hp := Real.rpow_nonneg hx0.le (-(5 / 2 : ℝ))
    nlinarith only [hb, hp, abs_nonneg (bernoulliTwo (Int.fract x))]

/-- The derivative of the third Bernoulli polynomial is three times the
second polynomial at every real argument. -/
private theorem hasDerivAt_bernoulli_three (x : ℝ) :
    HasDerivAt bernoulliThree (3 * bernoulliTwo x) x := by
  have h :=
    (((hasDerivAt_id x).pow 3).sub (((hasDerivAt_id x).pow 2).const_mul (3 / 2))).add
      ((hasDerivAt_id x).const_mul (1 / 2))
  convert h using 1
  · funext v
    rfl
  · simp only [bernoulliTwo, id_eq, Nat.cast_ofNat]
    ring

/-- The third Bernoulli polynomial vanishes at both endpoints of the unit
interval, so its first cellwise integration produces no boundary term. -/
private theorem bernoulli_three_endpoints : bernoulliThree 0 = 0 ∧ bernoulliThree 1 = 0 := by
  constructor <;> norm_num only [bernoulliThree]

/-- The derivative of the fourth Bernoulli polynomial is four times the
third polynomial, as required for the second integration step. -/
private theorem hasDerivAt_bernoulli_four (x : ℝ) :
    HasDerivAt bernoulliFour (4 * bernoulliThree x) x := by
  have h :=
    ((((hasDerivAt_id x).pow 4).sub (((hasDerivAt_id x).pow 3).const_mul 2)).add
          ((hasDerivAt_id x).pow 2)).sub_const
      (1 / 30)
  convert h using 1
  · funext v
    rfl
  · simp only [bernoulliThree, id_eq, Nat.cast_ofNat]
    ring

/-- The fourth Bernoulli polynomial has the same value `-1/30` at both
endpoints of the unit interval. -/
private theorem bernoulli_four_endpoints :
    bernoulliFour 0 = -1 / 30 ∧ bernoulliFour 1 = -1 / 30 := by
  constructor <;> norm_num only [bernoulliFour]

/-- The fifth Bernoulli polynomial differentiates to five times the fourth. -/
private theorem hasDerivAt_bernoulli_five (x : ℝ) :
    HasDerivAt bernoulliFive (5 * bernoulliFour x) x := by
  have h :=
    ((((hasDerivAt_id x).pow 5).sub (((hasDerivAt_id x).pow 4).const_mul (5 / 2))).add
          (((hasDerivAt_id x).pow 3).const_mul (5 / 3))).sub
      ((hasDerivAt_id x).const_mul (1 / 6))
  convert h using 1
  · funext v; rfl
  · simp only [bernoulliFour, id_eq, Nat.cast_ofNat]
    ring

/-- The sixth Bernoulli polynomial differentiates to six times the fifth. -/
private theorem hasDerivAt_bernoulli_six (x : ℝ) :
    HasDerivAt bernoulliSix (6 * bernoulliFive x) x := by
  have h :=
    (((((hasDerivAt_id x).pow 6).sub (((hasDerivAt_id x).pow 5).const_mul 3)).add
              (((hasDerivAt_id x).pow 4).const_mul (5 / 2))).sub
          (((hasDerivAt_id x).pow 2).const_mul (1 / 2))).add_const
      (1 / 42)
  convert h using 1
  · funext v; rfl
  · simp only [bernoulliFive, id_eq, Nat.cast_ofNat]
    ring

/-- The seventh Bernoulli polynomial differentiates to seven times the sixth. -/
private theorem hasDerivAt_bernoulli_seven (x : ℝ) :
    HasDerivAt bernoulliSeven (7 * bernoulliSix x) x := by
  have h :=
    (((((hasDerivAt_id x).pow 7).sub (((hasDerivAt_id x).pow 6).const_mul (7 / 2))).add
              (((hasDerivAt_id x).pow 5).const_mul (7 / 2))).sub
          (((hasDerivAt_id x).pow 3).const_mul (7 / 6))).add
      ((hasDerivAt_id x).const_mul (1 / 6))
  convert h using 1
  · funext v; rfl
  · simp only [bernoulliSix, id_eq, Nat.cast_ofNat]
    ring

/-- The fifth and seventh Bernoulli polynomials vanish at both ends of the
unit interval, so their integration steps have no boundary contribution. -/
private theorem bernoulli_odd_endpoints :
    (bernoulliFive 0 = 0 ∧ bernoulliFive 1 = 0) ∧
      (bernoulliSeven 0 = 0 ∧ bernoulliSeven 1 = 0) := by
  constructor <;> constructor <;> norm_num only [bernoulliFive, bernoulliSeven]

/-- The sixth Bernoulli polynomial has equal endpoint values `1/42`. -/
private theorem bernoulli_six_endpoints : bernoulliSix 0 = 1 / 42 ∧ bernoulliSix 1 = 1 / 42 := by
  constructor <;> norm_num only [bernoulliSix]

/-- A translated third Bernoulli polynomial divided by three is an
antiderivative of the second polynomial on each integer cell. -/
private theorem hasDerivAt_bernoulli_three_shift (n x : ℝ) :
    HasDerivAt (fun y ↦ bernoulliThree (y - n) / 3) (bernoulliTwo (x - n)) x := by
  have hp :=
    ((hasDerivAt_bernoulli_three (x - n)).comp x ((hasDerivAt_id x).sub_const n)).div_const 3
  convert hp using 1
  · rfl
  · ring

/-- The first cellwise integration step replaces a weight `g` by its
primitive `f/3` when that primitive vanishes at the cell endpoints. This is
applied below to the second and third Bernoulli polynomials. -/
private theorem integral_cell_primitive_three (f g : ℝ → ℝ) (hf : ∀ x, HasDerivAt f (3 * g x) x)
    (hg : Continuous g) (hf0 : f 0 = 0) (hf1 : f 1 = 0) (s : ℂ) (hs : s.re = 1 / 2) (n : ℕ)
    (hn : 1 ≤ n) :
    (∫ x in (n : ℝ)..((n : ℝ) + 1), (x : ℂ) ^ (-s - 2) * ((g (x - n) : ℝ) : ℂ)) =
      (s + 2) / 3 * ∫ x in (n : ℝ)..((n : ℝ) + 1), (x : ℂ) ^ (-s - 3) * ((f (x - n) : ℝ) : ℂ) := by
  let a : ℝ := n
  have ha : 0 < a := by
    dsimp only [a]
    exact_mod_cast Nat.lt_of_lt_of_le (by norm_num only : 0 < 1) hn
  have he : (-s - 2 : ℂ) ≠ 0 := by
    intro hz
    have hr := congrArg Complex.re hz
    simp only [Complex.sub_re, Complex.neg_re, Complex.re_ofNat, Complex.zero_re, hs] at hr
    norm_num only at hr
  have hpoint : ∀ x ∈ Set.uIcc a (a + 1), 0 < x := by
    intro x hx
    rw [Set.uIcc_of_le (le_add_of_nonneg_right (by norm_num only : (0 : ℝ) ≤ 1))] at hx
    exact lt_of_lt_of_le ha hx.1
  have hu (x : ℝ) (hx : x ∈ Set.uIcc a (a + 1)) :
    HasDerivAt (fun y : ℝ ↦ (y : ℂ) ^ (-s - 2)) ((-s - 2) * (x : ℂ) ^ (-s - 2 - 1)) x :=
    hasDerivAt_ofReal_cpow_const (ne_of_gt (hpoint x hx)) he
  have hv (x : ℝ) : HasDerivAt (fun y : ℝ ↦ ((f (y - a) / 3 : ℝ) : ℂ)) ((g (x - a) : ℝ) : ℂ) x := by
    have hh := ((hf (x - a)).comp x ((hasDerivAt_id x).sub_const a)).div_const 3
    have hh' : HasDerivAt (fun y : ℝ ↦ f (y - a) / 3) (g (x - a)) x := by
      convert hh using 1
      · rfl
      · ring
    exact hh'.ofReal_comp
  have huc : ContinuousOn (fun x : ℝ ↦ (-s - 2) * (x : ℂ) ^ (-s - 2 - 1)) (Set.uIcc a (a + 1)) := by
    apply ContinuousOn.const_mul
    intro x hx
    exact
      (Complex.continuousAt_ofReal_cpow_const x (-s - 2 - 1)
          (Or.inr (ne_of_gt (hpoint x hx)))).continuousWithinAt
  have hvc : Continuous (fun x : ℝ ↦ ((g (x - a) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (hg.comp (continuous_id.sub continuous_const))
  have h :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul hu (fun x _ ↦ hv x) huc.intervalIntegrable
      (hvc.intervalIntegrable a (a + 1))
  change (∫ x in a..a + 1, (x : ℂ) ^ (-s - 2) * ((g (x - a) : ℝ) : ℂ)) = _ at h
  have hv0 : ((f (a - a) / 3 : ℝ) : ℂ) = 0 := by
    rw [sub_self, hf0, zero_div]
    exact Complex.ofReal_zero
  have hv1 : ((f (a + 1 - a) / 3 : ℝ) : ℂ) = 0 := by
    rw [show a + 1 - a = 1 by ring, hf1, zero_div]
    exact Complex.ofReal_zero
  rw [hv0, hv1, mul_zero, mul_zero, sub_zero, zero_sub] at h
  have hfun :
    (fun x : ℝ ↦ ((-s - 2) * (x : ℂ) ^ (-s - 2 - 1)) * ((f (x - a) / 3 : ℝ) : ℂ)) = fun x : ℝ ↦
      (-(s + 2) / 3) * ((x : ℂ) ^ (-s - 3) * ((f (x - a) : ℝ) : ℂ)) := by
    funext x
    simp only [Complex.ofReal_div, Complex.ofReal_ofNat]
    have hex : (-s - 2 - 1 : ℂ) = -s - 3 := by ring
    rw [hex]
    ring
  rw [hfun, intervalIntegral.integral_const_mul] at h
  dsimp only [a] at h
  linear_combination h

/-- The second Bernoulli weight on a positive integer cell integrates by
parts to the third weight, with no boundary contribution. This is the first
step from the sawtooth remainder toward the eighth-order formula. -/
private theorem integral_bernoulli_two_cell (s : ℂ) (hs : s.re = 1 / 2) (n : ℕ) (hn : 1 ≤ n) :
    (∫ x in (n : ℝ)..((n : ℝ) + 1), (x : ℂ) ^ (-s - 2) * ((bernoulliTwo (x - n) : ℝ) : ℂ)) =
      (s + 2) / 3 *
        ∫ x in (n : ℝ)..((n : ℝ) + 1), (x : ℂ) ^ (-s - 3) * ((bernoulliThree (x - n) : ℝ) : ℂ) := by
  have hc : Continuous bernoulliTwo := by
    exact ((continuous_id.pow 2).sub continuous_id).add continuous_const
  exact
    integral_cell_primitive_three bernoulliThree bernoulliTwo hasDerivAt_bernoulli_three hc
      bernoulli_three_endpoints.1 bernoulli_three_endpoints.2 s hs n hn

/-- On an integer unit cell, a periodic weight and the same weight evaluated
at the translated coordinate agree inside the interval integral. The only
possible discrepancy occurs at an endpoint of measure zero. -/
private theorem integral_fract_eq_shift (f : ℝ → ℝ) (r : ℂ) (n : ℕ) :
    (∫ x in (n : ℝ)..((n : ℝ) + 1), (x : ℂ) ^ r * ((f (Int.fract x) : ℝ) : ℂ)) =
      ∫ x in (n : ℝ)..((n : ℝ) + 1), (x : ℂ) ^ r * ((f (x - n) : ℝ) : ℂ) := by
  apply intervalIntegral.integral_congr_ae
  rw [Set.uIoc_of_le (le_add_of_nonneg_right (by norm_num only : (0 : ℝ) ≤ 1))]
  filter_upwards [(MeasureTheory.Ioo_ae_eq_Ioc (μ := MeasureTheory.volume) (a := (n : ℝ)) (b :=
        (n : ℝ) + 1)).mem_iff] with
    x hx hxmem
  have hxo := hx.mpr hxmem
  have hxi : x ∈ Set.Ico ((n : ℤ) : ℝ) ((n : ℤ) + 1) := by
    simpa only [Int.cast_natCast, Int.cast_add, Int.cast_one] using
      (show x ∈ Set.Ico (n : ℝ) ((n : ℝ) + 1) from ⟨hxo.1.le, hxo.2⟩)
  have he : Int.fract x = x - n := by
    rw [← Int.self_sub_floor, Int.floor_eq_on_Ico (n : ℤ) x hxi]
    simp only [Int.cast_natCast]
  rw [he]

/-- A complex power times a continuous periodic weight is integrable on
every positive integer cell. On the cell it agrees almost everywhere with a
continuous translate of that weight. -/
private theorem intervalIntegrable_periodic_cell (f : ℝ → ℝ) (hf : Continuous f) (r : ℂ) (n : ℕ)
    (hn : 1 ≤ n) :
    IntervalIntegrable (fun x : ℝ ↦ (x : ℂ) ^ r * ((f (Int.fract x) : ℝ) : ℂ)) MeasureTheory.volume
      (n : ℝ) ((n : ℝ) + 1) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le (by norm_num only : 0 < 1) hn
  have hc : ContinuousOn (fun x : ℝ ↦ (x : ℂ) ^ r) (Set.Icc (n : ℝ) ((n : ℝ) + 1)) := by
    intro x hx
    exact
      (Complex.continuousAt_ofReal_cpow_const x r
          (Or.inr (ne_of_gt (lt_of_lt_of_le hn0 hx.1)))).continuousWithinAt
  have hp : Continuous (fun x : ℝ ↦ ((f (x - n) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (hf.comp (continuous_id.sub continuous_const))
  have hi :
    IntervalIntegrable (fun x : ℝ ↦ (x : ℂ) ^ r * ((f (x - n) : ℝ) : ℂ)) MeasureTheory.volume
      (n : ℝ) ((n : ℝ) + 1) := by
    apply
      ContinuousOn.intervalIntegrable_of_Icc
        (le_add_of_nonneg_right (by norm_num only : (0 : ℝ) ≤ 1))
    exact hc.mul hp.continuousOn
  apply hi.congr_ae
  apply (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr
  rw [Set.uIoc_of_le (le_add_of_nonneg_right (by norm_num only : (0 : ℝ) ≤ 1))]
  filter_upwards [(MeasureTheory.Ioo_ae_eq_Ioc (μ := MeasureTheory.volume) (a := (n : ℝ)) (b :=
        (n : ℝ) + 1)).mem_iff] with
    x hx hxmem
  have hxo := hx.mpr hxmem
  have hxi : x ∈ Set.Ico ((n : ℤ) : ℝ) ((n : ℤ) + 1) := by
    simpa only [Int.cast_natCast, Int.cast_add, Int.cast_one] using
      (show x ∈ Set.Ico (n : ℝ) ((n : ℝ) + 1) from ⟨hxo.1.le, hxo.2⟩)
  have he : Int.fract x = x - n := by
    rw [← Int.self_sub_floor, Int.floor_eq_on_Ico (n : ℤ) x hxi]
    simp only [Int.cast_natCast]
  rw [he]

/-- On a positive integer cell, integrating a power against `g` can be
integrated by parts using an explicit primitive `f/c`. This records the two
endpoint terms needed for the even Bernoulli polynomials. -/
private theorem integral_cell_primitive (f g : ℝ → ℝ) (c : ℝ) (hc : c ≠ 0)
    (hf : ∀ x, HasDerivAt f (c * g x) x) (hg : Continuous g) (r : ℂ) (hr : r ≠ 0) (n : ℕ)
    (hn : 1 ≤ n) :
    (∫ x in (n : ℝ)..((n : ℝ) + 1), (x : ℂ) ^ r * ((g (x - n) : ℝ) : ℂ)) =
      (((n : ℝ) + 1 : ℝ) : ℂ) ^ r * ((f 1 / c : ℝ) : ℂ) - (n : ℂ) ^ r * ((f 0 / c : ℝ) : ℂ) -
        r / (c : ℂ) * ∫ x in (n : ℝ)..((n : ℝ) + 1), (x : ℂ) ^ (r - 1) * ((f (x - n) : ℝ) : ℂ) := by
  let a : ℝ := n
  have ha : 0 < a := by
    dsimp only [a]
    exact_mod_cast Nat.lt_of_lt_of_le (by norm_num only : 0 < 1) hn
  have hpoint : ∀ x ∈ Set.uIcc a (a + 1), 0 < x := by
    intro x hx
    rw [Set.uIcc_of_le (le_add_of_nonneg_right (by norm_num only : (0 : ℝ) ≤ 1))] at hx
    exact lt_of_lt_of_le ha hx.1
  have hu (x : ℝ) (hx : x ∈ Set.uIcc a (a + 1)) :
    HasDerivAt (fun y : ℝ ↦ (y : ℂ) ^ r) (r * (x : ℂ) ^ (r - 1)) x :=
    hasDerivAt_ofReal_cpow_const (ne_of_gt (hpoint x hx)) hr
  have hv (x : ℝ) : HasDerivAt (fun y : ℝ ↦ ((f (y - a) / c : ℝ) : ℂ)) ((g (x - a) : ℝ) : ℂ) x := by
    have hh := ((hf (x - a)).comp x ((hasDerivAt_id x).sub_const a)).div_const c
    have hh' : HasDerivAt (fun y : ℝ ↦ f (y - a) / c) (g (x - a)) x := by
      convert hh using 1
      · rfl
      · simp only [mul_one, mul_div_cancel_left₀ _ hc]
    exact hh'.ofReal_comp
  have huc : ContinuousOn (fun x : ℝ ↦ r * (x : ℂ) ^ (r - 1)) (Set.uIcc a (a + 1)) := by
    apply ContinuousOn.const_mul
    intro x hx
    exact
      (Complex.continuousAt_ofReal_cpow_const x (r - 1)
          (Or.inr (ne_of_gt (hpoint x hx)))).continuousWithinAt
  have hvc : Continuous (fun x : ℝ ↦ ((g (x - a) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (hg.comp (continuous_id.sub continuous_const))
  have h :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul hu (fun x _ ↦ hv x) huc.intervalIntegrable
      (hvc.intervalIntegrable a (a + 1))
  change (∫ x in a..a + 1, (x : ℂ) ^ r * ((g (x - a) : ℝ) : ℂ)) = _ at h
  have he1 : a + 1 - a = 1 := by ring
  rw [he1, sub_self] at h
  have hfun :
    (fun x : ℝ ↦ (r * (x : ℂ) ^ (r - 1)) * ((f (x - a) / c : ℝ) : ℂ)) = fun x : ℝ ↦
      (r / (c : ℂ)) * ((x : ℂ) ^ (r - 1) * ((f (x - a) : ℝ) : ℂ)) := by
    funext x
    simp only [Complex.ofReal_div]
    ring
  rw [hfun, intervalIntegral.integral_const_mul] at h
  exact h

/-- The cellwise integration formula also holds for periodic weights. It
preserves both endpoint terms and is used for the fixed Bernoulli steps. -/
private theorem integral_periodic_primitive (f g : ℝ → ℝ) (c : ℝ) (hc : c ≠ 0)
    (hf : ∀ x, HasDerivAt f (c * g x) x) (hg : Continuous g) (r : ℂ) (hr : r ≠ 0) (n : ℕ)
    (hn : 1 ≤ n) :
    (∫ x in (n : ℝ)..((n : ℝ) + 1), (x : ℂ) ^ r * ((g (Int.fract x) : ℝ) : ℂ)) =
      (((n : ℝ) + 1 : ℝ) : ℂ) ^ r * ((f 1 / c : ℝ) : ℂ) - (n : ℂ) ^ r * ((f 0 / c : ℝ) : ℂ) -
        r / (c : ℂ) *
          ∫ x in (n : ℝ)..((n : ℝ) + 1), (x : ℂ) ^ (r - 1) * ((f (Int.fract x) : ℝ) : ℂ) := by
  rw [integral_fract_eq_shift g r n, integral_fract_eq_shift f (r - 1) n]
  exact integral_cell_primitive f g c hc hf hg r hr n hn

/-- A negative integer shift of a critical-line parameter is nonzero. This
supplies the complex-power derivative hypothesis at each fixed step. -/
private theorem critical_negative_shift_ne_zero {s : ℂ} (hs : s.re = 1 / 2) (m : ℕ) :
    (-s - m : ℂ) ≠ 0 := by
  intro hz
  have hr := congrArg Complex.re hz
  simp only [Complex.sub_re, Complex.neg_re, Complex.natCast_re, Complex.zero_re, hs] at hr
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  linarith only [hr, hm]

/-- When the primitive vanishes at both cell endpoints, the periodic
integration-by-parts formula has no boundary term. -/
private theorem integral_periodic_zero_primitive (f g : ℝ → ℝ) (c : ℝ) (hc : c ≠ 0)
    (hf : ∀ x, HasDerivAt f (c * g x) x) (hg : Continuous g) (hf0 : f 0 = 0) (hf1 : f 1 = 0) (r : ℂ)
    (hr : r ≠ 0) (n : ℕ) (hn : 1 ≤ n) :
    (∫ x in (n : ℝ)..((n : ℝ) + 1), (x : ℂ) ^ r * ((g (Int.fract x) : ℝ) : ℂ)) =
      -(r / (c : ℂ)) *
        ∫ x in (n : ℝ)..((n : ℝ) + 1), (x : ℂ) ^ (r - 1) * ((f (Int.fract x) : ℝ) : ℂ) := by
  have h := integral_periodic_primitive f g c hc hf hg r hr n hn
  simp only [hf0, hf1, zero_div, Complex.ofReal_zero, mul_zero, sub_zero, zero_sub] at h
  simpa only [neg_mul] using h

/-- On each positive integer cell, integration by parts moves the second
periodic Bernoulli weight to the third and raises the negative exponent by
one. The third polynomial vanishes at both cell endpoints. -/
private theorem integral_periodic_two_cell (s : ℂ) (hs : s.re = 1 / 2) (n : ℕ) (hn : 1 ≤ n) :
    (∫ x in (n : ℝ)..((n : ℝ) + 1), (x : ℂ) ^ (-s - 2) * ((bernoulliTwo (Int.fract x) : ℝ) : ℂ)) =
      (s + 2) / 3 *
        ∫ x in (n : ℝ)..((n : ℝ) + 1),
          (x : ℂ) ^ (-s - 3) * ((bernoulliThree (Int.fract x) : ℝ) : ℂ) := by
  rw [integral_fract_eq_shift bernoulliTwo (-s - 2) n,
    integral_fract_eq_shift bernoulliThree (-s - 3) n]
  exact integral_bernoulli_two_cell s hs n hn

/-- On each positive integer cell, the third periodic Bernoulli weight
integrates by parts to the fourth. Its equal endpoint values are retained
explicitly so that the boundary terms can telescope across cells. -/
private theorem integral_periodic_three_cell (s : ℂ) (hs : s.re = 1 / 2) (n : ℕ) (hn : 1 ≤ n) :
    (∫ x in (n : ℝ)..((n : ℝ) + 1), (x : ℂ) ^ (-s - 3) * ((bernoulliThree (Int.fract x) : ℝ) : ℂ)) =
      (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s - 3) * (((-1 / 30 : ℝ) / 4 : ℝ) : ℂ) -
        (n : ℂ) ^ (-s - 3) * (((-1 / 30 : ℝ) / 4 : ℝ) : ℂ) -
        (-s - 3) / (4 : ℂ) *
          ∫ x in (n : ℝ)..((n : ℝ) + 1),
            (x : ℂ) ^ (-s - 4) * ((bernoulliFour (Int.fract x) : ℝ) : ℂ) := by
  have hc : Continuous bernoulliThree := by
    exact
      (((continuous_id.pow 3).sub ((continuous_id.pow 2).const_mul (3 / 2))).add
        (continuous_id.const_mul (1 / 2)))
  have hr : (-s - 3 : ℂ) ≠ 0 := by
    intro hz
    have hr := congrArg Complex.re hz
    simp only [Complex.sub_re, Complex.neg_re, Complex.re_ofNat, Complex.zero_re, hs] at hr
    norm_num only at hr
  have h :=
    integral_cell_primitive bernoulliFour bernoulliThree 4 (by norm_num only)
      hasDerivAt_bernoulli_four hc (-s - 3) hr n hn
  rw [bernoulli_four_endpoints.1, bernoulli_four_endpoints.2] at h
  have he : (-s - 3 - 1 : ℂ) = -s - 4 := by ring
  rw [he] at h
  rw [integral_fract_eq_shift bernoulliThree (-s - 3) n,
    integral_fract_eq_shift bernoulliFour (-s - 4) n]
  exact h

/-- The eighth Bernoulli polynomial as an explicit real polynomial. Its
periodic evaluation supplies the remainder weight in the eighth-order
Euler–Maclaurin formula. -/
@[expose]
noncomputable def bernoulliEight (v : ℝ) : ℝ :=
  v ^ 8 - 4 * v ^ 7 + (14 / 3) * v ^ 6 - (7 / 3) * v ^ 4 + (2 / 3) * v ^ 2 - 1 / 30

/-- The eighth Bernoulli polynomial differentiates to eight times the
seventh, completing the fixed sequence of integration-by-parts primitives. -/
private theorem hasDerivAt_bernoulli_eight (x : ℝ) :
    HasDerivAt bernoulliEight (8 * bernoulliSeven x) x := by
  have h :=
    ((((((hasDerivAt_id x).pow 8).sub (((hasDerivAt_id x).pow 7).const_mul 4)).add
                  (((hasDerivAt_id x).pow 6).const_mul (14 / 3))).sub
              (((hasDerivAt_id x).pow 4).const_mul (7 / 3))).add
          (((hasDerivAt_id x).pow 2).const_mul (2 / 3))).sub_const
      (1 / 30)
  convert h using 1
  · funext v; rfl
  · simp only [bernoulliSeven, id_eq, Nat.cast_ofNat]
    ring

/-- The eighth Bernoulli polynomial has equal endpoint values `-1/30`. -/
private theorem bernoulli_eight_endpoints :
    bernoulliEight 0 = -1 / 30 ∧ bernoulliEight 1 = -1 / 30 := by
  constructor <;> norm_num only [bernoulliEight]

/-- The periodic fourth Bernoulli weight moves to the fifth on each
positive integer cell, with no boundary term. -/
private theorem integral_periodic_four_cell (s : ℂ) (hs : s.re = 1 / 2) (n : ℕ) (hn : 1 ≤ n) :
    (∫ x in (n : ℝ)..((n : ℝ) + 1), (x : ℂ) ^ (-s - 4) * ((bernoulliFour (Int.fract x) : ℝ) : ℂ)) =
      (s + 4) / 5 *
        ∫ x in (n : ℝ)..((n : ℝ) + 1),
          (x : ℂ) ^ (-s - 5) * ((bernoulliFive (Int.fract x) : ℝ) : ℂ) := by
  have hc : Continuous bernoulliFour :=
    continuous_iff_continuousAt.mpr (fun x ↦ (hasDerivAt_bernoulli_four x).continuousAt)
  have h :=
    integral_periodic_zero_primitive bernoulliFive bernoulliFour 5 (by norm_num only)
      hasDerivAt_bernoulli_five hc bernoulli_odd_endpoints.1.1 bernoulli_odd_endpoints.1.2 (-s - 4)
      (critical_negative_shift_ne_zero hs 4) n hn
  have he : (-s - 4 - 1 : ℂ) = -s - 5 := by ring
  have hk : -((-s - 4) / (5 : ℂ)) = (s + 4) / 5 := by ring
  simp only [Complex.ofReal_ofNat] at h
  rw [he, hk] at h
  exact h

/-- The periodic fifth Bernoulli weight moves to the sixth on each positive
integer cell, retaining the equal nonzero endpoint contributions. -/
private theorem integral_periodic_five_cell (s : ℂ) (hs : s.re = 1 / 2) (n : ℕ) (hn : 1 ≤ n) :
    (∫ x in (n : ℝ)..((n : ℝ) + 1), (x : ℂ) ^ (-s - 5) * ((bernoulliFive (Int.fract x) : ℝ) : ℂ)) =
      (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s - 5) * (((1 / 42 : ℝ) / 6 : ℝ) : ℂ) -
        (n : ℂ) ^ (-s - 5) * (((1 / 42 : ℝ) / 6 : ℝ) : ℂ) -
        (-s - 5) / (6 : ℂ) *
          ∫ x in (n : ℝ)..((n : ℝ) + 1),
            (x : ℂ) ^ (-s - 6) * ((bernoulliSix (Int.fract x) : ℝ) : ℂ) := by
  have hc : Continuous bernoulliFive :=
    continuous_iff_continuousAt.mpr (fun x ↦ (hasDerivAt_bernoulli_five x).continuousAt)
  have h :=
    integral_periodic_primitive bernoulliSix bernoulliFive 6 (by norm_num only)
      hasDerivAt_bernoulli_six hc (-s - 5) (critical_negative_shift_ne_zero hs 5) n hn
  rw [bernoulli_six_endpoints.1, bernoulli_six_endpoints.2] at h
  have he : (-s - 5 - 1 : ℂ) = -s - 6 := by ring
  rw [he] at h
  exact h

/-- The periodic sixth Bernoulli weight moves to the seventh on each
positive integer cell, with no boundary term. -/
private theorem integral_periodic_six_cell (s : ℂ) (hs : s.re = 1 / 2) (n : ℕ) (hn : 1 ≤ n) :
    (∫ x in (n : ℝ)..((n : ℝ) + 1), (x : ℂ) ^ (-s - 6) * ((bernoulliSix (Int.fract x) : ℝ) : ℂ)) =
      (s + 6) / 7 *
        ∫ x in (n : ℝ)..((n : ℝ) + 1),
          (x : ℂ) ^ (-s - 7) * ((bernoulliSeven (Int.fract x) : ℝ) : ℂ) := by
  have hc : Continuous bernoulliSix :=
    continuous_iff_continuousAt.mpr (fun x ↦ (hasDerivAt_bernoulli_six x).continuousAt)
  have h :=
    integral_periodic_zero_primitive bernoulliSeven bernoulliSix 7 (by norm_num only)
      hasDerivAt_bernoulli_seven hc bernoulli_odd_endpoints.2.1 bernoulli_odd_endpoints.2.2 (-s - 6)
      (critical_negative_shift_ne_zero hs 6) n hn
  have he : (-s - 6 - 1 : ℂ) = -s - 7 := by ring
  have hk : -((-s - 6) / (7 : ℂ)) = (s + 6) / 7 := by ring
  simp only [Complex.ofReal_ofNat] at h
  rw [he, hk] at h
  exact h

/-- The periodic seventh Bernoulli weight moves to the eighth on each
positive integer cell, retaining the equal nonzero endpoint contributions. -/
private theorem integral_periodic_seven_cell (s : ℂ) (hs : s.re = 1 / 2) (n : ℕ) (hn : 1 ≤ n) :
    (∫ x in (n : ℝ)..((n : ℝ) + 1), (x : ℂ) ^ (-s - 7) * ((bernoulliSeven (Int.fract x) : ℝ) : ℂ)) =
      (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s - 7) * (((-1 / 30 : ℝ) / 8 : ℝ) : ℂ) -
        (n : ℂ) ^ (-s - 7) * (((-1 / 30 : ℝ) / 8 : ℝ) : ℂ) -
        (-s - 7) / (8 : ℂ) *
          ∫ x in (n : ℝ)..((n : ℝ) + 1),
            (x : ℂ) ^ (-s - 8) * ((bernoulliEight (Int.fract x) : ℝ) : ℂ) := by
  have hc : Continuous bernoulliSeven :=
    continuous_iff_continuousAt.mpr (fun x ↦ (hasDerivAt_bernoulli_seven x).continuousAt)
  have h :=
    integral_periodic_primitive bernoulliEight bernoulliSeven 8 (by norm_num only)
      hasDerivAt_bernoulli_eight hc (-s - 7) (critical_negative_shift_ne_zero hs 7) n hn
  rw [bernoulli_eight_endpoints.1, bernoulli_eight_endpoints.2] at h
  have he : (-s - 7 - 1 : ℂ) = -s - 8 := by ring
  rw [he] at h
  exact h

/-- The difference of adjacent power terms multiplied by a fixed real
Bernoulli endpoint coefficient. These differences telescope when cells are
summed. -/
private noncomputable def emCellBoundary (r : ℂ) (c : ℝ) (n : ℕ) : ℂ :=
  (((n : ℝ) + 1 : ℝ) : ℂ) ^ r * (c : ℂ) - (n : ℂ) ^ r * (c : ℂ)

/-- Adjacent power-weighted periodic cell integrals sum to the integral over
the full finite interval. Each cell is integrable by continuity of the
underlying weight. -/
private theorem sum_periodic_cells (f : ℝ → ℝ) (hf : Continuous f) (r : ℂ) (N M : ℕ) (hN : 1 ≤ N)
    (hNM : N ≤ M) :
    (∑ n ∈ Finset.Ico N M,
        ∫ x in (n : ℝ)..((n : ℝ) + 1), (x : ℂ) ^ r * ((f (Int.fract x) : ℝ) : ℂ)) =
      ∫ x in (N : ℝ)..(M : ℝ), (x : ℂ) ^ r * ((f (Int.fract x) : ℝ) : ℂ) := by
  have h :=
    intervalIntegral.sum_integral_adjacent_intervals_Ico (a := fun n : ℕ ↦ (n : ℝ)) hNM
      (by
        intro n hn
        have hn1 : 1 ≤ n := le_trans hN hn.1
        simpa only [Nat.cast_add, Nat.cast_one] using intervalIntegrable_periodic_cell f hf r n hn1)
  simpa only [Nat.cast_add, Nat.cast_one] using h

/-- The Bernoulli endpoint differences telescope over adjacent integer
cells, leaving only the upper and lower endpoints of the finite interval. -/
private theorem sum_em_boundaries (r : ℂ) (c : ℝ) (N M : ℕ) (hNM : N ≤ M) :
    (∑ n ∈ Finset.Ico N M, emCellBoundary r c n) =
      (M : ℂ) ^ r * (c : ℂ) - (N : ℂ) ^ r * (c : ℂ) := by
  have h := Finset.sum_Ico_sub (fun n : ℕ ↦ (n : ℂ) ^ r * (c : ℂ)) hNM
  simpa only [emCellBoundary, Nat.cast_add, Nat.cast_one, Complex.ofReal_add,
    Complex.ofReal_natCast, Complex.ofReal_one] using h

/-- Six successive cellwise integrations by parts turn the second periodic
Bernoulli weight into the eighth. The fourth, sixth and eighth endpoint
differences are kept explicitly for telescoping over adjacent cells. -/
private theorem integral_two_to_eight_cell (s : ℂ) (hs : s.re = 1 / 2) (n : ℕ) (hn : 1 ≤ n) :
    (∫ x in (n : ℝ)..((n : ℝ) + 1), (x : ℂ) ^ (-s - 2) * ((bernoulliTwo (Int.fract x) : ℝ) : ℂ)) =
      (s + 2) / 3 *
        (emCellBoundary (-s - 3) ((-1 / 30 : ℝ) / 4) n +
          (s + 3) / 4 *
            ((s + 4) / 5 *
              (emCellBoundary (-s - 5) ((1 / 42 : ℝ) / 6) n +
                (s + 5) / 6 *
                  ((s + 6) / 7 *
                    (emCellBoundary (-s - 7) ((-1 / 30 : ℝ) / 8) n +
                      (s + 7) / 8 *
                        ∫ x in (n : ℝ)..((n : ℝ) + 1),
                          (x : ℂ) ^ (-s - 8) * ((bernoulliEight (Int.fract x) : ℝ) : ℂ)))))) := by
  rw [integral_periodic_two_cell s hs n hn, integral_periodic_three_cell s hs n hn,
    integral_periodic_four_cell s hs n hn, integral_periodic_five_cell s hs n hn,
    integral_periodic_six_cell s hs n hn, integral_periodic_seven_cell s hs n hn]
  dsimp only [emCellBoundary]
  ring

/-- Summing the six integration-by-parts steps over a finite range of
positive integer cells leaves three telescoped endpoint differences and the
integral with the eighth periodic Bernoulli weight. -/
private theorem integral_two_to_eight_finite (s : ℂ) (hs : s.re = 1 / 2) (N M : ℕ) (hN : 1 ≤ N)
    (hNM : N ≤ M) :
    (∫ x in (N : ℝ)..(M : ℝ), (x : ℂ) ^ (-s - 2) * ((bernoulliTwo (Int.fract x) : ℝ) : ℂ)) =
      (s + 2) / 3 *
        (((M : ℂ) ^ (-s - 3) * (((-1 / 30 : ℝ) / 4 : ℝ) : ℂ) -
            (N : ℂ) ^ (-s - 3) * (((-1 / 30 : ℝ) / 4 : ℝ) : ℂ)) +
          (s + 3) / 4 *
            ((s + 4) / 5 *
              (((M : ℂ) ^ (-s - 5) * (((1 / 42 : ℝ) / 6 : ℝ) : ℂ) -
                  (N : ℂ) ^ (-s - 5) * (((1 / 42 : ℝ) / 6 : ℝ) : ℂ)) +
                (s + 5) / 6 *
                  ((s + 6) / 7 *
                    (((M : ℂ) ^ (-s - 7) * (((-1 / 30 : ℝ) / 8 : ℝ) : ℂ) -
                        (N : ℂ) ^ (-s - 7) * (((-1 / 30 : ℝ) / 8 : ℝ) : ℂ)) +
                      (s + 7) / 8 *
                        ∫ x in (N : ℝ)..(M : ℝ),
                          (x : ℂ) ^ (-s - 8) * ((bernoulliEight (Int.fract x) : ℝ) : ℂ)))))) := by
  have h2 : Continuous bernoulliTwo := by
    exact ((continuous_id.pow 2).sub continuous_id).add continuous_const
  have h8 : Continuous bernoulliEight :=
    continuous_iff_continuousAt.mpr (fun x ↦ (hasDerivAt_bernoulli_eight x).continuousAt)
  have hsum :=
    Finset.sum_congr (s₁ := Finset.Ico N M) (s₂ := Finset.Ico N M) rfl
      (fun n hn ↦ integral_two_to_eight_cell s hs n (le_trans hN (Finset.mem_Ico.mp hn).1))
  simp only [← Finset.mul_sum, Finset.sum_add_distrib] at hsum
  rw [sum_periodic_cells bernoulliTwo h2 (-s - 2) N M hN hNM,
    sum_periodic_cells bernoulliEight h8 (-s - 8) N M hN hNM,
    sum_em_boundaries (-s - 3) ((-1 / 30 : ℝ) / 4) N M hNM,
    sum_em_boundaries (-s - 5) ((1 / 42 : ℝ) / 6) N M hNM,
    sum_em_boundaries (-s - 7) ((-1 / 30 : ℝ) / 8) N M hNM] at hsum
  exact hsum

/-- For a negative critical-line shift, an upper endpoint power tends to
zero as the integer endpoint tends to infinity. A fixed lower endpoint remains
in the limit. -/
private theorem tendsto_em_boundary {s : ℂ} (hs : s.re = 1 / 2) (k : ℕ) (c : ℂ) :
    Filter.Tendsto (fun M : ℕ ↦ (M : ℂ) ^ (-s - k) * c - (128 : ℂ) ^ (-s - k) * c) Filter.atTop
      (nhds (-((128 : ℂ) ^ (-s - k) * c))) := by
  have hr : (-s - k : ℂ).re < 0 := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.natCast_re, hs]
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    linarith only [hk]
  have h := (tendsto_natCast_cpow_atTop_zero hr).mul_const c
  simpa only [zero_mul, zero_sub] using h.sub_const ((128 : ℂ) ^ (-s - k) * c)

/-- On the unit interval the eighth Bernoulli polynomial has absolute value
at most `1/30`. Rewriting it in `u = v(1-v)` reduces the bound to polynomial
inequalities on `0 ≤ u ≤ 1/4`. -/
theorem abs_bernoulli_eight_le {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    |bernoulliEight v| ≤ 1 / 30 := by
  let u := v * (1 - v)
  have hu0 : 0 ≤ u := mul_nonneg hv0 (sub_nonneg.mpr hv1)
  have hu1 : u ≤ 1 / 4 := by
    dsimp only [u]
    nlinarith only [sq_nonneg (v - 1 / 2)]
  have h2 := pow_le_pow_left₀ hu0 hu1 2
  have h3 := pow_le_pow_left₀ hu0 hu1 3
  have h4 := pow_le_pow_left₀ hu0 hu1 4
  have hp2 : 0 ≤ u ^ 2 := pow_nonneg hu0 _
  have hp3 : 0 ≤ u ^ 3 := pow_nonneg hu0 _
  have hp4 : 0 ≤ u ^ 4 := pow_nonneg hu0 _
  have hb : |u ^ 4 + (4 / 3) * u ^ 3 + (2 / 3) * u ^ 2 - 1 / 30| ≤ 1 / 30 := by
    apply abs_le.mpr
    constructor <;> nlinarith only [h2, h3, h4, hp2, hp3, hp4]
  have he : bernoulliEight v = u ^ 4 + (4 / 3) * u ^ 3 + (2 / 3) * u ^ 2 - 1 / 30 := by
    dsimp only [bernoulliEight, u]
    ring
  rw [he]
  exact hb

/-- The periodic eighth Bernoulli weight is bounded by `1/30` on the real
line. The fractional part lies in the unit interval, so the polynomial bound
applies pointwise to the future Euler–Maclaurin remainder integral. -/
theorem abs_periodic_bernoulli_eight_le (v : ℝ) : |bernoulliEight (Int.fract v)| ≤ 1 / 30 := by
  exact abs_bernoulli_eight_le (Int.fract_nonneg v) (Int.fract_lt_one v).le

/-- The periodic eighth Bernoulli weight is measurable. Its polynomial
expression is built from the measurable fractional-part function. -/
theorem measurable_periodic_bernoulli_eight :
    Measurable (fun v : ℝ ↦ bernoulliEight (Int.fract v)) := by
  have h : Measurable (Int.fract : ℝ → ℝ) := measurable_fract
  change
    Measurable
      (fun v : ℝ ↦
        (Int.fract v) ^ 8 - 4 * (Int.fract v) ^ 7 + (14 / 3) * (Int.fract v) ^ 6 -
              (7 / 3) * (Int.fract v) ^ 4 +
            (2 / 3) * (Int.fract v) ^ 2 -
          1 / 30)
  exact
    (((((h.pow_const 8).sub ((h.pow_const 7).const_mul 4)).add
                  ((h.pow_const 6).const_mul (14 / 3))).sub
              ((h.pow_const 4).const_mul (7 / 3))).add
          ((h.pow_const 2).const_mul (2 / 3))).sub_const
      (1 / 30)

/-- On the critical line, the eighth-order periodic Bernoulli remainder
integrand is absolutely integrable from 128 to infinity. The majorant is
`t^(-17/2) / 30`. -/
theorem integrable_em8_tail {s : ℂ} (hs : s.re = 1 / 2) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ ↦ (t : ℂ) ^ (-s - 8) * ((bernoulliEight (Int.fract t) : ℝ) : ℂ))
      (Set.Ioi (128 : ℝ)) := by
  have hd :
    MeasureTheory.IntegrableOn (fun t : ℝ ↦ (1 / 30 : ℝ) * t ^ (-(17 / 2 : ℝ)))
      (Set.Ioi (128 : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num only) (by norm_num only)).const_mul _
  refine MeasureTheory.Integrable.mono' hd ?_ ?_
  · have hc : ContinuousOn (fun t : ℝ ↦ (t : ℂ) ^ (-s - 8)) (Set.Ioi (128 : ℝ)) := by
      intro y hy
      have hy0 : 0 < y := lt_trans (by norm_num only) hy
      exact
        (Complex.continuousAt_ofReal_cpow_const y (-s - 8)
            (Or.inr (ne_of_gt hy0))).continuousWithinAt
    have h1 :
      MeasureTheory.AEStronglyMeasurable (fun t : ℝ ↦ (t : ℂ) ^ (-s - 8))
        (MeasureTheory.volume.restrict (Set.Ioi (128 : ℝ))) :=
      hc.aestronglyMeasurable measurableSet_Ioi
    have h2 :
      MeasureTheory.AEStronglyMeasurable (fun t : ℝ ↦ ((bernoulliEight (Int.fract t) : ℝ) : ℂ))
        (MeasureTheory.volume.restrict (Set.Ioi (128 : ℝ))) :=
      (Complex.continuous_ofReal.measurable.comp
          measurable_periodic_bernoulli_eight).aestronglyMeasurable
    exact h1.mul h2
  · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans (by norm_num only) ht
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.norm_real, Real.norm_eq_abs]
    have he : (-s - 8).re = -(17 / 2 : ℝ) := by
      simp only [Complex.sub_re, Complex.neg_re, Complex.re_ofNat, hs]
      norm_num only
    rw [he]
    have hb := abs_periodic_bernoulli_eight_le t
    have hp := Real.rpow_nonneg ht0.le (-(17 / 2 : ℝ))
    nlinarith only [hb, hp, abs_nonneg (bernoulliEight (Int.fract t))]

/-- The periodic second Bernoulli tail from 128 equals the three lower
endpoint corrections and the eighth Bernoulli tail. The finite-cell identity
is passed to infinity using absolute integrability and vanishing upper powers. -/
private theorem integral_two_to_eight_tail (s : ℂ) (hs : s.re = 1 / 2) :
    (∫ x in Set.Ioi (128 : ℝ), (x : ℂ) ^ (-s - 2) * ((bernoulliTwo (Int.fract x) : ℝ) : ℂ)) =
      (s + 2) / 3 *
        (-(128 : ℂ) ^ (-s - 3) * (((-1 / 30 : ℝ) / 4 : ℝ) : ℂ) +
          (s + 3) / 4 *
            ((s + 4) / 5 *
              (-(128 : ℂ) ^ (-s - 5) * (((1 / 42 : ℝ) / 6 : ℝ) : ℂ) +
                (s + 5) / 6 *
                  ((s + 6) / 7 *
                    (-(128 : ℂ) ^ (-s - 7) * (((-1 / 30 : ℝ) / 8 : ℝ) : ℂ) +
                      (s + 7) / 8 *
                        ∫ x in Set.Ioi (128 : ℝ),
                          (x : ℂ) ^ (-s - 8) * ((bernoulliEight (Int.fract x) : ℝ) : ℂ)))))) := by
  have h2 :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi 128 (integrable_em2_tail hs)
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have h8 :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi 128 (integrable_em8_tail hs)
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hb4 := tendsto_em_boundary hs 3 (((-1 / 30 : ℝ) / 4 : ℝ) : ℂ)
  have hb6 := tendsto_em_boundary hs 5 (((1 / 42 : ℝ) / 6 : ℝ) : ℂ)
  have hb8 := tendsto_em_boundary hs 7 (((-1 / 30 : ℝ) / 8 : ℝ) : ℂ)
  simp only [Nat.cast_ofNat] at hb4 hb6 hb8
  have hr8 := (hb8.add (h8.const_mul ((s + 7) / 8))).const_mul ((s + 6) / 7)
  have hr6 := (hb6.add (hr8.const_mul ((s + 5) / 6))).const_mul ((s + 4) / 5)
  have hr := (hb4.add (hr6.const_mul ((s + 3) / 4))).const_mul ((s + 2) / 3)
  have hevent : ∀ᶠ M : ℕ in Filter.atTop, 128 ≤ M := Filter.eventually_ge_atTop 128
  have heq :=
    hevent.mono (fun M hM ↦ (integral_two_to_eight_finite s hs 128 M (by norm_num only) hM).symm)
  have hresult := tendsto_nhds_unique h2 (hr.congr' heq)
  simpa only [neg_mul] using hresult

/-- The original sawtooth tail equals one half of the second Bernoulli tail
minus one twelfth of the pure complex-power tail. Both terms are integrable
on the critical line. -/
private theorem sawtooth_tail_eq_bernoulli (s : ℂ) (hs : s.re = 1 / 2) :
    (∫ x in Set.Ioi (128 : ℝ), (x : ℂ) ^ (-s - 2) * ((zetaSawtooth x : ℝ) : ℂ)) =
      ((∫ x in Set.Ioi (128 : ℝ), (x : ℂ) ^ (-s - 2) * ((bernoulliTwo (Int.fract x) : ℝ) : ℂ)) -
          (∫ x in Set.Ioi (128 : ℝ), (x : ℂ) ^ (-s - 2)) * (1 / 6 : ℂ)) /
        2 := by
  have hre : (-s - 2 : ℂ).re < -1 := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.re_ofNat, hs]
    norm_num only
  have hp := integrableOn_Ioi_cpow_of_lt hre (by norm_num only : (0 : ℝ) < 128)
  have he :
    (fun x : ℝ ↦ (x : ℂ) ^ (-s - 2) * ((zetaSawtooth x : ℝ) : ℂ)) =
      (fun x : ℝ ↦
        ((x : ℂ) ^ (-s - 2) * ((bernoulliTwo (Int.fract x) : ℝ) : ℂ) -
            (x : ℂ) ^ (-s - 2) * (1 / 6 : ℂ)) /
          2) := by
    funext x
    rw [sawtooth_eq_bernoulli_two]
    simp only [Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_ofNat]
    ring
  rw [he, MeasureTheory.integral_div,
    MeasureTheory.integral_sub (integrable_em2_tail hs) (hp.mul_const _),
    MeasureTheory.integral_mul_const]

/-- The pure power tail occurring in the sawtooth decomposition cancels
against `s + 1` on the critical line, leaving the first Euler–Maclaurin
endpoint correction. -/
private theorem cpow_tail_cancellation (s : ℂ) (hs : s.re = 1 / 2) :
    (s + 1) * (∫ x in Set.Ioi (128 : ℝ), (x : ℂ) ^ (-s - 2)) = (128 : ℂ) ^ (-s - 1) := by
  have hr : (-s - 2 : ℂ).re < -1 := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.re_ofNat, hs]
    norm_num only
  have hs1 : s + 1 ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re, hs] at hh
    norm_num only at hh
  rw [integral_Ioi_cpow_of_lt hr (by norm_num only : (0 : ℝ) < 128)]
  simp only [Complex.ofReal_ofNat]
  have he : (-s - 2 + 1 : ℂ) = -s - 1 := by ring
  have hd : (-s - 1 : ℂ) = -(s + 1) := by ring
  rw [he, hd, div_neg, neg_div, neg_neg]
  exact mul_div_cancel₀ _ hs1

/-- The 128-cutoff Euler–Maclaurin approximation on the critical line with
four Bernoulli corrections. The powers are written separately so the exact
tail identity follows directly from the telescoped endpoint terms. -/
@[expose]
noncomputable def finiteEM8 (t : ℝ) : ℂ :=
  let s : ℂ := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I
  (∑ k ∈ Finset.Icc (1 : ℕ) 127, (k : ℂ) ^ (-s)) + (128 : ℂ) ^ (1 - s) / (s - 1) +
          (128 : ℂ) ^ (-s) / 2 +
          s * (128 : ℂ) ^ (-s - 1) / 12 -
        (s * (s + 1) * (s + 2)) * (128 : ℂ) ^ (-s - 3) / 720 +
      (s * (s + 1) * (s + 2) * (s + 3) * (s + 4)) * (128 : ℂ) ^ (-s - 5) / 30240 -
    (s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6)) * (128 : ℂ) ^ (-s - 7) / 1209600

/-- The coefficient of `128^(-(1/2+it))` in the grouped four-correction
Euler–Maclaurin approximation. It is a rational expression in the critical
parameter and can be evaluated using rational arithmetic at rational heights. -/
@[expose]
noncomputable def finiteEM8Coefficient (t : ℝ) : ℂ :=
  let s : ℂ := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I
  128 / (s - 1) + 1 / 2 + s / (12 * 128) - s * (s + 1) * (s + 2) / (720 * 128 ^ 3) +
      s * (s + 1) * (s + 2) * (s + 3) * (s + 4) / (30240 * 128 ^ 5) -
    s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6) / (1209600 * 128 ^ 7)

/-- The finite approximation is the sum of 127 powers plus one power at
128 multiplied by the grouped rational coefficient. The identity uses the
complex-power addition law at the positive nonzero base 128. -/
theorem finiteEM8_eq_grouped (t : ℝ) :
    finiteEM8 t =
      (∑ k ∈ Finset.Icc (1 : ℕ) 127, (k : ℂ) ^ (-((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)))) +
        finiteEM8Coefficient t * (128 : ℂ) ^ (-((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))) := by
  let s : ℂ := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I
  have hshift (k : ℕ) : (128 : ℂ) ^ (-s - k) = (128 : ℂ) ^ (-s) / (128 : ℂ) ^ k := by
    rw [Complex.cpow_sub _ _ (by norm_num only), Complex.cpow_natCast]
  have hpole : (128 : ℂ) ^ (1 - s) = (128 : ℂ) ^ (-s) * 128 := by
    have he : (1 - s : ℂ) = -s + 1 := by ring
    rw [he, Complex.cpow_add _ _ (by norm_num only), Complex.cpow_one]
  change
    (∑ k ∈ Finset.Icc (1 : ℕ) 127, (k : ℂ) ^ (-s)) + (128 : ℂ) ^ (1 - s) / (s - 1) +
              (128 : ℂ) ^ (-s) / 2 +
              s * (128 : ℂ) ^ (-s - 1) / 12 -
            (s * (s + 1) * (s + 2)) * (128 : ℂ) ^ (-s - 3) / 720 +
          (s * (s + 1) * (s + 2) * (s + 3) * (s + 4)) * (128 : ℂ) ^ (-s - 5) / 30240 -
        (s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6)) * (128 : ℂ) ^ (-s - 7) /
          1209600 =
      _
  have h1 := hshift 1
  have h3 := hshift 3
  have h5 := hshift 5
  have h7 := hshift 7
  norm_num only [Nat.cast_one, Nat.cast_ofNat] at h1 h3 h5 h7
  rw [hpole, h1, h3, h5, h7]
  dsimp only [finiteEM8Coefficient]
  ring

/-- For every real height, zeta equals the four-correction finite
Euler–Maclaurin expression minus its eighth Bernoulli tail. The identity is
obtained from the existing sawtooth formula by six cellwise integrations and
the limit of their telescoping endpoint terms. -/
theorem zeta_eq_finiteEM8 (t : ℝ) :
    riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) =
      finiteEM8 t -
        ((∏ j ∈ Finset.range 8, ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) + j)) / (40320 : ℂ)) *
          ∫ x in Set.Ioi (128 : ℝ),
            (x : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) - 8) *
              ((bernoulliEight (Int.fract x) : ℝ) : ℂ) := by
  let s : ℂ := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I
  have hs : s.re = 1 / 2 := by
    simp only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hs
    norm_num only at hs
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hs
    norm_num only at hs
  have hb := zeta_eq_finite_128 (by linarith only [hs]) hs0 hs1
  have hj := cpow_tail_cancellation s hs
  change
    riemannZeta s =
      finiteEM8 t -
        ((∏ j ∈ Finset.range 8, (s + j)) / (40320 : ℂ)) *
          ∫ x in Set.Ioi (128 : ℝ), (x : ℂ) ^ (-s - 8) * ((bernoulliEight (Int.fract x) : ℝ) : ℂ)
  have hf :
    finiteEM8 t =
      (∑ k ∈ Finset.Icc (1 : ℕ) 127, (k : ℂ) ^ (-s)) + (128 : ℂ) ^ (1 - s) / (s - 1) +
              (128 : ℂ) ^ (-s) / 2 +
              s * (128 : ℂ) ^ (-s - 1) / 12 -
            (s * (s + 1) * (s + 2)) * (128 : ℂ) ^ (-s - 3) / 720 +
          (s * (s + 1) * (s + 2) * (s + 3) * (s + 4)) * (128 : ℂ) ^ (-s - 5) / 30240 -
        (s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6)) * (128 : ℂ) ^ (-s - 7) /
          1209600 :=
    rfl
  rw [hb, hf, sawtooth_tail_eq_bernoulli s hs, integral_two_to_eight_tail s hs]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_ofNat, Nat.cast_zero,
    add_zero, one_mul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  simp only [Complex.ofReal_neg, Complex.ofReal_one, Nat.cast_one]
  linear_combination (s / 12) * hj

/-- The norm of the eighth-order tail integral is bounded by the integral of
the explicit `t^(-17/2) / 30` majorant on the critical line. -/
private theorem norm_em8_tail_le_integral {s : ℂ} (hs : s.re = 1 / 2) :
    ‖∫ t in Set.Ioi (128 : ℝ), (t : ℂ) ^ (-s - 8) * ((bernoulliEight (Int.fract t) : ℝ) : ℂ)‖ ≤
      ∫ t in Set.Ioi (128 : ℝ), (1 / 30 : ℝ) * t ^ (-(17 / 2 : ℝ)) := by
  have hd :
    MeasureTheory.IntegrableOn (fun t : ℝ ↦ (1 / 30 : ℝ) * t ^ (-(17 / 2 : ℝ)))
      (Set.Ioi (128 : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num only) (by norm_num only)).const_mul _
  apply (MeasureTheory.norm_integral_le_integral_norm _).trans
  apply MeasureTheory.integral_mono_of_nonneg
  · filter_upwards with t using norm_nonneg _
  · exact hd
  · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans (by norm_num only) ht
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.norm_real, Real.norm_eq_abs]
    have he : (-s - 8).re = -(17 / 2 : ℝ) := by
      simp only [Complex.sub_re, Complex.neg_re, Complex.re_ofNat, hs]
      norm_num only
    rw [he]
    have hb := abs_periodic_bernoulli_eight_le t
    have hp := Real.rpow_nonneg ht0.le (-(17 / 2 : ℝ))
    nlinarith only [hb, hp, abs_nonneg (bernoulliEight (Int.fract t))]

/-- Integrating the eighth-order power majorant from 128 gives at most the
explicit rational bound obtained from `sqrt 128 ≥ 11`. -/
private theorem em8_integral_majorant_le :
    (∫ t in Set.Ioi (128 : ℝ), (1 / 30 : ℝ) * t ^ (-(17 / 2 : ℝ))) ≤
      1 / (30 * (15 / 2) * 128 ^ 7 * 11) := by
  have hs : (11 : ℝ) ≤ Real.sqrt 128 :=
    (Real.le_sqrt (by norm_num only) (by norm_num only)).2 (by norm_num only)
  have hp : (128 : ℝ) ^ 7 * 11 ≤ (128 : ℝ) ^ (15 / 2 : ℝ) := by
    have he : (15 / 2 : ℝ) = 7 + 1 / 2 := by norm_num only
    rw [he, Real.rpow_add (by norm_num only), Real.rpow_ofNat, ← Real.sqrt_eq_rpow]
    exact mul_le_mul_of_nonneg_left hs (pow_nonneg (by norm_num only) _)
  have hp0 : 0 < (128 : ℝ) ^ 7 * 11 := by norm_num only
  have hi : ((128 : ℝ) ^ (15 / 2 : ℝ))⁻¹ ≤ ((128 : ℝ) ^ 7 * 11)⁻¹ :=
    (inv_le_inv₀ (lt_of_lt_of_le hp0 hp) hp0).2 hp
  have he :
    (1 / (30 * (15 / 2) * 128 ^ 7 * 11) : ℝ) = (1 / 30) * (((128 : ℝ) ^ 7 * 11)⁻¹ / (15 / 2)) := by
    norm_num only
  rw [he, MeasureTheory.integral_const_mul,
    integral_Ioi_rpow_of_lt (by norm_num only) (by norm_num only : (0 : ℝ) < 128)]
  simp only [show (-(17 / 2 : ℝ)) + 1 = -(15 / 2 : ℝ) by norm_num only,
    Real.rpow_neg (show (0 : ℝ) ≤ 128 by norm_num only), div_neg, neg_div, neg_neg]
  exact
    mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hi (show (0 : ℝ) ≤ 15 / 2 by norm_num only))
      (show (0 : ℝ) ≤ 1 / 30 by norm_num only)

/-- On the critical line, the eighth-order Bernoulli tail integral from 128
is bounded by an explicit rational constant. This is the analytic tail bound
needed after the finite Euler–Maclaurin identity is established. -/
theorem norm_em8_tail_le {s : ℂ} (hs : s.re = 1 / 2) :
    ‖∫ t in Set.Ioi (128 : ℝ), (t : ℂ) ^ (-s - 8) * ((bernoulliEight (Int.fract t) : ℝ) : ℂ)‖ ≤
      1 / (30 * (15 / 2) * 128 ^ 7 * 11) := by
  exact (norm_em8_tail_le_integral hs).trans em8_integral_majorant_le

/-- For `0 ≤ t ≤ 100` and `j ≤ 7`, each factor `1/2 + it + j` has norm
at most 101. Squaring the norm uses the sharper coordinate bounds rather than
the sum of absolute values. -/
theorem norm_critical_shift_le (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 100) (j : ℕ) (hj : j ≤ 7) :
    ‖(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) + j‖ ≤ 101 := by
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hj1 : (j : ℝ) ≤ 7 := by exact_mod_cast hj
  have hn := Complex.sq_norm ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) + j)
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.natCast_re, Complex.natCast_im, mul_zero, mul_one, sub_zero, add_zero, zero_add] at hn
  have ht2 : t ^ 2 ≤ 100 ^ 2 := pow_le_pow_left₀ ht0 ht 2
  have hj2 : ((j : ℝ) + 1 / 2) ^ 2 ≤ (15 / 2 : ℝ) ^ 2 := by
    apply pow_le_pow_left₀
    · linarith only [hj0]
    · linarith only [hj1]
  have hn0 := norm_nonneg ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) + j)
  nlinarith only [hn, ht2, hj2, hn0]

/-- For `0 ≤ t ≤ 100` and `n ≤ 8`, the first `n` rising factors on the critical line have
product norm at most `101^n`. Each factor is bounded separately, giving a common estimate for
the correction terms and the remainder. -/
theorem norm_critical_rising_le (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 100) (n : ℕ) (hn : n ≤ 8) :
    ‖∏ j ∈ Finset.range n, ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) + j)‖ ≤ (101 : ℝ) ^ n := by
  rw [norm_prod]
  calc
    _ ≤ ∏ _j ∈ Finset.range n, (101 : ℝ) := by
      apply Finset.prod_le_prod₀
      · intro j hj
        exact norm_nonneg _
      · intro j hj
        exact
          norm_critical_shift_le t ht0 ht j
            (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (Finset.mem_range.mp hj) hn))
    _ = _ := by simp only [Finset.prod_const, Finset.card_range]

/-- The eight rising factors in the eighth-order remainder at a critical
height `0 ≤ t ≤ 100` have product norm at most `101^8`. -/
theorem norm_critical_rising_eight_le (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 100) :
    ‖∏ j ∈ Finset.range 8, ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) + j)‖ ≤ (101 : ℝ) ^ 8 := by
  rw [norm_prod]
  calc
    _ ≤ ∏ _j ∈ Finset.range 8, (101 : ℝ) := by
      apply Finset.prod_le_prod₀
      · intro j hj
        exact norm_nonneg _
      · intro j hj
        exact norm_critical_shift_le t ht0 ht j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
    _ = _ := by simp only [Finset.prod_const, Finset.card_range]

/-- For `0 ≤ t ≤ 100`, the entire eighth-order Euler–Maclaurin tail at
cutoff 128, including its rising-factorial coefficient, has norm strictly
below `1/5000000`. The finite identity connecting this tail to zeta is a
separate requirement. -/
theorem norm_em8_remainder_lt (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 100) :
    ‖(∏ j ∈ Finset.range 8, ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) + j)) / (40320 : ℂ) *
          (∫ x in Set.Ioi (128 : ℝ),
            (x : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) - 8) *
              ((bernoulliEight (Int.fract x) : ℝ) : ℂ))‖ <
      1 / 5000000 := by
  have hs : ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) : ℂ).re = 1 / 2 := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hfac := norm_critical_rising_eight_le t ht0 ht
  have hi := norm_em8_tail_le hs
  rw [norm_mul, norm_div, Complex.norm_ofNat]
  have hd := div_le_div_of_nonneg_right hfac (show (0 : ℝ) ≤ 40320 by norm_num only)
  have hb := mul_le_mul hd hi (norm_nonneg _) (by norm_num only : (0 : ℝ) ≤ 101 ^ 8 / 40320)
  have hn : (101 : ℝ) ^ 8 / 40320 * (1 / (30 * (15 / 2) * 128 ^ 7 * 11)) < 1 / 5000000 := by
    norm_num only
  exact hb.trans_lt hn

/-- For `0 ≤ t ≤ 100`, the four-correction Euler–Maclaurin approximation
at cutoff 128 differs from zeta on the critical line by at most `1/5000000`.
The equality with the eighth Bernoulli remainder and its norm bound are both
proved internally. -/
theorem norm_zeta_sub_finiteEM8_le (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 100) :
    ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) - finiteEM8 t‖ ≤ 1 / 5000000 := by
  rw [zeta_eq_finiteEM8, sub_sub_cancel_left, norm_neg]
  exact (norm_em8_remainder_lt t ht0 ht).le

/-- The rational majorant obtained after bounding the eighth-order remainder
at cutoff 128 is strictly less than the required error budget. -/
theorem em8_rational_remainder_lt :
    (101 : ℝ) ^ 8 / (1209600 * (15 / 2) * 128 ^ 7 * 11) < 1 / 5000000 := by norm_num only

private theorem norm_em8_coefficient_aux (s : ℂ) (hp : ‖(128 : ℂ) / (s - 1)‖ ≤ (128 : ℝ) / 14)
    (h1 : ‖s‖ ≤ 101) (h3 : ‖s * (s + 1) * (s + 2)‖ ≤ (101 : ℝ) ^ 3)
    (h5 : ‖s * (s + 1) * (s + 2) * (s + 3) * (s + 4)‖ ≤ (101 : ℝ) ^ 5)
    (h7 : ‖s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6)‖ ≤ (101 : ℝ) ^ 7) :
    ‖128 / (s - 1) + 1 / 2 + s / (12 * 128) - s * (s + 1) * (s + 2) / (720 * 128 ^ 3) +
            s * (s + 1) * (s + 2) * (s + 3) * (s + 4) / (30240 * 128 ^ 5) -
          s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6) / (1209600 * 128 ^ 7)‖ ≤
      10 := by
  have ha := norm_add_le ((128 : ℂ) / (s - 1)) (1 / 2)
  have hb := norm_add_le ((128 : ℂ) / (s - 1) + 1 / 2) (s / (12 * 128))
  have hc :=
    norm_sub_le ((128 : ℂ) / (s - 1) + 1 / 2 + s / (12 * 128))
      (s * (s + 1) * (s + 2) / (720 * 128 ^ 3))
  have hd :=
    norm_add_le
      ((128 : ℂ) / (s - 1) + 1 / 2 + s / (12 * 128) - s * (s + 1) * (s + 2) / (720 * 128 ^ 3))
      (s * (s + 1) * (s + 2) * (s + 3) * (s + 4) / (30240 * 128 ^ 5))
  have he :=
    norm_sub_le
      ((128 : ℂ) / (s - 1) + 1 / 2 + s / (12 * 128) - s * (s + 1) * (s + 2) / (720 * 128 ^ 3) +
        s * (s + 1) * (s + 2) * (s + 3) * (s + 4) / (30240 * 128 ^ 5))
      (s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6) / (1209600 * 128 ^ 7))
  norm_num only [norm_div, norm_one, Complex.norm_ofNat, norm_mul, norm_pow] at hp h1 h3 h5 h7
  norm_num only [norm_div, norm_one, Complex.norm_ofNat, norm_mul, norm_pow] at ha hb hc hd he ⊢
  linarith only [hp, h1, h3, h5, h7, ha, hb, hc, hd, he]

/-- For `14 ≤ t ≤ 100`, the grouped correction coefficient has norm at most 10. The pole
is separated from the critical line by its imaginary part, and each remaining rising factor
is bounded uniformly. This controls propagation of the final power's approximation error. -/
theorem norm_finiteEM8_coefficient_le (t : ℝ) (ht : 14 ≤ t) (ht100 : t ≤ 100) :
    ‖finiteEM8Coefficient t‖ ≤ 10 := by
  let s : ℂ := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I
  have ht0 : 0 ≤ t := by linarith only [ht]
  have hd : (14 : ℝ) ≤ ‖s - 1‖ := by
    have h := Complex.abs_im_le_norm (s - 1)
    simp only [s, Complex.sub_im, Complex.one_im, sub_zero, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, zero_add,
      add_zero, abs_of_nonneg ht0] at h
    change (14 : ℝ) ≤ ‖(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) - 1‖
    linarith only [h, ht]
  have hp : ‖(128 : ℂ) / (s - 1)‖ ≤ (128 : ℝ) / 14 := by
    rw [norm_div, Complex.norm_ofNat]
    exact div_le_div_of_nonneg_left (by norm_num only) (by norm_num only) hd
  have h1 : ‖s‖ ≤ 101 := by
    simpa only [Nat.cast_zero, add_zero] using
      norm_critical_shift_le t ht0 ht100 0 (by norm_num only)
  have h3 := norm_critical_rising_le t ht0 ht100 3 (by norm_num only)
  have h5 := norm_critical_rising_le t ht0 ht100 5 (by norm_num only)
  have h7 := norm_critical_rising_le t ht0 ht100 7 (by norm_num only)
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat, add_zero, one_mul] at h3 h5 h7
  exact norm_em8_coefficient_aux s hp h1 h3 h5 h7

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
