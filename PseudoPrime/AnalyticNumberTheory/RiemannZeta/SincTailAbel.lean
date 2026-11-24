/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.SineMajorant
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountIntegral
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.OrdinateTail
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCombinedAbelRH
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountArgumentRH
import all PseudoPrime.Analysis.SincMomentDerivatives
public import PseudoPrime.Analysis.SincMomentDerivatives
import all PseudoPrime.Analysis.SineMajorant
import Mathlib.Analysis.Normed.Group.Tannery

/-! # Finite Abel identity for the smooth branch of the sinc weight -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Above the scaled cutoff, integrate the count against the smooth tail derivative.
The primitive differences use the original sinc weight, including at the cutoff itself. -/
theorem sincTail_finite_abel {β a b : ℝ} (hb : 0 < β) (ha : 0 < a) (hab : a ≤ b)
    (hcut : 2 / 5 ≤ β * a) :
    (∫ t in a..b, zeroCount t * deriv (Analysis.sincTailWeight β) t) =
      ∑ ρ ∈ zerosUpTo b,
        (riemannZetaZeroMultiplicity ρ : ℝ) *
          (Analysis.sincWeight (β * b) / b -
            Analysis.sincWeight (β * max a |ρ.im|) / max a |ρ.im|) := by
  have hd := fun (t : ℝ) (ht : t ∈ Set.Icc a b) ↦
    (Analysis.hasDerivAt_sincTailWeight hb.ne' (ha.trans_le ht.1).ne').differentiableAt.hasDerivAt
  rw [zeroCount_weighted_integral ha.le hab hd (Analysis.continuousOn_deriv_sincTail hb.ne' ha hab)]
  apply Finset.sum_congr rfl
  intro ρ _
  have htop := hcut.trans (mul_le_mul_of_nonneg_left hab hb.le)
  have hm := hcut.trans (mul_le_mul_of_nonneg_left (le_max_left a |ρ.im|) hb.le)
  rw [Analysis.sincWeight_div_eq_tail htop, Analysis.sincWeight_div_eq_tail hm]

/-- Under RH the two-sided count divided by squared height vanishes at infinity.
The count error divided by height tends to zero, as does the logarithmic main term
after division by squared height. -/
theorem count_div_sq_tendsto (hRH : RiemannHypothesis) :
    Filter.Tendsto (fun t : ℝ ↦ zeroCount t / t ^ 2) Filter.atTop (nhds 0) := by
  have hi : Filter.Tendsto (fun t : ℝ ↦ t⁻¹) Filter.atTop (nhds 0) := tendsto_inv_atTop_zero
  have hl := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hm := ((hl.sub (hi.const_mul (Real.log (2 * Real.pi)))).sub hi).const_mul (1 / Real.pi)
  have ht := (((zeroCountError_div_tendsto hRH).mul hi).add hm).add ((hi.pow 2).const_mul (7 / 4))
  simp only [mul_zero, sub_zero, add_zero, zero_pow (by decide : 2 ≠ 0)] at ht
  apply ht.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t hp
  simp only [zeroCountError, id_eq]
  field_simp [hp.ne', Real.pi_ne_zero]
  ring

/-- Multiplication by the tail weight kills any function growing slower than squared height. -/
private theorem weighted_endpoint {f : ℝ → ℝ} {β : ℝ} (hb : 0 < β)
    (hf : Filter.Tendsto (fun t ↦ f t / t ^ 2) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun t ↦ f t * Analysis.sincTailWeight β t) Filter.atTop (nhds 0) := by
  have ht := hf.abs.mul_const ((9 / 8 : ℝ) / β)
  simp only [abs_zero, zero_mul] at ht
  apply squeeze_zero_norm' _ ht
  filter_upwards with t
  have hn := Analysis.abs_iteratedDeriv_sincNumerator 0 (β * t)
  simp only [iteratedDeriv_zero, Analysis.sincMomentNumerator, Analysis.sincMomentAmplitude,
    ↓reduceIte, Rat.cast_div, Rat.cast_ofNat] at hn
  simp only [Real.norm_eq_abs, Analysis.sincTailWeight, abs_mul, abs_div, abs_of_pos hb]
  calc
    _ ≤ |f t| * ((9 / 8) / (β * |t ^ 2|)) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hn (mul_nonneg hb.le (abs_nonneg _)))
        (abs_nonneg _)
    _ = _ := by ring

/-- The upper count endpoint in the finite Abel formula tends to zero under RH. -/
theorem sincTail_endpoint_tendsto (hRH : RiemannHypothesis) {β : ℝ} (hb : 0 < β) :
    Filter.Tendsto (fun t ↦ zeroCount t * Analysis.sincTailWeight β t) Filter.atTop (nhds 0) := by
  exact weighted_endpoint hb (count_div_sq_tendsto hRH)

/-- The smooth counting main term has vanishing weighted upper endpoint at every
positive scale because its growth is of order height times log height. -/
theorem sincTail_main_endpoint {β : ℝ} (hb : 0 < β) :
    Filter.Tendsto
      (fun t ↦
        ((1 / Real.pi) * t * (Real.log t - Real.log (2 * Real.pi) - 1) + 7 / 4) *
          Analysis.sincTailWeight β t)
      Filter.atTop (nhds 0) := by
  apply weighted_endpoint hb
  have hi : Filter.Tendsto (fun t : ℝ ↦ t⁻¹) Filter.atTop (nhds 0) := tendsto_inv_atTop_zero
  have hl := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hm := ((hl.sub (hi.const_mul (Real.log (2 * Real.pi)))).sub hi).const_mul (1 / Real.pi)
  have h := hm.add ((hi.pow 2).const_mul (7 / 4))
  simp only [mul_zero, sub_zero, add_zero, zero_pow (by decide : 2 ≠ 0)] at h
  apply h.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
  simp only [id_eq]
  field_simp [ht.ne', Real.pi_ne_zero]

/-- The truncated clamped zero sum plus the count-derivative integral is precisely
the upper boundary term, including zeros on either endpoint. -/
theorem sincTail_sum_add_integral {β a b : ℝ} (hb : 0 < β) (ha : 0 < a) (hab : a ≤ b)
    (hcut : 2 / 5 ≤ β * a) :
    (∑ ρ ∈ zerosUpTo b,
          (riemannZetaZeroMultiplicity ρ : ℝ) *
            (Analysis.sincWeight (β * max a |ρ.im|) / max a |ρ.im|)) +
        (∫ t in a..b, zeroCount t * deriv (Analysis.sincTailWeight β) t) =
      zeroCount b * Analysis.sincTailWeight β b := by
  rw [sincTail_finite_abel hb ha hab hcut, ← Finset.sum_add_distrib, zeroCount_eq_sum,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ρ _
  rw [Analysis.sincWeight_div_eq_tail (hcut.trans (mul_le_mul_of_nonneg_left hab hb.le))]
  ring

/-- Under RH the truncated weighted sum and the negative Abel integral have the
same limit whenever either converges, since their difference tends to zero. -/
theorem sincTail_abel_tendsto (hRH : RiemannHypothesis) {β a : ℝ} (hb : 0 < β) (ha : 0 < a)
    (hcut : 2 / 5 ≤ β * a) :
    Filter.Tendsto
      (fun b ↦
        (∑ ρ ∈ zerosUpTo b,
            (riemannZetaZeroMultiplicity ρ : ℝ) *
              (Analysis.sincWeight (β * max a |ρ.im|) / max a |ρ.im|)) +
          ∫ t in a..b, zeroCount t * deriv (Analysis.sincTailWeight β) t)
      Filter.atTop (nhds 0) := by
  apply (sincTail_endpoint_tendsto hRH hb).congr'
  filter_upwards [Filter.eventually_ge_atTop a] with b hab
  exact (sincTail_sum_add_integral hb ha hab hcut).symm

/-- The weighted tail above a positive cutoff is absolutely summable under RH.
The inverse-square ordinate ledger includes multiplicities and both signs. -/
theorem sincTail_summable (hRH : RiemannHypothesis) {β a : ℝ} (hb : 0 < β) (hcut : 2 / 5 ≤ β * a) :
    Summable
      (fun ρ : ℂ ↦
        if riemannZeta ρ = 0 ∧ 0 ≤ ρ.re ∧ a < |ρ.im| then
          (riemannZetaZeroMultiplicity ρ : ℝ) * (Analysis.sincWeight (β * |ρ.im|) / |ρ.im|)
        else 0) := by
  apply Summable.of_norm_bounded ((ordinateTailWeight_summable hRH a).mul_right ((9 / 8 : ℝ) / β))
  intro ρ
  rw [ordinateTailWeight_eq]
  split
  next h =>
    have ht := hcut.trans (mul_le_mul_of_nonneg_left h.2.2.le hb.le)
    have hn := Analysis.abs_iteratedDeriv_sincNumerator 0 (β * |ρ.im|)
    simp only [iteratedDeriv_zero, Analysis.sincMomentNumerator, Analysis.sincMomentAmplitude,
      ↓reduceIte, Rat.cast_div, Rat.cast_ofNat] at hn
    rw [Analysis.sincWeight_div_eq_tail ht]
    simp only [Analysis.sincTailWeight, Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos hb,
      abs_of_nonneg (sq_nonneg |ρ.im|),
      abs_of_nonneg (Nat.cast_nonneg (riemannZetaZeroMultiplicity ρ) : (0 : ℝ) ≤ _)]
    calc
      _ ≤ (riemannZetaZeroMultiplicity ρ : ℝ) * ((9 / 8) / (β * |ρ.im| ^ 2)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hn (mul_nonneg hb.le (sq_nonneg _)))
          (Nat.cast_nonneg _)
      _ = _ := by ring
  next h => simp only [Real.norm_eq_abs, abs_zero, zero_mul, le_refl]

/-- Height truncations of the absolutely summable sinc tail converge to the full
two-sided sum. The lower cutoff is strict and the upper endpoint is included. -/
theorem sincTail_sum_tendsto (hRH : RiemannHypothesis) {β a : ℝ} (hb : 0 < β)
    (hcut : 2 / 5 ≤ β * a) :
    let w := fun ρ : ℂ ↦
      if riemannZeta ρ = 0 ∧ 0 ≤ ρ.re ∧ a < |ρ.im| then
        (riemannZetaZeroMultiplicity ρ : ℝ) * (Analysis.sincWeight (β * |ρ.im|) / |ρ.im|)
      else 0
    Filter.Tendsto (fun b ↦ ∑ ρ ∈ zerosUpTo b, w ρ) Filter.atTop (nhds (∑' ρ, w ρ)) := by
  classical
  intro w
  let f := fun (b : ℝ) (ρ : ℂ) ↦ if ρ ∈ zerosUpTo b then w ρ else 0
  have hlim (ρ : ℂ) : Filter.Tendsto (fun b ↦ f b ρ) Filter.atTop (nhds (w ρ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [Filter.eventually_ge_atTop |ρ.im|] with b hb'
    by_cases hz : riemannZeta ρ = 0 ∧ 0 ≤ ρ.re
    · have hm := (mem_zerosUpTo ((abs_nonneg _).trans hb')).2 ⟨hz.1, hz.2, hb'⟩
      simp only [f, hm, ↓reduceIte]
    · have hn : ¬(riemannZeta ρ = 0 ∧ 0 ≤ ρ.re ∧ a < |ρ.im|) := fun h ↦ hz ⟨h.1, h.2.1⟩
      simp only [f, w, hn, ↓reduceIte, ite_self]
  have hbound : ∀ b ρ, ‖f b ρ‖ ≤ ‖w ρ‖ := by
    intro b ρ
    unfold f
    split
    · exact le_rfl
    · simpa only [norm_zero] using norm_nonneg (w ρ)
  have hs : Summable w := sincTail_summable hRH hb hcut
  apply
    (tendsto_tsum_of_dominated_convergence hs.norm hlim (Filter.Eventually.of_forall hbound)).congr'
  filter_upwards with b
  rw [tsum_eq_sum (s := zerosUpTo b) (fun ρ hρ ↦ by simp only [f, hρ, ↓reduceIte])]
  exact Finset.sum_congr rfl (fun ρ hρ ↦ by simp only [f, hρ, ↓reduceIte])

/-- Separate the closed lower ledger from the strict upper tail in the finite Abel sum. -/
private theorem sincTail_clamped_split {β a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    let W := fun t : ℝ ↦ Analysis.sincWeight (β * t) / t
    let w := fun ρ : ℂ ↦
      if riemannZeta ρ = 0 ∧ 0 ≤ ρ.re ∧ a < |ρ.im| then
        (riemannZetaZeroMultiplicity ρ : ℝ) * W |ρ.im|
      else 0
    (∑ ρ ∈ zerosUpTo b, (riemannZetaZeroMultiplicity ρ : ℝ) * W (max a |ρ.im|)) =
      zeroCount a * W a + ∑ ρ ∈ zerosUpTo b, w ρ := by
  classical
  intro W w
  rw [zeroCount_eq_sum, Finset.sum_mul]
  have hf : (zerosUpTo b).filter (fun ρ ↦ |ρ.im| ≤ a) = zerosUpTo a := by
    ext ρ
    simp only [Finset.mem_filter, mem_zerosUpTo (ha.trans hab), mem_zerosUpTo ha]
    exact ⟨fun h ↦ ⟨h.1.1, h.1.2.1, h.2⟩, fun h ↦ ⟨⟨h.1, h.2.1, h.2.2.trans hab⟩, h.2.2⟩⟩
  rw [← hf, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ρ hρ
  have hz := (mem_zerosUpTo (ha.trans hab)).1 hρ
  by_cases h : |ρ.im| ≤ a
  · simp only [w, h, hz.1, hz.2.1, not_lt.mpr h, max_eq_left h, ↓reduceIte, and_false, add_zero]
  · have ht := lt_of_not_ge h
    simp only [w, h, hz.1, hz.2.1, ht, max_eq_right ht.le, ↓reduceIte, and_self, zero_add]

/-- The negative Abel integral converges to the lower endpoint mass plus the full
strict tail. Zeros at the lower cutoff contribute only to the endpoint mass. -/
theorem sincTail_integral_tendsto (hRH : RiemannHypothesis) {β a : ℝ} (hb : 0 < β) (ha : 0 < a)
    (hcut : 2 / 5 ≤ β * a) :
    let W := fun t : ℝ ↦ Analysis.sincWeight (β * t) / t
    let w := fun ρ : ℂ ↦
      if riemannZeta ρ = 0 ∧ 0 ≤ ρ.re ∧ a < |ρ.im| then
        (riemannZetaZeroMultiplicity ρ : ℝ) * W |ρ.im|
      else 0
    Filter.Tendsto (fun b ↦ -(∫ t in a..b, zeroCount t * deriv (Analysis.sincTailWeight β) t))
      Filter.atTop (nhds (zeroCount a * W a + ∑' ρ, w ρ)) := by
  intro W w
  have ht :=
    ((sincTail_sum_tendsto hRH hb hcut).const_add (zeroCount a * W a)).sub
      (sincTail_endpoint_tendsto hRH hb)
  rw [sub_zero] at ht
  apply ht.congr'
  filter_upwards [Filter.eventually_ge_atTop a] with b hab
  have he := sincTail_sum_add_integral hb ha hab hcut
  rw [sincTail_clamped_split (β := β) ha.le hab] at he
  linarith only [he]

/-- On a positive interval the Abel integral splits into the smooth count density,
its endpoint terms, and the discrepancy against the weight derivative. -/
theorem sincTail_main_split {β a b : ℝ} (hb : 0 < β) (ha : 0 < a) (hab : a ≤ b) :
    let M := fun t : ℝ ↦ (1 / Real.pi) * t * (Real.log t - Real.log (2 * Real.pi) - 1) + 7 / 4
    let W := Analysis.sincTailWeight β;
    -(∫ t in a..b, zeroCount t * deriv W t) =
      M a * W a - M b * W b + (∫ t in a..b, (Real.log t - Real.log (2 * Real.pi)) / Real.pi * W t) -
        ∫ t in a..b, zeroCountError t * deriv W t := by
  intro M W
  let D := fun t : ℝ ↦ (Real.log t - Real.log (2 * Real.pi)) / Real.pi
  have hd {t : ℝ} (ht : 0 < t) : HasDerivAt M (D t) t := by
    have h :=
      ((((hasDerivAt_id t).const_mul (1 / Real.pi)).mul
            (((Real.hasDerivAt_log ht.ne').sub_const (Real.log (2 * Real.pi))).sub_const
              1)).add_const
        (7 / 4))
    apply h.congr_deriv
    simp only [D, id_eq, mul_one]
    field_simp [Real.pi_ne_zero, ht.ne']
    ring
  have hp {t : ℝ} (ht : t ∈ Set.uIcc a b) : 0 < t :=
    ha.trans_le ((Set.uIcc_of_le hab) ▸ ht : t ∈ Set.Icc a b).1
  have hm : ContinuousOn M (Set.uIcc a b) := fun _ ht ↦ (hd (hp ht)).continuousAt.continuousWithinAt
  have hw' := Analysis.continuousOn_deriv_sincTail hb.ne' ha hab
  have hw {t : ℝ} (ht : 0 < t) : HasDerivAt W (deriv W t) t :=
    (Analysis.hasDerivAt_sincTailWeight hb.ne' ht.ne').differentiableAt.hasDerivAt
  have hD : ContinuousOn D (Set.uIcc a b) := fun _ ht ↦
    (((Real.continuousAt_log (hp ht).ne').sub continuousAt_const).div_const _).continuousWithinAt
  have hi :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hm
      (fun _ ht ↦ (hw (hp ht)).continuousAt.continuousWithinAt)
      (fun _ ht ↦ hd (hp (Set.Ioo_subset_Icc_self ht)))
      (fun _ ht ↦ hw (hp (Set.Ioo_subset_Icc_self ht))) hD.intervalIntegrable hw'.intervalIntegrable
  have hn := (zeroCount_integrable ha.le hab).mul_continuousOn hw'
  have he :
    (∫ t in a..b, zeroCountError t * deriv W t) =
      (∫ t in a..b, zeroCount t * deriv W t) - ∫ t in a..b, M t * deriv W t := by
    have hm' : IntervalIntegrable (fun t ↦ M t * deriv W t) MeasureTheory.volume a b :=
      (hm.mul hw').intervalIntegrable
    rw [← intervalIntegral.integral_sub hn hm']
    apply intervalIntegral.integral_congr
    intro t _
    exact sub_mul (zeroCount t) (M t) _
  dsimp only [D] at hi
  linarith only [he, hi]

/-- Rescale the smooth count-density integral to the fixed moment variable.
The logarithm splits into a constant depending on the scale and the logarithm
of the new variable. -/
theorem sincTail_density_rescale {β a b : ℝ} (hb : 0 < β) (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, (Real.log t - Real.log (2 * Real.pi)) / Real.pi * Analysis.sincTailWeight β t) =
      ∫ z in β * a..β * b,
        (Real.log z - Real.log (2 * Real.pi * β)) / Real.pi *
          (Analysis.sincMomentNumerator z / z ^ 2) := by
  let f := fun z : ℝ ↦
    (Real.log z - Real.log (2 * Real.pi * β)) / Real.pi * (Analysis.sincMomentNumerator z / z ^ 2)
  change _ = ∫ z in β * a..β * b, f z
  rw [← intervalIntegral.smul_integral_comp_mul_left f β, ← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro t ht
  have hp : 0 < t := ha.trans_le ((Set.uIcc_of_le hab) ▸ ht : t ∈ Set.Icc a b).1
  simp only [f, smul_eq_mul, Analysis.sincTailWeight, Analysis.sincMomentNumerator,
    Real.log_mul hb.ne' hp.ne',
    Real.log_mul (mul_ne_zero (two_ne_zero : (2 : ℝ) ≠ 0) Real.pi_ne_zero) hb.ne']
  field_simp [hb.ne', hp.ne', Real.pi_ne_zero]
  ring

/-- The rescaled density is a linear combination of the logarithmic and plain
moments on any strictly positive integration interval. -/
theorem sincTail_density_moments {β a b : ℝ} (hb : 0 < β) (ha : 0 < a) (hab : a ≤ b) :
    let n := Analysis.sincMomentNumerator
    (∫ t in a..b, (Real.log t - Real.log (2 * Real.pi)) / Real.pi * Analysis.sincTailWeight β t) =
      ((∫ z in β * a..β * b, n z * (Real.log z / z ^ 2)) -
          Real.log (2 * Real.pi * β) * (∫ z in β * a..β * b, n z * (1 / z ^ 2))) /
        Real.pi := by
  intro n
  rw [sincTail_density_rescale hb ha hab]
  have hp {z : ℝ} (hz : z ∈ Set.uIcc (β * a) (β * b)) : 0 < z :=
    (mul_pos hb ha).trans_le
      ((Set.uIcc_of_le (mul_le_mul_of_nonneg_left hab hb.le)) ▸ hz : z ∈ Set.Icc (β * a) (β * b)).1
  have hn : Continuous n := (Analysis.contDiff_sincMomentNumerator 1).continuous
  have hi : ContinuousOn (fun z : ℝ ↦ n z * (1 / z ^ 2)) (Set.uIcc (β * a) (β * b)) := by
    intro z hz
    fun_prop (disch := exact pow_ne_zero _ (hp hz).ne')
  have hj : ContinuousOn (fun z : ℝ ↦ n z * (Real.log z / z ^ 2)) (Set.uIcc (β * a) (β * b)) := by
    intro z hz
    fun_prop (disch :=
      first
      | exact (hp hz).ne'
      | exact pow_ne_zero _ (hp hz).ne')
  rw [← intervalIntegral.integral_const_mul, ←
    intervalIntegral.integral_sub hj.intervalIntegrable (hi.intervalIntegrable.const_mul _), ←
    intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro z _
  dsimp only [n]
  ring

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
