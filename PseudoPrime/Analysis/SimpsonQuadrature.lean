/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-! # One-sided Simpson quadrature error on a closed cell -/

public section

namespace PseudoPrime.Analysis

/-- One half of Simpson's rule on a cell of width two. The derivative terms at the
midpoint cancel when this bound is added to its reflected counterpart. -/
private theorem simpson_half_upper {f d e j k : ℝ → ℝ} {M : ℝ}
    (hf : ∀ x ∈ Set.Icc 0 1, HasDerivAt f (d x) x) (hd : ∀ x ∈ Set.Icc 0 1, HasDerivAt d (e x) x)
    (he : ∀ x ∈ Set.Icc 0 1, HasDerivAt e (j x) x) (hj : ∀ x ∈ Set.Icc 0 1, HasDerivAt j (k x) x)
    (hk : ∀ x ∈ Set.Icc 0 1, -M ≤ k x) :
    (∫ x in (0 : ℝ)..1, f x) ≤ f 0 / 3 + 2 * f 1 / 3 - d 1 / 6 + j 1 / 72 + M / 180 := by
  let K := fun t : ℝ ↦ t ^ 3 / 18 - t ^ 4 / 24
  let D := fun t : ℝ ↦ t ^ 2 / 6 - t ^ 3 / 6
  let E := fun t : ℝ ↦ t / 3 - t ^ 2 / 2
  let J := fun t : ℝ ↦ 1 / 3 - t
  let H := fun t : ℝ ↦ t ^ 4 / 72 - t ^ 5 / 120
  let F := fun t ↦ K t * j t - D t * e t + E t * d t - J t * f t + M * H t
  have hF (t : ℝ) (ht : t ∈ Set.Icc 0 1) : HasDerivAt F (f t + K t * (M + k t)) t := by
    have h := hasDerivAt_id t
    have k1 : HasDerivAt K (D t) t := by
      apply (((h.pow 3).div_const 18).sub ((h.pow 4).div_const 24)).congr_deriv
      dsimp only [D, id_eq]; ring
    have k2 : HasDerivAt D (E t) t := by
      apply (((h.pow 2).div_const 6).sub ((h.pow 3).div_const 6)).congr_deriv
      dsimp only [E, id_eq]; ring
    have k3 : HasDerivAt E (J t) t := by
      apply ((h.div_const 3).sub ((h.pow 2).div_const 2)).congr_deriv
      dsimp only [J, id_eq]; ring
    have k4 := (hasDerivAt_const t (1 / 3 : ℝ)).sub h
    have k0 : HasDerivAt H (K t) t := by
      apply (((h.pow 4).div_const 72).sub ((h.pow 5).div_const 120)).congr_deriv
      dsimp only [K, id_eq]; ring
    apply
      (((((k1.mul (hj t ht)).sub (k2.mul (he t ht))).add (k3.mul (hd t ht))).sub
              (k4.mul (hf t ht))).add
          (k0.const_mul M)).congr_deriv
    change
      D t * j t + K t * k t - (E t * e t + D t * j t) + (J t * d t + E t * e t) -
            ((0 - 1) * f t + J t * d t) +
          M * K t =
        _
    ring
  have h :=
    intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le zero_le_one
      (fun t ht ↦ (hF t ht).continuousAt.continuousWithinAt)
      (fun t ht ↦ (hF t (Set.Ioo_subset_Icc_self ht)).hasDerivWithinAt)
      ((show ContinuousOn f (Set.Icc 0 1) from fun t ht ↦
            (hf t ht).continuousAt.continuousWithinAt).integrableOn_compact
        isCompact_Icc)
      (fun t ht ↦
        le_add_of_nonneg_right
          (mul_nonneg
            (show 0 ≤ K t by
              have ht3 := pow_nonneg ht.1.le 3
              have hprod := mul_nonneg ht3 (sub_nonneg.mpr ht.2.le)
              dsimp only [K]; nlinarith only [ht3, hprod])
            (by linarith only [hk t (Set.Ioo_subset_Icc_self ht)])))
  dsimp only [F, K, D, E, J, H] at h
  linarith only [h]

/-- Simpson's upper error on [0,2] is M/90 if the fourth derivative is at least -M.
Integrating the quartic Peano kernel on the two halves gives the sharp constant. -/
theorem simpson_upper_zero_two {f d e j k : ℝ → ℝ} {M : ℝ}
    (hf : ∀ x ∈ Set.Icc 0 2, HasDerivAt f (d x) x) (hd : ∀ x ∈ Set.Icc 0 2, HasDerivAt d (e x) x)
    (he : ∀ x ∈ Set.Icc 0 2, HasDerivAt e (j x) x) (hj : ∀ x ∈ Set.Icc 0 2, HasDerivAt j (k x) x)
    (hk : ∀ x ∈ Set.Icc 0 2, -M ≤ k x) :
    (∫ x in (0 : ℝ)..2, f x) ≤ (f 0 + 4 * f 1 + f 2) / 3 + M / 90 := by
  have hin {x : ℝ} (hx : x ∈ Set.Icc 0 1) : x ∈ Set.Icc 0 2 := ⟨hx.1, by linarith only [hx.2]⟩
  have href {x : ℝ} (hx : x ∈ Set.Icc 0 1) : 2 - x ∈ Set.Icc 0 2 :=
    ⟨by linarith only [hx.2], by linarith only [hx.1]⟩
  have hl :=
    simpson_half_upper (fun x hx ↦ hf x (hin hx)) (fun x hx ↦ hd x (hin hx))
      (fun x hx ↦ he x (hin hx)) (fun x hx ↦ hj x (hin hx)) (fun x hx ↦ hk x (hin hx))
  have refl {F : ℝ → ℝ} {t y : ℝ} (h : HasDerivAt F y (2 - t)) :
    HasDerivAt (fun x ↦ F (2 - x)) (-y) t := by
    convert h.comp t ((hasDerivAt_const t (2 : ℝ)).sub (hasDerivAt_id t)) using 1
    · rfl
    · ring
  have hr :=
    simpson_half_upper (fun x hx ↦ refl (hf _ (href hx))) (fun x hx ↦ (refl (hd _ (href hx))).neg)
      (fun x hx ↦ by simpa only [Pi.neg_apply, neg_neg] using refl (he _ (href hx)))
      (fun x hx ↦ (refl (hj _ (href hx))).neg)
      (fun x hx ↦ by simpa only [Pi.neg_apply, neg_neg] using hk _ (href hx))
  rw [intervalIntegral.integral_comp_sub_left f 2] at hr
  norm_num only [Pi.neg_apply] at hr
  have hc : ContinuousOn f (Set.Icc 0 2) := fun x hx ↦ (hf x hx).continuousAt.continuousWithinAt
  have hi {a b : ℝ} (hab : a ≤ b) (ha : 0 ≤ a) (hb : b ≤ 2) :
    IntervalIntegrable f MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact hc.mono (Set.Icc_subset_Icc ha hb)
  rw [←
    intervalIntegral.integral_add_adjacent_intervals (hi zero_le_one le_rfl (by norm_num only))
      (hi (by norm_num only) zero_le_one le_rfl)]
  linarith only [hl, hr]

/-- A positive-width cell has Simpson upper error at most width^5 M/2880
when its fourth derivative is bounded below by -M throughout the closed cell. -/
theorem integral_le_simpson {f d e j k : ℝ → ℝ} {a b M : ℝ} (hab : a < b)
    (hf : ∀ x ∈ Set.Icc a b, HasDerivAt f (d x) x) (hd : ∀ x ∈ Set.Icc a b, HasDerivAt d (e x) x)
    (he : ∀ x ∈ Set.Icc a b, HasDerivAt e (j x) x) (hj : ∀ x ∈ Set.Icc a b, HasDerivAt j (k x) x)
    (hk : ∀ x ∈ Set.Icc a b, -M ≤ k x) :
    (∫ x in a..b, f x) ≤
      (b - a) / 6 * (f a + 4 * f ((a + b) / 2) + f b) + (b - a) ^ 5 * M / 2880 := by
  let w := (b - a) / 2
  have hw : 0 < w := half_pos (sub_pos.mpr hab)
  have hb : w * 2 + a = b := by
    dsimp only [w]; ring
  have hmid : w + a = (a + b) / 2 := by
    dsimp only [w]; ring
  have hmem {x : ℝ} (hx : x ∈ Set.Icc 0 2) : w * x + a ∈ Set.Icc a b :=
    ⟨by linarith only [mul_nonneg hw.le hx.1], by
      linarith only [mul_le_mul_of_nonneg_left hx.2 hw.le, hb]⟩
  have chain {F : ℝ → ℝ} {t y : ℝ} (c : ℝ) (h : HasDerivAt F y (w * t + a)) :
    HasDerivAt (fun x ↦ c * F (w * x + a)) (c * w * y) t := by
    apply ((h.comp t (((hasDerivAt_id t).const_mul w).add_const a)).const_mul c).congr_deriv
    ring
  have h :=
    simpson_upper_zero_two (fun x hx ↦ chain 1 (hf _ (hmem hx)))
      (fun x hx ↦ chain (1 * w) (hd _ (hmem hx))) (fun x hx ↦ chain (1 * w * w) (he _ (hmem hx)))
      (fun x hx ↦ chain (1 * w * w * w) (hj _ (hmem hx))) (M := w ^ 4 * M)
      (fun x hx ↦ by
        nlinarith only [mul_le_mul_of_nonneg_left (hk _ (hmem hx)) (pow_nonneg hw.le 4)])
  simp only [one_mul, mul_zero, zero_add, mul_one, hb, hmid] at h
  rw [intervalIntegral.integral_comp_mul_add f hw.ne' a, mul_zero, zero_add, hb, smul_eq_mul] at h
  have hi := mul_le_mul_of_nonneg_left h hw.le
  rw [← mul_assoc, mul_inv_cancel₀ hw.ne', one_mul] at hi
  dsimp only [w] at hi
  linarith only [hi]

end PseudoPrime.Analysis
