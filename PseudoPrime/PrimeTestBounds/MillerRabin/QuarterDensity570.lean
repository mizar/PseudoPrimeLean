/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAbel570
public import PseudoPrime.Analysis.ExponentialMomentTail
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Logarithmic derivatives of the section 31 principal weight -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The shifted logarithmic coordinate vanishes at the upper support endpoint. -/
noncomputable def quarterCoord570 (X t : ℝ) : ℝ :=
  (2 * (7 / 5) - Real.log (t / X)) / (2 * (25 / 51))

/-- Exponential and square-root factor multiplying the fifth power in the section 31 weight. -/
noncomputable def quarterFactor570 (X t : ℝ) : ℝ :=
  (1 / Real.sqrt t) * (Real.exp (-quarterCoord570 X t) / 120)

private theorem coord_deriv {X t : ℝ} (hx : 0 < X) (ht : 0 < t) :
    HasDerivAt (quarterCoord570 X) (-(51 / 50) / t) t := by
  have hlog := ((hasDerivAt_id t).div_const X).log (div_pos ht hx).ne'
  apply
    (((hasDerivAt_const t (2 * (7 / 5 : ℝ))).sub hlog).div_const (2 * (25 / 51 : ℝ))).congr_deriv
  simp only [id_eq]
  field_simp [hx.ne', ht.ne']
  ring

private theorem factor_deriv {X t : ℝ} (hx : 0 < X) (ht : 0 < t) :
    HasDerivAt (quarterFactor570 X) (quarterFactor570 X t * (13 / 25) / t) t := by
  have h :=
    ((hasDerivAt_const t (1 : ℝ)).div (Real.hasDerivAt_sqrt ht.ne') (Real.sqrt_pos.mpr ht).ne').mul
      (((coord_deriv hx ht).neg.exp).div_const 120)
  apply h.congr_deriv
  simp only [Pi.neg_apply, Pi.div_apply, quarterFactor570]
  field_simp [ht.ne', (Real.sqrt_pos.mpr ht).ne']
  nlinarith only [Real.sq_sqrt ht.le]

/-- On positive inputs the logarithmic derivative is the exponential factor
times a polynomial of degrees four and five in the shifted coordinate. -/
theorem quarter_log_deriv_570 {X t : ℝ} (hx : 0 < X) (ht : 0 < t) :
    let v := quarterCoord570 X t
    t * deriv (quarterWeight570 X) t =
      quarterFactor570 X t * ((13 / 25) * v ^ 5 - 5 * (51 / 50) * v ^ 4) := by
  intro v
  have he : quarterWeight570 X = fun u ↦ quarterFactor570 X u * quarterCoord570 X u ^ 5 := by
    funext u
    unfold quarterWeight570 quarterFactor570 quarterCoord570
    ring
  rw [he,
    show deriv (fun u ↦ quarterFactor570 X u * quarterCoord570 X u ^ 5) t = _ from
      ((factor_deriv hx ht).mul ((coord_deriv hx ht).pow 5)).deriv]
  dsimp only [Pi.pow_apply, v]
  field_simp [ht.ne']
  ring

/-- The second Abel density has a cubic factor in the shifted coordinate.
The remaining quadratic controls every sign change on the positive support. -/
theorem quarter_second_density_570 {X t : ℝ} (hx : 0 < X) (ht : 0 < t) :
    let v := quarterCoord570 X t
    deriv (fun u ↦ u * deriv (quarterWeight570 X) u) t =
      quarterFactor570 X t / t * v ^ 3 *
        ((13 / 25) ^ 2 * v ^ 2 - 10 * (51 / 50) * (13 / 25) * v + 20 * (51 / 50) ^ 2) := by
  intro v
  let F := fun u ↦
    quarterFactor570 X u *
      ((13 / 25) * quarterCoord570 X u ^ 5 - (5 * (51 / 50)) * quarterCoord570 X u ^ 4)
  have he : (fun u ↦ u * deriv (quarterWeight570 X) u) =ᶠ[nhds t] F :=
    Filter.eventually_of_mem (isOpen_Ioi.mem_nhds ht) (fun u hu ↦ quarter_log_deriv_570 hx hu)
  have hv := coord_deriv hx ht
  have hf :=
    (factor_deriv hx ht).mul
      (((hv.pow 5).const_mul (13 / 25)).sub ((hv.pow 4).const_mul (5 * (51 / 50))))
  rw [he.deriv_eq, show deriv F t = _ from hf.deriv]
  dsimp only [Pi.sub_apply, Pi.pow_apply, v]
  field_simp [ht.ne']
  ring

/-- Between the arithmetic cutoff and the end of support, the second Abel density
is nonnegative. Here the shifted coordinate is between zero and 357/125. -/
theorem quarter_outer_density_nonneg {X t : ℝ} (hx : 0 < X) (hl : X ≤ t)
    (hu : t ≤ X * Real.exp (14 / 5)) : 0 ≤ deriv (fun u ↦ u * deriv (quarterWeight570 X) u) t := by
  have ht := hx.trans_le hl
  have hlog := Real.log_nonneg ((one_le_div hx).mpr hl)
  have hlog' :=
    (Real.log_le_iff_le_exp (div_pos ht hx)).mpr ((div_le_iff₀ hx).mpr ((mul_comm _ X) ▸ hu))
  have hv : 0 ≤ quarterCoord570 X t := by
    unfold quarterCoord570
    norm_num only
    linarith only [hlog']
  have hu' : quarterCoord570 X t ≤ 357 / 125 := by
    unfold quarterCoord570
    norm_num only
    linarith only [hlog]
  have hq :
    0 ≤
      (13 / 25 : ℝ) ^ 2 * quarterCoord570 X t ^ 2 -
          10 * (51 / 50) * (13 / 25) * quarterCoord570 X t +
        20 * (51 / 50) ^ 2 := by
    nlinarith only [hu', sq_nonneg (quarterCoord570 X t)]
  have hf : 0 ≤ quarterFactor570 X t := by
    unfold quarterFactor570; positivity
  rw [quarter_second_density_570 hx ht]
  exact mul_nonneg (mul_nonneg (div_nonneg hf ht.le) (pow_nonneg hv 3)) hq

/-- On the support, the sign of the Abel density is the sign of the product
of the distances from the two critical coordinates, times a nonnegative cubic. -/
theorem quarter_density_roots_570 {X t : ℝ} (hx : 0 < X) (ht : 0 < t) :
    let v := quarterCoord570 X t
    deriv (fun u ↦ u * deriv (quarterWeight570 X) u) t =
      quarterFactor570 X t / t * v ^ 3 * (13 / 25) ^ 2 * (v - 51 / 26 * (5 - Real.sqrt 5)) *
        (v - 51 / 26 * (5 + Real.sqrt 5)) := by
  intro v
  rw [quarter_second_density_570 hx ht]
  dsimp only [v]
  ring_nf
  rw [Real.sq_sqrt (by norm_num only : (0 : ℝ) ≤ 5)]
  ring

/-- Throughout positive coordinates the density is nonpositive precisely between
the two roots, inclusive. This also determines the absolute density on both sides. -/
theorem quarter_density_nonpos_iff {X t : ℝ} (hx : 0 < X) (ht : 0 < t)
    (hv : 0 < quarterCoord570 X t) :
    deriv (fun u ↦ u * deriv (quarterWeight570 X) u) t ≤ 0 ↔
      51 / 26 * (5 - Real.sqrt 5) ≤ quarterCoord570 X t ∧
        quarterCoord570 X t ≤ 51 / 26 * (5 + Real.sqrt 5) := by
  rw [quarter_density_roots_570 hx ht, mul_assoc]
  have hf : 0 < quarterFactor570 X t := by
    unfold quarterFactor570; positivity
  have hp : 0 < quarterFactor570 X t / t * quarterCoord570 X t ^ 3 * (13 / 25) ^ 2 := by positivity
  rw [← mul_zero (quarterFactor570 X t / t * quarterCoord570 X t ^ 3 * (13 / 25) ^ 2),
    mul_le_mul_iff_right₀ hp, mul_nonpos_iff]
  have hlt : (51 / 26 : ℝ) * (5 - Real.sqrt 5) < 51 / 26 * (5 + Real.sqrt 5) := by
    linarith only [Real.sqrt_pos.mpr (by norm_num only : (0 : ℝ) < 5)]
  constructor
  · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
    · exact ⟨by linarith only [ha], by linarith only [hb]⟩
    · exact False.elim (by linarith only [ha, hb, hlt])
  · intro h
    exact Or.inl ⟨sub_nonneg.mpr h.1, sub_nonpos.mpr h.2⟩

/-- The primitive for the square-root-weighted second density. The three
tail polynomials integrate its fifth, fourth and third exponential moments. -/
noncomputable def quarterSqrtPrimitive570 (X t : ℝ) : ℝ :=
  let v := quarterCoord570 X t
  let m := fun k ↦ -Real.exp (-1 * v) * Analysis.logPowerTailPoly 1 k v
  show ℝ from
    -((13 / 25) ^ 2 * m 5 - 10 * (51 / 50) * (13 / 25) * m 4 + 20 * (51 / 50) ^ 2 * m 3) /
      (120 * (51 / 50))

/-- Differentiating the three exponential moments recovers the signed density times sqrt t.
On intervals of constant sign this primitive also evaluates its weighted variation. -/
theorem quarter_sqrt_primitive_deriv {X t : ℝ} (hx : 0 < X) (ht : 0 < t) :
    HasDerivAt (quarterSqrtPrimitive570 X)
      (Real.sqrt t * deriv (fun u ↦ u * deriv (quarterWeight570 X) u) t) t := by
  let v := quarterCoord570 X t
  have hm (k : ℕ) :=
    (Analysis.exponential_moment_primitive_deriv one_ne_zero k v).comp t (coord_deriv hx ht)
  have h5 := (hm 5).const_mul ((13 / 25 : ℝ) ^ 2)
  have h4 := (hm 4).const_mul (10 * (51 / 50 : ℝ) * (13 / 25))
  have h3 := (hm 3).const_mul (20 * (51 / 50 : ℝ) ^ 2)
  apply (((h5.sub h4).add h3).neg.div_const (120 * (51 / 50 : ℝ))).congr_deriv
  rw [quarter_second_density_570 hx ht]
  dsimp only [v, quarterFactor570]
  rw [neg_one_mul]
  field_simp [ht.ne', (Real.sqrt_pos.mpr ht).ne']
  ring

/-- On any positive interval, the signed square-root variation equals the difference
of the explicit primitive at its endpoints. -/
theorem quarter_sqrt_moment_570 {X a b : ℝ} (hx : 0 < X) (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, Real.sqrt t * deriv (fun u ↦ u * deriv (quarterWeight570 X) u) t) =
      quarterSqrtPrimitive570 X b - quarterSqrtPrimitive570 X a := by
  have ht {t : ℝ} (h : t ∈ Set.uIcc a b) : 0 < t :=
    ha.trans_le ((Set.uIcc_of_le hab ▸ h : t ∈ Set.Icc a b).1)
  apply
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t h ↦ quarter_sqrt_primitive_deriv hx (ht h))
  apply ContinuousOn.intervalIntegrable
  apply Real.continuous_sqrt.continuousOn.mul
  intro t h
  apply ContinuousAt.continuousWithinAt
  have he :=
    Filter.eventually_of_mem (isOpen_Ioi.mem_nhds (ht h) : Set.Ioi (0 : ℝ) ∈ nhds t)
      (fun u hu ↦ quarter_second_density_570 (t := u) hx hu)
  apply ContinuousAt.congr _ (Filter.EventuallyEq.symm he)
  have ht' := ht h
  unfold quarterFactor570 quarterCoord570
  fun_prop (disch := positivity)

end PseudoPrime.PrimeTestBounds.MillerRabin
