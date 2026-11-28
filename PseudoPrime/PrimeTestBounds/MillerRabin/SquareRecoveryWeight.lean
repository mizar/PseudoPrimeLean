/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.SquareRecoveryAbel
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSquarePrefix

/-! # Six-pole square recovery by partial summation -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The continued six-pole principal weight at a squared relative argument, divided by
the root scale. It interpolates square-index summands for Abel summation. -/
noncomputable def squareRootWeight (r t : ℝ) : ℝ :=
  refinedWeight (t ^ 2 / r ^ 2) / r

private theorem weight_deriv {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    HasDerivAt (squareRootWeight r) (refinedWeightDeriv (t ^ 2 / r ^ 2) * (2 * t / r ^ 2) / r)
      t := by
  have hi : HasDerivAt (fun z : ℝ ↦ z ^ 2 / r ^ 2) (2 * t / r ^ 2) t := by
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.pow_apply, id_eq, mul_one] using
      (((hasDerivAt_id t).pow 2).div_const (r ^ 2))
  exact ((refinedWeight_hasDerivAt (div_pos (pow_pos ht 2) (pow_pos hr 2))).comp t hi).div_const r

private theorem weight_nonpos {u : ℝ} (hu : 1 ≤ u) : refinedWeightDeriv u ≤ 0 := by
  have hc : refinedCoord u ≤ 567 / 200 := by
    dsimp only [refinedCoord]
    linarith only [Real.log_nonneg hu]
  unfold refinedWeightDeriv
  apply
    mul_nonpos_of_nonneg_of_nonpos
      (div_nonneg (Real.exp_pos _).le
        (mul_nonneg (mul_nonneg (by norm_num only) (zero_le_one.trans hu)) (Real.sqrt_nonneg u)))
  nlinarith only [mul_nonneg (by linarith only [hc] : 0 ≤ 27 / 5 - (29 / 50 : ℝ) * refinedCoord u)
      (pow_nonneg (sq_nonneg (refinedCoord u)) 2)]

private theorem weight_end {r : ℝ} (hr : 0 < r) :
    squareRootWeight r (Real.exp (21 / 16) * r) = 0 := by
  have he : (Real.exp (21 / 16) * r) ^ 2 / r ^ 2 = Real.exp (21 / 8) := by
    rw [mul_pow, mul_div_cancel_right₀ _ (pow_ne_zero _ hr.ne'), ← Real.exp_natCast_mul]
    norm_num only [Nat.cast_ofNat]
  rw [squareRootWeight, he, refinedWeight, refinedCoord, Real.log_exp]
  norm_num only [zero_mul, zero_div]

private theorem weight_cont {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    ContinuousAt (fun z ↦ refinedWeightDeriv (z ^ 2 / r ^ 2) * (2 * z / r ^ 2) / r) t := by
  let u := t ^ 2 / r ^ 2
  have hu : 0 < u := div_pos (pow_pos ht 2) (pow_pos hr 2)
  have hcoord := (refinedCoord_hasDerivAt hu).continuousAt
  have hD : ContinuousAt refinedWeightDeriv u := by
    unfold refinedWeightDeriv
    fun_prop (disch :=
      first
      | exact hu.ne'
      | exact (Real.sqrt_pos.mpr hu).ne'
      | exact mul_ne_zero (mul_ne_zero (by norm_num only) hu.ne') (Real.sqrt_pos.mpr hu).ne')
  have hi : ContinuousAt (fun z : ℝ ↦ z ^ 2 / r ^ 2) t := by fun_prop
  have hh : ContinuousAt (fun z : ℝ ↦ refinedWeightDeriv (z ^ 2 / r ^ 2)) t :=
    ContinuousAt.comp (g := refinedWeightDeriv) (f := fun z : ℝ ↦ z ^ 2 / r ^ 2) hD hi
  exact (hh.mul (show ContinuousAt (fun z : ℝ ↦ 2 * z / r ^ 2) t by fun_prop)).div_const r

/-- On the square recovery interval the six-pole root weight satisfies the
finite psi Abel lower bound. Its derivative is nonpositive above the lower
endpoint and the profile vanishes at the upper endpoint. -/
theorem squareRootWeight_abel {r : ℝ} (hr : 465 / 2 ≤ r) (hr' : r ≤ 278) :
    let V := Real.exp (21 / 16) * r;
    let f := squareRootWeight r;
    -(f r * (r + 81 / 100 * Real.sqrt r)) -
        (∫ t in r..V, deriv f t * (t - 81 / 100 * Real.sqrt t)) ≤
      ∑ k ∈ Finset.Ioc ⌊r⌋₊ ⌊V⌋₊, f k * ArithmeticFunction.vonMangoldt k := by
  intro V f
  have h0 : 0 < r := (by norm_num only : (0 : ℝ) < 465 / 2).trans_le hr
  apply square_window_abel_lower hr hr' V rfl
  · exact fun t ht ↦ (weight_deriv h0 (h0.trans_le ht.1)).differentiableAt
  · apply
      ContinuousOn.congr
        (fun t (ht : t ∈ Set.Icc r V) ↦ (weight_cont h0 (h0.trans_le ht.1)).continuousWithinAt)
    exact fun t ht ↦ (weight_deriv h0 (h0.trans_le ht.1)).deriv
  · intro t ht
    rw [(weight_deriv h0 (h0.trans_le ht.1)).deriv]
    apply div_nonpos_of_nonpos_of_nonneg _ h0.le
    apply
      mul_nonpos_of_nonpos_of_nonneg (weight_nonpos _)
        (div_nonneg (mul_nonneg (by norm_num only) (h0.le.trans ht.1)) (sq_nonneg r))
    exact (one_le_div (pow_pos h0 2)).mpr (pow_le_pow_left₀ h0.le ht.1 2)
  · dsimp only [f, squareRootWeight, refinedWeight, refinedCoord]
    rw [div_self (pow_ne_zero 2 h0.ne'), Real.log_one, mul_zero, sub_zero]
    positivity
  · exact weight_end h0

/-- On the support window the continued weight is exactly the actual
six-pole weight at the squared index and squared scale. -/
theorem squareRootWeight_eq_scaled {r t : ℝ} (hr : 0 < r) (ht : 0 < t)
    (hb : t ≤ Real.exp (21 / 16) * r) :
    squareRootWeight r t = refinedScaledWeight (r ^ 2) (t ^ 2) := by
  have hp := div_pos (pow_pos ht 2) (pow_pos hr 2)
  have hs := pow_le_pow_left₀ ht.le hb 2
  rw [mul_pow, ← Real.exp_natCast_mul] at hs
  have hlog : Real.log (t ^ 2 / r ^ 2) ≤ 21 / 8 := by
    apply (Real.log_le_iff_le_exp hp).mpr
    apply (div_le_iff₀ (pow_pos hr 2)).mpr
    convert hs using 1
    norm_num only [Nat.cast_ofNat]
  unfold refinedScaledWeight squareRootWeight refinedKernelWeight
  rw [refinedKernelWeight_eq hp hlog, Real.sqrt_sq hr.le]

/-- Partial integration removes the derivative of the root weight from the Abel
bound. The lower endpoint contributes twice the square-root error and the
remaining integral involves only the weight and the derivative of that error. -/
theorem squareRootWeight_integral_lower {r : ℝ} (hr : 465 / 2 ≤ r) (hr' : r ≤ 278) :
    let V := Real.exp (21 / 16) * r;
    let f := squareRootWeight r;
    (∫ t in r..V, f t * (1 - 81 / 100 * (1 / (2 * Real.sqrt t)))) -
        2 * (81 / 100) * Real.sqrt r * f r ≤
      ∑ k ∈ Finset.Ioc ⌊r⌋₊ ⌊V⌋₊, f k * ArithmeticFunction.vonMangoldt k := by
  intro V f
  have h0 : 0 < r := (by norm_num only : (0 : ℝ) < 465 / 2).trans_le hr
  have hV : r ≤ V := le_mul_of_one_le_left h0.le (Real.one_le_exp (by norm_num only))
  have pos {t : ℝ} (ht : t ∈ Set.uIcc r V) : 0 < t :=
    h0.trans_le ((Set.uIcc_of_le hV ▸ ht : t ∈ Set.Icc r V).1)
  have hd (t : ℝ) (ht : t ∈ Set.uIcc r V) := weight_deriv h0 (pos ht)
  have he (t : ℝ) (ht : t ∈ Set.uIcc r V) :=
    (hasDerivAt_id t).sub ((Real.hasDerivAt_sqrt (pos ht).ne').const_mul (81 / 100 : ℝ))
  have hc : ContinuousOn (deriv f) (Set.uIcc r V) := by
    apply
      ContinuousOn.congr
        (fun t (ht : t ∈ Set.uIcc r V) ↦ (weight_cont h0 (pos ht)).continuousWithinAt)
    exact fun t ht ↦ (hd t ht).deriv
  have hg : ContinuousOn (fun t : ℝ ↦ 1 - 81 / 100 * (1 / (2 * Real.sqrt t))) (Set.uIcc r V) :=
    fun t ht ↦
    (continuousAt_const.sub
        (continuousAt_const.mul
          (continuousAt_const.div (continuousAt_const.mul Real.continuous_sqrt.continuousAt)
            (mul_ne_zero (by norm_num only) (Real.sqrt_pos.mpr (pos ht)).ne')))).continuousWithinAt
  have hi :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (fun t ht ↦ (hd t ht).differentiableAt.hasDerivAt) he hc.intervalIntegrable
      hg.intervalIntegrable
  change
    (∫ t in r..V, f t * (1 - 81 / 100 * (1 / (2 * Real.sqrt t)))) =
      f V * (V - 81 / 100 * Real.sqrt V) - f r * (r - 81 / 100 * Real.sqrt r) -
        (∫ t in r..V, deriv f t * (t - 81 / 100 * Real.sqrt t)) at hi
  rw [show f V = 0 from weight_end h0, zero_mul] at hi
  have hab := squareRootWeight_abel hr hr'
  change
    -(f r * (r + 81 / 100 * Real.sqrt r)) -
        (∫ t in r..V, deriv f t * (t - 81 / 100 * Real.sqrt t)) ≤
      _ at hab
  linarith only [hi, hab]

/-- Bounding the square-root error density by its value at the lower endpoint
reduces square recovery to a single unweighted moment of the six-pole profile. -/
theorem squareRootWeight_moment_lower {r : ℝ} (hr : 465 / 2 ≤ r) (hr' : r ≤ 278) :
    let V := Real.exp (21 / 16) * r;
    let f := squareRootWeight r;
    (1 - 81 / 100 * (1 / (2 * Real.sqrt r))) * (∫ t in r..V, f t) -
        2 * (81 / 100) * Real.sqrt r * f r ≤
      ∑ k ∈ Finset.Ioc ⌊r⌋₊ ⌊V⌋₊, f k * ArithmeticFunction.vonMangoldt k := by
  intro V f
  have h0 : 0 < r := (by norm_num only : (0 : ℝ) < 465 / 2).trans_le hr
  have hV : r ≤ V := le_mul_of_one_le_left h0.le (Real.one_le_exp (by norm_num only))
  have pos {t : ℝ} (ht : t ∈ Set.uIcc r V) : 0 < t :=
    h0.trans_le ((Set.uIcc_of_le hV ▸ ht : t ∈ Set.Icc r V).1)
  have hf : ContinuousOn f (Set.uIcc r V) := fun t ht ↦
    (weight_deriv h0 (pos ht)).continuousAt.continuousWithinAt
  have hg : ContinuousOn (fun t : ℝ ↦ 1 - 81 / 100 * (1 / (2 * Real.sqrt t))) (Set.uIcc r V) :=
    fun t ht ↦
    (continuousAt_const.sub
        (continuousAt_const.mul
          (continuousAt_const.div (continuousAt_const.mul Real.continuous_sqrt.continuousAt)
            (mul_ne_zero (by norm_num only) (Real.sqrt_pos.mpr (pos ht)).ne')))).continuousWithinAt
  apply le_trans _ (squareRootWeight_integral_lower hr hr')
  apply sub_le_sub_right
  rw [← intervalIntegral.integral_const_mul]
  apply
    intervalIntegral.integral_mono_on hV (hf.intervalIntegrable.const_mul _)
      (hf.mul hg).intervalIntegrable
  intro t ht
  have ht0 := h0.trans_le ht.1
  have hw : 0 ≤ f t := by
    rw [show f t = refinedScaledWeight (r ^ 2) (t ^ 2) from squareRootWeight_eq_scaled h0 ht0 ht.2]
    unfold refinedScaledWeight refinedKernelWeight
    exact
      div_nonneg
        (div_nonneg (refinedSixPoleKernel.mellin_nonneg _ (div_pos (pow_pos ht0 2) (pow_pos h0 2)))
          (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _)
  rw [Pi.mul_apply, mul_comm (f t)]
  apply mul_le_mul_of_nonneg_right _ hw
  apply sub_le_sub_left
  exact
    mul_le_mul_of_nonneg_left
      (one_div_le_one_div_of_le (mul_pos (by norm_num only) (Real.sqrt_pos.mpr h0))
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ht.1) (by norm_num only)))
      (by norm_num only)

/-- The unweighted moment does not depend on the root radius. Substitution
by the radius cancels the scale factor in the principal weight. -/
theorem squareRootWeight_moment_eq {r : ℝ} (hr : 0 < r) :
    (∫ t in r..Real.exp (21 / 16) * r, squareRootWeight r t) =
      ∫ u in (1 : ℝ)..Real.exp (21 / 16), refinedWeight (u ^ 2) := by
  simp only [squareRootWeight, ← div_pow, intervalIntegral.integral_div]
  have h :=
    intervalIntegral.integral_comp_div (fun u : ℝ ↦ refinedWeight (u ^ 2)) (a := r) (b :=
      Real.exp (21 / 16) * r) hr.ne'
  rw [div_self hr.ne', mul_div_cancel_right₀ _ hr.ne', smul_eq_mul] at h
  rw [h, mul_div_cancel_left₀ _ hr.ne']

/-- A Taylor lower bound on exp(567/200) certifies the endpoint constant
for the six-pole recovery weight. -/
theorem refinedWeight_one_upper : refinedWeight 1 < 89611 / 1000000 := by
  have he := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 567 / 200) 18
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_succ,
    Nat.factorial_zero, Nat.cast_zero, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat] at he
  rw [refinedWeight, refinedCoord, Real.log_one, mul_zero, sub_zero, Real.sqrt_one, mul_one,
    Real.exp_neg, ← div_eq_mul_inv, div_div]
  apply (div_lt_iff₀ (mul_pos (Real.exp_pos _) (by norm_num only))).mpr
  linarith only [he]

private noncomputable def momentPrimitive (z : ℝ) : ℝ :=
  Real.exp (-z) * (z ^ 5 + 5 * z ^ 4 + 20 * z ^ 3 + 60 * z ^ 2 + 120 * z + 120) / (120 * (54 / 25))

private theorem primitive_deriv {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun x : ℝ ↦ momentPrimitive (refinedCoord (x ^ 2))) (refinedWeight (u ^ 2)) u := by
  have hz : HasDerivAt (fun x : ℝ ↦ refinedCoord (x ^ 2)) (-(54 / 25) / u) u := by
    have hd :=
      (refinedCoord_hasDerivAt (pow_pos hu 2)).comp (h := fun x : ℝ ↦ x ^ 2) u
        ((hasDerivAt_id u).pow 2)
    convert hd using 1
    · rfl
    dsimp only [id_eq, Nat.reduceSub, pow_one]
    field_simp [hu.ne']
    ring
  have hp :=
    (((((hz.pow 5).add ((hz.pow 4).const_mul 5)).add ((hz.pow 3).const_mul 20)).add
              ((hz.pow 2).const_mul 60)).add
          (hz.const_mul 120)).add_const
      120
  have hd := (hz.neg.exp.mul hp).div_const (120 * (54 / 25))
  convert hd using 1
  · rfl
  dsimp only [refinedWeight, Pi.add_apply, Pi.pow_apply, Pi.neg_apply, Nat.reduceSub]
  rw [Real.sqrt_sq hu.le]
  push_cast
  field_simp [hu.ne']
  ring

/-- Evaluate the normalized six-pole moment at both endpoints. The polynomial
primitive gives an exact expression involving one rational exponential. -/
private theorem squareMoment_exact :
    (∫ u in (1 : ℝ)..Real.exp (21 / 16), refinedWeight (u ^ 2)) =
      momentPrimitive 0 - momentPrimitive (567 / 200) := by
  have he : (1 : ℝ) ≤ Real.exp (21 / 16) := Real.one_le_exp (by norm_num only)
  have hu {u : ℝ} (h : u ∈ Set.uIcc 1 (Real.exp (21 / 16))) : 0 < u :=
    zero_lt_one.trans_le ((Set.uIcc_of_le he ▸ h : u ∈ Set.Icc 1 _).1)
  have hc : ContinuousOn (fun u : ℝ ↦ refinedWeight (u ^ 2)) (Set.uIcc 1 (Real.exp (21 / 16))) :=
    fun u h ↦
    ((refinedWeight_hasDerivAt (pow_pos (hu h) 2)).continuousAt.comp (f := fun x : ℝ ↦ x ^ 2)
        (continuousAt_id.pow 2)).continuousWithinAt
  have h :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u hu' ↦ primitive_deriv (hu hu'))
      hc.intervalIntegrable
  rw [h]
  congr 1
  · congr 1
    rw [refinedCoord, ← Real.exp_natCast_mul, Real.log_exp]
    norm_num only
  · rw [one_pow, refinedCoord, Real.log_one, mul_zero, sub_zero]

/-- The normalized recovery moment exceeds 0.0315762. Evaluate the primitive
and certify the remaining rational exponential by its positive Taylor sum. -/
theorem squareMoment_lower :
    315762 / 10000000 < ∫ u in (1 : ℝ)..Real.exp (21 / 16), refinedWeight (u ^ 2) := by
  have he := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 567 / 200) 22
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_succ,
    Nat.factorial_zero, Nat.cast_zero, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat] at he
  rw [squareMoment_exact]
  simp only [momentPrimitive, neg_zero, Real.exp_zero, Real.exp_neg]
  apply (lt_of_mul_lt_mul_right (a := Real.exp (567 / 200)) ?_ (Real.exp_pos _).le)
  field_simp [ne_of_gt (Real.exp_pos (567 / 200))]
  linarith only [he]

/-- On the entire first extension interval the square-root sum exceeds 0.021.
Use the radius-independent moment and the certified endpoint with sqrt r above
15. Multiplication by four supplies a recovery exceeding 0.084. -/
theorem squareRecovery_sum_lower {r : ℝ} (hr : 465 / 2 ≤ r) (hr' : r ≤ 278) :
    21 / 1000 <
      ∑ k ∈ Finset.Ioc ⌊r⌋₊ ⌊Real.exp (21 / 16) * r⌋₊,
        squareRootWeight r k * ArithmeticFunction.vonMangoldt k := by
  have h0 : 0 < r := (by norm_num only : (0 : ℝ) < 465 / 2).trans_le hr
  have hs : 15 ≤ Real.sqrt r := (Real.le_sqrt_of_sq_le (by linarith only [hr]))
  have hs0 := Real.sqrt_pos.mpr h0
  have h := squareRootWeight_moment_lower hr hr'
  dsimp only at h
  rw [squareRootWeight_moment_eq h0, squareRootWeight, div_self (pow_ne_zero 2 h0.ne')] at h
  have hu : Real.sqrt r * (refinedWeight 1 / r) = refinedWeight 1 / Real.sqrt r := by
    field_simp [h0.ne', hs0.ne']
    nlinarith only [congrArg (fun z : ℝ ↦ refinedWeight 1 * z) (Real.sq_sqrt h0.le)]
  rw [mul_assoc (2 * _), hu] at h
  have hc : (973 / 1000 : ℝ) ≤ 1 - 81 / 100 * (1 / (2 * Real.sqrt r)) := by
    have hi :=
      one_div_le_one_div_of_le (by norm_num only : (0 : ℝ) < 30)
        (show 30 ≤ 2 * Real.sqrt r by linarith only [hs])
    linarith only [hi]
  have hb : refinedWeight 1 / Real.sqrt r ≤ (89611 / 1000000) / 15 := by
    apply (div_le_iff₀ hs0).mpr
    linarith only [refinedWeight_one_upper, hs]
  have hm := mul_le_mul hc squareMoment_lower.le (by norm_num only) (by linarith only [hc])
  linarith only [hm, hb, h]

end PseudoPrime.PrimeTestBounds.MillerRabin
