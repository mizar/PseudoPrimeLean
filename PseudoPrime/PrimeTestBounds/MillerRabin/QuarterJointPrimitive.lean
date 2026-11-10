/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterJointElementary
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCommonScale
public import PseudoPrime.Analysis.NumericalLogBounds
public import PseudoPrime.Analysis.ExplicitLogSqrtAbsorption

/-! # Explicit primitive for the quarter-bound joint Abel estimate -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under the high-index no-witness hypotheses, evaluating the explicit joint
integral leaves a comparison of endpoint expressions only. This is the final
input for the scalar contradiction. -/
theorem quarter_high_primitive_cost {n : ℕ} [NeZero n] (hn : 1 < n) (ho : Odd n) {a r T : ℝ}
    (ha : 0 < a) (hr : 100 ≤ r) (hbound : Real.log (r ^ 2) = 2 * a) (hT : 0 ≤ T)
    (hscale : Real.log n ≤ T) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hindex : ⌊r ^ 2⌋₊ < (PrimeTest.fermatSubgroup n).index)
    (hnone :
      ¬∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n)) :
    (2 * a * (r ^ 2) ^ (-1 / 2 : ℝ)) *
          (r ^ 2 - (19 / 30 : ℝ) * (r ^ 2) ^ (3 / 4 : ℝ) - (63 / 10 : ℝ) * (r ^ 2) ^ (1 / 4 : ℝ) -
            1839 / 1000) +
        (quarterJointPrimitive a (r ^ 2) - quarterJointPrimitive a 16) <
      2 * a * T + 31 := by
  have hr2 : (16 : ℝ) ≤ r ^ 2 := by nlinarith only [sq_nonneg (r - 100), hr]
  have h := quarter_high_elementary_cost hn ho ha hr hbound hT hscale hGRH hindex hnone
  rw [quarter_joint_integral_eq (by norm_num only : (0 : ℝ) < 16) hr2] at h
  exact h

/-- From radius 100 onward, `log r` lies between four and an affine function
of `sqrt r`. A tangent at ten and certified logarithm bounds supply the
sharper estimate used to extend the high-index argument. -/
theorem quarter_log_radius_hundred {r : ℝ} (hr : 100 ≤ r) :
    4 ≤ Real.log r ∧ Real.log r ≤ Real.sqrt r / 5 + 263 / 100 := by
  have hr0 : 0 < r := by linarith only [hr]
  have hs : (0 : ℝ) < Real.sqrt r := Real.sqrt_pos.2 hr0
  have hlog100 := Real.log_le_log (by norm_num only : (0 : ℝ) < 100) hr
  have ht :=
    Analysis.log_le_log_add_sub_div (a := (10 : ℝ)) (y := Real.sqrt r) (by norm_num only) hs
  have h100 := Analysis.log_hundred_le_fourHundredSixtyThree_hundredths
  have hten := Analysis.two_le_log_ten
  have hteneq : Real.log (100 : ℝ) = 2 * Real.log 10 := by
    rw [show (100 : ℝ) = 10 ^ (2 : ℕ) by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  have hslog := Real.log_sqrt hr0.le
  constructor
  · linarith only [hlog100, hten, hteneq]
  · linarith only [ht, h100, hteneq, hslog]

/-- A scalar margin valid from square-root radius ten. The reciprocal term
is retained on `[10,11]`; beyond 11 the quadratic term suffices by itself. -/
theorem quarter_joint_scalar_hundred {a s L : ℝ} (hs : (10 : ℝ) ≤ s) (ha : 4 ≤ a)
    (hau : a ≤ s / 5 + 263 / 100) (hL : (27 / 10 : ℝ) ≤ L) :
    0 <
      4 * s ^ 2 - (19 / 5 : ℝ) * a * s - (38 / 5 : ℝ) * s - (98717 / 3000 : ℝ) * a - 96 / 5 +
        (98717 / 12000 : ℝ) * L +
        ((63 / 5 : ℝ) * a - 126 / 5) / s := by
  have hs0 : 0 < s := by linarith only [hs]
  have hmul := mul_le_mul_of_nonneg_right hau hs0.le
  have hnum : 0 ≤ (63 / 5 : ℝ) * a - 126 / 5 := by linarith only [ha]
  by_cases hsmall : s ≤ 11
  · have hrec : (126 / 55 : ℝ) ≤ ((63 / 5 : ℝ) * a - 126 / 5) / s := by
      apply (le_div_iff₀ hs0).2
      nlinarith only [ha, hsmall]
    have hp :=
      mul_nonneg (show 0 ≤ s - 10 by linarith only [hs])
        (show 0 ≤ (81 / 25 : ℝ) * s - 1 by linarith only [hs])
    nlinarith only [hmul, hau, hL, hrec, hp, hs]
  · have hlarge : (11 : ℝ) ≤ s := le_of_lt (lt_of_not_ge hsmall)
    have hrec := div_nonneg hnum hs0.le
    have hp :=
      mul_nonneg (show 0 ≤ s - 11 by linarith only [hlarge])
        (show 0 ≤ (81 / 25 : ℝ) * s - 1 by linarith only [hlarge])
    nlinarith only [hmul, hau, hL, hrec, hp, hlarge]

/-- At the upper support endpoint, the boundary Chebyshev lower expression
and the primitive combine into three power terms. The constant-error terms
cancel before the scalar comparison. -/
theorem quarter_joint_primitive_endpoint {a X : ℝ} (hX : 0 < X) (hbound : Real.log X = 2 * a) :
    (2 * a * X ^ (-1 / 2 : ℝ)) *
          (X - (19 / 30 : ℝ) * X ^ (3 / 4 : ℝ) - (63 / 10 : ℝ) * X ^ (1 / 4 : ℝ) - 1839 / 1000) +
        quarterJointPrimitive a X =
      (4 * a + 4) * Real.sqrt X - ((19 / 5 : ℝ) * a + 38 / 5) * X ^ (1 / 4 : ℝ) +
        ((63 / 5 : ℝ) * a - 126 / 5) * X ^ (-1 / 4 : ℝ) := by
  have h1 : X ^ (-1 / 2 : ℝ) * X = Real.sqrt X := by
    have h := Real.rpow_add hX (-1 / 2) 1
    norm_num only [Real.rpow_one] at h
    simpa only [neg_div, Real.sqrt_eq_rpow] using h.symm
  have h2 : X ^ (-1 / 2 : ℝ) * X ^ (3 / 4 : ℝ) = X ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add hX]
    congr 1
    norm_num only
  have h3 : X ^ (-1 / 2 : ℝ) * X ^ (1 / 4 : ℝ) = X ^ (-1 / 4 : ℝ) := by
    rw [← Real.rpow_add hX]
    congr 1
    norm_num only
  dsimp only [quarterJointPrimitive]
  rw [← Real.sqrt_eq_rpow, hbound]
  calc
    _ =
        (2 * a) * (X ^ (-1 / 2 : ℝ) * X) + (2 * a + 4) * Real.sqrt X -
          (19 / 30 : ℝ) *
            ((2 * a) * (X ^ (-1 / 2 : ℝ) * X ^ (3 / 4 : ℝ)) + (4 * a + 12) * X ^ (1 / 4 : ℝ)) -
          (63 / 10 : ℝ) *
            ((2 * a) * (X ^ (-1 / 2 : ℝ) * X ^ (1 / 4 : ℝ)) + (-4 * a + 4) * X ^ (-1 / 4 : ℝ)) :=
      by ring
    _ = _ := by
      rw [h1, h2, h3]; ring

/-- The evaluated principal lower bound exceeds its high-index upper budget
at radius `r ≥ 100`. The logarithmic radius estimates and algebraic margin
establish the strict contradiction without any numerical search. -/
theorem quarter_joint_endpoint_gap {a r : ℝ} (hr : 100 ≤ r) (hbound : Real.log (r ^ 2) = 2 * a) :
    2 * a * (2 * r) + 31 <
      (2 * a * (r ^ 2) ^ (-1 / 2 : ℝ)) *
          (r ^ 2 - (19 / 30 : ℝ) * (r ^ 2) ^ (3 / 4 : ℝ) - (63 / 10 : ℝ) * (r ^ 2) ^ (1 / 4 : ℝ) -
            1839 / 1000) +
        (quarterJointPrimitive a (r ^ 2) - quarterJointPrimitive a 16) := by
  have hr0 : 0 < r := by linarith only [hr]
  have hs0 : 0 < Real.sqrt r := Real.sqrt_pos.2 hr0
  have hs2 := Real.sq_sqrt hr0.le
  have hs : (10 : ℝ) ≤ Real.sqrt r := by nlinarith only [hr, hs0, hs2]
  have hlog := quarter_log_radius_hundred hr
  have halog : a = Real.log r := by
    rw [Real.log_pow] at hbound
    norm_num only [Nat.cast_ofNat] at hbound
    linarith only [hbound]
  have ha : 4 ≤ a := by linarith only [hlog.1, halog]
  have hau : a ≤ Real.sqrt r / 5 + 263 / 100 := by linarith only [hlog.2, halog]
  have hL : (27 / 10 : ℝ) ≤ Real.log 16 := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_gt_d9]
  have hmargin := quarter_joint_scalar_hundred hs ha hau hL
  have hquarter : (r ^ 2) ^ (1 / 4 : ℝ) = Real.sqrt r := by
    rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr0.le]
    norm_num only [Real.sqrt_eq_rpow]
  have hquarterInv : (r ^ 2) ^ (-1 / 4 : ℝ) = (Real.sqrt r)⁻¹ := by
    rw [neg_div, Real.rpow_neg (sq_nonneg r), hquarter]
  have hsqr : Real.sqrt (r ^ 2) = r := Real.sqrt_sq hr0.le
  have hend := quarter_joint_primitive_endpoint (sq_pos_of_pos hr0) hbound
  rw [hquarter, hquarterInv, hsqr] at hend
  rw [hquarter, quarter_joint_primitive_sixteen]
  simp only [div_eq_mul_inv] at hmargin
  nlinarith only [hmargin, hend, hs2]

/-- Under GRH, every odd composite with logarithm at most `2r` and Fermat
index above `floor r²` has a rejecting prime at most `r²` for `r ≥ 100`.
The explicit high-index comparison contradicts the joint endpoint gap. -/
theorem quarter_high_index_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r : ℝ} (hr : 100 ≤ r)
    (hscale : Real.log n ≤ 2 * r) (hindex : ⌊r ^ 2⌋₊ < (PrimeTest.fermatSubgroup n).index) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  have hr0 : 0 < r := by linarith only [hr]
  have ha : 0 < Real.log r := by
    have h := (quarter_log_radius_hundred hr).1
    linarith only [h]
  have hbound : Real.log (r ^ 2) = 2 * Real.log r := by
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  by_contra hnone
  have hc :=
    quarter_high_primitive_cost hn ho ha hr hbound (by linarith only [hr] : 0 ≤ 2 * r) hscale hGRH
      hindex hnone
  have hg := quarter_joint_endpoint_gap hr hbound
  linarith only [hc, hg]

/-- Under GRH, a nonuniform odd composite whose logarithm is at most a common
scale `T ≥ 200` has a rejecting prime at most `T²/4`. Below 300 the fixed
index threshold and the strengthened high-index bound overlap; above 300 the
variable-index branch applies. -/
theorem quarter_common_nonuniform {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hu : ¬UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {T : ℝ} (hT : 200 ≤ T) (hscale : Real.log n ≤ T) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (1 / 4 : ℝ) * T ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  by_cases hlarge : 300 ≤ T
  · by_cases hi : (PrimeTest.fermatSubgroup n).index ≤ ⌊(T / 2) ^ 2⌋₊
    · exact quarter_common_floor_index hn ho hc hu hGRH hlarge hscale hi
    · obtain ⟨p, hp, hb, hf⟩ :=
        quarter_high_index_witness hn ho hGRH (r := T / 2) (by linarith only [hT])
          (by linarith only [hscale]) (Nat.lt_of_not_ge hi)
      refine ⟨p, hp, ?_, hf⟩
      nlinarith only [hb]
  · by_cases hi : (PrimeTest.fermatSubgroup n).index ≤ 33000
    · exact
        quarter_common_index_le hn ho hc (PrimeTest.fermatSubgroup n) le_rfl hi hu hGRH
          (by linarith only [hT]) hscale
    · have hfloor : ⌊(T / 2) ^ 2⌋₊ ≤ 33000 := by
        apply Nat.lt_succ_iff.mp
        apply (Nat.floor_lt (sq_nonneg (T / 2))).mpr
        norm_num only [Nat.cast_ofNat]
        nlinarith only [hT, lt_of_not_ge hlarge, sq_nonneg (T / 2 - 150)]
      obtain ⟨p, hp, hb, hf⟩ :=
        quarter_high_index_witness hn ho hGRH (r := T / 2) (by linarith only [hT])
          (by linarith only [hscale]) (lt_of_le_of_lt hfloor (Nat.lt_of_not_ge hi))
      refine ⟨p, hp, ?_, hf⟩
      nlinarith only [hb]

/-- Under GRH, every nonuniform odd composite with `log n ≥ 200` has a
rejecting prime at most `(log n)²/4`. Apply the common-scale theorem at the
input's own logarithmic scale. -/
theorem quarter_nonuniform_high {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hu : ¬UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlog : (200 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  exact quarter_common_nonuniform hn ho hc hu hGRH hlog le_rfl

end PseudoPrime.PrimeTestBounds.MillerRabin
