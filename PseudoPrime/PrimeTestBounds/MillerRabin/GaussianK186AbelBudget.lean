/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186ForwardAbel
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianAbelErrorBound
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186AbelTail
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186AbelCellCert

import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186ForwardAbel
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleTailBudget

/-! # Weighted integral budgets for the K186 Abel residual -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The log-weighted error anchored at one in the Abel residual. -/
private noncomputable def anchoredError (t : ℝ) : ℝ :=
  AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t -
      (t - Real.log (2 * Real.pi) * Real.log t) +
    1

/-- Pointwise control by the square root transfers to a weighted integral. -/
private theorem anchored_integral_le {Q : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b)
    (hQ : IntervalIntegrable (fun t ↦ Real.sqrt t * |Q t|) MeasureTheory.volume a b)
    (h : ∀ t ∈ Set.Icc a b, |anchoredError t| ≤ C * Real.sqrt t) :
    |∫ t in a..b, anchoredError t * Q t| ≤ C * (∫ t in a..b, Real.sqrt t * |Q t|) := by
  rw [← intervalIntegral.integral_const_mul]
  apply
    intervalIntegral.norm_integral_le_of_norm_le (μ := MeasureTheory.volume) (f := fun t ↦
      anchoredError t * Q t) hab ?_ (hQ.const_mul C)
  exact
    Filter.Eventually.of_forall fun t ht ↦ by
      rw [Real.norm_eq_abs, abs_mul, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (h t ⟨ht.1.le, ht.2⟩) (abs_nonneg _)

/-- The anchored integrand is interval integrable above one. This allows
adjacent pieces to be joined before estimating their absolute values. -/
private theorem anchored_mul_integrable {Q : ℝ → ℝ} (hQ : ContinuousOn Q (Set.Ioi 0)) {a b : ℝ}
    (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t ↦ anchoredError t * Q t) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hab]
  have hpos : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := fun _ ht ↦ zero_lt_one.trans_le (ha.trans ht.1)
  have hs : ContinuousOn AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (Set.Icc a b) := by
    have hc :=
      AnalyticNumberTheory.Arithmetic.continuousOn_logWeightedMangoldtSum_scaled (x := 1)
        (by norm_num only) b
    simp only [one_mul] at hc
    exact hc.mono fun _ ht ↦ ⟨(zero_le_one.trans ha).trans ht.1, ht.2⟩
  have hl := Real.continuousOn_log.mono (fun t ht ↦ (hpos ht).ne')
  exact
    ((hs.sub (continuousOn_id.sub (continuousOn_const.mul hl))).add continuousOn_const).mul
      (hQ.mono hpos)

/-- A split at a point above one million
reduces the Abel residual to three weighted absolute integrals and one value. -/
theorem k186_abel_residual_split_le (hRH : RiemannHypothesis) {x T A C₁ C₂ E : ℝ} (hT : 10 ^ 6 ≤ T)
    (hTX : T ≤ Real.exp x)
    (h :
      let X := Real.exp x
      let Y := Real.exp (x + 5)
      let W :=
        middlePrincipalWeight HighGaussianKernel.k186.realProfile
          (Real.exp (-(11 / 4 : ℝ) * (x + 5))) (x + 5) (9 / 4)
      let P := fun t ↦ t * deriv W t
      let f := fun t ↦ Real.sqrt t * |deriv P t|
      (∫ t in (1 : ℝ)..T, f t) ≤ A ∧
        (∫ t in T..X, f t) ≤ C₁ ∧ (∫ t in X..Y, f t) ≤ C₂ ∧ Real.sqrt X * |P X| ≤ E) :
    -(3 * A + 51 / 1000 * (3 * C₁ + C₂ + 4 * E)) ≤ k186AbelResidual x := by
  let X := Real.exp x
  let Y := Real.exp (x + 5)
  let B := HighGaussianKernel.k186.realProfile
  let W := middlePrincipalWeight B (Real.exp (-(11 / 4 : ℝ) * (x + 5))) (x + 5) (9 / 4)
  let P := fun t ↦ t * deriv W t
  let Q := deriv P
  let f := fun t ↦ Real.sqrt t * |Q t|
  have hT₁ : 1 ≤ T := (by norm_num only : (1 : ℝ) ≤ 10 ^ 6).trans hT
  change T ≤ X at hTX
  have hXY : X ≤ Y := Real.exp_le_exp.mpr (le_add_of_nonneg_right (by norm_num only))
  have hQ : ContinuousOn Q (Set.Ioi 0) := middle_principal_moment_cont B _ _ _
  have hf (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) : IntervalIntegrable f MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact
      Real.continuous_sqrt.continuousOn.mul
        (hQ.abs.mono fun _ ht ↦ zero_lt_one.trans_le (ha.trans ht.1))
  obtain ⟨ha, hb, hc, hp⟩ := h
  have hA :=
    anchored_integral_le (Q := Q) (C := 1) hT₁ (hf 1 T le_rfl hT₁)
      (fun t ht ↦ by simpa only [anchoredError, one_mul] using anchored_log_error_le_sqrt hRH ht.1)
  have hB :=
    anchored_integral_le (Q := Q) hTX (hf T X hT₁ hTX)
      (fun _ ht ↦ anchored_log_error_le_large hRH (hT.trans ht.1))
  have hC :=
    anchored_integral_le (Q := Q) hXY (hf X Y (hT₁.trans hTX) hXY)
      (fun _ ht ↦ anchored_log_error_le_large hRH ((hT.trans hTX).trans ht.1))
  have hP :=
    mul_le_mul_of_nonneg_right (anchored_log_error_le_large hRH (hT.trans hTX)) (abs_nonneg (P X))
  change |anchoredError X| * |P X| ≤ (51 / 1000 * Real.sqrt X) * |P X| at hP
  rw [← abs_mul, mul_comm (anchoredError X) (P X), mul_assoc] at hP
  have hF :=
    intervalIntegral.integral_add_adjacent_intervals (anchored_mul_integrable hQ le_rfl hT₁)
      (anchored_mul_integrable hQ hT₁ hTX)
  have hG :=
    intervalIntegral.integral_add_adjacent_intervals
      (anchored_mul_integrable hQ le_rfl (hT₁.trans hTX))
      (anchored_mul_integrable hQ (hT₁.trans hTX) hXY)
  change
    _ ≤
      4 * (∫ t in (1 : ℝ)..X, anchoredError t * Q t) - (∫ t in (1 : ℝ)..Y, anchoredError t * Q t) -
        4 * (P X * anchoredError X)
  rw [← hG, ← hF]
  linarith only [ha, hb, hc, hp, (abs_le.mp hA).1, (abs_le.mp hB).1, (abs_le.mp hC).2,
    (abs_le.mp hP).2]

/-- A finite split at the point corresponding to profile coordinate 35
reduces the Abel residual to three weighted absolute integrals and one value. -/
theorem k186_abel_residual_of_integrals (hRH : RiemannHypothesis) {x : ℝ} (hx : 60 ≤ x)
    (h :
      let X := Real.exp x
      let Y := Real.exp (x + 5)
      let T := Real.exp (x - 30)
      let W :=
        middlePrincipalWeight HighGaussianKernel.k186.realProfile
          (Real.exp (-(11 / 4 : ℝ) * (x + 5))) (x + 5) (9 / 4)
      let P := fun t ↦ t * deriv W t
      let f := fun t ↦ Real.sqrt t * |deriv P t|
      (∫ t in (1 : ℝ)..T, f t) ≤ 2300 ∧
        (∫ t in T..X, f t) ≤ 59000 ∧ (∫ t in X..Y, f t) ≤ 67000 ∧ Real.sqrt X * |P X| ≤ 5) :
    -19798 ≤ k186AbelResidual x := by
  let T := Real.exp (x - 30)
  have hT : (10 : ℝ) ^ 6 ≤ T := by
    have he :=
      pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 2)
        ((by norm_num only : (2 : ℝ) ≤ 2.7182818283).trans Real.exp_one_gt_d9.le) 30
    have heq : Real.exp 30 = Real.exp 1 ^ 30 := by
      rw [← Real.exp_natCast_mul]
      norm_num only
    have h₁ : (10 : ℝ) ^ 6 ≤ Real.exp 30 := by
      rw [heq]
      exact (by norm_num only : (10 : ℝ) ^ 6 ≤ 2 ^ 30).trans he
    exact h₁.trans (Real.exp_le_exp.mpr (by linarith only [hx]))
  have hTX : T ≤ Real.exp x := Real.exp_le_exp.mpr (sub_le_self _ (by norm_num only))
  have hb := k186_abel_residual_split_le hRH hT hTX h
  linarith only [hb]

/-- In profile coordinates the square-root weighted derivative, including
the Jacobian, is independent of the moving logarithmic cutoff. -/
theorem k186_abel_weight_log (z v : ℝ) :
    let B := HighGaussianKernel.k186.realProfile
    let Q := Polynomial.C (9 / 4 : ℝ) * B - B.derivative
    let D := Polynomial.C (9 / 4 : ℝ) * Q - Q.derivative
    let W := middlePrincipalWeight B (Real.exp (-(11 / 4 : ℝ) * z)) z (9 / 4)
    let P := fun t ↦ t * deriv W t
    let t := Real.exp (z - v)
    Real.sqrt t * |deriv P t| * t = Real.exp (-(11 / 4 : ℝ) * v) * |D.eval v| := by
  intro B Q D W P t
  have ht : 0 < t := Real.exp_pos _
  have hd := (middle_principal_moment_deriv B (Real.exp (-(11 / 4 : ℝ) * z)) z (9 / 4) ht).deriv
  change
    deriv P t =
      Real.exp (-(11 / 4 : ℝ) * z) * (t ^ ((9 / 4 : ℝ) - 1) * D.eval (z - Real.log t)) at hd
  rw [hd, Real.sqrt_eq_rpow, Real.rpow_def_of_pos ht, Real.rpow_def_of_pos ht]
  have hl : Real.log t = z - v := Real.log_exp _
  rw [hl, sub_sub_cancel, abs_mul, abs_mul, abs_of_nonneg (Real.exp_nonneg (-(11 / 4 : ℝ) * z)),
    abs_of_nonneg (Real.exp_nonneg ((z - v) * ((9 / 4 : ℝ) - 1)))]
  change _ * _ * Real.exp (z - v) = _
  calc
    _ =
        (Real.exp ((z - v) * (1 / 2 : ℝ)) * Real.exp (-(11 / 4 : ℝ) * z) *
            Real.exp ((z - v) * ((9 / 4 : ℝ) - 1)) *
            Real.exp (z - v)) *
          |D.eval v| :=
      by ring
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 2
      ring

/-- Integrating the weighted Abel derivative in the reversed log coordinate
reduces the verification to a fixed polynomial and exponential. -/
theorem k186_abel_integral_log (z a b : ℝ) :
    let B := HighGaussianKernel.k186.realProfile
    let Q := Polynomial.C (9 / 4 : ℝ) * B - B.derivative
    let D := Polynomial.C (9 / 4 : ℝ) * Q - Q.derivative
    let W := middlePrincipalWeight B (Real.exp (-(11 / 4 : ℝ) * z)) z (9 / 4)
    let P := fun t ↦ t * deriv W t
    (∫ t in Real.exp (z - b)..Real.exp (z - a), Real.sqrt t * |deriv P t|) =
      ∫ v in a..b, Real.exp (-(11 / 4 : ℝ) * v) * |D.eval v| := by
  intro B Q D W P
  let g := fun t ↦ Real.sqrt t * |deriv P t|
  have hd (v : ℝ) : HasDerivAt (fun u ↦ Real.exp (z - u)) (-Real.exp (z - v)) v := by
    simpa only [Pi.sub_apply, id_eq, zero_sub, mul_neg, mul_one] using
      ((hasDerivAt_const v z).sub (hasDerivAt_id v)).exp
  have h :=
    intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos (g := g) (a := a) (b := b)
      (Real.continuous_exp.comp (continuous_const.sub continuous_id)).continuousOn (fun v _ ↦ hd v)
      (fun v _ ↦ neg_nonpos.mpr (Real.exp_nonneg _))
  change
    (∫ v in a..b, g (Real.exp (z - v)) * -Real.exp (z - v)) =
      ∫ t in Real.exp (z - a)..Real.exp (z - b), g t at h
  calc
    _ = -(∫ t in Real.exp (z - a)..Real.exp (z - b), g t) := by rw [intervalIntegral.integral_symm]
    _ = _ := by
      rw [← h]
      simp only [mul_neg, intervalIntegral.integral_neg, neg_neg]
      exact intervalIntegral.integral_congr fun v _ ↦ k186_abel_weight_log z v

/-- The remaining Abel endpoint is bounded using the value and first
derivative at five in the already verified K186 integer profile row. -/
theorem k186_abel_profile_endpoint :
    let B := HighGaussianKernel.k186.realProfile
    let Q := Polynomial.C (9 / 4 : ℝ) * B - B.derivative
    Real.exp (-(55 / 4 : ℝ)) * |Q.eval 5| ≤ 5 := by
  intro B Q
  have hB : 0 ≤ B.eval 5 := (high_real_profile_at_five_pos .k186).le
  have hQ : |Q.eval 5| ≤ 625000 := by
    simp only [Q, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
    refine (abs_sub_le _ 0 _).trans ?_
    simp only [sub_zero, zero_sub, abs_neg,
      abs_of_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 9 / 4) hB)]
    have hb : B.eval 5 ≤ 100000 := k186_profile_five_le
    have hd : |B.derivative.eval 5| ≤ 400000 := k186_profile_deriv_five_abs_le
    linarith only [hb, hd]
  have hE : Real.exp (-(55 / 4 : ℝ)) ≤ 1 / 800000 := by
    rw [show -(55 / 4 : ℝ) = -55 / 4 by ring]
    exact k186_exp_neg_pole_le
  exact (mul_le_mul hE hQ (abs_nonneg _) (by norm_num only)).trans (by norm_num only)

/-- The moving raw Abel endpoint always uses the fixed profile coordinate five. -/
theorem k186_abel_endpoint_abs_le (x : ℝ) :
    let W :=
      middlePrincipalWeight HighGaussianKernel.k186.realProfile (Real.exp (-(11 / 4 : ℝ) * (x + 5)))
        (x + 5) (9 / 4)
    Real.sqrt (Real.exp x) * |Real.exp x * deriv W (Real.exp x)| ≤ 5 := by
  let B := HighGaussianKernel.k186.realProfile
  have hp := k186_abel_profile_endpoint
  dsimp only at hp
  have he :=
    middle_principal_t_mul_deriv HighGaussianKernel.k186.realProfile
      (Real.exp (-(11 / 4 : ℝ) * (x + 5))) (x + 5) (9 / 4) (Real.exp_pos x)
  dsimp only
  rw [he, Real.sqrt_eq_rpow]
  simp only [middlePrincipalWeight, Real.rpow_def_of_pos (Real.exp_pos x), Real.log_exp,
    show x + 5 - x = 5 by ring, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
  let A := |(Polynomial.C (9 / 4 : ℝ) * B - B.derivative).eval 5|
  convert hp using 1
  calc
    _ =
        (Real.exp (x * (1 / 2 : ℝ)) * Real.exp (-(11 / 4 : ℝ) * (x + 5)) *
            Real.exp (x * (9 / 4 : ℝ))) *
          A :=
      by
      dsimp only [A, B]
      ring
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 2
      ring

/-- The polynomial multiplying the exponential in the second Abel derivative. -/
noncomputable def k186AbelPoly : Polynomial ℝ :=
  let B := HighGaussianKernel.k186.realProfile
  let Q := Polynomial.C (9 / 4 : ℝ) * B - B.derivative
  Polynomial.C (9 / 4 : ℝ) * Q - Q.derivative

/-- The weight of the absolute second Abel derivative after the logarithmic substitution. -/
noncomputable def k186AbelWeight (v : ℝ) : ℝ :=
  Real.exp (-(11 / 4 : ℝ) * v) * |k186AbelPoly.eval v|

/-- An exponential-polynomial square is integrable at positive Laplace rate. -/
private theorem abel_square_integrable (P : Polynomial ℝ) :
    MeasureTheory.IntegrableOn (fun t : ℝ ↦ P.eval t ^ 2 * Real.exp (-5 * t)) (Set.Ioi 0) := by
  simp only [← Polynomial.eval_pow]
  simp only [Polynomial.eval_eq_sum_range, Finset.sum_mul, mul_assoc]
  apply MeasureTheory.integrable_finsetSum
  intro k _
  have h : (-1 : ℝ) < k := neg_one_lt_zero.trans_le (Nat.cast_nonneg k)
  have hi :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) h zero_lt_one
      (show (0 : ℝ) < 5 by norm_num only)
  simp only [Real.rpow_natCast, Real.rpow_one] at hi
  exact hi.const_mul _

/-- Young's inequality bounds a finite weighted absolute integral using
one full squared Laplace moment and the elementary exponential tail. -/
theorem abel_abs_le_square_moment (P : Polynomial ℝ) {a b r M : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hr : 0 < r) (hm : (∫ v in Set.Ioi (0 : ℝ), P.eval v ^ 2 * Real.exp (-5 * v)) ≤ M) :
    (∫ v in a..b, Real.exp (-(11 / 4 : ℝ) * v) * |P.eval v|) ≤
      r * Real.exp (-(1 / 2 : ℝ) * a) + M / (2 * r) := by
  let F := fun v : ℝ ↦ Real.exp (-(1 / 2 : ℝ) * v)
  let G := fun v : ℝ ↦ P.eval v ^ 2 * Real.exp (-5 * v)
  have hF : Continuous F := Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hG : Continuous G :=
    (P.continuous.pow 2).mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have hleft : Continuous (fun v : ℝ ↦ Real.exp (-(11 / 4 : ℝ) * v) * |P.eval v|) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul P.continuous.abs
  have hp (v : ℝ) :
    Real.exp (-(11 / 4 : ℝ) * v) * |P.eval v| ≤ (r / 2) * F v + (1 / (2 * r)) * G v := by
    have h₁ : Real.exp (-(1 / 4 : ℝ) * v) ^ 2 = F v := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have h₂ : Real.exp (-(5 / 2 : ℝ) * v) ^ 2 * |P.eval v| ^ 2 = G v := by
      rw [sq_abs, pow_two (Real.exp _), ← Real.exp_add, mul_comm]
      congr 2
      ring
    have h₃ :
      Real.exp (-(1 / 4 : ℝ) * v) * Real.exp (-(5 / 2 : ℝ) * v) = Real.exp (-(11 / 4 : ℝ) * v) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hs :=
      sq_nonneg (r * Real.exp (-(1 / 4 : ℝ) * v) - Real.exp (-(5 / 2 : ℝ) * v) * |P.eval v|)
    calc
      _ ≤ (r ^ 2 * F v + G v) / (2 * r) := by
        apply (le_div_iff₀ (show 0 < 2 * r by positivity)).mpr
        rw [← h₁, ← h₂, ← h₃]
        nlinarith only [hs]
      _ = _ := by field_simp [hr.ne']
  have hI :=
    intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hab (hleft.intervalIntegrable a b)
      (((hF.const_mul _).add (hG.const_mul _)).intervalIntegrable a b) (fun v _ ↦ hp v)
  change _ ≤ (∫ v in a..b, (r / 2) * F v + (1 / (2 * r)) * G v) at hI
  rw [intervalIntegral.integral_add ((hF.const_mul _).intervalIntegrable a b)
      ((hG.const_mul _).intervalIntegrable a b),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hI
  have hf : (∫ v in a..b, F v) ≤ 2 * F a := by
    rw [intervalIntegral.integral_of_le hab]
    have hfi := integrableOn_exp_mul_Ioi (show (-(1 / 2) : ℝ) < 0 by norm_num only) a
    refine
      (MeasureTheory.setIntegral_mono_set hfi
            (Filter.Eventually.of_forall fun v ↦ Real.exp_nonneg (-(1 / 2 : ℝ) * v))
            (Filter.Eventually.of_forall fun v (hv : v ∈ Set.Ioc a b) ↦ hv.1)).trans_eq
        ?_
    dsimp only [F]
    rw [integral_exp_mul_Ioi (by norm_num only : (-(1 / 2) : ℝ) < 0)]
    ring
  have hg : (∫ v in a..b, G v) ≤ M := by
    rw [intervalIntegral.integral_of_le hab]
    exact
      (MeasureTheory.setIntegral_mono_set (abel_square_integrable P)
            (Filter.Eventually.of_forall fun v ↦
              mul_nonneg (sq_nonneg (P.eval v)) (Real.exp_nonneg _))
            (Filter.Eventually.of_forall fun v (hv : v ∈ Set.Ioc a b) ↦ ha.trans_lt hv.1)).trans
        hm
  exact
    hI.trans
      (by
        have hf' := mul_le_mul_of_nonneg_left hf (show 0 ≤ r / 2 by positivity)
        have hg' := mul_le_mul_of_nonneg_left hg (show 0 ≤ 1 / (2 * r) by positivity)
        rw [show (r / 2) * (2 * F a) = r * F a by ring] at hf'
        exact (add_le_add hf' hg').trans_eq (by rw [one_div_mul_eq_div]))

/-- The split residual estimate can be evaluated directly in profile
coordinates. The split is valid as soon as its original coordinate is at least one million. -/
theorem k186_abel_split_profile (hRH : RiemannHypothesis) {x b A C₁ C₂ : ℝ} (hb : 5 ≤ b)
    (hT : 10 ^ 6 ≤ Real.exp (x + 5 - b)) (ha : (∫ v in b..x + 5, k186AbelWeight v) ≤ A)
    (h₁ : (∫ v in (5 : ℝ)..b, k186AbelWeight v) ≤ C₁)
    (h₂ : (∫ v in (0 : ℝ)..5, k186AbelWeight v) ≤ C₂) :
    -(3 * A + 51 / 1000 * (3 * C₁ + C₂ + 20)) ≤ k186AbelResidual x := by
  have hTX := Real.exp_le_exp.mpr (show x + 5 - b ≤ x by linarith only [hb])
  rw [show (20 : ℝ) = 4 * 5 by norm_num only]
  apply k186_abel_residual_split_le hRH hT hTX (E := 5)
  have e₀ := k186_abel_integral_log (x + 5) b (x + 5)
  have e₁ := k186_abel_integral_log (x + 5) 5 b
  have e₂ := k186_abel_integral_log (x + 5) 0 5
  simp only [sub_self, Real.exp_zero] at e₀
  simp only [add_sub_cancel_right] at e₁
  simp only [sub_zero, add_sub_cancel_right] at e₂
  exact ⟨e₀.trans_le ha, e₁.trans_le h₁, e₂.trans_le h₂, k186_abel_endpoint_abs_le x⟩

/-- The rate-five square moment of the K186 second Abel polynomial. -/
noncomputable def k186AbelSquare : ℝ :=
  ∫ v in Set.Ioi (0 : ℝ), k186AbelPoly.eval v ^ 2 * Real.exp (-5 * v)

/-- A single square moment bounds the full K186 Abel residual for every
cutoff logarithm at least 30, with the split fixed at the original coordinate exp(14). -/
theorem k186_abel_residual_of_square (hRH : RiemannHypothesis) {x : ℝ} (hx : 30 ≤ x)
    (hm : k186AbelSquare ≤ 11 / 50) : -(6 / 5 : ℝ) ≤ k186AbelResidual x := by
  let b := x + 5 - 14
  have hb : 21 ≤ b := by
    dsimp only [b]; linarith only [hx]
  have h5 : (5 : ℝ) ≤ b := (by norm_num only : (5 : ℝ) ≤ 21).trans hb
  have hT : (10 : ℝ) ^ 6 ≤ Real.exp (x + 5 - b) := by
    rw [show x + 5 - b = 14 by
        dsimp only [b]; ring,
      show Real.exp 14 = Real.exp 1 ^ 14 by
        rw [← Real.exp_natCast_mul]; norm_num only]
    exact
      (by norm_num only : (10 : ℝ) ^ 6 ≤ (27 / 10) ^ 14).trans
        (pow_le_pow_left₀ (by norm_num only)
          ((by norm_num only : (27 / 10 : ℝ) ≤ 2.7182818283).trans Real.exp_one_gt_d9.le) 14)
  have he : Real.exp (-(1 / 2 : ℝ) * b) ≤ 3 / 100000 := by
    have h :=
      (middle_tail_exp_le 840 (by decide +kernel)).trans
        (Rat.cast_le.mpr (by decide +kernel : 1 / middleTailExpDen 840 ≤ 3 / 100000))
    norm_num only [Nat.cast_ofNat, Rat.cast_div, Rat.cast_ofNat] at h
    exact (Real.exp_le_exp.mpr (show -(1 / 2 : ℝ) * b ≤ -(21 / 2) by linarith only [hb])).trans h
  have hf {a c : ℝ} (ha : 0 ≤ a) (hac : a ≤ c) : (∫ v in a..c, k186AbelWeight v) ≤ 2 / 3 := by
    refine
      (abel_abs_le_square_moment k186AbelPoly ha hac (show (0 : ℝ) < 1 / 3 by norm_num only)
            hm).trans
        ?_
    have hE := Real.exp_le_one_iff.mpr (show -(1 / 2 : ℝ) * a ≤ 0 by linarith only [ha])
    linarith only [hE]
  have ha : (∫ v in b..x + 5, k186AbelWeight v) ≤ 1 / 250 := by
    refine
      (abel_abs_le_square_moment k186AbelPoly (by linarith only [hb])
            (sub_le_self _ (by norm_num only)) (show (0 : ℝ) < 50 by norm_num only) hm).trans
        ?_
    linarith only [he]
  have h :=
    k186_abel_split_profile hRH h5 hT ha (hf (by norm_num only) h5)
      (hf le_rfl (by norm_num only : (0 : ℝ) ≤ 5))
  linarith only [h]

/-- Three fixed profile-coordinate caps give the far Abel residual.
The endpoint and the part beyond 65 are supplied by previously checked bounds. -/
theorem k186_abel_residual_of_profile (hRH : RiemannHypothesis) {x : ℝ} (hx : 60 ≤ x)
    (h :
      let B := HighGaussianKernel.k186.realProfile
      let Q := Polynomial.C (9 / 4 : ℝ) * B - B.derivative
      let D := Polynomial.C (9 / 4 : ℝ) * Q - Q.derivative
      let f := fun v ↦ Real.exp (-(11 / 4 : ℝ) * v) * |D.eval v|
      (∫ v in (35 : ℝ)..65, f v) ≤ 2299 ∧
        (∫ v in (5 : ℝ)..35, f v) ≤ 59000 ∧ (∫ v in (0 : ℝ)..5, f v) ≤ 67000) :
    -19798 ≤ k186AbelResidual x := by
  apply k186_abel_residual_of_integrals hRH hx
  obtain ⟨hhead, h₁, h₂⟩ := h
  have hz : 65 ≤ x + 5 := by linarith only [hx]
  let B := HighGaussianKernel.k186.realProfile
  let Q := Polynomial.C (9 / 4 : ℝ) * B - B.derivative
  let D := Polynomial.C (9 / 4 : ℝ) * Q - Q.derivative
  let f := fun v : ℝ ↦ Real.exp (-(11 / 4 : ℝ) * v) * |D.eval v|
  have hcont : Continuous f :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul D.continuous.abs
  have htail : (∫ v in (65 : ℝ)..x + 5, f v) ≤ 1 := k186_abel_tail_le_one hz
  have h₀ : (∫ v in (35 : ℝ)..x + 5, f v) ≤ 2300 := by
    rw [←
      intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable 35 65)
        (hcont.intervalIntegrable 65 (x + 5))]
    change (∫ v in (35 : ℝ)..65, f v) ≤ 2299 at hhead
    linarith only [hhead, htail]
  have e₀ := k186_abel_integral_log (x + 5) 35 (x + 5)
  have e₁ := k186_abel_integral_log (x + 5) 5 35
  have e₂ := k186_abel_integral_log (x + 5) 0 5
  have eT : x + 5 - 35 = x - 30 := by ring
  simp only [sub_self, Real.exp_zero, eT] at e₀
  simp only [eT, add_sub_cancel_right] at e₁
  simp only [sub_zero, add_sub_cancel_right] at e₂
  refine ⟨e₀.trans_le h₀, e₁.trans_le h₁, e₂.trans_le h₂, ?_⟩
  exact k186_abel_endpoint_abs_le x

/-- The checked finite integrals give the required Abel residual on the
entire far ray. -/
theorem k186_abel_residual_le (hRH : RiemannHypothesis) {x : ℝ} (hx : 60 ≤ x) :
    -19798 ≤ k186AbelResidual x := by
  exact k186_abel_residual_of_profile hRH hx k186_abel_finite_caps

/-- In the K186 far range, the only remaining numerical hypotheses are
the caps on the main and variation charges of the compensation. -/
theorem uniform_k186_far_of_comp_caps {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 30000000000000 ≤ Real.log n)
    (hI : Real.exp (5 / 2) * highCompensationMain .k186 ≤ 13765063832627 / 500000000000000000)
    (hV : highCompensationVariation .k186 ≤ 1 / 4) :
    HasRejectingPrime n (gaussianWitnessCutoff (Real.log n)) := by
  apply uniform_k186_far_of_abel hn ho hu hGRH hL hI hV
  apply k186_abel_residual_le hGRH.riemann
  have hz := k186_gamma_far_domain hL
  linarith only [hz]

/-- The far proof can consume integer caps on the two compensation charges.
Their common scale is the scale of the existing compensation ticks. -/
theorem uniform_k186_far_of_comp_ticks {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 30000000000000 ≤ Real.log n)
    (hI : (highCompensationChargeTicks .k186).1 ≤ 225981049151000)
    (hV : (highCompensationChargeTicks .k186).2 ≤ 25000000000000000000) :
    HasRejectingPrime n (gaussianWitnessCutoff (Real.log n)) := by
  have hI' := (Int.cast_le (R := ℝ)).mpr hI
  have hV' := (Int.cast_le (R := ℝ)).mpr hV
  simp only [Int.cast_ofNat] at hI' hV'
  refine
    uniform_k186_far_of_comp_caps hn ho hu hGRH hL
      (k186_scaled_comp_of_cap
        ((high_comp_main_le_ticks .k186).trans (div_le_div_of_nonneg_right hI' (by norm_num only))))
      ?_
  exact
    (high_compensation_variation_sum_le .k186).trans
      ((div_le_div_of_nonneg_right hV' (by norm_num only : (0 : ℝ) ≤ 10 ^ 20)).trans_eq
        (by norm_num only))

end PseudoPrime.PrimeTestBounds.MillerRabin
