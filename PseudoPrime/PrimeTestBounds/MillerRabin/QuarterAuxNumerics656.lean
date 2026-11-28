/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAuxEuler656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAuxEuler656
import PseudoPrime.Analysis.LogTaylorBounds
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.EulerDerivatives

/-! # Rational exponential bounds for the section 132 auxiliary polynomial -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational Taylor polynomial is shared by positive and negative
exponential arguments in the auxiliary profile. -/
private def auxExpTaylor656 (x : ℚ) : ℚ :=
  ∑ j ∈ Finset.range 54, x ^ j / (j.factorial : ℚ)

/-- A uniform remainder of at most 10⁻¹⁶ encloses the signed exponential
arguments in the seven-frequency polynomial. -/
private theorem aux_exp_error_656 (x : ℚ) (hx : |(x : ℝ)| ≤ 10) :
    |Real.exp (x : ℝ) - (auxExpTaylor656 x : ℝ)| ≤ 1 / 10 ^ 16 := by
  have h :=
    Complex.exp_bound' (n := 54) (x := ((x : ℝ) : ℂ))
      (by
        rw [Complex.norm_real, Real.norm_eq_abs]; norm_num only; linarith only [hx])
  rw [Complex.norm_real, Real.norm_eq_abs] at h
  have hc :
    ((auxExpTaylor656 x : ℚ) : ℂ) =
      ∑ j ∈ Finset.range 54, ((x : ℝ) : ℂ) ^ j / (j.factorial : ℂ) := by
    simp only [auxExpTaylor656, Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast,
      Complex.ofReal_ratCast]
  rw [← hc, ← Complex.ofReal_ratCast, ← Complex.ofReal_exp, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs] at h
  exact
    h.trans
      ((mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hx 54) (by norm_num only))
            (by norm_num only)).trans
        (by norm_num only [Nat.factorial]))

/-- All arguments of the exponentials in equation (132.7) have magnitude
at most ten, including those formed from differences of frequencies. -/
private theorem aux_exp_arguments_656 :
    (∀ i : Fin 7, |((11 / 10 : ℚ) * |21 / 8 + quarterAuxShift656 i|)| ≤ 10) ∧
      (∀ i j : Fin 7, |((11 / 10 : ℚ) * |quarterAuxShift656 i - quarterAuxShift656 j|)| ≤ 10) := by
  decide +kernel

private def auxFrequency (i : Fin 7) : ℚ :=
  21 / 8 + quarterAuxShift656 i

private theorem aux_frequency_cast (i : Fin 7) :
    (auxFrequency i : ℝ) = quarterAuxFrequency656 i := by
  simp only [auxFrequency, quarterAuxFrequency656, Rat.cast_add, Rat.cast_div, Rat.cast_ofNat]

private theorem aux_coeff_cast (i : Fin 7) :
    (quarterAuxCoeffRat656 i : ℝ) = quarterAuxCoeff656 i := by
  unfold quarterAuxCoeff656
  rfl

private def auxPairApprox (f : ℚ → ℚ) (s : ℚ) : ℚ :=
  (auxExpTaylor656 (-(11 / 10) * |s|) * f |s| + auxExpTaylor656 ((11 / 10) * |s|) * f (-|s|)) / 2

private noncomputable def auxPairExact (f : ℚ → ℚ) (s : ℚ) : ℝ :=
  (Real.exp ((-(11 / 10) * |s| : ℚ) : ℝ) * (f |s| : ℝ) +
      Real.exp (((11 / 10) * |s| : ℚ) : ℝ) * (f (-|s|) : ℝ)) /
    2

/-- Each pair of exponential terms can use the same signed Taylor remainder.
The error scales by the sum of the absolute polynomial multipliers. -/
private theorem aux_pair_error (f : ℚ → ℚ) (s : ℚ) (hs : |((11 / 10 : ℚ) * |s|)| ≤ 10) :
    |auxPairExact f s - (auxPairApprox f s : ℝ)| ≤
      (|((f |s| : ℚ) : ℝ)| + |((f (-|s|) : ℚ) : ℝ)|) / (2 * 10 ^ 16) := by
  have hpos : |((((11 / 10 : ℚ) * |s|) : ℚ) : ℝ)| ≤ 10 := by exact_mod_cast hs
  have hneg : |((((-(11 / 10 : ℚ)) * |s|) : ℚ) : ℝ)| ≤ 10 := by
    simpa only [neg_mul, Rat.cast_neg, abs_neg] using hpos
  have h₁ := aux_exp_error_656 (-(11 / 10) * |s|) hneg
  have h₂ := aux_exp_error_656 ((11 / 10) * |s|) hpos
  simp only [auxPairExact, auxPairApprox, Rat.cast_div, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat,
    Rat.cast_neg]
  simp only [Rat.cast_mul, Rat.cast_neg, Rat.cast_div, Rat.cast_ofNat] at h₁ h₂
  rw [← sub_div, add_sub_add_comm, ← sub_mul, ← sub_mul, abs_div,
    abs_of_pos (by norm_num only : (0 : ℝ) < 2)]
  apply (div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num only : (0 : ℝ) ≤ 2)).trans
  rw [abs_mul, abs_mul]
  linarith only [mul_le_mul_of_nonneg_right h₁ (abs_nonneg (f |s| : ℝ)),
    mul_le_mul_of_nonneg_right h₂ (abs_nonneg (f (-|s|) : ℝ))]

private def auxMixApprox (f : ℚ → ℚ) : ℚ :=
  (∑ i,
        ∑ j,
          quarterAuxCoeffRat656 i * quarterAuxCoeffRat656 j *
            auxPairApprox f (auxFrequency i - auxFrequency j)) /
      2 -
    ∑ i, quarterAuxCoeffRat656 i * auxPairApprox f (auxFrequency i)

private noncomputable def auxMixExact (f : ℚ → ℚ) : ℝ :=
  (∑ i,
        ∑ j,
          quarterAuxCoeff656 i * quarterAuxCoeff656 j *
            auxPairExact f (auxFrequency i - auxFrequency j)) /
      2 -
    ∑ i, quarterAuxCoeff656 i * auxPairExact f (auxFrequency i)

/-- The absolute error in a mixed coefficient uses the sum of the errors of
the 49 pair terms and the seven single terms. -/
private theorem aux_mix_error (f : ℚ → ℚ)
    (hf₁ : ∀ i, |f (|auxFrequency i|)| + |f (-|auxFrequency i|)| ≤ 100)
    (hf₂ :
      ∀ i j,
        |f (|auxFrequency i - auxFrequency j|)| + |f (-|auxFrequency i - auxFrequency j|)| ≤ 100) :
    |auxMixExact f - (auxMixApprox f : ℝ)| ≤ 1 / 10 ^ 12 := by
  have hs (i : Fin 7) : |quarterAuxCoeff656 i| ≤ 1 := by
    have h : ∀ j, |quarterAuxCoeffRat656 j| ≤ 1 := by decide +kernel
    rw [← aux_coeff_cast]
    exact_mod_cast h i
  have hrow (s : ℚ) (h₁ : |((11 / 10 : ℚ) * |s|)| ≤ 10) (h₂ : |f (|s|)| + |f (-|s|)| ≤ 100) :
    |auxPairExact f s - (auxPairApprox f s : ℝ)| ≤ 1 / (2 * 10 ^ 14) := by
    have hc : |(f |s| : ℝ)| + |(f (-|s|) : ℝ)| ≤ 100 := by exact_mod_cast h₂
    exact (aux_pair_error f s h₁).trans (by linarith only [hc])
  have hsingle (i : Fin 7) :
    |quarterAuxCoeff656 i *
          (auxPairExact f (auxFrequency i) - (auxPairApprox f (auxFrequency i) : ℝ))| ≤
      1 / (2 * 10 ^ 14) := by
    rw [abs_mul]
    exact
      (mul_le_of_le_one_left (abs_nonneg _) (hs i)).trans
        (hrow _ (aux_exp_arguments_656.1 i) (hf₁ i))
  have hpair (i j : Fin 7) :
    |quarterAuxCoeff656 i * quarterAuxCoeff656 j *
          (auxPairExact f (auxFrequency i - auxFrequency j) -
            (auxPairApprox f (auxFrequency i - auxFrequency j) : ℝ))| ≤
      1 / (2 * 10 ^ 14) := by
    rw [abs_mul, abs_mul]
    have hc : |quarterAuxCoeff656 i| * |quarterAuxCoeff656 j| ≤ 1 :=
      (mul_le_of_le_one_left (abs_nonneg _) (hs i)).trans (hs j)
    apply (mul_le_of_le_one_left (abs_nonneg _) hc).trans
    apply hrow _ _ (hf₂ i j)
    simpa only [auxFrequency, add_sub_add_left_eq_sub] using aux_exp_arguments_656.2 i j
  unfold auxMixExact auxMixApprox
  simp only [Rat.cast_sub, Rat.cast_div, Rat.cast_sum, Rat.cast_mul, Rat.cast_ofNat, aux_coeff_cast]
  rw [sub_sub_sub_comm, ← sub_div]
  simp only [← Finset.sum_sub_distrib, ← mul_sub]
  apply (abs_sub _ _).trans
  rw [abs_div, abs_of_pos (by norm_num only : (0 : ℝ) < 2)]
  have hS :=
    (Finset.abs_sum_le_sum_abs (s := Finset.univ) _).trans (Finset.sum_le_sum (fun i _ ↦ hsingle i))
  have hP :=
    (Finset.abs_sum_le_sum_abs (s := Finset.univ) _).trans
      (Finset.sum_le_sum
        (fun i _ ↦
          (Finset.abs_sum_le_sum_abs (s := Finset.univ) _).trans
            (Finset.sum_le_sum (fun j _ ↦ hpair i j))))
  norm_num only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_ofNat] at hS hP
  linarith only [hS, hP]

private def profileConstant (s : ℚ) : ℚ :=
  3 / 8 + 33 / 80 * s + (11 / 10) ^ 2 / 8 * s ^ 2

private def profileLinear (s : ℚ) : ℚ :=
  33 / 80 + (11 / 10) ^ 2 / 4 * s

private def profileQuadratic (_ : ℚ) : ℚ :=
  (11 / 10) ^ 2 / 8

private theorem aux_mix_eq (f : ℚ → ℚ) (F : ℝ → ℝ) (h : ∀ s : ℚ, auxPairExact f s = F s) :
    auxMixExact f = quarterAuxMix656 F := by
  simp only [auxMixExact, quarterAuxMix656, ← aux_frequency_cast, ← Rat.cast_sub, h]

private theorem aux_constant_eq : auxMixExact profileConstant = quarterAuxConstant656 := by
  unfold quarterAuxConstant656
  apply aux_mix_eq
  intro s
  simp only [auxPairExact, quarterAuxPair656, quarterAuxProfile656, profileConstant, Rat.cast_abs,
    Rat.cast_neg, Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, zero_add,
    zero_sub]
  ring

private theorem aux_linear_eq : auxMixExact profileLinear = quarterAuxLinear656 := by
  unfold quarterAuxLinear656
  apply aux_mix_eq
  intro s
  simp only [auxPairExact, profileLinear, Rat.cast_abs, Rat.cast_neg, Rat.cast_add, Rat.cast_mul,
    Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat]
  ring

private theorem aux_quadratic_eq : auxMixExact profileQuadratic = quarterAuxQuadratic656 := by
  unfold quarterAuxQuadratic656
  apply aux_mix_eq
  intro s
  simp only [auxPairExact, profileQuadratic, Rat.cast_abs, Rat.cast_neg, Rat.cast_mul, Rat.cast_div,
    Rat.cast_pow, Rat.cast_ofNat]
  ring

private theorem aux_coefficient_box (f : ℚ → ℚ) {l u : ℚ}
    (hf₁ : ∀ i, |f (|auxFrequency i|)| + |f (-|auxFrequency i|)| ≤ 100)
    (hf₂ :
      ∀ i j,
        |f (|auxFrequency i - auxFrequency j|)| + |f (-|auxFrequency i - auxFrequency j|)| ≤ 100)
    (hl : l + 1 / 10 ^ 12 ≤ auxMixApprox f) (hu : auxMixApprox f ≤ u - 1 / 10 ^ 12) :
    auxMixExact f ∈ Set.Icc (l : ℝ) (u : ℝ) := by
  have he := abs_le.mp (aux_mix_error f hf₁ hf₂)
  have hl' := (Rat.cast_le (K := ℝ)).mpr hl
  have hu' := (Rat.cast_le (K := ℝ)).mpr hu
  simp only [Rat.cast_add, Rat.cast_sub, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat,
    Rat.cast_one] at hl' hu'
  exact ⟨by linarith only [he.1, hl'], by linarith only [he.2, hu']⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
-- Kernel evaluation checks the rational Taylor sums at the finite list of frequencies.
/-- Outward rational boxes for all three coefficients of the polynomial
in equation (132.7), computed from the shared signed Taylor sums. -/
theorem quarter_aux_coeff_boxes_656 :
    quarterAuxConstant656 ∈ Set.Icc 394.266144947 394.266144949 ∧
      quarterAuxLinear656 ∈ Set.Icc (-72.480277077) (-72.480277075) ∧
      quarterAuxQuadratic656 ∈ Set.Icc 3.305751634 3.305751637 := by
  have h₀ :=
    aux_coefficient_box profileConstant (l := 394266144947 / 1000000000) (u :=
      394266144949 / 1000000000) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  have h₁ :=
    aux_coefficient_box profileLinear (l := -72480277077 / 1000000000) (u :=
      -72480277075 / 1000000000) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  have h₂ :=
    aux_coefficient_box profileQuadratic (l := 3305751634 / 1000000000) (u :=
      3305751637 / 1000000000) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  norm_num only [aux_constant_eq, aux_linear_eq, aux_quadratic_eq, Rat.cast_div, Rat.cast_neg,
    Rat.cast_ofNat] at h₀ h₁ h₂ ⊢
  exact ⟨h₀, h₁, h₂⟩

/-- For logarithmic arguments at or above the cutoff of radius 322, the
section 132 trace cost is bounded by the shifted positive polynomial.
The same bound applies to both intervals ending at logarithm 656. -/
theorem quarter_aux_euler_tail_point_656 {α w v : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 4) (hw : 0 ≤ w)
    (hv : 2 * Real.log 322 ≤ v) :
    α * w * quarterAuxPoly656 v ≤
      4 * w *
        (if (119 / 10 : ℝ) ≤ v then 6.19661190 * (v - 119 / 10) + 3.305751637 * (v - 119 / 10) ^ 2
        else 0) := by
  obtain ⟨hc, hb, ha⟩ := quarter_aux_coeff_boxes_656
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound (N := 322) (j := 9) (n := 27) (lo := 57745 / 10000)
        (hi := 6) (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  apply quarter_aux_euler_cut_656 hα hα' hw (l := 11.549) (by linarith only [hv, hlog])
  · exact (by norm_num only : (0 : ℝ) ≤ 3.305751634).trans ha.1
  · rw [quarter_aux_poly_eq_656]
    linarith only [hc.2, hb.2, ha.2]
  · rw [quarter_aux_poly_eq_656]
    linarith only [hc.2, hb.2, ha.2]
  · norm_num only
  · exact ha.2
  · linarith only [ha.2, hb.2]

/-- At exponent 8/5 the three logarithmic moments make every quadratic
Euler weight absolutely summable. -/
private theorem aux_quad_summable (a b c : ℝ) :
    Summable
      (fun n : ℕ ↦
        ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (8 / 5 : ℝ) *
          (a * Real.log n ^ 2 + b * Real.log n + c)) := by
  have hm :=
    AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.summable_mangoldt_log (σ := 8 / 5)
      (by norm_num only)
  apply (((hm 2).mul_left a).add ((hm 1).mul_left b)).add ((hm 0).mul_left c) |>.congr
  intro n
  ring

/-- Starting at radius 322, the trace correction to the combined auxiliary
Euler series is bounded by a single positive tail with logarithmic split 119/10.
This inequality is the arithmetic-series input to the centered Abel estimate. -/
theorem quarter_aux_euler_tail_656 {X : ℝ} (hX : (322 : ℝ) ^ 2 ≤ X) (α : ℕ → ℝ)
    (hα : ∀ n, 0 ≤ α n ∧ α n ≤ 4) :
    (∑' n : ℕ,
        if X < (n : ℝ) then
          α n * (ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (8 / 5 : ℝ)) *
            quarterAuxPoly656 (Real.log n)
        else 0) ≤
      4 *
        ∑' n : ℕ,
          if (119 / 10 : ℝ) ≤ Real.log n then
            (ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (8 / 5 : ℝ)) *
              (6.19661190 * (Real.log n - 119 / 10) + 3.305751637 * (Real.log n - 119 / 10) ^ 2)
          else 0 := by
  let W := fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (8 / 5 : ℝ)
  let P := fun n : ℕ ↦ W n * quarterAuxPoly656 (Real.log n)
  let Q := fun n : ℕ ↦
    W n * (6.19661190 * (Real.log n - 119 / 10) + 3.305751637 * (Real.log n - 119 / 10) ^ 2)
  let R := fun n : ℕ ↦ if (119 / 10 : ℝ) ≤ Real.log n then Q n else 0
  have hP : Summable P := by
    simpa only [P, W, quarter_aux_poly_eq_656] using
      aux_quad_summable quarterAuxQuadratic656 quarterAuxLinear656 quarterAuxConstant656
  have hQ : Summable Q := by
    apply
      (aux_quad_summable 3.305751637 (6.19661190 - 2 * 3.305751637 * (119 / 10))
          (3.305751637 * (119 / 10) ^ 2 - 6.19661190 * (119 / 10))).congr
    intro n
    dsimp only [Q, W]
    ring
  have hR : Summable R :=
    hQ.norm.of_norm_bounded
      (fun n ↦ by
        dsimp only [R]
        split
        · exact le_rfl
        · rw [norm_zero]; exact norm_nonneg _)
  have hL : Summable (fun n : ℕ ↦ if X < (n : ℝ) then α n * P n else 0) :=
    (hP.norm.mul_left 4).of_norm_bounded
      (fun n ↦ by
        split
        · rw [norm_mul, Real.norm_eq_abs (α n), abs_of_nonneg (hα n).1]
          exact mul_le_mul_of_nonneg_right (hα n).2 (norm_nonneg _)
        · rw [norm_zero]; exact mul_nonneg (by norm_num only) (norm_nonneg _))
  rw [← tsum_mul_left]
  change
    (∑' n : ℕ, if X < (n : ℝ) then α n * W n * quarterAuxPoly656 (Real.log n) else 0) ≤
      ∑' n, 4 * R n
  have h' :=
    hL.tsum_le_tsum (g := fun n ↦ 4 * R n)
      (fun n ↦ by
        have hw : 0 ≤ W n :=
          div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
        by_cases hn : X < (n : ℝ)
        · rw [ite_eq_left hn]
          have hlog := Real.log_le_log (by norm_num only : (0 : ℝ) < 322 ^ 2) (hX.trans hn.le)
          rw [Real.log_pow, Nat.cast_ofNat] at hlog
          have hp := quarter_aux_euler_tail_point_656 (hα n).1 (hα n).2 hw hlog
          simpa only [P, R, Q, mul_ite, mul_zero, mul_assoc] using hp
        · rw [ite_eq_right hn]
          apply mul_nonneg (by norm_num only)
          dsimp only [R, Q]
          split
          · exact
              mul_nonneg hw
                (add_nonneg (mul_nonneg (by norm_num only) (sub_nonneg.mpr ‹_›))
                  (mul_nonneg (by norm_num only) (sq_nonneg _)))
          · exact le_rfl)
      (hR.mul_left 4)
  simpa only [P, mul_assoc] using h'

end PseudoPrime.PrimeTestBounds.MillerRabin
