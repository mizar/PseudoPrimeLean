/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Reflection
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterProfile663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterThetaPoly663
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.EulerDerivatives

/-! # Rational interval bounds for the combined K197 reflection -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational multipliers for the coefficient of degree j after shifting
the logarithmic variable by 23/2. -/
private def jointWeight197 (j : ℕ) (i : Fin 6) : ℚ :=
  -(gaussianCoeff197 i) * (Nat.choose 5 j) * (23 / 2 - quarterShift663 i) ^ (5 - j)

/-- The six real coefficients obtained by binomial expansion. -/
noncomputable def jointCoeff197 (j : ℕ) : ℝ :=
  ∑ i, (jointWeight197 j i : ℝ) * Real.exp ((11 / 10 : ℚ) * quarterShift663 i : ℚ)

/-- The exact rational approximation uses the existing exponential certificate. -/
private def jointApprox197 (j : ℕ) : ℚ :=
  ∑ i, jointWeight197 j i * profileExpTaylor ((11 / 10) * quarterShift663 i)

/-- Outward upper endpoints for the six centered coefficients. -/
@[expose]
def jointCoeffUpper197 (j : Fin 6) : ℚ :=
  ![56278.978230, 19053.251906, 869.480956, -243.513257, -11.241269, 1.409153] j

/-- The total rounding error is at most six times the bound for one
weighted exponential. -/
private theorem joint_error_197 (j : Fin 6) :
    |jointCoeff197 j - (jointApprox197 j : ℝ)| ≤ 6 / 10 ^ 10 := by
  have hw : ∀ k : Fin 6, ∀ i : Fin 6, |jointWeight197 k i| ≤ 1000000 := by decide +kernel
  have hx : ∀ i : Fin 6, |(11 / 10 : ℚ) * quarterShift663 i| ≤ 11 := by decide +kernel
  unfold jointCoeff197 jointApprox197
  rw [Rat.cast_sum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h (i : Fin 6) :
    |(jointWeight197 j i : ℝ) * Real.exp ((11 / 10 : ℚ) * quarterShift663 i : ℚ) -
          ((jointWeight197 j i * profileExpTaylor ((11 / 10) * quarterShift663 i) : ℚ) : ℝ)| ≤
      1 / 10 ^ 10 := by
    simp only [Rat.cast_mul, ← mul_sub, abs_mul]
    have hw' : |(jointWeight197 j i : ℝ)| ≤ 1000000 := by exact_mod_cast hw j i
    have he := profile_exp_error ((11 / 10) * quarterShift663 i) (by exact_mod_cast hx i)
    rw [Rat.cast_mul] at he
    exact (mul_le_mul hw' he (abs_nonneg _) (by norm_num only)).trans (by norm_num only)
  calc
    _ ≤ ∑ _ : Fin 6, (1 / 10 ^ 10 : ℝ) := Finset.sum_le_sum fun i _ ↦ h i
    _ = _ := by
      norm_num only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_ofNat]

/-- The rational upper endpoints bound all six real coefficients. -/
theorem joint_coeff_upper_197 (j : Fin 6) : jointCoeff197 j ≤ jointCoeffUpper197 j := by
  have h : ∀ k : Fin 6, jointApprox197 k + 6 / 10 ^ 10 ≤ jointCoeffUpper197 k := by decide +kernel
  have hc : (jointApprox197 j : ℝ) + 6 / 10 ^ 10 ≤ (jointCoeffUpper197 j : ℝ) := by
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr (h j)
  linarith only [(abs_le.mp (joint_error_197 j)).2, hc]

/-- Centering at 23/2 leaves a degree-five polynomial in the displacement. -/
theorem joint_poly_expand_197 (v : ℝ) :
    gaussianJoint197 v = ∑ j : Fin 6, jointCoeff197 j * (v - 23 / 2) ^ (j : ℕ) := by
  unfold gaussianJoint197 jointCoeff197
  rw [← Finset.sum_neg_distrib]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [jointWeight197, Rat.cast_neg, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_sub,
    Rat.cast_pow, Rat.cast_natCast]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ, Nat.reduceAdd,
    Nat.reduceSub, Nat.choose, Nat.cast_ofNat, Nat.cast_one, add_zero]
  ring

/-- For a nonnegative displacement from 23/2, the powers preserve each
coefficient inequality, including the negative coefficients. -/
theorem joint_poly_upper_197 {v : ℝ} (hv : 23 / 2 ≤ v) :
    gaussianJoint197 v ≤ ∑ j : Fin 6, (jointCoeffUpper197 j : ℝ) * (v - 23 / 2) ^ (j : ℕ) := by
  rw [joint_poly_expand_197]
  exact
    Finset.sum_le_sum fun j _ ↦
      mul_le_mul_of_nonneg_right (joint_coeff_upper_197 j) (pow_nonneg (sub_nonneg.mpr hv) _)

/-- Enclose the coefficient of degree `j` after translation by a displacement
in `[l,u]`, choosing the endpoint according to the sign of each term. -/
@[expose]
def jointShiftUpper197 (l u : ℚ) (j : Fin 6) : ℚ :=
  ∑ k : Fin 6,
    jointCoeffUpper197 k * (Nat.choose k.val j.val) *
      (if jointCoeffUpper197 k < 0 then l else u) ^ (k.val - j.val)

/-- The nonnegative part of each translated coefficient bounds the joint
reflection profile above the cutoff. -/
noncomputable def jointMajor197 (l u : ℚ) (t : ℝ) : ℝ :=
  ∑ j : Fin 6, (max 0 (jointShiftUpper197 l u j) : ℚ) * t ^ (j : ℕ)

private theorem joint_translate (z t : ℝ) :
    (∑ k : Fin 6, (jointCoeffUpper197 k : ℝ) * (z + t) ^ (k : ℕ)) =
      ∑ j : Fin 6,
        (∑ k : Fin 6,
            (jointCoeffUpper197 k : ℝ) * (Nat.choose k.val j.val : ℝ) * z ^ (k.val - j.val)) *
          t ^ (j : ℕ) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ, Nat.reduceAdd,
    Nat.reduceSub, Nat.choose, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, add_zero, zero_mul,
    mul_zero]
  ring

private theorem joint_shift_coeff_le {l u : ℚ} {z : ℝ} (hl : 0 ≤ l)
    (hz : z ∈ Set.Icc (l : ℝ) (u : ℝ)) (j : Fin 6) :
    (∑ k : Fin 6, (jointCoeffUpper197 k : ℝ) * (Nat.choose k.val j.val : ℝ) * z ^ (k.val - j.val)) ≤
      (jointShiftUpper197 l u j : ℝ) := by
  have hl' : 0 ≤ (l : ℝ) := by exact_mod_cast hl
  simp only [jointShiftUpper197, Rat.cast_sum, Rat.cast_mul, Rat.cast_natCast, Rat.cast_pow]
  apply Finset.sum_le_sum
  intro k _
  by_cases hk : jointCoeffUpper197 k < 0
  · rw [ite_eq_left hk]
    have hc : (jointCoeffUpper197 k : ℝ) ≤ 0 := by exact_mod_cast hk.le
    exact
      mul_le_mul_of_nonpos_left (pow_le_pow_left₀ hl' hz.1 _)
        (mul_nonpos_of_nonpos_of_nonneg hc (Nat.cast_nonneg _))
  · rw [ite_eq_right hk]
    have hc : 0 ≤ (jointCoeffUpper197 k : ℝ) := by exact_mod_cast le_of_not_gt hk
    exact
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hl'.trans hz.1) hz.2 _)
        (mul_nonneg hc (Nat.cast_nonneg _))

/-- A rational interval for the centered base yields a nonnegative
majorant for every nonnegative displacement past it. -/
theorem joint_majorizes_197 {l u : ℚ} {v t : ℝ} (hl : 0 ≤ l)
    (hv : v - 23 / 2 ∈ Set.Icc (l : ℝ) (u : ℝ)) (ht : 0 ≤ t) :
    0 ≤ jointMajor197 l u t ∧ gaussianJoint197 (v + t) ≤ jointMajor197 l u t := by
  have hl' : 0 ≤ (l : ℝ) := by exact_mod_cast hl
  have hbase := hl'.trans hv.1
  have hpos (j : Fin 6) : 0 ≤ (↑(max 0 (jointShiftUpper197 l u j)) : ℝ) := by
    exact_mod_cast (le_max_left 0 (jointShiftUpper197 l u j))
  refine ⟨Finset.sum_nonneg (fun j _ ↦ mul_nonneg (hpos j) (pow_nonneg ht _)), ?_⟩
  refine (joint_poly_upper_197 (by linarith only [hbase, ht] : 23 / 2 ≤ v + t)).trans ?_
  rw [show v + t - 23 / 2 = v - 23 / 2 + t by ring, joint_translate]
  apply Finset.sum_le_sum
  intro j _
  have h := joint_shift_coeff_le hl hv j
  have hm : (jointShiftUpper197 l u j : ℝ) ≤ (↑(max 0 (jointShiftUpper197 l u j)) : ℝ) := by
    exact_mod_cast (le_max_right 0 (jointShiftUpper197 l u j))
  exact mul_le_mul_of_nonneg_right (h.trans hm) (pow_nonneg ht _)

/-- The Mangoldt moment of the relative logarithm on the unknown support. -/
@[expose]
noncomputable def gaussianMoment197 (r : ℝ) (j : Fin 6) : ℝ :=
  ∑' n : ℕ,
    if r ^ 2 < (n : ℝ) then
      ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (8 / 5 : ℝ) *
        (Real.log n - 2 * Real.log r) ^ (j : ℕ)
    else 0

private theorem joint_moment_summable {r : ℝ} (hr : 1 ≤ r) (j : Fin 6) :
    Summable
      (fun n : ℕ ↦
        if r ^ 2 < (n : ℝ) then
          ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (8 / 5 : ℝ) *
            (Real.log n - 2 * Real.log r) ^ (j : ℕ)
        else 0) := by
  let A := fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (8 / 5 : ℝ)
  have hA (n : ℕ) : 0 ≤ A n :=
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hs : Summable (fun n : ℕ ↦ A n * Real.log n ^ (j : ℕ)) := by
    apply
      (AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.summable_mangoldt_log (σ := 8 / 5)
          (by norm_num only) (j : ℕ)).congr
    intro n
    simp only [A, div_mul_eq_mul_div]
  have hlog (n : ℕ) (hn : r ^ 2 < (n : ℝ)) : 0 ≤ Real.log n - 2 * Real.log r := by
    have h := Real.log_le_log (sq_pos_of_pos (zero_lt_one.trans_le hr)) hn.le
    rw [Real.log_pow, Nat.cast_ofNat] at h
    exact sub_nonneg.mpr h
  apply Summable.of_nonneg_of_le _ _ hs
  · intro n
    by_cases hn : r ^ 2 < (n : ℝ)
    · rw [ite_eq_left hn]
      exact mul_nonneg (hA n) (pow_nonneg (hlog n hn) _)
    · rw [ite_eq_right hn]
  · intro n
    by_cases hn : r ^ 2 < (n : ℝ)
    · rw [ite_eq_left hn]
      have hv : Real.log n - 2 * Real.log r ≤ Real.log n := by linarith only [Real.log_nonneg hr]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hlog n hn) hv _) (hA n)
    · rw [ite_eq_right hn]
      exact mul_nonneg (hA n) (pow_nonneg (Real.log_natCast_nonneg n) _)

private theorem joint_major_term (l u : ℚ) (r : ℝ) (n : ℕ) :
    (if r ^ 2 < (n : ℝ) then
        ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (8 / 5 : ℝ) *
          jointMajor197 l u (Real.log n - 2 * Real.log r)
      else 0) =
      ∑ j : Fin 6,
        (↑(max 0 (jointShiftUpper197 l u j)) : ℝ) *
          if r ^ 2 < (n : ℝ) then
            ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (8 / 5 : ℝ) *
              (Real.log n - 2 * Real.log r) ^ (j : ℕ)
          else 0 := by
  by_cases hn : r ^ 2 < (n : ℝ)
  · simp only [ite_eq_left hn, jointMajor197, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ mul_left_comm _ _ _
  · simp only [ite_eq_right hn, mul_zero, Finset.sum_const_zero]

private theorem joint_major_tail_summable (l u : ℚ) {r : ℝ} (hr : 1 ≤ r) :
    Summable
      (fun n : ℕ ↦
        if r ^ 2 < (n : ℝ) then
          (ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (8 / 5 : ℝ)) *
            jointMajor197 l u (Real.log n - 2 * Real.log r)
        else 0) := by
  simp only [joint_major_term]
  exact summable_sum fun j _ ↦ (joint_moment_summable hr j).mul_left _

/-- The translated coefficient majorant bounds the signed reflection
on the entire unknown support, for a certified log-radius interval. -/
theorem gaussian_joint_box_lower_197 {l u : ℚ} {r : ℝ} (hr : 1 ≤ r) (hl : 0 ≤ l)
    (hlog : 4 * Real.log r - 23 / 2 ∈ Set.Icc (l : ℝ) (u : ℝ)) (α : ℕ → ℝ)
    (hα : ∀ n, 0 ≤ α n ∧ α n ≤ 4)
    (hprefix : ∀ n : ℕ, (n : ℝ) ≤ r ^ 2 → ArithmeticFunction.vonMangoldt n ≠ 0 → α n = 0) :
    -4 * ((11 / 10 : ℝ) ^ 5 / 120 * r ^ (-(11 / 5) : ℝ)) *
        (∑' n : ℕ,
          if r ^ 2 < (n : ℝ) then
            (ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (8 / 5 : ℝ)) *
              jointMajor197 l u (Real.log n - 2 * Real.log r)
          else 0) ≤
      ∑ i, (gaussianCoeff197 i : ℝ) * quarterAuxReflection656 α r (quarterShift663 i : ℝ) := by
  exact
    gaussian_joint_reflection_lower_197 (zero_lt_one.trans_le hr) α hα hprefix (jointMajor197 l u)
      (fun _ ht ↦ joint_majorizes_197 hl hlog ht) (joint_major_tail_summable l u hr)

/-- Upper bounds for the six shifted moments give a lower bound for the
combined reflection, using only the nonnegative translated coefficients. -/
theorem gaussian_joint_moment_lower_197 {l u : ℚ} {r : ℝ} (hr : 1 ≤ r) (hl : 0 ≤ l)
    (hlog : 4 * Real.log r - 23 / 2 ∈ Set.Icc (l : ℝ) (u : ℝ)) (α : ℕ → ℝ)
    (hα : ∀ n, 0 ≤ α n ∧ α n ≤ 4)
    (hprefix : ∀ n : ℕ, (n : ℝ) ≤ r ^ 2 → ArithmeticFunction.vonMangoldt n ≠ 0 → α n = 0)
    (M : Fin 6 → ℝ) (hM : ∀ j, gaussianMoment197 r j ≤ M j) :
    -4 * ((11 / 10 : ℝ) ^ 5 / 120 * r ^ (-(11 / 5) : ℝ)) *
        (∑ j : Fin 6, (↑(max 0 (jointShiftUpper197 l u j)) : ℝ) * M j) ≤
      ∑ i, (gaussianCoeff197 i : ℝ) * quarterAuxReflection656 α r (quarterShift663 i : ℝ) := by
  have hb := gaussian_joint_box_lower_197 hr hl hlog α hα hprefix
  simp only [joint_major_term,
    Summable.tsum_finsetSum (fun j _ ↦ (joint_moment_summable hr j).mul_left _),
    tsum_mul_left] at hb
  have h :=
    Finset.sum_le_sum (s := Finset.univ)
      (fun j _ ↦
        mul_le_mul_of_nonneg_left (hM j)
          (show 0 ≤ (↑(max 0 (jointShiftUpper197 l u j)) : ℝ) by
            exact_mod_cast (le_max_left 0 (jointShiftUpper197 l u j))))
  have hc : -4 * ((11 / 10 : ℝ) ^ 5 / 120 * r ^ (-(11 / 5) : ℝ)) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by norm_num only) (by positivity)
  exact (mul_le_mul_of_nonpos_left h hc).trans hb

/-- The constant coefficient of the translated box also bounds the
unshifted polynomial value used in the conductor contribution. -/
theorem gaussian_joint_base_upper_197 {l u : ℚ} {v : ℝ} (hl : 0 ≤ l)
    (hv : v - 23 / 2 ∈ Set.Icc (l : ℝ) (u : ℝ)) :
    gaussianJoint197 v ≤ (jointShiftUpper197 l u 0 : ℝ) := by
  have hl' : 0 ≤ (l : ℝ) := by exact_mod_cast hl
  have h := joint_shift_coeff_le hl hv (0 : Fin 6)
  simp only [Fin.val_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.sub_zero] at h
  exact (joint_poly_upper_197 (sub_nonneg.mp (hl'.trans hv.1))).trans h

end PseudoPrime.PrimeTestBounds.MillerRabin
