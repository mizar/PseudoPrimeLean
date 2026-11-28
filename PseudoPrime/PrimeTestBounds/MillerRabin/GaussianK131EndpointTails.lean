/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131EndpointBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131CoeffCheck
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131EndpointBounds
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131CoeffCheck
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Constants
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Polynomials
import Mathlib.Tactic
meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Log

/-! # Endpoint estimates for the two main K131 tail polynomials -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem left_endpoint_log :
    2 * Real.log (465644807 / 400000) ∈
      Set.Icc ((14119427717253463 / 1000000000000000 : ℚ) : ℝ)
        ((14119427717253464 / 1000000000000000 : ℚ) : ℝ) := by
  have hy : (465644807 / 400000 : ℝ) = ((465644807 / 400000 : ℚ) : ℝ) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
  rw [hy]
  constructor <;> dyadic_interval [prec := 100]

private theorem right_endpoint_log :
    2 * Real.log (1036273 / 250) ∈
      Set.Icc ((16659360525478489 / 1000000000000000 : ℚ) : ℝ)
        ((16659360525478490 / 1000000000000000 : ℚ) : ℝ) := by
  have hy : (1036273 / 250 : ℝ) = ((1036273 / 250 : ℚ) : ℝ) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
  rw [hy]
  constructor <;> dyadic_interval [prec := 100]

private def endpointVariationTerm (C : ℕ → ℚ) (a b : ℚ) (j : ℕ) : ℚ :=
  (if 0 ≤ C j then C j else 0) * (b ^ j - a ^ j)

private def endpointVariation (n : ℕ) (C : ℕ → ℚ) (a b : ℚ) : ℚ :=
  ∑ j ∈ Finset.range n, endpointVariationTerm C a b j

private def variationBlock (C : ℕ → ℚ) (a b : ℚ) (i : ℕ) : ℚ :=
  ∑ j ∈ Finset.range 5, endpointVariationTerm C a b (i + j)

private theorem variation_split (C : ℕ → ℚ) (a b : ℚ) :
    endpointVariation 20 C a b =
      variationBlock C a b 0 + variationBlock C a b 5 + variationBlock C a b 10 +
        variationBlock C a b 15 := by
  unfold endpointVariation variationBlock
  rw [show 20 = 15 + 5 by decide, Finset.sum_range_add, show 15 = 10 + 5 by decide,
    Finset.sum_range_add, show 10 = 5 + 5 by decide, Finset.sum_range_add]
  simp only [Nat.zero_add, Nat.reduceAdd]

private theorem pow_difference_le {a b c d : ℚ} (ha : 0 ≤ a) (hab : a ≤ b) (hac : a ≤ c)
    (hbd : b ≤ d) (hwidth : b - a = d - c) (j : ℕ) : b ^ j - a ^ j ≤ d ^ j - c ^ j := by
  induction j with
  | zero => simp only [pow_zero, sub_self, le_refl]
  | succ j
    ih =>
    rw [show b ^ (j + 1) - a ^ (j + 1) = (b ^ j - a ^ j) * b + a ^ j * (b - a) by ring,
      show d ^ (j + 1) - c ^ (j + 1) = (d ^ j - c ^ j) * d + c ^ j * (d - c) by ring]
    apply add_le_add
    · exact
        (mul_le_mul_of_nonneg_left hbd (sub_nonneg.mpr (pow_le_pow_left₀ ha hab j))).trans
          (mul_le_mul_of_nonneg_right ih (ha.trans (hab.trans hbd)))
    · rw [← hwidth]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha hac _) (sub_nonneg.mpr hab)

private theorem variation_le {C : ℕ → ℚ} {a b c d : ℚ} (ha : 0 ≤ a) (hab : a ≤ b) (hac : a ≤ c)
    (hbd : b ≤ d) (hwidth : b - a = d - c) :
    endpointVariation 20 C a b ≤ endpointVariation 20 C c d := by
  unfold endpointVariation
  apply Finset.sum_le_sum
  intro j _
  unfold endpointVariationTerm
  apply mul_le_mul_of_nonneg_left (pow_difference_le ha hab hac hbd hwidth j)
  by_cases h : 0 ≤ C j
  · rw [ite_eq_left h]
    exact h
  · rw [ite_eq_right h]

private def slopeTerm (C : ℕ → ℚ) (k : ℕ) : ℚ :=
  (if 0 ≤ C k then C k else 0) * ((k : ℚ) * 17 ^ (k - 1))

private def slopeBlock (C : ℕ → ℚ) (i : ℕ) : ℚ :=
  ∑ j ∈ Finset.range 5, slopeTerm C (i + j)

private theorem slope_term_le {C : ℕ → ℚ} {k : ℕ} {M : ℚ} (hk : 0 < k) (hM : 0 ≤ M)
    (h : C k ≤ M / ((k : ℚ) * 17 ^ (k - 1))) : slopeTerm C k ≤ M := by
  unfold slopeTerm
  split
  · exact (le_div_iff₀ (mul_pos (Nat.cast_pos.mpr hk) (pow_pos (by decide +kernel) _))).mp h
  · rw [zero_mul]
    exact hM

private theorem slope_block_le {C : ℕ → ℚ} {i : ℕ} {M : ℚ}
    (h : ∀ j : Fin 5, slopeTerm C (i + j.val) ≤ M) : slopeBlock C i ≤ 5 * M := by
  unfold slopeBlock
  calc
    _ ≤ ∑ _ ∈ Finset.range 5, M := Finset.sum_le_sum (fun j hj ↦ h ⟨j, Finset.mem_range.mp hj⟩)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_ofNat]

private theorem block_le_slope {C : ℕ → ℚ} {a b : ℚ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 17)
    (i : ℕ) : variationBlock C a b i ≤ (b - a) * slopeBlock C i := by
  simp only [variationBlock, slopeBlock, slopeTerm, Finset.mul_sum, endpointVariationTerm]
  apply Finset.sum_le_sum
  intro j _
  let k := i + j
  let w := if 0 ≤ C k then C k else 0
  have hw : 0 ≤ w := by
    unfold w
    split
    · assumption
    · exact le_rfl
  have h := abs_pow_sub_pow_le (a := b) (b := a) (n := k)
  rw [abs_of_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ ha hab k)),
    abs_of_nonneg (sub_nonneg.mpr hab), abs_of_nonneg (ha.trans hab), abs_of_nonneg ha,
    max_eq_left hab] at h
  have hp :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (ha.trans hab) hb (k - 1))
      (mul_nonneg (sub_nonneg.mpr hab) (Nat.cast_nonneg k))
  calc
    _ ≤ w * ((b - a) * k * 17 ^ (k - 1)) := mul_le_mul_of_nonneg_left (h.trans hp) hw
    _ = _ := by ring

private theorem endpoint_max_eq (c : ℚ) : (if 0 ≤ c then c else 0) = max 0 c := by
  by_cases hc : 0 ≤ c
  · rw [ite_eq_left hc, max_eq_right hc]
  · rw [ite_eq_right hc, max_eq_left (le_of_not_ge hc)]

private theorem eval_neg_upper {P : Polynomial ℝ} {n : ℕ} {a b M : ℚ} {x : ℝ} (hd : P.natDegree < n)
    (ha : 0 ≤ a) (hx : x ∈ Set.Icc (a : ℝ) (b : ℝ)) (C : ℕ → ℚ)
    (hC : ∀ j ∈ Finset.range n, -(P.coeff j) ≤ (C j : ℝ))
    (hM : (∑ j ∈ Finset.range n, -(P.coeff j) * (a : ℝ) ^ j) ≤ (M : ℝ)) :
    -P.eval x ≤ ((M + endpointVariation n C a b : ℚ) : ℝ) := by
  rw [Polynomial.eval_eq_sum_range' hd, ← Finset.sum_neg_distrib]
  have ha' := (Rat.cast_nonneg (K := ℝ)).mpr ha
  have hS :
    (∑ j ∈ Finset.range n, -(P.coeff j) * x ^ j) =
      (∑ j ∈ Finset.range n, -(P.coeff j) * (a : ℝ) ^ j) +
        ∑ j ∈ Finset.range n, -(P.coeff j) * (x ^ j - (a : ℝ) ^ j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [hS, ← neg_mul, Rat.cast_add, endpointVariation, endpointVariationTerm, endpoint_max_eq,
    Rat.cast_sum, Rat.cast_mul, Rat.cast_max, Rat.cast_zero, Rat.cast_sub, Rat.cast_pow]
  apply add_le_add hM (Finset.sum_le_sum _)
  intro j hj
  have h₀ := sub_nonneg.mpr (pow_le_pow_left₀ ha' hx.1 j)
  have h₁ := sub_le_sub_right (pow_le_pow_left₀ (ha'.trans hx.1) hx.2 j) ((a : ℝ) ^ j)
  exact mul_le_mul ((hC j hj).trans (le_max_right _ _)) h₁ h₀ (le_max_left _ _)

private def tail19EndpointCap (a b : ℚ) : ℚ :=
  poly19LinearUpper (Finset.range 20) id (fun j ↦ -a ^ j) +
    endpointVariation 20 (fun j ↦ poly19LinearUpper {j} id (fun _ ↦ -1)) a b

private theorem tail19_eval_neg_upper {a b : ℚ} {x : ℝ} (ha : 0 ≤ a)
    (hx : x ∈ Set.Icc (a : ℝ) (b : ℝ)) :
    -gaussianK131Poly19.eval x ≤ (tail19EndpointCap a b : ℝ) := by
  unfold tail19EndpointCap
  apply eval_neg_upper (n := 20) (Nat.lt_succ_of_le gaussian_k131_poly19_degree) ha hx
  · intro j _
    simpa only [Finset.sum_singleton, id_eq, Rat.cast_neg, Rat.cast_one, neg_one_mul] using
      poly19_linear_le {j} id (fun _ ↦ -1)
  · simpa only [Rat.cast_neg, Rat.cast_pow, neg_mul, mul_neg, mul_comm, id_eq] using
      poly19_linear_le (Finset.range 20) id (fun j ↦ -a ^ j)

private def tail27EndpointCap (a b : ℚ) : ℚ :=
  poly27LinearUpper (Finset.range 20) id (fun j ↦ -a ^ j) +
    endpointVariation 20 (fun j ↦ poly27LinearUpper {j} id (fun _ ↦ -1)) a b

private theorem tail27_eval_neg_upper {a b : ℚ} {x : ℝ} (ha : 0 ≤ a)
    (hx : x ∈ Set.Icc (a : ℝ) (b : ℝ)) :
    -gaussianK131Poly27.eval x ≤ (tail27EndpointCap a b : ℝ) := by
  unfold tail27EndpointCap
  apply eval_neg_upper (n := 20) (Nat.lt_succ_of_le gaussian_k131_poly27_degree) ha hx
  · intro j _
    simpa only [Finset.sum_singleton, id_eq, Rat.cast_neg, Rat.cast_one, neg_one_mul] using
      poly27_linear_le {j} id (fun _ ↦ -1)
  · simpa only [Rat.cast_neg, Rat.cast_pow, neg_mul, mul_neg, mul_comm, id_eq] using
      poly27_linear_le (Finset.range 20) id (fun j ↦ -a ^ j)

private def tailInterceptDelta : ℚ :=
  2 * (123 / 10 - 8) / (519674 / 1000000)

/-- The secondary K131 polynomial with the tail's affine intercept. -/
noncomputable def gaussianK131TailPoly27 : Polynomial ℝ :=
  gaussianK131Poly27 +
    Polynomial.C (tailInterceptDelta : ℝ) *
      (Polynomial.C k131Prefactor * shiftPoly gaussianK131InversePoly (9 / 4) +
        Polynomial.C (gaussianK131Amplitude : ℝ) * shiftedInverse)

private theorem tail_poly27_degree : gaussianK131TailPoly27.natDegree ≤ 19 := by
  unfold gaussianK131TailPoly27
  exact
    Polynomial.natDegree_add_le_of_degree_le gaussian_k131_poly27_degree
      (degree_mul_C
        (Polynomial.natDegree_add_le_of_degree_le
          (degree_mul_C (degree_shift inverse_degree_le _) _) (degree_mul_C degree_inverse_shift _))
        _)

private def tailPoly27LinearUpper {ι : Type*} (s : Finset ι) (k : ι → ℕ) (c : ι → ℚ) : ℚ :=
  poly27LinearUpper s k c +
    prefactorLinearUpper
      (∑ i ∈ s, c i * tailInterceptDelta * shiftedCoeff 20 inverseCoeff (9 / 4) (k i)) +
    inverseLinearUpper s k (fun i ↦ c i * tailInterceptDelta * gaussianK131Amplitude)

private theorem tail_poly27_linear_le {ι : Type*} (s : Finset ι) (k : ι → ℕ) (c : ι → ℚ) :
    (∑ i ∈ s, (c i : ℝ) * gaussianK131TailPoly27.coeff (k i)) ≤
      (tailPoly27LinearUpper s k c : ℝ) := by
  have h₁ := poly27_linear_le s k c
  have h₂ :=
    prefactor_linear_le
      (∑ i ∈ s, c i * tailInterceptDelta * shiftedCoeff 20 inverseCoeff (9 / 4) (k i))
  have h₃ := inverse_linear_le s k (fun i ↦ c i * tailInterceptDelta * gaussianK131Amplitude)
  have hs (j : ℕ) :
    (shiftPoly gaussianK131InversePoly (9 / 4)).coeff j =
      (shiftedCoeff 20 inverseCoeff (9 / 4) j : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using coeff_shift_inverse (9 / 4) j
  rw [tailPoly27LinearUpper, Rat.cast_add, Rat.cast_add]
  refine le_trans (le_of_eq ?_) (add_le_add (add_le_add h₁ h₂) h₃)
  simp only [gaussianK131TailPoly27, Polynomial.coeff_add, Polynomial.coeff_C_mul, hs,
    coeff_shifted_inverse, Rat.cast_sum, Rat.cast_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

private def rawTail27Cap (a b : ℚ) : ℚ :=
  tailPoly27LinearUpper (Finset.range 20) id (fun j ↦ -a ^ j) +
    endpointVariation 20 (fun j ↦ tailPoly27LinearUpper {j} id (fun _ ↦ -1)) a b

private theorem raw_tail27_eval_neg_upper {a b : ℚ} {x : ℝ} (ha : 0 ≤ a)
    (hx : x ∈ Set.Icc (a : ℝ) (b : ℝ)) :
    -gaussianK131TailPoly27.eval x ≤ (rawTail27Cap a b : ℝ) := by
  unfold rawTail27Cap
  apply eval_neg_upper (n := 20) (Nat.lt_succ_of_le tail_poly27_degree) ha hx
  · intro j _
    simpa only [Finset.sum_singleton, id_eq, Rat.cast_neg, Rat.cast_one, neg_one_mul] using
      tail_poly27_linear_le {j} id (fun _ ↦ -1)
  · simpa only [Rat.cast_neg, Rat.cast_pow, neg_mul, mul_neg, mul_comm, id_eq] using
      tail_poly27_linear_le (Finset.range 20) id (fun j ↦ -a ^ j)

private def shiftedNegWeight (a : ℚ) (j k : ℕ) : ℚ :=
  -(a ^ (k - j) * (k.choose j : ℚ))

private def shiftedEvalCap (C : ℕ → ℚ) (w : ℚ) : ℚ :=
  ∑ j ∈ Finset.range 20, if j = 0 then C j else max 0 (C j) * w ^ j

private theorem shifted_eval_cap_sound {P : Polynomial ℝ} (hP : P.natDegree ≤ 19) {C : ℕ → ℚ}
    {a b : ℚ} {x : ℝ} (hx : x ∈ Set.Icc (a : ℝ) (b : ℝ))
    (hC : ∀ j, -((shiftPoly P (a : ℝ)).coeff j) ≤ (C j : ℝ)) :
    -P.eval x ≤ (shiftedEvalCap C (b - a) : ℝ) := by
  let Q := shiftPoly P (a : ℝ)
  let z := x - (a : ℝ)
  have hQ : Q.eval z = P.eval x := by
    rw [show Q = shiftPoly P (a : ℝ) from rfl, shiftPoly, Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C]
    rw [sub_add_cancel]
  have hdeg : Q.natDegree < 20 := Nat.lt_succ_of_le (degree_shift hP _)
  have hz : 0 ≤ z := sub_nonneg.mpr hx.1
  have hw : z ≤ ((b - a : ℚ) : ℝ) := by
    rw [Rat.cast_sub]
    exact sub_le_sub_right hx.2 _
  rw [← hQ, Polynomial.eval_eq_sum_range' hdeg, ← Finset.sum_neg_distrib, shiftedEvalCap,
    Rat.cast_sum]
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : j = 0
  · simp only [hj, ite_eq_left, pow_zero, mul_one]
    exact hC 0
  · simp only [ite_eq_right hj, ← neg_mul, Rat.cast_mul, Rat.cast_max, Rat.cast_zero, Rat.cast_pow]
    exact
      mul_le_mul ((hC j).trans (le_max_right _ _)) (pow_le_pow_left₀ hz hw j) (pow_nonneg hz j)
        (le_max_left _ _)

private theorem shifted_coeff_neg_eq {P : Polynomial ℝ} (hP : P.natDegree < 20) (a : ℚ) (j : ℕ) :
    -((shiftPoly P (a : ℝ)).coeff j) =
      ∑ k ∈ Finset.range 20, ((shiftedNegWeight a j k : ℚ) : ℝ) * P.coeff k := by
  rw [shiftPoly, coeff_translate hP, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _
  simp only [shiftedNegWeight, Rat.cast_neg, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast]
  ring

private def shiftedTail19Cap (a b : ℚ) : ℚ :=
  shiftedEvalCap (fun j ↦ poly19LinearUpper (Finset.range 20) id (shiftedNegWeight a j)) (b - a)

private def shiftedTail27Cap (a b : ℚ) : ℚ :=
  shiftedEvalCap (fun j ↦ tailPoly27LinearUpper (Finset.range 20) id (shiftedNegWeight a j)) (b - a)

private theorem shifted_tail19_sound {a b : ℚ} {x : ℝ} (hx : x ∈ Set.Icc (a : ℝ) (b : ℝ)) :
    -gaussianK131Poly19.eval x ≤ (shiftedTail19Cap a b : ℝ) := by
  apply shifted_eval_cap_sound gaussian_k131_poly19_degree hx
  intro j
  rw [shifted_coeff_neg_eq (Nat.lt_succ_of_le gaussian_k131_poly19_degree)]
  exact poly19_linear_le _ id (shiftedNegWeight a j)

private theorem shifted_tail27_sound {a b : ℚ} {x : ℝ} (hx : x ∈ Set.Icc (a : ℝ) (b : ℝ)) :
    -gaussianK131TailPoly27.eval x ≤ (shiftedTail27Cap a b : ℝ) := by
  apply shifted_eval_cap_sound tail_poly27_degree hx
  intro j
  rw [shifted_coeff_neg_eq (Nat.lt_succ_of_le tail_poly27_degree)]
  exact tail_poly27_linear_le _ id (shiftedNegWeight a j)

private theorem tail_zpow_lower {r a v C : ℝ} (ha : 0 < a) (hr : a ≤ r) (hC : 0 ≤ C) (hv : -v ≤ C)
    (n : ℕ) : -(C / a ^ n) ≤ r ^ (-(n : ℤ)) * v := by
  have hi : (r ^ n)⁻¹ ≤ (a ^ n)⁻¹ := inv_anti₀ (pow_pos ha _) (pow_le_pow_left₀ ha.le hr _)
  have h :=
    mul_le_mul_of_nonneg_left (neg_le.mp hv) (inv_nonneg.mpr (pow_nonneg (ha.le.trans hr) n))
  have h' := mul_le_mul_of_nonpos_right hi (neg_nonpos.mpr hC)
  rw [zpow_neg, zpow_natCast]
  simp only [div_eq_mul_inv, mul_neg] at *
  linarith only [h, h']

/-- Transfer upper bounds for the negatives of the two tail polynomials
to a lower bound for the combined, radius-weighted endpoint term. -/
theorem k131_endpoint_tail_lower {y a A B : ℝ} (ha : 0 < a) (hr : a ≤ y ^ (1 / 8 : ℝ)) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (h₁ : -gaussianK131Poly19.eval (2 * Real.log y) ≤ A)
    (h₂ : -gaussianK131Poly27.eval (2 * Real.log y) ≤ B) :
    -(A / a ^ (19 : ℕ)) - B / a ^ (27 : ℕ) ≤ k131EndpointTailTerms y := by
  have hp := tail_zpow_lower ha hr hA h₁ 19
  have hq := tail_zpow_lower ha hr hB h₂ 27
  rw [k131EndpointTailTerms, sub_eq_add_neg]
  exact add_le_add hp hq

private def rawTailPowerCap (A B r : ℚ) : ℚ :=
  max 0 A / r ^ 19 + max 0 B / r ^ 27

private theorem raw_tail_power_cap_sound {y : ℝ} {A B r : ℚ} (hy : 0 ≤ y) (hr : 0 < r)
    (hroot : (r : ℝ) ≤ y ^ (1 / 8 : ℝ)) (hA : -gaussianK131Poly19.eval (2 * Real.log y) ≤ (A : ℝ))
    (hB : -gaussianK131TailPoly27.eval (2 * Real.log y) ≤ (B : ℝ)) :
    -(rawTailPowerCap A B r : ℝ) ≤
      logPowerPoly (-(19 / 8 : ℝ)) gaussianK131Poly19 y +
        logPowerPoly (-(27 / 8 : ℝ)) gaussianK131TailPoly27 y := by
  have h19 := hA.trans (Rat.cast_le.mpr (le_max_right 0 A))
  have h27 := hB.trans (Rat.cast_le.mpr (le_max_right 0 B))
  have hr₀ : (0 : ℝ) < (r : ℝ) := Rat.cast_pos.mpr hr
  have h₁ := tail_zpow_lower hr₀ hroot (Rat.cast_nonneg.mpr (le_max_left _ _)) h19 19
  have h₂ := tail_zpow_lower hr₀ hroot (Rat.cast_nonneg.mpr (le_max_left _ _)) h27 27
  have h := add_le_add h₁ h₂
  rw [← k131_rpow_eighth hy, ← k131_rpow_eighth hy] at h
  have e19 : ((-(19 : ℕ) : ℤ) : ℝ) / 8 = -(19 / 8 : ℝ) := by norm_num only
  have e27 : ((-(27 : ℕ) : ℤ) : ℝ) / 8 = -(27 / 8 : ℝ) := by norm_num only
  rw [e19, e27, ← neg_add] at h
  simpa only [rawTailPowerCap, Rat.cast_add, Rat.cast_div, Rat.cast_pow, logPowerPoly] using h

/-- The rational upper bound on the cost of the two main tail terms on a
logarithmic interval, given a lower bound on the eighth root of the radius. -/
def k131RawTailCap (a b r : ℚ) : ℚ :=
  rawTailPowerCap (tail19EndpointCap a b) (rawTail27Cap a b) r

/-- The rational tail cost bounds the two real power-polynomial terms
uniformly over the specified interval. -/
theorem k131_raw_tail_cap_sound {y : ℝ} {a b r : ℚ} (hy : 0 ≤ y) (ha : 0 ≤ a) (hr : 0 < r)
    (hroot : (r : ℝ) ≤ y ^ (1 / 8 : ℝ)) (hx : 2 * Real.log y ∈ Set.Icc (a : ℝ) (b : ℝ)) :
    -(k131RawTailCap a b r : ℝ) ≤
      logPowerPoly (-(19 / 8 : ℝ)) gaussianK131Poly19 y +
        logPowerPoly (-(27 / 8 : ℝ)) gaussianK131TailPoly27 y := by
  exact
    raw_tail_power_cap_sound hy hr hroot (tail19_eval_neg_upper ha hx)
      (raw_tail27_eval_neg_upper ha hx)

/-- The two main tail terms bounded using coefficients translated to the
left logarithmic endpoint before estimating their variation. -/
def k131ShiftedTailCap (a b r : ℚ) : ℚ :=
  rawTailPowerCap (shiftedTail19Cap a b) (shiftedTail27Cap a b) r

/-- The translated rational cap transfers to the same real power-polynomial
terms as the original K131 tail cap. -/
theorem k131_shifted_tail_cap_sound {y : ℝ} {a b r : ℚ} (hy : 0 ≤ y) (hr : 0 < r)
    (hroot : (r : ℝ) ≤ y ^ (1 / 8 : ℝ)) (hx : 2 * Real.log y ∈ Set.Icc (a : ℝ) (b : ℝ)) :
    -(k131ShiftedTailCap a b r : ℝ) ≤
      logPowerPoly (-(19 / 8 : ℝ)) gaussianK131Poly19 y +
        logPowerPoly (-(27 / 8 : ℝ)) gaussianK131TailPoly27 y := by
  exact raw_tail_power_cap_sound hy hr hroot (shifted_tail19_sound hx) (shifted_tail27_sound hx)

private theorem left_gap_of_caps
    (h₁ :
      tail19EndpointCap (14119427717253463 / 1000000000000000)
          (14119427717253464 / 1000000000000000) ≤
        121010000)
    (h₂ :
      tail27EndpointCap (14119427717253463 / 1000000000000000)
          (14119427717253464 / 1000000000000000) ≤
        3490000000) :
    (1 / 200 : ℝ) < gaussianK131Gap (465644807 / 400000) := by
  have hx := left_endpoint_log
  have ha : (0 : ℚ) ≤ 14119427717253463 / 1000000000000000 := by decide +kernel
  have hp := (tail19_eval_neg_upper ha hx).trans ((Rat.cast_le (K := ℝ)).mpr h₁)
  have hq := (tail27_eval_neg_upper ha hx).trans ((Rat.cast_le (K := ℝ)).mpr h₂)
  norm_num only [Rat.cast_ofNat] at hp hq
  apply k131_left_gap_of_tail_terms
  refine
    lt_of_lt_of_le ?_
      (k131_endpoint_tail_lower (by norm_num only) k131_left_root_bounds.1 (by norm_num only)
        (by norm_num only) hp hq)
  norm_num only

private theorem right_gap_of_caps
    (h₁ :
      tail19EndpointCap (16659360525478489 / 1000000000000000)
          (16659360525478490 / 1000000000000000) ≤
        1650000000)
    (h₂ :
      tail27EndpointCap (16659360525478489 / 1000000000000000)
          (16659360525478490 / 1000000000000000) ≤
        39000000000) :
    (1 / 200 : ℝ) < gaussianK131Gap (1036273 / 250) := by
  have hx := right_endpoint_log
  have ha : (0 : ℚ) ≤ 16659360525478489 / 1000000000000000 := by decide +kernel
  have hp := (tail19_eval_neg_upper ha hx).trans ((Rat.cast_le (K := ℝ)).mpr h₁)
  have hq := (tail27_eval_neg_upper ha hx).trans ((Rat.cast_le (K := ℝ)).mpr h₂)
  norm_num only [Rat.cast_ofNat] at hp hq
  apply k131_right_gap_of_tail_terms
  refine
    lt_of_lt_of_le ?_
      (k131_endpoint_tail_lower (by norm_num only) k131_right_root_bounds.1 (by norm_num only)
        (by norm_num only) hp hq)
  norm_num only

private theorem left_tail19_base :
    poly19LinearUpper (Finset.range 20) id
        (fun j ↦ -(14119427717253463 / 1000000000000000 : ℚ) ^ j) ≤
      121001000 := by
  decide +kernel

private theorem right_tail19_base :
    poly19LinearUpper (Finset.range 20) id
        (fun j ↦ -(16659360525478489 / 1000000000000000 : ℚ) ^ j) ≤
      1647000000 := by
  decide +kernel

private theorem left_tail27_base :
    poly27LinearUpper (Finset.range 20) id
        (fun j ↦ -(14119427717253463 / 1000000000000000 : ℚ) ^ j) ≤
      3489900000 := by
  decide +kernel

private theorem right_tail27_base :
    poly27LinearUpper (Finset.range 20) id
        (fun j ↦ -(16659360525478489 / 1000000000000000 : ℚ) ^ j) ≤
      38800000000 := by
  decide +kernel

private theorem endpoint_variation_of_slopes {C : ℕ → ℚ} {a b M : ℚ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ 17) (h₀ : slopeBlock C 0 ≤ M) (h₁ : slopeBlock C 5 ≤ M) (h₂ : slopeBlock C 10 ≤ M)
    (h₃ : slopeBlock C 15 ≤ M) : endpointVariation 20 C a b ≤ (b - a) * (4 * M) := by
  rw [variation_split]
  have h (i : ℕ) := block_le_slope (C := C) ha hab hb i
  have hs := add_le_add (add_le_add (add_le_add h₀ h₁) h₂) h₃
  have ht := mul_le_mul_of_nonneg_left hs (sub_nonneg.mpr hab)
  linarith only [h 0, h 5, h 10, h 15, ht]

private theorem endpoint_gaps_of_variation
    (h₁ :
      endpointVariation 20 (fun j ↦ poly19LinearUpper {j} id (fun _ ↦ -1))
          (16659360525478489 / 1000000000000000) (16659360525478490 / 1000000000000000) ≤
        9000)
    (h₂ :
      endpointVariation 20 (fun j ↦ poly27LinearUpper {j} id (fun _ ↦ -1))
          (16659360525478489 / 1000000000000000) (16659360525478490 / 1000000000000000) ≤
        100000) :
    (1 / 200 : ℝ) < gaussianK131Gap (465644807 / 400000) ∧
      (1 / 200 : ℝ) < gaussianK131Gap (1036273 / 250) := by
  have hmono (C : ℕ → ℚ) :
    endpointVariation 20 C (14119427717253463 / 1000000000000000)
        (14119427717253464 / 1000000000000000) ≤
      endpointVariation 20 C (16659360525478489 / 1000000000000000)
        (16659360525478490 / 1000000000000000) := by
    apply variation_le <;> decide +kernel
  have hl₁ := (hmono _).trans h₁
  have hl₂ := (hmono _).trans h₂
  refine ⟨left_gap_of_caps ?_ ?_, right_gap_of_caps ?_ ?_⟩
  · unfold tail19EndpointCap
    linarith only [left_tail19_base, hl₁]
  · unfold tail27EndpointCap
    linarith only [left_tail27_base, hl₂]
  · unfold tail19EndpointCap
    linarith only [right_tail19_base, h₁]
  · unfold tail27EndpointCap
    linarith only [right_tail27_base, h₂]

private theorem slope19_0 :
    slopeBlock (fun j ↦ poly19LinearUpper {j} id (fun _ ↦ -1)) 0 ≤ 2250000000000000000 := by
  decide +kernel

private theorem slope19_5 :
    slopeBlock (fun j ↦ poly19LinearUpper {j} id (fun _ ↦ -1)) 5 ≤ 2250000000000000000 := by
  decide +kernel

private theorem slope19_10 :
    slopeBlock (fun j ↦ poly19LinearUpper {j} id (fun _ ↦ -1)) 10 ≤ 2250000000000000000 := by
  decide +kernel

private theorem slope19_15 :
    slopeBlock (fun j ↦ poly19LinearUpper {j} id (fun _ ↦ -1)) 15 ≤ 2250000000000000000 := by
  decide +kernel

private theorem variation19_upper :
    endpointVariation 20 (fun j ↦ poly19LinearUpper {j} id (fun _ ↦ -1))
        (16659360525478489 / 1000000000000000) (16659360525478490 / 1000000000000000) ≤
      9000 := by
  have h :=
    endpoint_variation_of_slopes (a := 16659360525478489 / 1000000000000000) (b :=
      16659360525478490 / 1000000000000000) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) slope19_0 slope19_5 slope19_10 slope19_15
  norm_num only at h
  norm_num only
  exact h

private theorem slope27_0 :
    slopeBlock (fun j ↦ poly27LinearUpper {j} id (fun _ ↦ -1)) 0 ≤ 25000000000000000000 := by
  decide +kernel

private theorem slope27_5 :
    slopeBlock (fun j ↦ poly27LinearUpper {j} id (fun _ ↦ -1)) 5 ≤ 25000000000000000000 := by
  decide +kernel

private theorem slope27_10 :
    slopeBlock (fun j ↦ poly27LinearUpper {j} id (fun _ ↦ -1)) 10 ≤ 25000000000000000000 := by
  decide +kernel

private theorem slope27_15 :
    slopeBlock (fun j ↦ poly27LinearUpper {j} id (fun _ ↦ -1)) 15 ≤ 25000000000000000000 := by
  decide +kernel

private theorem variation27_upper :
    endpointVariation 20 (fun j ↦ poly27LinearUpper {j} id (fun _ ↦ -1))
        (16659360525478489 / 1000000000000000) (16659360525478490 / 1000000000000000) ≤
      100000 := by
  have h :=
    endpoint_variation_of_slopes (a := 16659360525478489 / 1000000000000000) (b :=
      16659360525478490 / 1000000000000000) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) slope27_0 slope27_5 slope27_10 slope27_15
  norm_num only at h
  norm_num only
  exact h

/-- The K131 gap exceeds 1/200 at both endpoints of the affine bridge. -/
theorem k131_endpoint_gaps :
    (1 / 200 : ℝ) < gaussianK131Gap (465644807 / 400000) ∧
      (1 / 200 : ℝ) < gaussianK131Gap (1036273 / 250) := by
  exact endpoint_gaps_of_variation variation19_upper variation27_upper

/-- The K131 gap exceeds 1/200 throughout the affine bridge. -/
theorem gaussian_k131_gap {L : ℝ} (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000) :
    (1 / 200 : ℝ) < gaussianK131Gap (gaussianBridgeScale L) := by
  exact gaussian_k131_gap_of_endpoints hL k131_endpoint_gaps.1 k131_endpoint_gaps.2

end PseudoPrime.PrimeTestBounds.MillerRabin
