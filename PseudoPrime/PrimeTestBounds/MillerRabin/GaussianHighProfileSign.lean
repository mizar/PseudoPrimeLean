/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighCompensation
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianLaplaceMoment
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.GCDMonoid.Finset

/-! # Eventual signs of the high Gaussian profiles -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A positive common denominator can be cleared before testing the
translated coefficients. The sign conclusion is independent of the scale. -/
public theorem profile_shift_nonneg_of_scaled (P : Polynomial ℚ) (b : ℚ) {D : ℚ} (hD : 0 < D)
    (h : ∀ i, 0 ≤ ((Polynomial.C D * P).comp (Polynomial.X + Polynomial.C b)).coeff i) (j : ℕ)
    {t : ℝ} (ht : (b : ℝ) ≤ t) :
    0 ≤ ((Polynomial.derivative^[j]) (P.map (Rat.castHom ℝ))).eval t := by
  apply derivative_nonneg_of_shift _ _ j ht
  intro i
  have hi := h i
  rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.coeff_C_mul] at hi
  have he :
    (P.map (Rat.castHom ℝ)).comp (Polynomial.X + Polynomial.C (b : ℝ)) =
      (P.comp (Polynomial.X + Polynomial.C b)).map (Rat.castHom ℝ) := by
    rw [Polynomial.map_comp, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C,
      Rat.coe_castHom]
  rw [he, Polynomial.coeff_map, Rat.coe_castHom, Rat.cast_nonneg]
  exact nonneg_of_mul_nonneg_right hi hD

/-- An integral profile representing a positive multiple of the rational
profile supplies all the sign checks via integer coefficients. -/
public theorem profile_sign_from_int_shift (P : Polynomial ℚ) (A : Polynomial ℤ) (b : ℤ) {D : ℚ}
    (hD : 0 < D) (hA : A.map (Int.castRingHom ℚ) = Polynomial.C D * P)
    (h : ∀ i, 0 ≤ (A.comp (Polynomial.X + Polynomial.C b)).coeff i) (j : ℕ) {t : ℝ}
    (ht : (b : ℝ) ≤ t) : 0 ≤ ((Polynomial.derivative^[j]) (P.map (Rat.castHom ℝ))).eval t := by
  have ht' : (((b : ℚ) : ℝ)) ≤ t := by simpa only [Rat.cast_intCast] using ht
  refine profile_shift_nonneg_of_scaled P (b : ℚ) hD (fun i ↦ ?_) j ht'
  have he :
    (A.comp (Polynomial.X + Polynomial.C b)).map (Int.castRingHom ℚ) =
      (Polynomial.C D * P).comp (Polynomial.X + Polynomial.C (b : ℚ)) := by
    rw [Polynomial.map_comp, hA, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C,
      Int.coe_castRingHom]
  rw [← he, Polynomial.coeff_map, Int.coe_castRingHom]
  exact Int.cast_nonneg (h i)

/-- Integer binomial sums certify the shifted signs, with one sum for each
index up to the known degree and zero coefficients outside that range. -/
public theorem profile_sign_from_int_moments (P : Polynomial ℚ) (A : Polynomial ℤ) (b : ℤ) (N : ℕ)
    (hN : A.natDegree ≤ N) {D : ℚ} (hD : 0 < D)
    (hA : A.map (Int.castRingHom ℚ) = Polynomial.C D * P)
    (h :
      ∀ i ≤ N,
        0 ≤
          ∑ k ∈ Finset.range (N - i + 1), (Nat.fast_choose (k + i) i : ℤ) * A.coeff (k + i) * b ^ k)
    (j : ℕ) {t : ℝ} (ht : (b : ℝ) ≤ t) :
    0 ≤ ((Polynomial.derivative^[j]) (P.map (Rat.castHom ℝ))).eval t := by
  refine profile_sign_from_int_shift P A b hD hA (fun i ↦ ?_) j ht
  rw [← Polynomial.taylor_apply, Polynomial.taylor_coeff]
  by_cases hi : i ≤ N
  · have hd := (Polynomial.natDegree_hasseDeriv_le A i).trans (Nat.sub_le_sub_right hN i)
    rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hd)]
    simpa only [Polynomial.hasseDeriv_coeff, ← Nat.choose_eq_fast_choose] using h i hi
  · rw [Polynomial.hasseDeriv_eq_zero_of_lt_natDegree A i (hN.trans_lt (lt_of_not_ge hi)),
      Polynomial.eval_zero]

/-- The integer coefficient after clearing a common denominator. -/
public def clearedProfileCoeff (D : ℕ) (q : ℚ) : ℤ :=
  q.num * (D / q.den : ℕ)

/-- Exact divisibility makes the integer coefficient agree with rational scaling. -/
public theorem cleared_profile_coeff_cast (D : ℕ) (q : ℚ) (h : q.den ∣ D) :
    (clearedProfileCoeff D q : ℚ) = (D : ℚ) * q := by
  rw [clearedProfileCoeff, Int.cast_mul, Int.cast_natCast]
  have hD : ((D / q.den : ℕ) : ℚ) * (q.den : ℚ) = (D : ℚ) := by
    rw [← Nat.cast_mul, Nat.div_mul_cancel h]
  calc
    _ = (D : ℚ) * ((q.num : ℚ) / q.den) := by
      rw [← hD, ← mul_div_assoc]
      apply (eq_div_iff (Nat.cast_ne_zero.mpr q.den_ne_zero)).mpr
      ring
    _ = _ := congrArg ((D : ℚ) * ·) (Rat.num_div_den q)

/-- Build the integral polynomial with coefficients cleared by a common
denominator, retaining terms through the given degree bound. -/
public noncomputable def clearedProfile (P : Polynomial ℚ) (D N : ℕ) : Polynomial ℤ :=
  ∑ i ∈ Finset.range (N + 1), Polynomial.monomial i (clearedProfileCoeff D (P.coeff i))

/-- Clearing denominators retains the degree bound used by the integer sums. -/
public theorem cleared_profile_degree (P : Polynomial ℚ) (D N : ℕ) :
    (clearedProfile P D N).natDegree ≤ N := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  exact (Polynomial.natDegree_monomial_le _).trans (Nat.le_of_lt_succ (Finset.mem_range.mp hi))

/-- An exact common denominator yields an integral model of the rational profile. -/
public theorem cleared_profile_map (P : Polynomial ℚ) {D N : ℕ} (hN : P.natDegree ≤ N)
    (hD : ∀ i ≤ N, (P.coeff i).den ∣ D) :
    (clearedProfile P D N).map (Int.castRingHom ℚ) = Polynomial.C (D : ℚ) * P := by
  calc
    _ = Polynomial.C (D : ℚ) * ∑ i ∈ Finset.range (N + 1), Polynomial.monomial i (P.coeff i) := by
      simp only [clearedProfile, Polynomial.map_sum, Polynomial.map_monomial, Int.coe_castRingHom,
        Finset.mul_sum, Polynomial.C_mul_monomial]
      refine Finset.sum_congr rfl fun i hi ↦ congrArg (Polynomial.monomial i) ?_
      exact
        cleared_profile_coeff_cast D (P.coeff i) (hD i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
    _ = _ := congrArg (Polynomial.C (D : ℚ) * ·) (P.as_sum_range' _ (Nat.lt_succ_of_le hN)).symm

/-- The cleared integer binomial sums certify the sign of a physical kernel
and its derivatives without reducing rational additions in the shift. -/
public theorem high_profile_sign_from_cleared (K : HighGaussianKernel) (b : ℤ) {D : ℕ} (hD : 0 < D)
    (hden : ∀ i ≤ 2 * K.degree + 3, (K.ratProfile.coeff i).den ∣ D)
    (h :
      ∀ i ≤ 2 * K.degree + 3,
        0 ≤
          ∑ k ∈ Finset.range (2 * K.degree + 3 - i + 1),
            (Nat.fast_choose (k + i) i : ℤ) *
              (clearedProfile K.ratProfile D (2 * K.degree + 3)).coeff (k + i) *
              b ^ k)
    (j : ℕ) {t : ℝ} (ht : (b : ℝ) ≤ t) :
    0 ≤ ((Polynomial.derivative^[j]) K.realProfile).eval t := by
  rw [← high_comp_profile_map]
  exact
    profile_sign_from_int_moments _ _ _ _ (cleared_profile_degree _ _ _) (Nat.cast_pos.mpr hD)
      (cleared_profile_map _ (high_rat_profile_degree K) hden) h j ht

/-- Recover a cleared coefficient at an index within the retained degree. -/
private theorem cleared_profile_coeff_eq (P : Polynomial ℚ) (D N i : ℕ) (hi : i ≤ N) :
    (clearedProfile P D N).coeff i = clearedProfileCoeff D (P.coeff i) := by
  simp only [clearedProfile, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
    Finsupp.single_apply]
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
      (fun j _ hj ↦ ite_eq_right hj),
    ite_eq_left rfl]

/-- Check the shifted signs using a shared rational input row and exact
integer binomial sums. Rational arithmetic is confined to producing the input row. -/
public def highIntProfileSignCheck (K : HighGaussianKernel) (b : ℤ) : Bool :=
  let N := 2 * K.degree + 3
  let row := K.cellPowerRow 0 1
  let q := fun i : ℕ ↦ row[i]?.getD 0
  let D := (Finset.range (N + 1)).lcm (fun i ↦ (q i).den)
  let a := Array.ofFn (fun i : Fin (N + 1) ↦ clearedProfileCoeff D (q i))
  (List.range (N + 1)).all fun i ↦
    decide
      (0 ≤
        ∑ k ∈ Finset.range (N - i + 1), (Nat.fast_choose (k + i) i : ℤ) * a[k + i]?.getD 0 * b ^ k)

/-- The integer checker certifies the high profile and its derivatives on
the ray from its integer translation point. -/
public theorem high_int_profile_sign (K : HighGaussianKernel) (b : ℤ)
    (h : highIntProfileSignCheck K b = true) (j : ℕ) {t : ℝ} (ht : (b : ℝ) ≤ t) :
    0 ≤ ((Polynomial.derivative^[j]) K.realProfile).eval t := by
  let N := 2 * K.degree + 3
  let q := fun i : ℕ ↦ (K.cellPowerRow 0 1)[i]?.getD 0
  let D := (Finset.range (N + 1)).lcm (fun i ↦ (q i).den)
  have hq (i : ℕ) (hi : i ≤ N) : q i = K.ratProfile.coeff i := by
    dsimp only [q]
    rw [high_cell_power_coeff K 0 1 (Nat.lt_succ_of_le hi), Polynomial.C_1, one_mul, Polynomial.C_0,
      add_zero, Polynomial.comp_X]
  have hD : 0 < D := Nat.pos_of_ne_zero (Finset.lcm_ne_zero_iff.mpr fun i _ ↦ (q i).den_ne_zero)
  have hden (i : ℕ) (hi : i ≤ N) : (K.ratProfile.coeff i).den ∣ D := by
    rw [← hq i hi]
    exact Finset.dvd_lcm (f := fun i ↦ (q i).den) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  refine high_profile_sign_from_cleared K b hD hden (fun i hi ↦ ?_) j ht
  have hc :=
    of_decide_eq_true ((List.all_eq_true.mp h) i (List.mem_range.mpr (Nat.lt_succ_of_le hi)))
  refine hc.trans_eq ?_
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k + i ≤ N :=
    (Nat.add_le_add_right (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) i).trans_eq
      (Nat.sub_add_cancel hi)
  have hk'' := Nat.lt_succ_of_le hk'
  let a := Array.ofFn (fun l : Fin (N + 1) ↦ clearedProfileCoeff D (q l))
  change _ * a[k + i]?.getD 0 * _ = _
  rw [cleared_profile_coeff_eq _ _ _ _ hk']
  have ha : a[k + i]?.getD 0 = clearedProfileCoeff D (q (k + i)) := by
    simp only [a, getElem?_def, Array.size_ofFn, hk'', dite_eq_left, Array.getElem_ofFn,
      Option.getD_some]
  rw [ha, hq _ hk']

/-- The lowest log coordinate used in the high-range H28 estimate. -/
@[expose]
public def profileCorrectionStart : HighGaussianKernel → ℚ
  | .k186 => 35
  | .k196 => 85 / 2

/-- The log coordinate at which the translated coefficient check is made. -/
@[expose]
public def profileCorrectionEnd : HighGaussianKernel → ℤ
  | .k186 => 65
  | .k196 => 80

/-- For a checked high kernel, the H28 absolute tail is bounded by its exact
signed moment and twice the negative moment on the manuscript's finite interval. -/
public theorem high_profile_abs_tail_le (K : HighGaussianKernel)
    (h : highIntProfileSignCheck K (profileCorrectionEnd K) = true) (j : ℕ) {s z : ℝ} (hs : 0 < s)
    (hz : (profileCorrectionStart K : ℝ) ≤ z) :
    let P := (Polynomial.derivative^[j]) K.realProfile
    let Q := P.comp (Polynomial.X + Polynomial.C z)
    (∫ t in Set.Ioi z, Real.exp (-s * t) * |P.eval t|) ≤
      Real.exp (-s * z) *
          (∑ k ∈ Finset.range (Q.natDegree + 1), Q.coeff k * ((k.factorial : ℝ) / s ^ (k + 1))) +
        2 *
          ∫ t in (profileCorrectionStart K : ℝ)..(profileCorrectionEnd K : ℝ),
            Real.exp (-s * t) * max 0 (-P.eval t) := by
  intro P Q
  have h₀ : 0 ≤ (profileCorrectionStart K : ℝ) := by
    cases K <;> norm_num only [profileCorrectionStart, Rat.cast_ofNat, Rat.cast_div]
  have h₁ : (profileCorrectionStart K : ℝ) ≤ (profileCorrectionEnd K : ℝ) := by
    cases K <;>
      norm_num only [profileCorrectionStart, profileCorrectionEnd, Rat.cast_ofNat, Int.cast_ofNat,
        Rat.cast_div]
  exact
    abs_laplace_tail_le_finite P hs h₀ hz h₁ fun t ht ↦
      high_int_profile_sign K (profileCorrectionEnd K) h j ht.le

end PseudoPrime.PrimeTestBounds.MillerRabin
