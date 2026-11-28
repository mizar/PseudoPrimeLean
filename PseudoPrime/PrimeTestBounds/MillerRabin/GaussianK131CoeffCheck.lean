/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Bernstein
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131ReflectionHigher
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Polynomials
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Constants
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Reflection
import PseudoPrime.Analysis.PositiveTaylorTransport
import PseudoPrime.Analysis.ExponentialTaylorRatio
import PseudoPrime.Analysis.ExponentialFixedPointUpperBounds
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianDirectMiddleExp
import Mathlib.Data.List.GetD
import Mathlib.Tactic

/-! # Coefficient comparison for the final K131 curvature certificates -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Upper rational bound for an affine polynomial coefficient. Choosing
the larger product makes the rule valid for either sign of the basis
coefficient, including negative corrections in the K131 Gram expression. -/
def affineCoeffUpper {ι : Type*} (s : Finset ι) (P : ι → Polynomial ℚ) (lo hi : ι → ℚ) (n : ℕ) :
    ℚ :=
  ∑ i ∈ s, max (lo i * (P i).coeff n) (hi i * (P i).coeff n)

/-- Enclose the n-th coefficient of a real linear combination of rational
polynomials using bounds for its scalar weights. -/
theorem affine_coeff_le {ι : Type*} (s : Finset ι) (P : ι → Polynomial ℚ) (lo hi : ι → ℚ)
    (w : ι → ℝ) (hw : ∀ i ∈ s, (lo i : ℝ) ≤ w i ∧ w i ≤ (hi i : ℝ)) (n : ℕ) :
    (∑ i ∈ s, Polynomial.C (w i) * (P i).map (Rat.castHom ℝ)).coeff n ≤
      (affineCoeffUpper s P lo hi n : ℝ) := by
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_map,
    Rat.coe_castHom, affineCoeffUpper, Rat.cast_sum, Rat.cast_max, Rat.cast_mul]
  apply Finset.sum_le_sum
  intro i hi'
  by_cases h : 0 ≤ ((P i).coeff n : ℝ)
  · exact (mul_le_mul_of_nonneg_right (hw i hi').2 h).trans (le_max_right _ _)
  · exact (mul_le_mul_of_nonpos_right (hw i hi').1 (le_of_not_ge h)).trans (le_max_left _ _)

/-- A coefficientwise power upper bound transfers to Bernstein upper
bounds. The weights of the basis conversion are all nonnegative. -/
theorem bernstein_transform_mono {n : ℕ} {c d : Fin (n + 1) → ℝ} (h : ∀ j, c j ≤ d j)
    (k : Fin (n + 1)) :
    (∑ j : Fin (n + 1), c j * ((k.val.choose j.val : ℝ) / (n.choose j.val : ℝ))) ≤
      ∑ j : Fin (n + 1), d j * ((k.val.choose j.val : ℝ) / (n.choose j.val : ℝ)) := by
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_right (h j) (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

/-- Bound a Bernstein coefficient after collecting each uncertain scalar's
entire contribution. This retains cancellation within each rational basis row. -/
theorem bernstein_affine_le {ι : Type*} (s : Finset ι) (n : ℕ) (c : ι → Fin (n + 1) → ℚ)
    (lo hi : ι → ℚ) (w : ι → ℝ) (hw : ∀ i ∈ s, (lo i : ℝ) ≤ w i ∧ w i ≤ (hi i : ℝ))
    (k : Fin (n + 1)) :
    (∑ j : Fin (n + 1),
        (∑ i ∈ s, w i * (c i j : ℝ)) * ((k.val.choose j.val : ℝ) / (n.choose j.val : ℝ))) ≤
      ((∑ i ∈ s,
            let b := ∑ j : Fin (n + 1), c i j * ((k.val.choose j.val : ℚ) / (n.choose j.val : ℚ))
            max (lo i * b) (hi i * b) :
          ℚ) :
        ℝ) := by
  simp only [Finset.sum_mul, mul_assoc, Rat.cast_sum, Rat.cast_max, Rat.cast_mul, Rat.cast_div,
    Rat.cast_natCast]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i hi'
  rw [← Finset.mul_sum]
  let b := ∑ j : Fin (n + 1), (c i j : ℝ) * ((k.val.choose j.val : ℝ) / (n.choose j.val : ℝ))
  by_cases hb : 0 ≤ b
  · exact (mul_le_mul_of_nonneg_right (hw i hi').2 hb).trans (le_max_right _ _)
  · exact (mul_le_mul_of_nonpos_right (hw i hi').1 (le_of_not_ge hb)).trans (le_max_left _ _)

private theorem coeff_eval_fin (P : Polynomial ℝ) {n : ℕ} (hdeg : P.natDegree ≤ n) (t : ℝ) :
    P.eval t = ∑ j : Fin (n + 1), P.coeff j.val * t ^ j.val := by
  let f (j : ℕ) := P.coeff j * t ^ j
  change P.eval t = ∑ j : Fin (n + 1), f j.val
  rw [Fin.sum_univ_eq_sum_range]
  exact Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hdeg) t

/-- The degree and power-coefficient bounds of a normalized polynomial
are enough to check one K131 Bernstein row. No independent Bernstein
representation of the real polynomial is needed. -/
theorem k131_bernstein_of_coeff {a b x : ℝ} (hab : a < b) (hx : x ∈ Set.Icc a b) (i : Fin 5)
    (P : Polynomial ℝ)
    (hdeg :
      (P.comp (Polynomial.C a + Polynomial.C (b - a) * Polynomial.X)).natDegree ≤
        k131BernsteinDegree i)
    (A : Fin (k131BernsteinDegree i + 1) → ℚ)
    (hA :
      ∀ j : Fin (k131BernsteinDegree i + 1),
        (P.comp (Polynomial.C a + Polynomial.C (b - a) * Polynomial.X)).coeff j.val ≤ (A j : ℝ))
    (hcheck :
      ∀ k : Fin (k131BernsteinDegree i + 1),
        (∑ j : Fin (k131BernsteinDegree i + 1),
            A j * ((k.val.choose j.val : ℚ) / ((k131BernsteinDegree i).choose j.val : ℚ))) ≤
          k131BernsteinUpper i k) :
    P.eval x < 0 := by
  let Q := P.comp (Polynomial.C a + Polynomial.C (b - a) * Polynomial.X)
  apply k131_power_interval_neg i hab hx (fun t ↦ P.eval t) (fun j ↦ Q.coeff j.val)
  · intro k
    apply (bernstein_transform_mono hA k).trans
    simpa only [Rat.cast_sum, Rat.cast_mul, Rat.cast_div, Rat.cast_natCast] using
      (Rat.cast_le (K := ℝ)).mpr (hcheck k)
  · intro t
    have h := coeff_eval_fin Q hdeg (t : ℝ)
    simpa only [Q, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X] using h

/-- Polynomial representation of the degree-seventeen Taylor upper bound,
ready for the affine coefficient checks. -/
noncomputable def k131ExpUpperPoly : Polynomial ℝ :=
  (∑ j ∈ Finset.range 17, Polynomial.monomial j ((19 / 16 : ℝ) ^ j / (j.factorial : ℝ))) +
    Polynomial.monomial 17 ((19 / 16 : ℝ) ^ 17 / (17 : ℕ).factorial / (1 - (57 / 16 : ℝ) / 18))

/-- The polynomial version agrees with the analytic exponential upper bound. -/
theorem k131_exp_upper_poly_eval (u : ℝ) : k131ExpUpperPoly.eval u = k131ExpUpper u := by
  simp only [k131ExpUpperPoly, k131ExpUpper, Polynomial.eval_add, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial, mul_pow]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    rw [div_mul_eq_mul_div]
  · ring

/-- The first certificate polynomial includes the exponential majorant
after translating the logarithmic coordinate by fourteen. -/
noncomputable def k131DominantCheckPoly : Polynomial ℝ :=
  (logPowerCurvature (19 / 8) gaussianK131Poly19).comp (Polynomial.X + Polynomial.C 14) +
    Polynomial.C ((2 : ℝ) ^ 24) * k131ExpUpperPoly

/-- Negativity of the actual first certificate polynomial on the translated
interval implies the required curvature inequality for the dominant term. -/
theorem k131_dominant_check_sound {y : ℝ} (hy : 0 < y) (hlog : (2 * Real.log y : ℝ) ∈ Set.Icc 14 17)
    (hc : k131DominantCheckPoly.eval (2 * Real.log y - 14) ≤ 0) :
    logPowerPoly (-(19 / 8 : ℝ)) (logPowerCurvature (19 / 8) gaussianK131Poly19) y < -1 := by
  apply k131_dominant_curvature_lt hy hlog
  simp only [k131DominantCheckPoly, Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_mul, k131_exp_upper_poly_eval, sub_add_cancel] at hc
  exact hc

private theorem degree_mul_C {P : Polynomial ℝ} {n : ℕ} (h : P.natDegree ≤ n) (c : ℝ) :
    (Polynomial.C c * P).natDegree ≤ n :=
  (Polynomial.natDegree_C_mul_le c P).trans h

private theorem degree_sub {P Q : Polynomial ℝ} {n : ℕ} (hP : P.natDegree ≤ n)
    (hQ : Q.natDegree ≤ n) : (P - Q).natDegree ≤ n := by
  exact (Polynomial.natDegree_sub_le P Q).trans (max_le hP hQ)

private theorem degree_comp_affine {P S : Polynomial ℝ} {n : ℕ} (hP : P.natDegree ≤ n)
    (hS : S.natDegree ≤ 1) : (P.comp S).natDegree ≤ n :=
  Polynomial.natDegree_comp_le.trans ((Nat.mul_le_mul hP hS).trans_eq (Nat.mul_one n))

private theorem degree_iter {P : Polynomial ℝ} {n : ℕ} (hP : P.natDegree ≤ n) (j : ℕ) :
    ((Polynomial.derivative^[j]) P).natDegree ≤ n :=
  (Polynomial.natDegree_iterate_derivative P j).trans ((Nat.sub_le _ _).trans hP)

private theorem degree_moment {P : Polynomial ℝ} {n : ℕ} (hP : P.natDegree ≤ n) (a : ℝ) (m : ℕ) :
    (k131MomentPoly P a m).natDegree ≤ n := by
  unfold k131MomentPoly
  exact Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ ↦ degree_mul_C (degree_iter hP j) _

private theorem degree_shift {P : Polynomial ℝ} {n : ℕ} (hP : P.natDegree ≤ n) (h : ℝ) :
    (shiftPoly P h).natDegree ≤ n :=
  degree_comp_affine hP
    (Polynomial.natDegree_add_le_of_degree_le Polynomial.natDegree_X_le
      (by
        rw [Polynomial.natDegree_C]; exact Nat.zero_le _))

private theorem degree_fourier : gaussianK131Fourier.natDegree ≤ 9 := by
  unfold gaussianK131Fourier
  apply degree_mul_C
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  exact
    (Polynomial.natDegree_monomial_le _).trans
      (Nat.le_of_lt_succ ((Finset.mem_range.mp hk).trans_le (Nat.sub_le _ _)))

private theorem degree_shifted_fourier (h : ℝ) : (shiftedFourier h).natDegree ≤ 9 := by
  unfold shiftedFourier
  exact
    degree_mul_C
      (Polynomial.natDegree_add_le_of_degree_le (degree_mul_C (degree_shift degree_fourier _) _)
        (degree_mul_C (degree_shift degree_fourier _) _))
      _

private theorem degree_gram_fourier : gramFourier.natDegree ≤ 9 := by
  unfold gramFourier
  apply Polynomial.natDegree_add_le_of_degree_le
  · exact
      Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ ↦
        degree_mul_C (degree_shifted_fourier _) _
  · exact
      Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ ↦
        Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ ↦
          degree_mul_C (degree_shifted_fourier _) _

private theorem degree_inverse_shift : shiftedInverse.natDegree ≤ 19 := by
  unfold shiftedInverse
  exact
    Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ ↦
      degree_mul_C (degree_shift inverse_degree_le _) _

/-- The first main polynomial has degree at most nineteen. -/
theorem gaussian_k131_poly19_degree : gaussianK131Poly19.natDegree ≤ 19 := by
  unfold gaussianK131Poly19
  have h := Polynomial.natDegree_add_le_of_degree_le degree_fourier degree_gram_fourier
  exact
    degree_sub
      (Polynomial.natDegree_add_le_of_degree_le (degree_mul_C (degree_shift inverse_degree_le _) _)
        (degree_mul_C degree_inverse_shift _))
      ((degree_mul_C (degree_moment h _ _) _).trans (by decide))

private theorem degree_main_tail {P : Polynomial ℝ} (hP : P.natDegree ≤ 9) :
    (mainTailPoly P).natDegree ≤ 11 := by
  have hX := Polynomial.natDegree_pow_le_of_le 2 (Polynomial.natDegree_X_le (R := ℝ))
  have hG : (gammaMainPoly P).natDegree ≤ 9 := degree_sub (degree_mul_C hP _) (degree_iter hP 1)
  unfold mainTailPoly
  exact
    Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_mul_le_of_le hX hP)
      (degree_moment (Polynomial.natDegree_mul_le_of_le hX hG) _ _)

private theorem degree_remainder_gamma : remainderGamma.natDegree ≤ 19 := by
  unfold remainderGamma
  have h :=
    Polynomial.natDegree_add_le_of_degree_le
      (Polynomial.natDegree_add_le_of_degree_le (degree_mul_C inverse_degree_le ((19 / 16 : ℝ) ^ 2))
        (degree_mul_C (degree_iter inverse_degree_le 1) (2 * (19 / 16 : ℝ))))
      (degree_iter inverse_degree_le 2)
  exact
    Polynomial.natDegree_add_le_of_degree_le (degree_mul_C (degree_moment h _ _) _)
      (degree_mul_C h _)

/-- The second main polynomial has degree at most nineteen. -/
theorem gaussian_k131_poly27_degree : gaussianK131Poly27.natDegree ≤ 19 := by
  unfold gaussianK131Poly27
  apply degree_sub _ (degree_mul_C (degree_shift degree_remainder_gamma _) _)
  apply
    Polynomial.natDegree_add_le_of_degree_le _ (degree_mul_C (degree_shift inverse_degree_le _) _)
  apply degree_sub _ (degree_mul_C (degree_shift (degree_moment inverse_degree_le _ _) _) _)
  apply
    degree_sub _
      ((degree_mul_C
            (Polynomial.natDegree_add_le_of_degree_le (degree_main_tail degree_fourier)
              (degree_main_tail degree_gram_fourier))
            _).trans
        (by decide))
  exact
    Polynomial.natDegree_add_le_of_degree_le (degree_mul_C (degree_shift inverse_degree_le _) _)
      (degree_mul_C degree_inverse_shift _)

private theorem degree_curvature {P : Polynomial ℝ} {n : ℕ} (hp : P.natDegree ≤ n) (p : ℝ) :
    (logPowerCurvature p P).natDegree ≤ n := by
  unfold logPowerCurvature
  exact
    Polynomial.natDegree_add_le_of_degree_le
      (degree_sub (degree_mul_C hp _) (degree_mul_C (degree_iter hp 1) _))
      (degree_mul_C (degree_iter hp 2) _)

private theorem degree_exp_upper : k131ExpUpperPoly.natDegree ≤ 17 := by
  unfold k131ExpUpperPoly
  apply Polynomial.natDegree_add_le_of_degree_le _ (Polynomial.natDegree_monomial_le _)
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  exact (Polynomial.natDegree_monomial_le _).trans (Finset.mem_range.mp hj).le

private theorem degree_dominant_check : k131DominantCheckPoly.natDegree ≤ 19 := by
  unfold k131DominantCheckPoly
  exact
    Polynomial.natDegree_add_le_of_degree_le
      (degree_shift (degree_curvature gaussian_k131_poly19_degree _) _)
      (degree_mul_C (degree_exp_upper.trans (by decide)) _)

/-- Translation in the logarithmic variable acts by a finite binomial sum
on the power coefficients. The degree bound gives the summation limit. -/
theorem coeff_translate {P : Polynomial ℝ} {d : ℕ} (hd : P.natDegree < d) (h : ℝ) (k : ℕ) :
    (P.comp (Polynomial.X + Polynomial.C h)).coeff k =
      ∑ j ∈ Finset.range d, P.coeff j * (h ^ (j - k) * (j.choose k : ℝ)) := by
  conv_lhs => rw [P.as_sum_range_C_mul_X_pow' hd]
  simp only [Polynomial.sum_comp, Polynomial.finsetSum_coeff, Polynomial.mul_comp,
    Polynomial.C_comp, Polynomial.pow_comp, Polynomial.X_comp, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_add_C_pow]

/-- Scaling the logarithmic variable multiplies coefficient `k` by the
scale to the power `k`. -/
theorem coeff_scale_variable (P : Polynomial ℝ) (s : ℝ) (k : ℕ) :
    (P.comp (Polynomial.C s * Polynomial.X)).coeff k = P.coeff k * s ^ k := by
  let d := max (P.natDegree + 1) (k + 1)
  have hd : P.natDegree < d := (Nat.lt_succ_self _).trans_le (le_max_left _ _)
  have hk : k ∈ Finset.range d :=
    Finset.mem_range.mpr ((Nat.lt_succ_self _).trans_le (le_max_right _ _))
  conv_lhs => rw [P.as_sum_range_C_mul_X_pow' hd]
  simp only [Polynomial.sum_comp, Polynomial.finsetSum_coeff, Polynomial.mul_comp,
    Polynomial.C_comp, Polynomial.pow_comp, Polynomial.X_comp, mul_pow, ← map_pow, ← mul_assoc,
    ← map_mul, Polynomial.coeff_C_mul_X_pow, Finset.sum_ite_eq, ite_eq_left hk]

/-- Translating and scaling the logarithmic variable gives the power
coefficients on the unit interval used in the two K131 certificates. -/
theorem coeff_affine_variable {P : Polynomial ℝ} {d : ℕ} (hd : P.natDegree < d) (a s : ℝ) (k : ℕ) :
    (P.comp (Polynomial.C a + Polynomial.C s * Polynomial.X)).coeff k =
      (∑ j ∈ Finset.range d, P.coeff j * (a ^ (j - k) * (j.choose k : ℝ))) * s ^ k := by
  have he :
    (Polynomial.X + Polynomial.C a).comp (Polynomial.C s * Polynomial.X) =
      Polynomial.C a + Polynomial.C s * Polynomial.X := by
    simp only [Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp, add_comm]
  rw [← he, ← Polynomial.comp_assoc, coeff_scale_variable, coeff_translate hd]

/-- The coefficient of a K131 moment uses only coefficients at shifted indices
of the input polynomial, with factorial weights from iterated differentiation. -/
theorem coeff_k131_moment (P : Polynomial ℝ) (a : ℝ) (m k : ℕ) :
    (k131MomentPoly P a m).coeff k =
      ∑ j ∈ Finset.range 20,
        (((j + m).factorial : ℝ) / (j.factorial : ℝ) / a ^ (j + m + 1)) *
          (((k + j).descFactorial j : ℝ) * P.coeff (k + j)) := by
  simp only [k131MomentPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_iterate_derivative, nsmul_eq_mul]

/-- Express the curvature coefficient using three consecutive coefficients
of the input polynomial. -/
theorem coeff_log_power_curvature (p : ℝ) (P : Polynomial ℝ) (k : ℕ) :
    (logPowerCurvature p P).coeff k =
      (p * (p + 1)) * P.coeff k - (2 * (2 * p + 1)) * (P.coeff (k + 1) * ((k : ℝ) + 1)) +
        4 * ((P.coeff (k + 2) * ((k : ℝ) + 2)) * ((k : ℝ) + 1)) := by
  simp only [logPowerCurvature, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
    Polynomial.coeff_derivative, Nat.cast_succ, add_assoc, one_add_one_eq_two]

/-- The Taylor upper polynomial has rational coefficients, with the
geometric-tail correction only at degree seventeen. -/
def k131ExpUpperCoeff (k : ℕ) : ℚ :=
  if k < 17 then (19 / 16 : ℚ) ^ k / (k.factorial : ℚ)
  else if k = 17 then (19 / 16 : ℚ) ^ 17 / (17 : ℕ).factorial / (1 - (57 / 16 : ℚ) / 18) else 0

/-- Connect the executable coefficient formula to the real Taylor majorant. -/
theorem coeff_k131_exp_upper (k : ℕ) : k131ExpUpperPoly.coeff k = (k131ExpUpperCoeff k : ℝ) := by
  simp only [k131ExpUpperPoly, k131ExpUpperCoeff, Polynomial.coeff_add, Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial, Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_range]
  by_cases hk : k < 17
  · simp only [ite_eq_left hk, ite_eq_right (Nat.ne_of_lt hk).symm, add_zero, Rat.cast_div,
      Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat]
  · by_cases he : k = 17
    · subst k
      simp only [ite_eq_right hk, ite_true, zero_add, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast,
        Rat.cast_sub, Rat.cast_ofNat, Rat.cast_one]
    · simp only [ite_eq_right hk, ite_eq_right he, ite_eq_right (Ne.symm he), add_zero,
        Rat.cast_zero]

/-- The dominant K131 polynomial after normalization has a finite
curvature contribution and an exact rational exponential contribution. -/
theorem coeff_k131_dominant_normalized (k : ℕ) :
    (k131DominantCheckPoly.comp (Polynomial.C 0 + Polynomial.C 3 * Polynomial.X)).coeff k =
      ((∑ j ∈ Finset.range 20,
            (logPowerCurvature (19 / 8) gaussianK131Poly19).coeff j *
              ((14 : ℝ) ^ (j - k) * (j.choose k : ℝ))) +
          2 ^ 24 * (k131ExpUpperCoeff k : ℝ)) *
        3 ^ k := by
  rw [map_zero, zero_add, coeff_scale_variable]
  unfold k131DominantCheckPoly
  rw [Polynomial.coeff_add, Polynomial.coeff_C_mul, coeff_k131_exp_upper,
    coeff_translate (Nat.lt_succ_of_le (degree_curvature gaussian_k131_poly19_degree _))]

/-- The second K131 row uses the binomial transform on the same
logarithmic interval as the dominant row. -/
theorem coeff_k131_secondary_normalized (k : ℕ) :
    ((logPowerCurvature (27 / 8) gaussianK131Poly27).comp
            (Polynomial.C 14 + Polynomial.C 3 * Polynomial.X)).coeff
        k =
      (∑ j ∈ Finset.range 20,
          (logPowerCurvature (27 / 8) gaussianK131Poly27).coeff j *
            ((14 : ℝ) ^ (j - k) * (j.choose k : ℝ))) *
        3 ^ k := by
  exact
    coeff_affine_variable (Nat.lt_succ_of_le (degree_curvature gaussian_k131_poly27_degree _)) 14 3
      k

private def fourierCoeffFormula (k : ℕ) : ℚ :=
  gaussianK131Amplitude * ∑ j : Fin 9, if k < 10 - j.val then fourierTerm j k else 0

private def fourierCoeff (k : ℕ) : ℚ :=
  ([3 / 8, 81 / 128, 39656520663507039154095 / 88212978044351960904992,
          256576721963243866745031 / 1411407648709631374479872,
          60113122786994062104 / 2756655563885998778281,
          91766364334983975591 / 11026622255543995113124,
          1066343183483831612073 / 441064890221759804524960,
          25654402291265191803987 / 49399267704837098106795520,
          3539730368679427520433 / 49399267704837098106795520,
          6748548706754340093747 / 790388283277393569708728320] :
        List ℚ).getD
    k 0

private theorem fourier_coeff_small (k : Fin 10) :
    fourierCoeffFormula k.val = fourierCoeff k.val := by fin_cases k <;> decide +kernel

private def inverseCoeffFormula (k : ℕ) : ℚ :=
  ∑ j : Fin 9, if 2 * j.val + 3 = k then inverseCoeffs j else 0

private def inverseCoeff (k : ℕ) : ℚ :=
  ([0, 0, 0, 1 / 6, 0, 29 / 120, 0, 841 / 20160, 0, 1 / 15120, 0, 19 / 1663200, 0, 29 / 115315200,
          0, 1 / 9081072000, 0, 1 / 274450176000, 0, 1 / 41716426752000] :
        List ℚ).getD
    k 0

private theorem inverse_coeff_small (k : Fin 20) :
    inverseCoeffFormula k.val = inverseCoeff k.val := by fin_cases k <;> decide +kernel

private theorem coeff_fourier_formula (k : ℕ) :
    gaussianK131Fourier.coeff k = (fourierCoeffFormula k : ℝ) := by
  simp only [gaussianK131Fourier, fourierCoeffFormula, Polynomial.coeff_C_mul,
    Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Finsupp.single_apply, Finset.sum_ite_eq',
    Finset.mem_range, Rat.cast_mul, Rat.cast_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  split <;> simp only [Rat.cast_zero]

private theorem coeff_fourier (k : ℕ) : gaussianK131Fourier.coeff k = (fourierCoeff k : ℝ) := by
  by_cases hk : k < 10
  · rw [coeff_fourier_formula, fourier_coeff_small ⟨k, hk⟩]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (degree_fourier.trans_lt (Nat.le_of_not_gt hk))]
    have h : fourierCoeff k = 0 := by
      unfold fourierCoeff
      apply List.getD_eq_default
      exact Nat.le_of_not_gt hk
    rw [h, Rat.cast_zero]

private theorem coeff_inverse_formula (k : ℕ) :
    gaussianK131InversePoly.coeff k = (inverseCoeffFormula k : ℝ) := by
  simp only [gaussianK131InversePoly, inverseCoeffFormula, Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial, Finsupp.single_apply, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro j _
  split <;> simp only [Rat.cast_zero]

private theorem coeff_inverse (k : ℕ) : gaussianK131InversePoly.coeff k = (inverseCoeff k : ℝ) := by
  by_cases hk : k < 20
  · rw [coeff_inverse_formula, inverse_coeff_small ⟨k, hk⟩]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (inverse_degree_le.trans_lt (Nat.le_of_not_gt hk))]
    have h : inverseCoeff k = 0 := by
      unfold inverseCoeff
      apply List.getD_eq_default
      exact Nat.le_of_not_gt hk
    rw [h, Rat.cast_zero]

private def shiftedCoeff (d : ℕ) (c : ℕ → ℚ) (h : ℚ) (k : ℕ) : ℚ :=
  ∑ j ∈ Finset.Ico k d, c j * (h ^ (j - k) * (j.choose k : ℚ))

private theorem shifted_coeff_eq_sum (d : ℕ) (c : ℕ → ℚ) (h : ℚ) (k : ℕ) :
    shiftedCoeff d c h k = ∑ j ∈ Finset.range d, c j * (h ^ (j - k) * (j.choose k : ℚ)) := by
  unfold shiftedCoeff
  apply Finset.sum_subset (fun j hj ↦ Finset.mem_range.mpr (Finset.mem_Ico.mp hj).2)
  intro j hj hn
  have hjk : j < k :=
    Nat.lt_of_not_ge fun hle ↦ hn (Finset.mem_Ico.mpr ⟨hle, Finset.mem_range.mp hj⟩)
  rw [Nat.choose_eq_zero_of_lt hjk, Nat.cast_zero, mul_zero, mul_zero]

private theorem coeff_shift_rat {P : Polynomial ℝ} {d : ℕ} (hd : P.natDegree < d) (c : ℕ → ℚ)
    (hc : ∀ j, P.coeff j = (c j : ℝ)) (h : ℚ) (k : ℕ) :
    (shiftPoly P (h : ℝ)).coeff k = (shiftedCoeff d c h k : ℝ) := by
  rw [shiftPoly, coeff_translate hd]
  simp only [shifted_coeff_eq_sum, hc, Rat.cast_sum, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast]

private theorem coeff_shift_inverse (h : ℚ) (k : ℕ) :
    (shiftPoly gaussianK131InversePoly (h : ℝ)).coeff k = (shiftedCoeff 20 inverseCoeff h k : ℝ) :=
  coeff_shift_rat (Nat.lt_succ_of_le inverse_degree_le) inverseCoeff coeff_inverse h k

private theorem coeff_shift_fourier (h : ℚ) (k : ℕ) :
    (shiftPoly gaussianK131Fourier (h : ℝ)).coeff k = (shiftedCoeff 10 fourierCoeff h k : ℝ) :=
  coeff_shift_rat (Nat.lt_succ_of_le degree_fourier) fourierCoeff coeff_fourier h k

private def expTaylorUpper (t : ℚ) : ℚ :=
  PseudoPrime.Analysis.gammaPositiveTaylor t 80 + 2 * t ^ 80 / (80 : ℕ).factorial

private theorem exp_pos_bounds {t : ℚ} (ht : 0 ≤ t) (hmax : t ≤ 16) :
    (PseudoPrime.Analysis.gammaPositiveTaylor t 80 : ℝ) ≤ Real.exp (t : ℝ) ∧
      Real.exp (t : ℝ) ≤ (expTaylorUpper t : ℝ) := by
  refine ⟨PseudoPrime.Analysis.gamma_positive_taylor_le_exp ht 80, ?_⟩
  have h :=
    PseudoPrime.Analysis.exp_le_taylor_ratio (n := 80) (q := 1 / 2)
      ((Rat.cast_nonneg (K := ℝ)).mpr ht) (by norm_num only) (by norm_num only)
      (show (t : ℝ) / ((80 + 1 : ℕ) : ℝ) ≤ 1 / 2
        by
        have hb : (t : ℝ) ≤ 16 := by exact_mod_cast hmax
        norm_num only [Nat.reduceAdd, Nat.cast_ofNat]
        linarith only [hb])
  simp only [expTaylorUpper, PseudoPrime.Analysis.gammaPositiveTaylor, Rat.cast_add, Rat.cast_sum,
    Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_natCast]
  convert h using 1
  ring

private theorem exp_taylor_pos {t : ℚ} (ht : 0 ≤ t) :
    0 < PseudoPrime.Analysis.gammaPositiveTaylor t 80 := by
  unfold PseudoPrime.Analysis.gammaPositiveTaylor
  apply Finset.sum_pos'
  · exact fun j _ ↦ div_nonneg (pow_nonneg ht j) (Nat.cast_nonneg _)
  · exact
      ⟨0, Finset.mem_range.mpr (by decide), by
        norm_num only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, zero_lt_one]⟩

private def expWeightLower (t : ℚ) : ℚ :=
  if 0 ≤ t then PseudoPrime.Analysis.gammaPositiveTaylor t 80 else (expTaylorUpper (-t))⁻¹

private def expWeightUpper (t : ℚ) : ℚ :=
  if 0 ≤ t then expTaylorUpper t else (PseudoPrime.Analysis.gammaPositiveTaylor (-t) 80)⁻¹

private theorem exp_weight_bounds {t : ℚ} (ht : |t| ≤ 16) :
    (expWeightLower t : ℝ) ≤ Real.exp (t : ℝ) ∧ Real.exp (t : ℝ) ≤ (expWeightUpper t : ℝ) := by
  obtain ht₀ | ht₀ := le_or_gt 0 t
  · simpa only [expWeightLower, expWeightUpper, ite_eq_left ht₀] using
      exp_pos_bounds ht₀ ((le_abs_self t).trans ht)
  · have hn := (neg_nonneg.mpr ht₀.le)
    obtain ⟨hl, hu⟩ := exp_pos_bounds hn ((neg_le_abs t).trans ht)
    have hp := (Rat.cast_pos (K := ℝ)).mpr (exp_taylor_pos hn)
    simp only [expWeightLower, expWeightUpper, ite_eq_right (not_le.mpr ht₀), Rat.cast_inv]
    rw [← neg_neg (t : ℝ), Real.exp_neg, ← Rat.cast_neg]
    exact ⟨inv_anti₀ (Real.exp_pos _) hu, inv_anti₀ hp hl⟩

private def offsetRat : Fin 4 → ℚ :=
  ![0, 1 / 10, 21 / 10, 9 / 2]

private theorem offset_cast (j : Fin 4) : offsets j = (offsetRat j : ℝ) := by
  fin_cases j
  · change (0 : ℝ) = ((0 : ℚ) : ℝ)
    exact Rat.cast_zero.symm
  · change (1 / 10 : ℝ) = ((1 / 10 : ℚ) : ℝ)
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  · change (21 / 10 : ℝ) = ((21 / 10 : ℚ) : ℝ)
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
  · change (9 / 2 : ℝ) = ((9 / 2 : ℚ) : ℝ)
    norm_num only [Rat.cast_div, Rat.cast_ofNat]

private theorem exp_fourier_weights (h : ℚ) (hh : |h| ≤ 7) :
    let t : ℚ := (27 / 16) * |h|
    ((expWeightLower (-t) : ℝ) ≤ Real.exp (-(27 / 16 : ℝ) * (|h| : ℚ)) ∧
        Real.exp (-(27 / 16 : ℝ) * (|h| : ℚ)) ≤ (expWeightUpper (-t) : ℝ)) ∧
      ((expWeightLower t : ℝ) ≤ Real.exp ((27 / 16 : ℝ) * (|h| : ℚ)) ∧
        Real.exp ((27 / 16 : ℝ) * (|h| : ℚ)) ≤ (expWeightUpper t : ℝ)) := by
  dsimp only
  have ht : 0 ≤ (27 / 16 : ℚ) * |h| := mul_nonneg (by norm_num only) (abs_nonneg _)
  have hmax : (27 / 16 : ℚ) * |h| ≤ 16 := by linarith only [hh]
  have hpos := exp_weight_bounds (t := (27 / 16) * |h|) (by rwa [abs_of_nonneg ht])
  have hneg := exp_weight_bounds (t := -((27 / 16) * |h|)) (by rwa [abs_neg, abs_of_nonneg ht])
  simpa only [Rat.cast_mul, Rat.cast_neg, Rat.cast_div, Rat.cast_ofNat, neg_mul] using
    And.intro hneg hpos

private theorem offset_bounds (j : Fin 4) : 0 ≤ offsetRat j ∧ offsetRat j ≤ 9 / 2 := by
  fin_cases j
  · change (0 : ℚ) ≤ 0 ∧ (0 : ℚ) ≤ 9 / 2
    exact ⟨le_rfl, by norm_num only⟩
  · change (0 : ℚ) ≤ 1 / 10 ∧ (1 / 10 : ℚ) ≤ 9 / 2
    exact ⟨by norm_num only, by norm_num only⟩
  · change (0 : ℚ) ≤ 21 / 10 ∧ (21 / 10 : ℚ) ≤ 9 / 2
    exact ⟨by norm_num only, by norm_num only⟩
  · change (0 : ℚ) ≤ 9 / 2 ∧ (9 / 2 : ℚ) ≤ 9 / 2
    exact ⟨by norm_num only, le_rfl⟩

private theorem exp_conductor_weights (j : Fin 4) :
    let h := 9 / 4 + offsetRat j
    let t := (27 / 16) * |h|
    ((expWeightLower (-t) : ℝ) ≤ Real.exp (-(27 / 16 : ℝ) * (|h| : ℚ)) ∧
        Real.exp (-(27 / 16 : ℝ) * (|h| : ℚ)) ≤ (expWeightUpper (-t) : ℝ)) ∧
      ((expWeightLower t : ℝ) ≤ Real.exp ((27 / 16 : ℝ) * (|h| : ℚ)) ∧
        Real.exp ((27 / 16 : ℝ) * (|h| : ℚ)) ≤ (expWeightUpper t : ℝ)) := by
  apply exp_fourier_weights
  rw [abs_le]
  exact ⟨by linarith only [(offset_bounds j).1], by linarith only [(offset_bounds j).2]⟩

private theorem exp_gram_weights (i j : Fin 4) :
    let h := offsetRat i - offsetRat j
    let t := (27 / 16) * |h|
    ((expWeightLower (-t) : ℝ) ≤ Real.exp (-(27 / 16 : ℝ) * (|h| : ℚ)) ∧
        Real.exp (-(27 / 16 : ℝ) * (|h| : ℚ)) ≤ (expWeightUpper (-t) : ℝ)) ∧
      ((expWeightLower t : ℝ) ≤ Real.exp ((27 / 16 : ℝ) * (|h| : ℚ)) ∧
        Real.exp ((27 / 16 : ℝ) * (|h| : ℚ)) ≤ (expWeightUpper t : ℝ)) := by
  apply exp_fourier_weights
  rw [abs_le]
  exact
    ⟨by linarith only [(offset_bounds i).1, (offset_bounds j).2], by
      linarith only [(offset_bounds i).2, (offset_bounds j).1]⟩

private noncomputable def shiftedFourierCoeff (h : ℚ) (k : ℕ) : ℝ :=
  (1 / 2) *
    (Real.exp (-(27 / 16 : ℝ) * (|h| : ℚ)) * (shiftedCoeff 10 fourierCoeff |h| k : ℝ) +
      Real.exp ((27 / 16 : ℝ) * (|h| : ℚ)) * (shiftedCoeff 10 fourierCoeff (-|h|) k : ℝ))

private theorem coeff_shifted_fourier (h : ℚ) (k : ℕ) :
    (shiftedFourier (h : ℝ)).coeff k = shiftedFourierCoeff h k := by
  simp only [shiftedFourier, shiftedFourierCoeff, Polynomial.coeff_C_mul, Polynomial.coeff_add,
    ← Rat.cast_abs, ← Rat.cast_neg, coeff_shift_fourier]

private noncomputable def gramFourierCoeff (k : ℕ) : ℝ :=
  (∑ j : Fin 4, -gram j * shiftedFourierCoeff (9 / 4 + offsetRat j) k) +
    ∑ i : Fin 4,
      ∑ j : Fin 4, (gram i * gram j / 2) * shiftedFourierCoeff (offsetRat i - offsetRat j) k

private theorem coeff_gram_fourier (k : ℕ) : gramFourier.coeff k = gramFourierCoeff k := by
  simp only [gramFourier, gramFourierCoeff, Polynomial.coeff_add, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul, offset_cast, ← Rat.cast_sub]
  have h : (9 / 4 : ℝ) = ((9 / 4 : ℚ) : ℝ) := by norm_num only [Rat.cast_div, Rat.cast_ofNat]
  simp only [h, ← Rat.cast_add, coeff_shifted_fourier]

private def gramRat : Fin 4 → ℚ :=
  ![1831 / 10000, -973 / 5000, 1 / 80, -13 / 1250]

private theorem gram_cast (j : Fin 4) : gram j = (gramRat j : ℝ) := by
  fin_cases j
  · change (1831 / 10000 : ℝ) = ((1831 / 10000 : ℚ) : ℝ)
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
  · change (-973 / 5000 : ℝ) = ((-973 / 5000 : ℚ) : ℝ)
    norm_num only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat]
  · change (1 / 80 : ℝ) = ((1 / 80 : ℚ) : ℝ)
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  · change (-13 / 1250 : ℝ) = ((-13 / 1250 : ℚ) : ℝ)
    norm_num only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat]

/-- Working scale for the range-reduced exponential computed by the row checker. -/
private def expTickScale : ℕ :=
  10 ^ 32

/-- Accumulate each Taylor term once and keep the sum of the preceding terms. -/
private def expTaylorAccum (next : ℕ → ℕ → ℕ) (initial : ℕ) : ℕ → ℕ × ℕ
  | 0 => (initial, 0)
  | j + 1 =>
    let p := expTaylorAccum next initial j
    (next j p.1, p.2 + p.1)

/-- The accumulator agrees with the term recurrence and its partial sum. -/
private theorem exp_taylor_accum_eq (next : ℕ → ℕ → ℕ) (f : ℕ → ℕ)
    (hf : ∀ j, f (j + 1) = next j (f j)) (n : ℕ) :
    expTaylorAccum next (f 0) n = (f n, ∑ j ∈ Finset.range n, f j) := by
  induction n with
  | zero => simp only [expTaylorAccum, Finset.range_zero, Finset.sum_empty]
  | succ n ih => simp only [expTaylorAccum, ih, Finset.sum_range_succ, hf]

/-- Round the next scaled Taylor term down by natural division. -/
private def expLowerStep (a b j x : ℕ) : ℕ :=
  x * a / (b * (j + 1))

/-- Round the next scaled Taylor term up by ceiling division. -/
private def expUpperStep (a b j x : ℕ) : ℕ :=
  (x * a + b * (j + 1) - 1) / (b * (j + 1))

/-- The scaled lower and upper Taylor sums at the reduced nonnegative argument. -/
private def expTickSeed (a b : ℕ) : Analysis.IntegerInterval :=
  let L := expTaylorAccum (expLowerStep a b) expTickScale 24
  let U := expTaylorAccum (expUpperStep a b) expTickScale 24
  ⟨L.2, (U.2 + 2 * U.1 : ℕ)⟩

/-- The shared recurrence computes the existing lower and upper Taylor sums. -/
private theorem exp_tick_seed_eq (a b : ℕ) :
    expTickSeed a b =
      ⟨Analysis.expFixedPointLowerSum a b expTickScale 24,
        Analysis.expFixedPointUpperSum a b expTickScale 24⟩ := by
  have hl :=
    exp_taylor_accum_eq (expLowerStep a b) (Analysis.expFixedPointLowerTerm a b expTickScale)
      (fun _ ↦ rfl) 24
  have hu :=
    exp_taylor_accum_eq (expUpperStep a b) (Analysis.expFixedPointUpperTerm a b expTickScale)
      (fun _ ↦ rfl) 24
  change expTaylorAccum (expLowerStep a b) expTickScale 24 = _ at hl
  change expTaylorAccum (expUpperStep a b) expTickScale 24 = _ at hu
  simp only [expTickSeed, hl, hu, Analysis.expFixedPointLowerSum, Analysis.expFixedPointUpperSum]

/-- At a reduced argument at most one, the 24-term integer sums enclose the exponential. -/
private theorem exp_tick_seed_sound (a b : ℕ) (hb : 0 < b) (h : (a : ℝ) / b ≤ 1) :
    (expTickSeed a b).Contains expTickScale (Real.exp ((a : ℝ) / b)) := by
  have hs : (0 : ℝ) < expTickScale := Nat.cast_pos.mpr (by decide)
  have hsize : ((a : ℝ) / b) / (24 + 1 : ℕ) ≤ 1 / 2 := by
    norm_num only at *
    linarith only [h]
  exact
    ⟨(div_le_iff₀ hs).mpr
        (by
          simpa only [exp_tick_seed_eq, Int.cast_natCast, mul_comm] using
            Analysis.expFixedPointLowerSum_le_exp a b expTickScale 24),
      (le_div_iff₀ hs).mpr
        (by
          simpa only [exp_tick_seed_eq, Int.cast_natCast, mul_comm] using
            Analysis.expFixedPointUpperSum_ge_exp a b expTickScale 24 hb hsize)⟩

/-- Enclose a nonnegative rational argument by raising the reduced enclosure to the 64th power. -/
private def expPositiveTicks (t : ℚ) : Analysis.IntegerInterval :=
  gaussianMidExpFold expTickScale 64 ⟨expTickScale, expTickScale⟩
    (expTickSeed t.num.natAbs (64 * t.den))

/-- For a rational argument in [0,16], the binary interval evaluation encloses its exponential. -/
private theorem exp_positive_ticks_sound {t : ℚ} (ht : 0 ≤ t) (htmax : t ≤ 16) :
    (expPositiveTicks t).Contains expTickScale (Real.exp (t : ℝ)) := by
  have hnum : 0 ≤ t.num := Rat.num_nonneg.mpr ht
  have hden : 0 < 64 * t.den := Nat.mul_pos (by decide) t.den_pos
  have htR : (t : ℝ) ≤ 16 := by exact_mod_cast htmax
  have hx : (t.num.natAbs : ℝ) / ((64 * t.den : ℕ) : ℝ) = (t : ℝ) / 64 := by
    rw [← Int.cast_natCast, Int.natAbs_of_nonneg hnum]
    simp only [Nat.cast_mul, Nat.cast_ofNat, Rat.cast_def, div_div]
    rw [mul_comm (64 : ℝ)]
  have hseed :=
    exp_tick_seed_sound t.num.natAbs (64 * t.den) hden
      (by
        rw [hx]; linarith only [htR])
  have hG : (0 : ℤ) < (expTickScale : ℤ) := by decide
  have hs : (0 : ℝ) < expTickScale := Nat.cast_pos.mpr (by decide)
  have hone : (Analysis.IntegerInterval.mk expTickScale expTickScale).Contains expTickScale 1 := by
    simp only [Analysis.IntegerInterval.Contains, Int.cast_natCast, div_self hs.ne', le_refl,
      and_self]
  have hf := gaussian_mid_exp_fold_contains hG 64 hone hseed
  have he : (64 : ℝ) * ((t : ℝ) / 64) = (t : ℝ) := by
    rw [mul_comm, div_mul_cancel₀ _ (by norm_num only)]
  simpa only [expPositiveTicks, hx, one_mul, ← Real.exp_natCast_mul, Nat.cast_ofNat, he] using hf

/-- Enclose a signed exponent, using a reciprocal for the negative case. -/
private def expSignedTicks (t : ℚ) (I : Analysis.IntegerInterval) : Analysis.IntegerInterval :=
  if 0 ≤ t then I else gaussianMidScaledInv expTickScale 1 I

/-- For absolute argument at most 16 and positive input ticks, the signed enclosure is sound. -/
private theorem exp_signed_ticks_sound {t : ℚ} (ht : |t| ≤ 16)
    (hp : 0 < (expPositiveTicks |t|).lower) :
    (expSignedTicks t (expPositiveTicks |t|)).Contains expTickScale (Real.exp (t : ℝ)) := by
  unfold expSignedTicks
  split
  · rename_i h
    rw [abs_of_nonneg h]
    exact exp_positive_ticks_sound h ((le_abs_self t).trans ht)
  · rename_i h
    have hn : 0 ≤ -t := neg_nonneg.mpr (le_of_not_ge h)
    have hh := exp_positive_ticks_sound hn ((neg_le_abs t).trans ht)
    have hl : 0 < (expPositiveTicks (-t)).lower := by
      simpa only [abs_of_neg (lt_of_not_ge h)] using hp
    have hv :=
      gaussian_mid_scaled_inv (by decide : (0 : ℤ) < (expTickScale : ℤ)) (by decide : (0 : ℤ) ≤ 1)
        hl hh
    rw [abs_of_neg (lt_of_not_ge h)]
    simpa only [Int.cast_one, Rat.cast_neg, one_div, ← Real.exp_neg, neg_neg] using hv

private def expRoundedRows : List (ℚ × ℕ) :=
  [(-729 / 64, 113009360431463080), (-243 / 32, 5035890497369525153),
    (-297 / 40, 5961608766843588517), (-2349 / 320, 6486449911098249323),
    (-81 / 20, 174223746394935113869), (-1269 / 320, 189561852934701385088),
    (-243 / 64, 224407898643731458864), (-567 / 160, 289047308508338007126),
    (-27 / 8, 342181183116660346985), (-27 / 160, 8447200570049834451892),
    (0, 10000000000000000000000), (27 / 160, 11838241458899092735231),
    (27 / 8, 292242837812349398350082), (567 / 160, 345964127865647808432972),
    (243 / 64, 445617113320772005746529), (1269 / 320, 527532298570889832027577),
    (81 / 20, 573974570454461974772050), (2349 / 320, 15416753597202843548049084),
    (297 / 40, 16773995730173624379293546), (243 / 32, 19857461168433775936687028),
    (729 / 64, 884882452375678361262766619)]

private def expRoundScale : ℚ :=
  10 ^ 22

/-- Verify that the computed enclosure fits inside the recorded adjacent decimal ticks. -/
private def expRoundValid (r : ℚ × ℕ) : Bool :=
  let I := expPositiveTicks |r.1|
  let J := expSignedTicks r.1 I
  decide
    (|r.1| ≤ 16 ∧
      0 < I.lower ∧
      (r.2 : ℤ) * expTickScale ≤ J.lower * (10 ^ 22 : ℤ) ∧
      J.upper * (10 ^ 22 : ℤ) ≤ ((r.2 : ℤ) + 1) * expTickScale)

private theorem exp_rounded_valid : expRoundedRows.all expRoundValid = true := by decide +kernel

/-- A checked decimal row encloses the exponential at its recorded argument. -/
private theorem exp_round_sound (r : ℚ × ℕ) (h : expRoundValid r = true) :
    (r.2 : ℝ) / expRoundScale ≤ Real.exp (r.1 : ℝ) ∧
      Real.exp (r.1 : ℝ) ≤ ((r.2 : ℝ) + 1) / expRoundScale := by
  obtain ⟨ht, hp, hlo, hhi⟩ := of_decide_eq_true h
  obtain ⟨hl, hu⟩ := exp_signed_ticks_sound ht hp
  have hD : (0 : ℝ) < (10 : ℝ) ^ 22 := by norm_num only
  have hG : (0 : ℝ) < (expTickScale : ℝ) := Nat.cast_pos.mpr (by decide)
  have hloR := (Int.cast_le (R := ℝ)).mpr hlo
  have hhiR := (Int.cast_le (R := ℝ)).mpr hhi
  simp only [Int.cast_mul, Int.cast_natCast, Int.cast_pow, Int.cast_ofNat, Int.cast_add,
    Int.cast_one] at hloR hhiR
  simp only [expRoundScale, Rat.cast_pow, Rat.cast_ofNat]
  exact ⟨((div_le_div_iff₀ hD hG).mpr hloR).trans hl, hu.trans ((div_le_div_iff₀ hG hD).mpr hhiR)⟩

private def expRounded (t : ℚ) : ℚ × ℚ :=
  match expRoundedRows.find? (fun r ↦ r.1 == t) with
  | some r => ((r.2 : ℚ) / expRoundScale, ((r.2 : ℚ) + 1) / expRoundScale)
  | none => (expWeightLower t, expWeightUpper t)

/-- The stored rounded interval encloses the exponential, with Taylor bounds for other inputs. -/
private theorem exp_rounded_bounds {t : ℚ} (ht : |t| ≤ 16) :
    ((expRounded t).1 : ℝ) ≤ Real.exp (t : ℝ) ∧ Real.exp (t : ℝ) ≤ ((expRounded t).2 : ℝ) := by
  unfold expRounded
  split
  · rename_i r hr
    have hv := List.all_eq_true.mp exp_rounded_valid r (List.mem_of_find?_eq_some hr)
    have hk := List.find?_some hr
    have he : r.1 = t := eq_of_beq hk
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_add, Rat.cast_one, he] using
      exp_round_sound r hv
  · exact exp_weight_bounds ht

private def expContributionUpper (t v : ℚ) : ℚ :=
  let b := expRounded t
  max (b.1 * v) (b.2 * v)

/-- The sign of the coefficient determines which rounded endpoint supplies an upper bound. -/
private theorem exp_contribution_le {t v : ℚ} (ht : |t| ≤ 16) :
    Real.exp (t : ℝ) * (v : ℝ) ≤ (expContributionUpper t v : ℝ) := by
  simp only [expContributionUpper, Rat.cast_max, Rat.cast_mul]
  obtain ⟨hlo, hhi⟩ := exp_rounded_bounds ht
  by_cases hv : 0 ≤ (v : ℝ)
  · exact (mul_le_mul_of_nonneg_right hhi hv).trans (le_max_right _ _)
  · exact (mul_le_mul_of_nonpos_right hlo (le_of_not_ge hv)).trans (le_max_left _ _)

private def shiftedFourierUpper (h v₁ v₂ : ℚ) : ℚ :=
  let t := (27 / 16) * |h|
  expContributionUpper (-t) v₁ + expContributionUpper t v₂

private theorem shifted_fourier_linear_le {ι : Type*} (s : Finset ι) (k : ι → ℕ) (c : ι → ℚ) (h : ℚ)
    (hh : |h| ≤ 7) :
    (∑ j ∈ s, (c j : ℝ) * shiftedFourierCoeff h (k j)) ≤
      (shiftedFourierUpper h (∑ j ∈ s, c j / 2 * shiftedCoeff 10 fourierCoeff |h| (k j))
          (∑ j ∈ s, c j / 2 * shiftedCoeff 10 fourierCoeff (-|h|) (k j)) :
        ℝ) := by
  have ht : 0 ≤ (27 / 16 : ℚ) * |h| := mul_nonneg (by norm_num only) (abs_nonneg _)
  have hmax : |((27 / 16 : ℚ) * |h|)| ≤ 16 := by
    rw [abs_of_nonneg ht]
    linarith only [hh]
  have h₁ :=
    exp_contribution_le (t := -((27 / 16) * |h|)) (v :=
      ∑ j ∈ s, c j / 2 * shiftedCoeff 10 fourierCoeff |h| (k j))
      (by simpa only [abs_neg] using hmax)
  have h₂ :=
    exp_contribution_le (v := ∑ j ∈ s, c j / 2 * shiftedCoeff 10 fourierCoeff (-|h|) (k j)) hmax
  simp only [shiftedFourierUpper, Rat.cast_add]
  refine le_trans ?_ (add_le_add h₁ h₂)
  simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro j _
  unfold shiftedFourierCoeff
  simp only [neg_mul]
  ring

private def fourierLinearUpper {ι : Type*} (s : Finset ι) (k : ι → ℕ) (c : ι → ℚ) (h : ℚ) : ℚ :=
  shiftedFourierUpper h (∑ j ∈ s, c j / 2 * shiftedCoeff 10 fourierCoeff |h| (k j))
    (∑ j ∈ s, c j / 2 * shiftedCoeff 10 fourierCoeff (-|h|) (k j))

/-- The seven distinct shifts of the quadratic Gram part, including the diagonal. -/
private def gramPairOffset : Fin 7 → ℚ :=
  ![0, offsetRat 0 - offsetRat 1, offsetRat 0 - offsetRat 2, offsetRat 0 - offsetRat 3,
    offsetRat 1 - offsetRat 2, offsetRat 1 - offsetRat 3, offsetRat 2 - offsetRat 3]

/-- Combine the four diagonal weights and the two weights of each off-diagonal pair. -/
private def gramPairWeight : Fin 7 → ℚ :=
  ![(gramRat 0 ^ 2 + gramRat 1 ^ 2 + gramRat 2 ^ 2 + gramRat 3 ^ 2) / 2, gramRat 0 * gramRat 1,
    gramRat 0 * gramRat 2, gramRat 0 * gramRat 3, gramRat 1 * gramRat 2, gramRat 1 * gramRat 3,
    gramRat 2 * gramRat 3]

/-- The shifted Fourier coefficient depends on the absolute difference only. -/
private theorem shifted_fourier_sub_swap (a b : ℚ) (k : ℕ) :
    shiftedFourierCoeff (a - b) k = shiftedFourierCoeff (b - a) k := by
  simp only [shiftedFourierCoeff, abs_sub_comm a b]

/-- Collect symmetric Gram terms before applying a numerical interval bound. -/
private theorem gram_pair_group_eq (k : ℕ) :
    (∑ i : Fin 4,
        ∑ j : Fin 4,
          ((gramRat i : ℝ) * gramRat j / 2) * shiftedFourierCoeff (offsetRat i - offsetRat j) k) =
      ∑ i : Fin 7, (gramPairWeight i : ℝ) * shiftedFourierCoeff (gramPairOffset i) k := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero, gramPairOffset,
    gramPairWeight, Matrix.cons_val_zero, Matrix.cons_val_succ, Rat.cast_add, Rat.cast_div,
    Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat, sub_self]
  have h₂ : (1 : Fin 3).succ = (2 : Fin 4) := rfl
  have h₃ : (1 : Fin 2).succ.succ = (3 : Fin 4) := rfl
  rw [h₂, h₃, shifted_fourier_sub_swap (offsetRat 1) (offsetRat 0),
    shifted_fourier_sub_swap (offsetRat 2) (offsetRat 0),
    shifted_fourier_sub_swap (offsetRat 3) (offsetRat 0),
    shifted_fourier_sub_swap (offsetRat 2) (offsetRat 1),
    shifted_fourier_sub_swap (offsetRat 3) (offsetRat 1),
    shifted_fourier_sub_swap (offsetRat 3) (offsetRat 2)]
  ring

/-- The four linear shifts and the seven distinct quadratic shifts bound the Gram row. -/
private def gramLinearUpper {ι : Type*} (s : Finset ι) (k : ι → ℕ) (c : ι → ℚ) : ℚ :=
  (∑ j : Fin 4, fourierLinearUpper s k (fun r ↦ c r * -gramRat j) (9 / 4 + offsetRat j)) +
    ∑ j : Fin 7, fourierLinearUpper s k (fun r ↦ c r * gramPairWeight j) (gramPairOffset j)

private theorem gram_fourier_linear_le {ι : Type*} (s : Finset ι) (k : ι → ℕ) (c : ι → ℚ) :
    (∑ r ∈ s, (c r : ℝ) * gramFourierCoeff (k r)) ≤ (gramLinearUpper s k c : ℝ) := by
  simp only [gramFourierCoeff, gram_cast, gram_pair_group_eq, gramLinearUpper, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum, ← mul_assoc, Rat.cast_add, Rat.cast_sum]
  apply add_le_add
  · rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro j _
    have hh : |9 / 4 + offsetRat j| ≤ (7 : ℚ) := by
      rw [abs_le]
      exact ⟨by linarith only [(offset_bounds j).1], by linarith only [(offset_bounds j).2]⟩
    simpa only [fourierLinearUpper, Rat.cast_mul, Rat.cast_neg] using
      shifted_fourier_linear_le s k (fun r ↦ c r * -gramRat j) _ hh
  · rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro j _
    have hh : |gramPairOffset j| ≤ (7 : ℚ) := by fin_cases j <;> decide +kernel
    simpa only [fourierLinearUpper, Rat.cast_mul] using
      shifted_fourier_linear_le s k (fun r ↦ c r * gramPairWeight j) _ hh

private noncomputable def shiftedInverseCoeff (k : ℕ) : ℝ :=
  ∑ j : Fin 4,
    (-gram j * Real.exp ((27 / 16 : ℝ) * offsetRat j)) *
      (shiftedCoeff 20 inverseCoeff (-offsetRat j) k : ℝ)

private theorem coeff_shifted_inverse (k : ℕ) : shiftedInverse.coeff k = shiftedInverseCoeff k := by
  simp only [shiftedInverse, shiftedInverseCoeff, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul, offset_cast, ← Rat.cast_neg, coeff_shift_inverse]

private def inverseLinearUpper {ι : Type*} (s : Finset ι) (k : ι → ℕ) (c : ι → ℚ) : ℚ :=
  ∑ j : Fin 4,
    expContributionUpper ((27 / 16) * offsetRat j)
      (∑ r ∈ s, c r * (-gramRat j) * shiftedCoeff 20 inverseCoeff (-offsetRat j) (k r))

private theorem inverse_linear_le {ι : Type*} (s : Finset ι) (k : ι → ℕ) (c : ι → ℚ) :
    (∑ r ∈ s, (c r : ℝ) * shiftedInverseCoeff (k r)) ≤ (inverseLinearUpper s k c : ℝ) := by
  simp only [shiftedInverseCoeff, inverseLinearUpper, Finset.mul_sum, Rat.cast_sum, gram_cast]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro j _
  have hb : |(27 / 16 : ℚ) * offsetRat j| ≤ 16 := by
    rw [abs_of_nonneg (mul_nonneg (by norm_num only) (offset_bounds j).1)]
    linarith only [(offset_bounds j).2]
  refine le_trans ?_ (exp_contribution_le hb)
  simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_neg, Rat.cast_div, Rat.cast_ofNat, Finset.mul_sum]
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro r _
  ring

private def prefactorLinearUpper (v : ℚ) : ℚ :=
  expContributionUpper (-(27 / 16) * (9 / 4)) (gaussianK131Amplitude * v)

private theorem prefactor_linear_le (v : ℚ) :
    k131Prefactor * (v : ℝ) ≤ (prefactorLinearUpper v : ℝ) := by
  have h :=
    exp_contribution_le (t := -(27 / 16) * (9 / 4)) (v := gaussianK131Amplitude * v)
      (by
        rw [abs_le]; constructor <;> norm_num only)
  simpa only [prefactorLinearUpper, k131Prefactor, Rat.cast_mul, Rat.cast_neg, Rat.cast_div,
    Rat.cast_ofNat, mul_left_comm, mul_comm, mul_assoc] using h

private noncomputable def momentCoeff (c : ℕ → ℝ) (a : ℝ) (m k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range 20,
    (((j + m).factorial : ℝ) / (j.factorial : ℝ) / a ^ (j + m + 1)) *
      (((k + j).descFactorial j : ℝ) * c (k + j))

private def momentWeight (a : ℚ) (m k j : ℕ) : ℚ :=
  if m = 0 then ((k + j).descFactorial j : ℚ) / a ^ (j + 1)
  else
    (((j + m).factorial : ℚ) / (j.factorial : ℚ) / a ^ (j + m + 1)) * ((k + j).descFactorial j : ℚ)

private theorem moment_weight_eq (a : ℚ) (m k j : ℕ) :
    momentWeight a m k j =
      (((j + m).factorial : ℚ) / (j.factorial : ℚ) / a ^ (j + m + 1)) *
        ((k + j).descFactorial j : ℚ) := by
  unfold momentWeight
  split
  · rename_i hm
    subst m
    have hf : (j.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
    simp only [Nat.add_zero, div_self hf, div_mul_eq_mul_div, one_mul]
  · rfl

private theorem moment_coeff_weights (c : ℕ → ℝ) (a : ℚ) (m k : ℕ) :
    momentCoeff c (a : ℝ) m k = ∑ j ∈ Finset.range 20, (momentWeight a m k j : ℝ) * c (k + j) := by
  simp only [momentCoeff, moment_weight_eq, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_natCast, mul_assoc]

private def momentGramWeight {ι : Type*} (s : Finset ι) (k : ι → ℕ) (c : ι → ℚ) (a : ℚ) (m j : ℕ) :
    ℚ :=
  ∑ r ∈ s, if k r ≤ j ∧ j - k r < 20 then c r * momentWeight a m (k r) (j - k r) else 0

private theorem gram_coeff_zero {j : ℕ} (hj : 10 ≤ j) : gramFourierCoeff j = 0 := by
  rw [← coeff_gram_fourier]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (degree_gram_fourier.trans_lt hj)

private theorem moment_gram_fiber {ι : Type*} (s : Finset ι) (k : ι → ℕ) (c : ι → ℚ) (a : ℚ)
    (m j : ℕ) :
    (∑ r ∈ (s ×ˢ Finset.range 20).filter (fun r ↦ k r.1 + r.2 = j),
        c r.1 * momentWeight a m (k r.1) r.2) =
      momentGramWeight s k c a m j := by
  simp only [Finset.sum_filter, Finset.sum_product, momentGramWeight]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hj : k r ≤ j
  · have he (u : ℕ) : (k r + u = j) = (u = j - k r) := by
      apply propext
      constructor
      · intro hu
        rw [← hu, Nat.add_sub_cancel_left]
      · rintro rfl
        exact Nat.add_sub_of_le hj
    simp only [he, Finset.sum_ite_eq', Finset.mem_range, hj, true_and]
  · have hz (u : ℕ) : k r + u ≠ j := fun h ↦ hj (h ▸ Nat.le_add_right _ _)
    simp only [hz, ite_false, Finset.sum_const_zero, hj, false_and]

private theorem moment_linear_collect {ι : Type*} (s : Finset ι) (k : ι → ℕ) (c : ι → ℚ) (a : ℚ)
    (m : ℕ) (p : ℕ → ℝ) (hp : ∀ j, 10 ≤ j → p j = 0) :
    (∑ r ∈ s, (c r : ℝ) * momentCoeff p (a : ℝ) m (k r)) =
      ∑ j ∈ Finset.range 10, (momentGramWeight s k c a m j : ℝ) * p j := by
  rw [show
      (∑ r ∈ s, (c r : ℝ) * momentCoeff p (a : ℝ) m (k r)) =
        ∑ r ∈ s ×ˢ Finset.range 20,
          ((c r.1 * momentWeight a m (k r.1) r.2 : ℚ) : ℝ) * p (k r.1 + r.2)
      by
      simp only [moment_coeff_weights, Finset.sum_product, Finset.mul_sum, Rat.cast_mul, mul_assoc]]
  let t := s ×ˢ Finset.range 20
  let g : ι × ℕ → ℕ := fun r ↦ k r.1 + r.2
  let w : ι × ℕ → ℚ := fun r ↦ c r.1 * momentWeight a m (k r.1) r.2
  change (∑ r ∈ t, (w r : ℝ) * p (g r)) = _
  have hf :
    (∑ r ∈ t, (w r : ℝ) * p (g r)) =
      ∑ r ∈ t.filter (fun r ↦ g r ∈ Finset.range 10), (w r : ℝ) * p (g r) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro r hr hn
    have hg : ¬g r < 10 := fun h ↦ hn (Finset.mem_filter.mpr ⟨hr, Finset.mem_range.mpr h⟩)
    rw [hp _ (Nat.le_of_not_gt hg), mul_zero]
  rw [hf, ← Finset.sum_fiberwise_eq_sum_filter (g := g) (t := Finset.range 10)]
  apply Finset.sum_congr rfl
  intro j _
  have he := congrArg (fun x : ℚ ↦ (x : ℝ)) (moment_gram_fiber s k c a m j)
  simp only [Rat.cast_sum] at he
  have hg : ∀ r : ι × ℕ, g r = j → p (g r) = p j := fun r hr ↦ congrArg p hr
  rw [← he, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r hr
  rw [hg r (Finset.mem_filter.mp hr).2]

private theorem moment_gram_linear_le {ι : Type*} (s : Finset ι) (k : ι → ℕ) (c : ι → ℚ) (a : ℚ)
    (m : ℕ) :
    (∑ r ∈ s, (c r : ℝ) * momentCoeff gramFourierCoeff (a : ℝ) m (k r)) ≤
      (gramLinearUpper (Finset.range 10) id (momentGramWeight s k c a m) : ℝ) := by
  rw [moment_linear_collect s k c a m gramFourierCoeff (fun _ ↦ gram_coeff_zero)]
  exact gram_fourier_linear_le (Finset.range 10) id (momentGramWeight s k c a m)

private noncomputable def poly19Coeff (k : ℕ) : ℝ :=
  (-2 * k131Prefactor / (519674 / 1000000 : ℝ)) * (shiftedCoeff 20 inverseCoeff (9 / 4) k : ℝ) +
      (-2 * (gaussianK131Amplitude : ℝ) / (519674 / 1000000 : ℝ)) * shiftedInverseCoeff k -
    4 * momentCoeff (fun j ↦ (fourierCoeff j : ℝ) + gramFourierCoeff j) (19 / 16) 0 k

private theorem coeff_k131_poly19 (k : ℕ) : gaussianK131Poly19.coeff k = poly19Coeff k := by
  have h : (9 / 4 : ℝ) = ((9 / 4 : ℚ) : ℝ) := by norm_num only [Rat.cast_div, Rat.cast_ofNat]
  simp only [gaussianK131Poly19, poly19Coeff, Polynomial.coeff_add, Polynomial.coeff_sub,
    Polynomial.coeff_C_mul, h, coeff_shift_inverse, coeff_shifted_inverse, coeff_k131_moment,
    momentCoeff, coeff_fourier, coeff_gram_fourier]

private def poly19LinearUpper {ι : Type*} (s : Finset ι) (k : ι → ℕ) (c : ι → ℚ) : ℚ :=
  let scale : ℚ := 519674 / 1000000
  prefactorLinearUpper (∑ r ∈ s, c r * (-2 / scale) * shiftedCoeff 20 inverseCoeff (9 / 4) (k r)) +
    inverseLinearUpper s k (fun r ↦ c r * (-2 * gaussianK131Amplitude / scale)) +
    (∑ j ∈ Finset.range 10,
      momentGramWeight s k (fun r ↦ c r * -4) (19 / 16) 0 j * fourierCoeff j) +
    gramLinearUpper (Finset.range 10) id (momentGramWeight s k (fun r ↦ c r * -4) (19 / 16) 0)

private theorem poly19_linear_le {ι : Type*} (s : Finset ι) (k : ι → ℕ) (c : ι → ℚ) :
    (∑ r ∈ s, (c r : ℝ) * gaussianK131Poly19.coeff (k r)) ≤ (poly19LinearUpper s k c : ℝ) := by
  let scale : ℚ := 519674 / 1000000
  have h₁ :=
    prefactor_linear_le (∑ r ∈ s, c r * (-2 / scale) * shiftedCoeff 20 inverseCoeff (9 / 4) (k r))
  have h₂ := inverse_linear_le s k (fun r ↦ c r * (-2 * gaussianK131Amplitude / scale))
  have h₃ := moment_gram_linear_le s k (fun r ↦ c r * -4) (19 / 16) 0
  have ha : (19 / 16 : ℝ) = ((19 / 16 : ℚ) : ℝ) := by norm_num only [Rat.cast_div, Rat.cast_ofNat]
  have hz (j : ℕ) (hj : 10 ≤ j) : (fourierCoeff j : ℝ) = 0 := by
    rw [← coeff_fourier]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (degree_fourier.trans_lt hj)
  have hf :=
    moment_linear_collect s k (fun r ↦ c r * -4) (19 / 16) 0 (fun j ↦ (fourierCoeff j : ℝ)) hz
  have hf' :
    (∑ r ∈ s,
        ((c r * -4 : ℚ) : ℝ) *
          momentCoeff (fun j ↦ (fourierCoeff j : ℝ)) ((19 / 16 : ℚ) : ℝ) 0 (k r)) ≤
      ((∑ j ∈ Finset.range 10,
            momentGramWeight s k (fun r ↦ c r * -4) (19 / 16) 0 j * fourierCoeff j :
          ℚ) :
        ℝ) := by
    simp only [Rat.cast_sum, Rat.cast_mul]
    exact le_of_eq (by simpa only [Rat.cast_mul] using hf)
  have he := add_le_add (add_le_add (add_le_add h₁ h₂) hf') h₃
  dsimp only [scale] at he
  simp only [poly19LinearUpper, Rat.cast_add]
  refine le_trans ?_ he
  apply le_of_eq
  simp only [coeff_k131_poly19, poly19Coeff, ha, moment_coeff_weights]
  simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat, Finset.mul_sum,
    mul_add, mul_sub, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  rw [add_assoc (_ + _), ← Finset.sum_add_distrib]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro j _
    ring

private def curvatureWeight (p : ℚ) (j : ℕ) : Fin 3 → ℚ :=
  ![p * (p + 1), -(2 * (2 * p + 1)) * (j + 1), 4 * (j + 2) * (j + 1)]

private theorem coeff_curvature_sum (p : ℚ) (P : Polynomial ℝ) (j : ℕ) :
    (logPowerCurvature (p : ℝ) P).coeff j =
      ∑ r : Fin 3, (curvatureWeight p j r : ℝ) * P.coeff (j + r.val) := by
  rw [coeff_log_power_curvature, Fin.sum_univ_three]
  change
    _ =
      ((p * (p + 1) : ℚ) : ℝ) * P.coeff j +
        ((-(2 * (2 * p + 1)) * (j + 1) : ℚ) : ℝ) * P.coeff (j + 1) +
        ((4 * (j + 2) * (j + 1) : ℚ) : ℝ) * P.coeff (j + 2)
  simp only [Rat.cast_mul, Rat.cast_add, Rat.cast_neg, Rat.cast_natCast, Rat.cast_one,
    Rat.cast_ofNat]
  ring

private def translatedWeight (j k : ℕ) : ℚ :=
  14 ^ (j - k) * (j.choose k : ℚ) * 3 ^ k

private theorem coeff_poly19_tail (k : ℕ) (hk : 10 ≤ k) :
    gaussianK131Poly19.coeff k =
      (-2 * k131Prefactor / (519674 / 1000000 : ℝ)) * (shiftedCoeff 20 inverseCoeff (9 / 4) k : ℝ) +
        (-2 * (gaussianK131Amplitude : ℝ) / (519674 / 1000000 : ℝ)) * shiftedInverseCoeff k := by
  have hd :=
    degree_moment (Polynomial.natDegree_add_le_of_degree_le degree_fourier degree_gram_fourier)
      (19 / 16) 0
  have hz := Polynomial.coeff_eq_zero_of_natDegree_lt (hd.trans_lt hk)
  have h : (9 / 4 : ℝ) = ((9 / 4 : ℚ) : ℝ) := by norm_num only [Rat.cast_div, Rat.cast_ofNat]
  simp only [gaussianK131Poly19, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
    hz, mul_zero, sub_zero, h, coeff_shift_inverse, coeff_shifted_inverse]

private def poly19TailUpper {ι : Type*} (s : Finset ι) (k : ι → ℕ) (c : ι → ℚ) : ℚ :=
  let scale : ℚ := 519674 / 1000000
  prefactorLinearUpper (∑ r ∈ s, c r * (-2 / scale) * shiftedCoeff 20 inverseCoeff (9 / 4) (k r)) +
    inverseLinearUpper s k (fun r ↦ c r * (-2 * gaussianK131Amplitude / scale))

private theorem poly19_tail_le {ι : Type*} (s : Finset ι) (k : ι → ℕ) (c : ι → ℚ)
    (hk : ∀ r ∈ s, 10 ≤ k r) :
    (∑ r ∈ s, (c r : ℝ) * gaussianK131Poly19.coeff (k r)) ≤ (poly19TailUpper s k c : ℝ) := by
  let scale : ℚ := 519674 / 1000000
  have h₁ :=
    prefactor_linear_le (∑ r ∈ s, c r * (-2 / scale) * shiftedCoeff 20 inverseCoeff (9 / 4) (k r))
  have h₂ := inverse_linear_le s k (fun r ↦ c r * (-2 * gaussianK131Amplitude / scale))
  simp only [poly19TailUpper, Rat.cast_add]
  refine le_trans ?_ (add_le_add h₁ h₂)
  apply le_of_eq
  simp only [scale, Rat.cast_sum, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  rw [coeff_poly19_tail _ (hk r hr)]
  ring

private def dominantCoreUpper (k : ℕ) : ℚ :=
  let s := Finset.Ico k 20 ×ˢ (Finset.univ : Finset (Fin 3))
  let index := fun r : ℕ × Fin 3 ↦ r.1 + r.2.val
  let weight := fun r : ℕ × Fin 3 ↦ translatedWeight r.1 k * curvatureWeight (19 / 8) r.1 r.2
  if 10 ≤ k then poly19TailUpper s index weight else poly19LinearUpper s index weight

private theorem dominant_core_le (k : ℕ) :
    (∑ r ∈ Finset.Ico k 20 ×ˢ (Finset.univ : Finset (Fin 3)),
        ((translatedWeight r.1 k * curvatureWeight (19 / 8) r.1 r.2 : ℚ) : ℝ) *
          gaussianK131Poly19.coeff (r.1 + r.2.val)) ≤
      (dominantCoreUpper k : ℝ) := by
  unfold dominantCoreUpper
  split
  · rename_i hk
    apply poly19_tail_le
    intro r hr
    exact hk.trans ((Finset.mem_Ico.mp (Finset.mem_product.mp hr).1).1.trans (Nat.le_add_right _ _))
  · exact poly19_linear_le _ _ _

private def dominantCoeffUpper (k : ℕ) : ℚ :=
  dominantCoreUpper k + 2 ^ 24 * k131ExpUpperCoeff k * 3 ^ k

private theorem coeff_dominant_le (k : ℕ) :
    (k131DominantCheckPoly.comp (Polynomial.C 0 + Polynomial.C 3 * Polynomial.X)).coeff k ≤
      (dominantCoeffUpper k : ℝ) := by
  have hp : (19 / 8 : ℝ) = ((19 / 8 : ℚ) : ℝ) := by norm_num only [Rat.cast_div, Rat.cast_ofNat]
  have hs :
    ∀ f : ℕ → ℝ,
      (∑ j ∈ Finset.Ico k 20, f j * (14 ^ (j - k) * (j.choose k : ℝ))) =
        ∑ j ∈ Finset.range 20, f j * (14 ^ (j - k) * (j.choose k : ℝ)) := by
    intro f
    apply Finset.sum_subset (fun j hj ↦ Finset.mem_range.mpr (Finset.mem_Ico.mp hj).2)
    intro j hj hn
    have hjk : j < k :=
      Nat.lt_of_not_ge fun hle ↦ hn (Finset.mem_Ico.mpr ⟨hle, Finset.mem_range.mp hj⟩)
    rw [Nat.choose_eq_zero_of_lt hjk, Nat.cast_zero, mul_zero, mul_zero]
  rw [coeff_k131_dominant_normalized, add_mul]
  rw [← hs]
  simp only [dominantCoeffUpper, Rat.cast_add, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat]
  apply add_le_add_left
  refine le_trans ?_ (dominant_core_le k)
  apply le_of_eq
  simp only [hp, coeff_curvature_sum]
  simp only [Finset.sum_product, Finset.sum_mul, translatedWeight, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_natCast, Rat.cast_ofNat]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro r _
  ring

private theorem coeff_dominant_from_main (k : ℕ) :
    (k131DominantCheckPoly.comp (Polynomial.C 0 + Polynomial.C 3 * Polynomial.X)).coeff k =
      ((∑ j ∈ Finset.range 20,
            ((19 / 8 * (19 / 8 + 1)) * poly19Coeff j -
                  (2 * (2 * (19 / 8) + 1)) * (poly19Coeff (j + 1) * ((j : ℝ) + 1)) +
                4 * ((poly19Coeff (j + 2) * ((j : ℝ) + 2)) * ((j : ℝ) + 1))) *
              ((14 : ℝ) ^ (j - k) * (j.choose k : ℝ))) +
          2 ^ 24 * (k131ExpUpperCoeff k : ℝ)) *
        3 ^ k := by
  simp only [coeff_k131_dominant_normalized, coeff_log_power_curvature, coeff_k131_poly19]

private theorem coeff_moment_from {P : Polynomial ℝ} {c : ℕ → ℝ} (hc : ∀ j, P.coeff j = c j) (a : ℝ)
    (m k : ℕ) : (k131MomentPoly P a m).coeff k = momentCoeff c a m k := by
  simp only [coeff_k131_moment, momentCoeff, hc]

private noncomputable def mainTailCoeff (c : ℕ → ℝ) (k : ℕ) : ℝ :=
  (if k < 2 then 0 else c (k - 2)) +
    momentCoeff
      (fun j ↦ if j < 2 then 0 else (35 / 16) * c (j - 2) - c (j - 2 + 1) * ((j - 2 : ℕ) + 1 : ℝ))
      (27 / 16) 0 k

private theorem coeff_X_sq_mul (P : Polynomial ℝ) (k : ℕ) :
    (Polynomial.X ^ 2 * P).coeff k = if k < 2 then 0 else P.coeff (k - 2) := by
  rw [mul_comm, Polynomial.coeff_mul_X_pow']
  split <;> rename_i h
  · rw [ite_eq_right (Nat.not_lt.mpr h)]
  · rw [ite_eq_left (Nat.lt_of_not_ge h)]

private theorem coeff_main_tail {P : Polynomial ℝ} {c : ℕ → ℝ} (hc : ∀ j, P.coeff j = c j) (k : ℕ) :
    (mainTailPoly P).coeff k = mainTailCoeff c k := by
  unfold mainTailPoly mainTailCoeff
  rw [Polynomial.coeff_add, coeff_X_sq_mul, hc]
  congr 1
  apply coeff_moment_from
  intro j
  simp only [coeff_X_sq_mul, gammaMainPoly, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
    Polynomial.coeff_derivative, hc]

private def tailMomentIndices {ι : Type*} (s : Finset ι) (k : ι → ℕ) : Finset (ι × ℕ) :=
  (s ×ˢ Finset.range 20).filter fun r ↦ 2 ≤ k r.1 + r.2

private def tailMomentWeight {ι : Type*} (k : ι → ℕ) (c : ι → ℚ) (r : ι × ℕ) : ℚ :=
  c r.1 * momentWeight (27 / 16) 0 (k r.1) r.2

private theorem main_tail_linear_eq {ι : Type*} (s : Finset ι) (k : ι → ℕ) (c : ι → ℚ) (p : ℕ → ℝ) :
    (∑ r ∈ s, (c r : ℝ) * mainTailCoeff p (k r)) =
      (∑ r ∈ s.filter (fun r ↦ 2 ≤ k r), (c r : ℝ) * p (k r - 2)) +
        (∑ r ∈ tailMomentIndices s k,
          ((tailMomentWeight k c r * (35 / 16) : ℚ) : ℝ) * p (k r.1 + r.2 - 2)) +
        ∑ r ∈ tailMomentIndices s k,
          ((tailMomentWeight k c r * -(((k r.1 + r.2 - 2 : ℕ) : ℚ) + 1) : ℚ) : ℝ) *
            p (k r.1 + r.2 - 2 + 1) := by
  have he : (27 / 16 : ℝ) = ((27 / 16 : ℚ) : ℝ) := by norm_num only [Rat.cast_div, Rat.cast_ofNat]
  simp only [mainTailCoeff, he, moment_coeff_weights]
  simp only [tailMomentIndices, tailMomentWeight, Finset.sum_filter, Finset.sum_product,
    Rat.cast_mul, Rat.cast_neg, Rat.cast_div, Rat.cast_ofNat, Rat.cast_add, Rat.cast_natCast,
    Rat.cast_one, mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  · by_cases hr : 2 ≤ k r
    · simp only [ite_eq_left hr, ite_eq_right (not_lt.mpr hr)]
    · simp only [ite_eq_right hr, ite_eq_left (Nat.lt_of_not_ge hr), mul_zero]
  · apply Finset.sum_congr rfl
    intro j _
    by_cases hj : 2 ≤ k r + j
    · simp only [ite_eq_left hj, ite_eq_right (not_lt.mpr hj)]
      ring
    · simp only [ite_eq_right hj, ite_eq_left (Nat.lt_of_not_ge hj), mul_zero, add_zero]

private def collectWeight {ι : Type*} (s : Finset ι) (k : ι → ℕ) (c : ι → ℚ) (j : ℕ) : ℚ :=
  ∑ r ∈ s.filter (fun r ↦ k r = j), c r

private theorem collect_gram_linear {ι : Type*} (s : Finset ι) (k : ι → ℕ) (c : ι → ℚ) :
    (∑ r ∈ s, (c r : ℝ) * gramFourierCoeff (k r)) =
      ∑ j ∈ Finset.range 10, (collectWeight s k c j : ℝ) * gramFourierCoeff j := by
  have hf :
    (∑ r ∈ s, (c r : ℝ) * gramFourierCoeff (k r)) =
      ∑ r ∈ s.filter (fun r ↦ k r ∈ Finset.range 10), (c r : ℝ) * gramFourierCoeff (k r) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro r hr hn
    have hg : ¬k r < 10 := fun h ↦ hn (Finset.mem_filter.mpr ⟨hr, Finset.mem_range.mpr h⟩)
    rw [gram_coeff_zero (Nat.le_of_not_gt hg), mul_zero]
  rw [hf, ← Finset.sum_fiberwise_eq_sum_filter (g := k) (t := Finset.range 10)]
  apply Finset.sum_congr rfl
  intro j _
  simp only [collectWeight, Rat.cast_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r hr
  rw [(Finset.mem_filter.mp hr).2]

/-- The three analytic sums grouped by the Fourier coefficient index. -/
private def gramTailGather {ι : Type*} (s : Finset ι) (k : ι → ℕ) (c : ι → ℚ) (j : ℕ) : ℚ :=
  collectWeight (s.filter (fun r ↦ 2 ≤ k r)) (fun r ↦ k r - 2) c j +
    collectWeight (tailMomentIndices s k) (fun r ↦ k r.1 + r.2 - 2)
      (fun r ↦ tailMomentWeight k c r * (35 / 16)) j +
    collectWeight (tailMomentIndices s k) (fun r ↦ k r.1 + r.2 - 2 + 1)
      (fun r ↦ tailMomentWeight k c r * -(((k r.1 + r.2 - 2 : ℕ) : ℚ) + 1)) j

/-- A tail index is in the second-moment support exactly when it is shifted by two. -/
private theorem tail_index_eq (m j : ℕ) : (2 ≤ m ∧ m - 2 = j) ↔ m = j + 2 := by
  constructor
  · rintro ⟨hm, hj⟩
    exact (Nat.sub_add_cancel hm).symm.trans (congrArg (· + 2) hj)
  · rintro rfl
    exact ⟨Nat.le_add_left _ _, Nat.add_sub_cancel _ _⟩

/-- Gather a tail weight directly at the corresponding moment coefficient. -/
private theorem collect_tail_moment {ι : Type*} (s : Finset ι) (k : ι → ℕ) (c : ι → ℚ) (j : ℕ)
    (f : ℕ → ℚ) :
    collectWeight (tailMomentIndices s k) (fun r ↦ k r.1 + r.2 - 2)
        (fun r ↦ tailMomentWeight k c r * f (k r.1 + r.2 - 2)) j =
      momentGramWeight s k c (27 / 16) 0 (j + 2) * f j := by
  have he :
    (tailMomentIndices s k).filter (fun r ↦ k r.1 + r.2 - 2 = j) =
      (s ×ˢ Finset.range 20).filter (fun r ↦ k r.1 + r.2 = j + 2) := by
    rw [tailMomentIndices, Finset.filter_filter]
    apply Finset.filter_congr
    intro r _
    exact tail_index_eq (k r.1 + r.2) j
  rw [collectWeight, he, ← moment_gram_fiber, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r hr
  have hk := (tail_index_eq _ _).mpr (Finset.mem_filter.mp hr).2
  rw [hk.2, tailMomentWeight]

/-- The derivative shifts the gathered moment weight by one degree. -/
private theorem collect_tail_succ {ι : Type*} (s : Finset ι) (k : ι → ℕ) (c : ι → ℚ) (j : ℕ) :
    collectWeight (tailMomentIndices s k) (fun r ↦ k r.1 + r.2 - 2 + 1)
        (fun r ↦ tailMomentWeight k c r * -(((k r.1 + r.2 - 2 : ℕ) : ℚ) + 1)) j =
      (if j = 0 then 0 else momentGramWeight s k c (27 / 16) 0 (j + 1) * -(j : ℚ)) := by
  cases j with
  | zero =>
    simp only [collectWeight, Nat.add_one_ne_zero, Finset.filter_false, Finset.sum_empty,
      ite_eq_left]
  | succ j =>
    have h := collect_tail_moment s k c j (fun u ↦ -((u : ℚ) + 1))
    simp only [collectWeight, Nat.add_right_cancel_iff, Nat.add_one_ne_zero, Nat.cast_add,
      Nat.cast_one] at h ⊢
    exact h

/-- Compute a tail weight with two scalar moment lookups and no filtered product. -/
private def gramTailWeight {ι : Type*} (s : Finset ι) (k : ι → ℕ) (c : ι → ℚ) (j : ℕ) : ℚ :=
  collectWeight (s.filter (fun r ↦ 2 ≤ k r)) (fun r ↦ k r - 2) c j +
    momentGramWeight s k c (27 / 16) 0 (j + 2) * (35 / 16) +
    (if j = 0 then 0 else momentGramWeight s k c (27 / 16) 0 (j + 1) * -(j : ℚ))

/-- The numerical weight agrees with the fixed fibers of the analytic sum. -/
private theorem gram_tail_gather_eq {ι : Type*} (s : Finset ι) (k : ι → ℕ) (c : ι → ℚ) :
    gramTailGather s k c = gramTailWeight s k c := by
  funext j
  unfold gramTailGather gramTailWeight
  rw [collect_tail_moment s k c j (fun _ ↦ 35 / 16), collect_tail_succ]

private def gramTailUpper {ι : Type*} (s : Finset ι) (k : ι → ℕ) (c : ι → ℚ) : ℚ :=
  gramLinearUpper (Finset.range 10) id (gramTailWeight s k c)

private theorem gram_tail_linear_le {ι : Type*} (s : Finset ι) (k : ι → ℕ) (c : ι → ℚ) :
    (∑ r ∈ s, (c r : ℝ) * mainTailCoeff gramFourierCoeff (k r)) ≤ (gramTailUpper s k c : ℝ) := by
  rw [main_tail_linear_eq]
  rw [collect_gram_linear (s.filter (fun r ↦ 2 ≤ k r)), collect_gram_linear (tailMomentIndices s k),
    collect_gram_linear (tailMomentIndices s k)]
  simp only [← Finset.sum_add_distrib, ← add_mul, ← Rat.cast_add]
  change
    (∑ j ∈ Finset.range 10, (gramTailGather s k c j : ℝ) * gramFourierCoeff j) ≤
      (gramTailUpper s k c : ℝ)
  rw [gramTailUpper, ← gram_tail_gather_eq s k c]
  exact gram_fourier_linear_le (Finset.range 10) id (gramTailGather s k c)

private noncomputable def gammaRemainderCoeff (k : ℕ) : ℝ :=
  let g := fun j : ℕ ↦
    (19 / 16 : ℝ) ^ 2 * (inverseCoeff j : ℝ) +
      (2 * (19 / 16 : ℝ)) * ((inverseCoeff (j + 1) : ℝ) * ((j : ℝ) + 1)) +
      ((inverseCoeff (j + 2) : ℝ) * ((j : ℝ) + 2)) * ((j : ℝ) + 1)
  (17 / 10) * momentCoeff g (19 / 16) 0 k + ((5 / 12) / (2 - 19 / 16)) * g k

private theorem coeff_gamma_remainder (k : ℕ) : remainderGamma.coeff k = gammaRemainderCoeff k := by
  simp only [remainderGamma, gammaRemainderCoeff, Polynomial.coeff_add, Polynomial.coeff_C_mul,
    coeff_k131_moment, momentCoeff, Polynomial.coeff_derivative, coeff_inverse, Nat.cast_succ,
    Nat.cast_add, add_assoc, one_add_one_eq_two]

private noncomputable def shiftedRealCoeff (d : ℕ) (c : ℕ → ℝ) (h : ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range d, c j * (h ^ (j - k) * (j.choose k : ℝ))

private theorem coeff_shift_real {P : Polynomial ℝ} {d : ℕ} (hd : P.natDegree < d) {c : ℕ → ℝ}
    (hc : ∀ j, P.coeff j = c j) (h : ℝ) (k : ℕ) :
    (shiftPoly P h).coeff k = shiftedRealCoeff d c h k := by
  simp only [shiftPoly, coeff_translate hd, shiftedRealCoeff, hc]

private def momentRat (c : ℕ → ℚ) (a : ℚ) (k : ℕ) : ℚ :=
  ∑ j ∈ Finset.range 20, momentWeight a 0 k j * c (k + j)

/-- Apply the falling-factorial recurrence to one nonconstant term. -/
private theorem moment_rat_step_term (c : ℕ → ℚ) {a : ℚ} (ha : a ≠ 0) (k j : ℕ) :
    momentWeight a 0 k (j + 1) * c (k + (j + 1)) =
      ((k : ℚ) + 1) / a * (momentWeight a 0 (k + 1) j * c (k + 1 + j)) := by
  have hj : k + (j + 1) = k + 1 + j := (Nat.add_assoc k j 1).symm.trans (Nat.add_right_comm k j 1)
  simp only [momentWeight, ite_true, hj, Nat.descFactorial_succ, Nat.add_sub_cancel, pow_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp [ha]

/-- A supported moment coefficient depends only on the next coefficient. -/
private theorem moment_rat_step (c : ℕ → ℚ) {a : ℚ} (ha : a ≠ 0) (hz : ∀ n, 20 ≤ n → c n = 0)
    (k : ℕ) : momentRat c a k = c k / a + ((k : ℚ) + 1) / a * momentRat c a (k + 1) := by
  have h := hz (k + 1 + 19) (Nat.le_add_left 20 k)
  have hs :
    momentRat c a (k + 1) = ∑ j ∈ Finset.range 19, momentWeight a 0 (k + 1) j * c (k + 1 + j) := by
    rw [momentRat, show 20 = 19 + 1 by rfl, Finset.sum_range_succ, h, mul_zero, add_zero]
  rw [momentRat, show 20 = 19 + 1 by rfl, Finset.sum_range_succ', hs, Finset.mul_sum]
  rw [add_comm]
  congr 1
  · simp only [momentWeight, ite_true, Nat.add_zero, Nat.descFactorial_zero, Nat.cast_one, zero_add,
      pow_one, div_eq_mul_inv, one_mul]
    ring
  · exact Finset.sum_congr rfl (fun j _ ↦ moment_rat_step_term c ha k j)

/-- Compute a suffix of moment coefficients in one backward pass. -/
private def momentSuffix (c : ℕ → ℚ) (a : ℚ) : ℕ → ℕ → List ℚ
  | 0, _ => []
  | n + 1, k =>
    let tail := momentSuffix c a n (k + 1)
    (c k / a + ((k : ℚ) + 1) / a * tail.getD 0 0) :: tail

/-- Moments vanish above the support of their input coefficients. -/
private theorem moment_rat_zero (c : ℕ → ℚ) (a : ℚ) (hz : ∀ n, 20 ≤ n → c n = 0) {k : ℕ}
    (hk : 20 ≤ k) : momentRat c a k = 0 := by
  unfold momentRat
  apply Finset.sum_eq_zero
  intro j _
  rw [hz _ (hk.trans (Nat.le_add_right _ _)), mul_zero]

/-- Every entry of the backward pass is the corresponding finite moment. -/
private theorem moment_suffix_get (c : ℕ → ℚ) {a : ℚ} (ha : a ≠ 0) (hz : ∀ n, 20 ≤ n → c n = 0)
    (n k j : ℕ) (h : 20 ≤ k + n) : (momentSuffix c a n k).getD j 0 = momentRat c a (k + j) := by
  induction n generalizing k j with
  | zero =>
    have hk : 20 ≤ k := by simpa only [Nat.add_zero] using h
    exact (moment_rat_zero c a hz (hk.trans (Nat.le_add_right _ _))).symm
  | succ n
    ih =>
    have h' : 20 ≤ k + 1 + n := by
      rw [Nat.add_right_comm k 1 n, Nat.add_assoc]
      exact h
    cases j with
    | zero =>
      simpa only [momentSuffix, List.getD_cons_zero, Nat.add_zero, ih (k + 1) 0 h'] using
        (moment_rat_step c ha hz k).symm
    | succ
      j =>
      have he : k + (j + 1) = k + 1 + j :=
        (Nat.add_assoc k j 1).symm.trans (Nat.add_right_comm k j 1)
      simpa only [momentSuffix, List.getD_cons_succ, he] using ih (k + 1) j h'

private theorem cast_moment_rat (c : ℕ → ℚ) (a : ℚ) (k : ℕ) :
    (momentRat c a k : ℝ) = momentCoeff (fun j ↦ (c j : ℝ)) (a : ℝ) 0 k := by
  simp only [momentRat, moment_coeff_weights, Rat.cast_sum, Rat.cast_mul]

/-- Read a finite moment from the shared backward row. -/
private def momentRowAt (c : ℕ → ℚ) (a : ℚ) (k : ℕ) : ℚ :=
  (momentSuffix c a 20 0).getD k 0

/-- A supported backward row has the same real coefficients as the analytic moment. -/
private theorem cast_moment_row (c : ℕ → ℚ) {a : ℚ} (ha : a ≠ 0) (hz : ∀ n, 20 ≤ n → c n = 0)
    (k : ℕ) : (momentRowAt c a k : ℝ) = momentCoeff (fun j ↦ (c j : ℝ)) (a : ℝ) 0 k := by
  rw [momentRowAt, moment_suffix_get c ha hz 20 0 k (by decide), Nat.zero_add]
  exact cast_moment_rat c a k

/-- The finite inverse row has no terms above degree 19. -/
private theorem inverse_rat_zero (n : ℕ) (hn : 20 ≤ n) : inverseCoeff n = 0 := by
  unfold inverseCoeff
  apply List.getD_eq_default
  exact hn

/-- The finite Fourier row has no terms above degree 9. -/
private theorem fourier_rat_zero {n : ℕ} (hn : 10 ≤ n) : fourierCoeff n = 0 := by
  unfold fourierCoeff
  apply List.getD_eq_default
  exact hn

/-- Compute the Fourier coefficients entering the first tail moment. -/
private def fourierTailInput (j : ℕ) : ℚ :=
  if j < 2 then 0
  else (35 / 16) * fourierCoeff (j - 2) - fourierCoeff (j - 2 + 1) * ((j - 2 : ℕ) + 1 : ℚ)

/-- The Fourier tail input fits within the backward row. -/
private theorem fourier_tail_input_zero (j : ℕ) (hj : 20 ≤ j) : fourierTailInput j = 0 := by
  have hj' : 10 ≤ j - 2 := Nat.le_sub_of_add_le ((by decide : 10 + 2 ≤ 20).trans hj)
  simp only [fourierTailInput, ite_eq_right (not_lt.mpr ((by decide : 2 ≤ 20).trans hj)),
    fourier_rat_zero hj', fourier_rat_zero (hj'.trans (Nat.le_add_right _ _)), mul_zero, zero_mul,
    sub_zero]

/-- Interpret the Fourier tail moment produced by the backward pass. -/
private theorem cast_fourier_moment (k : ℕ) :
    (momentRowAt fourierTailInput (27 / 16) k : ℝ) =
      momentCoeff (fun j ↦ (fourierTailInput j : ℝ)) ((27 / 16 : ℚ) : ℝ) 0 k :=
  cast_moment_row fourierTailInput (by norm_num only) fourier_tail_input_zero k

private def fourierTailRat (k : ℕ) : ℚ :=
  (if k < 2 then 0 else fourierCoeff (k - 2)) + momentRowAt fourierTailInput (27 / 16) k

private theorem cast_fourier_tail_rat (k : ℕ) :
    (fourierTailRat k : ℝ) = mainTailCoeff (fun j ↦ (fourierCoeff j : ℝ)) k := by
  simp only [fourierTailRat, mainTailCoeff, Rat.cast_add, cast_fourier_moment, fourierTailInput,
    Rat.cast_div, Rat.cast_ofNat]
  congr 1
  · split <;> simp only [Rat.cast_zero]
  · congr 2
    funext j
    split <;>
      simp only [Rat.cast_zero, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat,
        Rat.cast_add, Rat.cast_natCast, Rat.cast_one]

private def gammaInputRat (j : ℕ) : ℚ :=
  (19 / 16 : ℚ) ^ 2 * inverseCoeff j +
    (2 * (19 / 16 : ℚ)) * (inverseCoeff (j + 1) * ((j : ℚ) + 1)) +
    (inverseCoeff (j + 2) * ((j : ℚ) + 2)) * ((j : ℚ) + 1)

/-- Differentiation and scaling preserve the finite support of the inverse row. -/
private theorem gamma_input_zero (j : ℕ) (hj : 20 ≤ j) : gammaInputRat j = 0 := by
  simp only [gammaInputRat, inverse_rat_zero j hj,
    inverse_rat_zero (j + 1) (hj.trans (Nat.le_add_right _ _)),
    inverse_rat_zero (j + 2) (hj.trans (Nat.le_add_right _ _)), mul_zero, zero_mul, add_zero]

/-- Interpret the Gamma remainder moment produced by the backward pass. -/
private theorem cast_gamma_moment (k : ℕ) :
    (momentRowAt gammaInputRat (19 / 16) k : ℝ) =
      momentCoeff (fun j ↦ (gammaInputRat j : ℝ)) ((19 / 16 : ℚ) : ℝ) 0 k :=
  cast_moment_row gammaInputRat (by norm_num only) gamma_input_zero k

/-- Interpret the inverse moment produced by the backward pass. -/
private theorem cast_inverse_moment (k : ℕ) :
    (momentRowAt inverseCoeff (19 / 16) k : ℝ) =
      momentCoeff (fun j ↦ (inverseCoeff j : ℝ)) ((19 / 16 : ℚ) : ℝ) 0 k :=
  cast_moment_row inverseCoeff (by norm_num only) inverse_rat_zero k

private def gammaRemainderRat (k : ℕ) : ℚ :=
  (17 / 10) * momentRowAt gammaInputRat (19 / 16) k + ((5 / 12) / (2 - 19 / 16)) * gammaInputRat k

private theorem cast_gamma_remainder (k : ℕ) :
    (gammaRemainderRat k : ℝ) = gammaRemainderCoeff k := by
  simp only [gammaRemainderRat, gammaRemainderCoeff, Rat.cast_add, Rat.cast_mul, Rat.cast_div,
    Rat.cast_sub, Rat.cast_ofNat, cast_gamma_moment, gammaInputRat, Rat.cast_pow, Rat.cast_natCast,
    Rat.cast_one]

private theorem cast_shifted_coeff (d : ℕ) (c : ℕ → ℚ) (h : ℚ) (k : ℕ) :
    (shiftedCoeff d c h k : ℝ) = shiftedRealCoeff d (fun j ↦ (c j : ℝ)) (h : ℝ) k := by
  simp only [shifted_coeff_eq_sum, shiftedRealCoeff, Rat.cast_sum, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_natCast]

private def poly27PrefFormula (k : ℕ) : ℚ :=
  let s : ℚ := 519674 / 1000000
  let t : ℚ := 123 / 10
  let h : ℚ := 9 / 4
  let cR : ℚ := 486361785475175632772883470102367621 / 1000000000000000000000000000000000000
  (-2 * t / s + cR) * shiftedCoeff 20 inverseCoeff h k -
    3 *
      (shiftedCoeff 20 (momentRowAt inverseCoeff (19 / 16)) h k +
        shiftedCoeff 20 gammaRemainderRat h k)

private def poly27PrefCoeff (k : ℕ) : ℚ :=
  ([-240643537688418040307820478936844499523412060710033478743501422151577197393112163446365706729607 /
            1216379664886200144397119394821108785756310522036224000000000000000000000000000000000000000,
          -3766043724199305151295290243957552821878191110989568485728802694396017492247240251877874833679 /
            16004995590607896636804202563435641917846191079424000000000000000000000000000000000000000,
          -12118982283787309790289179370200261455749121272514556697803653073260968773690968785648842339 /
            86714372394934424502809147015518183765420539904000000000000000000000000000000000000000,
          -62833660476701921446716187099970630241597084141023140803906659574410156977838668890857107 /
            1140978584143874006615909829151555049545007104000000000000000000000000000000000000000,
          -16488365155577249673244448047583170383422727103255053348842656208335774561909239908321 /
            1023605189124288881533411928066586467893248000000000000000000000000000000000000000,
          -14112488852068956573266698815251948186351783038994853581620985746344154454360407493 /
            3798804682984877765474875576495428861952000000000000000000000000000000000000000,
          -84217047893781397109538320110491944902423087921225498193325778491424748413369583 /
            119350200834916943759548990990860681216000000000000000000000000000000000000000,
          -97230952846840491650913746229552869001651215437657784652174016005061556608717 /
            845598588911354864693160867344154624000000000000000000000000000000000000000,
          -123001642543692210972053792228850923805684209254176027895629920427648717799 /
            7417531481678551444676849713545216000000000000000000000000000000000000000,
          -90876619313000602783241906382546137360726400768583643391368176425875711 /
            42998204209215011134950453805056000000000000000000000000000000000000000,
          -1700218124265225699058783605625308957084711074734016356242946814589017 /
            7354955983155199273083630256128000000000000000000000000000000000000000,
          -22959758016969728833153284517797571481253473547827208944976546676579 /
            1064533102825094631630525431808000000000000000000000000000000000000000,
          -4062595664226483306545086740218674856198249616589370340529951649 /
            2334502418476084718487994368000000000000000000000000000000000000000,
          -3130812971764955138886959070006148047615207440923134084098767 /
            24448333598433755107688448000000000000000000000000000000000000000,
          -20979105652085766227817898591227199639287731362152290395591 /
            2251820199855740602023936000000000000000000000000000000000000000,
          -5418178939716165133292571574465480727832269268530111519 /
            8080694497089978236928000000000000000000000000000000000000000,
          -147983080369256405073802449438561658236219579529047281 /
            3638675299859229966336000000000000000000000000000000000000000,
          -1597101776121821408052343108854641968260906663772537 /
            813914211810617229312000000000000000000000000000000000000000,
          -56538879924050959577809267710504007078397762527 /
            823799809524916224000000000000000000000000000000000000000,
          -217467550134662013935851558388906808400127593 /
            157491140056233984000000000000000000000000000000000000000] :
        List ℚ).getD
    k 0

private theorem poly27_pref_small (k : Fin 20) :
    poly27PrefCoeff k.val = poly27PrefFormula k.val := by fin_cases k <;> decide +kernel

private theorem poly27_pref_eq (k : ℕ) : poly27PrefCoeff k = poly27PrefFormula k := by
  by_cases hk : k < 20
  · exact poly27_pref_small ⟨k, hk⟩
  · have hs : Finset.Ico k 20 = ∅ := Finset.Ico_eq_empty_of_le (Nat.le_of_not_gt hk)
    have hz : poly27PrefCoeff k = 0 := by
      unfold poly27PrefCoeff
      apply List.getD_eq_default
      exact Nat.le_of_not_gt hk
    rw [hz]
    simp only [poly27PrefFormula, shiftedCoeff, hs, Finset.sum_empty, mul_zero, add_zero, sub_zero]

private noncomputable def poly27Coeff (k : ℕ) : ℝ :=
  let s : ℝ := 519674 / 1000000
  let t : ℝ := 123 / 10
  let h : ℝ := 9 / 4
  let cR : ℝ := 486361785475175632772883470102367621 / 1000000000000000000000000000000000000
  (-2 * t * k131Prefactor / s) * (shiftedCoeff 20 inverseCoeff (9 / 4) k : ℝ) +
          (-2 * t * (gaussianK131Amplitude : ℝ) / s) * shiftedInverseCoeff k -
        (1 / 6) *
          (mainTailCoeff (fun j ↦ (fourierCoeff j : ℝ)) k + mainTailCoeff gramFourierCoeff k) -
        (3 * k131Prefactor) *
          shiftedRealCoeff 20 (momentCoeff (fun j ↦ (inverseCoeff j : ℝ)) (19 / 16) 0) h k +
      (cR * k131Prefactor) * (shiftedCoeff 20 inverseCoeff (9 / 4) k : ℝ) -
    (3 * k131Prefactor) * shiftedRealCoeff 20 gammaRemainderCoeff h k

private theorem coeff_k131_poly27 (k : ℕ) : gaussianK131Poly27.coeff k = poly27Coeff k := by
  have h : (9 / 4 : ℝ) = ((9 / 4 : ℚ) : ℝ) := by norm_num only [Rat.cast_div, Rat.cast_ofNat]
  have hm :=
    coeff_shift_real (Nat.lt_succ_of_le (degree_moment inverse_degree_le (19 / 16) 0))
      (coeff_moment_from coeff_inverse (19 / 16) 0) ((9 / 4 : ℚ) : ℝ) k
  have hg :=
    coeff_shift_real (Nat.lt_succ_of_le degree_remainder_gamma) coeff_gamma_remainder
      ((9 / 4 : ℚ) : ℝ) k
  simp only [gaussianK131Poly27, poly27Coeff, Polynomial.coeff_add, Polynomial.coeff_sub,
    Polynomial.coeff_C_mul, hm, hg, coeff_main_tail coeff_fourier,
    coeff_main_tail coeff_gram_fourier, h, coeff_shift_inverse, coeff_shifted_inverse]

private def poly27InvScale : ℚ :=
  -2 * (123 / 10) * gaussianK131Amplitude / (519674 / 1000000)

private theorem coeff_poly27_split (k : ℕ) :
    gaussianK131Poly27.coeff k =
      k131Prefactor * (poly27PrefCoeff k : ℝ) + (poly27InvScale : ℝ) * shiftedInverseCoeff k -
        (1 / 6) *
          (mainTailCoeff (fun j ↦ (fourierCoeff j : ℝ)) k + mainTailCoeff gramFourierCoeff k) := by
  rw [coeff_k131_poly27]
  simp only [poly27Coeff, poly27_pref_eq, poly27PrefFormula, poly27InvScale, Rat.cast_sub,
    Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat]
  simp only [cast_shifted_coeff, cast_inverse_moment, cast_gamma_remainder, Rat.cast_div,
    Rat.cast_ofNat]
  ring

private theorem coeff_poly27_tail (k : ℕ) (hk : 12 ≤ k) :
    gaussianK131Poly27.coeff k =
      k131Prefactor * (poly27PrefCoeff k : ℝ) + (poly27InvScale : ℝ) * shiftedInverseCoeff k := by
  have hf :=
    Polynomial.coeff_eq_zero_of_natDegree_lt ((degree_main_tail degree_fourier).trans_lt hk)
  have hg :=
    Polynomial.coeff_eq_zero_of_natDegree_lt ((degree_main_tail degree_gram_fourier).trans_lt hk)
  rw [coeff_main_tail coeff_fourier] at hf
  rw [coeff_main_tail coeff_gram_fourier] at hg
  rw [coeff_poly27_split, hf, hg, add_zero, mul_zero, sub_zero]

private def poly27TailUpper {ι : Type*} (s : Finset ι) (k : ι → ℕ) (c : ι → ℚ) : ℚ :=
  prefactorLinearUpper (∑ r ∈ s, c r * poly27PrefCoeff (k r)) +
    inverseLinearUpper s k (fun r ↦ c r * poly27InvScale)

private theorem poly27_tail_le {ι : Type*} (s : Finset ι) (k : ι → ℕ) (c : ι → ℚ)
    (hk : ∀ r ∈ s, 12 ≤ k r) :
    (∑ r ∈ s, (c r : ℝ) * gaussianK131Poly27.coeff (k r)) ≤ (poly27TailUpper s k c : ℝ) := by
  have h₁ := prefactor_linear_le (∑ r ∈ s, c r * poly27PrefCoeff (k r))
  have h₂ := inverse_linear_le s k (fun r ↦ c r * poly27InvScale)
  simp only [poly27TailUpper, Rat.cast_add]
  refine le_trans ?_ (add_le_add h₁ h₂)
  apply le_of_eq
  simp only [Rat.cast_sum, Rat.cast_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  rw [coeff_poly27_tail _ (hk r hr)]
  ring

private def poly27LinearUpper {ι : Type*} (s : Finset ι) (k : ι → ℕ) (c : ι → ℚ) : ℚ :=
  poly27TailUpper s k c + (∑ r ∈ s, (c r * (-1 / 6)) * fourierTailRat (k r)) +
    gramTailUpper s k (fun r ↦ c r * (-1 / 6))

private theorem poly27_linear_le {ι : Type*} (s : Finset ι) (k : ι → ℕ) (c : ι → ℚ) :
    (∑ r ∈ s, (c r : ℝ) * gaussianK131Poly27.coeff (k r)) ≤ (poly27LinearUpper s k c : ℝ) := by
  have h₁ := prefactor_linear_le (∑ r ∈ s, c r * poly27PrefCoeff (k r))
  have h₂ := inverse_linear_le s k (fun r ↦ c r * poly27InvScale)
  have hg := gram_tail_linear_le s k (fun r ↦ c r * (-1 / 6))
  simp only [poly27LinearUpper, poly27TailUpper, Rat.cast_add]
  refine le_trans ?_ (add_le_add (add_le_add (add_le_add h₁ h₂) (le_refl _)) hg)
  apply le_of_eq
  simp only [coeff_poly27_split, Rat.cast_sum, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
    Rat.cast_one, Rat.cast_ofNat, cast_fourier_tail_rat, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  ring

private def secondaryTailUpper (k : ℕ) : ℚ :=
  let s := Finset.Ico k 20 ×ˢ (Finset.univ : Finset (Fin 3))
  let index := fun r : ℕ × Fin 3 ↦ r.1 + r.2.val
  let weight := fun r : ℕ × Fin 3 ↦ translatedWeight r.1 k * curvatureWeight (27 / 8) r.1 r.2
  if 12 ≤ k then poly27TailUpper s index weight else poly27LinearUpper s index weight

private theorem secondary_linear_le (k : ℕ) :
    (∑ r ∈ Finset.Ico k 20 ×ˢ (Finset.univ : Finset (Fin 3)),
        ((translatedWeight r.1 k * curvatureWeight (27 / 8) r.1 r.2 : ℚ) : ℝ) *
          gaussianK131Poly27.coeff (r.1 + r.2.val)) ≤
      (secondaryTailUpper k : ℝ) := by
  unfold secondaryTailUpper
  split
  · rename_i hk
    apply poly27_tail_le
    intro r hr
    exact hk.trans ((Finset.mem_Ico.mp (Finset.mem_product.mp hr).1).1.trans (Nat.le_add_right _ _))
  · exact poly27_linear_le _ _ _

private theorem coeff_secondary_upper (k : ℕ) :
    ((logPowerCurvature (27 / 8) gaussianK131Poly27).comp
            (Polynomial.C 14 + Polynomial.C 3 * Polynomial.X)).coeff
        k ≤
      (secondaryTailUpper k : ℝ) := by
  rw [coeff_k131_secondary_normalized]
  have hs :
    ∀ f : ℕ → ℝ,
      (∑ j ∈ Finset.Ico k 20, f j * (14 ^ (j - k) * (j.choose k : ℝ))) =
        ∑ j ∈ Finset.range 20, f j * (14 ^ (j - k) * (j.choose k : ℝ)) := by
    intro f
    apply Finset.sum_subset (fun j hj ↦ Finset.mem_range.mpr (Finset.mem_Ico.mp hj).2)
    intro j hj hn
    have hjk : j < k :=
      Nat.lt_of_not_ge fun hle ↦ hn (Finset.mem_Ico.mpr ⟨hle, Finset.mem_range.mp hj⟩)
    rw [Nat.choose_eq_zero_of_lt hjk, Nat.cast_zero, mul_zero, mul_zero]
  rw [← hs]
  refine le_trans ?_ (secondary_linear_le k)
  apply le_of_eq
  have hp : (27 / 8 : ℝ) = ((27 / 8 : ℚ) : ℝ) := by norm_num only [Rat.cast_div, Rat.cast_ofNat]
  simp only [hp, coeff_curvature_sum]
  simp only [Finset.sum_product, Finset.sum_mul, translatedWeight, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_natCast, Rat.cast_ofNat]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro r _
  ring

private theorem secondary_tail_0 : secondaryTailUpper 0 ≤ 0 := by decide +kernel

private theorem secondary_tail_1 : secondaryTailUpper 1 ≤ 0 := by decide +kernel

private theorem secondary_tail_2 : secondaryTailUpper 2 ≤ 0 := by decide +kernel

private theorem secondary_tail_3 : secondaryTailUpper 3 ≤ 0 := by decide +kernel

private theorem secondary_tail_4 : secondaryTailUpper 4 ≤ 0 := by decide +kernel

private theorem secondary_tail_5 : secondaryTailUpper 5 ≤ 0 := by decide +kernel

private theorem secondary_tail_6 : secondaryTailUpper 6 ≤ 0 := by decide +kernel

private theorem secondary_tail_7 : secondaryTailUpper 7 ≤ 0 := by decide +kernel

private theorem secondary_tail_8 : secondaryTailUpper 8 ≤ 0 := by decide +kernel

private theorem secondary_tail_9 : secondaryTailUpper 9 ≤ 0 := by decide +kernel

private theorem secondary_tail_10 : secondaryTailUpper 10 ≤ 0 := by decide +kernel

private theorem secondary_tail_11 : secondaryTailUpper 11 ≤ 0 := by decide +kernel

private theorem secondary_lower_nonpos (k : Fin 12) : secondaryTailUpper k.val ≤ 0 := by
  fin_cases k
  · exact secondary_tail_0
  · exact secondary_tail_1
  · exact secondary_tail_2
  · exact secondary_tail_3
  · exact secondary_tail_4
  · exact secondary_tail_5
  · exact secondary_tail_6
  · exact secondary_tail_7
  · exact secondary_tail_8
  · exact secondary_tail_9
  · exact secondary_tail_10
  · exact secondary_tail_11

private theorem secondary_tail_12 : secondaryTailUpper 12 ≤ 0 := by decide +kernel

private theorem secondary_tail_13 : secondaryTailUpper 13 ≤ 0 := by decide +kernel

private theorem secondary_tail_14 : secondaryTailUpper 14 ≤ 0 := by decide +kernel

private theorem secondary_tail_15 : secondaryTailUpper 15 ≤ 0 := by decide +kernel

private theorem secondary_tail_16 : secondaryTailUpper 16 ≤ 0 := by decide +kernel

private theorem secondary_tail_17 : secondaryTailUpper 17 ≤ 0 := by decide +kernel

private theorem secondary_tail_18 : secondaryTailUpper 18 ≤ 0 := by decide +kernel

private theorem secondary_tail_19 : secondaryTailUpper 19 ≤ 0 := by decide +kernel

private theorem secondary_tail_nonpos (k : Fin 8) : secondaryTailUpper (12 + k.val) ≤ 0 := by
  fin_cases k
  · exact secondary_tail_12
  · exact secondary_tail_13
  · exact secondary_tail_14
  · exact secondary_tail_15
  · exact secondary_tail_16
  · exact secondary_tail_17
  · exact secondary_tail_18
  · exact secondary_tail_19

private theorem coeff_secondary_high_nonpos (k : Fin 20) (hk : 12 ≤ k.val) :
    ((logPowerCurvature (27 / 8) gaussianK131Poly27).comp
            (Polynomial.C 14 + Polynomial.C 3 * Polynomial.X)).coeff
        k.val ≤
      0 := by
  let j : Fin 8 := ⟨k.val - 12, Nat.sub_lt_left_of_lt_add hk k.isLt⟩
  have he : 12 + j.val = k.val := Nat.add_sub_of_le hk
  have h := secondary_tail_nonpos j
  rw [he] at h
  exact (coeff_secondary_upper k.val).trans ((Rat.cast_nonpos (K := ℝ)).mpr h)

private theorem coeff_secondary_from_main (k : ℕ) :
    ((logPowerCurvature (27 / 8) gaussianK131Poly27).comp
            (Polynomial.C 14 + Polynomial.C 3 * Polynomial.X)).coeff
        k =
      (∑ j ∈ Finset.range 20,
          ((27 / 8 * (27 / 8 + 1)) * poly27Coeff j -
                (2 * (2 * (27 / 8) + 1)) * (poly27Coeff (j + 1) * ((j : ℝ) + 1)) +
              4 * ((poly27Coeff (j + 2) * ((j : ℝ) + 2)) * ((j : ℝ) + 1))) *
            ((14 : ℝ) ^ (j - k) * (j.choose k : ℝ))) *
        3 ^ k := by
  simp only [coeff_k131_secondary_normalized, coeff_log_power_curvature, coeff_k131_poly27]

/-- The two coefficient checks for the remaining K131 curvature signs.
The normalized power coefficients must admit rational upper bounds whose
Bernstein transform passes the selected certificate row. -/
def K131CoeffCheck (i : Fin 5) (a b : ℝ) (P : Polynomial ℝ) : Prop :=
  ∃ A : Fin (k131BernsteinDegree i + 1) → ℚ,
    (∀ j, (P.comp (Polynomial.C a + Polynomial.C (b - a) * Polynomial.X)).coeff j.val ≤ (A j : ℝ)) ∧
      ∀ k,
        (∑ j : Fin (k131BernsteinDegree i + 1),
            A j * ((k.val.choose j.val : ℚ) / ((k131BernsteinDegree i).choose j.val : ℚ))) ≤
          k131BernsteinUpper i k

/-- A direct Bernstein comparison with the selected rational row, with the
normalized power coefficients taken from the polynomial itself. -/
def K131BernsteinCheck (i : Fin 5) (a b : ℝ) (P : Polynomial ℝ) : Prop :=
  ∀ k : Fin (k131BernsteinDegree i + 1),
    (∑ j : Fin (k131BernsteinDegree i + 1),
        (P.comp (Polynomial.C a + Polynomial.C (b - a) * Polynomial.X)).coeff j.val *
          ((k.val.choose j.val : ℝ) / ((k131BernsteinDegree i).choose j.val : ℝ))) ≤
      (k131BernsteinUpper i k : ℝ)

/-- Componentwise power upper bounds also certify the direct Bernstein comparison. -/
theorem K131CoeffCheck.toBernstein {i : Fin 5} {a b : ℝ} {P : Polynomial ℝ}
    (h : K131CoeffCheck i a b P) : K131BernsteinCheck i a b P := by
  obtain ⟨A, hA, hcheck⟩ := h
  intro k
  apply (bernstein_transform_mono hA k).trans
  simpa only [Rat.cast_sum, Rat.cast_mul, Rat.cast_div, Rat.cast_natCast] using
    (Rat.cast_le (K := ℝ)).mpr (hcheck k)

/-- A rational affine decomposition of normalized power coefficients
reduces the direct check to a rational comparison for each Bernstein index. -/
theorem k131_bernstein_check_of_affine {ι : Type*} (s : Finset ι) (i : Fin 5) (a b : ℝ)
    (P : Polynomial ℝ) (c : ι → Fin (k131BernsteinDegree i + 1) → ℚ) (lo hi : ι → ℚ) (w : ι → ℝ)
    (hw : ∀ r ∈ s, (lo r : ℝ) ≤ w r ∧ w r ≤ (hi r : ℝ))
    (hc :
      ∀ j : Fin (k131BernsteinDegree i + 1),
        (P.comp (Polynomial.C a + Polynomial.C (b - a) * Polynomial.X)).coeff j.val =
          ∑ r ∈ s, w r * (c r j : ℝ))
    (hcheck :
      ∀ k : Fin (k131BernsteinDegree i + 1),
        (∑ r ∈ s,
            let v :=
              ∑ j : Fin (k131BernsteinDegree i + 1),
                c r j * ((k.val.choose j.val : ℚ) / ((k131BernsteinDegree i).choose j.val : ℚ))
            max (lo r * v) (hi r * v)) ≤
          k131BernsteinUpper i k) :
    K131BernsteinCheck i a b P := by
  intro k
  simp only [hc]
  exact
    (bernstein_affine_le s (k131BernsteinDegree i) c lo hi w hw k).trans
      ((Rat.cast_le (K := ℝ)).mpr (hcheck k))

/-- The dominant row is certified by rational comparisons using the
explicit upper bounds on its twenty normalized power coefficients. -/
private theorem k131_dominant_check_of_rational
    (hc :
      ∀ k : Fin 20,
        (∑ j : Fin 20,
            dominantCoeffUpper j.val * ((k.val.choose j.val : ℚ) / ((19 : ℕ).choose j.val : ℚ))) ≤
          k131BernsteinUpper 0 k) :
    K131BernsteinCheck 0 0 3 k131DominantCheckPoly := by
  apply K131CoeffCheck.toBernstein
  refine ⟨fun j ↦ dominantCoeffUpper j.val, ?_, hc⟩
  intro j
  rw [sub_zero]
  exact coeff_dominant_le j.val

private def dominantRoundedUpper (k : Fin 20) : ℚ :=
  ![-12365715, -45091596, -87223840, -112808674, -101942679, -64050182, -26940122, -6594133,
      -184739, 565719, 284018, 106973, 43411, 17935, 6469, 1943, 494, 138, 0, 0]
    k

/-- The constant upper bound absorbs the sum of all positive higher upper bounds. -/
private theorem dominant_rounded_sum_neg :
    dominantRoundedUpper 0 + (∑ j : Fin 19, max 0 (dominantRoundedUpper j.succ)) < 0 := by
  decide +kernel

private theorem dominant_rounded_hi_index (k : Fin 10) :
    dominantCoeffUpper (10 + k.val) ≤ dominantRoundedUpper (Fin.natAdd 10 k) := by
  fin_cases k <;> decide +kernel

private theorem dominant_rounded_high (k : Fin 20) (hk : 10 ≤ k.val) :
    dominantCoeffUpper k.val ≤ dominantRoundedUpper k := by
  let j : Fin 10 := ⟨k.val - 10, Nat.sub_lt_left_of_lt_add hk k.isLt⟩
  have he : Fin.natAdd 10 j = k := Fin.ext (Nat.add_sub_of_le hk)
  have h := dominant_rounded_hi_index j
  change dominantCoeffUpper (Fin.natAdd 10 j).val ≤ dominantRoundedUpper (Fin.natAdd 10 j) at h
  exact he ▸ h

/-- On the unit interval, each higher power is between zero and one. -/
private theorem power_sum_le {n : ℕ} {c a : Fin (n + 1) → ℝ} {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hc : ∀ i, c i ≤ a i) :
    (∑ i : Fin (n + 1), c i * t ^ i.val) ≤ a 0 + ∑ i : Fin n, max 0 (a i.succ) := by
  rw [Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one]
  apply add_le_add (hc 0)
  apply Finset.sum_le_sum
  intro i _
  exact
    (mul_le_mul_of_nonneg_right ((hc i.succ).trans (le_max_right _ _)) (pow_nonneg ht.1 _)).trans
      (mul_le_of_le_one_right (le_max_left _ _) (pow_le_one₀ ht.1 ht.2))

private theorem dominant_round_0 : dominantCoeffUpper 0 ≤ dominantRoundedUpper 0 := by
  decide +kernel

private theorem dominant_round_1 : dominantCoeffUpper 1 ≤ dominantRoundedUpper 1 := by
  decide +kernel

private theorem dominant_round_2 : dominantCoeffUpper 2 ≤ dominantRoundedUpper 2 := by
  decide +kernel

private theorem dominant_round_3 : dominantCoeffUpper 3 ≤ dominantRoundedUpper 3 := by
  decide +kernel

private theorem dominant_round_4 : dominantCoeffUpper 4 ≤ dominantRoundedUpper 4 := by
  decide +kernel

private theorem dominant_round_5 : dominantCoeffUpper 5 ≤ dominantRoundedUpper 5 := by
  decide +kernel

private theorem dominant_round_6 : dominantCoeffUpper 6 ≤ dominantRoundedUpper 6 := by
  decide +kernel

private theorem dominant_round_7 : dominantCoeffUpper 7 ≤ dominantRoundedUpper 7 := by
  decide +kernel

private theorem dominant_round_8 : dominantCoeffUpper 8 ≤ dominantRoundedUpper 8 := by
  decide +kernel

private theorem dominant_round_9 : dominantCoeffUpper 9 ≤ dominantRoundedUpper 9 := by
  decide +kernel

private theorem dominant_rounded_low (k : Fin 10) :
    dominantCoeffUpper k.val ≤ dominantRoundedUpper (Fin.castLE (by decide : 10 ≤ 20) k) := by
  fin_cases k
  · exact dominant_round_0
  · exact dominant_round_1
  · exact dominant_round_2
  · exact dominant_round_3
  · exact dominant_round_4
  · exact dominant_round_5
  · exact dominant_round_6
  · exact dominant_round_7
  · exact dominant_round_8
  · exact dominant_round_9

/-- The dominant K131 curvature polynomial, including its exponential
majorant, is negative throughout the normalized logarithmic interval. -/
theorem k131_dominant_negative {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 3) :
    k131DominantCheckPoly.eval x < 0 := by
  let Q := k131DominantCheckPoly.comp (Polynomial.C 0 + Polynomial.C 3 * Polynomial.X)
  have hd : Q.natDegree ≤ 19 := by
    apply degree_comp_affine degree_dominant_check
    rw [map_zero, zero_add]
    exact degree_mul_C Polynomial.natDegree_X_le _
  have hall (j : Fin 20) : dominantCoeffUpper j.val ≤ dominantRoundedUpper j := by
    by_cases hj : j.val < 10
    · exact dominant_rounded_low ⟨j.val, hj⟩
    · exact dominant_rounded_high j (Nat.le_of_not_gt hj)
  let t := x / 3
  have ht : t ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hx.1 (by norm_num only), (div_le_one (by norm_num only)).mpr hx.2⟩
  have hxt : 3 * t = x := by
    dsimp only [t]
    ring
  have he : Q.eval t = k131DominantCheckPoly.eval x := by
    simp only [Q, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, zero_add, hxt]
  rw [← he, coeff_eval_fin Q hd]
  refine
    (power_sum_le ht
          (fun j ↦ (coeff_dominant_le j.val).trans ((Rat.cast_le (K := ℝ)).mpr (hall j)))).trans_lt
      ?_
  simpa only [Rat.cast_add, Rat.cast_sum, Rat.cast_max, Rat.cast_zero] using
    (Rat.cast_lt (K := ℝ)).mpr dominant_rounded_sum_neg

private theorem bernstein_check_sound {i : Fin 5} {a b x : ℝ} {P : Polynomial ℝ}
    (h : K131BernsteinCheck i a b P) (hab : a < b) (hx : x ∈ Set.Icc a b)
    (hd : P.natDegree ≤ k131BernsteinDegree i) : P.eval x < 0 := by
  let Q := P.comp (Polynomial.C a + Polynomial.C (b - a) * Polynomial.X)
  have h_aff :
    (Polynomial.C a + Polynomial.C (b - a) * Polynomial.X : Polynomial ℝ).natDegree ≤ 1 := by
    apply Polynomial.natDegree_add_le_of_degree_le _ (degree_mul_C Polynomial.natDegree_X_le _)
    rw [Polynomial.natDegree_C]
    exact Nat.zero_le _
  apply k131_power_interval_neg i hab hx (fun t ↦ P.eval t) (fun j ↦ Q.coeff j.val) h
  intro t
  simpa only [Q, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X] using coeff_eval_fin Q (degree_comp_affine hd h_aff) (t : ℝ)

/-- The certificate can be supplied directly from upper bounds on finite
binomial sums in the original power basis. -/
theorem k131_coeff_check_of_power {i : Fin 5} {a b : ℝ} {P : Polynomial ℝ}
    (hd : P.natDegree ≤ k131BernsteinDegree i) (A : Fin (k131BernsteinDegree i + 1) → ℚ)
    (hA :
      ∀ k : Fin (k131BernsteinDegree i + 1),
        (∑ j ∈ Finset.range (k131BernsteinDegree i + 1),
              P.coeff j * (a ^ (j - k.val) * (j.choose k.val : ℝ))) *
            (b - a) ^ k.val ≤
          (A k : ℝ))
    (hB :
      ∀ k,
        (∑ j : Fin (k131BernsteinDegree i + 1),
            A j * ((k.val.choose j.val : ℚ) / ((k131BernsteinDegree i).choose j.val : ℚ))) ≤
          k131BernsteinUpper i k) :
    K131CoeffCheck i a b P := by
  refine ⟨A, fun k ↦ ?_, hB⟩
  rw [coeff_affine_variable (Nat.lt_succ_of_le hd)]
  exact hA k

private noncomputable def secondaryNormalized : Polynomial ℝ :=
  (logPowerCurvature (27 / 8) gaussianK131Poly27).comp
    (Polynomial.C 14 + Polynomial.C 3 * Polynomial.X)

private theorem secondary_normalized_degree : secondaryNormalized.natDegree ≤ 19 := by
  unfold secondaryNormalized
  apply degree_comp_affine (degree_curvature gaussian_k131_poly27_degree _)
  apply Polynomial.natDegree_add_le_of_degree_le _ (degree_mul_C Polynomial.natDegree_X_le _)
  rw [Polynomial.natDegree_C]
  exact Nat.zero_le _

private theorem secondary_eval_nonpos {x : ℝ} (hx : x ∈ Set.Icc 14 17) :
    (logPowerCurvature (27 / 8) gaussianK131Poly27).eval x ≤ 0 := by
  let t := (x - 14) / 3
  have ht : 0 ≤ t := div_nonneg (sub_nonneg.mpr hx.1) (by norm_num only)
  have he : 14 + 3 * t = x := by
    dsimp only [t]; ring
  have hr :
    secondaryNormalized.eval t = (logPowerCurvature (27 / 8) gaussianK131Poly27).eval x := by
    simp only [secondaryNormalized, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, he]
  rw [← hr, coeff_eval_fin secondaryNormalized secondary_normalized_degree]
  apply Finset.sum_nonpos
  intro k _
  apply mul_nonpos_of_nonpos_of_nonneg _ (pow_nonneg ht _)
  by_cases hk : k.val < 12
  · exact
      (coeff_secondary_upper k.val).trans
        ((Rat.cast_nonpos (K := ℝ)).mpr (secondary_lower_nonpos ⟨k.val, hk⟩))
  · exact coeff_secondary_high_nonpos k (Nat.le_of_not_gt hk)

/-- The K131 gap exceeds 1/200 throughout the affine bridge given the two
endpoint comparisons. Both main curvature signs are certified here. -/
theorem gaussian_k131_gap_of_endpoints {L : ℝ} (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000)
    (hleft : 1 / 200 < gaussianK131Gap (465644807 / 400000))
    (hright : 1 / 200 < gaussianK131Gap (1036273 / 250)) :
    1 / 200 < gaussianK131Gap (gaussianBridgeScale L) := by
  apply gaussian_k131_gap_of_main_signs hL _ hleft hright
  intro y hy
  let t := (y + 123 / 10) / (519674 / 1000000 : ℝ)
  have ht : t ∈ Set.Icc (9055 / 4 : ℝ) 8000 := by
    dsimp only [t]
    exact ⟨by linarith only [hy.1], by linarith only [hy.2]⟩
  have he : gaussianBridgeScale t = y := by
    dsimp only [gaussianBridgeScale, t]; ring
  have hlog := he ▸ k131_radius_log_mem ht
  have hp := (by norm_num only : (0 : ℝ) < 465644807 / 400000).trans hy.1
  have hu : 2 * Real.log y - 14 ∈ Set.Icc (0 : ℝ) 3 :=
    ⟨by linarith only [hlog.1], by linarith only [hlog.2]⟩
  refine ⟨(k131_dominant_check_sound hp hlog (k131_dominant_negative hu).le).le, ?_⟩
  unfold logPowerPoly
  exact mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg hp.le _) (secondary_eval_nonpos hlog)

end PseudoPrime.PrimeTestBounds.MillerRabin
