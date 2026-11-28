/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddlePoleRows
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddlePrincipalAbel
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK141LowerCharge
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK156LowerCharge
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleEulerLower
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianGammaCoefficients
public import PseudoPrime.LLS.PaperStatements.ShiftedPoleArithmetic
import PseudoPrime.LLS.PaperStatements.GammaReflectedEulerIntegral
import PseudoPrime.LLS.PaperStatements.ResolventLaplaceWeights
import PseudoPrime.LLS.PaperStatements.ReciprocalGapReflectedDigamma
import PseudoPrime.LLS.PaperStatements.ShiftedPoleExplicitFormula
import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticTripleConductors
import all PseudoPrime.LLS.PaperStatements.ShiftedPoleArithmetic
import all PseudoPrime.LLS.PaperStatements.ShiftedPoleKernel

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleGammaBounds

/-! # Identification of the middle contour polynomial -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The contour uses only log powers at least three. The omitted coefficients
are zero by the degree bound on the squared numerator. -/
public theorem middle_pole_contour_poly (Q : Polynomial ℚ) {N : ℕ} (hQ : 2 * Q.natDegree + 3 ≤ N)
    (z : ℝ) :
    LLS.PaperStatements.shiftedPolePolynomial (Finset.Ico 3 (N + 1)) (fun i ↦ max 1 i)
        (fun i ↦ (((Q ^ 2).coeff (N - i) : ℚ) : ℂ)) z =
      (((middlePoleProfile N Q).eval₂ (Rat.castHom ℝ) z : ℝ) : ℂ) := by
  simp only [LLS.PaperStatements.shiftedPolePolynomial, middlePoleProfile,
    Polynomial.eval₂_finsetSum, Polynomial.eval₂_monomial, Rat.coe_castHom, Rat.cast_div,
    Rat.cast_natCast, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_natCast, Complex.ofReal_pow, Complex.ofReal_ratCast]
  have hs : Finset.Ico 3 (N + 1) ⊆ Finset.range (N + 1) := fun i hi ↦
    Finset.mem_range.mpr (Finset.mem_Ico.mp hi).2
  rw [← Finset.sum_subset hs]
  · apply Finset.sum_congr rfl
    intro i hi
    have h1 : 1 ≤ i := (by decide : (1 : ℕ) ≤ 3).trans (Finset.mem_Ico.mp hi).1
    rw [max_eq_right h1, div_mul_eq_mul_div]
  · intro i hi hnot
    have hi3 : i < 3 := lt_of_not_ge (fun h ↦ hnot (Finset.mem_Ico.mpr ⟨h, Finset.mem_range.mp hi⟩))
    have hd := Polynomial.natDegree_pow_le (p := Q) (n := 2)
    have he : (Q ^ 2).natDegree < N - i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt he, Rat.cast_zero, zero_div, zero_mul]

/-- After division by the square root, the shifted-pole factor gives the
physical principal weight on every positive index. -/
private theorem middle_contour_scale {t a b x : ℝ} (ht : 0 < t) :
    (t / Real.exp x * Real.exp (-b)) ^ a / Real.sqrt t =
      Real.exp (-a * (x + b)) * t ^ (a - 1 / 2) := by
  have h : t / Real.exp x * Real.exp (-b) = t * Real.exp (-(x + b)) := by
    rw [div_eq_mul_inv, ← Real.exp_neg, mul_assoc, ← Real.exp_add, neg_add]
  rw [h, Real.mul_rpow ht.le (Real.exp_nonneg _), ← Real.exp_mul, mul_comm (t ^ a), mul_div_assoc,
    Real.sqrt_eq_rpow, ← Real.rpow_sub ht, show -(x + b) * a = -a * (x + b) from by ring]

/-- The contour's forward arithmetic series is the finite Mangoldt sum of
the physical profile that appears in the middle Euler lower bound. -/
public theorem middle_pole_forward_sum (Q : Polynomial ℚ) {N : ℕ} (hQ : 2 * Q.natDegree + 3 ≤ N)
    {a b x : ℝ} (ha : 1 / 2 < a) (κ : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    let B := (middlePoleProfile N Q).map (Rat.castHom ℝ)
    let W := middlePrincipalWeight B (κ * Real.exp (-a * (x + b))) (x + b) (a - 1 / 2)
    (κ : ℂ) *
        (∑' n,
          ∑ i ∈ Finset.Ico 3 (N + 1),
            ((Q ^ 2).coeff (N - i) : ℂ) *
              (LLS.PaperStatements.shiftedPoleKernel (max 1 i) a b (le_max_left _ _) ha).summand χ
                (Real.exp x) n) =
      ∑ n ∈ Finset.Ioc 0 ⌊Real.exp (x + b)⌋₊,
        ((ArithmeticFunction.vonMangoldt n * W n : ℝ) : ℂ) * χ n := by
  intro B W
  rw [LLS.PaperStatements.shiftedPole_summand_tsum _ _ _ (fun _ ↦ le_max_left _ _) ha
      (Real.exp_pos x) χ,
    ← Real.exp_add, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have ht : (0 : ℝ) < n := Nat.cast_pos.mpr (Finset.mem_Ioc.mp hn).1
  have hz : b - Real.log ((n : ℝ) / Real.exp x) = x + b - Real.log n := by
    rw [Real.log_div ht.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  rw [middle_pole_contour_poly Q hQ, hz]
  simp only [W, middlePrincipalWeight, B, Polynomial.eval_map, Complex.ofReal_mul, div_eq_mul_inv]
  have hs := congrArg Complex.ofReal (middle_contour_scale (a := a) (b := b) (x := x) ht)
  simp only [Complex.ofReal_mul, div_eq_mul_inv] at hs
  linear_combination
    ((κ : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ) * χ n *
        (((middlePoleProfile N Q).eval₂ (Rat.castHom ℝ) (x + b - Real.log n) : ℝ) : ℂ)) *
      hs

/-- The K141 forward contour term equals the finite sum using its certified
Euler profile and mass normalization. -/
public theorem middle_k141_contour_forward (x : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    let a : ℝ := ((2 : ℚ) : ℝ)
    let z := x + 7 / 2
    let κ := (middleK141Norm : ℝ)
    let W :=
      middlePrincipalWeight (middleK141Profile.map (Rat.castHom ℝ)) (κ * Real.exp (-a * z)) z
        (a - 1 / 2)
    (κ : ℂ) *
        (∑' n,
          ∑ i ∈ Finset.Ico 3 (31 + 1),
            ((middleK141Kernel ^ 2).coeff (31 - i) : ℂ) *
              (LLS.PaperStatements.shiftedPoleKernel (max 1 i) a (7 / 2) (le_max_left _ _)
                    (by norm_num only [Rat.cast_div, Rat.cast_ofNat])).summand
                χ (Real.exp x) n) =
      ∑ n ∈ Finset.Ioc 0 ⌊Real.exp z⌋₊,
        ((ArithmeticFunction.vonMangoldt n * W n : ℝ) : ℂ) * χ n := by
  have hd : 2 * middleK141Kernel.natDegree + 3 ≤ 31 :=
    Nat.add_le_add_right (Nat.mul_le_mul_left 2 middle_k141_kernel_degree) 3
  have h :=
    middle_pole_forward_sum middleK141Kernel hd (b := 7 / 2) (x := x) (a := ((2 : ℚ) : ℝ))
      (by norm_num only [Rat.cast_div, Rat.cast_ofNat]) (middleK141Norm : ℝ) χ
  rw [← middle_k141_profile_eq_pole] at h
  exact h

/-- The K156 forward contour term equals the finite sum using its certified
Euler profile and mass normalization. -/
public theorem middle_k156_contour_forward (x : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    let a : ℝ := ((49 / 20 : ℚ) : ℝ)
    let z := x + 7 / 2
    let κ := (middleK156Norm : ℝ)
    let W :=
      middlePrincipalWeight (middleK156Profile.map (Rat.castHom ℝ)) (κ * Real.exp (-a * z)) z
        (a - 1 / 2)
    (κ : ℂ) *
        (∑' n,
          ∑ i ∈ Finset.Ico 3 (51 + 1),
            ((middleK156Kernel ^ 2).coeff (51 - i) : ℂ) *
              (LLS.PaperStatements.shiftedPoleKernel (max 1 i) a (7 / 2) (le_max_left _ _)
                    (by norm_num only [Rat.cast_div, Rat.cast_ofNat])).summand
                χ (Real.exp x) n) =
      ∑ n ∈ Finset.Ioc 0 ⌊Real.exp z⌋₊,
        ((ArithmeticFunction.vonMangoldt n * W n : ℝ) : ℂ) * χ n := by
  have hd : 2 * middleK156Kernel.natDegree + 3 ≤ 51 :=
    Nat.add_le_add_right (Nat.mul_le_mul_left 2 middle_k156_kernel_degree) 3
  have h :=
    middle_pole_forward_sum middleK156Kernel hd (b := 7 / 2) (x := x) (a := ((49 / 20 : ℚ) : ℝ))
      (by norm_num only [Rat.cast_div, Rat.cast_ofNat]) (middleK156Norm : ℝ) χ
  rw [← middle_k156_profile_eq_pole] at h
  exact h

/-- The reciprocal-scale kernel transforms into the reflected physical weight. -/
private theorem middle_reciprocal_scale {t a b x : ℝ} (ht : 0 < t) :
    (((t * Real.exp x)⁻¹ * Real.exp (-b)) ^ a) / Real.sqrt t =
      Real.exp (-a * (x + b)) * t ^ (-(a + 1 / 2)) := by
  have h : (t * Real.exp x)⁻¹ * Real.exp (-b) = t⁻¹ * Real.exp (-(x + b)) := by
    rw [mul_inv_rev, ← Real.exp_neg]
    calc
      _ = t⁻¹ * (Real.exp (-x) * Real.exp (-b)) := by ring
      _ = _ := by rw [← Real.exp_add, neg_add]
  rw [h, Real.mul_rpow (inv_nonneg.mpr ht.le) (Real.exp_nonneg _), ← Real.exp_mul,
    Real.inv_rpow ht.le, ← Real.rpow_neg ht.le, mul_comm (t ^ (-a)), mul_div_assoc,
    Real.sqrt_eq_rpow, ← Real.rpow_sub ht]
  congr 2 <;> ring

/-- The real part of the reciprocal Mellin sum equals the reflected series
in the Euler lower bound. Only the norm bound on the combined twist is needed. -/
public theorem middle_pole_reflected_sum (Q : Polynomial ℚ) {N : ℕ} (hQ : 2 * Q.natDegree + 3 ≤ N)
    {a b x : ℝ} (ha : 1 / 2 < a) (hb : 0 ≤ b) (hx : 0 ≤ x) (κ : ℝ) (χ : ℕ → ℂ)
    (hχ : ∀ n, ‖χ n‖ ≤ 3) :
    let B := (middlePoleProfile N Q).map (Rat.castHom ℝ)
    ((κ : ℂ) *
          (∑' n : ℕ,
            (((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * χ n) *
              ∑ i ∈ Finset.Ico 3 (N + 1),
                ((Q ^ 2).coeff (N - i) : ℂ) *
                  (LLS.PaperStatements.shiftedPoleKernel (max 1 i) a b (le_max_left _ _)
                        ha).transform
                    (((n : ℝ) * Real.exp x)⁻¹))).re =
      middleReflectedSum B (fun n ↦ (χ n).re) κ a b x := by
  intro B
  let f := fun n : ℕ ↦
    ArithmeticFunction.vonMangoldt n * ((n : ℝ) ^ (-(a + 1 / 2)) * B.eval (x + b + Real.log n))
  have hσ : 1 < a + 1 / 2 := by linarith only [ha]
  have hs := summable_reflected_complex χ hχ B hσ (x + b)
  change Summable (fun n ↦ χ n * (f n : ℂ)) at hs
  have he :
    (fun n : ℕ ↦
        (((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * χ n) *
          ∑ i ∈ Finset.Ico 3 (N + 1),
            ((Q ^ 2).coeff (N - i) : ℂ) *
              (LLS.PaperStatements.shiftedPoleKernel (max 1 i) a b (le_max_left _ _) ha).transform
                (((n : ℝ) * Real.exp x)⁻¹)) =
      fun n ↦ (Real.exp (-a * (x + b)) : ℂ) * (χ n * (f n : ℂ)) := by
    funext n
    by_cases hn : n = 0
    · subst n
      simp only [f, ArithmeticFunction.map_zero, zero_div, Complex.ofReal_zero, zero_mul, mul_zero]
    · have ht : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      have hnx : 1 ≤ (n : ℝ) * Real.exp x :=
        one_le_mul_of_one_le_of_one_le (Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hn))
          (Real.one_le_exp hx)
      have hu := inv_pos.mpr (mul_pos ht (Real.exp_pos x))
      have hub := (inv_le_one_of_one_le₀ hnx).trans (Real.one_le_exp hb)
      rw [LLS.PaperStatements.shiftedPole_transform_sum _ _ _ (fun _ ↦ le_max_left _ _) ha hu hub,
        middle_pole_contour_poly Q hQ]
      have hz : b - Real.log (((n : ℝ) * Real.exp x)⁻¹) = x + b + Real.log n := by
        rw [Real.log_inv, Real.log_mul ht.ne' (Real.exp_pos x).ne', Real.log_exp]
        ring
      rw [hz]
      simp only [f, B, Polynomial.eval_map, Complex.ofReal_mul, div_eq_mul_inv]
      have hs' := congrArg Complex.ofReal (middle_reciprocal_scale (a := a) (b := b) (x := x) ht)
      simp only [Complex.ofReal_mul, div_eq_mul_inv] at hs'
      linear_combination
        (↑(ArithmeticFunction.vonMangoldt n) * χ n *
            ↑((middlePoleProfile N Q).eval₂ (Rat.castHom ℝ) (x + b + Real.log n))) *
          hs'
  rw [he, tsum_mul_left]
  simp only [Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.ofReal_re]
  rw [Complex.re_tsum hs, ← mul_assoc]
  simp only [middleReflectedSum, f]
  congr 1
  apply tsum_congr
  intro n
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  ring

/-- A reflected ordinary Dirichlet term has reciprocal Mellin scale. -/
private theorem middle_left_term (F : ℂ → ℂ) (f : ℕ → ℂ) {X : ℝ} (hX : 0 < X) {n : ℕ} (hn : n ≠ 0) :
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let r := fun t : ℝ ↦ ((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, LSeries.term f (r t) n * (F (l t) * (X : ℂ) ^ l t)) =
      (f n / (n : ℂ) ^ (1 / 2 : ℂ)) * Analysis.inverseMellin F (-9 / 16) ((n : ℝ) * X)⁻¹ := by
  intro l r
  unfold Analysis.inverseMellin
  rw [mul_left_comm (f n / (n : ℂ) ^ (1 / 2 : ℂ))]
  congr 1
  rw [← MeasureTheory.integral_const_mul (f n / (n : ℂ) ^ (1 / 2 : ℂ))]
  apply MeasureTheory.integral_congr_ae
  refine Filter.Eventually.of_forall fun t ↦ ?_
  have hr : r t = 1 / 2 - l t := by
    dsimp only [r, l]
    norm_num only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_ofNat]
    ring
  have hnX : 0 < (n : ℝ) * X := mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) hX
  change
    LSeries.term f (r t) n * (F (l t) * (X : ℂ) ^ l t) =
      (f n / (n : ℂ) ^ (1 / 2 : ℂ)) * (F (l t) * ((((n : ℝ) * X)⁻¹ : ℝ) : ℂ) ^ (-(l t)))
  rw [LSeries.term_of_ne_zero hn, hr, Complex.cpow_sub _ _ (Nat.cast_ne_zero.mpr hn),
    Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg hnX.le, Complex.cpow_neg, inv_inv,
    Complex.ofReal_mul, Complex.ofReal_mul_cpow (Nat.cast_nonneg n) (X : ℂ), Complex.ofReal_natCast,
    div_div_eq_mul_div]
  ring

/-- Move the inverse Mellin transform of a finite shifted-pole sum to a
line strictly to the right of its common pole. -/
private theorem middle_inverse_poles {ι : Type*} (s : Finset ι) (k : ι → ℕ) (c : ι → ℂ)
    (hk : ∀ i, 1 ≤ k i) {a line : ℝ} (ha : 1 / 2 < a) (hline : 0 < line + a) (b : ℝ) {u : ℝ}
    (hu : 0 < u) :
    let K := fun i ↦ LLS.PaperStatements.shiftedPoleKernel (k i) a b (hk i) ha
    Analysis.inverseMellin (fun z ↦ ∑ i ∈ s, c i * (K i).function z) line u =
      ∑ i ∈ s, c i * (K i).transform u := by
  intro K
  have hK (i : ι) :
    MeasureTheory.Integrable (fun t : ℝ ↦ (K i).function ((line : ℂ) + Complex.I * t)) :=
    LLS.PaperStatements.shifted_power_integrable (hk i) hline b
  simp only [Analysis.inverseMellin, Finset.sum_mul, mul_assoc]
  rw [MeasureTheory.integral_finsetSum _
      (fun i _ ↦ (LLS.PaperStatements.integrable_inverseMellin_of_line hu (hK i)).const_mul (c i)),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [MeasureTheory.integral_const_mul, mul_left_comm]
  change c i * Analysis.inverseMellin (K i).function line u = _
  congr 1
  rw [LLS.PaperStatements.MellinKernel.transform]
  exact
    (Analysis.inverseMellin_shiftedPole (hk i) hline hu b).trans
      (Analysis.inverseMellin_shiftedPole (hk i) (by linarith only [ha]) hu b).symm

/-- The ordinary reflected integral for a finite sum of shifted poles equals
its reciprocal-scale Mangoldt series on the common middle contour. -/
public theorem middle_shifted_pole_reflected {ι : Type*} (s : Finset ι) (k : ι → ℕ) (c : ι → ℂ)
    (hk : ∀ i, 1 ≤ k i) {a : ℝ} (ha : 9 / 16 < a) (b x : ℝ) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    let ha' : 1 / 2 < a := (by norm_num only : (1 / 2 : ℝ) < 9 / 16).trans ha
    let K := fun i ↦ LLS.PaperStatements.shiftedPoleKernel (k i) a b (hk i) ha'
    let F := fun z ↦ ∑ i ∈ s, c i * (K i).function z
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let r := fun t : ℝ ↦ ((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ, -logDeriv χ.LFunction (r t) * (F (l t) * (Real.exp x : ℂ) ^ l t)) =
      ∑' n : ℕ,
        (((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * χ n) *
          ∑ i ∈ s, c i * (K i).transform (((n : ℝ) * Real.exp x)⁻¹) := by
  intro ha' K F l r
  let X := Real.exp x
  let f := (fun n : ℕ ↦ χ n) * (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ))
  have hline : 0 < -9 / 16 + a := by linarith only [ha]
  have hK (i : ι) : MeasureTheory.Integrable (fun t ↦ (K i).function (l t)) :=
    LLS.PaperStatements.shifted_power_integrable (hk i) hline b
  have hi : MeasureTheory.Integrable (fun t ↦ F (l t) * (X : ℂ) ^ l t) := by
    have hz : MeasureTheory.Integrable (fun t ↦ F (l t)) :=
      MeasureTheory.integrable_finsetSum _ (fun i _ ↦ (hK i).const_mul (c i))
    have hh :=
      LLS.PaperStatements.integrable_inverseMellin_of_line (F := F) (c := -9 / 16)
        (inv_pos.mpr (Real.exp_pos x)) hz
    convert hh using 1
    funext t
    change F (l t) * (X : ℂ) ^ l t = F (l t) * ((X⁻¹ : ℝ) : ℂ) ^ (-(l t))
    rw [Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg (show 0 ≤ X from Real.exp_nonneg x),
      Complex.cpow_neg, inv_inv]
  have hs : LSeriesSummable f ((17 / 16 : ℝ) : ℂ) :=
    χ.LSeriesSummable_twist_vonMangoldt (by norm_num only [Complex.ofReal_re])
  simp only [r, LLS.PaperStatements.gamma_reflected_ordinary_eq_euler]
  rw [AnalyticNumberTheory.General.integral_LSeries_mul_weight_eq_tsum hs _
      (fun t ↦ F (l t) * (X : ℂ) ^ l t) continuous_neg hi,
    ← tsum_mul_left]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [LSeries.term_zero, zero_mul, MeasureTheory.integral_zero, mul_zero,
      ArithmeticFunction.map_zero, zero_div, Complex.ofReal_zero]
  · have hu := inv_pos.mpr (mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) (Real.exp_pos x))
    rw [middle_left_term F f (Real.exp_pos x) hn]
    dsimp only [F]
    rw [middle_inverse_poles s k c hk ha' hline b hu]
    have hr : (((Real.sqrt n : ℝ) : ℂ)) = (n : ℂ) ^ (1 / 2 : ℂ) := by
      rw [Real.sqrt_eq_rpow]
      simpa only [Complex.ofReal_natCast, Complex.ofReal_div, Complex.ofReal_one,
        Complex.ofReal_ofNat] using Complex.ofReal_cpow (Nat.cast_nonneg n) (1 / 2)
    simp only [f, Pi.mul_apply, Complex.ofReal_div, hr]
    ring

/-- The reflected ordinary contour for a squared middle kernel has the
real value bounded by the reflected-series estimate in the Euler lower bound. -/
public theorem middle_pole_reflected_integral (Q : Polynomial ℚ) {N : ℕ}
    (hQ : 2 * Q.natDegree + 3 ≤ N) {a b x : ℝ} (ha : 9 / 16 < a) (hb : 0 ≤ b) (hx : 0 ≤ x) (κ : ℝ)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    let ha' : 1 / 2 < a := (by norm_num only : (1 / 2 : ℝ) < 9 / 16).trans ha
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let r := fun t : ℝ ↦ ((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)
    let F := fun z ↦
      ∑ i ∈ Finset.Ico 3 (N + 1),
        ((Q ^ 2).coeff (N - i) : ℂ) *
          (LLS.PaperStatements.shiftedPoleKernel (max 1 i) a b (le_max_left _ _) ha').function z
    ((κ : ℂ) *
          (((1 / (2 * Real.pi) : ℝ) : ℂ) *
            (∫ t : ℝ, -logDeriv χ.LFunction (r t) * (F (l t) * (Real.exp x : ℂ) ^ l t)))).re =
      middleReflectedSum ((middlePoleProfile N Q).map (Rat.castHom ℝ)) (fun n ↦ (χ n).re) κ a b
        x := by
  intro ha' l r F
  have h :=
    middle_shifted_pole_reflected (Finset.Ico 3 (N + 1)) (fun i ↦ max 1 i)
      (fun i ↦ ((Q ^ 2).coeff (N - i) : ℂ)) (fun _ ↦ le_max_left _ _) ha b x χ
  dsimp only at h
  dsimp only [F, r, l]
  rw [h]
  exact
    middle_pole_reflected_sum Q hQ ha' hb hx κ (fun n ↦ χ n)
      (fun n ↦ (χ.norm_le_one n).trans (by norm_num only))

/-- A real constant on the left contour contributes its product with the
physical profile at `x + b`. For the conductor, the constant is the log level. -/
public theorem middle_pole_conductor_integral (Q : Polynomial ℚ) {N : ℕ}
    (hQ : 2 * Q.natDegree + 3 ≤ N) {a b x : ℝ} (ha : 9 / 16 < a) (hb : 0 ≤ b) (hx : 0 ≤ x)
    (κ L : ℝ) :
    let ha' : 1 / 2 < a := (by norm_num only : (1 / 2 : ℝ) < 9 / 16).trans ha
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let F := fun z ↦
      ∑ i ∈ Finset.Ico 3 (N + 1),
        ((Q ^ 2).coeff (N - i) : ℂ) *
          (LLS.PaperStatements.shiftedPoleKernel (max 1 i) a b (le_max_left _ _) ha').function z
    ((κ : ℂ) *
          (((1 / (2 * Real.pi) : ℝ) : ℂ) *
            (∫ t : ℝ, (L : ℂ) * (F (l t) * (Real.exp x : ℂ) ^ l t)))).re =
      L * (κ * Real.exp (-a * (x + b))) *
        (middlePoleProfile N Q).eval₂ (Rat.castHom ℝ) (x + b) := by
  intro ha' l F
  have hu : 0 < Real.exp (-x) := Real.exp_pos _
  have huv : Real.exp (-x) ≤ Real.exp b := Real.exp_le_exp.mpr ((neg_nonpos.mpr hx).trans hb)
  have hi :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, F (l t) * (Real.exp x : ℂ) ^ l t)) =
      Analysis.inverseMellin F (-9 / 16) (Real.exp (-x)) := by
    rw [Analysis.inverseMellin]
    congr 1
    apply MeasureTheory.integral_congr_ae
    refine Filter.Eventually.of_forall fun t ↦ ?_
    change F (l t) * (Real.exp x : ℂ) ^ l t = F (l t) * (Real.exp (-x) : ℂ) ^ (-(l t))
    rw [Real.exp_neg, Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg (Real.exp_nonneg x),
      Complex.cpow_neg, inv_inv]
  rw [MeasureTheory.integral_const_mul, mul_left_comm _ (L : ℂ), hi]
  dsimp only [F]
  have hline : 0 < -9 / 16 + a := by linarith only [ha]
  rw [middle_inverse_poles _ _ _ (fun _ ↦ le_max_left _ _) ha' hline b hu,
    LLS.PaperStatements.shiftedPole_transform_sum _ _ _ (fun _ ↦ le_max_left _ _) ha' hu huv,
    middle_pole_contour_poly Q hQ, Real.log_exp, sub_neg_eq_add, add_comm b x, ← Real.exp_add, ←
    Real.exp_mul]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, zero_mul]
  rw [show (-x + -b) * a = -a * (x + b) from by ring]
  ring

/-- The three pair levels of a triple product contribute `2 * log n` times
one physical profile value. This gives the conductor term in the middle residual. -/
public theorem middle_pair_conductor (Q : Polynomial ℚ) {N : ℕ} (hQ : 2 * Q.natDegree + 3 ≤ N)
    {a b x : ℝ} (ha : 9 / 16 < a) (hb : 0 ≤ b) (hx : 0 ≤ x) (κ : ℝ) {n p q r : ℕ} [NeZero p]
    [NeZero q] [NeZero r] (hn : n = p * q * r) :
    let ha' : 1 / 2 < a := (by norm_num only : (1 / 2 : ℝ) < 9 / 16).trans ha
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let F := fun z ↦
      ∑ i ∈ Finset.Ico 3 (N + 1),
        ((Q ^ 2).coeff (N - i) : ℂ) *
          (LLS.PaperStatements.shiftedPoleKernel (max 1 i) a b (le_max_left _ _) ha').function z
    let L := Real.log (p * q : ℕ) + Real.log (p * r : ℕ) + Real.log (q * r : ℕ)
    ((κ : ℂ) *
          (((1 / (2 * Real.pi) : ℝ) : ℂ) *
            (∫ t : ℝ, (L : ℂ) * (F (l t) * (Real.exp x : ℂ) ^ l t)))).re =
      (2 * Real.log n) * (κ * Real.exp (-a * (x + b))) *
        (middlePoleProfile N Q).eval₂ (Rat.castHom ℝ) (x + b) := by
  dsimp only
  rw [pair_level_log_sum hn]
  exact middle_pole_conductor_integral Q hQ ha hb hx κ (2 * Real.log n)

/-- On either Gamma contour the inverse squared kernel is the physical
polynomial times the exponential on its logarithmic support. -/
public theorem middle_pole_inverse_log (Q : Polynomial ℚ) {N : ℕ} (hQ : 2 * Q.natDegree + 3 ≤ N)
    {a c : ℝ} (ha : 1 / 2 < a) (hc : 0 < c + a) (b y : ℝ) :
    let F := fun z ↦
      ∑ i ∈ Finset.Ico 3 (N + 1),
        ((Q ^ 2).coeff (N - i) : ℂ) *
          (LLS.PaperStatements.shiftedPoleKernel (max 1 i) a b (le_max_left _ _) ha).function z
    Analysis.inverseMellin F c (Real.exp (b - y)) =
      if 0 ≤ y then ((Real.exp (-a * y) * (middlePoleProfile N Q).eval₂ (Rat.castHom ℝ) y : ℝ) : ℂ)
      else 0 := by
  intro F
  dsimp only [F]
  rw [middle_inverse_poles _ _ _ (fun _ ↦ le_max_left _ _) ha hc b (Real.exp_pos _)]
  by_cases hy : 0 ≤ y
  · have hu : Real.exp (b - y) ≤ Real.exp b := Real.exp_le_exp.mpr (sub_le_self b hy)
    rw [ite_eq_left hy,
      LLS.PaperStatements.shiftedPole_transform_sum _ _ _ (fun _ ↦ le_max_left _ _) ha
        (Real.exp_pos _) hu,
      Real.log_exp, sub_sub_cancel, middle_pole_contour_poly Q hQ, ← Real.exp_add, ← Real.exp_mul, ←
      Complex.ofReal_mul]
    rw [show (b - y + -b) * a = -a * y from by ring]
  · rw [ite_eq_right hy]
    exact
      LLS.PaperStatements.shiftedPole_transform_sum_zero _ _ _ (fun _ ↦ le_max_left _ _) ha
        (Real.exp_le_exp.mpr (by linarith only [lt_of_not_ge hy]))

/-- The shifted-pole contour weight is continuous and integrable on lines
strictly to the right of its pole. -/
private theorem middle_pole_weight_regular (Q : Polynomial ℚ) (N : ℕ) {a c : ℝ} (ha : 1 / 2 < a)
    (hc : 0 < c + a) (b x : ℝ) :
    let l := fun t : ℝ ↦ (c : ℂ) + Complex.I * t
    let F := fun z ↦
      ∑ i ∈ Finset.Ico 3 (N + 1),
        ((Q ^ 2).coeff (N - i) : ℂ) *
          (LLS.PaperStatements.shiftedPoleKernel (max 1 i) a b (le_max_left _ _) ha).function z
    let W := fun t ↦ F (l t) * Complex.exp (l t * (x : ℂ))
    Continuous W ∧ MeasureTheory.Integrable W := by
  intro l F W
  have hl : Continuous l := continuous_const.add (continuous_const.mul Complex.continuous_ofReal)
  have hden (t : ℝ) : l t + (a : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [l, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero, Complex.zero_re] at hre
    exact hc.ne' hre
  have hF : Continuous fun t ↦ F (l t) := by
    apply continuous_finsetSum
    intro i _
    apply continuous_const.mul
    change Continuous (fun t ↦ Complex.exp ((b : ℂ) * l t) / (l t + (a : ℂ)) ^ (max 1 i + 1))
    exact
      (Complex.continuous_exp.comp (continuous_const.mul hl)).div ((hl.add continuous_const).pow _)
        (fun t ↦ pow_ne_zero _ (hden t))
  have hExp : Continuous fun t ↦ Complex.exp (l t * (x : ℂ)) :=
    Complex.continuous_exp.comp (hl.mul continuous_const)
  refine ⟨hF.mul hExp, ?_⟩
  have hi : MeasureTheory.Integrable (fun t ↦ F (l t)) := by
    apply MeasureTheory.integrable_finsetSum
    intro i _
    exact (LLS.PaperStatements.shifted_power_integrable (le_max_left 1 i) hc b).const_mul _
  refine
    hi.mul_bdd hExp.aestronglyMeasurable (c := Real.exp (c * x))
      (Filter.Eventually.of_forall fun t ↦ ?_)
  rw [Complex.norm_exp]
  simp only [l, Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero, add_zero]
  exact le_rfl

/-- Reflecting the line parameter gives the same Laplace exchange for either
sign of the imaginary part in the resolvent. -/
private theorem signed_resolvent_laplace (W : ℝ → ℂ) (hW : Continuous W)
    (hiW : MeasureTheory.Integrable W) {β ε : ℝ} (hβ : 0 < β) (he : ε = 1 ∨ ε = -1) :
    (∫ t : ℝ, (1 / ((β : ℂ) + Complex.I * ((ε * t : ℝ) : ℂ) / 2)) * W t) =
      ∫ u in Set.Ioi (0 : ℝ),
        ∫ t : ℝ, Complex.exp (-((β : ℂ) + Complex.I * ((ε * t : ℝ) : ℂ) / 2) * (u : ℂ)) * W t := by
  rcases he with rfl | rfl
  · simpa only [one_mul] using LLS.PaperStatements.resolvent_integral_eq_laplace_weight hβ W hW hiW
  · have h :=
      LLS.PaperStatements.resolvent_integral_eq_laplace_weight hβ (fun t ↦ W (-t))
        (hW.comp continuous_neg) hiW.comp_neg
    have hl :=
      MeasureTheory.integral_neg_eq_self
        (fun t : ℝ ↦ (1 / ((β : ℂ) + Complex.I * ((-1 * t : ℝ) : ℂ) / 2)) * W t)
        MeasureTheory.volume
    rw [← hl]
    simp only [neg_one_mul, neg_neg] at *
    rw [h]
    apply MeasureTheory.integral_congr_ae
    refine MeasureTheory.ae_of_all _ fun u ↦ ?_
    have hr :=
      MeasureTheory.integral_neg_eq_self
        (fun t : ℝ ↦ Complex.exp (-((β : ℂ) + Complex.I * ((-t : ℝ) : ℂ) / 2) * (u : ℂ)) * W t)
        MeasureTheory.volume
    simpa only [neg_neg] using hr

/-- Either Gamma resolvent is a Laplace integral of the physical profile.
The sign selects the direction of the shift in logarithmic height. -/
public theorem middle_gamma_resolvent (Q : Polynomial ℚ) {N : ℕ} (hQ : 2 * Q.natDegree + 3 ≤ N)
    {a c b x β ε : ℝ} (ha : 1 / 2 < a) (hc : 0 < c + a) (hβ : 0 < β) (he : ε = 1 ∨ ε = -1) :
    let l := fun t : ℝ ↦ (c : ℂ) + Complex.I * t
    let F := fun z ↦
      ∑ i ∈ Finset.Ico 3 (N + 1),
        ((Q ^ 2).coeff (N - i) : ℂ) *
          (LLS.PaperStatements.shiftedPoleKernel (max 1 i) a b (le_max_left _ _) ha).function z
    let W := fun t ↦ F (l t) * Complex.exp (l t * (x : ℂ))
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ, (1 / ((β : ℂ) + Complex.I * ((ε * t : ℝ) : ℂ) / 2)) * W t) =
      ∫ u in Set.Ioi (0 : ℝ),
        if 0 ≤ b + x - ε * u / 2 then
          ((Real.exp ((ε * c / 2 - β) * u - a * (b + x - ε * u / 2)) *
                (middlePoleProfile N Q).eval₂ (Rat.castHom ℝ) (b + x - ε * u / 2) :
              ℝ) :
            ℂ)
        else 0 := by
  intro l F W
  obtain ⟨hW, hiW⟩ := middle_pole_weight_regular Q N ha hc b x
  rw [signed_resolvent_laplace W hW hiW hβ he, ← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  refine MeasureTheory.ae_of_all _ fun u ↦ ?_
  let y := b + x - ε * u / 2
  have ht :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ, Complex.exp (-((β : ℂ) + Complex.I * ((ε * t : ℝ) : ℂ) / 2) * (u : ℂ)) * W t) =
      (Real.exp ((ε * c / 2 - β) * u) : ℂ) * Analysis.inverseMellin F c (Real.exp (b - y)) := by
    dsimp only [Analysis.inverseMellin]
    rw [mul_left_comm _ (((1 / (2 * Real.pi) : ℝ) : ℂ))]
    apply congrArg (((1 / (2 * Real.pi) : ℝ) : ℂ) * ·)
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    refine MeasureTheory.ae_of_all _ fun t ↦ ?_
    dsimp only
    have hu := Real.exp_pos (b - y)
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hu.ne'), ← Complex.ofReal_log hu.le,
      Real.log_exp, Complex.ofReal_exp]
    dsimp only [W, l]
    calc
      _ =
          F ((c : ℂ) + Complex.I * t) *
            Complex.exp
              (-((β : ℂ) + Complex.I * ((ε * t : ℝ) : ℂ) / 2) * (u : ℂ) +
                ((c : ℂ) + Complex.I * t) * (x : ℂ)) :=
        by
        rw [Complex.exp_add]; ring
      _ = _ := by
        rw [mul_left_comm, ← Complex.exp_add]
        congr 2
        simp only [y, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_div,
          Complex.ofReal_add, Complex.ofReal_ofNat]
        ring
  dsimp only
  rw [ht]
  dsimp only [F]
  rw [middle_pole_inverse_log Q hQ ha hc b y]
  change
    _ =
      if 0 ≤ y then
        ((Real.exp ((ε * c / 2 - β) * u - a * y) * (middlePoleProfile N Q).eval₂ (Rat.castHom ℝ) y :
            ℝ) :
          ℂ)
      else 0
  by_cases hy : 0 ≤ y
  · rw [ite_eq_left hy, ite_eq_left hy, ← Complex.ofReal_mul, ← mul_assoc, ← Real.exp_add, neg_mul,
      ← sub_eq_add_neg]
  · rw [ite_eq_right hy, mul_zero]
    exact (ite_eq_right hy).symm

/-- The middle contour weight decays quadratically on either common Gamma line. -/
private theorem middle_pole_weight_quadratic (Q : Polynomial ℚ) (N : ℕ) {a c : ℝ} (ha : 1 / 2 < a)
    (ha1 : 1 ≤ a) (hl : -(9 / 16) ≤ c) (hr : c ≤ 9 / 16) (hne : c ≠ -1 / 2) (b x : ℝ) :
    let l := fun t : ℝ ↦ (c : ℂ) + Complex.I * t
    let F := fun z ↦
      ∑ i ∈ Finset.Ico 3 (N + 1),
        ((Q ^ 2).coeff (N - i) : ℂ) *
          (LLS.PaperStatements.shiftedPoleKernel (max 1 i) a b (le_max_left _ _) ha).function z
    let W := fun t ↦ F (l t) * Complex.exp (l t * (x : ℂ))
    ∃ A : ℝ, ∀ t : ℝ, ‖W t‖ ≤ A / (1 + t ^ 2) := by
  intro l F W
  let K := fun i : ℕ ↦ LLS.PaperStatements.shiftedPoleKernel (max 1 i) a b (le_max_left _ _) ha
  have hK (i : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, ‖(K i).function (l t)‖ ≤ C / (1 + t ^ 2) := by
    have hd : (K i).delta = 1 / 8 := by
      dsimp only [K]
      rw [LLS.PaperStatements.shiftedPoleKernel_delta, min_eq_right]
      linarith only [ha1]
    exact
      LLS.PaperStatements.MellinKernel.exists_norm_line_le_inverseSquare (K i)
        (by
          rw [hd]; linarith only [hl])
        (by
          rw [hd]; linarith only [hr])
        hne
  choose C _ hC using hK
  let q := fun i : ℕ ↦ ((Q ^ 2).coeff (N - i) : ℂ)
  refine ⟨(∑ i ∈ Finset.Ico 3 (N + 1), ‖q i‖ * C i) * Real.exp (c * x), fun t ↦ ?_⟩
  have he : ‖Complex.exp (l t * (x : ℂ))‖ = Real.exp (c * x) := by
    simp only [Complex.norm_exp, l, Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.I_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  change
    ‖(∑ i ∈ Finset.Ico 3 (N + 1), q i * (K i).function (l t)) * Complex.exp (l t * (x : ℂ))‖ ≤ _
  rw [norm_mul, he, mul_div_right_comm, Finset.sum_div]
  refine
    mul_le_mul_of_nonneg_right ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_))
      (Real.exp_nonneg _)
  rw [norm_mul, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (hC i t) (norm_nonneg _)

/-- The constant part of the Gamma integrand evaluates the profile at the
unshifted logarithmic height on either contour. -/
private theorem middle_gamma_weight_integral (Q : Polynomial ℚ) {N : ℕ}
    (hQ : 2 * Q.natDegree + 3 ≤ N) {a c b x : ℝ} (ha : 1 / 2 < a) (hc : 0 < c + a)
    (hz : 0 ≤ b + x) :
    let l := fun t : ℝ ↦ (c : ℂ) + Complex.I * t
    let F := fun z ↦
      ∑ i ∈ Finset.Ico 3 (N + 1),
        ((Q ^ 2).coeff (N - i) : ℂ) *
          (LLS.PaperStatements.shiftedPoleKernel (max 1 i) a b (le_max_left _ _) ha).function z
    let W := fun t ↦ F (l t) * Complex.exp (l t * (x : ℂ))
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, W t) =
      ((Real.exp (-a * (b + x)) * (middlePoleProfile N Q).eval₂ (Rat.castHom ℝ) (b + x) : ℝ) :
        ℂ) := by
  intro l F W
  have h := middle_pole_inverse_log Q hQ ha hc b (b + x)
  dsimp only at h
  rw [ite_eq_left hz] at h
  refine Eq.trans ?_ h
  rw [Analysis.inverseMellin]
  congr 1
  apply MeasureTheory.integral_congr_ae
  refine MeasureTheory.ae_of_all _ fun t ↦ ?_
  dsimp only [W, l]
  have hu := Real.exp_pos (b - (b + x))
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hu.ne'), ← Complex.ofReal_log hu.le,
    Real.log_exp]
  rw [show b - (b + x) = -x by ring, Complex.ofReal_neg]
  congr 2
  ring

/-- Exchange a digamma difference for its reciprocal series in either orientation. -/
private theorem middle_digamma_exchange {A β ε : ℝ} (hβ : 0 < β) (he : ε = 1 ∨ ε = -1) (W : ℝ → ℂ)
    (hW : Continuous W) (hA : ∀ t : ℝ, ‖W t‖ ≤ A / (1 + t ^ 2)) :
    (∫ t : ℝ,
        (Complex.digamma ((β : ℂ) + Complex.I * ((ε * t : ℝ) : ℂ) / 2) - Complex.digamma (β : ℂ)) *
          W t) =
      ∑' n : ℕ,
        ∫ t : ℝ,
          (1 / ((β + n : ℝ) : ℂ) - 1 / (((β + n : ℝ) : ℂ) + Complex.I * ((ε * t : ℝ) : ℂ) / 2)) *
            W t := by
  rcases he with rfl | rfl
  · simpa only [one_mul, Complex.ofReal_div, Complex.ofReal_ofNat, mul_div_assoc] using
      LLS.PaperStatements.quadratic_digamma_integral_eq_tsum hβ W hW hA
  · simpa only [neg_one_mul, Complex.ofReal_neg, mul_neg, neg_div, ← sub_eq_add_neg,
      Complex.ofReal_div, Complex.ofReal_ofNat, mul_div_assoc] using
      LLS.PaperStatements.quadratic_reflected_digamma_eq_tsum hβ W hW hA

/-- The signed reciprocal difference is integrable under quadratic decay. -/
private theorem middle_digamma_diff_integrable {A β ε : ℝ} (hβ : 0 < β) (he : ε = 1 ∨ ε = -1)
    (W : ℝ → ℂ) (hW : Continuous W) (hA : ∀ t : ℝ, ‖W t‖ ≤ A / (1 + t ^ 2)) :
    MeasureTheory.Integrable
      (fun t : ℝ ↦ (1 / (β : ℂ) - 1 / ((β : ℂ) + Complex.I * ((ε * t : ℝ) : ℂ) / 2)) * W t) := by
  rcases he with rfl | rfl
  · simpa only [one_mul, Complex.ofReal_div, Complex.ofReal_ofNat, mul_div_assoc] using
      (LLS.PaperStatements.quadratic_resolvent_integral_bound hβ W hW hA).1
  · have h :=
      (LLS.PaperStatements.quadratic_resolvent_integral_bound hβ (fun t ↦ W (-t))
          (hW.comp continuous_neg) (fun t ↦ by simpa only [neg_sq] using hA (-t))).1.comp_neg
    simpa only [Function.comp_apply, neg_neg, neg_one_mul, Complex.ofReal_div, Complex.ofReal_ofNat,
      mul_div_assoc] using h

/-- The integrated reciprocal differences are absolutely summable in either orientation. -/
private theorem middle_digamma_term_summable {A β ε : ℝ} (hβ : 0 < β) (he : ε = 1 ∨ ε = -1)
    (W : ℝ → ℂ) (hW : Continuous W) (hA : ∀ t : ℝ, ‖W t‖ ≤ A / (1 + t ^ 2)) :
    Summable
      (fun n : ℕ ↦
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            (1 / ((β + n : ℝ) : ℂ) - 1 / (((β + n : ℝ) : ℂ) + Complex.I * ((ε * t : ℝ) : ℂ) / 2)) *
              W t)) := by
  have hp : 0 ≤ (1 / (2 * Real.pi) : ℝ) := by positivity
  have hb (f : ℝ → ℂ) :
    (1 / (2 * Real.pi)) * ‖∫ t : ℝ, f t‖ ≤ (∫ t : ℝ, ‖f t‖) / (2 * Real.pi) := by
    calc
      _ ≤ (1 / (2 * Real.pi)) * ∫ t : ℝ, ‖f t‖ :=
        mul_le_mul_of_nonneg_left (MeasureTheory.norm_integral_le_integral_norm f) hp
      _ = _ := by ring
  rcases he with rfl | rfl
  · apply (LLS.PaperStatements.summable_quadratic_resolvent_norm hβ W hW hA).of_norm_bounded
    intro n
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hp]
    simpa only [one_mul, Complex.ofReal_div, Complex.ofReal_ofNat, mul_div_assoc] using
      hb (fun t ↦ (1 / ((β + n : ℝ) : ℂ) - 1 / (((β + n : ℝ) : ℂ) + Complex.I * (t / 2))) * W t)
  · apply
      (LLS.PaperStatements.summable_quadratic_resolvent_norm hβ (fun t ↦ W (-t))
          (hW.comp continuous_neg) (fun t ↦ by simpa only [neg_sq] using hA (-t))).of_norm_bounded
    intro n
    have hflip :=
      MeasureTheory.integral_neg_eq_self
        (fun t : ℝ ↦
          (1 / ((β + n : ℝ) : ℂ) - 1 / (((β + n : ℝ) : ℂ) + Complex.I * ((-1 * t : ℝ) : ℂ) / 2)) *
            W t)
        MeasureTheory.volume
    rw [← hflip, norm_mul, Complex.norm_real, Real.norm_of_nonneg hp]
    simpa only [neg_one_mul, neg_neg, Complex.ofReal_div, Complex.ofReal_ofNat, mul_div_assoc] using
      hb (fun t ↦ (1 / ((β + n : ℝ) : ℂ) - 1 / (((β + n : ℝ) : ℂ) + Complex.I * (t / 2))) * W (-t))

/-- The normalized Gamma difference equals the series of constant-profile
terms minus physical Laplace resolvents, on either common Gamma contour. -/
public theorem middle_gamma_digamma_series (Q : Polynomial ℚ) {N : ℕ} (hQ : 2 * Q.natDegree + 3 ≤ N)
    {a c b x β ε : ℝ} (ha : 1 / 2 < a) (ha1 : 1 ≤ a) (hl : -(9 / 16) ≤ c) (hr : c ≤ 9 / 16)
    (hne : c ≠ -1 / 2) (hβ : 0 < β) (he : ε = 1 ∨ ε = -1) (hz : 0 ≤ b + x) :
    let l := fun t : ℝ ↦ (c : ℂ) + Complex.I * t
    let F := fun z ↦
      ∑ i ∈ Finset.Ico 3 (N + 1),
        ((Q ^ 2).coeff (N - i) : ℂ) *
          (LLS.PaperStatements.shiftedPoleKernel (max 1 i) a b (le_max_left _ _) ha).function z
    let W := fun t ↦ F (l t) * Complex.exp (l t * (x : ℂ))
    let B := (middlePoleProfile N Q).eval₂ (Rat.castHom ℝ)
    let D := fun n : ℕ ↦
      ((Real.exp (-a * (b + x)) * B (b + x) / (β + n) : ℝ) : ℂ) -
        (∫ u in Set.Ioi (0 : ℝ),
          if 0 ≤ b + x - ε * u / 2 then
            ((Real.exp ((ε * c / 2 - (β + n)) * u - a * (b + x - ε * u / 2)) *
                  B (b + x - ε * u / 2) :
                ℝ) :
              ℂ)
          else 0)
    Summable D ∧
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            (Complex.digamma ((β : ℂ) + Complex.I * ((ε * t : ℝ) : ℂ) / 2) -
                Complex.digamma (β : ℂ)) *
              W t) =
        ∑' n, D n := by
  intro l F W B D
  have hc : 0 < c + a := by linarith only [ha1, hl]
  obtain ⟨hW, hiW⟩ := middle_pole_weight_regular Q N ha hc b x
  obtain ⟨A, hA⟩ := middle_pole_weight_quadratic Q N ha ha1 hl hr hne b x
  have hterm (n : ℕ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          (1 / ((β + n : ℝ) : ℂ) - 1 / (((β + n : ℝ) : ℂ) + Complex.I * ((ε * t : ℝ) : ℂ) / 2)) *
            W t) =
      D n := by
    dsimp only [D]
    let γ := β + (n : ℝ)
    have hγ : 0 < γ := add_pos_of_pos_of_nonneg hβ (Nat.cast_nonneg n)
    have hd := middle_digamma_diff_integrable hγ he W hW hA
    have hconst := hiW.const_mul (1 / (γ : ℂ))
    change MeasureTheory.Integrable (fun t : ℝ ↦ (1 / (γ : ℂ)) * W t) at hconst
    have hres :
      MeasureTheory.Integrable
        (fun t : ℝ ↦ (1 / ((γ : ℂ) + Complex.I * ((ε * t : ℝ) : ℂ) / 2)) * W t) := by
      refine (hconst.sub hd).congr (MeasureTheory.ae_of_all _ fun t ↦ ?_)
      simp only [Pi.sub_apply, sub_mul, sub_sub_cancel]
    have hsplit :
      (∫ t : ℝ, (1 / (γ : ℂ) - 1 / ((γ : ℂ) + Complex.I * ((ε * t : ℝ) : ℂ) / 2)) * W t) =
        (∫ t : ℝ, (1 / (γ : ℂ)) * W t) -
          ∫ t : ℝ, (1 / ((γ : ℂ) + Complex.I * ((ε * t : ℝ) : ℂ) / 2)) * W t := by
      simpa only [sub_mul] using MeasureTheory.integral_sub hconst hres
    rw [hsplit, mul_sub]
    have hB := middle_gamma_weight_integral Q hQ ha hc hz
    have hR := middle_gamma_resolvent Q hQ (b := b) (x := x) ha hc hγ he
    dsimp only at hB hR
    rw [hR, MeasureTheory.integral_const_mul, mul_left_comm _ (1 / (γ : ℂ)), hB]
    simp only [B, γ, Complex.ofReal_div, Complex.ofReal_mul]
    ring
  refine ⟨(middle_digamma_term_summable hβ he W hW hA).congr hterm, ?_⟩
  rw [middle_digamma_exchange hβ he W hW hA, ← tsum_mul_left]
  exact tsum_congr hterm

/-- The reflected resolvent is a finite derivative sum at the cutoff.
The Laplace rate is `a + c + 2 * β` on the reflected line. -/
public theorem middle_gamma_reflect_derivatives (Q : Polynomial ℚ) {N : ℕ}
    (hQ : 2 * Q.natDegree + 3 ≤ N) {a c b x β : ℝ} (ha : 1 / 2 < a) (hc : 0 < c + a) (hβ : 0 < β)
    (hz : 0 ≤ b + x) :
    let l := fun t : ℝ ↦ (c : ℂ) + Complex.I * t
    let F := fun z ↦
      ∑ i ∈ Finset.Ico 3 (N + 1),
        ((Q ^ 2).coeff (N - i) : ℂ) *
          (LLS.PaperStatements.shiftedPoleKernel (max 1 i) a b (le_max_left _ _) ha).function z
    let W := fun t ↦ F (l t) * Complex.exp (l t * (x : ℂ))
    let P := (middlePoleProfile N Q).map (Rat.castHom ℝ)
    let z := b + x
    let d := a + c + 2 * β
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, (1 / ((β : ℂ) - Complex.I * ((t : ℂ) / 2))) * W t) =
      ((2 * Real.exp (-a * z) *
            ∑ j ∈ Finset.range (P.natDegree + 1),
              ((Polynomial.derivative^[j]) P).eval z / d ^ (j + 1) :
          ℝ) :
        ℂ) := by
  intro l F W P z d
  have hr := middle_gamma_resolvent Q hQ (b := b) (x := x) (ε := -1) ha hc hβ (Or.inr rfl)
  simp only [neg_one_mul, Complex.ofReal_neg, mul_neg, neg_div, ← sub_eq_add_neg,
    mul_div_assoc] at hr
  rw [hr]
  let G := fun v : ℝ ↦ ((Real.exp (-d * v) * P.eval (z + v) : ℝ) : ℂ)
  have he (u : ℝ) (hu : u ∈ Set.Ioi (0 : ℝ)) :
    (if 0 ≤ z - -(u / 2) then
        ((Real.exp ((-(c / 2) - β) * u - a * (z - -(u / 2))) *
              (middlePoleProfile N Q).eval₂ (Rat.castHom ℝ) (z - -(u / 2)) :
            ℝ) :
          ℂ)
      else 0) =
      (Real.exp (-a * z) : ℂ) * G ((1 / 2) * u) := by
    have hy : z - -(u / 2) = z + (1 / 2) * u := by ring
    have hy0 := add_nonneg hz (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 1 / 2) (le_of_lt hu))
    rw [hy, ite_eq_left hy0]
    simp only [G, P, Polynomial.eval_map, ← Complex.ofReal_mul, ← mul_assoc, ← Real.exp_add]
    rw [show (-(c / 2) - β) * u - a * (z + 1 / 2 * u) = -a * z + -d * (1 / 2) * u
        by
        dsimp only [d]
        ring]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi he, MeasureTheory.integral_const_mul]
  have hs := MeasureTheory.integral_comp_mul_left_Ioi G 0 (by norm_num only : (0 : ℝ) < 1 / 2)
  rw [mul_zero, show (1 / 2 : ℝ)⁻¹ = 2 by norm_num only, Complex.real_smul] at hs
  have hd : 0 < d := by
    dsimp only [d]; linarith only [hc, hβ]
  rw [hs]
  dsimp only [G]
  rw [integral_complex_ofReal, gamma_shift_moment_derivatives P z hd]
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

/-- Regroup the reflected digamma difference into a finite derivative series.
The constant coefficient stays as one convergent reciprocal difference. -/
public theorem middle_gamma_reflect_coeffs (Q : Polynomial ℚ) {N : ℕ} (hQ : 2 * Q.natDegree + 3 ≤ N)
    {a c b x β : ℝ} (ha : 1 / 2 < a) (ha1 : 1 ≤ a) (hl : -(9 / 16) ≤ c) (hr : c ≤ 9 / 16)
    (hne : c ≠ -1 / 2) (hβ : 0 < β) (hz : 0 ≤ b + x) :
    let l := fun t : ℝ ↦ (c : ℂ) + Complex.I * t
    let F := fun z ↦
      ∑ i ∈ Finset.Ico 3 (N + 1),
        ((Q ^ 2).coeff (N - i) : ℂ) *
          (LLS.PaperStatements.shiftedPoleKernel (max 1 i) a b (le_max_left _ _) ha).function z
    let W := fun t ↦ F (l t) * Complex.exp (l t * (x : ℂ))
    let P := (middlePoleProfile N Q).map (Rat.castHom ℝ)
    let z := b + x
    let d := a + c + 2 * β
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          (Complex.digamma ((β : ℂ) - Complex.I * ((t : ℂ) / 2)) - Complex.digamma (β : ℂ)) * W t) =
      ((2 * Real.exp (-a * z) *
            (P.eval z * (∑' n : ℕ, (1 / (2 * (β + n)) - 1 / (d + 2 * n))) +
              ∑ j ∈ Finset.range P.natDegree,
                (-((Polynomial.derivative^[j + 1]) P).eval z) *
                  (∑' n : ℕ, 1 / (d + 2 * n) ^ (j + 2))) :
          ℝ) :
        ℂ) := by
  intro l F W P z d
  have hc : 0 < c + a := by linarith only [ha1, hl]
  have hd : 0 < d := by
    dsimp only [d]; linarith only [hc, hβ]
  let v := fun j : ℕ ↦ ((Polynomial.derivative^[j]) P).eval z
  let f := fun n : ℕ ↦
    P.eval z * (1 / (2 * (β + n)) - 1 / (d + 2 * n)) +
      ∑ j ∈ Finset.range P.natDegree, (-v (j + 1)) / (d + 2 * n) ^ (j + 2)
  have hs :=
    gamma_pole_coefficients_tsum hβ hd P.natDegree (fun j ↦ if j = 0 then P.eval z else -v j)
  simp only [Nat.succ_ne_zero, ite_true, ite_false] at hs
  change (∑' n, f n) = _ at hs
  rw [← hs, Complex.ofReal_mul, Complex.ofReal_tsum f, ← tsum_mul_left]
  have hD := (middle_gamma_digamma_series Q hQ (ε := -1) ha ha1 hl hr hne hβ (Or.inr rfl) hz).2
  simp only [neg_one_mul, Complex.ofReal_neg, mul_neg, neg_div, ← sub_eq_add_neg,
    mul_div_assoc] at hD
  rw [hD]
  apply tsum_congr
  intro n
  have hβn := add_pos_of_pos_of_nonneg hβ (Nat.cast_nonneg (α := ℝ) n)
  have hR := middle_gamma_resolvent Q hQ (b := b) (x := x) (ε := -1) ha hc hβn (Or.inr rfl)
  simp only [neg_one_mul, Complex.ofReal_neg, mul_neg, neg_div, ← sub_eq_add_neg,
    mul_div_assoc] at hR
  have hM := hR.symm.trans (middle_gamma_reflect_derivatives Q hQ ha hc hβn hz)
  rw [hM]
  have hdn : a + c + 2 * (β + n) = d + 2 * n := by
    dsimp only [d]; ring
  rw [hdn, Finset.sum_range_succ', pow_one, Function.iterate_zero_apply]
  simp only [f, v, P, z, Polynomial.eval_map, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_ofNat,
    Complex.ofReal_one, neg_div, Finset.sum_neg_distrib]
  rw [div_mul_eq_div_div (1 : ℂ) (2 : ℂ)]
  ring

/-- A forward pole produces a finite Laplace moment on the physical support.
The moment is valid for either sign of the finite-interval exponent. -/
public theorem middle_gamma_forward_moment (Q : Polynomial ℚ) {N : ℕ} (hQ : 2 * Q.natDegree + 3 ≤ N)
    {a c b x β : ℝ} (ha : 1 / 2 < a) (hc : 0 < c + a) (hβ : 0 < β) (hz : 0 ≤ b + x) :
    let l := fun t : ℝ ↦ (c : ℂ) + Complex.I * t
    let F := fun z ↦
      ∑ i ∈ Finset.Ico 3 (N + 1),
        ((Q ^ 2).coeff (N - i) : ℂ) *
          (LLS.PaperStatements.shiftedPoleKernel (max 1 i) a b (le_max_left _ _) ha).function z
    let W := fun t ↦ F (l t) * Complex.exp (l t * (x : ℂ))
    let P := (middlePoleProfile N Q).map (Rat.castHom ℝ)
    let z := b + x
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, (1 / ((β : ℂ) + Complex.I * ((t : ℂ) / 2))) * W t) =
      ((2 * Real.exp (-a * z) *
            (∫ v in (0 : ℝ)..z, Real.exp ((a + c - 2 * β) * (z - v)) * P.eval v) :
          ℝ) :
        ℂ) := by
  intro l F W P z
  have h := middle_gamma_resolvent Q hQ (b := b) (x := x) (ε := 1) ha hc hβ (Or.inl rfl)
  simp only [one_mul, mul_div_assoc] at h
  rw [h]
  let G := fun v : ℝ ↦ ((Real.exp ((a + c - 2 * β) * (z - v)) * P.eval v : ℝ) : ℂ)
  have hterm (u : ℝ) :
    ((Real.exp ((c / 2 - β) * u - a * (z - u / 2)) *
            (middlePoleProfile N Q).eval₂ (Rat.castHom ℝ) (z - u / 2) :
          ℝ) :
        ℂ) =
      (Real.exp (-a * z) : ℂ) * G (z - u / 2) := by
    simp only [G, P, Polynomial.eval_map, ← Complex.ofReal_mul, ← mul_assoc, ← Real.exp_add]
    rw [show (c / 2 - β) * u - a * (z - u / 2) = -a * z + (a + c - 2 * β) * (z - (z - u / 2)) by
        ring]
  have ht :
    (∫ u in Set.Ioi (0 : ℝ), if 0 ≤ z - u / 2 then (Real.exp (-a * z) : ℂ) * G (z - u / 2) else 0) =
      ∫ u in (0 : ℝ)..(2 * z), (Real.exp (-a * z) : ℂ) * G (z - u / 2) := by
    rw [intervalIntegral.integral_of_le (mul_nonneg (by norm_num only) hz), ←
      MeasureTheory.integral_indicator measurableSet_Ioi, ←
      MeasureTheory.integral_indicator measurableSet_Ioc]
    apply MeasureTheory.integral_congr_ae
    refine MeasureTheory.ae_of_all _ fun u ↦ ?_
    by_cases hu : 0 < u
    · rw [Set.indicator_of_mem hu]
      by_cases hu₂ : u ≤ 2 * z
      · rw [Set.indicator_of_mem (show u ∈ Set.Ioc 0 (2 * z) from ⟨hu, hu₂⟩),
          ite_eq_left (by linarith only [hu₂] : 0 ≤ z - u / 2)]
      · rw [Set.indicator_of_notMem (fun h ↦ hu₂ h.2 : u ∉ Set.Ioc 0 (2 * z)),
          ite_eq_right (by linarith only [lt_of_not_ge hu₂] : ¬0 ≤ z - u / 2)]
    · rw [Set.indicator_of_notMem hu,
        Set.indicator_of_notMem (fun h ↦ hu h.1 : u ∉ Set.Ioc 0 (2 * z))]
  change
    (∫ u in Set.Ioi (0 : ℝ),
        if 0 ≤ z - u / 2 then
          ((Real.exp ((c / 2 - β) * u - a * (z - u / 2)) *
                (middlePoleProfile N Q).eval₂ (Rat.castHom ℝ) (z - u / 2) :
              ℝ) :
            ℂ)
        else 0) =
      _
  simp only [hterm]
  rw [ht, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_div G (by norm_num only : (2 : ℝ) ≠ 0) z]
  rw [show z - 2 * z / 2 = 0 by ring, zero_div, sub_zero, Complex.real_smul]
  dsimp only [G]
  rw [intervalIntegral.integral_ofReal]
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

/-- Once the decay rate is positive, a forward digamma summand is the sum
of a derivative term at the evaluation height and a decaying term at zero. -/
public theorem middle_forward_tail_term (P : Polynomial ℝ) {a c β z : ℝ} (hz : 0 ≤ z) (m n : ℕ)
    (hm : a + c < 2 * (β + m)) :
    let γ := β + ((n + m : ℕ) : ℝ)
    let d := 2 * γ - a - c
    let A := fun y : ℝ ↦
      ∑ j ∈ Finset.range (P.natDegree + 1),
        (-1 : ℝ) ^ j * ((Polynomial.derivative^[j]) P).eval y / d ^ (j + 1)
    Real.exp (-a * z) *
        (P.eval z / γ - 2 * (∫ v in (0 : ℝ)..z, Real.exp ((a + c - 2 * γ) * (z - v)) * P.eval v)) =
      Real.exp (-a * z) * (P.eval z / γ - 2 * A z + 2 * Real.exp (-d * z) * A 0) := by
  intro γ d A
  have hd : 0 < d := by
    dsimp only [d, γ]
    rw [Nat.cast_add]
    linarith only [hm, Nat.cast_nonneg (α := ℝ) n]
  have he : a + c - 2 * γ = -d := by
    dsimp only [d]
    ring
  rw [he, gamma_forward_decay_derivatives P hd hz]
  change Real.exp (-a * z) * (P.eval z / γ - 2 * (A z - Real.exp (-d * z) * A 0)) = _
  ring

/-- The forward digamma difference is a series of finite moments.
Split at `m` to retain low-index poles as individual finite moments and expand the tail. -/
public theorem middle_gamma_forward_series (Q : Polynomial ℚ) {N : ℕ} (hQ : 2 * Q.natDegree + 3 ≤ N)
    {a c b x β : ℝ} (ha : 1 / 2 < a) (ha1 : 1 ≤ a) (hl : -(9 / 16) ≤ c) (hr : c ≤ 9 / 16)
    (hne : c ≠ -1 / 2) (hβ : 0 < β) (hz : 0 < b + x) (m : ℕ) (hm : a + c < 2 * (β + m)) :
    let l := fun t : ℝ ↦ (c : ℂ) + Complex.I * t
    let F := fun z ↦
      ∑ i ∈ Finset.Ico 3 (N + 1),
        ((Q ^ 2).coeff (N - i) : ℂ) *
          (LLS.PaperStatements.shiftedPoleKernel (max 1 i) a b (le_max_left _ _) ha).function z
    let W := fun t ↦ F (l t) * Complex.exp (l t * (x : ℂ))
    let P := (middlePoleProfile N Q).map (Rat.castHom ℝ)
    let z := b + x
    let f := fun n : ℕ ↦
      ((Real.exp (-a * z) *
            (P.eval z / (β + n) -
              2 * (∫ v in (0 : ℝ)..z, Real.exp ((a + c - 2 * (β + n)) * (z - v)) * P.eval v)) :
          ℝ) :
        ℂ)
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          (Complex.digamma ((β : ℂ) + Complex.I * ((t : ℂ) / 2)) - Complex.digamma (β : ℂ)) * W t) =
      (∑ n ∈ Finset.range m, f n) +
        let β₀ := β + (m : ℝ)
        let d := 2 * β₀ - a - c
        ((2 * Real.exp (-a * z) *
              (P.eval z * (∑' n : ℕ, (1 / (2 * (β₀ + n)) - 1 / (d + 2 * n))) +
                (∑ j ∈ Finset.range P.natDegree,
                  (-((-1 : ℝ) ^ (j + 1) * ((Polynomial.derivative^[j + 1]) P).eval z)) *
                    (∑' n : ℕ, 1 / (d + 2 * n) ^ (j + 2))) +
                ∑' n : ℕ,
                  Real.exp (-(d + 2 * n) * z) *
                    ∑ j ∈ Finset.range (P.natDegree + 1),
                      (-1 : ℝ) ^ j * ((Polynomial.derivative^[j]) P).eval 0 /
                        (d + 2 * n) ^ (j + 1)) :
            ℝ) :
          ℂ) := by
  intro l F W P z f
  have hc : 0 < c + a := by linarith only [ha1, hl]
  obtain ⟨hs, hD⟩ :=
    middle_gamma_digamma_series Q hQ (ε := 1) ha ha1 hl hr hne hβ (Or.inl rfl) hz.le
  simp only [one_mul, mul_div_assoc] at hs
  simp only [one_mul, mul_div_assoc] at hD
  have hterm (n : ℕ) :
    ((Real.exp (-a * z) * P.eval z / (β + n) : ℝ) : ℂ) -
        (∫ u in Set.Ioi (0 : ℝ),
          if 0 ≤ z - u / 2 then
            ((Real.exp ((c / 2 - (β + n)) * u - a * (z - u / 2)) *
                  (middlePoleProfile N Q).eval₂ (Rat.castHom ℝ) (z - u / 2) :
                ℝ) :
              ℂ)
          else 0) =
      f n := by
    have hβn := add_pos_of_pos_of_nonneg hβ (Nat.cast_nonneg (α := ℝ) n)
    have hR := middle_gamma_resolvent Q hQ (b := b) (x := x) (ε := 1) ha hc hβn (Or.inl rfl)
    simp only [one_mul, mul_div_assoc] at hR
    have hm := hR.symm.trans (middle_gamma_forward_moment Q hQ ha hc hβn hz.le)
    rw [hm]
    simp only [f, P, z, Polynomial.eval_map, Complex.ofReal_mul, Complex.ofReal_div,
      Complex.ofReal_ofNat, Complex.ofReal_sub]
    ring
  simp only [P, z, Polynomial.eval_map, mul_div_assoc] at hterm
  rw [hD, tsum_congr hterm]
  rw [← (hs.congr hterm).sum_add_tsum_nat_add m]
  congr 1
  have hb₀ : 0 < β + (m : ℝ) := add_pos_of_pos_of_nonneg hβ (Nat.cast_nonneg m)
  have hd : 0 < 2 * (β + (m : ℝ)) - a - c := by linarith only [hm]
  have hz₀ : 0 < z := hz
  dsimp only
  rw [← gamma_forward_tail_tsum P hb₀ hd hz₀, Complex.ofReal_mul, Complex.ofReal_tsum, ←
    tsum_mul_left]
  apply tsum_congr
  intro n
  rw [← Complex.ofReal_mul]
  refine (congrArg Complex.ofReal (middle_forward_tail_term P hz.le m n hm)).trans ?_
  apply congrArg Complex.ofReal
  simp only [Nat.cast_add]
  rw [show β + ((n : ℝ) + m) = β + m + n by ring,
    show 2 * (β + (m : ℝ) + n) - a - c = 2 * (β + m) - a - c + 2 * n by ring]
  rw [div_mul_eq_div_div (P.eval z) (2 : ℝ) (β + m + n)]
  dsimp only [z]
  ring

/-- Bound the origin series of the middle forward tail uniformly for
physical heights from a positive cutoff, using only derivatives at zero. -/
public theorem middle_gamma_origin_le (Q : Polynomial ℚ) (N m : ℕ) {a c β z z₀ : ℝ}
    (hm : a + c < 2 * (β + m)) (hz₀ : 0 < z₀) (hz : z₀ ≤ z) :
    let P := (middlePoleProfile N Q).map (Rat.castHom ℝ)
    let d := 2 * (β + (m : ℝ)) - a - c
    |∑' n : ℕ,
          Real.exp (-(d + 2 * n) * z) *
            ∑ j ∈ Finset.range (P.natDegree + 1),
              (-1 : ℝ) ^ j * ((Polynomial.derivative^[j]) P).eval 0 / (d + 2 * n) ^ (j + 1)| ≤
      (∑ j ∈ Finset.range (P.natDegree + 1),
          |((Polynomial.derivative^[j]) P).eval 0| * (Real.exp (-d * z₀) / d ^ (j + 1))) /
        (1 - Real.exp (-2 * z₀)) := by
  intro P d
  have hd : 0 < d := by
    dsimp only [d]
    linarith only [hm]
  simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using
    gamma_origin_tsum_abs_le_from hd hz₀ hz (P.natDegree + 1)
      (fun j ↦ (-1 : ℝ) ^ j * ((Polynomial.derivative^[j]) P).eval 0)

/-- Isolate the first two forward poles for a middle-kernel pole between
one half and five halves. The first contributes a full residue at one half. -/
public theorem middle_gamma_head_moments (P : Polynomial ℝ) {a z : ℝ} (ha₀ : 1 / 2 < a)
    (ha₁ : a < 5 / 2) (hz : 0 ≤ z) :
    let M := fun y : ℝ ↦
      ∑ j ∈ Finset.range (P.natDegree + 1),
        ((Polynomial.derivative^[j]) P).eval y / (a - 1 / 2) ^ (j + 1)
    let V := fun y : ℝ ↦
      ∑ j ∈ Finset.range (P.natDegree + 1),
        (-1 : ℝ) ^ j * ((Polynomial.derivative^[j]) P).eval y / (5 / 2 - a) ^ (j + 1)
    Real.exp (-a * z) *
        ((∫ v in (0 : ℝ)..z, Real.exp ((a - 1 / 2) * (z - v)) * P.eval v) +
          ∫ v in (0 : ℝ)..z, Real.exp ((a - 5 / 2) * (z - v)) * P.eval v) =
      Real.exp (-(1 / 2) * z) * M 0 +
        Real.exp (-a * z) * (V z - M z - Real.exp (-(5 / 2 - a) * z) * V 0) := by
  intro M V
  rw [mul_add, gamma_growing_moment ha₀ hz, show a - 5 / 2 = -(5 / 2 - a) by ring,
    gamma_forward_decay_derivatives P (sub_pos.mpr ha₁) hz]
  change
    Real.exp (-(1 / 2) * z) * M 0 - Real.exp (-a * z) * M z +
        Real.exp (-a * z) * (V z - Real.exp (-(5 / 2 - a) * z) * V 0) =
      _
  ring

/-- On the K156 physical height range through `135/4`, bound the second
forward pole with a Taylor polynomial and a uniform factorial remainder. -/
public theorem middle_k156_second_pole_error (P : Polynomial ℝ) {z M : ℝ} (hz : 0 ≤ z)
    (hz' : z ≤ 135 / 4) (hM : ∀ v ∈ Set.Icc 0 z, |P.eval v| ≤ M) (m : ℕ) :
    let T := fun v : ℝ ↦
      ∑ j ∈ Finset.range (m + 1), ((-(1 / 20 : ℝ)) ^ j / (j.factorial : ℝ)) * (z - v) ^ j
    |(∫ v in (0 : ℝ)..z, Real.exp (-(1 / 20 : ℝ) * (z - v)) * P.eval v) -
          ∫ v in (0 : ℝ)..z, T v * P.eval v| ≤
      (((27 / 16 : ℝ)) ^ (m + 1) / ((m + 1).factorial : ℝ)) * M * (135 / 4) := by
  intro T
  have hM₀ := (abs_nonneg (P.eval 0)).trans (hM 0 ⟨le_rfl, hz⟩)
  refine (gamma_forward_taylor_error P (d := 1 / 20) (by norm_num only) hz hM m).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ hz |>.trans (mul_le_mul_of_nonneg_left hz' ?_)
  · exact
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right
          (pow_le_pow_left₀ (mul_nonneg (by norm_num only) hz) (by linarith only [hz']) _)
          (Nat.cast_nonneg _))
        hM₀
  · exact mul_nonneg (div_nonneg (pow_nonneg (by norm_num only) _) (Nat.cast_nonneg _)) hM₀

/-- Each forward contour pole with positive real denominator is integrable
and contributes a finite physical convolution. -/
private theorem middle_forward_pole (Q : Polynomial ℚ) {N : ℕ} (hQ : 2 * Q.natDegree + 3 ≤ N)
    {a b x q : ℝ} (ha : 1 ≤ a) (hq : -(9 / 16) < q) (hz : 0 ≤ b + x) :
    let ha' : 1 / 2 < a := (by norm_num only : (1 / 2 : ℝ) < 1).trans_le ha
    let l := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
    let F := fun z ↦
      ∑ i ∈ Finset.Ico 3 (N + 1),
        ((Q ^ 2).coeff (N - i) : ℂ) *
          (LLS.PaperStatements.shiftedPoleKernel (max 1 i) a b (le_max_left _ _) ha').function z
    let W := fun t ↦ F (l t) * Complex.exp (l t * (x : ℂ))
    let P := (middlePoleProfile N Q).map (Rat.castHom ℝ)
    let z := b + x
    MeasureTheory.Integrable (fun t : ℝ ↦ (l t + (q : ℂ))⁻¹ * W t) ∧
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, (l t + (q : ℂ))⁻¹ * W t) =
        ((Real.exp (-a * z) * (∫ v in (0 : ℝ)..z, Real.exp ((a - q) * (z - v)) * P.eval v) : ℝ) :
          ℂ) := by
  intro ha' l F W P z
  have hc : 0 < 9 / 16 + a := by linarith only [ha]
  have hl : -(9 / 16 : ℝ) ≤ 9 / 16 := by norm_num only
  have hn : (9 / 16 : ℝ) ≠ -1 / 2 := by norm_num only
  let β : ℝ := (9 / 16 + q) / 2
  have hβ : 0 < β := by
    dsimp only [β]; linarith only [hq]
  have he (t : ℝ) :
    (l t + (q : ℂ))⁻¹ = (2 : ℂ)⁻¹ * (1 / ((β : ℂ) + Complex.I * ((t : ℂ) / 2))) := by
    rw [one_div, ← mul_inv]
    congr 1
    simp only [l, β, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_ofNat]
    ring
  obtain ⟨hW, hiW⟩ := middle_pole_weight_regular Q N ha' hc b x
  obtain ⟨A, hA⟩ := middle_pole_weight_quadratic Q N ha' ha hl le_rfl hn b x
  change MeasureTheory.Integrable W at hiW
  have hi :=
    (hiW.const_mul (1 / (β : ℂ))).sub
      (LLS.PaperStatements.quadratic_resolvent_integral_bound hβ W hW hA).1
  have hi₁ :
    MeasureTheory.Integrable (fun t : ℝ ↦ (1 / ((β : ℂ) + Complex.I * ((t : ℂ) / 2))) * W t) := by
    simpa only [Pi.sub_def, sub_mul, sub_sub_cancel, Complex.ofReal_div, Complex.ofReal_ofNat,
      mul_div_assoc] using hi
  refine ⟨by simpa only [he, mul_assoc] using hi₁.const_mul ((2 : ℂ)⁻¹), ?_⟩
  have hM := middle_gamma_forward_moment Q hQ ha' hc hβ hz
  simp only [he, mul_assoc, MeasureTheory.integral_const_mul, mul_left_comm _ ((2 : ℂ)⁻¹)]
  rw [hM,
    show a + 9 / 16 - 2 * β = a - q by
      dsimp only [β]; ring]
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

/-- The middle forward Gamma contour splits into its shifted baseline,
digamma difference and the two finite convolutions at the isolated poles. -/
public theorem middle_gamma_forward_split (Q : Polynomial ℚ) {N : ℕ} (hQ : 2 * Q.natDegree + 3 ≤ N)
    {a b x : ℝ} (ha : 1 ≤ a) (hz : 0 ≤ b + x) :
    let ha' : 1 / 2 < a := (by norm_num only : (1 / 2 : ℝ) < 1).trans_le ha
    let l := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
    let F := fun z ↦
      ∑ i ∈ Finset.Ico 3 (N + 1),
        ((Q ^ 2).coeff (N - i) : ℂ) *
          (LLS.PaperStatements.shiftedPoleKernel (max 1 i) a b (le_max_left _ _) ha').function z
    let W := fun t ↦ F (l t) * Complex.exp (l t * (x : ℂ))
    let P := (middlePoleProfile N Q).map (Rat.castHom ℝ)
    let z := b + x
    let β := ((81 / 32 : ℝ) : ℂ)
    let B := (Complex.digamma β - Complex.log (Real.pi : ℂ)) / 2
    let E := fun t : ℝ ↦ Complex.digamma (β + Complex.I * ((t : ℂ) / 2)) - Complex.digamma β
    let D := ((1 / (2 * Real.pi) : ℝ) : ℂ)
    let M := fun q : ℝ ↦
      ((Real.exp (-a * z) * (∫ v in (0 : ℝ)..z, Real.exp ((a - q) * (z - v)) * P.eval v) : ℝ) : ℂ)
    D * (∫ t : ℝ, logDeriv Complex.Gammaℝ (l t + 1 / 2) * W t) =
      B * ((Real.exp (-a * z) * P.eval z : ℝ) : ℂ) + (2 : ℂ)⁻¹ * (D * ∫ t : ℝ, E t * W t) -
        M (1 / 2) -
        M (5 / 2) := by
  intro ha' l F W P z β B E D M
  have hc : 0 < 9 / 16 + a := by linarith only [ha]
  have hl : -(9 / 16 : ℝ) ≤ 9 / 16 := by norm_num only
  have hn : (9 / 16 : ℝ) ≠ -1 / 2 := by norm_num only
  obtain ⟨hW, hiW⟩ := middle_pole_weight_regular Q N ha' hc b x
  obtain ⟨A, hA⟩ := middle_pole_weight_quadratic Q N ha' ha hl le_rfl hn b x
  have hE : MeasureTheory.Integrable (fun t ↦ E t * W t) := by
    have h :=
      (LLS.PaperStatements.integrable_quadratic_reflected_digamma
          (by norm_num only : (0 : ℝ) < 81 / 32) (fun t ↦ W (-t)) (hW.comp continuous_neg)
          (fun t ↦ by simpa only [neg_sq] using hA (-t))).comp_neg
    simpa only [E, β, neg_neg, Complex.ofReal_neg, neg_div, mul_neg, sub_neg_eq_add,
      Complex.ofReal_div, Complex.ofReal_ofNat] using h
  obtain ⟨hp, hP⟩ := middle_forward_pole Q hQ (q := 1 / 2) ha (by norm_num only) hz
  obtain ⟨hq, hQ'⟩ := middle_forward_pole Q hQ (q := 5 / 2) ha (by norm_num only) hz
  have hp' : MeasureTheory.Integrable (fun t ↦ (l t + 1 / 2)⁻¹ * W t) := by
    simpa only [l, W, F, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using hp
  have hq' : MeasureTheory.Integrable (fun t ↦ (l t + 5 / 2)⁻¹ * W t) := by
    simpa only [l, W, F, Complex.ofReal_div, Complex.ofReal_ofNat] using hq
  have hsplit := gamma_forward_integral_split W hiW hE hp' hq'
  change
    (∫ t : ℝ, logDeriv Complex.Gammaℝ (l t + 1 / 2) * W t) =
      B * (∫ t : ℝ, W t) + (2 : ℂ)⁻¹ * (∫ t : ℝ, E t * W t) - (∫ t : ℝ, (l t + 1 / 2)⁻¹ * W t) -
        ∫ t : ℝ, (l t + 5 / 2)⁻¹ * W t at hsplit
  have hBase : D * (∫ t : ℝ, W t) = ((Real.exp (-a * z) * P.eval z : ℝ) : ℂ) :=
    (middle_gamma_weight_integral Q hQ ha' hc hz).trans (by rw [Polynomial.eval_map])
  have hP₀ : D * (∫ t : ℝ, (l t + 1 / 2)⁻¹ * W t) = M (1 / 2) := by
    simpa only [l, W, F, D, M, P, z, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat] using hP
  have hQ₀ : D * (∫ t : ℝ, (l t + 5 / 2)⁻¹ * W t) = M (5 / 2) := by
    simpa only [l, W, F, D, M, P, z, Complex.ofReal_div, Complex.ofReal_ofNat] using hQ'
  rw [hsplit, mul_sub, mul_sub, mul_add, mul_left_comm _ B, mul_left_comm _ ((2 : ℂ)⁻¹), hBase, hP₀,
    hQ₀]

/-- The reflected middle Gamma contour equals a derivative sum at the
physical height, including the zeroth coefficient at the shifted pole. -/
public theorem middle_gamma_reflect_logDeriv (Q : Polynomial ℚ) {N : ℕ}
    (hQ : 2 * Q.natDegree + 3 ≤ N) {a b x : ℝ} (ha : 1 ≤ a) (hz : 0 ≤ b + x) :
    let ha' : 1 / 2 < a := (by norm_num only : (1 / 2 : ℝ) < 1).trans_le ha
    let l := fun t : ℝ ↦ ((-(9 / 16) : ℝ) : ℂ) + Complex.I * t
    let F := fun z ↦
      ∑ i ∈ Finset.Ico 3 (N + 1),
        ((Q ^ 2).coeff (N - i) : ℂ) *
          (LLS.PaperStatements.shiftedPoleKernel (max 1 i) a b (le_max_left _ _) ha').function z
    let W := fun t ↦ F (l t) * Complex.exp (l t * (x : ℂ))
    let P := (middlePoleProfile N Q).map (Rat.castHom ℝ)
    let z := b + x
    let d := a + 1 / 2
    (((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, logDeriv Complex.Gammaℝ (1 / 2 - l t) * W t)).re =
      Real.exp (-a * z) *
        (((Complex.digamma ((d / 2 : ℝ) : ℂ)).re - Real.log Real.pi) / 2 * P.eval z -
          ∑ j ∈ Finset.range P.natDegree,
            ((Polynomial.derivative^[j + 1]) P).eval z *
              (∑' n : ℕ, 1 / (d + 2 * n) ^ (j + 2))) := by
  intro ha' l F W P z d
  let β : ℝ := 17 / 32
  let e := fun t : ℝ ↦
    Complex.digamma ((β : ℂ) - Complex.I * ((t : ℂ) / 2)) - Complex.digamma (β : ℂ)
  let B := (Complex.digamma (β : ℂ) - Complex.log (Real.pi : ℂ)) / 2
  have hb : 0 < β := by norm_num only [β]
  have hd : 0 < d := by
    dsimp only [d]; linarith only [ha]
  have he (t : ℝ) : (1 / 2 - l t) / 2 = (β : ℂ) - Complex.I * ((t : ℂ) / 2) := by
    simp only [l, β, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat]
    ring
  have hg (t : ℝ) : logDeriv Complex.Gammaℝ (1 / 2 - l t) = B + e t / 2 := by
    have hp : 0 < ((1 / 2 - l t) / 2).re := by
      rw [he]
      norm_num only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.div_ofNat_im, Complex.ofReal_im, zero_div, zero_mul, one_mul, sub_zero, β]
    rw [AnalyticNumberTheory.DirichletLFunction.logDeriv_Gammaℝ_of_half_ne_neg_nat
        (AnalyticNumberTheory.Gamma.not_neg_nat_of_re_pos hp),
      he]
    dsimp only [B, e]
    ring
  have hc : 0 < -(9 / 16) + a := by linarith only [ha]
  have hu : (-(9 / 16) : ℝ) ≤ 9 / 16 := by norm_num only
  have hn : (-(9 / 16) : ℝ) ≠ -1 / 2 := by norm_num only
  obtain ⟨hW, hiW⟩ := middle_pole_weight_regular Q N ha' hc b x
  obtain ⟨A, hA⟩ := middle_pole_weight_quadratic Q N ha' ha le_rfl hu hn b x
  change Continuous W at hW
  change MeasureTheory.Integrable W at hiW
  have hi : MeasureTheory.Integrable (fun t ↦ e t * W t) := by
    simpa only [e, Complex.ofReal_div, Complex.ofReal_ofNat] using
      LLS.PaperStatements.integrable_quadratic_reflected_digamma hb W hW hA
  have hk : a + -(9 / 16) + 2 * β = d := by
    dsimp only [β, d]; ring
  have hv := middle_gamma_reflect_coeffs Q hQ ha' ha le_rfl hu hn hb hz
  simp only [hk, gamma_pole_diff_tsum hb hd] at hv
  have hbase :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, W t) = ((Real.exp (-a * z) * P.eval z : ℝ) : ℂ) :=
    (middle_gamma_weight_integral Q hQ ha' hc hz).trans (by rw [Polynomial.eval_map])
  simp only [hg, add_mul, div_eq_mul_inv (e _) 2, mul_comm (e _) ((2 : ℂ)⁻¹), mul_assoc]
  rw [MeasureTheory.integral_add (hiW.const_mul B) (hi.const_mul _),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, mul_add, mul_left_comm _ B,
    mul_left_comm _ ((2 : ℂ)⁻¹), hbase]
  rw [show ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, e t * W t) = _ from hv]
  have hB : B.re = ((Complex.digamma (β : ℂ)).re - Real.log Real.pi) / 2 := by
    dsimp only [B]
    rw [Complex.div_ofNat_re, Complex.sub_re, Complex.log_ofReal_re]
  simp only [← Complex.ofReal_ofNat, ← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, Complex.add_re, hB, neg_mul, Finset.sum_neg_distrib]
  ring

/-- The forward middle Gamma contour is the shifted derivative series,
the origin series and the two isolated finite pole moments. -/
public theorem middle_gamma_forward_logDeriv (Q : Polynomial ℚ) {N : ℕ}
    (hQ : 2 * Q.natDegree + 3 ≤ N) {a b x : ℝ} (ha : 1 ≤ a) (ha₁ : a < 9 / 2) (hz : 0 < b + x) :
    let ha' : 1 / 2 < a := (by norm_num only : (1 / 2 : ℝ) < 1).trans_le ha
    let l := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
    let F := fun z ↦
      ∑ i ∈ Finset.Ico 3 (N + 1),
        ((Q ^ 2).coeff (N - i) : ℂ) *
          (LLS.PaperStatements.shiftedPoleKernel (max 1 i) a b (le_max_left _ _) ha').function z
    let W := fun t ↦ F (l t) * Complex.exp (l t * (x : ℂ))
    let P := (middlePoleProfile N Q).map (Rat.castHom ℝ)
    let z := b + x
    let d := 9 / 2 - a
    let T :=
      ∑' n : ℕ,
        Real.exp (-(d + 2 * n) * z) *
          ∑ j ∈ Finset.range (P.natDegree + 1),
            (-1 : ℝ) ^ j * ((Polynomial.derivative^[j]) P).eval 0 / (d + 2 * n) ^ (j + 1)
    let M := fun q : ℝ ↦ ∫ v in (0 : ℝ)..z, Real.exp ((a - q) * (z - v)) * P.eval v
    (((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, logDeriv Complex.Gammaℝ (l t + 1 / 2) * W t)).re =
      Real.exp (-a * z) *
        (((Complex.digamma ((d / 2 : ℝ) : ℂ)).re - Real.log Real.pi) / 2 * P.eval z -
              (∑ j ∈ Finset.range P.natDegree,
                (-1 : ℝ) ^ (j + 1) * ((Polynomial.derivative^[j + 1]) P).eval z *
                  (∑' n : ℕ, 1 / (d + 2 * n) ^ (j + 2))) +
            T -
          M (1 / 2) -
          M (5 / 2)) := by
  intro ha' l F W P z d T M
  let β : ℝ := 81 / 32
  have hβ : 0 < β := by norm_num only [β]
  have hd : 0 < d := sub_pos.mpr ha₁
  have hl : -(9 / 16 : ℝ) ≤ 9 / 16 := by norm_num only
  have hn : (9 / 16 : ℝ) ≠ -1 / 2 := by norm_num only
  have hm : a + 9 / 16 < 2 * (β + (0 : ℕ)) := by
    norm_num only [β, Nat.cast_zero, add_zero]
    linarith only [ha₁]
  have hk : 2 * β - a - 9 / 16 = d := by
    dsimp only [β, d]; ring
  have hs := middle_gamma_forward_series Q hQ ha' ha hl le_rfl hn hβ hz 0 hm
  simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, add_zero, zero_add, hk,
    gamma_pole_diff_tsum hβ hd, neg_mul, Finset.sum_neg_distrib] at hs
  have hsplit := middle_gamma_forward_split Q hQ ha hz.le
  dsimp only at hsplit
  rw [hsplit, hs]
  dsimp only [T, M, β, P, z]
  have hB :
    (((Complex.digamma (((81 / 32 : ℝ) : ℂ)) - Complex.log (Real.pi : ℂ)) / 2) : ℂ).re =
      ((Complex.digamma (((81 / 32 : ℝ) : ℂ))).re - Real.log Real.pi) / 2 := by
    rw [Complex.div_ofNat_re, Complex.sub_re, Complex.log_ofReal_re]
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re _ (Complex.ofReal _), hB]
  simp only [← Complex.ofReal_ofNat, ← Complex.ofReal_inv, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  ring_nf

/-- Combine the middle forward and reflected Gamma contours at the same
height. Only the forward contour contributes isolated poles and an origin series. -/
public theorem middle_gamma_contour_sum (Q : Polynomial ℚ) {N : ℕ} (hQ : 2 * Q.natDegree + 3 ≤ N)
    {a b x : ℝ} (ha : 1 ≤ a) (ha₁ : a < 9 / 2) (hz : 0 < b + x) :
    let ha' : 1 / 2 < a := (by norm_num only : (1 / 2 : ℝ) < 1).trans_le ha
    let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
    let l := fun t : ℝ ↦ ((-(9 / 16) : ℝ) : ℂ) + Complex.I * t
    let F := fun s ↦
      ∑ i ∈ Finset.Ico 3 (N + 1),
        ((Q ^ 2).coeff (N - i) : ℂ) *
          (LLS.PaperStatements.shiftedPoleKernel (max 1 i) a b (le_max_left _ _) ha').function s
    let W := fun s : ℂ ↦ F s * Complex.exp (s * (x : ℂ))
    let P := (middlePoleProfile N Q).map (Rat.castHom ℝ)
    let z := b + x
    let d := 9 / 2 - a
    let e := a + 1 / 2
    let B :=
      ((Complex.digamma ((d / 2 : ℝ) : ℂ)).re + (Complex.digamma ((e / 2 : ℝ) : ℂ)).re) / 2 -
        Real.log Real.pi
    let C := fun j : ℕ ↦
      -((-1 : ℝ) ^ (j + 1) * (∑' n : ℕ, 1 / (d + 2 * n) ^ (j + 2))) -
        ∑' n : ℕ, 1 / (e + 2 * n) ^ (j + 2)
    let T :=
      ∑' n : ℕ,
        Real.exp (-(d + 2 * n) * z) *
          ∑ j ∈ Finset.range (P.natDegree + 1),
            (-1 : ℝ) ^ j * ((Polynomial.derivative^[j]) P).eval 0 / (d + 2 * n) ^ (j + 1)
    let M := fun q : ℝ ↦ ∫ v in (0 : ℝ)..z, Real.exp ((a - q) * (z - v)) * P.eval v
    let D := ((1 / (2 * Real.pi) : ℝ) : ℂ)
    (D * (∫ t : ℝ, logDeriv Complex.Gammaℝ (r t + 1 / 2) * W (r t))).re +
        (D * (∫ t : ℝ, logDeriv Complex.Gammaℝ (1 / 2 - l t) * W (l t))).re =
      Real.exp (-a * z) *
        (B * P.eval z +
            (∑ j ∈ Finset.range P.natDegree, C j * ((Polynomial.derivative^[j + 1]) P).eval z) +
            T -
          M (1 / 2) -
          M (5 / 2)) := by
  intro ha' r l F W P z d e B C T M D
  rw [middle_gamma_forward_logDeriv Q hQ ha ha₁ hz, middle_gamma_reflect_logDeriv Q hQ ha hz.le]
  dsimp only [B, C, T, M, P, z, d, e]
  simp only [sub_mul, neg_mul, Finset.sum_sub_distrib, Finset.sum_neg_distrib, mul_assoc, mul_comm,
    mul_left_comm]
  ring

/-- At the origin, the factorial in the profile coefficients cancels with
the derivative factorial, leaving the corresponding reversed square coefficient. -/
private theorem middle_origin_derivative (Q : Polynomial ℚ) {N j : ℕ} (hj : j ≤ N) :
    ((Polynomial.derivative^[j]) ((middlePoleProfile N Q).map (Rat.castHom ℝ))).eval 0 =
      ((Q ^ 2).coeff (N - j) : ℝ) := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative, zero_add,
    Nat.descFactorial_self, nsmul_eq_mul, Polynomial.coeff_map, Rat.coe_castHom]
  have h : (middlePoleProfile N Q).coeff j = (Q ^ 2).coeff (N - j) / j.factorial := by
    simp only [middlePoleProfile, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))]
    · rw [Finsupp.single_eq_same]
    · intro k _ hk
      rw [Finsupp.single_eq_of_ne hk.symm]
  rw [h, Rat.cast_div, Rat.cast_natCast, mul_div_cancel₀]
  exact (Nat.cast_pos.mpr (Nat.factorial_pos j)).ne'

/-- At any nonzero rate the finite derivative transform of the middle
profile is the square of the compact kernel polynomial divided by a power. -/
public theorem middle_origin_transform (Q : Polynomial ℚ) {N : ℕ} (hQ : 2 * Q.natDegree ≤ N) {s : ℝ}
    (hs : s ≠ 0) :
    let P := (middlePoleProfile N Q).map (Rat.castHom ℝ)
    (∑ j ∈ Finset.range (P.natDegree + 1), ((Polynomial.derivative^[j]) P).eval 0 / s ^ (j + 1)) =
      (Q.eval₂ (Rat.castHom ℝ) s) ^ 2 / s ^ (N + 1) := by
  intro P
  have hd : P.natDegree ≤ N := by
    refine Polynomial.natDegree_map_le.trans ?_
    unfold middlePoleProfile
    exact
      Polynomial.natDegree_sum_le_of_forall_le _ _ fun j hj ↦
        (Polynomial.natDegree_monomial_le _).trans (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
  have he :
    (Q.eval₂ (Rat.castHom ℝ) s) ^ 2 =
      ∑ j ∈ Finset.range (N + 1), ((Q ^ 2).coeff j : ℝ) * s ^ j := by
    rw [← Polynomial.eval₂_pow,
      Polynomial.eval₂_eq_sum_range' (f := Rat.castHom ℝ)
        (Nat.lt_succ_of_le (Polynomial.natDegree_pow_le.trans hQ))]
    rfl
  have hpad :
    (∑ j ∈ Finset.range (P.natDegree + 1), ((Polynomial.derivative^[j]) P).eval 0 / s ^ (j + 1)) =
      ∑ j ∈ Finset.range (N + 1), ((Polynomial.derivative^[j]) P).eval 0 / s ^ (j + 1) := by
    apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hd))
    intro j _ hj
    have hlt : P.natDegree < j :=
      Nat.lt_of_succ_le (not_lt.mp (fun h ↦ hj (Finset.mem_range.mpr h)))
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative, zero_add,
      Polynomial.coeff_eq_zero_of_natDegree_lt hlt, smul_zero, zero_div]
  rw [hpad, he, Finset.sum_div]
  rw [← Finset.sum_range_reflect (fun j ↦ ((Q ^ 2).coeff j : ℝ) * s ^ j / s ^ (N + 1))]
  apply Finset.sum_congr rfl
  intro j hj
  have hj₀ : j ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  rw [middle_origin_derivative Q hj₀]
  simp only [Nat.add_sub_cancel]
  have hp : N + 1 = (j + 1) + (N - j) := by rw [Nat.add_right_comm, Nat.add_sub_of_le hj₀]
  have hpow : s ^ (N + 1) = s ^ (j + 1) * s ^ (N - j) := (congrArg (s ^ ·) hp).trans (pow_add s _ _)
  rw [hpow, mul_div_mul_right _ _ (pow_ne_zero _ hs)]

/-- The alternating derivative sum is the negative square transform at
the negative rate. This determines the sign of the forward origin terms. -/
public theorem middle_origin_alternating (Q : Polynomial ℚ) {N : ℕ} (hQ : 2 * Q.natDegree ≤ N)
    {d : ℝ} (hd : 0 < d) :
    let P := (middlePoleProfile N Q).map (Rat.castHom ℝ)
    (∑ j ∈ Finset.range (P.natDegree + 1),
        (-1 : ℝ) ^ j * ((Polynomial.derivative^[j]) P).eval 0 / d ^ (j + 1)) =
      -(Q.eval₂ (Rat.castHom ℝ) (-d)) ^ 2 / (-d) ^ (N + 1) := by
  intro P
  rw [neg_div, ← middle_origin_transform Q hQ (neg_ne_zero.mpr hd.ne'), ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [show (-d) ^ (j + 1) = -((-1 : ℝ) ^ j * d ^ (j + 1)) by
      rw [neg_eq_neg_one_mul d, mul_pow, pow_succ (-1 : ℝ), mul_neg_one, neg_mul]]
  rw [div_neg, neg_neg, div_mul_eq_div_div, div_eq_mul_inv _ ((-1 : ℝ) ^ j), ← inv_pow, inv_neg,
    inv_one, mul_comm ((-1 : ℝ) ^ j)]

/-- When the reversed pole order is even, every forward origin term
is nonpositive, so the entire convergent correction can be omitted in an upper bound. -/
public theorem middle_gamma_origin_nonpos (Q : Polynomial ℚ) {N : ℕ} (hQ : 2 * Q.natDegree ≤ N)
    (hN : Even (N + 1)) {d z : ℝ} (hd : 0 < d) :
    let P := (middlePoleProfile N Q).map (Rat.castHom ℝ)
    (∑' n : ℕ,
        Real.exp (-(d + 2 * n) * z) *
          ∑ j ∈ Finset.range (P.natDegree + 1),
            (-1 : ℝ) ^ j * ((Polynomial.derivative^[j]) P).eval 0 / (d + 2 * n) ^ (j + 1)) ≤
      0 := by
  intro P
  apply tsum_nonpos
  intro n
  have hn : 0 < d + 2 * (n : ℝ) := by linarith only [hd, Nat.cast_nonneg (α := ℝ) n]
  rw [middle_origin_alternating Q hQ hn]
  exact
    mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (hN.pow_nonneg _))

/-- For an even pole order the origin series can be dropped from the
combined upper bound. The first-pole residue is an exact compact square. -/
public theorem middle_gamma_contour_le (Q : Polynomial ℚ) {N : ℕ} (hQ : 2 * Q.natDegree + 3 ≤ N)
    {a b x : ℝ} (hN : Even (N + 1)) (ha : 1 ≤ a) (ha₁ : a < 9 / 2) (hz : 0 < b + x) :
    let ha' : 1 / 2 < a := (by norm_num only : (1 / 2 : ℝ) < 1).trans_le ha
    let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
    let l := fun t : ℝ ↦ ((-(9 / 16) : ℝ) : ℂ) + Complex.I * t
    let F := fun s ↦
      ∑ i ∈ Finset.Ico 3 (N + 1),
        ((Q ^ 2).coeff (N - i) : ℂ) *
          (LLS.PaperStatements.shiftedPoleKernel (max 1 i) a b (le_max_left _ _) ha').function s
    let W := fun s : ℂ ↦ F s * Complex.exp (s * (x : ℂ))
    let P := (middlePoleProfile N Q).map (Rat.castHom ℝ)
    let z := b + x
    let d := 9 / 2 - a
    let e := a + 1 / 2
    let B :=
      ((Complex.digamma ((d / 2 : ℝ) : ℂ)).re + (Complex.digamma ((e / 2 : ℝ) : ℂ)).re) / 2 -
        Real.log Real.pi
    let C := fun j : ℕ ↦
      -((-1 : ℝ) ^ (j + 1) * (∑' n : ℕ, 1 / (d + 2 * n) ^ (j + 2))) -
        ∑' n : ℕ, 1 / (e + 2 * n) ^ (j + 2)
    let L :=
      ∑ j ∈ Finset.range (P.natDegree + 1),
        ((Polynomial.derivative^[j]) P).eval z / (a - 1 / 2) ^ (j + 1)
    let M := fun q : ℝ ↦ ∫ v in (0 : ℝ)..z, Real.exp ((a - q) * (z - v)) * P.eval v
    let D := ((1 / (2 * Real.pi) : ℝ) : ℂ)
    (D * (∫ t : ℝ, logDeriv Complex.Gammaℝ (r t + 1 / 2) * W (r t))).re +
        (D * (∫ t : ℝ, logDeriv Complex.Gammaℝ (1 / 2 - l t) * W (l t))).re ≤
      Real.exp (-a * z) *
          (B * P.eval z +
              (∑ j ∈ Finset.range P.natDegree, C j * ((Polynomial.derivative^[j + 1]) P).eval z) +
              L -
            M (5 / 2)) -
        Real.exp (-(1 / 2) * z) * (Q.eval₂ (Rat.castHom ℝ) (a - 1 / 2)) ^ 2 /
          (a - 1 / 2) ^ (N + 1) := by
  intro ha' r l F W P z d e B C L M D
  have hd : 0 < d := sub_pos.mpr ha₁
  have hdeg : 2 * Q.natDegree ≤ N := (Nat.le_add_right _ _).trans hQ
  have hT := middle_gamma_origin_nonpos Q hdeg hN (d := d) (z := z) hd
  have h₁ := gamma_growing_moment (P := P) (a := a) (q := 1 / 2) ha' hz.le
  dsimp only at h₁
  rw [middle_origin_transform Q hdeg (sub_ne_zero.mpr ha'.ne')] at h₁
  rw [middle_gamma_contour_sum Q hQ ha ha₁ hz]
  dsimp only [B, C, L, M, P, z, d, e] at hT h₁ ⊢
  have hE := mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos (-a * (b + x))).le hT
  linear_combination hE - h₁

/-- At positive decay the second pole has an alternating derivative sum
and a compact square residue, both with exact coefficients. -/
public theorem middle_gamma_decay_square (Q : Polynomial ℚ) {N : ℕ} (hQ : 2 * Q.natDegree ≤ N)
    {d z : ℝ} (hd : 0 < d) (hz : 0 ≤ z) :
    let P := (middlePoleProfile N Q).map (Rat.castHom ℝ)
    (∫ v in (0 : ℝ)..z, Real.exp (-d * (z - v)) * P.eval v) =
      (∑ j ∈ Finset.range (P.natDegree + 1),
          (-1 : ℝ) ^ j * ((Polynomial.derivative^[j]) P).eval z / d ^ (j + 1)) +
        Real.exp (-d * z) * ((Q.eval₂ (Rat.castHom ℝ) (-d)) ^ 2 / (-d) ^ (N + 1)) := by
  intro P
  rw [gamma_forward_decay_derivatives P hd hz, middle_origin_alternating Q hQ hd]
  simp only [neg_div, mul_neg, sub_neg_eq_add]

/-- Bound both K141 Gamma contours. Both isolated pole residues
are retained as compact squares. -/
public theorem middle_k141_gamma_contour_le {x : ℝ} (hx : 20 ≤ x) :
    let a : ℝ := 2
    let b : ℝ := 7 / 2
    let ha : 1 / 2 < a := by norm_num only [a]
    let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
    let l := fun t : ℝ ↦ ((-(9 / 16) : ℝ) : ℂ) + Complex.I * t
    let F := fun s ↦
      ∑ i ∈ Finset.Ico 3 32,
        ((middleK141Kernel ^ 2).coeff (31 - i) : ℂ) *
          (LLS.PaperStatements.shiftedPoleKernel (max 1 i) a b (le_max_left _ _) ha).function s
    let W := fun s : ℂ ↦ F s * Complex.exp (s * (x : ℂ))
    let P := middleK141Profile.map (Rat.castHom ℝ)
    let z := b + x
    let D := ((1 / (2 * Real.pi) : ℝ) : ℂ)
    let κ := (middleK141Norm : ℝ)
    κ *
        ((D * (∫ t : ℝ, logDeriv Complex.Gammaℝ (r t + 1 / 2) * W (r t))).re +
          (D * (∫ t : ℝ, logDeriv Complex.Gammaℝ (1 / 2 - l t) * W (l t))).re) ≤
      κ * Real.exp (-a * z) *
          ((∑ j ∈ Finset.range (P.natDegree + 1),
            middleGammaDerivCoeff (2 : ℚ) true j * ((Polynomial.derivative^[j]) P).eval z)) -
        κ *
          (Real.exp (-(1 / 2) * z) * (middleK141Kernel.eval₂ (Rat.castHom ℝ) (a - 1 / 2)) ^ 2 /
            (a - 1 / 2) ^ 32) -
        κ *
          (Real.exp (-(5 / 2) * z) * (middleK141Kernel.eval₂ (Rat.castHom ℝ) (-(1 / 2))) ^ 2 /
            (-(1 / 2) : ℝ) ^ 32) := by
  intro a b ha r l F W P z D κ
  have hdeg : 2 * middleK141Kernel.natDegree + 3 ≤ 31 :=
    Nat.add_le_add_right (Nat.mul_le_mul_left 2 middle_k141_kernel_degree) 3
  have hzpos : 0 < b + x := by
    dsimp only [b]; linarith only [hx]
  have h :=
    middle_gamma_contour_le middleK141Kernel hdeg (a := a) (by decide) (by norm_num only [a])
      (by norm_num only [a]) hzpos
  have hV :=
    middle_gamma_decay_square middleK141Kernel ((Nat.le_add_right _ _).trans hdeg) (d := 1 / 2)
      (by norm_num only) hzpos.le
  dsimp only at h hV
  rw [← middle_k141_profile_eq_pole] at h hV
  have hκ : 0 ≤ κ := Rat.cast_nonneg.mpr (by decide +kernel)
  have hmain := mul_le_mul_of_nonneg_left h hκ
  have hV₀ := congrArg ((κ * Real.exp (-a * z)) * ·) hV
  have hE : Real.exp (-a * z) * Real.exp (-(1 / 2) * z) = Real.exp (-(5 / 2) * z) := by
    rw [← Real.exp_add]
    congr 1
    dsimp only [a]
    ring
  rw [mul_add (κ * Real.exp (-a * z)),
    mul_assoc κ (Real.exp (-a * z)) (Real.exp (-(1 / 2) * z) * _), ←
    mul_assoc (Real.exp (-a * z)) (Real.exp (-(1 / 2) * z)), hE] at hV₀
  have hr : a - 5 / 2 = -(1 / 2 : ℝ) := by norm_num only [a]
  rw [hr] at hmain
  have hcoeff := middle_gamma_deriv_sum_real P (2 : ℚ) true z
  dsimp only at hcoeff
  norm_num only [Rat.cast_ofNat, ite_true] at hcoeff
  rw [hcoeff]
  dsimp only [r, l, F, W, P, z, D, κ] at hmain hV₀ ⊢
  norm_num only [a] at hmain hV₀ ⊢
  linear_combination hmain - hV₀

end PseudoPrime.PrimeTestBounds.MillerRabin
