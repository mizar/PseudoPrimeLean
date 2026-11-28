/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Algebra.Polynomial.Derivative

/-! # Laplace moments of translated polynomials -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The exponential weight at any positive rate makes each monomial integrable on `(0, ∞)`. -/
private theorem exp_monomial_integrable (k : ℕ) {s : ℝ} (hs : 0 < s) :
    MeasureTheory.IntegrableOn (fun t : ℝ ↦ t ^ k * Real.exp (-s * t)) (Set.Ioi 0) := by
  have hk : (-1 : ℝ) < k := neg_lt_zero.mpr zero_lt_one |>.trans_le (Nat.cast_nonneg k)
  simpa only [Real.rpow_natCast, Real.rpow_one] using
    integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) hk zero_lt_one hs

/-- The Laplace moment of the degree-`k` monomial is `k! / s^(k+1)`. -/
private theorem exp_monomial_integral (k : ℕ) {s : ℝ} (hs : 0 < s) :
    (∫ t : ℝ in Set.Ioi 0, t ^ k * Real.exp (-s * t)) = (k.factorial : ℝ) / s ^ (k + 1) := by
  have hk := add_pos_of_nonneg_of_pos (Nat.cast_nonneg (α := ℝ) k) zero_lt_one
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (k : ℝ) + 1) (r := s) hk hs
  rw [add_sub_cancel_right, Real.Gamma_nat_eq_factorial] at h
  have hc : (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) := by rw [Nat.cast_add, Nat.cast_one]
  rw [hc, Real.rpow_natCast, one_div, inv_pow, mul_comm _ (k.factorial : ℝ)] at h
  simpa only [Real.rpow_natCast, neg_mul, div_eq_mul_inv] using h

/-- The Laplace integral of a polynomial is the factorial-weighted sum of its coefficients.
Applying this to the polynomial composed with `X + C z` evaluates the tail moment at `z`. -/
public theorem polynomial_laplace_moment (P : Polynomial ℝ) {s : ℝ} (hs : 0 < s) :
    (∫ t : ℝ in Set.Ioi 0, P.eval t * Real.exp (-s * t)) =
      ∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k * ((k.factorial : ℝ) / s ^ (k + 1)) := by
  simp only [Polynomial.eval_eq_sum_range, Finset.sum_mul, mul_assoc]
  rw [MeasureTheory.integral_finsetSum _ (fun k _ ↦ (exp_monomial_integrable k hs).const_mul _)]
  exact
    Finset.sum_congr rfl
      (fun k _ ↦ by rw [MeasureTheory.integral_const_mul, exp_monomial_integral k hs])

/-- Translate the polynomial by the cutoff `z` before taking its Laplace moment.
The finite sum uses the coefficients of the translated polynomial. -/
public theorem polynomial_laplace_tail (P : Polynomial ℝ) (z : ℝ) {s : ℝ} (hs : 0 < s) :
    let Q := P.comp (Polynomial.X + Polynomial.C z)
    (∫ t : ℝ in Set.Ioi 0, P.eval (z + t) * Real.exp (-s * t)) =
      ∑ k ∈ Finset.range (Q.natDegree + 1), Q.coeff k * ((k.factorial : ℝ) / s ^ (k + 1)) := by
  have he (t : ℝ) : (P.comp (Polynomial.X + Polynomial.C z)).eval t = P.eval (z + t) := by
    rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, add_comm t]
  have hf :
    (fun t : ℝ ↦ P.eval (z + t) * Real.exp (-s * t)) =
      (fun t : ℝ ↦ (P.comp (Polynomial.X + Polynomial.C z)).eval t * Real.exp (-s * t)) :=
    funext (fun t ↦ congrArg (· * Real.exp (-s * t)) (he t).symm)
  rw [hf]
  exact polynomial_laplace_moment (P.comp (Polynomial.X + Polynomial.C z)) hs

/-- Translation by `z` carries the positive half-line to the tail starting at `z`. -/
public theorem integral_translate_Ioi (f : ℝ → ℝ) (z : ℝ) :
    (∫ t in Set.Ioi (0 : ℝ), f (z + t)) = ∫ t in Set.Ioi z, f t := by
  have hp : (fun t : ℝ ↦ z + t) ⁻¹' Set.Ioi z = Set.Ioi 0 := by
    ext t
    exact lt_add_iff_pos_right z
  have he : MeasurableEmbedding (fun t : ℝ ↦ z + t) :=
    (Homeomorph.addLeft z).isClosedEmbedding.measurableEmbedding
  simpa only [hp] using
    (MeasureTheory.measurePreserving_add_left MeasureTheory.volume z).setIntegral_preimage_emb he f
      (Set.Ioi z)

/-- Evaluate an exponentially weighted polynomial integral starting at the cutoff `z`. -/
public theorem polynomial_exp_tail (P : Polynomial ℝ) (z : ℝ) {s : ℝ} (hs : 0 < s) :
    let Q := P.comp (Polynomial.X + Polynomial.C z)
    (∫ t in Set.Ioi z, P.eval t * Real.exp (-s * t)) =
      Real.exp (-s * z) *
        ∑ k ∈ Finset.range (Q.natDegree + 1), Q.coeff k * ((k.factorial : ℝ) / s ^ (k + 1)) := by
  have hf (t : ℝ) :
    P.eval (z + t) * Real.exp (-s * (z + t)) =
      Real.exp (-s * z) * (P.eval (z + t) * Real.exp (-s * t)) := by
    rw [mul_add, Real.exp_add, ← mul_assoc, mul_comm (P.eval _) (Real.exp _), mul_assoc]
  rw [← integral_translate_Ioi (fun t ↦ P.eval t * Real.exp (-s * t)) z]
  simp only [hf, MeasureTheory.integral_const_mul, polynomial_laplace_tail P z hs]

/-- Evaluate the power-weighted tail of a polynomial in `log t`.
The logarithmic substitution gives the Laplace moment used in the Euler tail estimate. -/
public theorem polynomial_log_power_tail (P : Polynomial ℝ) {a s : ℝ} (ha : 0 < a) (hs : 0 < s) :
    let z := Real.log a
    let Q := P.comp (Polynomial.X + Polynomial.C z)
    (∫ t in Set.Ioi a, t ^ (-s - 1) * P.eval (Real.log t)) =
      a ^ (-s) *
        ∑ k ∈ Finset.range (Q.natDegree + 1), Q.coeff k * ((k.factorial : ℝ) / s ^ (k + 1)) := by
  let g := fun x : ℝ ↦ P.eval x * Real.exp (-s * x)
  have he :
    (∫ t in Set.Ioi a, t ^ (-s - 1) * P.eval (Real.log t)) =
      ∫ t in Set.Ioi a, t⁻¹ • g (Real.log t) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have ht₀ := ha.trans ht
    simp only [g, smul_eq_mul]
    rw [mul_comm (-s), ← Real.rpow_def_of_pos ht₀, Real.rpow_sub ht₀, Real.rpow_one, div_eq_mul_inv,
      mul_comm (t ^ (-s)) t⁻¹, mul_assoc, mul_comm (t ^ (-s)) (P.eval _)]
  rw [he, MeasureTheory.integral_comp_log_Ioi g ha]
  exact
    (polynomial_exp_tail P (Real.log a) hs).trans (by rw [mul_comm (-s), ← Real.rpow_def_of_pos ha])

/-- On the positive half-line the absolute coefficients bound the absolute polynomial value. -/
private theorem abs_eval_le_coeff_sum (P : Polynomial ℝ) {t : ℝ} (ht : 0 ≤ t) :
    |P.eval t| ≤ ∑ k ∈ Finset.range (P.natDegree + 1), |P.coeff k| * t ^ k := by
  rw [Polynomial.eval_eq_sum_range]
  simpa only [abs_mul, abs_pow, abs_of_nonneg ht] using
    (Finset.abs_sum_le_sum_abs (fun k ↦ P.coeff k * t ^ k) (Finset.range (P.natDegree + 1)))

/-- Bound an absolute Laplace moment by the complete moments of its monomials. -/
private theorem abs_laplace_integrable_and_le (P : Polynomial ℝ) {s : ℝ} (hs : 0 < s) :
    MeasureTheory.IntegrableOn (fun t : ℝ ↦ Real.exp (-s * t) * |P.eval t|) (Set.Ioi 0) ∧
      (∫ t : ℝ in Set.Ioi 0, Real.exp (-s * t) * |P.eval t|) ≤
        ∑ k ∈ Finset.range (P.natDegree + 1), |P.coeff k| * ((k.factorial : ℝ) / s ^ (k + 1)) := by
  let f := fun t : ℝ ↦ Real.exp (-s * t) * |P.eval t|
  let g := fun t : ℝ ↦
    ∑ k ∈ Finset.range (P.natDegree + 1), |P.coeff k| * (t ^ k * Real.exp (-s * t))
  have hterm (k : ℕ) := (exp_monomial_integrable k hs).const_mul |P.coeff k|
  have hg : MeasureTheory.IntegrableOn g (Set.Ioi 0) :=
    MeasureTheory.integrable_finsetSum _ fun k _ ↦ hterm k
  have hfg (t : ℝ) (ht : t ∈ Set.Ioi 0) : f t ≤ g t := by
    have h := mul_le_mul_of_nonneg_right (abs_eval_le_coeff_sum P ht.le) (Real.exp_nonneg (-s * t))
    simpa only [f, g, Finset.sum_mul, mul_assoc, mul_comm (Real.exp (-s * t))] using h
  have hf : MeasureTheory.IntegrableOn f (Set.Ioi 0) := by
    have hfcont : Continuous f :=
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul P.continuous.abs
    apply MeasureTheory.Integrable.mono hg hfcont.aestronglyMeasurable
    filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_Ioi (a := (0 : ℝ)))] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_nonneg _) (abs_nonneg _))]
    exact
      (hfg t ht).trans
        (by
          rw [Real.norm_eq_abs]; exact le_abs_self _)
  refine ⟨hf, (MeasureTheory.setIntegral_mono_on hf hg measurableSet_Ioi hfg).trans_eq ?_⟩
  rw [show g = _ from rfl, MeasureTheory.integral_finsetSum _ (fun k _ ↦ hterm k)]
  exact
    Finset.sum_congr rfl
      (fun k _ ↦ by rw [MeasureTheory.integral_const_mul, exp_monomial_integral k hs])

/-- Bound an absolute Laplace moment by the complete moments of its monomials. -/
public theorem polynomial_abs_laplace_le (P : Polynomial ℝ) {s : ℝ} (hs : 0 < s) :
    (∫ t : ℝ in Set.Ioi 0, Real.exp (-s * t) * |P.eval t|) ≤
      ∑ k ∈ Finset.range (P.natDegree + 1), |P.coeff k| * ((k.factorial : ℝ) / s ^ (k + 1)) :=
  (abs_laplace_integrable_and_le P hs).2

/-- A finite nonnegative cutoff has the same upper bound as the complete absolute moment. -/
public theorem polynomial_abs_laplace_interval_le (P : Polynomial ℝ) {s z : ℝ} (hs : 0 < s)
    (hz : 0 ≤ z) :
    (∫ t : ℝ in 0..z, Real.exp (-s * t) * |P.eval t|) ≤
      ∑ k ∈ Finset.range (P.natDegree + 1), |P.coeff k| * ((k.factorial : ℝ) / s ^ (k + 1)) := by
  rw [intervalIntegral.integral_of_le hz]
  have h := abs_laplace_integrable_and_le P hs
  refine (MeasureTheory.setIntegral_mono_set h.1 ?_ ?_).trans h.2
  · exact Filter.Eventually.of_forall fun t ↦ mul_nonneg (Real.exp_nonneg _) (abs_nonneg _)
  · exact Filter.Eventually.of_forall fun _ ht ↦ ht.1

/-- Translate the absolute polynomial before estimating its complete exponential moment. -/
public theorem polynomial_abs_laplace_shift_le (P : Polynomial ℝ) (z : ℝ) {s : ℝ} (hs : 0 < s) :
    let Q := P.comp (Polynomial.X + Polynomial.C z)
    (∫ t : ℝ in Set.Ioi 0, Real.exp (-s * t) * |P.eval (z + t)|) ≤
      ∑ k ∈ Finset.range (Q.natDegree + 1), |Q.coeff k| * ((k.factorial : ℝ) / s ^ (k + 1)) := by
  have he (t : ℝ) : (P.comp (Polynomial.X + Polynomial.C z)).eval t = P.eval (z + t) := by
    rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, add_comm t]
  have hf :
    (fun t : ℝ ↦ Real.exp (-s * t) * |P.eval (z + t)|) =
      (fun t : ℝ ↦ Real.exp (-s * t) * |(P.comp (Polynomial.X + Polynomial.C z)).eval t|) :=
    funext fun t ↦ congrArg (fun v : ℝ ↦ Real.exp (-s * t) * |v|) (he t).symm
  rw [hf]
  exact polynomial_abs_laplace_le (P.comp (Polynomial.X + Polynomial.C z)) hs

/-- A later nonnegative cutoff reduces the weighted absolute tail integral. -/
public theorem abs_laplace_tail_mono (P : Polynomial ℝ) {s a b : ℝ} (hs : 0 < s) (ha : 0 ≤ a)
    (hab : a ≤ b) :
    (∫ t in Set.Ioi b, Real.exp (-s * t) * |P.eval t|) ≤
      ∫ t in Set.Ioi a, Real.exp (-s * t) * |P.eval t| := by
  have h := (abs_laplace_integrable_and_le P hs).1.mono_set (Set.Ioi_subset_Ioi ha)
  exact
    MeasureTheory.setIntegral_mono_set h
      (Filter.Eventually.of_forall fun _ ↦ mul_nonneg (Real.exp_nonneg _) (abs_nonneg _))
      (Filter.Eventually.of_forall fun _ ht ↦ hab.trans_lt ht)

/-- An increased finite cutoff enlarges the weighted absolute integral. -/
public theorem abs_laplace_interval_mono (P : Polynomial ℝ) {s a b : ℝ} (hs : 0 < s) (ha : 0 ≤ a)
    (hab : a ≤ b) :
    (∫ t in (0 : ℝ)..a, Real.exp (-s * t) * |P.eval t|) ≤
      ∫ t in (0 : ℝ)..b, Real.exp (-s * t) * |P.eval t| := by
  rw [intervalIntegral.integral_of_le ha, intervalIntegral.integral_of_le (ha.trans hab)]
  have hsub : Set.Ioc (0 : ℝ) b ⊆ Set.Ioi 0 := fun _ ht ↦ ht.1
  have h := (abs_laplace_integrable_and_le P hs).1.mono_set hsub
  exact
    MeasureTheory.setIntegral_mono_set h
      (Filter.Eventually.of_forall fun _ ↦ mul_nonneg (Real.exp_nonneg _) (abs_nonneg _))
      (Filter.Eventually.of_forall fun _ ht ↦ ⟨ht.1, ht.2.trans hab⟩)

/-- Transfer the lower H27 moment to a tail whose endpoints can be compared directly. -/
public theorem normalized_abs_laplace_tail (P : Polynomial ℝ) (d z : ℝ) :
    Real.exp (-(d + 1 / 2) * z) *
        (∫ t in Set.Ioi (0 : ℝ), Real.exp (-d * t) * |P.eval (5 + z + t)|) =
      Real.exp (5 * d - z / 2) * (∫ t in Set.Ioi (5 + z), Real.exp (-d * t) * |P.eval t|) := by
  rw [← integral_translate_Ioi (fun t ↦ Real.exp (-d * t) * |P.eval t|) (5 + z)]
  have h (t : ℝ) :
    Real.exp (-d * (5 + z + t)) * |P.eval (5 + z + t)| =
      Real.exp (-d * (5 + z)) * (Real.exp (-d * t) * |P.eval (5 + z + t)|) := by
    rw [mul_add, Real.exp_add, mul_assoc]
  have hf := funext h
  change _ = _ * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-d * (5 + z + t)) * |P.eval (5 + z + t)|
  rw [hf, MeasureTheory.integral_const_mul, ← mul_assoc, ← Real.exp_add]
  rw [show 5 * d - z / 2 + -d * (5 + z) = -(d + 1 / 2) * z by ring]

/-- Split an absolute Laplace tail at a finite endpoint for interval certification. -/
public theorem abs_laplace_tail_split (P : Polynomial ℝ) {s a b : ℝ} (hs : 0 < s) (ha : 0 ≤ a)
    (hab : a ≤ b) :
    (∫ t in Set.Ioi a, Real.exp (-s * t) * |P.eval t|) =
      (∫ t in a..b, Real.exp (-s * t) * |P.eval t|) +
        ∫ t in Set.Ioi b, Real.exp (-s * t) * |P.eval t| := by
  have h := (abs_laplace_integrable_and_le P hs).1.mono_set (Set.Ioi_subset_Ioi ha)
  rw [← intervalIntegral.integral_Ioi_sub_Ioi h hab, sub_add_cancel]

/-- Bound the tail beyond the last interval by the shifted absolute coefficients. -/
public theorem abs_laplace_tail_le_coeffs (P : Polynomial ℝ) {s : ℝ} (hs : 0 < s) (a : ℝ) :
    let Q := P.comp (Polynomial.X + Polynomial.C a)
    (∫ t in Set.Ioi a, Real.exp (-s * t) * |P.eval t|) ≤
      Real.exp (-s * a) *
        ∑ k ∈ Finset.range (Q.natDegree + 1), |Q.coeff k| * ((k.factorial : ℝ) / s ^ (k + 1)) := by
  intro Q
  rw [← integral_translate_Ioi (fun t ↦ Real.exp (-s * t) * |P.eval t|) a]
  have h (t : ℝ) :
    Real.exp (-s * (a + t)) * |P.eval (a + t)| =
      Real.exp (-s * a) * (Real.exp (-s * t) * |P.eval (a + t)|) := by
    rw [mul_add, Real.exp_add, mul_assoc]
  change (∫ t in Set.Ioi (0 : ℝ), Real.exp (-s * (a + t)) * |P.eval (a + t)|) ≤ _
  rw [funext h, MeasureTheory.integral_const_mul]
  exact mul_le_mul_of_nonneg_left (polynomial_abs_laplace_shift_le P a hs) (Real.exp_nonneg _)

/-- Bound the absolute tail by the signed tail and twice the full negative
moment. The latter can be certified independently of the cutoff. -/
public theorem abs_laplace_tail_le_signed (P : Polynomial ℝ) {s a : ℝ} (hs : 0 < s) {a₀ : ℝ}
    (h₀ : 0 ≤ a₀) (ha : a₀ ≤ a) :
    (∫ t in Set.Ioi a, Real.exp (-s * t) * |P.eval t|) ≤
      (∫ t in Set.Ioi a, Real.exp (-s * t) * P.eval t) +
        2 * ∫ t in Set.Ioi a₀, Real.exp (-s * t) * max 0 (-P.eval t) := by
  let w := fun t : ℝ ↦ Real.exp (-s * t)
  let f := fun t : ℝ ↦ w t * |P.eval t|
  let g := fun t : ℝ ↦ w t * P.eval t
  let h := fun t : ℝ ↦ w t * max 0 (-P.eval t)
  have hf : MeasureTheory.IntegrableOn f (Set.Ioi 0) := (abs_laplace_integrable_and_le P hs).1
  have hg : MeasureTheory.IntegrableOn g (Set.Ioi 0) := by
    refine
      hf.mono'
        ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
            P.continuous).aestronglyMeasurable
        ?_
    exact
      Filter.Eventually.of_forall fun t ↦ by
        simp only [g, f, w, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), le_refl]
  have he (t : ℝ) : f t = g t + 2 * h t := by
    by_cases ht : 0 ≤ P.eval t
    · simp only [f, g, h, abs_of_nonneg ht, max_eq_left (neg_nonpos.mpr ht), mul_zero, add_zero]
    · have ht' := le_of_not_ge ht
      simp only [f, g, h, abs_of_nonpos ht', max_eq_right (neg_nonneg.mpr ht')]
      ring
  have hh : MeasureTheory.IntegrableOn h (Set.Ioi 0) := by
    have hh' : h = fun t ↦ (1 / 2 : ℝ) * (f t - g t) := by
      funext t
      rw [he]
      ring
    rw [hh']
    exact (hf.sub hg).const_mul _
  have hsub := Set.Ioi_subset_Ioi (h₀.trans ha)
  change (∫ t in Set.Ioi a, f t) ≤ (∫ t in Set.Ioi a, g t) + 2 * ∫ t in Set.Ioi a₀, h t
  rw [funext he, MeasureTheory.integral_add (hg.mono_set hsub) ((hh.mono_set hsub).const_mul 2),
    MeasureTheory.integral_const_mul]
  exact
    add_le_add_right
      (mul_le_mul_of_nonneg_left
        (MeasureTheory.setIntegral_mono_set (hh.mono_set (Set.Ioi_subset_Ioi h₀))
          (Filter.Eventually.of_forall fun t ↦ mul_nonneg (Real.exp_nonneg _) (le_max_left _ _))
          (Filter.Eventually.of_forall (Set.Ioi_subset_Ioi ha)))
        zero_le_two)
      _

/-- Evaluate the signed part of the absolute tail bound by finitely many
polynomial moments, leaving a cutoff-independent negative correction. -/
public theorem abs_laplace_tail_le_moments (P : Polynomial ℝ) {s a a₀ : ℝ} (hs : 0 < s)
    (h₀ : 0 ≤ a₀) (ha : a₀ ≤ a) :
    let Q := P.comp (Polynomial.X + Polynomial.C a)
    (∫ t in Set.Ioi a, Real.exp (-s * t) * |P.eval t|) ≤
      Real.exp (-s * a) *
          (∑ k ∈ Finset.range (Q.natDegree + 1), Q.coeff k * ((k.factorial : ℝ) / s ^ (k + 1))) +
        2 * ∫ t in Set.Ioi a₀, Real.exp (-s * t) * max 0 (-P.eval t) := by
  intro Q
  refine (abs_laplace_tail_le_signed P hs h₀ ha).trans_eq ?_
  congr 1
  simpa only [mul_comm (Real.exp (-s * _)) (P.eval _)] using polynomial_exp_tail P a hs

/-- If the profile is eventually nonnegative, its weighted negative moment
is supported on the finite interval ending at that sign boundary. -/
public theorem negative_laplace_eq_interval (P : Polynomial ℝ) (s : ℝ) {a₀ b : ℝ} (hb : a₀ ≤ b)
    (hP : ∀ t > b, 0 ≤ P.eval t) :
    (∫ t in Set.Ioi a₀, Real.exp (-s * t) * max 0 (-P.eval t)) =
      ∫ t in a₀..b, Real.exp (-s * t) * max 0 (-P.eval t) := by
  let f := fun t : ℝ ↦ Real.exp (-s * t) * max 0 (-P.eval t)
  rw [intervalIntegral.integral_of_le hb]
  have he : (∫ t in Set.Ioi a₀, f t) = ∫ t in Set.Ioi a₀, (Set.Iic b).indicator f t := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t _
    by_cases ht : t ≤ b
    · exact (Set.indicator_of_mem ht f).symm
    · rw [Set.indicator_of_notMem (fun h ↦ ht h),
        show f t = 0 by
          simp only [f, max_eq_left (neg_nonpos.mpr (hP t (lt_of_not_ge ht))), mul_zero]]
  rw [he, MeasureTheory.setIntegral_indicator measurableSet_Iic]
  rfl

/-- An eventual sign bound reduces the H28 correction to a bounded
interval, while the signed tail keeps its exact polynomial moment. -/
public theorem abs_laplace_tail_le_finite (P : Polynomial ℝ) {s a a₀ b : ℝ} (hs : 0 < s)
    (h₀ : 0 ≤ a₀) (ha : a₀ ≤ a) (hb : a₀ ≤ b) (hP : ∀ t > b, 0 ≤ P.eval t) :
    let Q := P.comp (Polynomial.X + Polynomial.C a)
    (∫ t in Set.Ioi a, Real.exp (-s * t) * |P.eval t|) ≤
      Real.exp (-s * a) *
          (∑ k ∈ Finset.range (Q.natDegree + 1), Q.coeff k * ((k.factorial : ℝ) / s ^ (k + 1))) +
        2 * ∫ t in a₀..b, Real.exp (-s * t) * max 0 (-P.eval t) := by
  intro Q
  rw [← negative_laplace_eq_interval P s hb hP]
  exact abs_laplace_tail_le_moments P hs h₀ ha

/-- Nonnegative coefficients at a translated origin certify the sign of the
profile and every derivative on the ray starting there. -/
public theorem derivative_nonneg_of_shift (P : Polynomial ℝ) {b : ℝ}
    (hP : ∀ i, 0 ≤ (P.comp (Polynomial.X + Polynomial.C b)).coeff i) (j : ℕ) {t : ℝ} (ht : b ≤ t) :
    0 ≤ ((Polynomial.derivative^[j]) P).eval t := by
  let L : Polynomial ℝ := Polynomial.X + Polynomial.C b
  have hcomp (k : ℕ) :
    (Polynomial.derivative^[k]) (P.comp L) = ((Polynomial.derivative^[k]) P).comp L := by
    induction k with
    | zero => rfl
    | succ k
      ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
        Polynomial.derivative_comp]
      simp only [L, Polynomial.derivative_add, Polynomial.derivative_X, Polynomial.derivative_C,
        add_zero, one_mul]
  have he :
    ((Polynomial.derivative^[j]) (P.comp L)).eval (t - b) =
      ((Polynomial.derivative^[j]) P).eval t := by
    rw [hcomp, Polynomial.eval_comp]
    simp only [L, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, sub_add_cancel]
  rw [← he, Polynomial.eval_eq_sum_range]
  exact
    Finset.sum_nonneg fun i _ ↦
      mul_nonneg
        (by
          rw [Polynomial.coeff_iterate_derivative]; exact nsmul_nonneg (hP (i + j)) _)
        (pow_nonneg (sub_nonneg.mpr ht) i)

end PseudoPrime.PrimeTestBounds.MillerRabin
