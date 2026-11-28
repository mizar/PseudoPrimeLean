/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianEulerPolyAbel
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianLaplaceMoment
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevPsiLeeNosal
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith

/-! # RH upper bounds for polynomial Euler tails -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The Lee–Nosal envelope implies the coarser logarithmic-square bound in H18. -/
private theorem euler_psi_rh (hRH : RiemannHypothesis) {t : ℝ} (ht : 101 ≤ t)
    (hl : 1 ≤ Real.log t) : |Chebyshev.psi t - t| ≤ Real.sqrt t * Real.log t ^ 2 / 24 := by
  have ht₀ := (by norm_num only : (0 : ℝ) < 101).trans_le ht
  have hs := Real.sqrt_pos.2 ht₀
  have h := (div_le_iff₀ hs).mp (AnalyticNumberTheory.Arithmetic.psi_lee_nosal_of_RH hRH ht)
  have hπ : (24 : ℝ) ≤ 8 * Real.pi := by linarith only [Real.pi_gt_three]
  have hn :=
    mul_le_mul_of_nonneg_left (sub_le_self (Real.log t) (Real.log_nonneg hl)) (zero_le_one.trans hl)
  calc
    _ ≤ Real.log t ^ 2 / (8 * Real.pi) * Real.sqrt t :=
      h.trans
        (mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right (by simpa only [pow_two] using hn) (by positivity)) hs.le)
    _ ≤ _ := by
      rw [mul_comm, ← mul_div_assoc]
      exact div_le_div_of_nonneg_left (mul_nonneg hs.le (sq_nonneg _)) (by norm_num only) hπ

/-- The Chebyshev boundary costs the RH envelope times the nonnegative Euler weight. -/
private theorem euler_poly_boundary_rh (P : Polynomial ℝ) (σ : ℝ) (hRH : RiemannHypothesis) {a : ℝ}
    (ha : 101 ≤ a) (hl : 1 ≤ Real.log a) (hP : 0 ≤ P.eval (Real.log a)) :
    -(Chebyshev.psi a - a) * (a ^ (-σ) * P.eval (Real.log a)) ≤
      a ^ (-(σ - 1 / 2)) * (Real.log a ^ 2 * P.eval (Real.log a)) / 24 := by
  have ha₀ := (by norm_num only : (0 : ℝ) < 101).trans_le ha
  refine
    (mul_le_mul_of_nonneg_right ((neg_le_abs _).trans (euler_psi_rh hRH ha hl))
          (mul_nonneg (Real.rpow_nonneg ha₀.le _) hP)).trans_eq
      ?_
  have he : Real.sqrt a * a ^ (-σ) = a ^ (-(σ - 1 / 2)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add ha₀]
    congr 1
    ring
  calc
    _ = (Real.sqrt a * a ^ (-σ)) * (Real.log a ^ 2 * P.eval (Real.log a)) / 24 := by ring
    _ = _ := by rw [he]

/-- On a tail where the derivative polynomial is nonnegative, the RH majorant
of the centered error is a power-weighted polynomial integral divided by 24. -/
private theorem euler_poly_error_rh (P : Polynomial ℝ) {σ a : ℝ} (hσ : 2 < σ)
    (hRH : RiemannHypothesis) (ha : 101 ≤ a) (hl : 1 ≤ Real.log a)
    (hQ : ∀ z, Real.log a ≤ z → 0 ≤ (Polynomial.C σ * P - P.derivative).eval z) :
    let f := fun t : ℝ ↦ t ^ (-σ) * P.eval (Real.log t)
    let Q := Polynomial.X ^ 2 * (Polynomial.C σ * P - P.derivative)
    |∫ t in Set.Ioi a, (Chebyshev.psi t - t) * deriv f t| ≤
      (∫ t in Set.Ioi a, t ^ (-(σ - 1 / 2) - 1) * Q.eval (Real.log t)) / 24 := by
  intro f Q
  have ha₁ := (by norm_num only : (1 : ℝ) ≤ 101).trans ha
  have ha₀ := zero_lt_one.trans_le ha₁
  have hs : 0 < σ - 1 / 2 := by linarith only [hσ]
  have hi := (euler_poly_integrable Q ha₁ hs).div_const 24
  rw [← MeasureTheory.integral_div, ← Real.norm_eq_abs]
  apply MeasureTheory.norm_integral_le_of_norm_le hi
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
  have ht₀ := ha₀.trans ht
  have hlog := Real.log_le_log ha₀ ht.le
  have hw := hQ (Real.log t) hlog
  rw [Real.norm_eq_abs, abs_mul]
  refine
    (mul_le_mul_of_nonneg_right (euler_psi_rh hRH (ha.trans ht.le) (hl.trans hlog))
          (abs_nonneg _)).trans_eq
      ?_
  rw [show deriv f t = _ from (euler_poly_weight_deriv P σ ht₀).deriv, abs_neg,
    abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ht₀.le _) hw)]
  have he : Real.sqrt t * t ^ (-σ - 1) = t ^ (-(σ - 1 / 2) - 1) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add ht₀]
    congr 1
    ring
  simp only [Q, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  rw [← he]
  ring

/-- Under RH the Mangoldt tail is bounded by the main polynomial integral and the
two logarithmic-square error contributions from the lower boundary and derivative.
The sign assumptions hold on the logarithmic tail and are the inputs of H18. -/
public theorem euler_poly_tail_rh (P : Polynomial ℝ) {σ a : ℝ} (hσ : 2 < σ)
    (hRH : RiemannHypothesis) (ha : 101 ≤ a) (hl : 1 ≤ Real.log a) (hP : 0 ≤ P.eval (Real.log a))
    (hQ : ∀ z, Real.log a ≤ z → 0 ≤ (Polynomial.C σ * P - P.derivative).eval z) :
    let f := fun t : ℝ ↦ t ^ (-σ) * P.eval (Real.log t)
    let Q := Polynomial.X ^ 2 * (Polynomial.C σ * P - P.derivative)
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * f n) -
        (∑ n ∈ Finset.Ioc 0 ⌊a⌋₊, ArithmeticFunction.vonMangoldt n * f n) ≤
      (∫ t in Set.Ioi a, f t) +
        (a ^ (-(σ - 1 / 2)) * (Real.log a ^ 2 * P.eval (Real.log a)) +
            (∫ t in Set.Ioi a, t ^ (-(σ - 1 / 2) - 1) * Q.eval (Real.log t))) /
          24 := by
  have h := euler_poly_centered_tail P hσ ((by norm_num only : (1 : ℝ) ≤ 101).trans ha)
  have hb := euler_poly_boundary_rh P σ hRH ha hl hP
  have he := (neg_le_abs _).trans (euler_poly_error_rh P hσ hRH ha hl hQ)
  dsimp only at h he ⊢
  linarith only [h, hb, he]

/-- The factorial-weighted moment of a logarithmic polynomial at cutoff `z` and rate `s`. -/
@[expose]
public noncomputable def eulerPolyMoment (P : Polynomial ℝ) (z s : ℝ) : ℝ :=
  let Q := P.comp (Polynomial.X + Polynomial.C z)
  ∑ k ∈ Finset.range (Q.natDegree + 1), Q.coeff k * ((k.factorial : ℝ) / s ^ (k + 1))

/-- Evaluate both integrals of the RH Euler bound as the finite moments in H18. -/
public theorem euler_poly_tail_rh_moment (P : Polynomial ℝ) {σ a : ℝ} (hσ : 2 < σ)
    (hRH : RiemannHypothesis) (ha : 101 ≤ a) (hl : 1 ≤ Real.log a) (hP : 0 ≤ P.eval (Real.log a))
    (hQ : ∀ z, Real.log a ≤ z → 0 ≤ (Polynomial.C σ * P - P.derivative).eval z) :
    let f := fun t : ℝ ↦ t ^ (-σ) * P.eval (Real.log t)
    let Q := Polynomial.X ^ 2 * (Polynomial.C σ * P - P.derivative)
    let z := Real.log a
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * f n) -
        (∑ n ∈ Finset.Ioc 0 ⌊a⌋₊, ArithmeticFunction.vonMangoldt n * f n) ≤
      a ^ (-(σ - 1)) * eulerPolyMoment P z (σ - 1) +
        a ^ (-(σ - 1 / 2)) * (z ^ 2 * P.eval z + eulerPolyMoment Q z (σ - 1 / 2)) / 24 := by
  intro f Q z
  have ha₀ := (by norm_num only : (0 : ℝ) < 101).trans_le ha
  have h₁ := polynomial_log_power_tail P ha₀ (show 0 < σ - 1 by linarith only [hσ])
  have h₂ := polynomial_log_power_tail Q ha₀ (show 0 < σ - 1 / 2 by linarith only [hσ])
  dsimp only at h₁ h₂
  rw [neg_sub, sub_sub_cancel_left] at h₁
  have h := euler_poly_tail_rh P hσ hRH ha hl hP hQ
  change _ ≤ (∫ t in Set.Ioi a, t ^ (-σ) * P.eval (Real.log t)) + _ at h
  rw [h₁, h₂] at h
  simpa only [eulerPolyMoment, mul_add, neg_sub, Q, z, f] using h

/-- For summable weights vanishing at zero, removing the finite prefix leaves the tail. -/
private theorem euler_tail_subtype {f : ℕ → ℝ} (hf : Summable f) (h0 : f 0 = 0) (a : ℝ) :
    (∑' n : { n : ℕ // ⌊a⌋₊ < n }, f n.val) = (∑' n : ℕ, f n) - ∑ n ∈ Finset.Ioc 0 ⌊a⌋₊, f n := by
  have he := hf.sum_add_tsum_compl (s := Finset.Icc 0 ⌊a⌋₊)
  have hs : (∑ n ∈ Finset.Ioc 0 ⌊a⌋₊, f n) = ∑ n ∈ Finset.Icc 0 ⌊a⌋₊, f n := by
    refine
      Finset.sum_subset (fun n hn ↦ Finset.mem_Icc.mpr ⟨Nat.zero_le n, (Finset.mem_Ioc.mp hn).2⟩)
        (fun n hn hnot ↦ ?_)
    have hn₀ : n = 0 := by
      by_contra h
      exact hnot (Finset.mem_Ioc.mpr ⟨Nat.pos_of_ne_zero h, (Finset.mem_Icc.mp hn).2⟩)
    simpa only [hn₀] using h0
  have hc : (↑(Finset.Icc 0 ⌊a⌋₊) : Set ℕ)ᶜ = {n | ⌊a⌋₊ < n} := by
    ext n
    simp only [Set.mem_compl_iff, Finset.mem_coe, Finset.mem_Icc, Nat.zero_le, true_and, not_le,
      Set.mem_ofPred_eq]
  rw [← hs, hc] at he
  exact eq_sub_of_add_eq' he

/-- A trace deficit between zero and four costs at most four times the H18 moment.
The polynomial and its derivative combination must be nonnegative on the logarithmic tail. -/
public theorem euler_trace_tail_rh (P : Polynomial ℝ) {σ a : ℝ} (hσ : 2 < σ)
    (hRH : RiemannHypothesis) (ha : 101 ≤ a) (hl : 1 ≤ Real.log a)
    (hP : ∀ z, Real.log a ≤ z → 0 ≤ P.eval z)
    (hQ : ∀ z, Real.log a ≤ z → 0 ≤ (Polynomial.C σ * P - P.derivative).eval z) (α : ℕ → ℝ)
    (hα : ∀ n, α n ∈ Set.Icc 0 4) :
    let z := Real.log a
    let Q := Polynomial.X ^ 2 * (Polynomial.C σ * P - P.derivative)
    (∑' n : { n : ℕ // ⌊a⌋₊ < n },
        α n.val *
          (ArithmeticFunction.vonMangoldt n.val * (n.val : ℝ) ^ (-σ) * P.eval (Real.log n.val))) ≤
      4 *
        (a ^ (-(σ - 1)) * eulerPolyMoment P z (σ - 1) +
          a ^ (-(σ - 1 / 2)) * (z ^ 2 * P.eval z + eulerPolyMoment Q z (σ - 1 / 2)) / 24) := by
  intro z Q
  let f := fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * ((n : ℝ) ^ (-σ) * P.eval (Real.log n))
  have ha₀ := (by norm_num only : (0 : ℝ) < 101).trans_le ha
  have hf : Summable f := euler_poly_summable P ((by norm_num only : (1 : ℝ) < 2).trans hσ)
  have hnon (n : { n : ℕ // ⌊a⌋₊ < n }) : 0 ≤ f n.val := by
    have hn := (Nat.floor_lt ha₀.le).mp n.property
    exact
      mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hP _ (Real.log_le_log ha₀ hn.le)))
  have hg := (hf.subtype (fun n : ℕ ↦ ⌊a⌋₊ < n)).mul_left (4 : ℝ)
  have hle (n : { n : ℕ // ⌊a⌋₊ < n }) : α n.val * f n.val ≤ 4 * f n.val :=
    mul_le_mul_of_nonneg_right (hα _).2 (hnon n)
  have hs := hg.of_nonneg_of_le (fun n ↦ mul_nonneg (hα _).1 (hnon n)) hle
  have ht := hs.tsum_le_tsum hle hg
  have hf₀ : f 0 = 0 := by simp only [f, ArithmeticFunction.map_zero, zero_mul]
  rw [tsum_mul_left, euler_tail_subtype hf hf₀] at ht
  simp only [mul_assoc]
  exact
    ht.trans
      (mul_le_mul_of_nonneg_left (euler_poly_tail_rh_moment P hσ hRH ha hl (hP _ le_rfl) hQ)
        (by norm_num only))

end PseudoPrime.PrimeTestBounds.MillerRabin
