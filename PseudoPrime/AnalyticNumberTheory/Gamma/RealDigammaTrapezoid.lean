/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Gamma.UniformDigamma
public import PseudoPrime.Analysis.LogTrapezoidBounds

/-! # Two-sided real digamma bounds with an exactly telescoping remainder -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Gamma

/-- The real logarithmic increment error at r+k. Positive r makes this
the real part of the complex digamma error term. Its trapezoid enclosure
telescopes over k, supplying an explicit quadratic endpoint remainder. -/
noncomputable def realDigammaLogError (r : ℝ) (k : ℕ) : ℝ :=
  Real.log (r + k + 1) - Real.log (r + k) - (r + k)⁻¹

/-- For positive r, enclose the first N real logarithmic increment errors
by exact reciprocal and inverse-square endpoint differences. Sum the
pointwise trapezoid bounds and telescope both rational sequences. -/
theorem sum_realDigammaLogError_bounds {r : ℝ} (hr : 0 < r) (N : ℕ) :
    -(1 / 2 : ℝ) * (r⁻¹ - (r + N)⁻¹) - (1 / 8 : ℝ) * (r⁻¹ ^ 2 - (r + N)⁻¹ ^ 2) ≤
        (∑ k ∈ Finset.range N, realDigammaLogError r k) ∧
      (∑ k ∈ Finset.range N, realDigammaLogError r k) ≤ -(1 / 2 : ℝ) * (r⁻¹ - (r + N)⁻¹) := by
  have hlo :=
    Finset.sum_le_sum (s := Finset.range N)
      (fun k _ ↦
        (Analysis.log_increment_trapezoid_bounds
            (add_pos_of_pos_of_nonneg hr (Nat.cast_nonneg k))).1)
  have hhi :=
    Finset.sum_le_sum (s := Finset.range N)
      (fun k _ ↦
        (Analysis.log_increment_trapezoid_bounds
            (add_pos_of_pos_of_nonneg hr (Nat.cast_nonneg k))).2)
  have he1 := Finset.sum_range_sub' (fun k : ℕ ↦ (r + k)⁻¹) N
  have he2 := Finset.sum_range_sub' (fun k : ℕ ↦ (r + k)⁻¹ ^ 2) N
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero, ← add_assoc] at he1 he2
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, he1, he2] at hlo
  rw [← Finset.mul_sum, he1] at hhi
  exact ⟨hlo, hhi⟩

/-- At positive real r, the real error is the real part of the complex
digamma logarithmic increment. Positive shifted arguments remove absolute
values from the complex logarithms and reciprocals. -/
theorem realDigammaLogError_eq_re {r : ℝ} (hr : 0 < r) (k : ℕ) :
    realDigammaLogError r k = (digammaLogError (r : ℂ) k).re := by
  have hk : 0 ≤ r + k := (add_pos_of_pos_of_nonneg hr (Nat.cast_nonneg k)).le
  have hk1 : 0 ≤ r + k + 1 := add_nonneg hk zero_le_one
  simp only [realDigammaLogError, digammaLogError, ← Complex.ofReal_natCast, ← Complex.ofReal_add,
    ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.sub_re, Complex.ofReal_re, Complex.log_re,
    Complex.norm_of_nonneg hk, Complex.norm_of_nonneg hk1, one_div]

/-- For r≥1/2, the real increment-error series sums to Re ψ(r)-log r.
Map the already absolutely convergent complex error series through its
continuous real-part map and identify the real shifted logarithms. -/
theorem hasSum_realDigammaLogError {r : ℝ} (hr : 1 / 2 ≤ r) :
    HasSum (realDigammaLogError r) ((Complex.digamma (r : ℂ)).re - Real.log r) := by
  have hr0 := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1 / 2) hr
  have hrc : (1 / 2 : ℝ) ≤ (r : ℂ).re := hr
  have hs := summable_digammaLogError hrc
  have ht := (Complex.reCLM.summable hs).congr (fun k ↦ (realDigammaLogError_eq_re hr0 k).symm)
  have he := congrArg Complex.re (digamma_sub_log_eq_tsum_digammaLogError hrc)
  rw [Complex.sub_re, Complex.log_re, Complex.norm_of_nonneg hr0.le, Complex.re_tsum hs] at he
  have heq : (∑' k : ℕ, realDigammaLogError r k) = (Complex.digamma (r : ℂ)).re - Real.log r := by
    rw [tsum_congr (realDigammaLogError_eq_re hr0)]
    exact he.symm
  exact heq ▸ ht.hasSum

/-- For r≥1/2, the real digamma value lies between log r-1/(2r)-1/(8r²)
and log r-1/(2r). Pass the finite telescoping enclosure to the absolutely
convergent error series; translated reciprocal endpoints tend to zero.
This supplies a proved quadratic remainder without an asymptotic assumption. -/
theorem real_digamma_trapezoid_bounds {r : ℝ} (hr : 1 / 2 ≤ r) :
    Real.log r - (1 / 2 : ℝ) * r⁻¹ - (1 / 8 : ℝ) * r⁻¹ ^ 2 ≤ (Complex.digamma (r : ℂ)).re ∧
      (Complex.digamma (r : ℂ)).re ≤ Real.log r - (1 / 2 : ℝ) * r⁻¹ := by
  have hr0 := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1 / 2) hr
  have hi : Filter.Tendsto (fun N : ℕ ↦ (r + (N : ℝ))⁻¹) Filter.atTop (nhds 0) := by
    have h :=
      ((tendsto_natCast_atTop_atTop :
              Filter.Tendsto (fun N : ℕ ↦ (N : ℝ)) Filter.atTop Filter.atTop).atTop_add
          (tendsto_const_nhds (x := r))).inv_tendsto_atTop
    exact
      h.congr'
        (Filter.Eventually.of_forall
          (fun N ↦ by
            dsimp only [Pi.inv_apply]
            rw [add_comm]))
  have hs := (hasSum_realDigammaLogError hr).tendsto_sum_nat
  have hl := ((tendsto_const_nhds (x := r⁻¹)).sub hi).const_mul (-(1 / 2 : ℝ))
  have hq := ((tendsto_const_nhds (x := r⁻¹ ^ 2)).sub (hi.pow 2)).const_mul (1 / 8 : ℝ)
  have hlo :=
    le_of_tendsto_of_tendsto (hl.sub hq) hs
      (Filter.Eventually.of_forall (fun N ↦ (sum_realDigammaLogError_bounds hr0 N).1))
  have hhi :=
    le_of_tendsto_of_tendsto hs hl
      (Filter.Eventually.of_forall (fun N ↦ (sum_realDigammaLogError_bounds hr0 N).2))
  simp only [sub_zero, zero_pow (by decide : 2 ≠ 0)] at hlo hhi
  constructor <;> linarith only [hlo, hhi]

/-- For r≥1/2 and any finite prefix N, enclose Re ψ(r) by the translated
logarithm, the exact finite reciprocal sum, and an error at most 1/(8(r+N)²).
The recurrence transfers the proved real-axis bounds to a short finite
certificate, without assuming an Euler-Maclaurin or digamma remainder formula. -/
theorem real_digamma_finite_prefix_bounds {r : ℝ} (hr : 1 / 2 ≤ r) (N : ℕ) :
    Real.log (r + N) - (1 / 2 : ℝ) * (r + N)⁻¹ - (1 / 8 : ℝ) * (r + N)⁻¹ ^ 2 -
          (∑ k ∈ Finset.range N, (r + k)⁻¹) ≤
        (Complex.digamma (r : ℂ)).re ∧
      (Complex.digamma (r : ℂ)).re ≤
        Real.log (r + N) - (1 / 2 : ℝ) * (r + N)⁻¹ - (∑ k ∈ Finset.range N, (r + k)⁻¹) := by
  have hr0 := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1 / 2) hr
  have hN := real_digamma_trapezoid_bounds (hr.trans (le_add_of_nonneg_right (Nat.cast_nonneg N)))
  have he :=
    congrArg Complex.re
      (Complex.digamma_apply_add_nat (not_neg_nat_of_re_pos (show 0 < (r : ℂ).re from hr0)) N)
  simp only [← Complex.ofReal_natCast, ← Complex.ofReal_add, ← Complex.ofReal_inv,
    ← Complex.ofReal_sum, Complex.add_re, Complex.ofReal_re] at he
  constructor <;> linarith only [hN.1, hN.2, he]

end PseudoPrime.AnalyticNumberTheory.Gamma
