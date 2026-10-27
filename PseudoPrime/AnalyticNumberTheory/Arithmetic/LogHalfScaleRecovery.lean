/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.FiniteDyadicRecovery
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimitiveComparison
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.LogWeightedDifferences

/-! # Recovering character logarithmic sums from half-scale errors -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For a complex Dirichlet character, positive scale, and a positive index
below its floor, the character term has norm at most the unsigned logarithmic
Mangoldt weight. The weight is nonnegative and character values have norm at most
one. This gives the local character-independent majorant. -/
theorem norm_characterLogWeightedTerm_le_unsigned {q n : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) (hn0 : 0 < n) (hnx : n ≤ ⌊x⌋₊) :
    ‖characterLogWeightedTerm x χ n‖ ≤ logWeightedMangoldtTerm x n := by
  have hw := logWeightedMangoldtTerm_nonneg hx hn0 hnx
  rw [characterLogWeightedTerm, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw]
  exact mul_le_of_le_one_right hw (DirichletCharacter.norm_le_one χ _)

/-- For every complex Dirichlet character and positive scale, the norm of the
logarithmically weighted character sum is at most the unsigned sum. Apply the
triangle inequality and the termwise unsigned comparison. No primitivity, RH,
or quantitative analytic estimate is required. -/
theorem norm_characterLogWeightedSum_le_unsigned {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) : ‖characterLogWeightedSum x χ‖ ≤ logWeightedMangoldtSum x := by
  calc
    _ ≤ ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ‖characterLogWeightedTerm x χ n‖ := norm_sum_le _ _
    _ ≤ _ :=
      Finset.sum_le_sum
        (fun n hn ↦
          norm_characterLogWeightedTerm_le_unsigned χ hx (Finset.mem_Ioc.mp hn).1
            (Finset.mem_Ioc.mp hn).2)

/-- The unsigned logarithmic Mangoldt sum increases between positive ordered
cutoffs. Its finite difference is bounded below by a nonnegative Chebyshev and
logarithmic product. This supplies a common local bound on dyadic stopping scales. -/
theorem logWeightedMangoldtSum_mono_of_pos {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    logWeightedMangoldtSum x ≤ logWeightedMangoldtSum y := by
  have hdiff := (logWeightedMangoldtSum_difference_bounds hx hxy).1
  have hlog : 0 ≤ Real.log (y / x) := Real.log_nonneg ((one_le_div₀ hx).mpr hxy)
  have hnonneg := mul_nonneg (Chebyshev.psi_nonneg x) hlog
  linarith only [hdiff, hnonneg]

/-- For any finite family of characters, an aggregate half-scale error `εt`
above a positive cutoff `L` implies a full norm sum at most `2εx` plus the family
cardinality times the unsigned sum at `2L`. Apply finite dyadic recovery and the
character-independent local majorant. The principal error does not acquire a
factor from the number of characters. -/
theorem sum_norm_characterLogWeightedSum_le_of_half_errors {ι : Type*} (S : Finset ι) (q : ι → ℕ)
    (χ : ∀ i, DirichletCharacter ℂ (q i)) {ε L x : ℝ} (hε : 0 ≤ ε) (hL : 0 < L) (hx : L ≤ x)
    (hhalf :
      ∀ t : ℝ,
        L ≤ t →
          ∑ i ∈ S, ‖characterLogWeightedSum t (χ i) - characterLogWeightedSum (t / 2) (χ i)‖ ≤
            ε * t) :
    ∑ i ∈ S, ‖characterLogWeightedSum x (χ i)‖ ≤
      2 * ε * x + (S.card : ℝ) * logWeightedMangoldtSum (2 * L) := by
  have hlocal (t : ℝ) (htlo : L ≤ t) (hthi : t < 2 * L) (i : ι) (_hi : i ∈ S) :
    ‖characterLogWeightedSum t (χ i)‖ ≤ logWeightedMangoldtSum (2 * L) :=
    (norm_characterLogWeightedSum_le_unsigned (χ i) (hL.trans_le htlo)).trans
      (logWeightedMangoldtSum_mono_of_pos (hL.trans_le htlo) hthi.le)
  have hb :=
    Analysis.sum_norm_le_two_half_scale_error_add_local_bound S
      (fun i t ↦ characterLogWeightedSum t (χ i)) (fun _ ↦ logWeightedMangoldtSum (2 * L)) hε hL hx
      hlocal hhalf
  simpa only [Finset.sum_const, nsmul_eq_mul] using hb

/-- For scale at least one, the unsigned logarithmic Mangoldt sum is at most
`(log 4 + 4) x log x`. Bound every logarithmic weight by `log x` and use the
unconditional Chebyshev upper bound. This makes the dyadic local remainder explicit. -/
theorem logWeightedMangoldtSum_le_linear_log {x : ℝ} (hx : 1 ≤ x) :
    logWeightedMangoldtSum x ≤ (Real.log 4 + 4) * x * Real.log x := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hsum : logWeightedMangoldtSum x ≤ Chebyshev.psi x * Real.log x := by
    rw [logWeightedMangoldtSum, psi_eq_positive_sum, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Ioc.mp hn).1
    have hnone : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ioc.mp hn).1
    have harg : x / (n : ℝ) ≤ x := div_le_self hxpos.le hnone
    have hl := Real.log_le_log (div_pos hxpos hnpos) harg
    exact mul_le_mul_of_nonneg_left hl ArithmeticFunction.vonMangoldt_nonneg
  exact hsum.trans (mul_le_mul_of_nonneg_right (Chebyshev.psi_le_const_mul_self hxpos.le) hlog)

/-- For a finite family and cutoff `L ≥ 1`, aggregate half-scale errors above
`L` give a full norm sum bounded by `2εx` plus an explicit family-cardinality
multiple of `L log(2L)`. Insert the elementary unsigned majorant into the dyadic
recovery estimate. This is the arithmetic interface for choosing one uniform
small-scale budget in the theta-supply argument. -/
theorem sum_norm_characterLogWeightedSum_le_linear_local_remainder {ι : Type*} (S : Finset ι)
    (q : ι → ℕ) (χ : ∀ i, DirichletCharacter ℂ (q i)) {ε L x : ℝ} (hε : 0 ≤ ε) (hL : 1 ≤ L)
    (hx : L ≤ x)
    (hhalf :
      ∀ t : ℝ,
        L ≤ t →
          ∑ i ∈ S, ‖characterLogWeightedSum t (χ i) - characterLogWeightedSum (t / 2) (χ i)‖ ≤
            ε * t) :
    ∑ i ∈ S, ‖characterLogWeightedSum x (χ i)‖ ≤
      2 * ε * x + (S.card : ℝ) * ((Real.log 4 + 4) * (2 * L) * Real.log (2 * L)) := by
  have hb :=
    sum_norm_characterLogWeightedSum_le_of_half_errors S q χ hε (zero_lt_one.trans_le hL) hx hhalf
  have hsmall := logWeightedMangoldtSum_le_linear_log (by linarith only [hL] : 1 ≤ 2 * L)
  exact hb.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hsmall (Nat.cast_nonneg S.card)))

/-- For a finite character family, aggregate half-scale error `epsilon t`
above a cutoff `L >= 1` bounds the difference at `x` and `4x/5` by `4 epsilon x`
plus twice the explicit local remainder, provided `4x/5 >= L`. Apply dyadic
recovery at both endpoints and the norm triangle inequality. This connects the
half-scale explicit formula to the principal difference with coefficient above one half. -/
theorem sum_norm_characterLogWeightedSum_four_fifths_difference_le {ι : Type*} (S : Finset ι)
    (q : ι → ℕ) (χ : ∀ i, DirichletCharacter ℂ (q i)) {ε L x : ℝ} (hε : 0 ≤ ε) (hL : 1 ≤ L)
    (hx : L ≤ 4 * x / 5)
    (hhalf :
      ∀ t : ℝ,
        L ≤ t →
          ∑ i ∈ S, ‖characterLogWeightedSum t (χ i) - characterLogWeightedSum (t / 2) (χ i)‖ ≤
            ε * t) :
    ∑ i ∈ S, ‖characterLogWeightedSum x (χ i) - characterLogWeightedSum (4 * x / 5) (χ i)‖ ≤
      4 * ε * x + 2 * (S.card : ℝ) * ((Real.log 4 + 4) * (2 * L) * Real.log (2 * L)) := by
  have hxpos : 0 ≤ x := by linarith only [hL, hx]
  have hscale : 4 * x / 5 ≤ x := by linarith only [hxpos]
  have hb :=
    sum_norm_characterLogWeightedSum_le_linear_local_remainder S q χ hε hL (hx.trans hscale) hhalf
  have hc := sum_norm_characterLogWeightedSum_le_linear_local_remainder S q χ hε hL hx hhalf
  have ht :
    (∑ i ∈ S, ‖characterLogWeightedSum x (χ i) - characterLogWeightedSum (4 * x / 5) (χ i)‖) ≤
      (∑ i ∈ S, ‖characterLogWeightedSum x (χ i)‖) +
        ∑ i ∈ S, ‖characterLogWeightedSum (4 * x / 5) (χ i)‖ := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun i _ ↦ norm_sub_le _ _)
  have hmul := mul_le_mul_of_nonneg_left hscale hε
  linarith only [hb, hc, ht, hmul]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
