/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.MellinKernelTransformRegularity
public import PseudoPrime.LLS.RiemannMangoldtLimits
public import PseudoPrime.LLS.MellinKernelPrimitiveComparison

/-!
# Integral lower bounds for truncated principal-character kernel sums

Continuous weighted Mangoldt limits provide the main term. Positivity removes the
lower cutoff at zero, and the finite primitivization estimate controls primes dividing
the modulus. The resulting lower estimate is uniform in the principal-character modulus.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements.MellinKernel

/-- Under RH, for a fixed positive cutoff and any positive allowance, the normalized
finite Mangoldt sum with the comparison weight eventually exceeds its full integral minus
that allowance. First use a positive lower cutoff, then pass it to zero and enlarge the
finite sum using nonnegativity. This supplies the lower estimate in Proposition 6.1. -/
theorem eventually_integral_le_weighted_mangoldt_sum (K : MellinKernel) (hRH : RiemannHypothesis)
    {b ε : ℝ} (hb : 0 < b) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in Filter.atTop,
      (∫ u in 0..b, (K.transform u).re / Real.sqrt u) - ε ≤
        (∑ n ∈ Finset.Ioc 0 ⌊b * x⌋₊,
            ArithmeticFunction.vonMangoldt n *
              ((K.transform ((n : ℝ) / x)).re / Real.sqrt ((n : ℝ) / x))) /
          x := by
  have hcut :=
    (tendsto_integral_weight_cutoff K hb).eventually
      (eventually_gt_nhds (sub_lt_self _ (half_pos hε)))
  have hpos : ∀ᶠ a : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < a := self_mem_nhdsWithin
  have haevent := hcut.and (hpos.and ((eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds))
  obtain ⟨a, hia, ha, hab⟩ := haevent.exists
  have hc : ContinuousOn (fun u : ℝ ↦ (K.transform u).re / Real.sqrt u) (Set.Icc a b) :=
    (continuousOn_weight K).mono (fun u hu ↦ lt_of_lt_of_le ha hu.1)
  have hs :=
    (LLS.tendsto_weighted_mangoldt_scaled_interval_sum hRH ha hab.le
          (fun u : ℝ ↦ (K.transform u).re / Real.sqrt u) hc).eventually
      (eventually_gt_nhds (sub_lt_self _ (half_pos hε)))
  filter_upwards [hs, Filter.eventually_gt_atTop (0 : ℝ)] with x hxsum hx
  have hcomp :
    (∑ n ∈ Finset.Ioc ⌊a * x⌋₊ ⌊b * x⌋₊,
        ArithmeticFunction.vonMangoldt n *
          ((K.transform ((n : ℝ) / x)).re / Real.sqrt ((n : ℝ) / x))) ≤
      (∑ n ∈ Finset.Ioc 0 ⌊b * x⌋₊,
        ArithmeticFunction.vonMangoldt n *
          ((K.transform ((n : ℝ) / x)).re / Real.sqrt ((n : ℝ) / x))) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc (Nat.zero_le _) (le_refl _))
    intro n hn hna
    have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Finset.mem_Ioc.mp hn).1
    exact
      mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (div_nonneg (K.mellin_nonneg _ (div_pos hnpos hx)) (Real.sqrt_nonneg _))
  have hd := div_le_div_of_nonneg_right hcomp hx.le
  linarith only [hia, hxsum, hd]

/-- Dividing a nonzero level-one summand by the square root of the scale gives the
normalized Mangoldt comparison weight. The level-one character equals one and the
square-root factors cancel. This converts the weighted limit to the paper's summands. -/
theorem level_one_summand_re_div_sqrt (K : MellinKernel) (x : ℝ) {n : ℕ} (hn : n ≠ 0) :
    (K.summand (1 : DirichletCharacter ℂ 1) x n).re / Real.sqrt x =
      ArithmeticFunction.vonMangoldt n *
          ((K.transform ((n : ℝ) / x)).re / Real.sqrt ((n : ℝ) / x)) /
        x := by
  simp only [summand, ite_eq_right hn, MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1)),
    mul_one, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hd : Real.sqrt ((n : ℝ) / x) * x = Real.sqrt (n : ℝ) * Real.sqrt x := by
    rw [Real.sqrt_div (Nat.cast_nonneg n), div_mul_eq_mul_div, mul_div_assoc, Real.div_sqrt]
  calc
    _ =
        (ArithmeticFunction.vonMangoldt n * (K.transform ((n : ℝ) / x)).re) /
          (Real.sqrt (n : ℝ) * Real.sqrt x) :=
      by ring
    _ =
        (ArithmeticFunction.vonMangoldt n * (K.transform ((n : ℝ) / x)).re) /
          (Real.sqrt ((n : ℝ) / x) * x) :=
      by rw [hd]
    _ = _ := by ring

/-- A finite level-one real sum divided by the square root of the scale is the normalized
Mangoldt sum with comparison weight. Apply the summand identity on positive indices.
This connects the arithmetic limit to the principal sum appearing in the subgroup bound. -/
theorem sum_level_one_re_div_sqrt (K : MellinKernel) (x y : ℝ) :
    (∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, (K.summand (1 : DirichletCharacter ℂ 1) x n).re) / Real.sqrt x =
      (∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
          ArithmeticFunction.vonMangoldt n *
            ((K.transform ((n : ℝ) / x)).re / Real.sqrt ((n : ℝ) / x))) /
        x := by
  rw [Finset.sum_div, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  exact level_one_summand_re_div_sqrt K x (Nat.ne_of_gt (Finset.mem_Ioc.mp hn).1)

/-- Under RH, a fixed positive cutoff and any positive allowance give an eventual lower
bound for the finite level-one sum by the square root of the scale times the integral minus
the allowance. Multiply the normalized comparison by the positive square root.
This is the main term before the modulus correction. -/
theorem eventually_level_one_sum_ge_integral (K : MellinKernel) (hRH : RiemannHypothesis) {b ε : ℝ}
    (hb : 0 < b) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in Filter.atTop,
      Real.sqrt x * ((∫ u in 0..b, (K.transform u).re / Real.sqrt u) - ε) ≤
        ∑ n ∈ Finset.Ioc 0 ⌊b * x⌋₊, (K.summand (1 : DirichletCharacter ℂ 1) x n).re := by
  filter_upwards [eventually_integral_le_weighted_mangoldt_sum K hRH hb hε,
    Filter.eventually_gt_atTop (0 : ℝ)] with x hxlower hx
  have h :=
    (le_div_iff₀ (Real.sqrt_pos.mpr hx)).mp
      (show
        (∫ u in 0..b, (K.transform u).re / Real.sqrt u) - ε ≤
          (∑ n ∈ Finset.Ioc 0 ⌊b * x⌋₊, (K.summand (1 : DirichletCharacter ℂ 1) x n).re) /
            Real.sqrt x
        by
        rw [sum_level_one_re_div_sqrt]
        exact hxlower)
  simpa only [mul_comm] using h

/-- A kernel-dependent positive constant bounds the difference between finite level-one
and principal-character real sums by `C log(q) log(x)/sqrt(x)` for nonzero modulus,
scale at least two and nonnegative cutoff. The primitive source of the principal character
has level one; apply the absolute finite primitivization bound to its real difference.
The estimate is uniform in the modulus and cutoff. -/
theorem exists_principal_finite_difference_le (K : MellinKernel) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ {q : ℕ} [NeZero q] {x y : ℝ},
          2 ≤ x →
            0 ≤ y →
            (∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, (K.summand (1 : DirichletCharacter ℂ 1) x n).re) -
                (∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, (K.summand (1 : DirichletCharacter ℂ q) x n).re) ≤
              C * Real.log q * Real.log x / Real.sqrt x := by
  obtain ⟨C, hC, hb⟩ := exists_sum_norm_summand_sub_primitive_le_log K
  refine ⟨C, hC, ?_⟩
  intro q _ x y hx hy
  have he :
    ∀ n : ℕ,
      K.summand (1 : DirichletCharacter ℂ q).primitiveCharacter x n =
        K.summand (1 : DirichletCharacter ℂ 1) x n := by
    intro n
    have hn : IsUnit (n : ZMod ((1 : DirichletCharacter ℂ q).conductor)) := by
      rw [DirichletCharacter.conductor_one]
      exact isUnit_of_subsingleton _
    rw [summand, summand, DirichletCharacter.primitiveCharacter_one, MulChar.one_apply hn,
      MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1))]
  have h := hb (1 : DirichletCharacter ℂ q) hx hy
  simp only [he] at h
  let D :=
    ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
      (K.summand (1 : DirichletCharacter ℂ q) x n - K.summand (1 : DirichletCharacter ℂ 1) x n)
  have hn := (neg_le_abs D.re).trans ((Complex.abs_re_le_norm D).trans ((norm_sum_le _ _).trans h))
  simpa only [D, Complex.re_sum, Complex.sub_re, Finset.sum_sub_distrib, neg_sub] using hn

/-- Under RH, a positive kernel-dependent constant gives the eventual integral lower
bound for every nonzero modulus at once. For each fixed positive cutoff and allowance,
the finite principal sum is bounded below by `sqrt(x) * (integral - allowance)` minus
`C log(q) log(x)/sqrt(x)`. Combine the level-one lower bound and the finite modulus
correction. This removes the missing integral lower premise from the subgroup comparison. -/
theorem exists_eventually_principal_sum_ge_integral (K : MellinKernel) (hRH : RiemannHypothesis) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ {b ε : ℝ},
          0 < b →
            0 < ε →
            ∀ᶠ x : ℝ in Filter.atTop,
              ∀ (q : ℕ) [NeZero q],
                Real.sqrt x * ((∫ u in 0..b, (K.transform u).re / Real.sqrt u) - ε) -
                    C * Real.log q * Real.log x / Real.sqrt x ≤
                  ∑ n ∈ Finset.Icc 1 ⌊b * x⌋₊, (K.summand (1 : DirichletCharacter ℂ q) x n).re := by
  obtain ⟨C, hC, hb⟩ := exists_principal_finite_difference_le K
  refine ⟨C, hC, ?_⟩
  intro b ε hbpos hε
  filter_upwards [eventually_level_one_sum_ge_integral K hRH hbpos hε,
    Filter.eventually_ge_atTop (2 : ℝ)] with x hl hx
  intro q _
  have hxp : 0 < x := (by norm_num only : (0 : ℝ) < 2).trans_le hx
  have hd := hb (q := q) hx (mul_nonneg hbpos.le hxp.le)
  have h :
    Real.sqrt x * ((∫ u in 0..b, (K.transform u).re / Real.sqrt u) - ε) -
        C * Real.log q * Real.log x / Real.sqrt x ≤
      ∑ n ∈ Finset.Ioc 0 ⌊b * x⌋₊, (K.summand (1 : DirichletCharacter ℂ q) x n).re := by
    linarith only [hl, hd]
  simpa only [← Finset.Icc_add_one_left_eq_Ioc, zero_add] using h

end PseudoPrime.LLS.PaperStatements.MellinKernel
