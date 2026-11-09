/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.GammaPrincipalUpperBounds
public import PseudoPrime.LLS.GammaSmoothedPrincipalBounds
public import PseudoPrime.LLS.RiemannExponentialErrorBounds
public import PseudoPrime.Analysis.ExponentialPolynomialMoments
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ExponentialLogWeightedSummation
public import PseudoPrime.LLS.GammaExponentialPrincipalBounds

/-! # Full principal Gamma sum with explicit error one fifth -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under RH and L>=46000, every finite level-one Gamma sum at scale
(32/99)L^2 is at most sqrt(x)+1/5. Transfer the actual exponential sum bound
to the proved Gamma summand identity and cancel x/sqrt(x).
This is the cutoff-uniform input for the convergent full Gamma series. -/
theorem gamma_level_one_finite_sum_upper_one_fifth (hRH : RiemannHypothesis) {L : ℝ}
    (hL : 46000 ≤ L) (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N,
        (gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) ((32 / 99 : ℝ) * L ^ 2) n).re ≤
      Real.sqrt ((32 / 99 : ℝ) * L ^ 2) + 1 / 5 := by
  have hx0 : 0 < (32 / 99 : ℝ) * L ^ 2 := zero_lt_one.trans_le (ramp_scale_ge_one hL)
  have heq :
    (∑ n ∈ Finset.Ioc 0 N,
        (gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) ((32 / 99 : ℝ) * L ^ 2) n).re) =
      AnalyticNumberTheory.Arithmetic.exponentialMangoldtSum ((32 / 99 : ℝ) * L ^ 2) (N : ℝ) /
        Real.sqrt ((32 / 99 : ℝ) * L ^ 2) := by
    simpa only [Nat.floor_natCast] using gamma_level_one_sum_eq_exponential (y := (N : ℝ)) hx0
  rw [heq]
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hx0)).mpr
  rw [add_mul, ← pow_two, Real.sq_sqrt hx0.le]
  have hraw := exponentialMangoldtSum_upper_uniform hRH (ramp_scale_ge_one hL) N
  have herr := gamma_exponential_error_le_one_fifth_root hL
  linarith only [hraw, herr]

/-- At positive scale, the range partial sum is at most the positive closed-cutoff
sum through N. The zero summand vanishes and the added terms are nonnegative.
This matches the summable-series API to the arithmetic cutoff convention. -/
private theorem gamma_level_one_sum_range_le_Ioc {x : ℝ} (hx : 0 < x) (N : ℕ) :
    (∑ n ∈ Finset.range N, (gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re) ≤
      ∑ n ∈ Finset.Ioc 0 N, (gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re := by
  have hsub : Finset.range N ⊆ Finset.Icc 0 N := fun n hn ↦
    Finset.mem_Icc.mpr ⟨Nat.zero_le n, (Finset.mem_range.mp hn).le⟩
  have h :=
    Finset.sum_le_sum_of_subset_of_nonneg (f := fun n : ℕ ↦
      (gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re) hsub
      (fun n _ _ ↦ MellinKernel.principal_summand_re_nonneg gammaMellinKernel hx n)
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le N), Finset.sum_cons] at h
  simpa only [MellinKernel.summand, ite_true, Complex.zero_re, zero_add] using h

/-- At positive scale, a common upper bound for every finite positive-index
Gamma sum bounds the real part of the full convergent series. Use the existing
absolute summability and the real continuous-linear map on the sum.
This supplies the quantitative full-series transfer without an analytic placeholder. -/
theorem gamma_level_one_sum_upper_of_finite_upper {x C : ℝ} (hx : 0 < x)
    (hC :
      ∀ N : ℕ,
        ∑ n ∈ Finset.Ioc 0 N, (gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re ≤ C) :
    (∑' n : ℕ, gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re ≤ C := by
  have hs := MellinKernel.summable_summand gammaMellinKernel (1 : DirichletCharacter ℂ 1) hx
  change Complex.reCLM (∑' n : ℕ, gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n) ≤ C
  rw [Complex.reCLM.map_tsum hs]
  exact
    (Complex.reCLM.summable hs).tsum_le_of_sum_range_le
      (fun N ↦ (gamma_level_one_sum_range_le_Ioc hx N).trans (hC N))

/-- Under RH and L>=46000, the actual full level-one Gamma series at scale
(32/99)L^2 has real part at most sqrt(x)+1/5. Apply the proved finite uniform
upper bound to the existing convergent series. This is the full principal contract P1. -/
theorem gamma_level_one_sum_upper_one_fifth (hRH : RiemannHypothesis) {L : ℝ} (hL : 46000 ≤ L) :
    (∑' n : ℕ,
          gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) ((32 / 99 : ℝ) * L ^ 2) n).re ≤
      Real.sqrt ((32 / 99 : ℝ) * L ^ 2) + 1 / 5 := by
  exact
    gamma_level_one_sum_upper_of_finite_upper (zero_lt_one.trans_le (ramp_scale_ge_one hL))
      (gamma_level_one_finite_sum_upper_one_fifth hRH hL)

/-- Under RH and L>=46000, the primitive source of the principal character
at every nonzero level has full Gamma series real part at most sqrt(x)+1/5.
Identify its summands with the level-one summands and use the new full bound.
This supplies the principal term to the quadratic comparison at the original level. -/
theorem gamma_primitive_principal_sum_upper_one_fifth (hRH : RiemannHypothesis) {q : ℕ} [NeZero q]
    {L : ℝ} (hL : 46000 ≤ L) :
    (∑' n : ℕ,
          gammaMellinKernel.summand (1 : DirichletCharacter ℂ q).primitiveCharacter
            ((32 / 99 : ℝ) * L ^ 2) n).re ≤
      Real.sqrt ((32 / 99 : ℝ) * L ^ 2) + 1 / 5 := by
  rw [tsum_congr
      (MellinKernel.principal_primitive_summand_eq_level_one gammaMellinKernel (q := q)
        ((32 / 99 : ℝ) * L ^ 2))]
  exact gamma_level_one_sum_upper_one_fifth hRH hL

end PseudoPrime.LLS.PaperStatements
