/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaTruncatedBounds
public import PseudoPrime.LLS.MellinKernelPrimitiveSupport

/-! # Numerical full principal Gamma sum

The finite upper Abel bound passes to the convergent level-one Gamma series.
This gives an explicit principal term without a scale threshold or unknown error.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under RH, at any positive scale and natural cutoff, the finite level-one
Gamma sum is at most sqrt(x)+13x^(1/4). Apply the upper Abel estimate with
the uniform Chebyshev error thirteen and the exact Gamma summand identity.
The bound is independent of cutoff and supports passage to the full series. -/
theorem gamma_level_one_finite_sum_upper_thirteen (hRH : RiemannHypothesis) {x : ℝ} (hx : 0 < x)
    (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, (gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re ≤
      Real.sqrt x + 13 * x ^ (1 / 4 : ℝ) := by
  have h :=
    AnalyticNumberTheory.Arithmetic.exponentialMangoldtSum_div_sqrt_upper_of_psi_error
      (by norm_num only : (0 : ℝ) ≤ 13) hx (Nat.cast_nonneg N)
      (fun t ht ↦ LLS.psi_error_le_thirteen hRH ht)
  rw [← gamma_level_one_sum_eq_exponential hx] at h
  simpa only [Nat.floor_natCast] using h

/-- Under RH, the full level-one Gamma sum has real part at most
sqrt(x)+13x^(1/4) at every positive scale. Transfer the finite upper bounds
to the absolutely convergent nonnegative series using range partial sums.
This is the numerical principal term in the primitive Gamma comparison. -/
theorem gamma_level_one_sum_upper_thirteen (hRH : RiemannHypothesis) {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ, gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re ≤
      Real.sqrt x + 13 * x ^ (1 / 4 : ℝ) := by
  have hs := MellinKernel.summable_summand gammaMellinKernel (1 : DirichletCharacter ℂ 1) hx
  change Complex.reCLM (∑' n : ℕ, gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n) ≤ _
  rw [Complex.reCLM.map_tsum hs]
  apply (Complex.reCLM.summable hs).tsum_le_of_sum_range_le
  intro N
  have hzero : (gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x 0).re = 0 := by
    simp only [MellinKernel.summand, ite_true, Complex.zero_re]
  have he :
    (∑ n ∈ Finset.Icc 0 N, (gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re) =
      ∑ n ∈ Finset.Ioc 0 N, (gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re := by
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le N), Finset.sum_cons, hzero, zero_add]
  have hsub : Finset.range N ⊆ Finset.Icc 0 N := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le n, (Finset.mem_range.mp hn).le⟩
  calc
    _ ≤ ∑ n ∈ Finset.Icc 0 N, (gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun n _ _ ↦ MellinKernel.principal_summand_re_nonneg gammaMellinKernel hx n)
    _ = _ := he
    _ ≤ _ := gamma_level_one_finite_sum_upper_thirteen hRH hx N

/-- Under RH, the primitive source of every nonzero-level principal Gamma
series has real part at most sqrt(x)+13x^(1/4), for x>0.
Its summands equal the level-one principal summands; apply the full upper bound.
This is the principal term in the aggregate primitive-character comparison. -/
theorem gamma_primitive_principal_sum_upper_thirteen (hRH : RiemannHypothesis) {q : ℕ} [NeZero q]
    {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ, gammaMellinKernel.summand (1 : DirichletCharacter ℂ q).primitiveCharacter x n).re ≤
      Real.sqrt x + 13 * x ^ (1 / 4 : ℝ) := by
  rw [tsum_congr
      (MellinKernel.principal_primitive_summand_eq_level_one gammaMellinKernel (q := q) x)]
  exact gamma_level_one_sum_upper_thirteen hRH hx

end PseudoPrime.LLS.PaperStatements
