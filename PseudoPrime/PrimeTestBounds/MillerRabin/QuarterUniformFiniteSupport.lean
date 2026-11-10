/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformFromBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleFullPrincipal

/-! # Finite-support principal bounds for uniform triple cells -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At positive scale, the complex principal series has exactly the finite
support cutoff. Absolute convergence permits taking real parts termwise. -/
theorem quarter_principal_support {X : ℝ} (hX : 0 < X) :
    (∑' k : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re =
      ∑ k ∈ Finset.Ioc 0 ⌊X * Real.exp (21 / 8 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re := by
  have hs :=
    LLS.PaperStatements.MellinKernel.summable_summand refinedSixPoleKernel
      (1 : DirichletCharacter ℂ 1) hX
  change Complex.reCLM (∑' k : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k) = _
  rw [Complex.reCLM.map_tsum hs]
  exact refined_principal_sum_finite hX

/-- The support endpoint of the sixth-pole kernel is below fourteen.
A rational Taylor envelope certifies the exponential comparison. -/
theorem quarter_kernel_support_le_fourteen : Real.exp (21 / 8 : ℝ) ≤ 14 := by
  have ht :=
    Analysis.exp_le_taylor_add_two_next (x := (21 / 8 : ℝ)) (n := 16) (by norm_num only)
      (by norm_num only)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at ht
  linarith only [ht]

/-- The full principal sum is bounded by its finite sum through `14 * X`.
The kernel vanishes beyond its support and the additional summands are nonnegative. -/
theorem quarter_principal_support_upper {X : ℝ} (hX : 0 < X) :
    (∑' k : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re ≤
      ∑ k ∈ Finset.Ioc 0 ⌊14 * X⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re := by
  rw [quarter_principal_support hX]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    have hk' := Finset.mem_Ioc.mp hk
    apply Finset.mem_Ioc.mpr
    refine ⟨hk'.1, hk'.2.trans ?_⟩
    apply Nat.floor_mono
    nlinarith only [quarter_kernel_support_le_fourteen, hX]
  · intro k hk hnot
    exact LLS.PaperStatements.MellinKernel.principal_summand_re_nonneg refinedSixPoleKernel hX k

/-- A finite-support upper bound for the principal sum, together with the
finite lower bounds and cell budget, yields a quarter-square witness for a
uniform Korselt triple. No estimate for an infinite tail is required. -/
theorem quarter_uniform_of_finite_support {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {X U S P F H : ℝ} (hX : 1 ≤ X) (hH : refinedReflectedEuler (1 : DirichletCharacter ℂ 1) X ≤ H)
    (hU : Real.log n ≤ U) (hcut : X ≤ (1 / 4 : ℝ) * Real.log n ^ 2)
    (hS :
      S ≤
        ∑ k ∈ Finset.Ioc 0 ⌊X⌋₊, (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re)
    (hP : P ≤ ∑ k ∈ Finset.Ioc 0 ⌊X⌋₊, ArithmeticFunction.vonMangoldt k * refinedSixEulerWeight k)
    (hF :
      (∑ k ∈ Finset.Ioc 0 ⌊14 * X⌋₊,
          (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re) ≤
        F)
    (hcert : quarterUniformBudget X U P F H ≤ 4 * S) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply quarter_uniform_of_bounds hn ho hu hGRH hX hH hU hcut hS hP _ hcert
  exact (quarter_principal_support_upper (zero_lt_one.trans_le hX)).trans hF

end PseudoPrime.PrimeTestBounds.MillerRabin
