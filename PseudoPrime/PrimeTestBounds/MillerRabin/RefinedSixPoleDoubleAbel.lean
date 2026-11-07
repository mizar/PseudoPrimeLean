/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleSecondMoment
public import PseudoPrime.LLS.PaperStatements.RationalPoleDoubleAbel

/-! # Double Abel identity for the refined principal sum -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

theorem refined_abel_clipped_integrable {v y : ℝ} (hv : 0 < v) (hy : 0 ≤ y)
    (hyb : y ≤ Real.exp (21 / 8 : ℝ)) :
    IntervalIntegrable (fun u : ℝ ↦ Analysis.positiveLogRatio v u * refinedSecondDensity u)
      MeasureTheory.volume 0 y := by
  have hQ := refined_second_integrable.mono_set (Set.Ioc_subset_Ioc le_rfl hyb)
  have hprod :=
    MeasureTheory.IntegrableOn.mul_continuousOn_of_subset hQ
      (Analysis.positiveLogRatio_continuous hv).continuousOn measurableSet_Ioc isCompact_Icc
      (Set.Ioc_subset_Icc_self : Set.Ioc (0 : ℝ) y ⊆ _)
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hy).mpr
  simpa only [mul_comm] using hprod

/-- For a positive atom through the support endpoint, recover its refined weight by
integrating the clipped logarithm against the second density and retaining both boundaries.
The atom vanishes below its location; the logarithmic primitive evaluates the rest.
This is the exact scalar identity used before finite arithmetic summation. -/
theorem refined_log_atom {v y : ℝ} (hv : 0 < v) (hvy : v ≤ y) (hyb : y ≤ Real.exp (21 / 8 : ℝ)) :
    refinedWeight v =
      (∫ u : ℝ in (0 : ℝ)..y, Analysis.positiveLogRatio v u * refinedSecondDensity u) -
          y * refinedWeightDeriv y * Real.log (y / v) +
        refinedWeight y := by
  have hy : 0 ≤ y := hv.le.trans hvy
  have hi := refined_abel_clipped_integrable hv hy hyb
  have hi0v :
    IntervalIntegrable (fun u : ℝ ↦ Analysis.positiveLogRatio v u * refinedSecondDensity u)
      MeasureTheory.volume 0 v :=
    hi.mono_set
      (by
        rw [Set.uIcc_of_le hy, Set.uIcc_of_le hv.le]
        exact Set.Icc_subset_Icc_right hvy)
  have hivy :
    IntervalIntegrable (fun u : ℝ ↦ Analysis.positiveLogRatio v u * refinedSecondDensity u)
      MeasureTheory.volume v y :=
    hi.mono_set
      (by
        rw [Set.uIcc_of_le hy, Set.uIcc_of_le hvy]
        exact Set.Icc_subset_Icc_left hv.le)
  have hlog :
    IntervalIntegrable (fun u : ℝ ↦ Real.log (u / v) * refinedSecondDensity u) MeasureTheory.volume
      v y := by
    apply IntervalIntegrable.congr ?_ hivy
    intro u hu
    rw [Set.uIoc_of_le hvy] at hu
    dsimp only
    rw [Analysis.positiveLogRatio_eq_log hu.1.le]
  have hz :
    (∫ u : ℝ in (0 : ℝ)..v, Analysis.positiveLogRatio v u * refinedSecondDensity u) = 0 := by
    calc
      _ = ∫ u : ℝ in (0 : ℝ)..v, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [Set.uIcc_of_le hv.le] at hu
        dsimp only
        rw [Analysis.positiveLogRatio_zero hu.2, zero_mul]
      _ = 0 := intervalIntegral.integral_zero
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hi0v hivy
  rw [hz, zero_add] at hsplit
  rw [← hsplit]
  have heq :
    (∫ u : ℝ in v..y, Analysis.positiveLogRatio v u * refinedSecondDensity u) =
      ∫ u : ℝ in v..y, Real.log (u / v) * refinedSecondDensity u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le hvy] at hu
    dsimp only
    rw [Analysis.positiveLogRatio_eq_log hu.1]
  rw [heq,
    Analysis.log_variation_integral hv hv hvy
      (fun u hu ↦ refinedWeight_hasDerivAt (hv.trans_le hu.1))
      (fun u hu ↦ refinedWeight_log_deriv (hv.trans_le hu.1)) hlog,
    Real.log_div_self]
  ring

/-- A real coefficient scales the exact clipped atom identity and both boundary terms.
Move the coefficient outside the integral and normalize multiplication.
This prepares the finite interchange while retaining the hard-cutoff contribution. -/
private theorem refined_weighted_log_atom {v y : ℝ} (hv : 0 < v) (hvy : v ≤ y)
    (hyb : y ≤ Real.exp (21 / 8 : ℝ)) (c : ℝ) :
    c * refinedWeight v =
      (∫ u : ℝ in (0 : ℝ)..y, (c * Analysis.positiveLogRatio v u) * refinedSecondDensity u) -
          (y * refinedWeightDeriv y) * (c * Analysis.positiveLogRatio v y) +
        refinedWeight y * c := by
  have h := congrArg (fun z : ℝ ↦ c * z) (refined_log_atom hv hvy hyb)
  rw [Analysis.positiveLogRatio_eq_log hvy]
  simp only [mul_assoc, intervalIntegral.integral_const_mul]
  linarith only [h]

/-- Any finite family of positive atoms below the supported cutoff obeys the exact
second-Abel identity, including its logarithmic and plain boundary sums.
Sum the weighted atom identities and exchange the justified finite integrals.
This supplies the arithmetic reconstruction without abstract summation premises. -/
theorem refined_finite_log_identity {ι : Type*} (s : Finset ι) (c v : ι → ℝ) {y : ℝ} (hy : 0 ≤ y)
    (hyb : y ≤ Real.exp (21 / 8 : ℝ)) (hv : ∀ i ∈ s, 0 < v i) (hvy : ∀ i ∈ s, v i ≤ y) :
    (∑ i ∈ s, c i * refinedWeight (v i)) =
      (∫ u : ℝ in (0 : ℝ)..y,
            (∑ i ∈ s, c i * Analysis.positiveLogRatio (v i) u) * refinedSecondDensity u) -
          (y * refinedWeightDeriv y) * (∑ i ∈ s, c i * Analysis.positiveLogRatio (v i) y) +
        refinedWeight y * (∑ i ∈ s, c i) := by
  have he :=
    Finset.sum_congr rfl (fun i hi ↦ refined_weighted_log_atom (hv i hi) (hvy i hi) hyb (c i))
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at he
  have hi (i : ι) (his : i ∈ s) :
    IntervalIntegrable
      (fun u : ℝ ↦ (c i * Analysis.positiveLogRatio (v i) u) * refinedSecondDensity u)
      MeasureTheory.volume 0 y := by
    simpa only [mul_assoc] using (refined_abel_clipped_integrable (hv i his) hy hyb).const_mul (c i)
  rw [← intervalIntegral.integral_finsetSum hi] at he
  simpa only [Finset.sum_mul] using he

/-- The real inverse-Mellin profile divided by the square root. This is the kernel
weight used to express the principal arithmetic summand at a positive scale. -/
noncomputable def refinedKernelWeight (u : ℝ) : ℝ :=
  (refinedSixPoleKernel.transform u).re / Real.sqrt u

/-- The principal weight at scale `x`, including the square-root normalization.
The summand identity connects it to the original Mellin-kernel arithmetic sum. -/
noncomputable def refinedScaledWeight (x t : ℝ) : ℝ :=
  refinedKernelWeight (t / x) / Real.sqrt x

/-- For positive scale and a cutoff in the support, the finite Mangoldt sum has an
exact double Abel expression with both boundary terms. Apply the finite atom identity
to positive integers and identify the logarithmically weighted and Chebyshev sums. -/
theorem refined_mangoldt_double_abel {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y)
    (hyb : y ≤ Real.exp (21 / 8 : ℝ)) :
    (∑ n ∈ Finset.Ioc 0 ⌊x * y⌋₊, ArithmeticFunction.vonMangoldt n * refinedScaledWeight x n) =
      ((∫ u : ℝ in (0 : ℝ)..y,
              AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) *
                refinedSecondDensity u) -
            y * refinedWeightDeriv y *
              AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * y) +
          refinedWeight y * Chebyshev.psi (x * y)) /
        Real.sqrt x := by
  have hv (n : ℕ) (hn : n ∈ Finset.Ioc 0 ⌊x * y⌋₊) : 0 < (n : ℝ) / x :=
    div_pos (Nat.cast_pos.mpr (Finset.mem_Ioc.mp hn).1) hx
  have hvy (n : ℕ) (hn : n ∈ Finset.Ioc 0 ⌊x * y⌋₊) : (n : ℝ) / x ≤ y := by
    have hnle := (Nat.le_floor_iff (mul_nonneg hx.le hy)).mp (Finset.mem_Ioc.mp hn).2
    exact (div_le_iff₀ hx).mpr (by linarith only [hnle])
  have h :=
    refined_finite_log_identity (Finset.Ioc 0 ⌊x * y⌋₊) (fun n ↦ ArithmeticFunction.vonMangoldt n)
      (fun n ↦ (n : ℝ) / x) hy hyb hv hvy
  have hI :
    (∫ u : ℝ in (0 : ℝ)..y,
        (∑ n ∈ Finset.Ioc 0 ⌊x * y⌋₊,
            ArithmeticFunction.vonMangoldt n * Analysis.positiveLogRatio ((n : ℝ) / x) u) *
          refinedSecondDensity u) =
      ∫ u : ℝ in (0 : ℝ)..y,
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) *
          refinedSecondDensity u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le hy] at hu
    dsimp only
    rw [← AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum_eq_clipped_scaled hx hu.1 hu.2]
  rw [hI, ← AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum_eq_clipped_scaled hx hy le_rfl, ←
    AnalyticNumberTheory.Arithmetic.psi_eq_positive_sum] at h
  calc
    _ =
        (∑ n ∈ Finset.Ioc 0 ⌊x * y⌋₊,
            ArithmeticFunction.vonMangoldt n * refinedWeight ((n : ℝ) / x)) /
          Real.sqrt x :=
      by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro n hn
      have hw : refinedKernelWeight ((n : ℝ) / x) = refinedWeight ((n : ℝ) / x) :=
        refinedKernelWeight_eq (hv n hn)
          ((Real.log_le_iff_le_exp (hv n hn)).mpr ((hvy n hn).trans hyb))
      dsimp only [refinedScaledWeight]
      rw [hw]
      ring
    _ = _ := congrArg (fun z : ℝ ↦ z / Real.sqrt x) h

/-- At a positive scale and nonzero index, the level-one principal summand equals
the scaled Mangoldt weight. Unfold the summand and normalize the square-root quotient. -/
theorem refined_principal_summand_eq {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : n ≠ 0) :
    (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) x n).re =
      ArithmeticFunction.vonMangoldt n * refinedScaledWeight x n := by
  simp only [LLS.PaperStatements.MellinKernel.summand, ite_eq_right hn,
    MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1)), mul_one, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  dsimp only [refinedScaledWeight, refinedKernelWeight]
  rw [Real.sqrt_div (Nat.cast_nonneg n)]
  have hs := (Real.sqrt_pos.mpr hx).ne'
  rw [div_div, div_mul_cancel₀ _ hs]
  ring

/-- The actual level-one finite principal sum satisfies the exact double Abel identity
on the positive support, including both endpoint terms. Substitute the principal summand
identity into the Mangoldt formula; this is the input for quantitative cutoff bounds. -/
theorem refined_principal_double_abel {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y)
    (hyb : y ≤ Real.exp (21 / 8 : ℝ)) :
    (∑ n ∈ Finset.Ioc 0 ⌊x * y⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) x n).re) =
      ((∫ u : ℝ in (0 : ℝ)..y,
              AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) *
                refinedSecondDensity u) -
            y * refinedWeightDeriv y *
              AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * y) +
          refinedWeight y * Chebyshev.psi (x * y)) /
        Real.sqrt x := by
  rw [← refined_mangoldt_double_abel hx hy hyb]
  apply Finset.sum_congr rfl
  intro n hn
  exact refined_principal_summand_eq hx (Nat.ne_of_gt (Finset.mem_Ioc.mp hn).1)

end PseudoPrime.PrimeTestBounds.MillerRabin
