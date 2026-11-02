/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.RationalPoleSecondVariation
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.LogWeightedSummationByParts
public import PseudoPrime.LLS.PaperStatements.RationalPolePrincipalSupport

/-!
# Exact double Abel identities for the actual fourth-pole principal sums

Clipped logarithmic atoms vanish before their positive locations. Their integrability,
proved using the actual second density, justifies each finite sum and integral exchange.
The natural-floor cutoff includes integer endpoints. The unit cutoff retains its Chebyshev
boundary term; only the full support endpoint has both weight and derivative equal to zero.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- A clipped logarithmic atom times the actual second density is integrable through
any nonnegative endpoint in the support. Restrict the integrable density and multiply
by the continuous atom on the enclosing compact interval.
This justifies finite atom reconstruction without requiring smoothness at zero. -/
theorem fourPole_clipped_integrable {v y : ℝ} (hv : 0 < v) (hy : 0 ≤ y)
    (hyb : y ≤ Real.exp (28 / 25 : ℝ)) :
    IntervalIntegrable (fun u : ℝ ↦ Analysis.positiveLogRatio v u * fourPoleSecondDensity u)
      MeasureTheory.volume 0 y := by
  have hQ := fourPole_second_integrable.mono_set (Set.Ioc_subset_Ioc le_rfl hyb)
  have hprod :=
    MeasureTheory.IntegrableOn.mul_continuousOn_of_subset hQ
      (Analysis.positiveLogRatio_continuous hv).continuousOn measurableSet_Ioc isCompact_Icc
      (Set.Ioc_subset_Icc_self : Set.Ioc (0 : ℝ) y ⊆ _)
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hy).mpr
  simpa only [mul_comm] using hprod

/-- For a positive atom through the support endpoint, recover its K4 weight by
integrating the clipped logarithm against the second density and retaining both boundaries.
The atom vanishes below its location; the logarithmic primitive evaluates the rest.
This is the exact scalar identity used before finite arithmetic summation. -/
theorem fourPole_log_atom {v y : ℝ} (hv : 0 < v) (hvy : v ≤ y) (hyb : y ≤ Real.exp (28 / 25 : ℝ)) :
    fourPoleWeight v =
      (∫ u : ℝ in (0 : ℝ)..y, Analysis.positiveLogRatio v u * fourPoleSecondDensity u) -
          y * fourPoleWeightDeriv y * Real.log (y / v) +
        fourPoleWeight y := by
  have hy : 0 ≤ y := hv.le.trans hvy
  have hi := fourPole_clipped_integrable hv hy hyb
  have hi0v :
    IntervalIntegrable (fun u : ℝ ↦ Analysis.positiveLogRatio v u * fourPoleSecondDensity u)
      MeasureTheory.volume 0 v :=
    hi.mono_set
      (by
        rw [Set.uIcc_of_le hy, Set.uIcc_of_le hv.le]
        exact Set.Icc_subset_Icc_right hvy)
  have hivy :
    IntervalIntegrable (fun u : ℝ ↦ Analysis.positiveLogRatio v u * fourPoleSecondDensity u)
      MeasureTheory.volume v y :=
    hi.mono_set
      (by
        rw [Set.uIcc_of_le hy, Set.uIcc_of_le hvy]
        exact Set.Icc_subset_Icc_left hv.le)
  have hlog :
    IntervalIntegrable (fun u : ℝ ↦ Real.log (u / v) * fourPoleSecondDensity u) MeasureTheory.volume
      v y := by
    apply IntervalIntegrable.congr ?_ hivy
    intro u hu
    rw [Set.uIoc_of_le hvy] at hu
    dsimp only
    rw [Analysis.positiveLogRatio_eq_log hu.1.le]
  have hz :
    (∫ u : ℝ in (0 : ℝ)..v, Analysis.positiveLogRatio v u * fourPoleSecondDensity u) = 0 := by
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
    (∫ u : ℝ in v..y, Analysis.positiveLogRatio v u * fourPoleSecondDensity u) =
      ∫ u : ℝ in v..y, Real.log (u / v) * fourPoleSecondDensity u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le hvy] at hu
    dsimp only
    rw [Analysis.positiveLogRatio_eq_log hu.1]
  rw [heq,
    Analysis.log_variation_integral hv hv hvy
      (fun u hu ↦ fourPoleWeight_hasDerivAt (hv.trans_le hu.1))
      (fun u hu ↦ fourPoleWeight_log_deriv (hv.trans_le hu.1)) hlog,
    Real.log_div_self]
  ring

/-- A real coefficient scales the exact clipped atom identity and both boundary terms.
Move the coefficient outside the integral and normalize multiplication.
This prepares the finite interchange while retaining the hard-cutoff contribution. -/
private theorem fourPole_weighted_log_atom {v y : ℝ} (hv : 0 < v) (hvy : v ≤ y)
    (hyb : y ≤ Real.exp (28 / 25 : ℝ)) (c : ℝ) :
    c * fourPoleWeight v =
      (∫ u : ℝ in (0 : ℝ)..y, (c * Analysis.positiveLogRatio v u) * fourPoleSecondDensity u) -
          (y * fourPoleWeightDeriv y) * (c * Analysis.positiveLogRatio v y) +
        fourPoleWeight y * c := by
  have h := congrArg (fun z : ℝ ↦ c * z) (fourPole_log_atom hv hvy hyb)
  rw [Analysis.positiveLogRatio_eq_log hvy]
  simp only [mul_assoc, intervalIntegral.integral_const_mul]
  linarith only [h]

/-- Any finite family of positive atoms below the supported cutoff obeys the exact
second-Abel identity, including its logarithmic and plain boundary sums.
Sum the weighted atom identities and exchange the justified finite integrals.
This supplies the arithmetic reconstruction without abstract summation premises. -/
theorem fourPole_finite_log_identity {ι : Type*} (s : Finset ι) (c v : ι → ℝ) {y : ℝ} (hy : 0 ≤ y)
    (hyb : y ≤ Real.exp (28 / 25 : ℝ)) (hv : ∀ i ∈ s, 0 < v i) (hvy : ∀ i ∈ s, v i ≤ y) :
    (∑ i ∈ s, c i * fourPoleWeight (v i)) =
      (∫ u : ℝ in (0 : ℝ)..y,
            (∑ i ∈ s, c i * Analysis.positiveLogRatio (v i) u) * fourPoleSecondDensity u) -
          (y * fourPoleWeightDeriv y) * (∑ i ∈ s, c i * Analysis.positiveLogRatio (v i) y) +
        fourPoleWeight y * (∑ i ∈ s, c i) := by
  have he :=
    Finset.sum_congr rfl (fun i hi ↦ fourPole_weighted_log_atom (hv i hi) (hvy i hi) hyb (c i))
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at he
  have hi (i : ι) (his : i ∈ s) :
    IntervalIntegrable
      (fun u : ℝ ↦ (c i * Analysis.positiveLogRatio (v i) u) * fourPoleSecondDensity u)
      MeasureTheory.volume 0 y := by
    simpa only [mul_assoc] using (fourPole_clipped_integrable (hv i his) hy hyb).const_mul (c i)
  rw [← intervalIntegral.integral_finsetSum hi] at he
  simpa only [Finset.sum_mul] using he

/-- For positive scale and a supported nonnegative endpoint, the actual finite K4
principal sum equals its double-Abel integral and both displayed boundary terms.
Use positive integer atoms through the natural floor, identify the actual kernel weight,
and reconstruct the genuine Mangoldt and Chebyshev sums. No zero atom is introduced.
This covers integer cutoffs and provides both the unit and full-support identities. -/
theorem fourPole_mangoldt_double_abel {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y)
    (hyb : y ≤ Real.exp (28 / 25 : ℝ)) :
    (∑ n ∈ Finset.Ioc 0 ⌊x * y⌋₊, ArithmeticFunction.vonMangoldt n * fourScaledWeight x n) =
      ((∫ u : ℝ in (0 : ℝ)..y,
              AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) *
                fourPoleSecondDensity u) -
            y * fourPoleWeightDeriv y *
              AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * y) +
          fourPoleWeight y * Chebyshev.psi (x * y)) /
        Real.sqrt x := by
  have hv (n : ℕ) (hn : n ∈ Finset.Ioc 0 ⌊x * y⌋₊) : 0 < (n : ℝ) / x :=
    div_pos (Nat.cast_pos.mpr (Finset.mem_Ioc.mp hn).1) hx
  have hvy (n : ℕ) (hn : n ∈ Finset.Ioc 0 ⌊x * y⌋₊) : (n : ℝ) / x ≤ y := by
    have hnle := (Nat.le_floor_iff (mul_nonneg hx.le hy)).mp (Finset.mem_Ioc.mp hn).2
    exact (div_le_iff₀ hx).mpr (by linarith only [hnle])
  have h :=
    fourPole_finite_log_identity (Finset.Ioc 0 ⌊x * y⌋₊) (fun n ↦ ArithmeticFunction.vonMangoldt n)
      (fun n ↦ (n : ℝ) / x) hy hyb hv hvy
  have hI :
    (∫ u : ℝ in (0 : ℝ)..y,
        (∑ n ∈ Finset.Ioc 0 ⌊x * y⌋₊,
            ArithmeticFunction.vonMangoldt n * Analysis.positiveLogRatio ((n : ℝ) / x) u) *
          fourPoleSecondDensity u) =
      ∫ u : ℝ in (0 : ℝ)..y,
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) *
          fourPoleSecondDensity u := by
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
            ArithmeticFunction.vonMangoldt n * fourPoleWeight ((n : ℝ) / x)) /
          Real.sqrt x :=
      by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro n hn
      have hw : fourPoleKernelWeight ((n : ℝ) / x) = fourPoleWeight ((n : ℝ) / x) :=
        fourPoleKernelWeight_eq (hv n hn)
          ((Real.log_le_iff_le_exp (hv n hn)).mpr ((hvy n hn).trans hyb))
      dsimp only [fourScaledWeight]
      rw [hw]
      ring
    _ = _ := congrArg (fun z : ℝ ↦ z / Real.sqrt x) h

/-- At every positive scale, the actual unit-cutoff principal sum has the exact
second-Abel expression, including w(1)*psi(x) and -w'(1)*M(x).
Specialize the supported finite identity to endpoint one.
The retained Chebyshev term is essential for the improved hard-cutoff error bound. -/
theorem fourPole_cutoff_double_abel {x : ℝ} (hx : 0 < x) :
    (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * fourScaledWeight x n) =
      ((∫ u : ℝ in (0 : ℝ)..1,
              AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) *
                fourPoleSecondDensity u) -
            fourPoleWeightDeriv 1 * AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum x +
          fourPoleWeight 1 * Chebyshev.psi x) /
        Real.sqrt x := by
  have hb : (1 : ℝ) ≤ Real.exp (28 / 25 : ℝ) := Real.one_le_exp_iff.mpr (by norm_num only)
  simpa only [mul_one, one_mul] using fourPole_mangoldt_double_abel hx zero_le_one hb

/-- At every positive scale, the full actual principal series equals its supported
second-Abel integral divided by the square root of the scale.
The exact support coordinate makes the weight and derivative zero at the upper endpoint;
the proved finite-support series identity then removes both boundary terms. -/
theorem fourPole_full_double_abel {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ, (MellinKernel.summand rationalPoleFourKernel) (1 : DirichletCharacter ℂ 1) x n).re =
      (∫ u : ℝ in (0 : ℝ)..Real.exp (28 / 25 : ℝ),
          AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) *
            fourPoleSecondDensity u) /
        Real.sqrt x := by
  have h := fourPole_mangoldt_double_abel hx (Real.exp_pos (28 / 25 : ℝ)).le le_rfl
  have hw : fourPoleWeight (Real.exp (28 / 25 : ℝ)) = 0 := by
    norm_num only [fourPoleWeight, fourPoleCoord_support, zero_pow, zero_mul, zero_div]
  have hd : fourPoleWeightDeriv (Real.exp (28 / 25 : ℝ)) = 0 := by
    norm_num only [fourPoleWeightDeriv, fourPoleCoord_support, zero_pow, mul_zero, sub_zero]
  simp only [hw, hd, mul_zero, zero_mul, sub_zero, add_zero] at h
  rw [fourPole_principal_sum_finite hx]
  simpa only [mul_comm x (Real.exp (28 / 25 : ℝ))] using h

end PseudoPrime.LLS.PaperStatements
