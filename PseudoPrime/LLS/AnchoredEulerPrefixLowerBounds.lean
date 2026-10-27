/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PowerLogBoundarySummation
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ExponentialLogWeightedSummation
public import PseudoPrime.LLS.PairedEulerExcludedBounds
public import PseudoPrime.LLS.RiemannWeightedErrorBounds
public import PseudoPrime.LLS.ReflectedSplitWitnessBounds
public import PseudoPrime.LLS.VariableRampPrincipalBounds

/-! # Anchored analytic lower bounds for finite Euler prefixes -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For a nonnegative exponent, positive ordered endpoints and a continuous lower
profile F for the actual logarithmically weighted sum, the displayed integral and
boundary expression bounds the Mangoldt power tail below. Use exact double partial
summation, integral monotonicity and nonnegative psi at the upper endpoint.
This keeps an exact finite anchor while estimating only the subsequent tail. -/
theorem power_mangoldt_tail_ge_of_logWeighted_lower {σ a b : ℝ} (hσ : 0 ≤ σ) (ha : 0 < a)
    (hab : a ≤ b) (F : ℝ → ℝ) (hF : ContinuousOn F (Set.Icc a b))
    (hl : ∀ t ∈ Set.Icc a b, F t ≤ logWeightedMangoldtSum t) :
    (∫ t in a..b, F t * (σ ^ 2 * t ^ (-σ - 1))) -
          a ^ (-σ) * (Chebyshev.psi a + σ * logWeightedMangoldtSum a) +
        b ^ (-σ) * (σ * F b) ≤
      ∑ m ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-σ) := by
  have hpos : ∀ t ∈ Set.Icc a b, 0 < t := fun t ht ↦ ha.trans_le ht.1
  have hA0 := continuousOn_logWeightedMangoldtSum_scaled (x := 1) (by norm_num only) b
  simp only [one_mul] at hA0
  have hA : ContinuousOn logWeightedMangoldtSum (Set.Icc a b) :=
    hA0.mono (fun t ht ↦ ⟨ha.le.trans ht.1, ht.2⟩)
  have hw : ContinuousOn (fun t : ℝ ↦ σ ^ 2 * t ^ (-σ - 1)) (Set.Icc a b) :=
    continuousOn_const.mul (continuousOn_id.rpow_const (fun t ht ↦ Or.inl (hpos t ht).ne'))
  have hiF := (hF.mul hw)
  have hiA := (hA.mul hw)
  rw [← Set.uIcc_of_le hab] at hiF hiA
  have hi :=
    intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hab hiF.intervalIntegrable
      hiA.intervalIntegrable
      (fun t ht ↦
        mul_le_mul_of_nonneg_right (hl t ht)
          (mul_nonneg (sq_nonneg σ) (Real.rpow_nonneg (hpos t ht).le _)))
  simp only [Pi.mul_apply] at hi
  have hb :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hl b ⟨hab, le_rfl⟩) hσ)
      (Real.rpow_nonneg (ha.trans_le hab).le (-σ))
  have hp := mul_nonneg (Real.rpow_nonneg (ha.trans_le hab).le (-σ)) (Chebyshev.psi_nonneg b)
  rw [power_mangoldt_tail_eq_log_integral σ ha hab]
  nlinarith only [hi, hb, hp]

/-- The finite Mangoldt power prefix at anchor a plus an analytic tail lower expression
to cutoff b. The upper psi term is dropped, and a lower smoothed profile F replaces
the upper smoothed value and integral. This gives a compact alternative to enumerating
all terms up to b. -/
noncomputable def anchoredPowerPrefixLower (σ a b : ℝ) (F : ℝ → ℝ) : ℝ :=
  (∑ m ∈ Finset.Ioc 0 ⌊a⌋₊, ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-σ)) +
        (∫ t in a..b, F t * (σ ^ 2 * t ^ (-σ - 1))) -
      a ^ (-σ) * (Chebyshev.psi a + σ * logWeightedMangoldtSum a) +
    b ^ (-σ) * (σ * F b)

/-- Under the continuous smoothed lower-profile assumptions and nonnegative exponent,
the anchored expression bounds the full finite Mangoldt power prefix below.
Add the exact retained prefix to the proved tail bound. This connects the analytic
estimate to a finite arithmetic sum. -/
theorem anchoredPowerPrefixLower_le {σ a b : ℝ} (hσ : 0 ≤ σ) (ha : 0 < a) (hab : a ≤ b) (F : ℝ → ℝ)
    (hF : ContinuousOn F (Set.Icc a b)) (hl : ∀ t ∈ Set.Icc a b, F t ≤ logWeightedMangoldtSum t) :
    anchoredPowerPrefixLower σ a b F ≤
      ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-σ) := by
  have ht := power_mangoldt_tail_ge_of_logWeighted_lower hσ ha hab F hF hl
  rw [power_prefix_sum_split hab]
  dsimp only [anchoredPowerPrefixLower]
  linarith only [ht]

/-- For nonnegative power exponent and logarithmic coefficient and positive ordered
cutoffs, retain the logarithmic Euler contribution at the anchor while bounding
the first power prefix analytically. Nonnegativity lets the logarithmic prefix
grow to the upper cutoff. This supplies the paired Euler weight used by witnesses. -/
theorem anchoredPowerPrefixLower_add_logPrefix_le {σ τ c a b : ℝ} (hσ : 0 ≤ σ) (hc : 0 ≤ c)
    (ha : 0 < a) (hab : a ≤ b) (F : ℝ → ℝ) (hF : ContinuousOn F (Set.Icc a b))
    (hl : ∀ t ∈ Set.Icc a b, F t ≤ logWeightedMangoldtSum t) :
    anchoredPowerPrefixLower σ a b F +
        (∑ m ∈ Finset.Ioc 0 ⌊a⌋₊, c * Real.log m * ArithmeticFunction.vonMangoldt m / (m : ℝ) ^ τ) ≤
      ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, pairedEulerPrefixWeight σ τ c m := by
  have hp := anchoredPowerPrefixLower_le hσ ha hab F hF hl
  have he :
    (∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-σ)) =
      ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, ArithmeticFunction.vonMangoldt m / (m : ℝ) ^ σ := by
    apply Finset.sum_congr rfl
    intro m _
    rw [Real.rpow_neg (Nat.cast_nonneg m), div_eq_mul_inv]
  have hsub : Finset.Ioc 0 ⌊a⌋₊ ⊆ Finset.Ioc 0 ⌊b⌋₊ :=
    Finset.Ioc_subset_Ioc le_rfl (Nat.floor_mono hab)
  have ht :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun m _ _ ↦
        div_nonneg
          (mul_nonneg (mul_nonneg hc (Real.log_natCast_nonneg m))
            (ArithmeticFunction.vonMangoldt_nonneg (n := m)))
          (Real.rpow_nonneg (Nat.cast_nonneg m) τ))
  rw [he] at hp
  simp only [pairedEulerPrefixWeight, Finset.sum_add_distrib]
  linarith only [hp, ht]

end PseudoPrime.AnalyticNumberTheory.Arithmetic

namespace PseudoPrime.LLS

/-- The RH lower profile t-sqrt(t)/20-(1839/1000)log(t)-21/20 for the smoothed
Mangoldt sum above one. It is used only on positive closed intervals and leaves
the finite lower anchor exact. -/
noncomputable def riemannSmoothedLowerProfile (t : ℝ) : ℝ :=
  t - Real.sqrt t / 20 - (1839 / 1000 : ℝ) * Real.log t - 21 / 20

/-- On a closed interval with positive left endpoint, the RH smoothed lower profile
is continuous. Combine continuity of the square root and positive-base logarithm.
This discharges the profile regularity needed by anchored partial summation. -/
theorem continuousOn_riemannSmoothedLowerProfile {a b : ℝ} (ha : 0 < a) :
    ContinuousOn riemannSmoothedLowerProfile (Set.Icc a b) := by
  have hlog : ContinuousOn Real.log (Set.Icc a b) :=
    continuousOn_id.log (fun t ht ↦ (ha.trans_le ht.1).ne')
  exact
    ((continuousOn_id.sub (Real.continuous_sqrt.continuousOn.div_const 20)).sub
          (continuousOn_const.mul hlog)).sub
      continuousOn_const

/-- Under RH, a nonnegative power exponent and logarithmic coefficient and an anchor
above one give the displayed lower bound for the actual finite paired Euler sum.
Insert the sharp RH profile into the generic anchored comparison. This avoids an
integer-input certificate and leaves only a small finite anchor to evaluate. -/
theorem anchoredEulerPrefix_lower_of_rh (hRH : RiemannHypothesis) {σ τ c a b : ℝ} (hσ : 0 ≤ σ)
    (hc : 0 ≤ c) (ha : 1 < a) (hab : a ≤ b) :
    AnalyticNumberTheory.Arithmetic.anchoredPowerPrefixLower σ a b riemannSmoothedLowerProfile +
        (∑ m ∈ Finset.Ioc 0 ⌊a⌋₊, c * Real.log m * ArithmeticFunction.vonMangoldt m / (m : ℝ) ^ τ) ≤
      ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, AnalyticNumberTheory.Arithmetic.pairedEulerPrefixWeight σ τ c m := by
  apply
    AnalyticNumberTheory.Arithmetic.anchoredPowerPrefixLower_add_logPrefix_le hσ hc
      (zero_lt_one.trans ha) hab _ (continuousOn_riemannSmoothedLowerProfile (zero_lt_one.trans ha))
  intro t ht
  exact logWeightedMangoldtSum_ge_rational_refined hRH (ha.trans_le ht.1)

/-- The anchored paired Euler lower expression at fixed exponents 5/4 and 11/4
and logarithmic coefficient 3/4. It packages the generic analytic lower bound for
the two-pole witness comparisons without fixing the anchor. -/
noncomputable def anchoredTwoPolePrefixLower (a b : ℝ) : ℝ :=
  AnalyticNumberTheory.Arithmetic.anchoredPowerPrefixLower (5 / 4) a b riemannSmoothedLowerProfile +
    ∑ m ∈ Finset.Ioc 0 ⌊a⌋₊,
      (3 / 4 : ℝ) * Real.log m * ArithmeticFunction.vonMangoldt m / (m : ℝ) ^ (11 / 4 : ℝ)

/-- Under RH and ordered cutoffs with anchor above one, the two-pole anchored
expression bounds the actual paired prefix mass below. Specialize the generic
Euler comparison. This supplies the prefix saving in the nonprincipal contradiction. -/
theorem anchoredTwoPolePrefixLower_le (hRH : RiemannHypothesis) {a b : ℝ} (ha : 1 < a)
    (hab : a ≤ b) :
    anchoredTwoPolePrefixLower a b ≤ twoPoleEulerPrefixMass (Finset.Ioc 0 ⌊b⌋₊) := by
  exact anchoredEulerPrefix_lower_of_rh hRH (by norm_num only) (by norm_num only) ha hab

/-- For nonprincipal GRH data and a positive separated gap using the anchored prefix,
triviality at all primes through the ramp cutoff is impossible. Bound the actual
finite Euler prefix analytically and invoke the split-remainder witness criterion.
This connects the small-anchor analytic tail to the prime-witness consumer. -/
theorem prime_trivial_false_of_anchoredEulerPrefix {q A : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) (hqA : q ≤ A) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x C a b : ℝ} (hx : 2 ≤ x) (ha : 1 < a) (hab : a ≤ b) (hb : b ≤ (99 / 40 : ℝ) * x)
    (hC : AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant χ.primitiveCharacter ≤ C)
    (hgap : 0 < reflectedSplitGap A C x + 2 * anchoredTwoPolePrefixLower a b) :
    ¬(∀ p : ℕ, p.Prime → (p : ℝ) ≤ (99 / 40 : ℝ) * x → χ p = 1) := by
  have hg :=
    mul_le_mul_of_nonneg_left (anchoredTwoPolePrefixLower_le hGRH.riemann ha hab)
      (by norm_num only : (0 : ℝ) ≤ 2)
  have hS : ∀ n ∈ Finset.Ioc 0 ⌊b⌋₊, (n : ℝ) ≤ (99 / 40 : ℝ) * x := by
    intro n hn
    exact
      ((Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2).trans
            (Nat.floor_le ((zero_lt_one.trans ha).trans_le hab).le)).trans
        hb
  have he :
    reflectedSplitGap A (C - 2 * anchoredTwoPolePrefixLower a b) x =
      reflectedSplitGap A C x + 2 * anchoredTwoPolePrefixLower a b := by
    dsimp only [reflectedSplitGap, reflectedSplitUpper]
    ring
  exact
    prime_trivial_false_of_reflectedSplit_prefix χ hne hqA hGRH hx hC (Finset.Ioc 0 ⌊b⌋₊) hS hg
      (he.symm ▸ hgap)

/-- Under the anchored-prefix hypotheses and any positive stencil width at most x,
positivity of the variable-width principal gap yields a nontrivial prime.
Keep the full finite Euler prefix, insert the anchored lower bound and apply the
actual variable-width principal comparison. This is the consumer used by the
small-scale numerical candidate without enumerating the full Euler support. -/
theorem prime_trivial_false_of_anchoredEulerPrefix_variable_width {q A : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (hqA : q ≤ A)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x C a b h : ℝ} (hx : 2 ≤ x)
    (hh : 0 < h) (hhx : h ≤ x) (ha : 1 < a) (hab : a ≤ b) (hb : b ≤ (99 / 40 : ℝ) * x)
    (hC : AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant χ.primitiveCharacter ≤ C)
    (hgap :
      0 <
        variableRampPrincipalLower x h - reflectedSplitUpper A C x +
          2 * anchoredTwoPolePrefixLower a b) :
    ¬(∀ p : ℕ, p.Prime → (p : ℝ) ≤ (99 / 40 : ℝ) * x → χ p = 1) := by
  intro ht
  let S := Finset.Ioc 0 ⌊b⌋₊
  have hg :=
    mul_le_mul_of_nonneg_left (anchoredTwoPolePrefixLower_le hGRH.riemann ha hab)
      (by norm_num only : (0 : ℝ) ≤ 2)
  have hS : ∀ n ∈ S, (n : ℝ) ≤ (99 / 40 : ℝ) * x := by
    intro n hn
    exact
      ((Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2).trans
            (Nat.floor_le ((zero_lt_one.trans ha).trans_le hab).le)).trans
        hb
  have ht' : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ (99 / 40 : ℝ) * x → χ.primitiveCharacter p = 1 :=
    fun p hp hb ↦ PaperStatements.primitiveCharacter_apply_one_of_apply_one χ (ht p hp hb)
  have he :=
    AnalyticNumberTheory.Arithmetic.pairedEulerPrefix_eq_twice_of_coprime_support
      χ.primitiveCharacter S hS (fun n _ ↦ Nat.coprime_one_right n) (fun p hp hb _ ↦ ht' p hp hb)
  have hd :
    2 * anchoredTwoPolePrefixLower a b ≤
      ∑ n ∈ S,
        (1 + (χ.primitiveCharacter n).re) *
          AnalyticNumberTheory.Arithmetic.pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4) n := by
    rw [he]
    exact hg
  have hu := gamma_primitive_re_le_reflectedSplit_of_prefix χ hne hqA hGRH hx hC S hd
  have hx0 : 0 < x := by linarith only [hx]
  have hl :=
    gammaLocalCorrection_nonpos_of_level_primes_above χ hx0
      (fun p hp ↦ (level_prime_above_cutoff_of_all_prime_trivial χ ht hp).le)
  have hJ :=
    variableRampPrincipalLower_le_actual hGRH.riemann (by linarith only [hx] : 1 ≤ x) hh hhx
  have hN := gamma_ramp_no_witness_comparison_general χ hx0 (fun p hp _ hb0 ↦ ht p hp hb0)
  linarith only [hu, hl, hJ, hN, hgap]

end PseudoPrime.LLS
