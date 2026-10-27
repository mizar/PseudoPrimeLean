/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.AnchoredEulerPrefixLowerBounds

/-! # Closed analytic Euler tails with a finite anchor -/

@[expose] public section

namespace PseudoPrime.LLS

/-- An explicit primitive of the RH smoothed lower profile times the 5/4 power kernel.
It uses only rational powers and log t on positive t. Its endpoint difference removes
the analytic integral from the anchored finite Euler lower bound. -/
noncomputable def anchoredEulerTailPrimitive (t : ℝ) : ℝ :=
  (-25 / 4 : ℝ) * t ^ (-1 / 4 : ℝ) + (5 / 48 : ℝ) * t ^ (-3 / 4 : ℝ) +
    ((1839 / 800 : ℝ) * Real.log t + 6303 / 2000) * t ^ (-5 / 4 : ℝ)

/-- At any positive t, the explicit primitive has derivative equal to the actual
RH lower-profile integrand. Apply power and logarithm differentiation and align
the real powers using positivity. This justifies the subsequent exact integral. -/
theorem anchoredEulerTailPrimitive_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt anchoredEulerTailPrimitive
      (riemannSmoothedLowerProfile t * ((5 / 4 : ℝ) ^ 2 * t ^ (-(5 / 4 : ℝ) - 1))) t := by
  have h1 := (Real.hasDerivAt_rpow_const (p := -1 / 4) (Or.inl ht.ne')).const_mul (-25 / 4)
  have h2 := (Real.hasDerivAt_rpow_const (p := -3 / 4) (Or.inl ht.ne')).const_mul (5 / 48)
  have h3 := Real.hasDerivAt_rpow_const (p := -5 / 4) (Or.inl ht.ne')
  have hl := ((Real.hasDerivAt_log ht.ne').const_mul (1839 / 800)).add_const (6303 / 2000)
  have h := (h1.add h2).add (hl.mul h3)
  have hp1 : t ^ ((-1 / 4 : ℝ) - 1) = t * t ^ (-9 / 4 : ℝ) := by
    calc
      _ = t ^ (1 + (-9 / 4 : ℝ)) := by
        congr 1; norm_num only
      _ = t ^ (1 : ℝ) * t ^ (-9 / 4 : ℝ) := Real.rpow_add ht _ _
      _ = _ := by rw [Real.rpow_one]
  have hp2 : t ^ ((-3 / 4 : ℝ) - 1) = Real.sqrt t * t ^ (-9 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add ht]
    congr 1
    norm_num only
  have hp3 : t ^ (-5 / 4 : ℝ) = t * t ^ (-9 / 4 : ℝ) := by
    calc
      _ = t ^ (1 + (-9 / 4 : ℝ)) := by
        congr 1; norm_num only
      _ = t ^ (1 : ℝ) * t ^ (-9 / 4 : ℝ) := Real.rpow_add ht _ _
      _ = _ := by rw [Real.rpow_one]
  simp only [Pi.add_def, Pi.mul_def] at h
  unfold anchoredEulerTailPrimitive
  apply h.congr_deriv
  rw [hp1, hp2, hp3]
  dsimp only [riemannSmoothedLowerProfile]
  norm_num only
  field_simp [ht.ne']
  ring

/-- For positive ordered endpoints, the RH profile integral in the anchored bound
is the difference of the two explicit primitive values. Use the verified derivative
and continuity of the integrand. This leaves only finite sums and elementary endpoints. -/
theorem integral_riemannSmoothedLowerProfile_power {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, riemannSmoothedLowerProfile t * ((5 / 4 : ℝ) ^ 2 * t ^ (-(5 / 4 : ℝ) - 1))) =
      anchoredEulerTailPrimitive b - anchoredEulerTailPrimitive a := by
  have hw : ContinuousOn (fun t : ℝ ↦ (5 / 4 : ℝ) ^ 2 * t ^ (-(5 / 4 : ℝ) - 1)) (Set.Icc a b) :=
    continuousOn_const.mul (continuousOn_id.rpow_const (fun t ht ↦ Or.inl (ha.trans_le ht.1).ne'))
  have hi := (continuousOn_riemannSmoothedLowerProfile ha).mul hw
  rw [← Set.uIcc_of_le hab] at hi
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hi.intervalIntegrable
  intro t ht
  rw [Set.uIcc_of_le hab] at ht
  exact anchoredEulerTailPrimitive_hasDerivAt (ha.trans_le ht.1)

/-- The anchored paired Euler lower expression with the analytic integral evaluated.
Inputs are a finite anchor a and upper cutoff b. The finite Mangoldt prefix and lower
boundary remain exact. This is suitable for rational endpoint certification. -/
noncomputable def closedAnchoredEulerPrefix (a b : ℝ) : ℝ :=
  (∑ m ∈ Finset.Ioc 0 ⌊a⌋₊, ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-5 / 4 : ℝ)) +
        anchoredEulerTailPrimitive b -
      anchoredEulerTailPrimitive a -
      a ^ (-5 / 4 : ℝ) *
        (Chebyshev.psi a + (5 / 4 : ℝ) * AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum a) +
    b ^ (-5 / 4 : ℝ) * ((5 / 4 : ℝ) * riemannSmoothedLowerProfile b) +
    ∑ m ∈ Finset.Ioc 0 ⌊a⌋₊,
      (3 / 4 : ℝ) * Real.log m * ArithmeticFunction.vonMangoldt m / (m : ℝ) ^ (11 / 4 : ℝ)

/-- For positive ordered endpoints, the closed expression equals the original
anchored analytic lower bound. Substitute the exact integral formula and normalize
the rational exponents. This transfers all existing witness consumers. -/
theorem closedAnchoredEulerPrefix_eq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    closedAnchoredEulerPrefix a b = anchoredTwoPolePrefixLower a b := by
  dsimp only [closedAnchoredEulerPrefix, anchoredTwoPolePrefixLower,
    AnalyticNumberTheory.Arithmetic.anchoredPowerPrefixLower]
  rw [integral_riemannSmoothedLowerProfile_power ha hab]
  norm_num only
  ring

/-- Under RH and an anchor above one, the closed expression bounds the actual finite
paired Euler mass below. Rewrite it as the proved anchored bound. This provides a
lower bound with no unevaluated analytic integral. -/
theorem closedAnchoredEulerPrefix_le (hRH : RiemannHypothesis) {a b : ℝ} (ha : 1 < a)
    (hab : a ≤ b) : closedAnchoredEulerPrefix a b ≤ twoPoleEulerPrefixMass (Finset.Ioc 0 ⌊b⌋₊) := by
  rw [closedAnchoredEulerPrefix_eq (zero_lt_one.trans ha) hab]
  exact anchoredTwoPolePrefixLower_le hRH ha hab

/-- Under nonprincipal GRH data, a positive variable-width witness gap using the
closed Euler prefix excludes prime triviality through the cutoff. Rewrite the closed
bound and invoke the existing anchored witness theorem. This connects exact integral
evaluation to the prime-witness consumer. -/
theorem prime_trivial_false_of_closedAnchoredEulerPrefix {q A : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (hqA : q ≤ A)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x C a b h : ℝ} (hx : 2 ≤ x)
    (hh : 0 < h) (hhx : h ≤ x) (ha : 1 < a) (hab : a ≤ b) (hb : b ≤ (99 / 40 : ℝ) * x)
    (hC : AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant χ.primitiveCharacter ≤ C)
    (hgap :
      0 <
        variableRampPrincipalLower x h - reflectedSplitUpper A C x +
          2 * closedAnchoredEulerPrefix a b) :
    ¬(∀ p : ℕ, p.Prime → (p : ℝ) ≤ (99 / 40 : ℝ) * x → χ p = 1) := by
  rw [closedAnchoredEulerPrefix_eq (zero_lt_one.trans ha) hab] at hgap
  exact
    prime_trivial_false_of_anchoredEulerPrefix_variable_width χ hne hqA hGRH hx hh hhx ha hab hb hC
      hgap

/-- At a positive upper endpoint, the primitive plus the smoothed boundary simplifies
to three rational powers, with complete cancellation of log b. Align product powers
and expand the polynomial coefficients. This exposes the uniform tail shape. -/
theorem anchoredTailEndpoint_eq {b : ℝ} (hb : 0 < b) :
    anchoredEulerTailPrimitive b +
        b ^ (-5 / 4 : ℝ) * ((5 / 4 : ℝ) * riemannSmoothedLowerProfile b) =
      -5 * b ^ (-1 / 4 : ℝ) + (1 / 24 : ℝ) * b ^ (-3 / 4 : ℝ) +
        (1839 / 1000 : ℝ) * b ^ (-5 / 4 : ℝ) := by
  have h1 : b * b ^ (-5 / 4 : ℝ) = b ^ (-1 / 4 : ℝ) := by
    calc
      _ = b ^ (1 : ℝ) * b ^ (-5 / 4 : ℝ) := by rw [Real.rpow_one]
      _ = b ^ ((1 : ℝ) + -5 / 4) := (Real.rpow_add hb _ _).symm
      _ = _ := by
        congr 1; norm_num only
  have h2 : Real.sqrt b * b ^ (-5 / 4 : ℝ) = b ^ (-3 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hb]
    congr 1
    norm_num only
  dsimp only [anchoredEulerTailPrimitive, riemannSmoothedLowerProfile]
  nlinarith only [h1, h2]

/-- The finite-anchor constant containing the retained power and logarithmic prefixes,
primitive value, and Chebyshev-smoothed boundary. It depends only on the anchor a.
This separates the finite certification from the upper-cutoff dependence. -/
noncomputable def anchoredEulerConstant (a : ℝ) : ℝ :=
  (∑ m ∈ Finset.Ioc 0 ⌊a⌋₊, ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-5 / 4 : ℝ)) -
      anchoredEulerTailPrimitive a -
      a ^ (-5 / 4 : ℝ) *
        (Chebyshev.psi a + (5 / 4 : ℝ) * AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum a) +
    ∑ m ∈ Finset.Ioc 0 ⌊a⌋₊,
      (3 / 4 : ℝ) * Real.log m * ArithmeticFunction.vonMangoldt m / (m : ℝ) ^ (11 / 4 : ℝ)

/-- For a positive upper cutoff, the closed Euler lower bound equals its anchor
constant minus 5b^(-1/4), plus two nonnegative rational-power corrections.
Use the endpoint cancellation identity. This makes the remaining scale dependence explicit. -/
theorem closedAnchoredEulerPrefix_eq_constant {a b : ℝ} (hb : 0 < b) :
    closedAnchoredEulerPrefix a b =
      anchoredEulerConstant a - 5 * b ^ (-1 / 4 : ℝ) + (1 / 24 : ℝ) * b ^ (-3 / 4 : ℝ) +
        (1839 / 1000 : ℝ) * b ^ (-5 / 4 : ℝ) := by
  have he := anchoredTailEndpoint_eq hb
  dsimp only [closedAnchoredEulerPrefix, anchoredEulerConstant]
  linarith only [he]

/-- Under RH, with anchor above one and ordered cutoffs, the finite paired Euler
mass is at least K(a)-5b^(-1/4). Drop the two proved nonnegative correction terms
from the exact closed lower bound. This gives a simple monotone analytic tail. -/
theorem anchoredEulerConstant_sub_le_prefix (hRH : RiemannHypothesis) {a b : ℝ} (ha : 1 < a)
    (hab : a ≤ b) :
    anchoredEulerConstant a - 5 * b ^ (-1 / 4 : ℝ) ≤
      twoPoleEulerPrefixMass (Finset.Ioc 0 ⌊b⌋₊) := by
  have hb := (zero_lt_one.trans ha).trans_le hab
  have he := closedAnchoredEulerPrefix_le hRH ha hab
  rw [closedAnchoredEulerPrefix_eq_constant hb] at he
  have h1 := Real.rpow_nonneg hb.le (-3 / 4 : ℝ)
  have h2 := Real.rpow_nonneg hb.le (-5 / 4 : ℝ)
  linarith only [he, h1, h2]

end PseudoPrime.LLS
