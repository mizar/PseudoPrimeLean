/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPrincipalLogMoments
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianCenteredVariationRat
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianCenteredTailBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMidpointBound
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPrincipalHeadCert
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianCenteredTail
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianLaplaceMoment
import Mathlib.Tactic.Ring

/-! # Assembly of the centered principal zero series -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The two-sided low ledger uses the checked centered error on each positive bracket. -/
public theorem high_centered_head_le (K : HighGaussianKernel) (hRH : RiemannHypothesis) :
    (∑ ρ ∈ AnalyticNumberTheory.RiemannZeta.zerosUpTo 100,
        (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
          ‖highPrincipalMultiplier K ρ.im‖) ≤
      2 *
        ((∑ i, ‖highPrincipalMultiplier K (highZeroBracketMid i : ℝ)‖) +
          (highCenteredErrorTicks K : ℝ) / 1000000) := by
  exact
    high_zero_head_of_positive K hRH
      (high_positive_head_of_brackets K hRH (high_centered_low_budget_le K))

/-- The principal series bound uses checked bracket errors and checked inverse-square tail caps. -/
public theorem high_centered_principal_le (K : HighGaussianKernel) (hRH : RiemannHypothesis) {X : ℝ}
    (hX : 0 < X) :
    let d := (K.pole : ℝ) - 1 / 2
    let W := fun u : ℝ ↦ u ^ d * K.realProfile.eval (5 - Real.log u)
    let F := fun u : ℝ ↦ u * deriv W u
    |Real.exp (-(5 * (K.pole : ℝ))) *
          (principalErrorFunctional (deriv F) gaussianLogZetaZeroSum (F 1) X (Real.exp 5) /
            Real.sqrt X)| ≤
      2 *
          ((∑ i, ‖highPrincipalMultiplier K (highZeroBracketMid i : ℝ)‖) +
            (highCenteredErrorTicks K : ℝ) / 1000000) +
        ((highCenteredTailTicks K : ℝ) / 1000) * (13 / 1000) := by
  exact
    high_principal_series_of_head K hRH
      (div_nonneg (Nat.cast_nonneg (highCenteredTailTicks K)) (by norm_num only))
      (high_centered_head_le K hRH) (fun _ ht ↦ high_centered_tail_ticks_le K ht) hX

/-- Bound the principal zero series using the rational midpoint sum and certified errors. -/
public theorem high_principal_le_midpoint_sum (K : HighGaussianKernel) (hRH : RiemannHypothesis)
    {X : ℝ} (hX : 0 < X) :
    let d := (K.pole : ℝ) - 1 / 2
    let W := fun u : ℝ ↦ u ^ d * K.realProfile.eval (5 - Real.log u)
    let F := fun u : ℝ ↦ u * deriv W u
    |Real.exp (-(5 * (K.pole : ℝ))) *
          (principalErrorFunctional (deriv F) gaussianLogZetaZeroSum (F 1) X (Real.exp 5) /
            Real.sqrt X)| ≤
      2 * ((highMidpointNormSum K : ℝ) + (highCenteredErrorTicks K : ℝ) / 1000000) +
        ((highCenteredTailTicks K : ℝ) / 1000) * (13 / 1000) := by
  exact
    (high_centered_principal_le K hRH hX).trans
      (add_le_add_left
        (mul_le_mul_of_nonneg_left (add_le_add_left (high_midpoint_sum_le K) _) zero_le_two) _)

/-- Both kernels satisfy a common cap below the manuscript's two spectral budgets. -/
public theorem high_principal_le_spectral_cap (K : HighGaussianKernel) (hRH : RiemannHypothesis)
    {X : ℝ} (hX : 0 < X) :
    let d := (K.pole : ℝ) - 1 / 2
    let W := fun u : ℝ ↦ u ^ d * K.realProfile.eval (5 - Real.log u)
    let F := fun u : ℝ ↦ u * deriv W u
    |Real.exp (-(5 * (K.pole : ℝ))) *
          (principalErrorFunctional (deriv F) gaussianLogZetaZeroSum (F 1) X (Real.exp 5) /
            Real.sqrt X)| ≤
      97 / 4000 := by
  have h : (highMidpointNormSum K : ℝ) ≤ 856 / 100000 := by
    have hc := Rat.cast_le (K := ℝ).mpr (high_midpoint_norm_sum_bound K)
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hc
  refine (high_principal_le_midpoint_sum K hRH hX).trans ?_
  refine (add_le_add_left (mul_le_mul_of_nonneg_left (add_le_add_left h _) zero_le_two) _).trans ?_
  cases K <;> norm_num only [highCenteredErrorTicks, highCenteredTailTicks, Nat.cast_ofNat]

/-- A common midpoint budget yields the manuscript's principal zero-series bound. -/
public theorem high_principal_le_one_fortieth (K : HighGaussianKernel) (hRH : RiemannHypothesis)
    {X : ℝ} (hX : 0 < X) :
    let d := (K.pole : ℝ) - 1 / 2
    let W := fun u : ℝ ↦ u ^ d * K.realProfile.eval (5 - Real.log u)
    let F := fun u : ℝ ↦ u * deriv W u
    |Real.exp (-(5 * (K.pole : ℝ))) *
          (principalErrorFunctional (deriv F) gaussianLogZetaZeroSum (F 1) X (Real.exp 5) /
            Real.sqrt X)| ≤
      1 / 40 := by
  exact (high_principal_le_spectral_cap K hRH hX).trans (by norm_num only)

/-- Combine the spectral budget with a bound for the normalized remainder. -/
public theorem high_principal_error_le (K : HighGaussianKernel) (hRH : RiemannHypothesis) {X : ℝ}
    (hX : 0 < X) (R : ℝ) :
    let d := (K.pole : ℝ) - 1 / 2
    let W := fun u : ℝ ↦ u ^ d * K.realProfile.eval (5 - Real.log u)
    let F := fun u : ℝ ↦ u * deriv W u
    let E := principalErrorFunctional (deriv F) gaussianLogZetaError (F 1) X (Real.exp 5)
    let Z := principalErrorFunctional (deriv F) gaussianLogZetaZeroSum (F 1) X (Real.exp 5)
    let c := Real.exp (-(5 * (K.pole : ℝ)))
    c * (|E - Z| / Real.sqrt X) ≤ R → |c * (E / Real.sqrt X)| ≤ 97 / 4000 + R := by
  intro d W F E Z c hR
  have h := high_principal_le_spectral_cap K hRH hX
  change |c * (Z / Real.sqrt X)| ≤ _ at h
  rw [show E / Real.sqrt X = Z / Real.sqrt X + (E - Z) / Real.sqrt X by ring, mul_add]
  have hc : 0 ≤ c := Real.exp_nonneg _
  exact
    (abs_add_le _ _).trans
      (add_le_add h
        (by
          simpa only [abs_mul, abs_div, abs_of_nonneg hc, abs_of_nonneg (Real.sqrt_nonneg X)] using
            hR))

/-- The rational second-derivative polynomial used in both absolute moments of H27. -/
@[expose]
public noncomputable def highRemainderRatPoly (K : HighGaussianKernel) : Polynomial ℚ :=
  let d := K.pole - 1 / 2
  let B := highRatProfile K
  Polynomial.C (d ^ 2) * B - Polynomial.C (2 * d) * B.derivative + B.derivative.derivative

/-- Casting the rational polynomial gives the derivative polynomial in the remainder bound. -/
public theorem high_remainder_rat_poly_map (K : HighGaussianKernel) :
    let d := (K.pole : ℝ) - 1 / 2
    let B := K.realProfile
    (highRemainderRatPoly K).map (Rat.castHom ℝ) =
      Polynomial.C (d ^ 2) * B - Polynomial.C (2 * d) * B.derivative + B.derivative.derivative := by
  simp only [highRemainderRatPoly, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_C, ← Polynomial.derivative_map, high_rat_profile_map, Rat.coe_castHom,
    Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_pow]

/-- The H27 derivative polynomial fits the same degree bound as the kernel profile. -/
public theorem high_remainder_rat_degree (K : HighGaussianKernel) :
    (highRemainderRatPoly K).natDegree ≤ 2 * K.degree + 3 := by
  have h := high_rat_profile_degree K
  have hd (p : Polynomial ℚ) : p.derivative.natDegree ≤ p.natDegree :=
    (Polynomial.natDegree_derivative_le p).trans (Nat.sub_le _ _)
  have h₁ := (hd (highRatProfile K)).trans h
  have h₂ := (hd (highRatProfile K).derivative).trans h₁
  let d := K.pole - 1 / 2
  let B := highRatProfile K
  change
    (Polynomial.C (d ^ 2) * B - Polynomial.C (2 * d) * B.derivative +
          B.derivative.derivative).natDegree ≤
      _
  simpa only [max_self] using
    Polynomial.natDegree_add_le_of_le
      (Polynomial.natDegree_sub_le_of_le ((Polynomial.natDegree_C_mul_le (d ^ 2) B).trans h)
        ((Polynomial.natDegree_C_mul_le (2 * d) B.derivative).trans h₁))
      h₂

/-- Estimate a finite H27 integral by the existing rational Bernstein partition bound. -/
public theorem high_remainder_integral_bernstein (K : HighGaussianKernel) (N : ℕ) {s : ℝ}
    (hs : 0 ≤ s) (p e : ℕ → ℚ) (hp : ∀ j < N, p j < p (j + 1))
    (he : ∀ j < N, Real.exp (-s * (p j : ℝ)) ≤ (e j : ℝ)) :
    let P := highRemainderRatPoly K
    let n := 2 * K.degree + 3
    (∫ x in (p 0 : ℝ)..(p N : ℝ), Real.exp (-s * x) * |(P.map (Rat.castHom ℝ)).eval x|) ≤
      ((∑ j ∈ Finset.range N,
          e j *
            ((p (j + 1) - p j) *
              ((∑ k : Fin (n + 1),
                  |Analysis.bernsteinRatCoeff
                      (P.comp (Polynomial.C (p (j + 1) - p j) * Polynomial.X + Polynomial.C (p j)))
                      n k|) /
                ((n : ℚ) + 1)))) :
        ℚ) := by
  simp only [Polynomial.eval_map]
  exact Analysis.weighted_abs_rat_bernstein _ N _ (high_remainder_rat_degree K) hs p e hp he

/-- The manuscript's H27 moments give the remainder charge in the full principal bound. -/
public theorem high_principal_error_le_moments (K : HighGaussianKernel) (hRH : RiemannHypothesis)
    {X : ℝ} (hX : 1 ≤ X) :
    let d := (K.pole : ℝ) - 1 / 2
    let B := K.realProfile
    let D := (highRemainderRatPoly K).map (Rat.castHom ℝ)
    let W := fun u : ℝ ↦ u ^ d * B.eval (5 - Real.log u)
    let F := fun u : ℝ ↦ u * deriv W u
    let z := Real.log X
    let c := Real.exp (-(5 * (K.pole : ℝ)))
    |c *
          (principalErrorFunctional (deriv F) gaussianLogZetaError (F 1) X (Real.exp 5) /
            Real.sqrt X)| ≤
      97 / 4000 +
        c *
          (51 / 10 * Real.exp (-(d + 1 / 2) * z) *
              (∫ t in Set.Ioi (0 : ℝ), Real.exp (-d * t) * |D.eval (5 + z + t)|) +
            5 / 4 * Real.exp (-(5 / 2 : ℝ) * z) * Real.exp ((d - 2) * 5) *
              (∫ t in (0 : ℝ)..(5 + z), Real.exp (-(d - 2) * t) * |D.eval t|) +
            5 / 3 * |F 1| * Real.exp (-(5 / 2 : ℝ) * z)) := by
  intro d B D W F z c
  dsimp only [D]
  rw [high_remainder_rat_poly_map]
  exact
    high_principal_error_le K hRH (zero_lt_one.trans_le hX) _
      (mul_le_mul_of_nonneg_left (high_principal_rem_normalized K hRH hX) (Real.exp_nonneg _))

/-- The lower H27 contribution is bounded by the lower endpoint of a log interval. -/
private theorem h27_low_endpoint (P : Polynomial ℝ) {d l z : ℝ} (hd : 0 < d) (hl : 0 ≤ l)
    (hlz : l ≤ z) :
    Real.exp (-(d + 1 / 2) * z) *
        (∫ t in Set.Ioi (0 : ℝ), Real.exp (-d * t) * |P.eval (5 + z + t)|) ≤
      Real.exp (5 * d - l / 2) * (∫ t in Set.Ioi (5 + l), Real.exp (-d * t) * |P.eval t|) := by
  rw [normalized_abs_laplace_tail]
  exact
    mul_le_mul
      (Real.exp_le_exp.mpr (sub_le_sub_left (div_le_div_of_nonneg_right hlz (by norm_num only)) _))
      (abs_laplace_tail_mono P hd (add_nonneg (by norm_num only) hl) (add_le_add_right hlz 5))
      (MeasureTheory.setIntegral_nonneg measurableSet_Ioi
        (fun _ _ ↦ mul_nonneg (Real.exp_nonneg _) (abs_nonneg _)))
      (Real.exp_nonneg _)

/-- Bound the finite H27 integral at the upper endpoint and its weight at the lower one. -/
private theorem h27_finite_endpoint (P : Polynomial ℝ) {s l z u : ℝ} (hs : 0 < s) (hl : 0 ≤ l)
    (hlz : l ≤ z) (hzu : z ≤ u) :
    Real.exp (-(5 / 2 : ℝ) * z) * (∫ t in (0 : ℝ)..(5 + z), Real.exp (-s * t) * |P.eval t|) ≤
      Real.exp (-(5 / 2 : ℝ) * l) * (∫ t in (0 : ℝ)..(5 + u), Real.exp (-s * t) * |P.eval t|) := by
  have hz : 0 ≤ 5 + z := add_nonneg (by norm_num only) (hl.trans hlz)
  exact
    mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hlz (by norm_num only)))
      (abs_laplace_interval_mono P hs hz (add_le_add_right hzu 5))
      (intervalIntegral.integral_nonneg hz
        (fun _ _ ↦ mul_nonneg (Real.exp_nonneg _) (abs_nonneg _)))
      (Real.exp_nonneg _)

/-- Evaluate the H27 boundary derivative on the rational profile at the shift five. -/
public noncomputable def highPrincipalBoundaryRat (K : HighGaussianKernel) : ℚ :=
  (highCenteredRatPoly K).eval 5

/-- The boundary contribution in the normalized principal error has this rational value. -/
private theorem high_principal_boundary_eq (K : HighGaussianKernel) :
    let d := (K.pole : ℝ) - 1 / 2
    let W := fun v : ℝ ↦ v ^ d * K.realProfile.eval (5 - Real.log v)
    1 * deriv W 1 = (highPrincipalBoundaryRat K : ℝ) := by
  intro d W
  rw [(reflected_log_weight_deriv K.realProfile d 5 zero_lt_one).deriv, Real.log_one, sub_zero,
    Real.one_rpow, one_mul, one_mul]
  change (highCenteredProfile K).eval 5 = _
  rw [← high_centered_rat_map]
  simpa only [Rat.coe_castHom, Rat.cast_ofNat, highPrincipalBoundaryRat] using
    (Polynomial.eval_map_apply (p := highCenteredRatPoly K) (Rat.castHom ℝ) (5 : ℚ))

/-- Bound the H27 remainder uniformly over a nonnegative interval of logarithmic cutoffs. -/
public theorem high_principal_error_on_log_interval (K : HighGaussianKernel)
    (hRH : RiemannHypothesis) {X l u : ℝ} (hX : 1 ≤ X) (hl : 0 ≤ l)
    (hlog : Real.log X ∈ Set.Icc l u) :
    let d := (K.pole : ℝ) - 1 / 2
    let D := (highRemainderRatPoly K).map (Rat.castHom ℝ)
    let W := fun v : ℝ ↦ v ^ d * K.realProfile.eval (5 - Real.log v)
    let F := fun v : ℝ ↦ v * deriv W v
    let c := Real.exp (-(5 * (K.pole : ℝ)))
    |c *
          (principalErrorFunctional (deriv F) gaussianLogZetaError (F 1) X (Real.exp 5) /
            Real.sqrt X)| ≤
      97 / 4000 +
        c *
          (51 / 10 *
              (Real.exp (5 * d - l / 2) *
                (∫ t in Set.Ioi (5 + l), Real.exp (-d * t) * |D.eval t|)) +
            (5 / 4 * Real.exp ((d - 2) * 5)) *
              (Real.exp (-(5 / 2 : ℝ) * l) *
                (∫ t in (0 : ℝ)..(5 + u), Real.exp (-(d - 2) * t) * |D.eval t|)) +
            5 / 3 * |(highPrincipalBoundaryRat K : ℝ)| * Real.exp (-(5 / 2 : ℝ) * l)) := by
  intro d D W F c
  have hd₂ : 0 < d - 2 := by
    cases K <;> norm_num only [d, HighGaussianKernel.pole, Rat.cast_div, Rat.cast_ofNat]
  have hd : 0 < d := (by norm_num only : (0 : ℝ) < 2).trans (sub_pos.mp hd₂)
  let z := Real.log X
  let e := Real.exp ((d - 2) * 5)
  let f := Real.exp (-(5 / 2 : ℝ) * z)
  let A := ∫ t in Set.Ioi (0 : ℝ), Real.exp (-d * t) * |D.eval (5 + z + t)|
  let B := ∫ t in (0 : ℝ)..(5 + z), Real.exp (-(d - 2) * t) * |D.eval t|
  have low :=
    mul_le_mul_of_nonneg_left (h27_low_endpoint D hd hl hlog.1)
      (by norm_num only : (0 : ℝ) ≤ 51 / 10)
  have high :=
    mul_le_mul_of_nonneg_left (h27_finite_endpoint D hd₂ hl hlog.1 hlog.2)
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 5 / 4) (Real.exp_nonneg ((d - 2) * 5)))
  have boundary :=
    mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hlog.1 (by norm_num only : -(5 / 2 : ℝ) ≤ 0)))
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 5 / 3) (abs_nonneg (F 1)))
  refine (high_principal_error_le_moments K hRH hX).trans ?_
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
  change (51 / 10 * Real.exp (-(d + 1 / 2) * z) * A + 5 / 4 * f * e * B) + 5 / 3 * |F 1| * f ≤ _
  rw [mul_assoc (51 / 10 : ℝ), mul_right_comm (5 / 4 : ℝ) f e, mul_assoc ((5 / 4 : ℝ) * e) f B]
  have hF : F 1 = (highPrincipalBoundaryRat K : ℝ) := high_principal_boundary_eq K
  rw [← hF]
  exact add_le_add (add_le_add low high) boundary

/-- Extend a certified finite H27 integral by a polynomial bound on the remaining tail. -/
public theorem high_remainder_tail_le (K : HighGaussianKernel) {s a b M : ℝ} (hs : 0 < s)
    (ha : 0 ≤ a) (hab : a ≤ b) :
    let D := (highRemainderRatPoly K).map (Rat.castHom ℝ)
    let Q := D.comp (Polynomial.X + Polynomial.C b)
    (∫ t in a..b, Real.exp (-s * t) * |D.eval t|) ≤ M →
      (∫ t in Set.Ioi a, Real.exp (-s * t) * |D.eval t|) ≤
        M +
          Real.exp (-s * b) *
            ∑ k ∈ Finset.range (Q.natDegree + 1),
              |Q.coeff k| * ((k.factorial : ℝ) / s ^ (k + 1)) := by
  intro D Q hM
  rw [abs_laplace_tail_split D hs ha hab]
  exact add_le_add hM (abs_laplace_tail_le_coeffs D hs b)

end PseudoPrime.PrimeTestBounds.MillerRabin
