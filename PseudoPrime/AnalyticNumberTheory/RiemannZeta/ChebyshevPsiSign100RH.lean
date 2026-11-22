/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiPiecewiseRH
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiIntegrated194RH
public import PseudoPrime.AnalyticNumberTheory.RiemannXi.CriticalLineZeros
public import PseudoPrime.AnalyticNumberTheory.RiemannXi.CriticalNormalizedSign
public import PseudoPrime.AnalyticNumberTheory.RiemannXi.CriticalLineMellin
public import PseudoPrime.AnalyticNumberTheory.RiemannXi.ThetaGaussianBounds
public import PseudoPrime.AnalyticNumberTheory.RiemannXi.CriticalMellinSplit
public import PseudoPrime.AnalyticNumberTheory.RiemannXi.CriticalMellinNumerics
public import PseudoPrime.AnalyticNumberTheory.RiemannXi.CriticalMellinQuadrature
import all PseudoPrime.AnalyticNumberTheory.RiemannXi.CriticalMellinPhase
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100Bounds
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCount100RH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCount100PhaseRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaFiniteDerivative128
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaFiniteGridApprox
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointInterface
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node01Lower
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node01Upper
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node02Lower
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node02Upper
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node03Lower
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node03Upper
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node04Lower
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node04Upper
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node05Lower
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node05Upper
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node06Lower
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node06Upper
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node07Lower
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node07Upper
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node08Lower
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node08Upper
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node09Lower
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node09Upper
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node10Lower
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node10Upper
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node11Lower
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node11Upper
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node12Lower
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node12Upper
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node13Lower
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node13Upper
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node14Lower
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node14Upper
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node15Lower
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node15Upper
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node16Lower
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node16Upper
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node17Lower
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node17Upper
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node18Lower
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node18Upper
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node19Lower
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node19Upper
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node20Lower
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node20Upper
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node21Lower
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node21Upper
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node22Lower
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node22Upper
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node23Lower
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node23Upper
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node24Lower
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node24Upper
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node25Lower
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node25Upper
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node26Lower
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node26Upper
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node27Lower
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node27Upper
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node28Lower
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node28Upper
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node29Lower
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node29Upper

/-! # The piecewise ψ bound from low-zero endpoint signs -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The xi function changes sign at the endpoints of each of the 29 rational
candidate intervals. This proposition is the remaining finite sign-certificate
input; it does not assert the signs without proof. -/
def LowZero100SignChanges : Prop :=
  ∀ i : Fin 29,
    let a : ℝ := lowZero100Lower i
    let b : ℝ := a + 1 / 100
    let f := fun t : ℝ ↦ (RiemannXi.riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re
    (f a < 0 ∧ 0 < f b) ∨ (f b < 0 ∧ 0 < f a)

/-- The normalized zeta value has the prescribed alternating margin `9/100000` at both
endpoints of each of the 29 candidate intervals. The zero-based even indices have negative
lower-endpoint values and positive upper-endpoint values; odd indices have the reverse signs. -/
def LowZero100SignMargins : Prop :=
  ∀ i : Fin 29,
    let a : ℝ := lowZero100Lower i
    let b : ℝ := a + 1 / 100
    if i.val % 2 = 0 then
      RiemannXi.normalizedZeta a < -(9 / 100000 : ℝ) ∧ (9 / 100000 : ℝ) < RiemannXi.normalizedZeta b
    else
      (9 / 100000 : ℝ) < RiemannXi.normalizedZeta a ∧ RiemannXi.normalizedZeta b < -(9 / 100000 : ℝ)

/-- At each candidate interval, the regularized completed-zeta values lie on
opposite sides of the algebraic xi-sign threshold. This is an equivalent
finite certificate condition using an absolutely convergent Mellin integral. -/
def LowZero100MellinSigns : Prop :=
  ∀ i : Fin 29,
    let a : ℝ := lowZero100Lower i
    let b : ℝ := a + 1 / 100
    let h := fun t : ℝ ↦ (t ^ 2 + 1 / 4) * RiemannXi.criticalCompletedZeta t
    (1 < h a ∧ h b < 1) ∨ (1 < h b ∧ h a < 1)

/-- The candidate xi-sign condition is equivalent to the Mellin threshold
condition. Both endpoints retain strict inequalities, so either certificate
can be used to construct the same critical-line zero intervals. -/
theorem low_zero_signs_iff_mellin : LowZero100SignChanges ↔ LowZero100MellinSigns := by
  simp only [LowZero100SignChanges, LowZero100MellinSigns, RiemannXi.xi_critical_neg_iff,
    RiemannXi.xi_critical_pos_iff]

/-- The rational endpoint tests for the computed completed-zeta approximation.
The strict margins include the proved uniform approximation error. -/
private def LowZero100RationalSigns : Prop :=
  ∀ i : Fin 29,
    let a : ℚ := lowZero100Lower i
    let b : ℚ := a + 1 / 100
    let lo := fun t : ℚ ↦ (t ^ 2 + 1 / 4) * (RiemannXi.gridCompletedHalf t - 4 / 10 ^ 38)
    let hi := fun t : ℚ ↦ (t ^ 2 + 1 / 4) * (RiemannXi.gridCompletedHalf t + 4 / 10 ^ 38)
    (1 < lo a ∧ hi b < 1) ∨ (1 < lo b ∧ hi a < 1)

/-- The rational endpoint tests imply all critical-line xi sign changes.
The endpoint height bounds are checked by exact finite arithmetic. -/
private theorem low_zero_signs_of_rational (hs : LowZero100RationalSigns) :
    LowZero100SignChanges := by
  have hpa : ∀ i : Fin 29, (0 : ℚ) ≤ lowZero100Lower i := by decide +kernel
  have hbu : ∀ i : Fin 29, lowZero100Lower i + (1 / 100 : ℚ) ≤ 100 := by decide +kernel
  intro i
  let a : ℚ := lowZero100Lower i
  let b : ℚ := a + 1 / 100
  have ha0 : 0 ≤ a := hpa i
  have hb0 : 0 ≤ b := by
    dsimp only [b]; linarith only [ha0]
  have hb100 : b ≤ 100 := hbu i
  have ha100 : |a| ≤ 100 := by
    rw [abs_of_nonneg ha0]
    dsimp only [b] at hb100
    linarith only [hb100]
  have hb100' : |b| ≤ 100 := by rwa [abs_of_nonneg hb0]
  have hi := hs i
  change
    (1 < (a ^ 2 + 1 / 4) * (RiemannXi.gridCompletedHalf a - 4 / 10 ^ 38) ∧
        (b ^ 2 + 1 / 4) * (RiemannXi.gridCompletedHalf b + 4 / 10 ^ 38) < 1) ∨
      (1 < (b ^ 2 + 1 / 4) * (RiemannXi.gridCompletedHalf b - 4 / 10 ^ 38) ∧
        (a ^ 2 + 1 / 4) * (RiemannXi.gridCompletedHalf a + 4 / 10 ^ 38) < 1) at hi
  have hres :
    ((RiemannXi.riemannXi (((1 / 2 : ℝ) : ℂ) + (a : ℂ) * Complex.I)).re < 0 ∧
        0 < (RiemannXi.riemannXi (((1 / 2 : ℝ) : ℂ) + (b : ℂ) * Complex.I)).re) ∨
      ((RiemannXi.riemannXi (((1 / 2 : ℝ) : ℂ) + (b : ℂ) * Complex.I)).re < 0 ∧
        0 < (RiemannXi.riemannXi (((1 / 2 : ℝ) : ℂ) + (a : ℂ) * Complex.I)).re) := by
    rcases hi with h | h
    · exact Or.inl ⟨RiemannXi.grid_xi_neg a ha100 h.1, RiemannXi.grid_xi_pos b hb100' h.2⟩
    · exact Or.inr ⟨RiemannXi.grid_xi_neg b hb100' h.1, RiemannXi.grid_xi_pos a ha100 h.2⟩
  have hbR : (b : ℝ) = (lowZero100Lower i : ℝ) + 1 / 100 := by
    simp only [a, b, Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  change
    ((RiemannXi.riemannXi (((1 / 2 : ℝ) : ℂ) + ((lowZero100Lower i : ℝ) : ℂ) * Complex.I)).re < 0 ∧
        0 <
          (RiemannXi.riemannXi
              (((1 / 2 : ℝ) : ℂ) + (((lowZero100Lower i : ℝ) + 1 / 100 : ℝ) : ℂ) * Complex.I)).re) ∨
      _
  rw [← hbR, Complex.ofReal_ratCast, Complex.ofReal_ratCast]
  exact hres

/-- The finite Gaussian Mellin integrals, including their rigorous error
budget, prove opposite endpoint signs in each candidate interval. The
parameters select a common number of terms and a common integral cutoff. -/
def LowZero100FiniteSigns (N : ℕ) (A : ℝ) : Prop :=
  ∀ i : Fin 29,
    let a : ℝ := lowZero100Lower i
    let b : ℝ := a + 1 / 100
    let lo := fun t : ℝ ↦
      (t ^ 2 + 1 / 4) *
        (RiemannXi.criticalCompletedFinite t N A - RiemannXi.criticalMellinError N A)
    let hi := fun t : ℝ ↦
      (t ^ 2 + 1 / 4) *
        (RiemannXi.criticalCompletedFinite t N A + RiemannXi.criticalMellinError N A)
    (1 < lo a ∧ hi b < 1) ∨ (1 < lo b ∧ hi a < 1)

/-- A finite Gaussian-integral certificate proves all candidate xi endpoint
sign changes. The explicit analytic error is already included in the
certificate, so no unproved approximation is used in the transfer. -/
theorem low_zero_signs_of_finite {A : ℝ} (hA : 1 ≤ A) (N : ℕ) (h : LowZero100FiniteSigns N A) :
    LowZero100SignChanges := by
  intro i
  have hi := h i
  rcases hi with hneg | hpos
  · exact
      Or.inl
        ⟨RiemannXi.critical_xi_negative_of_finite hA N hneg.1,
          RiemannXi.critical_xi_positive_of_finite hA N hneg.2⟩
  · exact
      Or.inr
        ⟨RiemannXi.critical_xi_negative_of_finite hA N hpos.1,
          RiemannXi.critical_xi_positive_of_finite hA N hpos.2⟩

/-- The compact Gaussian integrals at the candidate endpoints satisfy the
opposite-sign tests with the rational margin `10⁻⁵²`. The common parameters
are eight Gaussian terms and integration cutoff sixty. -/
def LowZero100CompactSigns : Prop :=
  ∀ i : Fin 29,
    let a : ℝ := lowZero100Lower i
    let b : ℝ := a + 1 / 100
    let lo := fun t : ℝ ↦
      (t ^ 2 + 1 / 4) * (RiemannXi.criticalCompletedFinite t 8 60 - 1 / (10 : ℝ) ^ 52)
    let hi := fun t : ℝ ↦
      (t ^ 2 + 1 / 4) * (RiemannXi.criticalCompletedFinite t 8 60 + 1 / (10 : ℝ) ^ 52)
    (1 < lo a ∧ hi b < 1) ∨ (1 < lo b ∧ hi a < 1)

/-- A compact-integral certificate with the rational error margin proves
all 29 xi endpoint sign changes. The transcendental truncation errors have
already been bounded, so the remaining checks concern finite integrals. -/
theorem low_zero_signs_of_compact (h : LowZero100CompactSigns) : LowZero100SignChanges := by
  intro i
  have hi := h i
  rcases hi with hneg | hpos
  · exact
      Or.inl
        ⟨RiemannXi.critical_xi_neg_eight_sixty hneg.1, RiemannXi.critical_xi_pos_eight_sixty hneg.2⟩
  · exact
      Or.inr
        ⟨RiemannXi.critical_xi_neg_eight_sixty hpos.1, RiemannXi.critical_xi_pos_eight_sixty hpos.2⟩

/-- The explicit 200th-order Taylor sums on the fixed rational grid prove
opposite signs at the candidate endpoints with the common rigorous error
`10⁻⁵² + 10⁻⁶⁰`. The remaining comparisons involve finite sums of endpoint
derivatives and do not require any external zero table. -/
def LowZero100TaylorSigns : Prop :=
  ∀ i : Fin 29,
    let a : ℝ := lowZero100Lower i
    let b : ℝ := a + 1 / 100
    let E : ℝ := 1 / (10 : ℝ) ^ 52 + 1 / (10 : ℝ) ^ 60
    let q := fun t : ℝ ↦
      RiemannXi.criticalThetaQuadrature t 8 200 944 RiemannXi.criticalQuadratureGrid
    (1 < (a ^ 2 + 1 / 4) * (q a - E) ∧ (b ^ 2 + 1 / 4) * (q b + E) < 1) ∨
      (1 < (b ^ 2 + 1 / 4) * (q b - E) ∧ (a ^ 2 + 1 / 4) * (q a + E) < 1)

/-- The endpoint sign certificate expressed using finite sums of explicit
coefficients, without iterated derivatives or external numerical tables. -/
def LowZero100ExplicitSigns : Prop :=
  ∀ i : Fin 29,
    let a : ℝ := lowZero100Lower i
    let b : ℝ := a + 1 / 100
    let E : ℝ := 1 / (10 : ℝ) ^ 52 + 1 / (10 : ℝ) ^ 60
    let q := fun t : ℝ ↦
      RiemannXi.criticalExplicitQuadrature t 8 200 944 RiemannXi.criticalQuadratureGrid
    (1 < (a ^ 2 + 1 / 4) * (q a - E) ∧ (b ^ 2 + 1 / 4) * (q b + E) < 1) ∨
      (1 < (b ^ 2 + 1 / 4) * (q b - E) ∧ (a ^ 2 + 1 / 4) * (q a + E) < 1)

/-- Explicit coefficient comparisons supply the derivative-based endpoint
certificate by the proven equality of the two quadrature forms. -/
theorem low_zero_taylor_of_explicit (h : LowZero100ExplicitSigns) : LowZero100TaylorSigns := by
  simpa only [LowZero100ExplicitSigns, LowZero100TaylorSigns,
    RiemannXi.critical_fixed_quadrature_explicit] using h

/-- A certificate for the explicit Taylor sums proves all 29 endpoint
sign changes. The rational endpoint bounds place both sides within the
height range of the uniform quadrature theorem. -/
theorem low_zero_signs_of_taylor (h : LowZero100TaylorSigns) : LowZero100SignChanges := by
  have hpa : ∀ i : Fin 29, (0 : ℚ) ≤ lowZero100Lower i := by decide +kernel
  have hbu : ∀ i : Fin 29, lowZero100Lower i + (1 / 100 : ℚ) ≤ 100 := by decide +kernel
  intro i
  let a : ℝ := lowZero100Lower i
  let b : ℝ := a + 1 / 100
  have ha0 : 0 ≤ a := by
    dsimp only [a]
    exact_mod_cast hpa i
  have hb0 : 0 ≤ b := by
    dsimp only [b]; linarith only [ha0]
  have hb100 : b ≤ 100 := by
    dsimp only [a, b]
    have hr : ((lowZero100Lower i + (1 / 100 : ℚ) : ℚ) : ℝ) ≤ ((100 : ℚ) : ℝ) :=
      Rat.cast_le.mpr (hbu i)
    norm_num only [Rat.cast_add, Rat.cast_div, Rat.cast_ofNat] at hr
    exact hr
  have ha100 : |a| ≤ 100 := by
    rw [abs_of_nonneg ha0]
    dsimp only [b] at hb100
    linarith only [hb100]
  have hb100' : |b| ≤ 100 := by rwa [abs_of_nonneg hb0]
  have hEa := RiemannXi.critical_quadrature_error ha100
  have hEb := RiemannXi.critical_quadrature_error hb100'
  have hi := h i
  change
    (1 <
          (a ^ 2 + 1 / 4) *
            (RiemannXi.criticalThetaQuadrature a 8 200 944 RiemannXi.criticalQuadratureGrid -
              (1 / (10 : ℝ) ^ 52 + 1 / (10 : ℝ) ^ 60)) ∧
        (b ^ 2 + 1 / 4) *
            (RiemannXi.criticalThetaQuadrature b 8 200 944 RiemannXi.criticalQuadratureGrid +
              (1 / (10 : ℝ) ^ 52 + 1 / (10 : ℝ) ^ 60)) <
          1) ∨
      (1 <
          (b ^ 2 + 1 / 4) *
            (RiemannXi.criticalThetaQuadrature b 8 200 944 RiemannXi.criticalQuadratureGrid -
              (1 / (10 : ℝ) ^ 52 + 1 / (10 : ℝ) ^ 60)) ∧
        (a ^ 2 + 1 / 4) *
            (RiemannXi.criticalThetaQuadrature a 8 200 944 RiemannXi.criticalQuadratureGrid +
              (1 / (10 : ℝ) ^ 52 + 1 / (10 : ℝ) ^ 60)) <
          1) at hi
  rcases hi with hneg | hpos
  · exact
      Or.inl
        ⟨RiemannXi.critical_xi_neg_of_approx hEa hneg.1,
          RiemannXi.critical_xi_pos_of_approx hEb hneg.2⟩
  · exact
      Or.inr
        ⟨RiemannXi.critical_xi_neg_of_approx hEb hpos.1,
          RiemannXi.critical_xi_pos_of_approx hEa hpos.2⟩

/-- The ordinates belong to the open intervals used in the height-100 sign certificate. -/
def LowZero100OpenBoxes (g : Fin 29 → ℝ) : Prop :=
  ∀ i, (lowZero100Lower i : ℝ) < g i ∧ g i < (lowZero100Lower i : ℝ) + 1 / 100

/-- Height-100 endpoint signs give ordered zeros strictly inside their certified intervals. -/
theorem low_zero_100_open_of_signs (hsign : LowZero100SignChanges) :
    ∃ g : Fin 29 → ℝ,
      StrictMono g ∧
        (∀ i, 0 < g i) ∧
        (∀ i, g i ≤ 100) ∧
        (∀ i, riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 0) ∧
        LowZero100OpenBoxes g := by
  let a : Fin 29 → ℝ := fun i ↦ lowZero100Lower i
  let b : Fin 29 → ℝ := fun i ↦ (lowZero100Lower i : ℝ) + 1 / 100
  have hpa : ∀ i : Fin 29, (0 : ℚ) ≤ lowZero100Lower i := by decide +kernel
  have hbu : ∀ i : Fin 29, lowZero100Lower i + (1 / 100 : ℚ) ≤ 100 := by decide +kernel
  have hsepq : ∀ i j : Fin 29, i < j → lowZero100Lower i + (1 / 100 : ℚ) ≤ lowZero100Lower j := by
    decide +kernel
  have hab : ∀ i, a i < b i := by
    intro i
    dsimp only [a, b]
    linarith only
  have hsep : ∀ i j, i < j → b i ≤ a j := by
    intro i j hij
    have h := hsepq i j hij
    dsimp only [a, b]
    have hr : ((lowZero100Lower i + (1 / 100 : ℚ) : ℚ) : ℝ) ≤ (lowZero100Lower j : ℝ) :=
      Rat.cast_le.mpr h
    norm_num only [Rat.cast_add, Rat.cast_div, Rat.cast_ofNat] at hr
    exact hr
  have hs :
    ∀ i,
      let f := fun t : ℝ ↦ (RiemannXi.riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re
      (f (a i) < 0 ∧ 0 < f (b i)) ∨ (f (b i) < 0 ∧ 0 < f (a i)) :=
    hsign
  obtain ⟨g, hm, hg, hz⟩ := RiemannXi.critical_zeros_of_sign_intervals a b hab hsep hs
  refine ⟨g, hm, ?_, ?_, hz, hg⟩
  · intro i
    have h : (0 : ℝ) ≤ a i := by
      dsimp only [a]
      exact_mod_cast hpa i
    exact h.trans_lt (hg i).1
  · intro i
    have h : b i ≤ (100 : ℝ) := by
      dsimp only [b]
      have hr : ((lowZero100Lower i + (1 / 100 : ℚ) : ℚ) : ℝ) ≤ ((100 : ℚ) : ℝ) :=
        Rat.cast_le.mpr (hbu i)
      norm_num only [Rat.cast_add, Rat.cast_div, Rat.cast_ofNat] at hr
      exact hr
    exact (hg i).2.le.trans h

/-- Certified sign changes on the candidate intervals produce the ordered
critical-line zero ordinates and both bracket predicates. The rational
endpoints are checked internally for positivity, separation and height. -/
theorem low_zero_100_of_signs (hsign : LowZero100SignChanges) :
    ∃ g : Fin 29 → ℝ,
      StrictMono g ∧
        (∀ i, 0 < g i) ∧
        (∀ i, g i ≤ 100) ∧
        (∀ i, riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 0) ∧
        LowZero100LowerBounds g ∧ LowZero100UpperBounds g := by
  obtain ⟨g, hm, hp, hh, hz, hb⟩ := low_zero_100_open_of_signs hsign
  exact ⟨g, hm, hp, hh, hz, fun i ↦ (hb i).1.le, fun i ↦ (hb i).2.le⟩

/-- Under RH, the endpoint signs and the two-sided count bound construct
29 ordered zeros that satisfy the candidate bounds, exhaust the positive
ledger through height 100, and all have multiplicity one. This is the
conditional bridge from the two independent certificates to Z100. -/
private theorem low_zero_100_complete_of_signs (hRH : RiemannHypothesis) (hc : zeroCount 100 ≤ 58)
    (hs : LowZero100SignChanges) :
    ∃ g : Fin 29 → ℝ,
      StrictMono g ∧
        (∀ i, 0 < g i) ∧
        (∀ i, g i ≤ 100) ∧
        (∀ i, riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 0) ∧
        LowZero100LowerBounds g ∧
        LowZero100UpperBounds g ∧
        ((zerosUpTo 100).filter (fun ρ ↦ 0 < ρ.im)) ⊆
          Finset.univ.image (fun i ↦ ((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) ∧
        ∀ i, riemannZetaZeroMultiplicity (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 1 := by
  obtain ⟨g, hm, hp, hh, hz, hl, hu⟩ := low_zero_100_of_signs hs
  have h := critical_zeros_complete_simple hRH hc g hm hp hh hz
  exact ⟨g, hm, hp, hh, hz, hl, hu, h.1, h.2⟩

/-- Under RH and the candidate endpoint signs, the constructed 29 critical
zeros leave at most three units jointly for other positive zeros through 100
and excess multiplicity at the selected zeros. This does not assert that the
remaining budget vanishes. -/
private theorem low_zero_remaining_budget_of_signs (hRH : RiemannHypothesis)
    (hs : LowZero100SignChanges) :
    ∃ g : Fin 29 → ℝ,
      StrictMono g ∧
        (∀ i, 0 < g i) ∧
        (∀ i, g i ≤ 100) ∧
        (∀ i, riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 0) ∧
        ((∑
              ρ ∈
                ((zerosUpTo 100).filter (fun ρ ↦ 0 < ρ.im)) \
                  Finset.univ.image (fun i ↦ ((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I),
              riemannZetaZeroMultiplicity ρ) +
            (∑ ρ ∈ Finset.univ.image (fun i ↦ ((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I),
              (riemannZetaZeroMultiplicity ρ - 1)) ≤
          3) := by
  obtain ⟨g, hm, hp, hh, hz, _, _⟩ := low_zero_100_of_signs hs
  exact ⟨g, hm, hp, hh, hz, critical_zeros_remaining_budget_le_3 hRH g hm hp hh hz⟩

/-- Under RH, certified candidate endpoint signs and the height-100 count
bound imply the requested piecewise ψ envelope for `x ≥ 101`. The zero
ordinates and their order are constructed from the sign changes. -/
theorem psi_piecewise_of_signs (hRH : RiemannHypothesis) (hs : LowZero100SignChanges)
    (hc : zeroCount 100 ≤ 58) {x : ℝ} (hx : 101 ≤ x) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ psiPiecewiseEnvelope x := by
  obtain ⟨g, hm, hp, hh, hz, hl, hu⟩ := low_zero_100_of_signs hs
  exact psi_piecewise_of_brackets hRH g hm hp hh hz hc hl hu hx

/-- Under RH, the rational endpoint tests and the height-100 zero count
bound imply the piecewise ψ envelope for every real `x ≥ 101`. -/
private theorem psi_piecewise_of_rational (hRH : RiemannHypothesis) (hs : LowZero100RationalSigns)
    (hc : zeroCount 100 ≤ 58) {x : ℝ} (hx : 101 ≤ x) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ psiPiecewiseEnvelope x := by
  exact psi_piecewise_of_signs hRH (low_zero_signs_of_rational hs) hc hx

/-- Under RH, certified candidate endpoint signs and the height-100 count
bound imply the Lee–Nosal logarithmic ψ estimate for all `x ≥ 101`. -/
theorem psi_lee_nosal_of_signs (hRH : RiemannHypothesis) (hs : LowZero100SignChanges)
    (hc : zeroCount 100 ≤ 58) {x : ℝ} (hx : 101 ≤ x) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ leeNosalPsiLog (Real.log x) := by
  obtain ⟨g, hm, hp, hh, hz, hl, hu, _, _⟩ := low_zero_100_complete_of_signs hRH hc hs
  exact psi_lee_nosal_of_brackets hRH g hm hp hh hz hc hl hu hx

/-- Under RH and the 29 endpoint sign changes, the internally certified
height-100 upper bound and the constructed zeros give the exact count 58. -/
theorem count_100_eq_58_of_signs (hRH : RiemannHypothesis) (hs : LowZero100SignChanges) :
    zeroCount 100 = 58 := by
  obtain ⟨g, hm, hp, hh, hz, _, _⟩ := low_zero_100_of_signs hs
  exact critical_zeros_count_eq_58 hRH (zero_count_100_le_58_of_RH hRH) g hm hp hh hz

/-- Under RH and the 29 endpoint sign changes, there are 29 ordered positive
critical-line zeros through height 100, they exhaust the positive ledger, and
each is simple. The count bound is supplied by the internal certificate. -/
theorem low_zeros_complete_of_signs (hRH : RiemannHypothesis) (hs : LowZero100SignChanges) :
    ∃ g : Fin 29 → ℝ,
      StrictMono g ∧
        (∀ i, 0 < g i) ∧
        (∀ i, g i ≤ 100) ∧
        (∀ i, riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 0) ∧
        ((zerosUpTo 100).filter (fun ρ ↦ 0 < ρ.im)) ⊆
          Finset.univ.image (fun i ↦ ((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) ∧
        ∀ i, riemannZetaZeroMultiplicity (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 1 := by
  obtain ⟨g, hm, hp, hh, hz, _, _⟩ := low_zero_100_of_signs hs
  have h := critical_zeros_complete_simple hRH (zero_count_100_le_58_of_RH hRH) g hm hp hh hz
  exact ⟨g, hm, hp, hh, hz, h.1, h.2⟩

/-- Under RH and the 29 endpoint sign changes, the Lee–Nosal logarithmic
estimate holds for every `x ≥ 101`. The height-100 count bound is supplied
by the internal finite-sum certificate. -/
theorem psi_lee_nosal_of_signs_RH (hRH : RiemannHypothesis) (hs : LowZero100SignChanges) {x : ℝ}
    (hx : 101 ≤ x) : |Chebyshev.psi x - x| / Real.sqrt x ≤ leeNosalPsiLog (Real.log x) := by
  exact psi_lee_nosal_of_signs hRH hs (zero_count_100_le_58_of_RH hRH) hx

/-- Under RH, the certified candidate signs and positivity of the real part of zeta
on the horizontal segment at height 100 imply the Lee–Nosal bound for `x ≥ 101`.
The phase argument derives the required zero count from that positivity. -/
private theorem psi_lee_nosal_of_positive_line (hRH : RiemannHypothesis)
    (hs : LowZero100SignChanges)
    (hpos :
      ∀ t : ℝ,
        t ∈ Set.Icc (1 / 2) (3 / 2) → 0 < (riemannZeta ((t : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)).re)
    {x : ℝ} (hx : 101 ≤ x) : |Chebyshev.psi x - x| / Real.sqrt x ≤ leeNosalPsiLog (Real.log x) := by
  exact psi_lee_nosal_of_signs hRH hs (count_100_le_58_of_positive_line hRH hpos) hx

/-- Under RH, the candidate signs and 129 lower bounds for zeta on the line
at height 100 imply the Lee–Nosal estimate for `x ≥ 101`. The zero count is
derived from the grid bounds and the internally proved derivative estimate. -/
private theorem psi_lee_nosal_of_grid_values (hRH : RiemannHypothesis) (hs : LowZero100SignChanges)
    (hg :
      ∀ k : ℕ,
        k ≤ 128 →
          1 ≤ (riemannZeta (((1 / 2 + (k : ℝ) / 128 : ℝ) : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)).re)
    {x : ℝ} (hx : 101 ≤ x) : |Chebyshev.psi x - x| / Real.sqrt x ≤ leeNosalPsiLog (Real.log x) := by
  exact psi_lee_nosal_of_signs hRH hs (count_100_le_58_of_grid_values hRH hg) hx

/-- Under RH, the candidate signs and positivity on the horizontal segment at height 100
give the stronger piecewise envelope for `x ≥ 101`. The zero count follows from positivity. -/
private theorem psi_piecewise_of_positive_line (hRH : RiemannHypothesis)
    (hs : LowZero100SignChanges)
    (hpos :
      ∀ t : ℝ,
        t ∈ Set.Icc (1 / 2) (3 / 2) → 0 < (riemannZeta ((t : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)).re)
    {x : ℝ} (hx : 101 ≤ x) : |Chebyshev.psi x - x| / Real.sqrt x ≤ psiPiecewiseEnvelope x := by
  exact psi_piecewise_of_signs hRH hs (count_100_le_58_of_positive_line hRH hpos) hx

/-- Under RH, endpoint signs and a complete simple enumeration of 29
positive ledger zeros imply the Lee–Nosal bound for `x ≥ 101`. The count
bound is derived from the enumeration rather than assumed separately. -/
private theorem psi_lee_nosal_of_complete_simple (hRH : RiemannHypothesis)
    (hs : LowZero100SignChanges) (z : Fin 29 → ℂ) (hinj : Function.Injective z)
    (hz : ∀ i, z i ∈ (zerosUpTo 100).filter (fun ρ ↦ 0 < ρ.im))
    (hcomplete : (zerosUpTo 100).filter (fun ρ ↦ 0 < ρ.im) ⊆ Finset.univ.image z)
    (hsimple : ∀ i, riemannZetaZeroMultiplicity (z i) = 1) {x : ℝ} (hx : 101 ≤ x) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ leeNosalPsiLog (Real.log x) := by
  exact
    psi_lee_nosal_of_signs hRH hs
      (count_100_le_58_of_complete_simple hRH z hinj hz hcomplete hsimple) hx

/-- Under RH, the endpoint signs and height-100 count bound give the
integrated envelope and its `1/200` Lee–Nosal margin for `log x ≥ 97/5`.
The ordinate hypotheses are obtained from the sign certificate. -/
theorem psi_integrated_of_signs (hRH : RiemannHypothesis) (hs : LowZero100SignChanges)
    (hc : zeroCount 100 ≤ 58) {x : ℝ} (hx : 0 < x) (hL : (97 / 5 : ℝ) ≤ Real.log x) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ integratedPsiEnvelope (Real.log x) ∧
      integratedPsiEnvelope (Real.log x) ≤ leeNosalPsiLog (Real.log x) - 1 / 200 := by
  obtain ⟨g, hm, hp, hh, hz, hl, _⟩ := low_zero_100_of_signs hs
  exact psi_integrated_envelope_of_brackets hRH g hm hp hh hz hc hl hx hL

/-- Under RH, a finite Gaussian-integral sign certificate and the
height-100 count bound give the complete piecewise ψ estimate for every
`x ≥ 101`. The sign certificate includes the explicit truncation errors. -/
theorem psi_piecewise_of_finite (hRH : RiemannHypothesis) {A : ℝ} (hA : 1 ≤ A) (N : ℕ)
    (hs : LowZero100FiniteSigns N A) (hc : zeroCount 100 ≤ 58) {x : ℝ} (hx : 101 ≤ x) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ psiPiecewiseEnvelope x := by
  exact psi_piecewise_of_signs hRH (low_zero_signs_of_finite hA N hs) hc hx

/-- Under RH, a finite Gaussian-integral sign certificate and the
height-100 count bound imply the integrated ψ envelope with the stated
`1/200` margin for `log x ≥ 97/5`. -/
theorem psi_integrated_of_finite (hRH : RiemannHypothesis) {A : ℝ} (hA : 1 ≤ A) (N : ℕ)
    (hs : LowZero100FiniteSigns N A) (hc : zeroCount 100 ≤ 58) {x : ℝ} (hx : 0 < x)
    (hL : (97 / 5 : ℝ) ≤ Real.log x) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ integratedPsiEnvelope (Real.log x) ∧
      integratedPsiEnvelope (Real.log x) ≤ leeNosalPsiLog (Real.log x) - 1 / 200 := by
  exact psi_integrated_of_signs hRH (low_zero_signs_of_finite hA N hs) hc hx hL

/-- Under RH, the compact-integral sign certificate with rational error
margin and the height-100 count bound imply the complete piecewise ψ
estimate for every `x ≥ 101`. -/
theorem psi_piecewise_of_compact (hRH : RiemannHypothesis) (hs : LowZero100CompactSigns)
    (hc : zeroCount 100 ≤ 58) {x : ℝ} (hx : 101 ≤ x) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ psiPiecewiseEnvelope x := by
  exact psi_piecewise_of_signs hRH (low_zero_signs_of_compact hs) hc hx

/-- Under RH, an explicit Taylor-sum endpoint certificate and the
height-100 count bound imply the complete piecewise ψ estimate for every
`x ≥ 101`. All analytic and quadrature errors are included in the fixed
rational sign margin. -/
theorem psi_piecewise_of_taylor (hRH : RiemannHypothesis) (hs : LowZero100TaylorSigns)
    (hc : zeroCount 100 ≤ 58) {x : ℝ} (hx : 101 ≤ x) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ psiPiecewiseEnvelope x := by
  exact psi_piecewise_of_signs hRH (low_zero_signs_of_taylor hs) hc hx

/-- Under RH, the explicit finite coefficient comparisons and the
height-100 count bound imply the piecewise ψ estimate for `x ≥ 101`.
The comparisons contain the proved analytic and quadrature error margins. -/
theorem psi_piecewise_of_explicit (hRH : RiemannHypothesis) (hs : LowZero100ExplicitSigns)
    (hc : zeroCount 100 ≤ 58) {x : ℝ} (hx : 101 ≤ x) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ psiPiecewiseEnvelope x := by
  exact psi_piecewise_of_taylor hRH (low_zero_taylor_of_explicit hs) hc hx

-- Combining all 29 independently verified endpoint pairs requires more elaboration steps.
set_option maxHeartbeats 20000000 in
-- Each case instantiates and converts a separately verified endpoint pair.
/-- All 29 candidate intervals have opposite xi endpoint signs. Each pair follows from
kernel-checked rational finite approximations and the uniform analytic error bounds; no RH
assumption or external zero table is used. This supplies the input for the low-zero count and
the global Lee–Nosal estimate. -/
theorem low_zero_100_sign_changes : LowZero100SignChanges := by
  intro i
  fin_cases i
  case
    «0» =>
    have h :=
      endpoint_checked_signs (14473 / 1024) (by norm_num only) (by norm_num only)
        endpoint_01_lower_check.1 endpoint_01_upper_check.1
        (Or.inl ⟨endpoint_01_lower_check.2, endpoint_01_upper_check.2⟩)
    change
      (let a : ℝ := (14473 / 1024 : ℚ)
      let b : ℝ := a + 1 / 100
      let f := fun t : ℝ ↦ (RiemannXi.riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re
      (f a < 0 ∧ 0 < f b) ∨ (f b < 0 ∧ 0 < f a))
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
  case
    «1» =>
    have h :=
      endpoint_checked_signs (10763 / 512) (by norm_num only) (by norm_num only)
        endpoint_02_lower_check.1 endpoint_02_upper_check.1
        (Or.inr ⟨endpoint_02_upper_check.2, endpoint_02_lower_check.2⟩)
    change
      (let a : ℝ := (10763 / 512 : ℚ)
      let b : ℝ := a + 1 / 100
      let f := fun t : ℝ ↦ (RiemannXi.riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re
      (f a < 0 ∧ 0 < f b) ∨ (f b < 0 ∧ 0 < f a))
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
  case
    «2» =>
    have h :=
      endpoint_checked_signs (25611 / 1024) (by norm_num only) (by norm_num only)
        endpoint_03_lower_check.1 endpoint_03_upper_check.1
        (Or.inl ⟨endpoint_03_lower_check.2, endpoint_03_upper_check.2⟩)
    change
      (let a : ℝ := (25611 / 1024 : ℚ)
      let b : ℝ := a + 1 / 100
      let f := fun t : ℝ ↦ (RiemannXi.riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re
      (f a < 0 ∧ 0 < f b) ∨ (f b < 0 ∧ 0 < f a))
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
  case
    «3» =>
    have h :=
      endpoint_checked_signs (31155 / 1024) (by norm_num only) (by norm_num only)
        endpoint_04_lower_check.1 endpoint_04_upper_check.1
        (Or.inr ⟨endpoint_04_upper_check.2, endpoint_04_lower_check.2⟩)
    change
      (let a : ℝ := (31155 / 1024 : ℚ)
      let b : ℝ := a + 1 / 100
      let f := fun t : ℝ ↦ (RiemannXi.riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re
      (f a < 0 ∧ 0 < f b) ∨ (f b < 0 ∧ 0 < f a))
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
  case
    «4» =>
    have h :=
      endpoint_checked_signs (33725 / 1024) (by norm_num only) (by norm_num only)
        endpoint_05_lower_check.1 endpoint_05_upper_check.1
        (Or.inl ⟨endpoint_05_lower_check.2, endpoint_05_upper_check.2⟩)
    change
      (let a : ℝ := (33725 / 1024 : ℚ)
      let b : ℝ := a + 1 / 100
      let f := fun t : ℝ ↦ (RiemannXi.riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re
      (f a < 0 ∧ 0 < f b) ∨ (f b < 0 ∧ 0 < f a))
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
  case
    «5» =>
    have h :=
      endpoint_checked_signs (4811 / 128) (by norm_num only) (by norm_num only)
        endpoint_06_lower_check.1 endpoint_06_upper_check.1
        (Or.inr ⟨endpoint_06_upper_check.2, endpoint_06_lower_check.2⟩)
    change
      (let a : ℝ := (4811 / 128 : ℚ)
      let b : ℝ := a + 1 / 100
      let f := fun t : ℝ ↦ (RiemannXi.riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re
      (f a < 0 ∧ 0 < f b) ∨ (f b < 0 ∧ 0 < f a))
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
  case
    «6» =>
    have h :=
      endpoint_checked_signs (10475 / 256) (by norm_num only) (by norm_num only)
        endpoint_07_lower_check.1 endpoint_07_upper_check.1
        (Or.inl ⟨endpoint_07_lower_check.2, endpoint_07_upper_check.2⟩)
    change
      (let a : ℝ := (10475 / 256 : ℚ)
      let b : ℝ := a + 1 / 100
      let f := fun t : ℝ ↦ (RiemannXi.riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re
      (f a < 0 ∧ 0 < f b) ∨ (f b < 0 ∧ 0 < f a))
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
  case
    «7» =>
    have h :=
      endpoint_checked_signs (22183 / 512) (by norm_num only) (by norm_num only)
        endpoint_08_lower_check.1 endpoint_08_upper_check.1
        (Or.inr ⟨endpoint_08_upper_check.2, endpoint_08_lower_check.2⟩)
    change
      (let a : ℝ := (22183 / 512 : ℚ)
      let b : ℝ := a + 1 / 100
      let f := fun t : ℝ ↦ (RiemannXi.riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re
      (f a < 0 ∧ 0 < f b) ∨ (f b < 0 ∧ 0 < f a))
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
  case
    «8» =>
    have h :=
      endpoint_checked_signs (49157 / 1024) (by norm_num only) (by norm_num only)
        endpoint_09_lower_check.1 endpoint_09_upper_check.1
        (Or.inl ⟨endpoint_09_lower_check.2, endpoint_09_upper_check.2⟩)
    change
      (let a : ℝ := (49157 / 1024 : ℚ)
      let b : ℝ := a + 1 / 100
      let f := fun t : ℝ ↦ (RiemannXi.riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re
      (f a < 0 ∧ 0 < f b) ∨ (f b < 0 ∧ 0 < f a))
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
  case
    «9» =>
    have h :=
      endpoint_checked_signs (6371 / 128) (by norm_num only) (by norm_num only)
        endpoint_10_lower_check.1 endpoint_10_upper_check.1
        (Or.inr ⟨endpoint_10_upper_check.2, endpoint_10_lower_check.2⟩)
    change
      (let a : ℝ := (6371 / 128 : ℚ)
      let b : ℝ := a + 1 / 100
      let f := fun t : ℝ ↦ (RiemannXi.riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re
      (f a < 0 ∧ 0 < f b) ∨ (f b < 0 ∧ 0 < f a))
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
  case
    «10» =>
    have h :=
      endpoint_checked_signs (54241 / 1024) (by norm_num only) (by norm_num only)
        endpoint_11_lower_check.1 endpoint_11_upper_check.1
        (Or.inl ⟨endpoint_11_lower_check.2, endpoint_11_upper_check.2⟩)
    change
      (let a : ℝ := (54241 / 1024 : ℚ)
      let b : ℝ := a + 1 / 100
      let f := fun t : ℝ ↦ (RiemannXi.riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re
      (f a < 0 ∧ 0 < f b) ∨ (f b < 0 ∧ 0 < f a))
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
  case
    «11» =>
    have h :=
      endpoint_checked_signs (7225 / 128) (by norm_num only) (by norm_num only)
        endpoint_12_lower_check.1 endpoint_12_upper_check.1
        (Or.inr ⟨endpoint_12_upper_check.2, endpoint_12_lower_check.2⟩)
    change
      (let a : ℝ := (7225 / 128 : ℚ)
      let b : ℝ := a + 1 / 100
      let f := fun t : ℝ ↦ (RiemannXi.riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re
      (f a < 0 ∧ 0 < f b) ∨ (f b < 0 ∧ 0 < f a))
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
  case
    «12» =>
    have h :=
      endpoint_checked_signs (60771 / 1024) (by norm_num only) (by norm_num only)
        endpoint_13_lower_check.1 endpoint_13_upper_check.1
        (Or.inl ⟨endpoint_13_lower_check.2, endpoint_13_upper_check.2⟩)
    change
      (let a : ℝ := (60771 / 1024 : ℚ)
      let b : ℝ := a + 1 / 100
      let f := fun t : ℝ ↦ (RiemannXi.riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re
      (f a < 0 ∧ 0 < f b) ∨ (f b < 0 ∧ 0 < f a))
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
  case
    «13» =>
    have h :=
      endpoint_checked_signs (62291 / 1024) (by norm_num only) (by norm_num only)
        endpoint_14_lower_check.1 endpoint_14_upper_check.1
        (Or.inr ⟨endpoint_14_upper_check.2, endpoint_14_lower_check.2⟩)
    change
      (let a : ℝ := (62291 / 1024 : ℚ)
      let b : ℝ := a + 1 / 100
      let f := fun t : ℝ ↦ (RiemannXi.riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re
      (f a < 0 ∧ 0 < f b) ∨ (f b < 0 ∧ 0 < f a))
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
  case
    «14» =>
    have h :=
      endpoint_checked_signs (66675 / 1024) (by norm_num only) (by norm_num only)
        endpoint_15_lower_check.1 endpoint_15_upper_check.1
        (Or.inl ⟨endpoint_15_lower_check.2, endpoint_15_upper_check.2⟩)
    change
      (let a : ℝ := (66675 / 1024 : ℚ)
      let b : ℝ := a + 1 / 100
      let f := fun t : ℝ ↦ (RiemannXi.riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re
      (f a < 0 ∧ 0 < f b) ∨ (f b < 0 ∧ 0 < f a))
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
  case
    «15» =>
    have h :=
      endpoint_checked_signs (68689 / 1024) (by norm_num only) (by norm_num only)
        endpoint_16_lower_check.1 endpoint_16_upper_check.1
        (Or.inr ⟨endpoint_16_upper_check.2, endpoint_16_lower_check.2⟩)
    change
      (let a : ℝ := (68689 / 1024 : ℚ)
      let b : ℝ := a + 1 / 100
      let f := fun t : ℝ ↦ (RiemannXi.riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re
      (f a < 0 ∧ 0 < f b) ∨ (f b < 0 ∧ 0 < f a))
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
  case
    «16» =>
    have h :=
      endpoint_checked_signs (71215 / 1024) (by norm_num only) (by norm_num only)
        endpoint_17_lower_check.1 endpoint_17_upper_check.1
        (Or.inl ⟨endpoint_17_lower_check.2, endpoint_17_upper_check.2⟩)
    change
      (let a : ℝ := (71215 / 1024 : ℚ)
      let b : ℝ := a + 1 / 100
      let f := fun t : ℝ ↦ (RiemannXi.riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re
      (f a < 0 ∧ 0 < f b) ∨ (f b < 0 ∧ 0 < f a))
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
  case
    «17» =>
    have h :=
      endpoint_checked_signs (18449 / 256) (by norm_num only) (by norm_num only)
        endpoint_18_lower_check.1 endpoint_18_upper_check.1
        (Or.inr ⟨endpoint_18_upper_check.2, endpoint_18_lower_check.2⟩)
    change
      (let a : ℝ := (18449 / 256 : ℚ)
      let b : ℝ := a + 1 / 100
      let f := fun t : ℝ ↦ (RiemannXi.riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re
      (f a < 0 ∧ 0 < f b) ∨ (f b < 0 ∧ 0 < f a))
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
  case
    «18» =>
    have h :=
      endpoint_checked_signs (77521 / 1024) (by norm_num only) (by norm_num only)
        endpoint_19_lower_check.1 endpoint_19_upper_check.1
        (Or.inl ⟨endpoint_19_lower_check.2, endpoint_19_upper_check.2⟩)
    change
      (let a : ℝ := (77521 / 1024 : ℚ)
      let b : ℝ := a + 1 / 100
      let f := fun t : ℝ ↦ (RiemannXi.riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re
      (f a < 0 ∧ 0 < f b) ∨ (f b < 0 ∧ 0 < f a))
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
  case
    «19» =>
    have h :=
      endpoint_checked_signs (19749 / 256) (by norm_num only) (by norm_num only)
        endpoint_20_lower_check.1 endpoint_20_upper_check.1
        (Or.inr ⟨endpoint_20_upper_check.2, endpoint_20_lower_check.2⟩)
    change
      (let a : ℝ := (19749 / 256 : ℚ)
      let b : ℝ := a + 1 / 100
      let f := fun t : ℝ ↦ (RiemannXi.riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re
      (f a < 0 ∧ 0 < f b) ∨ (f b < 0 ∧ 0 < f a))
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
  case
    «20» =>
    have h :=
      endpoint_checked_signs (81241 / 1024) (by norm_num only) (by norm_num only)
        endpoint_21_lower_check.1 endpoint_21_upper_check.1
        (Or.inl ⟨endpoint_21_lower_check.2, endpoint_21_upper_check.2⟩)
    change
      (let a : ℝ := (81241 / 1024 : ℚ)
      let b : ℝ := a + 1 / 100
      let f := fun t : ℝ ↦ (RiemannXi.riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re
      (f a < 0 ∧ 0 < f b) ∨ (f b < 0 ∧ 0 < f a))
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
  case
    «21» =>
    have h :=
      endpoint_checked_signs (21225 / 256) (by norm_num only) (by norm_num only)
        endpoint_22_lower_check.1 endpoint_22_upper_check.1
        (Or.inr ⟨endpoint_22_upper_check.2, endpoint_22_lower_check.2⟩)
    change
      (let a : ℝ := (21225 / 256 : ℚ)
      let b : ℝ := a + 1 / 100
      let f := fun t : ℝ ↦ (RiemannXi.riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re
      (f a < 0 ∧ 0 < f b) ∨ (f b < 0 ∧ 0 < f a))
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
  case
    «22» =>
    have h :=
      endpoint_checked_signs (86769 / 1024) (by norm_num only) (by norm_num only)
        endpoint_23_lower_check.1 endpoint_23_upper_check.1
        (Or.inl ⟨endpoint_23_lower_check.2, endpoint_23_upper_check.2⟩)
    change
      (let a : ℝ := (86769 / 1024 : ℚ)
      let b : ℝ := a + 1 / 100
      let f := fun t : ℝ ↦ (RiemannXi.riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re
      (f a < 0 ∧ 0 < f b) ∨ (f b < 0 ∧ 0 < f a))
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
  case
    «23» =>
    have h :=
      endpoint_checked_signs (89523 / 1024) (by norm_num only) (by norm_num only)
        endpoint_24_lower_check.1 endpoint_24_upper_check.1
        (Or.inr ⟨endpoint_24_upper_check.2, endpoint_24_lower_check.2⟩)
    change
      (let a : ℝ := (89523 / 1024 : ℚ)
      let b : ℝ := a + 1 / 100
      let f := fun t : ℝ ↦ (RiemannXi.riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re
      (f a < 0 ∧ 0 < f b) ∨ (f b < 0 ∧ 0 < f a))
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
  case
    «24» =>
    have h :=
      endpoint_checked_signs (22735 / 256) (by norm_num only) (by norm_num only)
        endpoint_25_lower_check.1 endpoint_25_upper_check.1
        (Or.inl ⟨endpoint_25_lower_check.2, endpoint_25_upper_check.2⟩)
    change
      (let a : ℝ := (22735 / 256 : ℚ)
      let b : ℝ := a + 1 / 100
      let f := fun t : ℝ ↦ (RiemannXi.riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re
      (f a < 0 ∧ 0 < f b) ∨ (f b < 0 ∧ 0 < f a))
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
  case
    «25» =>
    have h :=
      endpoint_checked_signs (94711 / 1024) (by norm_num only) (by norm_num only)
        endpoint_26_lower_check.1 endpoint_26_upper_check.1
        (Or.inr ⟨endpoint_26_upper_check.2, endpoint_26_lower_check.2⟩)
    change
      (let a : ℝ := (94711 / 1024 : ℚ)
      let b : ℝ := a + 1 / 100
      let f := fun t : ℝ ↦ (RiemannXi.riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re
      (f a < 0 ∧ 0 < f b) ∨ (f b < 0 ∧ 0 < f a))
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
  case
    «26» =>
    have h :=
      endpoint_checked_signs (48461 / 512) (by norm_num only) (by norm_num only)
        endpoint_27_lower_check.1 endpoint_27_upper_check.1
        (Or.inl ⟨endpoint_27_lower_check.2, endpoint_27_upper_check.2⟩)
    change
      (let a : ℝ := (48461 / 512 : ℚ)
      let b : ℝ := a + 1 / 100
      let f := fun t : ℝ ↦ (RiemannXi.riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re
      (f a < 0 ∧ 0 < f b) ∨ (f b < 0 ∧ 0 < f a))
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
  case
    «27» =>
    have h :=
      endpoint_checked_signs (98171 / 1024) (by norm_num only) (by norm_num only)
        endpoint_28_lower_check.1 endpoint_28_upper_check.1
        (Or.inr ⟨endpoint_28_upper_check.2, endpoint_28_lower_check.2⟩)
    change
      (let a : ℝ := (98171 / 1024 : ℚ)
      let b : ℝ := a + 1 / 100
      let f := fun t : ℝ ↦ (RiemannXi.riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re
      (f a < 0 ∧ 0 < f b) ∨ (f b < 0 ∧ 0 < f a))
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
  case
    «28» =>
    have h :=
      endpoint_checked_signs (101203 / 1024) (by norm_num only) (by norm_num only)
        endpoint_29_lower_check.1 endpoint_29_upper_check.1
        (Or.inl ⟨endpoint_29_lower_check.2, endpoint_29_upper_check.2⟩)
    change
      (let a : ℝ := (101203 / 1024 : ℚ)
      let b : ℝ := a + 1 / 100
      let f := fun t : ℝ ↦ (RiemannXi.riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re
      (f a < 0 ∧ 0 < f b) ∨ (f b < 0 ∧ 0 < f a))
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h

-- Combining 58 independently checked margins requires more elaboration steps.
set_option maxHeartbeats 20000000 in
-- Each case converts two exact rational certificates into real inequalities.
/-- All 58 candidate endpoints satisfy the prescribed alternating normalized zeta margins
of `9/100000`. Each endpoint follows from a kernel-checked rational approximation and the
uniform analytic error bound, without RH or an external numerical table. -/
theorem low_zero_100_sign_margins : LowZero100SignMargins := by
  intro i
  fin_cases i
  case
    «0» =>
    change
      RiemannXi.normalizedZeta ((14473 / 1024 : ℚ) : ℝ) < -(9 / 100000 : ℝ) ∧
        (9 / 100000 : ℝ) < RiemannXi.normalizedZeta (((14473 / 1024 : ℚ) : ℝ) + 1 / 100)
    have hl :=
      endpoint_fast_negative_margin (14473 / 1024) (by norm_num only) (by norm_num only)
        endpoint_01_lower_check.1 endpoint_01_lower_check.2
    have hu :=
      endpoint_fast_positive_margin ((14473 / 1024 : ℚ) + 1 / 100) (by norm_num only)
        (by norm_num only) endpoint_01_upper_check.1 endpoint_01_upper_check.2
    constructor
    · exact hl
    · simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hu
  case
    «1» =>
    change
      (9 / 100000 : ℝ) < RiemannXi.normalizedZeta ((10763 / 512 : ℚ) : ℝ) ∧
        RiemannXi.normalizedZeta (((10763 / 512 : ℚ) : ℝ) + 1 / 100) < -(9 / 100000 : ℝ)
    have hl :=
      endpoint_fast_positive_margin (10763 / 512) (by norm_num only) (by norm_num only)
        endpoint_02_lower_check.1 endpoint_02_lower_check.2
    have hu :=
      endpoint_fast_negative_margin ((10763 / 512 : ℚ) + 1 / 100) (by norm_num only)
        (by norm_num only) endpoint_02_upper_check.1 endpoint_02_upper_check.2
    constructor
    · exact hl
    · simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hu
  case
    «2» =>
    change
      RiemannXi.normalizedZeta ((25611 / 1024 : ℚ) : ℝ) < -(9 / 100000 : ℝ) ∧
        (9 / 100000 : ℝ) < RiemannXi.normalizedZeta (((25611 / 1024 : ℚ) : ℝ) + 1 / 100)
    have hl :=
      endpoint_fast_negative_margin (25611 / 1024) (by norm_num only) (by norm_num only)
        endpoint_03_lower_check.1 endpoint_03_lower_check.2
    have hu :=
      endpoint_fast_positive_margin ((25611 / 1024 : ℚ) + 1 / 100) (by norm_num only)
        (by norm_num only) endpoint_03_upper_check.1 endpoint_03_upper_check.2
    constructor
    · exact hl
    · simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hu
  case
    «3» =>
    change
      (9 / 100000 : ℝ) < RiemannXi.normalizedZeta ((31155 / 1024 : ℚ) : ℝ) ∧
        RiemannXi.normalizedZeta (((31155 / 1024 : ℚ) : ℝ) + 1 / 100) < -(9 / 100000 : ℝ)
    have hl :=
      endpoint_fast_positive_margin (31155 / 1024) (by norm_num only) (by norm_num only)
        endpoint_04_lower_check.1 endpoint_04_lower_check.2
    have hu :=
      endpoint_fast_negative_margin ((31155 / 1024 : ℚ) + 1 / 100) (by norm_num only)
        (by norm_num only) endpoint_04_upper_check.1 endpoint_04_upper_check.2
    constructor
    · exact hl
    · simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hu
  case
    «4» =>
    change
      RiemannXi.normalizedZeta ((33725 / 1024 : ℚ) : ℝ) < -(9 / 100000 : ℝ) ∧
        (9 / 100000 : ℝ) < RiemannXi.normalizedZeta (((33725 / 1024 : ℚ) : ℝ) + 1 / 100)
    have hl :=
      endpoint_fast_negative_margin (33725 / 1024) (by norm_num only) (by norm_num only)
        endpoint_05_lower_check.1 endpoint_05_lower_check.2
    have hu :=
      endpoint_fast_positive_margin ((33725 / 1024 : ℚ) + 1 / 100) (by norm_num only)
        (by norm_num only) endpoint_05_upper_check.1 endpoint_05_upper_check.2
    constructor
    · exact hl
    · simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hu
  case
    «5» =>
    change
      (9 / 100000 : ℝ) < RiemannXi.normalizedZeta ((4811 / 128 : ℚ) : ℝ) ∧
        RiemannXi.normalizedZeta (((4811 / 128 : ℚ) : ℝ) + 1 / 100) < -(9 / 100000 : ℝ)
    have hl :=
      endpoint_fast_positive_margin (4811 / 128) (by norm_num only) (by norm_num only)
        endpoint_06_lower_check.1 endpoint_06_lower_check.2
    have hu :=
      endpoint_fast_negative_margin ((4811 / 128 : ℚ) + 1 / 100) (by norm_num only)
        (by norm_num only) endpoint_06_upper_check.1 endpoint_06_upper_check.2
    constructor
    · exact hl
    · simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hu
  case
    «6» =>
    change
      RiemannXi.normalizedZeta ((10475 / 256 : ℚ) : ℝ) < -(9 / 100000 : ℝ) ∧
        (9 / 100000 : ℝ) < RiemannXi.normalizedZeta (((10475 / 256 : ℚ) : ℝ) + 1 / 100)
    have hl :=
      endpoint_fast_negative_margin (10475 / 256) (by norm_num only) (by norm_num only)
        endpoint_07_lower_check.1 endpoint_07_lower_check.2
    have hu :=
      endpoint_fast_positive_margin ((10475 / 256 : ℚ) + 1 / 100) (by norm_num only)
        (by norm_num only) endpoint_07_upper_check.1 endpoint_07_upper_check.2
    constructor
    · exact hl
    · simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hu
  case
    «7» =>
    change
      (9 / 100000 : ℝ) < RiemannXi.normalizedZeta ((22183 / 512 : ℚ) : ℝ) ∧
        RiemannXi.normalizedZeta (((22183 / 512 : ℚ) : ℝ) + 1 / 100) < -(9 / 100000 : ℝ)
    have hl :=
      endpoint_fast_positive_margin (22183 / 512) (by norm_num only) (by norm_num only)
        endpoint_08_lower_check.1 endpoint_08_lower_check.2
    have hu :=
      endpoint_fast_negative_margin ((22183 / 512 : ℚ) + 1 / 100) (by norm_num only)
        (by norm_num only) endpoint_08_upper_check.1 endpoint_08_upper_check.2
    constructor
    · exact hl
    · simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hu
  case
    «8» =>
    change
      RiemannXi.normalizedZeta ((49157 / 1024 : ℚ) : ℝ) < -(9 / 100000 : ℝ) ∧
        (9 / 100000 : ℝ) < RiemannXi.normalizedZeta (((49157 / 1024 : ℚ) : ℝ) + 1 / 100)
    have hl :=
      endpoint_fast_negative_margin (49157 / 1024) (by norm_num only) (by norm_num only)
        endpoint_09_lower_check.1 endpoint_09_lower_check.2
    have hu :=
      endpoint_fast_positive_margin ((49157 / 1024 : ℚ) + 1 / 100) (by norm_num only)
        (by norm_num only) endpoint_09_upper_check.1 endpoint_09_upper_check.2
    constructor
    · exact hl
    · simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hu
  case
    «9» =>
    change
      (9 / 100000 : ℝ) < RiemannXi.normalizedZeta ((6371 / 128 : ℚ) : ℝ) ∧
        RiemannXi.normalizedZeta (((6371 / 128 : ℚ) : ℝ) + 1 / 100) < -(9 / 100000 : ℝ)
    have hl :=
      endpoint_fast_positive_margin (6371 / 128) (by norm_num only) (by norm_num only)
        endpoint_10_lower_check.1 endpoint_10_lower_check.2
    have hu :=
      endpoint_fast_negative_margin ((6371 / 128 : ℚ) + 1 / 100) (by norm_num only)
        (by norm_num only) endpoint_10_upper_check.1 endpoint_10_upper_check.2
    constructor
    · exact hl
    · simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hu
  case
    «10» =>
    change
      RiemannXi.normalizedZeta ((54241 / 1024 : ℚ) : ℝ) < -(9 / 100000 : ℝ) ∧
        (9 / 100000 : ℝ) < RiemannXi.normalizedZeta (((54241 / 1024 : ℚ) : ℝ) + 1 / 100)
    have hl :=
      endpoint_fast_negative_margin (54241 / 1024) (by norm_num only) (by norm_num only)
        endpoint_11_lower_check.1 endpoint_11_lower_check.2
    have hu :=
      endpoint_fast_positive_margin ((54241 / 1024 : ℚ) + 1 / 100) (by norm_num only)
        (by norm_num only) endpoint_11_upper_check.1 endpoint_11_upper_check.2
    constructor
    · exact hl
    · simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hu
  case
    «11» =>
    change
      (9 / 100000 : ℝ) < RiemannXi.normalizedZeta ((7225 / 128 : ℚ) : ℝ) ∧
        RiemannXi.normalizedZeta (((7225 / 128 : ℚ) : ℝ) + 1 / 100) < -(9 / 100000 : ℝ)
    have hl :=
      endpoint_fast_positive_margin (7225 / 128) (by norm_num only) (by norm_num only)
        endpoint_12_lower_check.1 endpoint_12_lower_check.2
    have hu :=
      endpoint_fast_negative_margin ((7225 / 128 : ℚ) + 1 / 100) (by norm_num only)
        (by norm_num only) endpoint_12_upper_check.1 endpoint_12_upper_check.2
    constructor
    · exact hl
    · simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hu
  case
    «12» =>
    change
      RiemannXi.normalizedZeta ((60771 / 1024 : ℚ) : ℝ) < -(9 / 100000 : ℝ) ∧
        (9 / 100000 : ℝ) < RiemannXi.normalizedZeta (((60771 / 1024 : ℚ) : ℝ) + 1 / 100)
    have hl :=
      endpoint_fast_negative_margin (60771 / 1024) (by norm_num only) (by norm_num only)
        endpoint_13_lower_check.1 endpoint_13_lower_check.2
    have hu :=
      endpoint_fast_positive_margin ((60771 / 1024 : ℚ) + 1 / 100) (by norm_num only)
        (by norm_num only) endpoint_13_upper_check.1 endpoint_13_upper_check.2
    constructor
    · exact hl
    · simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hu
  case
    «13» =>
    change
      (9 / 100000 : ℝ) < RiemannXi.normalizedZeta ((62291 / 1024 : ℚ) : ℝ) ∧
        RiemannXi.normalizedZeta (((62291 / 1024 : ℚ) : ℝ) + 1 / 100) < -(9 / 100000 : ℝ)
    have hl :=
      endpoint_fast_positive_margin (62291 / 1024) (by norm_num only) (by norm_num only)
        endpoint_14_lower_check.1 endpoint_14_lower_check.2
    have hu :=
      endpoint_fast_negative_margin ((62291 / 1024 : ℚ) + 1 / 100) (by norm_num only)
        (by norm_num only) endpoint_14_upper_check.1 endpoint_14_upper_check.2
    constructor
    · exact hl
    · simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hu
  case
    «14» =>
    change
      RiemannXi.normalizedZeta ((66675 / 1024 : ℚ) : ℝ) < -(9 / 100000 : ℝ) ∧
        (9 / 100000 : ℝ) < RiemannXi.normalizedZeta (((66675 / 1024 : ℚ) : ℝ) + 1 / 100)
    have hl :=
      endpoint_fast_negative_margin (66675 / 1024) (by norm_num only) (by norm_num only)
        endpoint_15_lower_check.1 endpoint_15_lower_check.2
    have hu :=
      endpoint_fast_positive_margin ((66675 / 1024 : ℚ) + 1 / 100) (by norm_num only)
        (by norm_num only) endpoint_15_upper_check.1 endpoint_15_upper_check.2
    constructor
    · exact hl
    · simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hu
  case
    «15» =>
    change
      (9 / 100000 : ℝ) < RiemannXi.normalizedZeta ((68689 / 1024 : ℚ) : ℝ) ∧
        RiemannXi.normalizedZeta (((68689 / 1024 : ℚ) : ℝ) + 1 / 100) < -(9 / 100000 : ℝ)
    have hl :=
      endpoint_fast_positive_margin (68689 / 1024) (by norm_num only) (by norm_num only)
        endpoint_16_lower_check.1 endpoint_16_lower_check.2
    have hu :=
      endpoint_fast_negative_margin ((68689 / 1024 : ℚ) + 1 / 100) (by norm_num only)
        (by norm_num only) endpoint_16_upper_check.1 endpoint_16_upper_check.2
    constructor
    · exact hl
    · simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hu
  case
    «16» =>
    change
      RiemannXi.normalizedZeta ((71215 / 1024 : ℚ) : ℝ) < -(9 / 100000 : ℝ) ∧
        (9 / 100000 : ℝ) < RiemannXi.normalizedZeta (((71215 / 1024 : ℚ) : ℝ) + 1 / 100)
    have hl :=
      endpoint_fast_negative_margin (71215 / 1024) (by norm_num only) (by norm_num only)
        endpoint_17_lower_check.1 endpoint_17_lower_check.2
    have hu :=
      endpoint_fast_positive_margin ((71215 / 1024 : ℚ) + 1 / 100) (by norm_num only)
        (by norm_num only) endpoint_17_upper_check.1 endpoint_17_upper_check.2
    constructor
    · exact hl
    · simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hu
  case
    «17» =>
    change
      (9 / 100000 : ℝ) < RiemannXi.normalizedZeta ((18449 / 256 : ℚ) : ℝ) ∧
        RiemannXi.normalizedZeta (((18449 / 256 : ℚ) : ℝ) + 1 / 100) < -(9 / 100000 : ℝ)
    have hl :=
      endpoint_fast_positive_margin (18449 / 256) (by norm_num only) (by norm_num only)
        endpoint_18_lower_check.1 endpoint_18_lower_check.2
    have hu :=
      endpoint_fast_negative_margin ((18449 / 256 : ℚ) + 1 / 100) (by norm_num only)
        (by norm_num only) endpoint_18_upper_check.1 endpoint_18_upper_check.2
    constructor
    · exact hl
    · simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hu
  case
    «18» =>
    change
      RiemannXi.normalizedZeta ((77521 / 1024 : ℚ) : ℝ) < -(9 / 100000 : ℝ) ∧
        (9 / 100000 : ℝ) < RiemannXi.normalizedZeta (((77521 / 1024 : ℚ) : ℝ) + 1 / 100)
    have hl :=
      endpoint_fast_negative_margin (77521 / 1024) (by norm_num only) (by norm_num only)
        endpoint_19_lower_check.1 endpoint_19_lower_check.2
    have hu :=
      endpoint_fast_positive_margin ((77521 / 1024 : ℚ) + 1 / 100) (by norm_num only)
        (by norm_num only) endpoint_19_upper_check.1 endpoint_19_upper_check.2
    constructor
    · exact hl
    · simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hu
  case
    «19» =>
    change
      (9 / 100000 : ℝ) < RiemannXi.normalizedZeta ((19749 / 256 : ℚ) : ℝ) ∧
        RiemannXi.normalizedZeta (((19749 / 256 : ℚ) : ℝ) + 1 / 100) < -(9 / 100000 : ℝ)
    have hl :=
      endpoint_fast_positive_margin (19749 / 256) (by norm_num only) (by norm_num only)
        endpoint_20_lower_check.1 endpoint_20_lower_check.2
    have hu :=
      endpoint_fast_negative_margin ((19749 / 256 : ℚ) + 1 / 100) (by norm_num only)
        (by norm_num only) endpoint_20_upper_check.1 endpoint_20_upper_check.2
    constructor
    · exact hl
    · simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hu
  case
    «20» =>
    change
      RiemannXi.normalizedZeta ((81241 / 1024 : ℚ) : ℝ) < -(9 / 100000 : ℝ) ∧
        (9 / 100000 : ℝ) < RiemannXi.normalizedZeta (((81241 / 1024 : ℚ) : ℝ) + 1 / 100)
    have hl :=
      endpoint_fast_negative_margin (81241 / 1024) (by norm_num only) (by norm_num only)
        endpoint_21_lower_check.1 endpoint_21_lower_check.2
    have hu :=
      endpoint_fast_positive_margin ((81241 / 1024 : ℚ) + 1 / 100) (by norm_num only)
        (by norm_num only) endpoint_21_upper_check.1 endpoint_21_upper_check.2
    constructor
    · exact hl
    · simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hu
  case
    «21» =>
    change
      (9 / 100000 : ℝ) < RiemannXi.normalizedZeta ((21225 / 256 : ℚ) : ℝ) ∧
        RiemannXi.normalizedZeta (((21225 / 256 : ℚ) : ℝ) + 1 / 100) < -(9 / 100000 : ℝ)
    have hl :=
      endpoint_fast_positive_margin (21225 / 256) (by norm_num only) (by norm_num only)
        endpoint_22_lower_check.1 endpoint_22_lower_check.2
    have hu :=
      endpoint_fast_negative_margin ((21225 / 256 : ℚ) + 1 / 100) (by norm_num only)
        (by norm_num only) endpoint_22_upper_check.1 endpoint_22_upper_check.2
    constructor
    · exact hl
    · simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hu
  case
    «22» =>
    change
      RiemannXi.normalizedZeta ((86769 / 1024 : ℚ) : ℝ) < -(9 / 100000 : ℝ) ∧
        (9 / 100000 : ℝ) < RiemannXi.normalizedZeta (((86769 / 1024 : ℚ) : ℝ) + 1 / 100)
    have hl :=
      endpoint_fast_negative_margin (86769 / 1024) (by norm_num only) (by norm_num only)
        endpoint_23_lower_check.1 endpoint_23_lower_check.2
    have hu :=
      endpoint_fast_positive_margin ((86769 / 1024 : ℚ) + 1 / 100) (by norm_num only)
        (by norm_num only) endpoint_23_upper_check.1 endpoint_23_upper_check.2
    constructor
    · exact hl
    · simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hu
  case
    «23» =>
    change
      (9 / 100000 : ℝ) < RiemannXi.normalizedZeta ((89523 / 1024 : ℚ) : ℝ) ∧
        RiemannXi.normalizedZeta (((89523 / 1024 : ℚ) : ℝ) + 1 / 100) < -(9 / 100000 : ℝ)
    have hl :=
      endpoint_fast_positive_margin (89523 / 1024) (by norm_num only) (by norm_num only)
        endpoint_24_lower_check.1 endpoint_24_lower_check.2
    have hu :=
      endpoint_fast_negative_margin ((89523 / 1024 : ℚ) + 1 / 100) (by norm_num only)
        (by norm_num only) endpoint_24_upper_check.1 endpoint_24_upper_check.2
    constructor
    · exact hl
    · simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hu
  case
    «24» =>
    change
      RiemannXi.normalizedZeta ((22735 / 256 : ℚ) : ℝ) < -(9 / 100000 : ℝ) ∧
        (9 / 100000 : ℝ) < RiemannXi.normalizedZeta (((22735 / 256 : ℚ) : ℝ) + 1 / 100)
    have hl :=
      endpoint_fast_negative_margin (22735 / 256) (by norm_num only) (by norm_num only)
        endpoint_25_lower_check.1 endpoint_25_lower_check.2
    have hu :=
      endpoint_fast_positive_margin ((22735 / 256 : ℚ) + 1 / 100) (by norm_num only)
        (by norm_num only) endpoint_25_upper_check.1 endpoint_25_upper_check.2
    constructor
    · exact hl
    · simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hu
  case
    «25» =>
    change
      (9 / 100000 : ℝ) < RiemannXi.normalizedZeta ((94711 / 1024 : ℚ) : ℝ) ∧
        RiemannXi.normalizedZeta (((94711 / 1024 : ℚ) : ℝ) + 1 / 100) < -(9 / 100000 : ℝ)
    have hl :=
      endpoint_fast_positive_margin (94711 / 1024) (by norm_num only) (by norm_num only)
        endpoint_26_lower_check.1 endpoint_26_lower_check.2
    have hu :=
      endpoint_fast_negative_margin ((94711 / 1024 : ℚ) + 1 / 100) (by norm_num only)
        (by norm_num only) endpoint_26_upper_check.1 endpoint_26_upper_check.2
    constructor
    · exact hl
    · simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hu
  case
    «26» =>
    change
      RiemannXi.normalizedZeta ((48461 / 512 : ℚ) : ℝ) < -(9 / 100000 : ℝ) ∧
        (9 / 100000 : ℝ) < RiemannXi.normalizedZeta (((48461 / 512 : ℚ) : ℝ) + 1 / 100)
    have hl :=
      endpoint_fast_negative_margin (48461 / 512) (by norm_num only) (by norm_num only)
        endpoint_27_lower_check.1 endpoint_27_lower_check.2
    have hu :=
      endpoint_fast_positive_margin ((48461 / 512 : ℚ) + 1 / 100) (by norm_num only)
        (by norm_num only) endpoint_27_upper_check.1 endpoint_27_upper_check.2
    constructor
    · exact hl
    · simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hu
  case
    «27» =>
    change
      (9 / 100000 : ℝ) < RiemannXi.normalizedZeta ((98171 / 1024 : ℚ) : ℝ) ∧
        RiemannXi.normalizedZeta (((98171 / 1024 : ℚ) : ℝ) + 1 / 100) < -(9 / 100000 : ℝ)
    have hl :=
      endpoint_fast_positive_margin (98171 / 1024) (by norm_num only) (by norm_num only)
        endpoint_28_lower_check.1 endpoint_28_lower_check.2
    have hu :=
      endpoint_fast_negative_margin ((98171 / 1024 : ℚ) + 1 / 100) (by norm_num only)
        (by norm_num only) endpoint_28_upper_check.1 endpoint_28_upper_check.2
    constructor
    · exact hl
    · simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hu
  case
    «28» =>
    change
      RiemannXi.normalizedZeta ((101203 / 1024 : ℚ) : ℝ) < -(9 / 100000 : ℝ) ∧
        (9 / 100000 : ℝ) < RiemannXi.normalizedZeta (((101203 / 1024 : ℚ) : ℝ) + 1 / 100)
    have hl :=
      endpoint_fast_negative_margin (101203 / 1024) (by norm_num only) (by norm_num only)
        endpoint_29_lower_check.1 endpoint_29_lower_check.2
    have hu :=
      endpoint_fast_positive_margin ((101203 / 1024 : ℚ) + 1 / 100) (by norm_num only)
        (by norm_num only) endpoint_29_upper_check.1 endpoint_29_upper_check.2
    constructor
    · exact hl
    · simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hu

/-- There are 29 strictly increasing positive critical-line zeta zeros through height 100,
each in its internally certified candidate interval. The endpoint sign changes and continuity
provide these zeros without assuming RH. -/
theorem low_zero_100_exists :
    ∃ g : Fin 29 → ℝ,
      StrictMono g ∧
        (∀ i, 0 < g i) ∧
        (∀ i, g i ≤ 100) ∧
        (∀ i, riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 0) ∧
        LowZero100LowerBounds g ∧ LowZero100UpperBounds g := by
  exact low_zero_100_of_signs low_zero_100_sign_changes

/-- Under RH, the multiplicity-weighted number of nontrivial zeta zeros through height 100
is exactly 58. The certified 29 positive zeros and the independently proved upper bound
force equality. -/
theorem count_100_eq_58_of_RH (hRH : RiemannHypothesis) : zeroCount 100 = 58 := by
  exact count_100_eq_58_of_signs hRH low_zero_100_sign_changes

/-- Under RH, the 29 internally certified positive critical-line zeros through height 100
exhaust the positive zero ledger and each has multiplicity one. The independent count bound
and endpoint sign proofs supply all hypotheses. -/
theorem low_zeros_complete_of_RH (hRH : RiemannHypothesis) :
    ∃ g : Fin 29 → ℝ,
      StrictMono g ∧
        (∀ i, 0 < g i) ∧
        (∀ i, g i ≤ 100) ∧
        (∀ i, riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 0) ∧
        ((zerosUpTo 100).filter (fun ρ ↦ 0 < ρ.im)) ⊆
          Finset.univ.image (fun i ↦ ((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) ∧
        ∀ i, riemannZetaZeroMultiplicity (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 1 := by
  exact low_zeros_complete_of_signs hRH low_zero_100_sign_changes

/-- Under RH, the normalized Chebyshev ψ error satisfies the Lee–Nosal logarithmic bound
for every `x ≥ 101`. The low-zero signs and height-100 count bound are proved internally. -/
theorem psi_lee_nosal_of_RH (hRH : RiemannHypothesis) {x : ℝ} (hx : 101 ≤ x) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ leeNosalPsiLog (Real.log x) := by
  exact psi_lee_nosal_of_signs_RH hRH low_zero_100_sign_changes hx

/-- Under RH, the normalized Chebyshev ψ error is bounded by the complete piecewise
envelope for every `x ≥ 101`. The proof supplies the certified endpoint signs and the
independent height-100 count bound to the existing interval estimates. -/
theorem psi_piecewise_of_RH (hRH : RiemannHypothesis) {x : ℝ} (hx : 101 ≤ x) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ psiPiecewiseEnvelope x := by
  exact psi_piecewise_of_signs hRH low_zero_100_sign_changes (zero_count_100_le_58_of_RH hRH) hx

/-- Under RH, for positive `x` with `log x ≥ 97/5`, the normalized Chebyshev ψ error is at
most the integrated envelope, which is at most the Lee–Nosal expression minus `1/200`.
The low-zero sign and count inputs are supplied by internal proofs. -/
theorem psi_integrated_of_RH (hRH : RiemannHypothesis) {x : ℝ} (hx : 0 < x)
    (hL : (97 / 5 : ℝ) ≤ Real.log x) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ integratedPsiEnvelope (Real.log x) ∧
      integratedPsiEnvelope (Real.log x) ≤ leeNosalPsiLog (Real.log x) - 1 / 200 := by
  exact psi_integrated_of_signs hRH low_zero_100_sign_changes (zero_count_100_le_58_of_RH hRH) hx hL

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
