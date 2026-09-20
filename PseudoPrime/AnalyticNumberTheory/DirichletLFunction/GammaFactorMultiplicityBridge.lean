/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.HadamardMultiplicityFactorization
import Mathlib.Analysis.Meromorphic.Complex

/-!
# The ordinary/completed zero-multiplicity bridge for Dirichlet L-functions

For a nontrivial character at a positive level, at an ordinary `L`-zero `ρ` with `gammaFactor χ ρ ≠
0`, the completed `L`-function has a zero of
the *same* analytic order at `ρ`: since `completedLFunction χ` and `LFunction χ` are both entire
(globally differentiable) and `LFunction χ = completedLFunction χ / gammaFactor χ` holds as an
exact functional identity (mathlib), the only missing ingredient is `AnalyticAt ℂ (gammaFactor χ)
ρ`. This is obtained from `Complex.Gamma`'s global meromorphicity (`Meromorphic.Gamma`, mathlib)
combined with pointwise continuity at the pole-avoiding argument (`MeromorphicAt.analyticAt`),
avoiding any need to prove the (nonpositive-integer) pole locus is closed/discrete by hand.

This is fully generic Dirichlet-L-function theory, independent of any particular contour or
explicit-formula construction.
-/

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-! ### Analyticity of `Complex.Gamma`/`Complex.Gammaℝ`/`gammaFactor` at nonzero points -/

/--
Input/assumptions: `w : ℂ` with `Complex.Gamma w ≠ 0`.
Conclusion: `Complex.Gamma` is analytic at `w`.
Content: `Complex.Gamma_eq_zero_iff` converts the nonzero value into pole-avoidance
(`∀ m, w ≠ -m`), giving `DifferentiableAt` (`Complex.differentiableAt_Gamma`) hence `ContinuousAt`;
combined with global meromorphicity (`Meromorphic.Gamma`), `MeromorphicAt.analyticAt` upgrades
`ContinuousAt` to `AnalyticAt`.
-/
theorem analyticAt_Gamma_of_ne_zero {w : ℂ} (hw : Complex.Gamma w ≠ 0) :
    AnalyticAt ℂ Complex.Gamma w := by
  have hs : ∀ m : ℕ, w ≠ -(m : ℂ) := by
    intro m hm
    exact hw ((Complex.Gamma_eq_zero_iff w).mpr ⟨m, hm⟩)
  exact (Meromorphic.Gamma w).analyticAt (Complex.differentiableAt_Gamma w hs).continuousAt

/--
Input/assumptions: `s : ℂ` with `Complex.Gammaℝ s ≠ 0`.
Conclusion: `Complex.Gammaℝ` is analytic at `s`.
Content: `Gammaℝ = π^(-·/2) * Gamma(·/2)`; the first factor is entire (nonzero base, affine
exponent), and `Gamma (s/2) ≠ 0` (from `hs`, since the first factor is always nonzero) gives
`AnalyticAt ℂ Complex.Gamma (s/2)` (`analyticAt_Gamma_of_ne_zero`), composed with the entire affine
map `z ↦ z/2`.
-/
theorem analyticAt_Gammaℝ_of_ne_zero {s : ℂ} (hs : Complex.Gammaℝ s ≠ 0) :
    AnalyticAt ℂ Complex.Gammaℝ s := by
  change AnalyticAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2)) s
  have hGne : Complex.Gamma (s / 2) ≠ 0 := by
    intro h
    apply hs
    change (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) = 0
    rw [h, mul_zero]
  have hpiDiff : Differentiable ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) := fun z =>
    (differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hpiAnalytic : AnalyticAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s := hpiDiff.analyticAt s
  have hGammaAnalytic : AnalyticAt ℂ (fun z : ℂ => Complex.Gamma (z / 2)) s := by
    have hcomp : AnalyticAt ℂ (fun z : ℂ => z / 2) s := by fun_prop
    exact
      AnalyticAt.comp (g := Complex.Gamma) (f := fun z : ℂ => z / 2)
        (analyticAt_Gamma_of_ne_zero hGne) hcomp
  exact hpiAnalytic.mul hGammaAnalytic

/--
Input/assumptions: a character `χ`, `ρ : ℂ` with `gammaFactor χ ρ ≠ 0`.
Conclusion: `gammaFactor χ` is analytic at `ρ`.
Content: parity dispatch — even: `gammaFactor χ = Gammaℝ` directly; odd: `gammaFactor χ ρ =
Gammaℝ (ρ + 1)`, composed with the entire affine shift `z ↦ z + 1`.
-/
theorem analyticAt_gammaFactor_of_ne_zero {N : ℕ} {χ : DirichletCharacter ℂ N} {ρ : ℂ}
    (hΓ : DirichletCharacter.gammaFactor χ ρ ≠ 0) :
    AnalyticAt ℂ (DirichletCharacter.gammaFactor χ) ρ := by
  rcases χ.even_or_odd with heven | hodd
  · have heq : DirichletCharacter.gammaFactor χ = Complex.Gammaℝ := by
      funext z; exact heven.gammaFactor_def z
    rw [heq]
    rw [heq] at hΓ
    exact analyticAt_Gammaℝ_of_ne_zero hΓ
  · have heq : DirichletCharacter.gammaFactor χ = fun z => Complex.Gammaℝ (z + 1) := by
      funext z; exact hodd.gammaFactor_def z
    rw [heq]
    rw [heq] at hΓ
    have hcomp : AnalyticAt ℂ (fun z : ℂ => z + 1) ρ := by fun_prop
    exact
      AnalyticAt.comp (g := Complex.Gammaℝ) (f := fun z : ℂ => z + 1)
        (analyticAt_Gammaℝ_of_ne_zero hΓ) hcomp

/-! ### The multiplicity bridge -/

/--
Input/assumptions: `N ≥ 1`, `χ ≠ 1`, `ρ : ℂ` with `gammaFactor χ ρ ≠ 0`.
Conclusion: `analyticOrderAt (LFunction χ) ρ = analyticOrderAt (completedLFunction χ) ρ`.
Content: `LFunction χ = fun z => completedLFunction χ z / gammaFactor χ z` holds as an exact
functional identity (`DirichletLFunction.dirichletLFunction_eq_completed_div_gammaFactor`, valid at
every point since
`N ≠ 1`). Writing this as `completedLFunction χ * (gammaFactor χ)⁻¹`, `analyticOrderAt_mul` (both
factors `AnalyticAt` — `completedLFunction χ` globally, `(gammaFactor χ)⁻¹` via `AnalyticAt.inv`
fed by `analyticAt_gammaFactor_of_ne_zero`) splits the order into a sum; the inverse factor has
order `0` (`AnalyticAt.analyticOrderAt_eq_zero`, since `(gammaFactor χ ρ)⁻¹ ≠ 0`).
-/
theorem analyticOrderAt_LFunction_eq_completedLFunction_of_gamma_ne_zero {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hne : χ ≠ 1) {ρ : ℂ}
    (hΓ : DirichletCharacter.gammaFactor χ ρ ≠ 0) :
    analyticOrderAt (DirichletCharacter.LFunction χ) ρ =
      analyticOrderAt (DirichletCharacter.completedLFunction χ) ρ := by
  have hFanalytic : AnalyticAt ℂ (DirichletCharacter.completedLFunction χ) ρ :=
    (DirichletCharacter.differentiable_completedLFunction hne).analyticAt ρ
  have hΓanalytic : AnalyticAt ℂ (DirichletCharacter.gammaFactor χ) ρ :=
    analyticAt_gammaFactor_of_ne_zero hΓ
  have hΓinvAnalytic : AnalyticAt ℂ (fun z => (DirichletCharacter.gammaFactor χ z)⁻¹) ρ :=
    hΓanalytic.inv hΓ
  have hΓinvOrder : analyticOrderAt (fun z => (DirichletCharacter.gammaFactor χ z)⁻¹) ρ = 0 :=
    hΓinvAnalytic.analyticOrderAt_eq_zero.mpr (inv_ne_zero hΓ)
  have hLeq :
    DirichletCharacter.LFunction χ = fun z =>
      DirichletCharacter.completedLFunction χ z * (DirichletCharacter.gammaFactor χ z)⁻¹ := by
    funext z
    rw [dirichletLFunction_eq_completed_div_gammaFactor χ z
        (Or.inr (dirichletCharacter_level_ne_one_of_ne_one hne)),
      div_eq_mul_inv]
  have hmul :
    analyticOrderAt
        (fun z =>
          DirichletCharacter.completedLFunction χ z * (DirichletCharacter.gammaFactor χ z)⁻¹)
        ρ =
      analyticOrderAt (DirichletCharacter.completedLFunction χ) ρ +
        analyticOrderAt (fun z => (DirichletCharacter.gammaFactor χ z)⁻¹) ρ :=
    analyticOrderAt_mul hFanalytic hΓinvAnalytic
  rw [hLeq, hmul, hΓinvOrder, add_zero]

/--
Input/assumptions: `N ≥ 1`, `χ ≠ 1`, `ρ : ℂ` with `gammaFactor χ ρ ≠ 0`.
Conclusion: `dirichletLFunctionZeroMultiplicity χ ρ = divisor (completedLFunction χ) univ ρ`
(as integers).
Content: `analyticOrderAt_LFunction_eq_completedLFunction_of_gamma_ne_zero` gives equal `ℕ∞`-orders;
`dirichletLFunctionZeroMultiplicity` is the `.toNat` of `L`'s order, while `MeromorphicOn.divisor`
(via `AnalyticOnNhd.divisor_apply`, `completedLFunction χ` being entire) is the `ℤ`-cast `.untop₀`
of the same (now equal) order — both reductions agree on every `ℕ∞` value, `⊤` or finite.
-/
theorem dirichletLFunctionZeroMultiplicity_eq_divisor_completedLFunction_of_gamma_ne_zero {N : ℕ}
    [NeZero N] {χ : DirichletCharacter ℂ N} (hne : χ ≠ 1) {ρ : ℂ}
    (hΓ : DirichletCharacter.gammaFactor χ ρ ≠ 0) :
    (dirichletLFunctionZeroMultiplicity χ ρ : ℤ) =
      MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ := by
  have horder := analyticOrderAt_LFunction_eq_completedLFunction_of_gamma_ne_zero hne hΓ
  have hAnU : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) Set.univ := fun z _ =>
    (DirichletCharacter.differentiable_completedLFunction hne).analyticAt z
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hAnU (Set.mem_univ ρ), ← horder,
    dirichletLFunctionZeroMultiplicity, analyticOrderNatAt]
  cases analyticOrderAt (DirichletCharacter.LFunction χ) ρ with
  | top => simp only [ENat.toNat_top, CharP.cast_eq_zero, ENat.map_top, WithTop.untop₀_top]
  | coe n =>
    simp only [ENat.toNat_natCast, ENat.map_natCast, WithTop.coe_natCast, WithTop.untop₀_natCast]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
