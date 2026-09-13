/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.NumberTheory.MulChar.Basic
import PseudoPrime.AnalyticNumberTheory.GRH.Definition
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.QuadraticFunctionalEquation
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.HadamardLimit
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveFunctionalEquation
import PseudoPrime.AnalyticNumberTheory.RiemannXi.HadamardLimit

/-!
# Quadratic specializations of functional-equation and zero-mass estimates

Self-duality `χ⁻¹ = χ` gives reflection identities for a primitive quadratic character.
Under GRH these feed zero-mass identities, weighted zero-sum bounds, truncated genus-sum
estimates, and endpoint logarithmic-derivative formulas.
General primitive-character counterparts are in `PrimitiveFunctionalEquation`;
inversion and primitivity algebra is in `PrimitiveCharacterInv`. Quadraticity is
an assumption of this route, not an assertion that the general counterparts fail.
-/

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/--
Input/assumptions: a primitive quadratic complex Dirichlet character and a completed zero at a
reflected point.
Conclusion: the corresponding point is a completed zero of the same character (not its inverse).
Content: specialize `dirichletCompletedLFunction_inv_zero_of_one_sub_zero`
using `MulChar.IsQuadratic.inv`.
-/
theorem completedLFunction_zero_of_one_sub_zero_isQuadratic {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hquad : χ.IsQuadratic) (s : ℂ)
    (hzero : DirichletCharacter.completedLFunction χ (1 - s) = 0) :
    DirichletCharacter.completedLFunction χ s = 0 := by
  have h :=
    dirichletCompletedLFunction_inv_zero_of_one_sub_zero
      hprimitive s hzero
  rwa [hquad.inv] at h

/--
Input/assumptions: GRH, a primitive nontrivial quadratic complex Dirichlet character, and a
completed-`L` zero.
Conclusion: that zero has real part `1 / 2`.
Content: a zero of the completed function with `Re s ≥ 1` forces a zero of the (Euler-series)
`L`-function there via `L = F / gammaFactor` (valid unconditionally since `0 / x = 0`),
contradicting mathlib's nonvanishing for `Re s ≥ 1`; this rules out `Re s ≥ 1`, and self-duality
reflects any zero with `Re s ≤ 0` to one with `Re (1 - s) ≥ 1`, ruling out `Re s ≤ 0` too. What
remains, `0 < Re s < 1`, is exactly GRH's hypothesis window.
-/
theorem completedLFunction_zero_re_eq_half_of_grh_quadratic {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hquad : χ.IsQuadratic) {ρ : ℂ}
    (hzero : DirichletCharacter.completedLFunction χ ρ = 0) : ρ.re = (1 : ℝ) / 2 := by
  have hstep1 : ∀ s : ℂ, DirichletCharacter.completedLFunction χ s = 0 → 1 ≤ s.re → False := by
    intro s hs0 hs1
    have hsne0 : s ≠ 0 := by
      intro h; rw [h, Complex.zero_re] at hs1; linarith
    have heq :=
      dirichletLFunction_eq_completed_div_gammaFactor
        χ s (Or.inl hsne0)
    rw [hs0, zero_div] at heq
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hne) hs1 heq
  have hlt1 : ρ.re < 1 := by
    by_contra h
    push Not at h
    exact hstep1 ρ hzero h
  have hgt0 : 0 < ρ.re := by
    by_contra h
    push Not at h
    set s := 1 - ρ with hs_def
    have hs_eq : (1 : ℂ) - s = ρ := by
      rw [hs_def]; ring
    have hcompleted_one_sub : DirichletCharacter.completedLFunction χ (1 - s) = 0 := by
      rw [hs_eq]
      exact hzero
    have hzero_s : DirichletCharacter.completedLFunction χ s = 0 :=
      completedLFunction_zero_of_one_sub_zero_isQuadratic hprimitive hquad s hcompleted_one_sub
    have hsre : 1 ≤ s.re := by
      have hsre_eq : s.re = 1 - ρ.re := by
        rw [hs_def]
        simp only [Complex.sub_re, Complex.one_re]
      rw [hsre_eq]
      linarith
    exact hstep1 s hzero_s hsre
  have hρne0 : ρ ≠ 0 := by
    intro h
    rw [h] at hgt0
    simp only [Complex.zero_re, lt_self_iff_false] at hgt0
  have hL0 : DirichletCharacter.LFunction χ ρ = 0 := by
    have heq :=
      dirichletLFunction_eq_completed_div_gammaFactor
        χ ρ (Or.inl hρne0)
    rw [hzero, zero_div] at heq
    exact heq
  exact hGRH.zero_re_eq_half N χ hprimitive ρ hL0 hgt0

/--
Input/assumptions: GRH, `2 ≤ N`, and a primitive nontrivial quadratic complex Dirichlet character.
Conclusion: half the real part of the global Hadamard genus-one `tsum` equals the classical
zero-mass sum `Σ' ρ, m_ρ Re(1 / ρ)`.
Content: `Complex.re_tsum` moves `.re` inside the summability; termwise, either the divisor
multiplicity is zero (both sides vanish) or GRH forces `Re ρ = 1 / 2` and
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.genusOneTerm_re_eq_of_re_eq_half` applies.
-/
theorem dirichletCompletedLFunctionQuadraticZeroMass_eq_tsum_re_inv {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) :
    (1 / 2 : ℝ) *
        (∑' ρ : ℂ,
            ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) *
              (1 / (1 - ρ) + 1 / ρ)).re =
      ∑' ρ : ℂ,
        ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) *
          (1 / ρ).re := by
  have hsummable :=
    summable_completedLFunctionGenusOneTerm_one
      hN2 hprimitive hne hinv
  have hpt :
    ∀ ρ : ℂ,
      (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) *
            (1 / (1 - ρ) + 1 / ρ)).re =
        2 *
          (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) *
            (1 / ρ).re) := by
    intro ρ
    set D := MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ with hD_def
    by_cases hD0 : D = 0
    · simp only [hD0, Int.cast_zero, one_div, zero_mul, Complex.zero_re, Complex.inv_re, mul_zero]
    · have hzero : DirichletCharacter.completedLFunction χ ρ = 0 :=
        dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero
          hne hD0
      have hre_half : ρ.re = (1 : ℝ) / 2 :=
        completedLFunction_zero_re_eq_half_of_grh_quadratic hGRH hprimitive hne hquad hzero
      have hterm :=
        genusOneTerm_re_eq_of_re_eq_half
          hre_half
      have hcast : ((D : ℤ) : ℂ) = (((D : ℤ) : ℝ) : ℂ) := by
        push_cast; ring
      rw [hcast, Complex.re_ofReal_mul, hterm]
      ring
  rw [Complex.re_tsum hsummable, tsum_congr hpt, tsum_mul_left]
  ring

/--
Input/assumptions: a primitive nontrivial quadratic complex Dirichlet character, and a point `s`
where the completed `L`-function doesn't vanish.
Conclusion: the self-dual functional equation's log-derivative at the reflection pair `(s, 1 - s)`:
`-logDeriv F (1 - s) = Complex.log N + logDeriv F s`.
Content: specializes `DirichletLFunction.completedLFunction_logDeriv_functionalEquation_at` via
`hquad.inv :
χ⁻¹ = χ`, which collapses the pair system to a single function.
-/
theorem completedLFunction_logDeriv_functionalEquation_isQuadratic_at {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hquad : χ.IsQuadratic)
    {s : ℂ} (hFs : DirichletCharacter.completedLFunction χ s ≠ 0) :
    -logDeriv (DirichletCharacter.completedLFunction χ) (1 - s) =
      Complex.log N + logDeriv (DirichletCharacter.completedLFunction χ) s := by
  have hFs' : DirichletCharacter.completedLFunction χ⁻¹ s ≠ 0 := by rwa [hquad.inv]
  have h :=
    completedLFunction_logDeriv_functionalEquation_at
      hprimitive hne (s := s) hFs'
  rwa [hquad.inv] at h

/--
Input/assumptions: a primitive nontrivial quadratic complex Dirichlet character.
Conclusion: the self-dual functional equation's log-derivative at the reflection point `s = 0`:
`-logDeriv F 1 = Complex.log N + logDeriv F 0`.
Content: `completedLFunction_logDeriv_functionalEquation_isQuadratic_at` at `s := 0`, using
`DirichletLFunction.dirichletCompletedLFunction_zero_ne_zero_of_primitive` for the nonvanishing
hypothesis and
`sub_zero` to simplify `1 - 0` to `1`.
Role: supplies the functional-equation input to the linear system for the real part
of `logDeriv F 0` and the zero mass.
-/
theorem completedLFunction_logDeriv_functionalEquation_isQuadratic {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1)
    (hquad : χ.IsQuadratic) :
    -logDeriv (DirichletCharacter.completedLFunction χ) 1 =
      Complex.log N + logDeriv (DirichletCharacter.completedLFunction χ) 0 := by
  have hF0ne : DirichletCharacter.completedLFunction χ 0 ≠ 0 :=
    dirichletCompletedLFunction_zero_ne_zero_of_primitive
      hprimitive hne
  have h := completedLFunction_logDeriv_functionalEquation_isQuadratic_at hprimitive hne hquad hF0ne
  simpa only [sub_zero] using h

/--
Input/assumptions: GRH, `2 ≤ N`, and a primitive nontrivial quadratic complex Dirichlet character.
Conclusion: `Re (logDeriv F 0) + (1/2) * log N = -Z_χ`, where `Z_χ` is the real zero mass
`Σ' ρ, m_ρ Re(1/ρ)`.
Content: take real parts of the centered identity (`L₁ - L₀ = 2 Z_χ`) and the
functional-equation log-derivative (`L₁ + L₀ = -log N`), and solve the resulting `2 × 2` linear
system by `linarith`.
Role: isolates `Re (logDeriv F 0)` in terms of the zero mass — the remaining link to any
particular normalization constant is left to the caller.
-/
theorem completedLFunction_logDeriv_zero_re_add_half_log_eq_neg_zeroMass_isQuadratic {N : ℕ}
    [NeZero N] (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) :
    (logDeriv (DirichletCharacter.completedLFunction χ) 0).re + (1 / 2) * Real.log N =
      -(∑' ρ : ℂ,
          ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) *
            (1 / ρ).re) := by
  have hH9g :=
    completedLFunction_centeredLogDeriv_one_eq_tsum
      hN2 hprimitive hne hinv
  have hH10c :=
    dirichletCompletedLFunctionQuadraticZeroMass_eq_tsum_re_inv hN2 hGRH hprimitive hne hinv hquad
  have hH10d := completedLFunction_logDeriv_functionalEquation_isQuadratic hprimitive hne hquad
  have hlogNre : (Complex.log (N : ℂ)).re = Real.log N := by
    rw [show ((N : ℂ)) = ((N : ℝ) : ℂ) from by
        push_cast; ring]
    exact Complex.log_ofReal_re _
  have hre9g :
    (logDeriv (DirichletCharacter.completedLFunction χ) 1).re -
        (logDeriv (DirichletCharacter.completedLFunction χ) 0).re =
      (∑' ρ : ℂ,
          ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) *
            (1 / (1 - ρ) + 1 / ρ)).re := by
    have := congrArg Complex.re hH9g
    simpa only [one_div, Complex.sub_re] using this
  have hre10d :
    -(logDeriv (DirichletCharacter.completedLFunction χ) 1).re =
      Real.log N + (logDeriv (DirichletCharacter.completedLFunction χ) 0).re := by
    have := congrArg Complex.re hH10d
    simpa only [Complex.neg_re, Complex.add_re, hlogNre] using this
  linarith [hre9g, hre10d, hH10c]

/--
Input/assumptions: GRH, `2 ≤ N`, and a primitive nontrivial quadratic complex Dirichlet character.
Conclusion: `Re B(χ) = -Z_χ`, where `Z_χ` is the real zero mass `Σ' ρ, m_ρ Re(1/ρ)`.
Content: a primitive character has `conductor = N` (unfolds `IsPrimitive`), reducing directly to
`completedLFunction_logDeriv_zero_re_add_half_log_eq_neg_zeroMass_isQuadratic`.
Role: the identification of `B(χ)` with the real zero mass.
-/
theorem primitiveBRe_eq_neg_zeroMass_isQuadratic {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) :
    primitiveBRe χ =
      -(∑' ρ : ℂ,
          ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) *
            (1 / ρ).re) := by
  rw [primitiveBRe,
    (hprimitive : χ.conductor = N)]
  exact
    completedLFunction_logDeriv_zero_re_add_half_log_eq_neg_zeroMass_isQuadratic hN2 hGRH hprimitive
      hne hinv hquad

/--
Input/assumptions: GRH and a primitive nontrivial quadratic complex Dirichlet character.
Conclusion: the real zero mass `Z_χ = Σ' ρ, m_ρ Re(1/ρ)` is nonnegative.
Content: on the critical line `Re ρ = 1/2 > 0`, so `Re(1/ρ) = Re ρ / normSq ρ ≥ 0`; divisor
multiplicities are nonnegative since `completedLFunction` is entire
(`MeromorphicOn.AnalyticOnNhd.divisor_nonneg`). Neither the summability hypotheses `2 ≤ N`/`χ⁻¹≠1`
nor `tsum`'s convergence are needed: `tsum_nonneg` only needs pointwise nonnegativity.
Role: turns `Re B(χ) = -Z_χ` into the absolute-value form `|Re B(χ)| = Z_χ`.
-/
theorem primitiveZeroMass_nonneg_of_grh_quadratic {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hquad : χ.IsQuadratic) :
    0 ≤
      ∑' ρ : ℂ,
        ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) *
          (1 / ρ).re := by
  have hdiff := DirichletCharacter.differentiable_completedLFunction hne
  have hanalytic : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) Set.univ := fun z _ =>
    hdiff.analyticAt z
  apply tsum_nonneg
  intro ρ
  set D := MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ with hD_def
  by_cases hD0 : D = 0
  · simp only [hD0, Int.cast_zero, one_div, Complex.inv_re, zero_mul, Std.le_refl]
  · have hDnonneg : (0 : ℝ) ≤ (D : ℝ) := by
      exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hanalytic ρ
    have hzero : DirichletCharacter.completedLFunction χ ρ = 0 :=
      dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero
        hne hD0
    have hre_half : ρ.re = (1 : ℝ) / 2 :=
      completedLFunction_zero_re_eq_half_of_grh_quadratic hGRH hprimitive hne hquad hzero
    have hinv_re_pos : 0 ≤ (1 / ρ).re := by
      rw [one_div, Complex.inv_re, hre_half]
      exact div_nonneg (by norm_num only) (Complex.normSq_nonneg ρ)
    exact mul_nonneg hDnonneg hinv_re_pos

/--
Input/assumptions: GRH, `2 ≤ N`, and a primitive nontrivial quadratic complex Dirichlet character.
Conclusion: `|Re B(χ)| = Z_χ`.
Content: combines `primitiveBRe_eq_neg_zeroMass_isQuadratic` with the sign information from
`primitiveZeroMass_nonneg_of_grh_quadratic`.
Role: the final closed form for `|Re B(χ)|` in terms of the real zero mass.
-/
theorem abs_primitiveBRe_eq_zeroMass_isQuadratic {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) :
    |primitiveBRe χ| =
      ∑' ρ : ℂ,
        ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) *
          (1 / ρ).re := by
  rw [primitiveBRe_eq_neg_zeroMass_isQuadratic hN2 hGRH hprimitive hne hinv hquad, abs_neg,
    abs_of_nonneg (primitiveZeroMass_nonneg_of_grh_quadratic hGRH hprimitive hne hquad)]

/--
Input/assumptions: GRH, `2 ≤ N`, and a primitive nontrivial quadratic complex Dirichlet character.
Conclusion: the inverse-square zero mass `Σ' ρ, m_ρ / |ρ|²` equals `2 * |Re B(χ)|`.
Content: on the critical line `Re(1/ρ) = Re ρ / normSq ρ = 1 / (2 * normSq ρ)`, so
`abs_primitiveBRe_eq_zeroMass_isQuadratic`'s zero mass identity `Σ' ρ, m_ρ Re(1/ρ) = |Re B(χ)|`
rescales termwise into this inverse-square form; no new summability or Jensen-type estimate is
needed beyond that identity's own.
Role: a common zero estimate feeding both reciprocal-zero-term and log-zero-term bounds.
-/
theorem tsum_divisor_inv_normSq_eq_two_mul_abs_BRe {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) :
    ∑' ρ : ℂ,
        ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) /
          Complex.normSq ρ =
      2 * |primitiveBRe χ| := by
  have hZ := abs_primitiveBRe_eq_zeroMass_isQuadratic hN2 hGRH hprimitive hne hinv hquad
  rw [hZ, ← tsum_mul_left]
  apply tsum_congr
  intro ρ
  set D := MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ with hD_def
  by_cases hD0 : D = 0
  · simp only [hD0, Int.cast_zero, zero_div, one_div, Complex.inv_re, zero_mul, mul_zero]
  · have hzero : DirichletCharacter.completedLFunction χ ρ = 0 :=
      dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero
        hne hD0
    have hre_half : ρ.re = (1 : ℝ) / 2 :=
      completedLFunction_zero_re_eq_half_of_grh_quadratic hGRH hprimitive hne hquad hzero
    have hInvRe : (1 / ρ).re = (1 : ℝ) / 2 / Complex.normSq ρ := by
      rw [one_div, Complex.inv_re, hre_half]
    rw [hInvRe]
    ring

/--
Input/assumptions: GRH, `2 ≤ N`, and a primitive nontrivial quadratic complex Dirichlet character.
Conclusion: the inverse-square zero mass `Σ' ρ, m_ρ / |ρ|²` converges.
Content: `Re` of the summable genus-one series
(`DirichletLFunction.summable_completedLFunctionGenusOneTerm_one`) is
summable (`Complex.reCLM.summable`), and pointwise coincides with `m_ρ / normSq ρ` up to the same
GRH rescaling as `tsum_divisor_inv_normSq_eq_two_mul_abs_BRe`.
Role: the summability companion needed to legitimately bound `‖tsum‖ ≤ tsum ‖·‖` in the
reciprocal/log zero-term estimates below.
-/
theorem summable_divisor_div_normSq_of_grh_quadratic {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) :
    Summable
      (fun ρ : ℂ =>
        ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) /
          Complex.normSq ρ) := by
  have hsummable :=
    summable_completedLFunctionGenusOneTerm_one
      hN2 hprimitive hne hinv
  have hsummableRe := Complex.reCLM.summable hsummable
  apply hsummableRe.congr
  intro ρ
  set D := MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ with hD_def
  by_cases hD0 : D = 0
  · simp only [hD0, Int.cast_zero, one_div, zero_mul, Complex.reCLM_apply, Complex.zero_re,
      zero_div]
  · have hzero : DirichletCharacter.completedLFunction χ ρ = 0 :=
      dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero
        hne hD0
    have hre_half : ρ.re = (1 : ℝ) / 2 :=
      completedLFunction_zero_re_eq_half_of_grh_quadratic hGRH hprimitive hne hquad hzero
    have hterm :=
      genusOneTerm_re_eq_of_re_eq_half hre_half
    have hInvRe : (1 / ρ).re = (1 : ℝ) / 2 / Complex.normSq ρ := by
      rw [one_div, Complex.inv_re, hre_half]
    have hcast : ((D : ℤ) : ℂ) = (((D : ℤ) : ℝ) : ℂ) := by
      push_cast; ring
    change Complex.reCLM (((D : ℤ) : ℂ) * (1 / (1 - ρ) + 1 / ρ)) = ((D : ℤ) : ℝ) / Complex.normSq ρ
    rw [Complex.reCLM_apply, hcast, Complex.re_ofReal_mul, hterm, hInvRe]
    ring

/--
Input/assumptions: GRH, a primitive nontrivial quadratic complex Dirichlet character, a positive
real `x`, and any `ρ : ℂ`.
Conclusion: `‖D_ρ x^{ρ-1}/(ρ(ρ-1))‖ = (D_ρ/normSq ρ)/√x`, where `D_ρ` is the completed-`L`
divisor at `ρ`.
Content: `D_ρ ≠ 0` forces `completedL(ρ) = 0` by
`dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero`, hence GRH gives `ρ.re = 1/2`;
on the critical line `ρ - 1 = -conj ρ`, so
`ρ(ρ-1) = -normSq ρ` (`Complex.mul_conj`) and `‖x^{ρ-1}‖ = x^{-1/2} = 1/√x`
(`Complex.norm_cpow_eq_rpow_re_of_pos`); both sides vanish when `D_ρ = 0`.
Role: the pointwise identity shared by the whole-line `tsum` bound
(`norm_tsum_reciprocalZeroContribution_le`) and any arbitrary-`Finset` bound — factored out once so
both can reuse it.
-/
theorem norm_completedReciprocalZeroTerm_eq {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hquad : χ.IsQuadratic) {x : ℝ} (hx : 0 < x)
    (ρ : ℂ) :
    ‖((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) *
            (x : ℂ) ^ (ρ - 1) /
          (ρ * (ρ - 1))‖ =
      (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) /
          Complex.normSq ρ) /
        Real.sqrt x := by
  set D := MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ with hD_def
  by_cases hD0 : D = 0
  · simp only [hD0, Int.cast_zero, zero_mul, zero_div, norm_zero]
  · have hDnonneg : (0 : ℝ) ≤ (D : ℝ) := by
      have hdiff := DirichletCharacter.differentiable_completedLFunction hne
      have hanalytic : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) Set.univ :=
        fun z _ => hdiff.analyticAt z
      exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hanalytic ρ
    have hzero : DirichletCharacter.completedLFunction χ ρ = 0 :=
      dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero
        hne hD0
    have hre_half : ρ.re = (1 : ℝ) / 2 :=
      completedLFunction_zero_re_eq_half_of_grh_quadratic hGRH hprimitive hne hquad hzero
    have hconj : (1 : ℂ) - ρ = starRingEnd ℂ ρ := by
      have h1 : (1 - ρ).re = (starRingEnd ℂ ρ).re := by
        simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]; linarith [hre_half]
      have h2 : (1 - ρ).im = (starRingEnd ℂ ρ).im := by
        simp only [Complex.sub_im, Complex.one_im, zero_sub, Complex.conj_im]
      exact Complex.ext h1 h2
    have hprod : ρ * (ρ - 1) = -(Complex.normSq ρ : ℂ) := by
      have : ρ - 1 = -starRingEnd ℂ ρ := by
        rw [← hconj]; ring
      rw [this, mul_neg, Complex.mul_conj]
    have hnormprod : ‖ρ * (ρ - 1)‖ = Complex.normSq ρ := by
      rw [hprod, norm_neg, Complex.norm_real, Real.norm_of_nonneg (Complex.normSq_nonneg ρ)]
    have hnormpow : ‖(x : ℂ) ^ (ρ - 1)‖ = 1 / Real.sqrt x := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.sub_re, Complex.one_re, hre_half,
        show (1 : ℝ) / 2 - 1 = -(1 / 2 : ℝ) from by ring, Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow,
        one_div]
    rw [norm_div, norm_mul, Complex.norm_intCast, abs_of_nonneg hDnonneg, hnormpow, hnormprod]
    ring

/--
Input/assumptions: GRH, `2 ≤ N`, a primitive nontrivial quadratic complex Dirichlet character, and
a positive real `x`.
Conclusion: the reciprocal zero-sum contribution `Σ' ρ, m_ρ x^{ρ-1} / (ρ(ρ-1))` has norm at most
`2 * |Re B(χ)| / √x`.
Content: `norm_completedReciprocalZeroTerm_eq` plus `norm_tsum_le_tsum_norm` and
`tsum_divisor_inv_normSq_eq_two_mul_abs_BRe`'s `Σ m_ρ/normSq ρ = 2|Re B(χ)|` finishes it.
Role: a reciprocal-kernel zero-term bound, avoiding any need for a paper-specific `θ` device.
-/
theorem norm_tsum_reciprocalZeroContribution_le {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) {x : ℝ}
    (hx : 0 < x) :
    ‖∑' ρ : ℂ,
          ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) *
              (x : ℂ) ^ (ρ - 1) /
            (ρ * (ρ - 1))‖ ≤
      2 * |primitiveBRe χ| / Real.sqrt x := by
  have hsummableInv :=
    summable_divisor_div_normSq_of_grh_quadratic hN2 hGRH hprimitive hne hinv hquad
  have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hpt := norm_completedReciprocalZeroTerm_eq hGRH hprimitive hne hquad hx
  refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq ?_)
  · exact (hsummableInv.div_const (Real.sqrt x)).congr (fun ρ => (hpt ρ).symm)
  · calc
      ∑' ρ : ℂ,
            ‖((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) :
                    ℂ) *
                  (x : ℂ) ^ (ρ - 1) /
                (ρ * (ρ - 1))‖ =
          ∑' ρ : ℂ,
            (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) :
                  ℝ) /
                Complex.normSq ρ) /
              Real.sqrt x :=
        tsum_congr hpt
      _ =
          (∑' ρ : ℂ,
              ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) :
                  ℝ) /
                Complex.normSq ρ) /
            Real.sqrt x :=
        tsum_div_const
      _ = 2 * |primitiveBRe χ| / Real.sqrt x :=
        by rw [tsum_divisor_inv_normSq_eq_two_mul_abs_BRe hN2 hGRH hprimitive hne hinv hquad]

/--
Input/assumptions: GRH, `2 ≤ N`, a primitive nontrivial quadratic complex Dirichlet character, and
a positive real `x`.
Conclusion: the logarithmic zero-sum contribution `Σ' ρ, m_ρ x^ρ / ρ²` has norm at most
`2 * √x * |Re B(χ)|`.
Content: `‖ρ²‖ = ‖ρ‖² = normSq ρ` (`Complex.normSq_eq_norm_sq`) and
`‖x^ρ‖ = x^{ρ.re} = x^{1/2} = √x` on the critical line, so `‖m_ρ x^ρ/ρ²‖ = √x·(m_ρ/normSq ρ)`
unconditionally; `norm_tsum_le_tsum_norm` plus the inverse-square zero estimate finishes it,
mirroring the reciprocal-kernel argument.
Role: a logarithmic-kernel zero-term bound.
-/
theorem norm_tsum_logZeroContribution_le {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) {x : ℝ}
    (hx : 0 < x) :
    ‖∑' ρ : ℂ,
          ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) *
              (x : ℂ) ^ ρ /
            ρ ^ 2‖ ≤
      2 * Real.sqrt x * |primitiveBRe χ| := by
  have hsummableInv :=
    summable_divisor_div_normSq_of_grh_quadratic hN2 hGRH hprimitive hne hinv hquad
  have hpt :
    ∀ ρ : ℂ,
      ‖((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) *
              (x : ℂ) ^ ρ /
            ρ ^ 2‖ =
        Real.sqrt x *
          (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) /
            Complex.normSq ρ) := by
    intro ρ
    set D := MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ with hD_def
    by_cases hD0 : D = 0
    · simp only [hD0, Int.cast_zero, zero_mul, zero_div, norm_zero, mul_zero]
    · have hDnonneg : (0 : ℝ) ≤ (D : ℝ) := by
        have hdiff := DirichletCharacter.differentiable_completedLFunction hne
        have hanalytic : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) Set.univ :=
          fun z _ => hdiff.analyticAt z
        exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hanalytic ρ
      have hzero : DirichletCharacter.completedLFunction χ ρ = 0 :=
        dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero
          hne hD0
      have hre_half : ρ.re = (1 : ℝ) / 2 :=
        completedLFunction_zero_re_eq_half_of_grh_quadratic hGRH hprimitive hne hquad hzero
      have hnormsq : ‖ρ ^ 2‖ = Complex.normSq ρ := by rw [norm_pow, ← Complex.normSq_eq_norm_sq]
      have hnormpow : ‖(x : ℂ) ^ ρ‖ = Real.sqrt x := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, hre_half, ← Real.sqrt_eq_rpow]
      rw [norm_div, norm_mul, Complex.norm_intCast, abs_of_nonneg hDnonneg, hnormpow, hnormsq]
      ring
  refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq ?_)
  · exact (hsummableInv.mul_left (Real.sqrt x)).congr (fun ρ => (hpt ρ).symm)
  · calc
      ∑' ρ : ℂ,
            ‖((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) :
                    ℂ) *
                  (x : ℂ) ^ ρ /
                ρ ^ 2‖ =
          ∑' ρ : ℂ,
            Real.sqrt x *
              (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) :
                  ℝ) /
                Complex.normSq ρ) :=
        tsum_congr hpt
      _ =
          Real.sqrt x *
            ∑' ρ : ℂ,
              ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) :
                  ℝ) /
                Complex.normSq ρ :=
        tsum_mul_left
      _ = 2 * Real.sqrt x * |primitiveBRe χ| :=
        by
        rw [tsum_divisor_inv_normSq_eq_two_mul_abs_BRe hN2 hGRH hprimitive hne hinv hquad]
        ring

/-! ### The Cauchy–Schwarz bound on the truncated genus sum -/

/--
Input/assumptions: GRH, `2 ≤ N`, a primitive nontrivial quadratic character, `0 < R`, a point `s`
where `completedLFunction χ` does not vanish, and a positive margin `δ` such that every zero of
`completedLFunction χ` inside `ball 0 R` stays at distance `≥ δ` from `s`.
Conclusion: `‖DirichletLFunction.completedLFunctionTruncatedGenusSum χ R s‖ ≤ ‖s‖ · √(2|Re B(χ)|) ·
√(log(max 1 (completedLFunctionBallBound N (2R))/‖F(0)‖)/log 2) / δ`.
Content: writing `1/(s-ρ)+1/ρ = s/(ρ(s-ρ))` termwise, weighted Cauchy–Schwarz
(`Finset.sum_mul_sq_le_sq_mul_sq`, weight `√(m_ρ)` on `1/|ρ|` and `1/|s-ρ|`) splits the sum into
`√(Σ m_ρ/|ρ|²)` (the zero mass `2|Re B(χ)|`, `R`-independent) times `√(Σ m_ρ/|s-ρ|²)` (bounded by
`(ball-count bound)/δ²` using the separation hypothesis).
Role: a pointwise ingredient for bounding the horizontal-edge log-derivative.
-/
theorem norm_completedLFunctionTruncatedGenusSum_le {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) {R : ℝ}
    (hR : 0 < R) {s : ℂ} (hsne : DirichletCharacter.completedLFunction χ s ≠ 0) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 → ‖ρ‖ < R → δ ≤ ‖s - ρ‖) :
    ‖completedLFunctionTruncatedGenusSum χ R
          s‖ ≤
      ‖s‖ * Real.sqrt (2 * |primitiveBRe χ|) *
          Real.sqrt
            (Real.log
                (max 1
                    (completedLFunctionBallBound
                      N (2 * R)) /
                  ‖DirichletCharacter.completedLFunction χ 0‖) /
              Real.log 2) /
        δ := by
  have hN1 : 1 < N := by omega
  set Dv :=
    MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R) with
    hDv_def
  have hdiff := DirichletCharacter.differentiable_completedLFunction hne
  have hAnClosed :
    AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) (Metric.closedBall (0 : ℂ) R) :=
    fun z _ => hdiff.analyticAt z
  have hAnBall :
    AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R) := fun z _ =>
    hdiff.analyticAt z
  have hAnU : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) Set.univ := fun z _ =>
    hdiff.analyticAt z
  have h0ne : DirichletCharacter.completedLFunction χ 0 ≠ 0 :=
    dirichletCompletedLFunction_zero_ne_zero_of_primitive
      hprimitive hne
  have hfin : (Function.support Dv).Finite := hAnClosed.meromorphicOn.divisor_ball_support_finite
  set S := hfin.toFinset with hS_def
  have hDv_nonneg : ∀ ρ, (0 : ℤ) ≤ Dv ρ := fun ρ =>
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAnBall ρ
  have hρ_ball : ∀ ρ, Dv ρ ≠ 0 → ρ ∈ Metric.ball (0 : ℂ) R := by
    intro ρ hne'
    by_contra hnot
    exact hne' (Dv.apply_eq_zero_of_notMem hnot)
  have hDv_zero :
    ∀ ρ, ρ ∈ Metric.ball (0 : ℂ) R → Dv ρ ≠ 0 → DirichletCharacter.completedLFunction χ ρ = 0 := by
    intro ρ hρmem hDvne
    by_contra hFne
    apply hDvne
    have hordzero : analyticOrderAt (DirichletCharacter.completedLFunction χ) ρ = 0 :=
      (hAnBall ρ hρmem).analyticOrderAt_eq_zero.mpr hFne
    rw [hDv_def, MeromorphicOn.AnalyticOnNhd.divisor_apply hAnBall hρmem, hordzero]
    simp only [ENat.map_zero, CharP.cast_eq_zero, WithTop.coe_zero, WithTop.untop₀_zero]
  -- Step 1: rewrite the genus sum as a Finset sum over S
  have heqsum :
    completedLFunctionTruncatedGenusSum χ R s =
      ∑ ρ ∈ S, ((Dv ρ : ℤ) : ℂ) * (1 / (s - ρ) + 1 / ρ) := by
    unfold completedLFunctionTruncatedGenusSum
    apply finsum_eq_finsetSum_of_support_subset
    intro ρ hρ
    rw [hS_def, Set.Finite.coe_toFinset]
    rw [Function.mem_support] at hρ ⊢
    intro hDv0
    apply hρ
    rw [hDv0]
    simp only [Int.cast_zero, one_div, zero_mul]
  -- Step 2: termwise norm computation
  have hterm_eq :
    ∀ ρ ∈ S, ‖((Dv ρ : ℤ) : ℂ) * (1 / (s - ρ) + 1 / ρ)‖ = (Dv ρ : ℝ) * ‖s‖ / (‖ρ‖ * ‖s - ρ‖) := by
    intro ρ hρS
    rw [hS_def, Set.Finite.mem_toFinset, Function.mem_support] at hρS
    have hρmem := hρ_ball ρ hρS
    have hFzero := hDv_zero ρ hρmem hρS
    have hρ0 : ρ ≠ 0 := fun h0 => h0ne (h0 ▸ hFzero)
    have hsρ : s ≠ ρ := fun heq => hsne (heq ▸ hFzero)
    have hid : (1 : ℂ) / (s - ρ) + 1 / ρ = s / (ρ * (s - ρ)) := by
      field_simp
      ring
    rw [hid, norm_mul, norm_div, norm_mul, Complex.norm_intCast,
      abs_of_nonneg (show (0 : ℝ) ≤ (Dv ρ : ℝ) by exact_mod_cast hDv_nonneg ρ)]
    ring
  -- Step 3: triangle inequality
  have hnorm_le :
    ‖completedLFunctionTruncatedGenusSum χ R
          s‖ ≤
      ‖s‖ * ∑ ρ ∈ S, (Dv ρ : ℝ) / (‖ρ‖ * ‖s - ρ‖) := by
    rw [heqsum]
    calc
      ‖∑ ρ ∈ S, ((Dv ρ : ℤ) : ℂ) * (1 / (s - ρ) + 1 / ρ)‖ ≤
          ∑ ρ ∈ S, ‖((Dv ρ : ℤ) : ℂ) * (1 / (s - ρ) + 1 / ρ)‖ :=
        norm_sum_le S _
      _ = ∑ ρ ∈ S, (Dv ρ : ℝ) * ‖s‖ / (‖ρ‖ * ‖s - ρ‖) := Finset.sum_congr rfl hterm_eq
      _ = ‖s‖ * ∑ ρ ∈ S, (Dv ρ : ℝ) / (‖ρ‖ * ‖s - ρ‖) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun ρ _ => by ring)
  -- Step 4: weighted Cauchy–Schwarz
  have hCS :
    (∑ ρ ∈ S, (Dv ρ : ℝ) / (‖ρ‖ * ‖s - ρ‖)) ^ 2 ≤
      (∑ ρ ∈ S, (Dv ρ : ℝ) / ‖ρ‖ ^ 2) * (∑ ρ ∈ S, (Dv ρ : ℝ) / ‖s - ρ‖ ^ 2) := by
    have hkey :=
      Finset.sum_mul_sq_le_sq_mul_sq S (fun ρ => Real.sqrt (Dv ρ) / ‖ρ‖)
        (fun ρ => Real.sqrt (Dv ρ) / ‖s - ρ‖)
    have heq1 :
      ∀ ρ ∈ S,
        (Real.sqrt (Dv ρ) / ‖ρ‖) * (Real.sqrt (Dv ρ) / ‖s - ρ‖) = (Dv ρ : ℝ) / (‖ρ‖ * ‖s - ρ‖) :=
      fun ρ _ => by rw [div_mul_div_comm, Real.mul_self_sqrt (by exact_mod_cast hDv_nonneg ρ)]
    have heq2 : ∀ ρ ∈ S, (Real.sqrt (Dv ρ) / ‖ρ‖) ^ 2 = (Dv ρ : ℝ) / ‖ρ‖ ^ 2 := fun ρ _ => by
      rw [div_pow, Real.sq_sqrt (by exact_mod_cast hDv_nonneg ρ)]
    have heq3 : ∀ ρ ∈ S, (Real.sqrt (Dv ρ) / ‖s - ρ‖) ^ 2 = (Dv ρ : ℝ) / ‖s - ρ‖ ^ 2 := fun ρ _ =>
      by rw [div_pow, Real.sq_sqrt (by exact_mod_cast hDv_nonneg ρ)]
    rwa [Finset.sum_congr rfl heq1, Finset.sum_congr rfl heq2, Finset.sum_congr rfl heq3] at hkey
  -- Step 5a: bound the first Cauchy–Schwarz factor via the zero mass
  have hfactorA :
    ∑ ρ ∈ S, (Dv ρ : ℝ) / ‖ρ‖ ^ 2 ≤
      2 * |primitiveBRe χ| := by
    have hterm_eq2 :
      ∀ ρ ∈ S,
        (Dv ρ : ℝ) / ‖ρ‖ ^ 2 =
          ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) /
            Complex.normSq ρ := by
      intro ρ hρS
      rw [hS_def, Set.Finite.mem_toFinset, Function.mem_support] at hρS
      have hρmem := hρ_ball ρ hρS
      rw [← Complex.normSq_eq_norm_sq, hDv_def,
        divisor_completedLFunction_domain_eq hne
          hρmem]
    calc
      ∑ ρ ∈ S, (Dv ρ : ℝ) / ‖ρ‖ ^ 2 =
          ∑ ρ ∈ S,
            ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) /
              Complex.normSq ρ :=
        Finset.sum_congr rfl hterm_eq2
      _ ≤
          ∑' ρ : ℂ,
            ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) /
              Complex.normSq ρ :=
        (summable_divisor_div_normSq_of_grh_quadratic hN2 hGRH hprimitive hne hinv
              hquad).sum_le_tsum
          S
          (fun i _ =>
            div_nonneg (by exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAnU i)
              (Complex.normSq_nonneg i))
      _ = 2 * |primitiveBRe χ| :=
        tsum_divisor_inv_normSq_eq_two_mul_abs_BRe hN2 hGRH hprimitive hne hinv hquad
  -- Step 5b: bound the second Cauchy–Schwarz factor via the good-height margin
  have hfactorB :
    ∑ ρ ∈ S, (Dv ρ : ℝ) / ‖s - ρ‖ ^ 2 ≤
      (Real.log
            (max 1
                (completedLFunctionBallBound N
                  (2 * R)) /
              ‖DirichletCharacter.completedLFunction χ 0‖) /
          Real.log 2) /
        δ ^ 2 := by
    have hterm_le : ∀ ρ ∈ S, (Dv ρ : ℝ) / ‖s - ρ‖ ^ 2 ≤ (Dv ρ : ℝ) / δ ^ 2 := by
      intro ρ hρS
      rw [hS_def, Set.Finite.mem_toFinset, Function.mem_support] at hρS
      have hρmem := hρ_ball ρ hρS
      have hFzero := hDv_zero ρ hρmem hρS
      have hρnorm : ‖ρ‖ < R := by
        rw [Metric.mem_ball, dist_zero_right] at hρmem; exact hρmem
      have hsep' : δ ≤ ‖s - ρ‖ := hsep ρ hFzero hρnorm
      have hδsq : δ ^ 2 ≤ ‖s - ρ‖ ^ 2 := pow_le_pow_left₀ hδ.le hsep' 2
      have hDvρnonneg : (0 : ℝ) ≤ (Dv ρ : ℝ) := by exact_mod_cast hDv_nonneg ρ
      gcongr
    have hSsum :
      (∑ ρ ∈ S, (Dv ρ : ℝ)) ≤
        Real.log
            (max 1
                (completedLFunctionBallBound N
                  (2 * R)) /
              ‖DirichletCharacter.completedLFunction χ 0‖) /
          Real.log 2 := by
      have hSsumZ : (∑ ρ ∈ S, Dv ρ : ℤ) = ∑ᶠ ρ, Dv ρ := by
        symm
        apply finsum_eq_finsetSum_of_support_subset
        rw [hS_def, Set.Finite.coe_toFinset]
      have : ((∑ ρ ∈ S, Dv ρ : ℤ) : ℝ) = ∑ ρ ∈ S, (Dv ρ : ℝ) := by
        push_cast; ring
      rw [← this, hSsumZ]
      exact
        finsum_divisor_ball_completedLFunction_le
          hN1 hprimitive hne hinv hR
    calc
      ∑ ρ ∈ S, (Dv ρ : ℝ) / ‖s - ρ‖ ^ 2 ≤ ∑ ρ ∈ S, (Dv ρ : ℝ) / δ ^ 2 := Finset.sum_le_sum hterm_le
      _ = (∑ ρ ∈ S, (Dv ρ : ℝ)) / δ ^ 2 := by rw [Finset.sum_div]
      _ ≤ _ := by gcongr
  -- Step 6: combine
  have hH2nonneg :
    (0 : ℝ) ≤
      Real.log
          (max 1
              (completedLFunctionBallBound N
                (2 * R)) /
            ‖DirichletCharacter.completedLFunction χ 0‖) /
        Real.log 2 := by
    have hfinsum_nonneg :
      (0 : ℤ) ≤
        ∑ᶠ u,
          MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall (0 : ℂ) R) u := by
      apply finsum_nonneg
      intro u
      exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAnClosed u
    exact
      le_trans (by exact_mod_cast hfinsum_nonneg)
        (finsum_divisor_completedLFunction_le
          hN1 hprimitive hne hinv hR)
  have hCSfull :
    (∑ ρ ∈ S, (Dv ρ : ℝ) / (‖ρ‖ * ‖s - ρ‖)) ^ 2 ≤
      2 * |primitiveBRe χ| *
        (Real.log
            (max 1
                (completedLFunctionBallBound N
                  (2 * R)) /
              ‖DirichletCharacter.completedLFunction χ 0‖) /
          Real.log 2 /
          δ ^ 2) :=
    hCS.trans
      (mul_le_mul hfactorA hfactorB
        (Finset.sum_nonneg (fun ρ _ => div_nonneg (by exact_mod_cast hDv_nonneg ρ) (sq_nonneg _)))
        (by positivity))
  have hsum_nonneg : 0 ≤ ∑ ρ ∈ S, (Dv ρ : ℝ) / (‖ρ‖ * ‖s - ρ‖) :=
    Finset.sum_nonneg
      (fun ρ _ =>
        div_nonneg (by exact_mod_cast hDv_nonneg ρ) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
  have hrw :
    2 * |primitiveBRe χ| *
        (Real.log
            (max 1
                (completedLFunctionBallBound N
                  (2 * R)) /
              ‖DirichletCharacter.completedLFunction χ 0‖) /
          Real.log 2 /
          δ ^ 2) =
      (Real.sqrt (2 * |primitiveBRe χ|) *
            Real.sqrt
              (Real.log
                  (max 1
                      (completedLFunctionBallBound
                        N (2 * R)) /
                    ‖DirichletCharacter.completedLFunction χ 0‖) /
                Real.log 2) /
          δ) ^
        2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hH2nonneg]
    ring
  rw [hrw] at hCSfull
  have hsum_le :
    ∑ ρ ∈ S, (Dv ρ : ℝ) / (‖ρ‖ * ‖s - ρ‖) ≤
      Real.sqrt (2 * |primitiveBRe χ|) *
          Real.sqrt
            (Real.log
                (max 1
                    (completedLFunctionBallBound
                      N (2 * R)) /
                  ‖DirichletCharacter.completedLFunction χ 0‖) /
              Real.log 2) /
        δ := by
    have hrhs_nonneg :
      (0 : ℝ) ≤
        Real.sqrt (2 * |primitiveBRe χ|) *
            Real.sqrt
              (Real.log
                  (max 1
                      (completedLFunctionBallBound
                        N (2 * R)) /
                    ‖DirichletCharacter.completedLFunction χ 0‖) /
                Real.log 2) /
          δ := by
      positivity
    nlinarith [hCSfull, hsum_nonneg, hrhs_nonneg]
  calc
    ‖completedLFunctionTruncatedGenusSum χ R
            s‖ ≤
        ‖s‖ * ∑ ρ ∈ S, (Dv ρ : ℝ) / (‖ρ‖ * ‖s - ρ‖) :=
      hnorm_le
    _ ≤
        ‖s‖ *
          (Real.sqrt (2 * |primitiveBRe χ|) *
              Real.sqrt
                (Real.log
                    (max 1
                        (completedLFunctionBallBound
                          N (2 * R)) /
                      ‖DirichletCharacter.completedLFunction χ 0‖) /
                  Real.log 2) /
            δ) :=
      mul_le_mul_of_nonneg_left hsum_le (norm_nonneg s)
    _ =
        ‖s‖ * Real.sqrt (2 * |primitiveBRe χ|) *
            Real.sqrt
              (Real.log
                  (max 1
                      (completedLFunctionBallBound
                        N (2 * R)) /
                    ‖DirichletCharacter.completedLFunction χ 0‖) /
                Real.log 2) /
          δ :=
      by ring

/--
Input/assumptions: GRH, `2 ≤ N`, a primitive nontrivial quadratic character, `R ≥ 1` with no zero
of `completedLFunction χ` exactly on `‖ρ‖ = R`, a point `s` with `‖s‖ ≤ R/2` where
`completedLFunction χ` doesn't vanish, and a margin `δ > 0` separating `s` from every zero inside
`ball 0 R`.
Conclusion: `‖logDeriv F(s) - logDeriv F(0)‖` is bounded by the finite-radius error term plus the
Cauchy–Schwarz genus-sum bound.
Content: the triangle inequality applied to
`DirichletLFunction.norm_centeredLogDeriv_sub_truncatedGenus_le`
(bounding the difference from the truncated genus sum) and
`norm_completedLFunctionTruncatedGenusSum_le` (bounding the genus sum itself).
Role: a pointwise ingredient combined at a good height/radius `T`/`R`, this makes a horizontal
contour edge integral vanish as `T → ∞`.
-/
theorem norm_centeredLogDeriv_le_of_separation {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) {R : ℝ}
    (hR : 1 ≤ R) (hzf : ∀ ρ : ℂ, ‖ρ‖ = R → DirichletCharacter.completedLFunction χ ρ ≠ 0) {s : ℂ}
    (hs : ‖s‖ ≤ R / 2) (hsne : DirichletCharacter.completedLFunction χ s ≠ 0) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 → ‖ρ‖ < R → δ ≤ ‖s - ρ‖) :
    ‖logDeriv (DirichletCharacter.completedLFunction χ) s -
          logDeriv (DirichletCharacter.completedLFunction χ) 0‖ ≤
      192 * ‖s‖ *
            ((4 * (N : ℝ) + 3) * (R + 3) * Real.log (R + 3) -
                Real.log ‖DirichletCharacter.completedLFunction χ 0‖ +
              1) /
          R ^ 2 +
        2 * ‖s‖ / R ^ 2 *
          (Real.log
              (max 1
                  (completedLFunctionBallBound N
                    (2 * R)) /
                ‖DirichletCharacter.completedLFunction χ 0‖) /
            Real.log 2) +
        ‖s‖ * Real.sqrt (2 * |primitiveBRe χ|) *
            Real.sqrt
              (Real.log
                  (max 1
                      (completedLFunctionBallBound
                        N (2 * R)) /
                    ‖DirichletCharacter.completedLFunction χ 0‖) /
                Real.log 2) /
          δ := by
  have hN1 : 1 < N := by omega
  have hH9e :=
    norm_centeredLogDeriv_sub_truncatedGenus_le
      hN1 hprimitive hne hinv hR hzf hs hsne
  have hGenus :=
    norm_completedLFunctionTruncatedGenusSum_le hN2 hGRH hprimitive hne hinv hquad
      (show (0 : ℝ) < R by linarith) hsne hδ hsep
  calc
    ‖logDeriv (DirichletCharacter.completedLFunction χ) s -
            logDeriv (DirichletCharacter.completedLFunction χ) 0‖ =
        ‖((logDeriv (DirichletCharacter.completedLFunction χ) s -
                logDeriv (DirichletCharacter.completedLFunction χ) 0) -
              completedLFunctionTruncatedGenusSum
                χ R s) +
            completedLFunctionTruncatedGenusSum
              χ R s‖ :=
      by ring_nf
    _ ≤
        ‖(logDeriv (DirichletCharacter.completedLFunction χ) s -
                logDeriv (DirichletCharacter.completedLFunction χ) 0) -
              completedLFunctionTruncatedGenusSum
                χ R s‖ +
          ‖completedLFunctionTruncatedGenusSum χ
              R s‖ :=
      norm_add_le _ _
    _ ≤ _ := add_le_add hH9e hGenus

/--
Input/assumptions: GRH, `2 ≤ N`, primitive nontrivial quadratic `χ`, `R > 0`.
Conclusion: `DirichletLFunction.completedLFunctionTruncatedGenusSum χ R` has a derivative `D` at
`0` with
`‖D‖ ≤ 2 * |Re B(χ)|`.
Content: (finiteness) `Dv := divisor F (ball 0 R)` has finite support
(`divisor_ball_support_finite`); the finsum defining the truncated genus sum coincides, for every
`s`, with the finite sum over `Dv`'s support (`finsum_eq_sum_of_support_subset`); each finite
summand's derivative at `0` is `D_ρ * (-(1/ρ²))` (via `hasDerivAt_inv` composed with the affine
shift, since `ρ ≠ 0` for `ρ` in the support by `F 0 ≠ 0`), summed via `HasDerivAt.fun_sum`.
(norm bound) each `Dv`-summand's norm equals `D_ρ/normSq ρ` for the *global* (`Set.univ`) divisor
(since `Dv ρ = divisor_univ ρ` inside the ball, `DirichletLFunction.divisor_ball_eq_if_univ`), and
the finite sum of
these nonnegative terms is at most the global `tsum`, which is `2|Re B(χ)|`
(`tsum_divisor_inv_normSq_eq_two_mul_abs_BRe`).
Role: a finite-ledger bound supplying the truncated genus sum's own derivative-norm bound needed
to isolate `(logDeriv F)'(0)` via a slope estimate.
-/
theorem exists_hasDerivAt_completedLFunctionTruncatedGenusSum_zero_norm_le {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic)
    (hN2 : 2 ≤ N) {R : ℝ} (_hR : 0 < R) :
    ∃ D : ℂ,
      HasDerivAt
          (completedLFunctionTruncatedGenusSum χ
            R)
          D 0 ∧
        ‖D‖ ≤ 2 * |primitiveBRe χ| := by
  have hdiff := DirichletCharacter.differentiable_completedLFunction hne
  have hanalyticClosed :
    AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) (Metric.closedBall (0 : ℂ) R) :=
    fun z _ => hdiff.analyticAt z
  set Dv :=
    MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R) with
    hDv_def
  have hfin : (Function.support Dv).Finite :=
    hanalyticClosed.meromorphicOn.divisor_ball_support_finite
  have h0ne : DirichletCharacter.completedLFunction χ 0 ≠ 0 :=
    dirichletCompletedLFunction_zero_ne_zero_of_primitive
      hprimitive hne
  have hkey : ∀ u ∈ hfin.toFinset, u ∈ Metric.ball (0 : ℂ) R ∧ u ≠ 0 := by
    intro u hu
    rw [Set.Finite.mem_toFinset] at hu
    exact
      ⟨Dv.supportWithinDomain hu,
        ne_of_mem_divisorBallSupport_of_completedLFunction_ne_zero
          hne hu h0ne⟩
  have hsub :
    ∀ s : ℂ,
      Function.support (fun ρ : ℂ => ((Dv ρ : ℤ) : ℂ) * (1 / (s - ρ) + 1 / ρ)) ⊆ hfin.toFinset := by
    intro s u hu
    rw [Function.mem_support] at hu
    rw [Set.Finite.coe_toFinset, Function.mem_support]
    intro hDu0
    apply hu
    rw [hDu0]
    simp only [Int.cast_zero, one_div, zero_mul]
  have heq :
    completedLFunctionTruncatedGenusSum χ R =
      fun s : ℂ => ∑ ρ ∈ hfin.toFinset, ((Dv ρ : ℤ) : ℂ) * (1 / (s - ρ) + 1 / ρ) := by
    funext s
    rw [completedLFunctionTruncatedGenusSum,
      finsum_eq_sum_of_support_subset _ (hsub s)]
  set D : ℂ := ∑ ρ ∈ hfin.toFinset, ((Dv ρ : ℤ) : ℂ) * (-(1 / ρ ^ 2)) with hD_def
  refine ⟨D, ?_, ?_⟩
  · rw [heq]
    apply HasDerivAt.fun_sum
    intro ρ hρ
    obtain ⟨_, hρne0⟩ := hkey ρ hρ
    have hne' : (0 : ℂ) - ρ ≠ 0 := by
      rw [zero_sub, neg_ne_zero]; exact hρne0
    have hc : HasDerivAt (fun s : ℂ => s - ρ) 1 0 := (hasDerivAt_id (0 : ℂ)).sub_const ρ
    have hinvderiv := hc.inv hne'
    have hval : -(1 : ℂ) / ((0 : ℂ) - ρ) ^ 2 = -(1 / ρ ^ 2) := by
      rw [zero_sub, neg_sq]; ring
    rw [hval] at hinvderiv
    have h2 : HasDerivAt (fun s : ℂ => (1 : ℂ) / (s - ρ)) (-(1 / ρ ^ 2)) 0 := by
      have heq2 : (fun s : ℂ => (1 : ℂ) / (s - ρ)) = (fun s : ℂ => s - ρ)⁻¹ := by
        funext s; rw [Pi.inv_apply, one_div]
      rw [heq2]; exact hinvderiv
    have h3 : HasDerivAt (fun _ : ℂ => (1 : ℂ) / ρ) 0 0 := hasDerivAt_const 0 (1 / ρ)
    have h4 : HasDerivAt (fun s : ℂ => (1 : ℂ) / (s - ρ) + 1 / ρ) (-(1 / ρ ^ 2)) 0 := by
      have hadd := h2.add h3
      have hfun :
        (fun s : ℂ => (1 : ℂ) / (s - ρ)) + (fun _ : ℂ => (1 : ℂ) / ρ) = fun s : ℂ =>
          (1 : ℂ) / (s - ρ) + 1 / ρ := by
        funext s; rfl
      rw [hfun, add_zero] at hadd
      exact hadd
    exact h4.const_mul ((Dv ρ : ℤ) : ℂ)
  · have hsummable :=
      summable_divisor_div_normSq_of_grh_quadratic hN2 hGRH hprimitive hne hinv hquad
    have htsum := tsum_divisor_inv_normSq_eq_two_mul_abs_BRe hN2 hGRH hprimitive hne hinv hquad
    have hterm :
      ∀ ρ ∈ hfin.toFinset,
        ‖((Dv ρ : ℤ) : ℂ) * (-(1 / ρ ^ 2))‖ =
          ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) /
            Complex.normSq ρ := by
      intro ρ hρ
      obtain ⟨hρball, _⟩ := hkey ρ hρ
      have hDeq :
        Dv ρ = MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ := by
        rw [hDv_def,
          divisor_ball_eq_if_univ hne,
          ite_eq_left (by rwa [Metric.mem_ball, dist_zero_right] at hρball)]
      have hanalyticUniv : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) Set.univ :=
        fun z _ => hdiff.analyticAt z
      have hDnonneg :
        (0 : ℝ) ≤
          ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) :
            ℝ) := by
        exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hanalyticUniv ρ
      have hnormsq : ‖ρ ^ 2‖ = Complex.normSq ρ := by rw [norm_pow, ← Complex.normSq_eq_norm_sq]
      rw [norm_mul, Complex.norm_intCast, hDeq, abs_of_nonneg hDnonneg, norm_neg, norm_div,
        norm_one, hnormsq, mul_one_div]
    calc
      ‖D‖ ≤ ∑ ρ ∈ hfin.toFinset, ‖((Dv ρ : ℤ) : ℂ) * (-(1 / ρ ^ 2))‖ := by
        rw [hD_def]; exact norm_sum_le _ _
      _ =
          ∑ ρ ∈ hfin.toFinset,
            ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) /
              Complex.normSq ρ :=
        Finset.sum_congr rfl hterm
      _ ≤
          ∑' ρ : ℂ,
            ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) /
              Complex.normSq ρ :=
        by
        have hanalyticUniv : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) Set.univ :=
          fun z _ => hdiff.analyticAt z
        have hallNonneg :
          ∀ ρ : ℂ,
            (0 : ℝ) ≤
              ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) :
                  ℝ) /
                Complex.normSq ρ := by
          intro ρ
          have :
            (0 : ℝ) ≤
              ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) :
                ℝ) := by
            exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hanalyticUniv ρ
          exact div_nonneg this (Complex.normSq_nonneg ρ)
        exact hsummable.sum_le_tsum hfin.toFinset (fun ρ _ => hallNonneg ρ)
      _ = 2 * |primitiveBRe χ| := htsum

/--
Input/assumptions: GRH, `2 ≤ N`, primitive nontrivial quadratic `χ`, `hinv`, `R ≥ 1`, `R`
zero-free sphere.
Conclusion: `‖deriv (logDeriv F) 0‖ ≤ DirichletLFunction.completedLFunctionH9eSlopeError χ R + 2 *
|Re B(χ)|`.
Content: triangle inequality combining
`DirichletLFunction.norm_deriv_logDeriv_completedLFunction_zero_sub_le` and
`exists_hasDerivAt_completedLFunctionTruncatedGenusSum_zero_norm_le`'s norm bound on `D`.
Role: a fixed-`R` bound, ready for `R → ∞` along a good-radius sequence.
-/
theorem norm_deriv_logDeriv_completedLFunction_zero_le {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic)
    (hN2 : 2 ≤ N) {R : ℝ} (hR : 1 ≤ R)
    (hzf : ∀ ρ : ℂ, ‖ρ‖ = R → DirichletCharacter.completedLFunction χ ρ ≠ 0) :
    ‖deriv (logDeriv (DirichletCharacter.completedLFunction χ)) 0‖ ≤
      completedLFunctionH9eSlopeError χ R +
        2 * |primitiveBRe χ| := by
  have hN1 : 1 < N := by omega
  obtain ⟨D, hD, hDnorm⟩ :=
    exists_hasDerivAt_completedLFunctionTruncatedGenusSum_zero_norm_le hGRH hprimitive hne hinv
      hquad hN2 (show (0 : ℝ) < R by linarith)
  have hsub :=
    norm_deriv_logDeriv_completedLFunction_zero_sub_le
      hN1 hprimitive hne hinv hR hzf hD
  calc
    ‖deriv (logDeriv (DirichletCharacter.completedLFunction χ)) 0‖ ≤
        ‖deriv (logDeriv (DirichletCharacter.completedLFunction χ)) 0 - D‖ + ‖D‖ :=
      by
      have := norm_add_le (deriv (logDeriv (DirichletCharacter.completedLFunction χ)) 0 - D) D
      simpa only [ge_iff_le, sub_add_cancel] using this
    _ ≤
        completedLFunctionH9eSlopeError χ R +
          2 * |primitiveBRe χ| :=
      add_le_add hsub hDnorm

/--
Input/assumptions: GRH, `2 ≤ N`, primitive nontrivial quadratic `χ`, `hinv`.
Conclusion: `‖deriv (logDeriv F) 0‖ ≤ 2 * |Re B(χ)|`.
Content: transfers `norm_deriv_logDeriv_completedLFunction_zero_le` through `R → ∞` along
`DirichletLFunction.completedLFunctionGoodRadius` (`R_n > n + 2 ≥ 1`, zero-free by construction),
using
`DirichletLFunction.tendsto_completedLFunctionH9eSlopeError_atTop` to vanish the error term via
`le_of_tendsto`.
Role: a Hadamard-side derivative-norm bound at the origin, without ever exposing the global
identity `(logDeriv F)'(0) = -Σ_ρ m_ρ/ρ²` — only the triangle-inequality bound survives to the
public API.
-/
theorem norm_deriv_logDeriv_completedLFunction_zero_le_two_mul_abs_BRe {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic)
    (hN2 : 2 ≤ N) :
    ‖deriv (logDeriv (DirichletCharacter.completedLFunction χ)) 0‖ ≤
      2 * |primitiveBRe χ| := by
  have htendError :=
    tendsto_completedLFunctionH9eSlopeError_atTop
      hN2 hprimitive hne hinv
  have htendComp :=
    htendError.comp
      (tendsto_completedLFunctionGoodRadius_atTop
        hne)
  have htendSum :
    Filter.Tendsto
      (fun n : ℕ =>
        completedLFunctionH9eSlopeError χ
            (completedLFunctionGoodRadius hne
              n) +
          2 * |primitiveBRe χ|)
      Filter.atTop
      (nhds (0 + 2 * |primitiveBRe χ|)) :=
    htendComp.add tendsto_const_nhds
  simp only [zero_add] at htendSum
  have hev :
    ∀ᶠ n : ℕ in Filter.atTop,
      ‖deriv (logDeriv (DirichletCharacter.completedLFunction χ)) 0‖ ≤
        completedLFunctionH9eSlopeError χ
            (completedLFunctionGoodRadius hne
              n) +
          2 * |primitiveBRe χ| := by
    filter_upwards with n
    have hRgt :=
      completedLFunctionGoodRadius_gt hne n
    have hR1 :
      (1 : ℝ) ≤
        completedLFunctionGoodRadius hne n := by
      have hnnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    exact
      norm_deriv_logDeriv_completedLFunction_zero_le hGRH hprimitive hne hinv hquad hN2 hR1
        (completedLFunctionGoodRadius_zeroFree
          hne n)
  exact ge_of_tendsto htendSum hev

/--
Input/assumptions: `N ≥ 2`, `χ` primitive nontrivial quadratic mod `N`, GRH, `χ⁻¹ ≠ 1`.
Conclusion: `-Re(deriv(logDeriv F) 0) ≤ 2 |Re B(χ)|`.
Content: `-Re(z) ≤ ‖-z‖ = ‖z‖` (`Complex.re_le_norm`), then
`norm_deriv_logDeriv_completedLFunction_zero_le_two_mul_abs_BRe`.
Role: a real-part corollary of the derivative-norm bound at the origin.
-/
theorem neg_re_deriv_logDeriv_completedLFunction_zero_le {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic)
    (hN2 : 2 ≤ N) :
    -(deriv (logDeriv (DirichletCharacter.completedLFunction χ)) 0).re ≤
      2 * |primitiveBRe χ| := by
  have hnormBound :=
    norm_deriv_logDeriv_completedLFunction_zero_le_two_mul_abs_BRe hGRH hprimitive hne hinv hquad
      hN2
  have hre := Complex.re_le_norm (-deriv (logDeriv (DirichletCharacter.completedLFunction χ)) 0)
  rw [Complex.neg_re, norm_neg] at hre
  linarith [hre, hnormBound]

/--
Input/assumptions: `N ≥ 2`, `χ` primitive nontrivial quadratic mod `N`, GRH, `χ⁻¹ ≠ 1`.
Conclusion: `(logDeriv (completedLFunction χ) 0).re = -|Re B(χ)| - (1/2) log N`.
Content: `DirichletLFunction.primitiveBRe χ = (logDeriv F 0).re + (1/2) log N` (definition,
`χ.conductor = N` from
primitivity); `primitiveBRe_eq_neg_zeroMass_isQuadratic` and the zero-mass identity
(`abs_primitiveBRe_eq_zeroMass_isQuadratic`) together give `DirichletLFunction.primitiveBRe χ =
-|DirichletLFunction.primitiveBRe
χ|`; solve for `(logDeriv F 0).re`.
Role: the `s = 0` completed-`L` endpoint real part, common to both parities of a residue closed
form built from it.
-/
theorem completedLFunction_logDeriv_zero_re_eq_neg_abs_BRe_sub_half_log {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) :
    (logDeriv (DirichletCharacter.completedLFunction χ) 0).re =
      -|primitiveBRe χ| -
        (1 / 2) * Real.log N := by
  have hB := primitiveBRe_eq_neg_zeroMass_isQuadratic hN2 hGRH hprimitive hne hinv hquad
  have habs := abs_primitiveBRe_eq_zeroMass_isQuadratic hN2 hGRH hprimitive hne hinv hquad
  have hBneg :
    primitiveBRe χ =
      -|primitiveBRe χ| := by
    rw [habs, hB]
  have hBRe :
    primitiveBRe χ =
      (logDeriv (DirichletCharacter.completedLFunction χ) 0).re + (1 / 2) * Real.log N := by
    rw [primitiveBRe,
      (hprimitive : χ.conductor = N)]
  rw [hBneg] at hBRe
  linarith [hBRe]

/--
Input/assumptions: `N ≥ 2`, `χ` primitive nontrivial quadratic mod `N`, GRH, `χ⁻¹ ≠ 1`.
Conclusion: `(logDeriv (completedLFunction χ) 1).re = |Re B(χ)| - (1/2) log N`.
Content: the functional equation at `s = 0`
(`completedLFunction_logDeriv_functionalEquation_isQuadratic_at`, fed by `completedLFunction χ 0 ≠
0`) gives `logDeriv F 1 = -log N - logDeriv F 0`; take `.re` and substitute the `s = 0` value.
Role: the `s = 1` completed-`L` endpoint real part, common to both parities of a residue closed
form built from it.
-/
theorem completedLFunction_logDeriv_one_re_eq_abs_BRe_sub_half_log {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) :
    (logDeriv (DirichletCharacter.completedLFunction χ) 1).re =
      |primitiveBRe χ| -
        (1 / 2) * Real.log N := by
  have hF0ne :=
    dirichletCompletedLFunction_zero_ne_zero_of_primitive
      hprimitive hne
  have hFE :=
    completedLFunction_logDeriv_functionalEquation_isQuadratic_at hprimitive hne hquad hF0ne
  rw [sub_zero] at hFE
  have hFEre :
    -(logDeriv (DirichletCharacter.completedLFunction χ) 1).re =
      Real.log N + (logDeriv (DirichletCharacter.completedLFunction χ) 0).re := by
    have hlogNre : (Complex.log (N : ℂ)).re = Real.log N := by
      rw [show ((N : ℕ) : ℂ) = ((N : ℝ) : ℂ) from by
          push_cast; ring,
        Complex.log_ofReal_re]
    have := congrArg Complex.re hFE
    simpa only [Complex.neg_re, Complex.add_re, hlogNre] using this
  rw [completedLFunction_logDeriv_zero_re_eq_neg_abs_BRe_sub_half_log hN2 hGRH hprimitive hne hinv
      hquad] at hFEre
  linarith [hFEre]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
