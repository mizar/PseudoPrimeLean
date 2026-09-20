/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.Basic
import PseudoPrime.AnalyticNumberTheory.Gamma.TrigammaSpecialValues
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaFactorMultiplicityBridge
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaFactorLogDeriv

/-!
# Even Dirichlet L-functions at zero

Canonical local factor, simple zero, and logarithmic derivative at the origin.
-/

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For a Dirichlet character `χ`, define `G_χ(s) := F(s, χ) / (2π · Γ_ℝ(s + 2))`.
For primitive nontrivial even characters this is the nonvanishing local factor of `L` at zero.
It is used to compute the zero multiplicity and logarithmic derivatives. -/
noncomputable def dirichletEvenZeroLocalFactor {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (s : ℂ) : ℂ :=
  DirichletCharacter.completedLFunction χ s / (2 * Real.pi * Complex.Gammaℝ (s + 2))

/-- `Γ_ℝ(2) ≠ 0`: `2` is not `-2n` for any `n : ℕ`. -/
theorem Gammaℝ_two_ne_zero : Complex.Gammaℝ 2 ≠ 0 := by
  intro h
  rw [Complex.Gammaℝ_eq_zero_iff] at h
  obtain ⟨n, hn⟩ := h
  have hre : (2 : ℂ).re = (-(2 * (n : ℂ))).re := congrArg Complex.re hn
  have hnnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  simp only [Complex.re_ofNat, Complex.neg_re, Complex.mul_re, Complex.natCast_re, Complex.im_ofNat,
    Complex.natCast_im, mul_zero, sub_zero] at hre
  linarith

/-- The even-zero local factor's denominator `2π · Γ_ℝ(s + 2)` is analytic and nonzero at `0`. -/
theorem analyticAt_evenZeroLocalFactor_denom :
    AnalyticAt ℂ (fun s : ℂ => 2 * (Real.pi : ℂ) * Complex.Gammaℝ (s + 2)) 0 ∧
      (2 * (Real.pi : ℂ) * Complex.Gammaℝ ((0 : ℂ) + 2)) ≠ 0 := by
  have hΓ2ne : Complex.Gammaℝ (2 : ℂ) ≠ 0 := Gammaℝ_two_ne_zero
  have hΓanalytic : AnalyticAt ℂ Complex.Gammaℝ ((0 : ℂ) + 2) := by
    rw [zero_add]; exact analyticAt_Gammaℝ_of_ne_zero hΓ2ne
  have hshift : AnalyticAt ℂ (fun s : ℂ => s + 2) 0 := by fun_prop
  have hcomp : AnalyticAt ℂ (fun s : ℂ => Complex.Gammaℝ (s + 2)) 0 :=
    AnalyticAt.comp (g := Complex.Gammaℝ) (f := fun s : ℂ => s + 2) hΓanalytic hshift
  refine ⟨(analyticAt_const).mul hcomp, ?_⟩
  simp only [zero_add]
  have hpine : (2 : ℂ) * (Real.pi : ℂ) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  exact mul_ne_zero hpine hΓ2ne

/--
Input/assumptions: `N ≥ 1`, `χ` primitive nontrivial mod `N`.
Conclusion: `AnalyticAt ℂ (dirichletEvenZeroLocalFactor χ) 0` and
`dirichletEvenZeroLocalFactor χ 0 ≠ 0`.
Content: `completedLFunction χ` is entire (globally differentiable); the denominator
`2π · Γ_ℝ(s + 2)` is analytic and nonzero at `0` (`analyticAt_evenZeroLocalFactor_denom`); the
numerator at `0` is `completedLFunction χ 0 ≠ 0`
(`DirichletLFunction.dirichletCompletedLFunction_zero_ne_zero_of_primitive`).
Role: the regularity input for `G_χ` feeding both the multiplicity-one identification and the
generic local derivative formula.
-/
theorem analyticAt_and_ne_zero_dirichletEvenZeroLocalFactor {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) :
    AnalyticAt ℂ (dirichletEvenZeroLocalFactor χ) 0 ∧ dirichletEvenZeroLocalFactor χ 0 ≠ 0 := by
  obtain ⟨hdenomAnalytic, hdenomNe⟩ := analyticAt_evenZeroLocalFactor_denom
  have hFanalytic : AnalyticAt ℂ (DirichletCharacter.completedLFunction χ) 0 :=
    (DirichletCharacter.differentiable_completedLFunction hne).analyticAt 0
  have hF0ne : DirichletCharacter.completedLFunction χ 0 ≠ 0 :=
    dirichletCompletedLFunction_zero_ne_zero_of_primitive hprimitive hne
  refine ⟨hFanalytic.div hdenomAnalytic hdenomNe, ?_⟩
  unfold dirichletEvenZeroLocalFactor
  exact div_ne_zero hF0ne hdenomNe

/--
Input/assumptions: `N ≥ 1`, `χ` primitive nontrivial even mod `N`.
Conclusion: `LFunction χ =ᶠ[𝓝 0] fun s ↦ s * dirichletEvenZeroLocalFactor χ s`.
Content: for `s ≠ 0`, `L(s) = F(s)/Γ_ℝ(s) = F(s) · s / (2π · Γ_ℝ(s+2)) = s · G_χ(s)` via
`Complex.Gammaℝ_add_two` (`Γ_ℝ(s+2) = Γ_ℝ(s) · s / 2 / π`, valid for `s ≠ 0`); at `s = 0`, both
sides vanish
(`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.dirichletLFunction_zero_of_even`).
Role: the local factorization identity used to identify the multiplicity as one and to compare
other analytic local factors with the canonical one.
-/
theorem eventuallyEq_dirichletLFunction_evenZeroLocalFactor {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (_hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (heven : χ.Even) :
    Filter.EventuallyEq (nhds (0 : ℂ)) (DirichletCharacter.LFunction χ)
      (fun s => s * dirichletEvenZeroLocalFactor χ s) := by
  have hΓ2ne : Complex.Gammaℝ (2 : ℂ) ≠ 0 := Gammaℝ_two_ne_zero
  have hcont : ContinuousAt (fun s : ℂ => Complex.Gammaℝ (s + 2)) 0 := by
    have hΓanalytic : AnalyticAt ℂ Complex.Gammaℝ ((0 : ℂ) + 2) := by
      rw [zero_add]; exact analyticAt_Gammaℝ_of_ne_zero hΓ2ne
    have hshift : AnalyticAt ℂ (fun s : ℂ => s + 2) 0 := by fun_prop
    exact
      (AnalyticAt.comp (g := Complex.Gammaℝ) (f := fun s : ℂ => s + 2) hΓanalytic
          hshift).continuousAt
  have hnear : ∀ᶠ s in nhds (0 : ℂ), Complex.Gammaℝ (s + 2) ≠ 0 := by
    have := hcont.eventually_ne (by simpa only [zero_add, ne_eq] using hΓ2ne)
    simpa only [ne_eq] using this
  have hL0 : DirichletCharacter.LFunction χ 0 = 0 := dirichletLFunction_zero_of_even hne heven
  filter_upwards [hnear] with s hΓsne
  rcases eq_or_ne s 0 with rfl | hs0
  · simp only [hL0, zero_mul]
  · unfold dirichletEvenZeroLocalFactor
    rw [dirichletLFunction_eq_completed_div_gammaFactor χ s
        (Or.inr (dirichletCharacter_level_ne_one_of_ne_one hne)),
      heven.gammaFactor_def]
    have hGE := Complex.Gammaℝ_add_two (s := s) hs0
    have hΓsne' : Complex.Gammaℝ s ≠ 0 := by
      intro h
      apply hΓsne
      rw [hGE, h]; ring
    have hdenomEq : 2 * (Real.pi : ℂ) * Complex.Gammaℝ (s + 2) = Complex.Gammaℝ s * s := by
      rw [hGE]; field_simp
    rw [hdenomEq]
    have hπne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp

/--
Input/assumptions: `N ≥ 1`, `χ` primitive nontrivial even mod `N`.
Conclusion: `PseudoPrime.AnalyticNumberTheory.DirichletLFunction.dirichletLFunctionZeroMultiplicity
χ 0 = 1`.
Content: `AnalyticAt.analyticOrderAt_eq_natCast` (mathlib, an iff) applied with `n := 1` and witness
`G_χ` (`eventuallyEq_dirichletLFunction_evenZeroLocalFactor`, `analyticAt_and_ne_zero_
dirichletEvenZeroLocalFactor`) directly gives `analyticOrderAt (LFunction χ) 0 = 1`; unfolding
`DirichletLFunction.dirichletLFunctionZeroMultiplicity`/`analyticOrderNatAt`
(`.toNat`) finishes.
Role: identifies the trivial zero at the origin as simple, for local expansions and residues.
-/
theorem dirichletLFunctionZeroMultiplicity_zero_of_primitive_even_eq_one {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (heven : χ.Even) :
    dirichletLFunctionZeroMultiplicity χ 0 = 1 := by
  have hLanalytic : AnalyticAt ℂ (DirichletCharacter.LFunction χ) 0 :=
    (DirichletCharacter.differentiable_LFunction hne).analyticAt 0
  obtain ⟨hGanalytic, hG0⟩ := analyticAt_and_ne_zero_dirichletEvenZeroLocalFactor hprimitive hne
  have heq := eventuallyEq_dirichletLFunction_evenZeroLocalFactor hprimitive hne heven
  have horder : analyticOrderAt (DirichletCharacter.LFunction χ) 0 = ((1 : ℕ) : ℕ∞) := by
    rw [hLanalytic.analyticOrderAt_eq_natCast]
    refine ⟨dirichletEvenZeroLocalFactor χ, hGanalytic, hG0, ?_⟩
    filter_upwards [heq] with s hs
    rw [hs]
    simp only [sub_zero, pow_one, smul_eq_mul]
  unfold dirichletLFunctionZeroMultiplicity analyticOrderNatAt
  rw [horder]
  simp only [Nat.cast_one, ENat.toNat_one]

/--
Input/assumptions: `N ≥ 1`, `χ` primitive nontrivial mod `N`.
Conclusion: `logDeriv G_χ 0 = logDeriv (completedLFunction χ) 0 + (log π + γ) / 2`.
Content: `G_χ = completedLFunction χ / (2π · Γ_ℝ(· + 2))`; `logDeriv` of a nonzero-constant multiple
drops the constant (`logDeriv_const_mul`), and `logDeriv (Γ_ℝ ∘ (· + 2)) 0 = logDeriv Γ_ℝ 2`
(`logDeriv_comp`, shift has derivative `1`), which equals `-log π / 2 + digamma 1 / 2 = -(log π +
γ) / 2` (`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.logDeriv_Gammaℝ_of_half_ne_neg_nat`
at `2`, `Complex.digamma_one`).
Role: supplies the local-factor special value used in the even residue formula.
-/
theorem logDeriv_dirichletEvenZeroLocalFactor_zero {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) :
    logDeriv (dirichletEvenZeroLocalFactor χ) 0 =
      logDeriv (DirichletCharacter.completedLFunction χ) 0 +
        (Complex.log (Real.pi : ℂ) + (Real.eulerMascheroniConstant : ℂ)) / 2 := by
  have hΓ2ne : Complex.Gammaℝ (2 : ℂ) ≠ 0 := Gammaℝ_two_ne_zero
  have hΓhalf : ∀ m : ℕ, (2 : ℂ) / 2 ≠ -(m : ℂ) := by
    intro m hm
    have him := congrArg Complex.re hm
    have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_self, Complex.one_re,
      Complex.neg_re, Complex.natCast_re] at him
    linarith only [him, hmnn]
  have hΓdiff : DifferentiableAt ℂ Complex.Gammaℝ (2 : ℂ) :=
    differentiableAt_Gammaℝ_of_half_ne_neg_nat hΓhalf
  have hshiftDeriv : HasDerivAt (fun s : ℂ => s + 2) 1 0 := by
    simpa only [hasDerivAt_add_const_iff, id_eq] using (hasDerivAt_id (0 : ℂ)).add_const (2 : ℂ)
  have hΓshiftDiff : DifferentiableAt ℂ (fun s : ℂ => Complex.Gammaℝ (s + 2)) 0 := by
    rw [show (fun s : ℂ => Complex.Gammaℝ (s + 2)) = Complex.Gammaℝ ∘ fun s : ℂ => s + 2 from rfl]
    exact
      DifferentiableAt.comp 0
        (by
          rw [zero_add]; exact hΓdiff)
        hshiftDeriv.differentiableAt
  have hFanalytic : AnalyticAt ℂ (DirichletCharacter.completedLFunction χ) 0 :=
    (DirichletCharacter.differentiable_completedLFunction hne).analyticAt 0
  have hF0ne : DirichletCharacter.completedLFunction χ 0 ≠ 0 :=
    dirichletCompletedLFunction_zero_ne_zero_of_primitive hprimitive hne
  have hDdiff : DifferentiableAt ℂ (fun s : ℂ => 2 * (Real.pi : ℂ) * Complex.Gammaℝ (s + 2)) 0 :=
    (differentiableAt_const _).mul hΓshiftDiff
  have hπne : (2 : ℂ) * (Real.pi : ℂ) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hD0ne : 2 * (Real.pi : ℂ) * Complex.Gammaℝ ((0 : ℂ) + 2) ≠ 0 := by
    rw [zero_add]; exact mul_ne_zero hπne hΓ2ne
  have hdiv := logDeriv_div (0 : ℂ) hF0ne hD0ne hFanalytic.differentiableAt hDdiff
  have hGeq :
    dirichletEvenZeroLocalFactor χ = fun s =>
      DirichletCharacter.completedLFunction χ s / (2 * (Real.pi : ℂ) * Complex.Gammaℝ (s + 2)) :=
    rfl
  rw [hGeq,
    show
      (fun s : ℂ =>
          DirichletCharacter.completedLFunction χ s /
            (2 * (Real.pi : ℂ) * Complex.Gammaℝ (s + 2))) =
        DirichletCharacter.completedLFunction χ /
          (fun s : ℂ => 2 * (Real.pi : ℂ) * Complex.Gammaℝ (s + 2))
      from by
      funext s
      rfl,
    hdiv]
  have hDlogDeriv :
    logDeriv (fun s : ℂ => 2 * (Real.pi : ℂ) * Complex.Gammaℝ (s + 2)) 0 =
      logDeriv (fun s : ℂ => Complex.Gammaℝ (s + 2)) 0 :=
    logDeriv_const_mul 0 (2 * (Real.pi : ℂ)) hπne
  rw [hDlogDeriv]
  have hcomp :=
    logDeriv_comp (f := Complex.Gammaℝ) (g := fun s : ℂ => s + 2) (x := (0 : ℂ))
      (by
        rw [zero_add]; exact hΓdiff)
      hshiftDeriv.differentiableAt
  have heqfun : (fun s : ℂ => Complex.Gammaℝ (s + 2)) = Complex.Gammaℝ ∘ fun s : ℂ => s + 2 := rfl
  rw [heqfun, hcomp, hshiftDeriv.deriv, mul_one, zero_add]
  have hΓ2logDeriv :
    logDeriv Complex.Gammaℝ (2 : ℂ) =
      -Complex.log (Real.pi : ℂ) / 2 + Complex.digamma ((2 : ℂ) / 2) / 2 :=
    logDeriv_Gammaℝ_of_half_ne_neg_nat hΓhalf
  rw [hΓ2logDeriv]
  norm_num only
  rw [Complex.digamma_one]
  ring

/--
Input/assumptions: `N ≥ 1`, `χ` primitive nontrivial mod `N`.
Conclusion: `(logDeriv G_χ)'(0) = (logDeriv F)'(0) - π² / 24`.
Content: mirrors `logDeriv_dirichletEvenZeroLocalFactor_zero`'s value computation, upgraded to an
eventual (not just pointwise-at-`0`) identity `logDeriv G_χ =ᶠ[𝓝 0] logDeriv F - logDeriv D`
(`D(s) := 2π·Γ_ℝ(s + 2)`, nonzero eventually near `0` by continuity from `Γ_ℝ(2) ≠ 0`) so
`Filter.EventuallyEq.deriv_eq` applies; `deriv (logDeriv D) 0 = deriv (logDeriv Γ_ℝ) 2` (chain rule,
shift derivative `1`), computed via `logDeriv Γ_ℝ(s) = -log π/2 + digamma(s/2)/2`
(`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.logDeriv_Gammaℝ_of_half_ne_neg_nat`)
differentiated at `s = 2` (chain rule, inner derivative
`1/2`, `PseudoPrime.AnalyticNumberTheory.Gamma.deriv_digamma_one_eq = π²/6`), giving
`(1/2)·(1/2)·(π²/6) = π²/24`.
Role: supplies the local-factor derivative used in the even residue formula. The odd gamma
factor instead contributes `π²/8`, through digamma at `1/2`.
-/
theorem deriv_logDeriv_dirichletEvenZeroLocalFactor_zero {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) :
    deriv (logDeriv (dirichletEvenZeroLocalFactor χ)) 0 =
      deriv (logDeriv (DirichletCharacter.completedLFunction χ)) 0 - (Real.pi : ℂ) ^ 2 / 24 := by
  have hhalf_near : ∀ᶠ s : ℂ in nhds (0 : ℂ), ∀ m : ℕ, (s + 2) / 2 ≠ -(m : ℂ) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (show (0 : ℝ) < 1 by norm_num only)] with s hs m hm
    rw [Metric.mem_ball, dist_zero_right] at hs
    have hre_bound : |s.re| ≤ ‖s‖ := Complex.abs_re_le_norm s
    have hre_gt : (-1 : ℝ) < s.re := by
      have := abs_lt.mp (hre_bound.trans_lt hs); linarith [this.1]
    have him := congrArg Complex.re hm
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.neg_re, Complex.natCast_re] at him
    have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have h2re : Complex.re (2 : ℂ) = 2 := by rfl
    rw [h2re] at him
    linarith
  have hΓne : ∀ᶠ s in nhds (0 : ℂ), Complex.Gammaℝ (s + 2) ≠ 0 := by
    filter_upwards [hhalf_near] with s hs
    exact Gammaℝ_ne_zero_of_half_ne_neg_nat hs
  have hΓdiff :
    ∀ᶠ s in nhds (0 : ℂ), DifferentiableAt ℂ (fun t : ℂ => Complex.Gammaℝ (t + 2)) s := by
    filter_upwards [hhalf_near] with s hs
    exact (differentiableAt_Gammaℝ_of_half_ne_neg_nat hs).comp s ((differentiableAt_id).add_const 2)
  have hπne : (2 : ℂ) * (Real.pi : ℂ) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hDne : ∀ᶠ s in nhds (0 : ℂ), 2 * (Real.pi : ℂ) * Complex.Gammaℝ (s + 2) ≠ 0 := by
    filter_upwards [hΓne] with s hs
    exact mul_ne_zero hπne hs
  have hDdiff :
    ∀ᶠ s in nhds (0 : ℂ),
      DifferentiableAt ℂ (fun t : ℂ => 2 * (Real.pi : ℂ) * Complex.Gammaℝ (t + 2)) s := by
    filter_upwards [hΓdiff] with s hs
    exact (differentiableAt_const _).mul hs
  have hFdiff := DirichletCharacter.differentiable_completedLFunction hne
  have hF0ne := dirichletCompletedLFunction_zero_ne_zero_of_primitive hprimitive hne
  have hFne_ev : ∀ᶠ s in nhds (0 : ℂ), DirichletCharacter.completedLFunction χ s ≠ 0 :=
    hFdiff.continuous.continuousAt.eventually_ne hF0ne
  have hqeq :
    logDeriv (dirichletEvenZeroLocalFactor χ) =ᶠ[nhds (0 : ℂ)]
      (fun s =>
        logDeriv (DirichletCharacter.completedLFunction χ) s -
          logDeriv (fun t : ℂ => 2 * (Real.pi : ℂ) * Complex.Gammaℝ (t + 2)) s) := by
    filter_upwards [hDne, hDdiff, hFne_ev] with s hDs hDdiffs hFs
    change
      logDeriv
          (fun t =>
            DirichletCharacter.completedLFunction χ t /
              (2 * (Real.pi : ℂ) * Complex.Gammaℝ (t + 2)))
          s =
        _
    rw [show
        (fun t : ℂ =>
            DirichletCharacter.completedLFunction χ t /
              (2 * (Real.pi : ℂ) * Complex.Gammaℝ (t + 2))) =
          DirichletCharacter.completedLFunction χ /
            (fun t : ℂ => 2 * (Real.pi : ℂ) * Complex.Gammaℝ (t + 2))
        from by
        funext t
        rfl,
      logDeriv_div s hFs hDs (hFdiff s) hDdiffs]
  have hderivEq :
    deriv (logDeriv (dirichletEvenZeroLocalFactor χ)) 0 =
      deriv
        (fun s =>
          logDeriv (DirichletCharacter.completedLFunction χ) s -
            logDeriv (fun t : ℂ => 2 * (Real.pi : ℂ) * Complex.Gammaℝ (t + 2)) s)
        0 :=
    hqeq.deriv_eq
  rw [hderivEq]
  have hFanalytic0 : AnalyticAt ℂ (DirichletCharacter.completedLFunction χ) 0 := hFdiff.analyticAt 0
  have hDlogDeriv_ev :
    (fun s => logDeriv (fun t : ℂ => 2 * (Real.pi : ℂ) * Complex.Gammaℝ (t + 2)) s) =ᶠ[nhds (0 : ℂ)]
      (fun s => logDeriv (fun t : ℂ => Complex.Gammaℝ (t + 2)) s) := by
    filter_upwards [hΓne] with s hs
    exact logDeriv_const_mul s (2 * (Real.pi : ℂ)) hπne
  have hFqdiff : DifferentiableAt ℂ (logDeriv (DirichletCharacter.completedLFunction χ)) 0 :=
    differentiableAt_logDeriv_completedLFunction_zero hprimitive hne
  have hDqdiff :
    DifferentiableAt ℂ
      (fun s => logDeriv (fun t : ℂ => 2 * (Real.pi : ℂ) * Complex.Gammaℝ (t + 2)) s) 0 := by
    have hΓ2ne : Complex.Gammaℝ (2 : ℂ) ≠ 0 := Gammaℝ_two_ne_zero
    have hΓhalf : ∀ m : ℕ, (2 : ℂ) / 2 ≠ -(m : ℂ) := by
      intro m hm
      have him := congrArg Complex.re hm
      have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_self, Complex.one_re,
        Complex.neg_re, Complex.natCast_re] at him;
      linarith
    have hΓanalytic2 : AnalyticAt ℂ Complex.Gammaℝ (2 : ℂ) := analyticAt_Gammaℝ_of_ne_zero hΓ2ne
    have hshiftAnalytic : AnalyticAt ℂ (fun t : ℂ => t + 2) 0 := by fun_prop
    have hcompAnalytic : AnalyticAt ℂ (fun t : ℂ => Complex.Gammaℝ (t + 2)) 0 := by
      have : AnalyticAt ℂ Complex.Gammaℝ ((0 : ℂ) + 2) := by
        rw [zero_add]; exact hΓanalytic2
      exact AnalyticAt.comp (g := Complex.Gammaℝ) (f := fun t : ℂ => t + 2) this hshiftAnalytic
    have hDshiftne : Complex.Gammaℝ ((0 : ℂ) + 2) ≠ 0 := by
      rw [zero_add]; exact hΓ2ne
    have hlogGamma : AnalyticAt ℂ (logDeriv (fun t : ℂ => Complex.Gammaℝ (t + 2))) 0 := by
      rw [logDeriv]
      exact hcompAnalytic.deriv.div hcompAnalytic hDshiftne
    have hlogGammaDiff := hlogGamma.differentiableAt
    have heq2 :
      (fun s =>
          logDeriv (fun t : ℂ => 2 * (Real.pi : ℂ) * Complex.Gammaℝ (t + 2)) s) =ᶠ[nhds (0 : ℂ)]
        logDeriv (fun t : ℂ => Complex.Gammaℝ (t + 2)) :=
      hDlogDeriv_ev
    exact heq2.differentiableAt_iff.mpr hlogGammaDiff
  have hraw2 := deriv_sub hFqdiff hDqdiff
  have hfunSub :
    logDeriv (DirichletCharacter.completedLFunction χ) -
        (fun s => logDeriv (fun t : ℂ => 2 * (Real.pi : ℂ) * Complex.Gammaℝ (t + 2)) s) =
      fun s =>
      logDeriv (DirichletCharacter.completedLFunction χ) s -
        logDeriv (fun t : ℂ => 2 * (Real.pi : ℂ) * Complex.Gammaℝ (t + 2)) s := by
    funext s; rfl
  rw [hfunSub] at hraw2
  rw [hraw2, hDlogDeriv_ev.deriv_eq]
  have hshiftDeriv2 : HasDerivAt (fun t : ℂ => t + 2) 1 0 := by
    simpa only [hasDerivAt_add_const_iff, id_eq] using (hasDerivAt_id (0 : ℂ)).add_const (2 : ℂ)
  have hpoint2 : ((0 : ℂ) + 2) / 2 = (1 : ℂ) := by norm_num only
  have h2 :
    HasDerivAt Complex.digamma (deriv Complex.digamma (((0 : ℂ) + 2) / 2)) (((0 : ℂ) + 2) / 2) := by
    rw [hpoint2]; exact Gamma.differentiableAt_digamma_one.hasDerivAt
  have hhalf_deriv : HasDerivAt (fun t : ℂ => t / 2) (1 / 2 : ℂ) ((0 : ℂ) + 2) := by
    simpa only [one_div, zero_add, id_eq] using (hasDerivAt_id ((0 : ℂ) + 2)).div_const (2 : ℂ)
  have h3 :=
    HasDerivAt.comp (h₂ := Complex.digamma) (h := fun t : ℂ => t / 2) (x := (0 : ℂ) + 2) h2
      hhalf_deriv
  have hcompDigamma :
    HasDerivAt (fun t : ℂ => Complex.digamma (t / 2))
      (deriv Complex.digamma (((0 : ℂ) + 2) / 2) * (1 / 2 : ℂ)) ((0 : ℂ) + 2) := by
    convert h3 using 1
    rfl
  have hcompShift :=
    HasDerivAt.comp (h₂ := fun t : ℂ => Complex.digamma (t / 2)) (h := fun s : ℂ => s + 2) (x :=
      (0 : ℂ)) hcompDigamma hshiftDeriv2
  have hcompShift' :
    HasDerivAt (fun s : ℂ => Complex.digamma ((s + 2) / 2))
      (deriv Complex.digamma (((0 : ℂ) + 2) / 2) * (1 / 2 : ℂ) * 1) 0 := by
    convert hcompShift using 1
    rfl
  have hΓRlog_ev :
    (fun s : ℂ => logDeriv (fun t : ℂ => Complex.Gammaℝ (t + 2)) s) =ᶠ[nhds (0 : ℂ)]
      (fun s : ℂ => -(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma ((s + 2) / 2) / 2) := by
    filter_upwards [hhalf_near] with s hs
    have hcomp :=
      logDeriv_comp (f := Complex.Gammaℝ) (g := fun t : ℂ => t + 2) (x := s)
        (differentiableAt_Gammaℝ_of_half_ne_neg_nat hs) ((differentiableAt_id).add_const 2)
    have heqfun : (fun t : ℂ => Complex.Gammaℝ (t + 2)) = Complex.Gammaℝ ∘ fun t : ℂ => t + 2 := rfl
    rw [heqfun, hcomp]
    have hshiftDerivS : deriv (fun t : ℂ => t + 2) s = 1 := by
      simp only [differentiableAt_fun_id, differentiableAt_const, deriv_fun_add, deriv_id'',
        deriv_const', add_zero]
    rw [hshiftDerivS, mul_one]
    exact logDeriv_Gammaℝ_of_half_ne_neg_nat hs
  rw [hΓRlog_ev.deriv_eq]
  have hconstDeriv : HasDerivAt (fun _ : ℂ => -(Complex.log (Real.pi : ℂ)) / 2) 0 0 :=
    hasDerivAt_const 0 _
  have hfinal := (hconstDeriv.add (hcompShift'.div_const 2))
  rw [hpoint2, Gamma.deriv_digamma_one_eq] at hfinal
  have hfunFinal :
    (fun _ : ℂ => -(Complex.log (Real.pi : ℂ)) / 2) +
        (fun t : ℂ => Complex.digamma ((t + 2) / 2) / 2) =
      fun s : ℂ => -(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma ((s + 2) / 2) / 2 := by
    funext s; rfl
  rw [hfunFinal] at hfinal
  rw [hfinal.deriv]
  ring

/--
Input/assumptions: `χ.Even`.
Conclusion: `(logDeriv (gammaFactor χ) 1).re = -log π / 2 - γ / 2 - log 2`.
Content:
`DirichletLFunction.logDeriv_gammaFactor_eq_of_even_of_half_ne_neg_nat`
at `s = 1` gives `-log π / 2 +
digamma (1/2) / 2`; `Complex.digamma_one_half` evaluates `digamma (1/2) = -2 log 2 - γ`. The exact
mirror of `logDeriv_gammaFactor_zero_re_of_odd` (odd `s = 0` and even `s = 1` both land on
`digamma (1/2)`).
Role: supplies the even gamma-factor value at one for the sum of endpoint residues.
-/
theorem logDeriv_gammaFactor_one_re_of_even {N : ℕ} {χ : DirichletCharacter ℂ N} (heven : χ.Even) :
    (logDeriv (DirichletCharacter.gammaFactor χ) 1).re =
      -Real.log Real.pi / 2 - Real.eulerMascheroniConstant / 2 - Real.log 2 := by
  have hhalf : ∀ m : ℕ, (1 : ℂ) / 2 ≠ -(m : ℂ) := by
    intro m hm
    have him := congrArg Complex.re hm
    have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    simp only [one_div, Complex.inv_re, Complex.re_ofNat, Complex.normSq_ofNat, div_self_mul_self',
      Complex.neg_re, Complex.natCast_re] at him
    linarith only [him, hmnn]
  rw [logDeriv_gammaFactor_eq_of_even_of_half_ne_neg_nat heven hhalf, Complex.digamma_one_half]
  have heq :
    -Complex.log (Real.pi : ℂ) / 2 + (-2 * Complex.log 2 - (Real.eulerMascheroniConstant : ℂ)) / 2 =
      ((-Real.log Real.pi / 2 - Real.eulerMascheroniConstant / 2 - Real.log 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_log Real.pi_nonneg,
      show (2 : ℂ) = ((2 : ℝ) : ℂ) from by
        norm_num only [Complex.ext_iff, Complex.ofReal_ofNat, Nat.cast_ofNat],
      ← Complex.ofReal_log (by norm_num only : (0 : ℝ) ≤ 2)]
    push_cast
    ring
  rw [heq, Complex.ofReal_re]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
