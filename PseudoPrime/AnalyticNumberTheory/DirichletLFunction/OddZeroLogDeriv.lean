/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaFactorLogDeriv
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaFactorMultiplicityBridge
import PseudoPrime.AnalyticNumberTheory.Gamma.TrigammaSpecialValues

/-!
# Logarithmic derivatives of odd Dirichlet L-functions at zero

Pole-free neighborhoods and the completed-to-ordinary derivative comparison at the origin.
-/

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- A neighborhood of `0` avoiding every odd-character gamma-factor pole `(s+1)/2 = -m`
(`m : ℕ`), via the radius-`1` ball (all such poles have `‖s‖ = 2m + 1 ≥ 1`). -/
theorem eventually_half_ne_neg_nat_of_odd_near_zero :
    ∀ᶠ s : ℂ in nhds (0 : ℂ), ∀ m : ℕ, (s + 1) / 2 ≠ -(m : ℂ) := by
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (show (0 : ℝ) < 1 by norm_num only)] with s hs m hm
  rw [Metric.mem_ball, dist_zero_right] at hs
  have hre_bound : |s.re| ≤ ‖s‖ := Complex.abs_re_le_norm s
  have hre_gt : (-1 : ℝ) < s.re := by
    have := abs_lt.mp (hre_bound.trans_lt hs)
    linarith [this.1]
  have him := congrArg Complex.re hm
  simp only [Complex.add_re, Complex.one_re, Complex.div_ofNat_re, Complex.neg_re,
    Complex.natCast_re] at him
  have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

/--
Input/assumptions: `χ.Odd`.
Conclusion: `deriv (logDeriv (gammaFactor χ)) 0 = π² / 8`.
Content: `logDeriv (gammaFactor χ) =ᶠ[𝓝 0] (fun s ↦ -(log π)/2 + digamma((s+1)/2)/2)`
(`DirichletLFunction.logDeriv_gammaFactor_eq_of_odd_of_half_ne_neg_nat`,
valid on the pole-free neighborhood
`eventually_half_ne_neg_nat_of_odd_near_zero`); differentiate via `Filter.EventuallyEq.deriv_eq`,
then chain rule (`HasDerivAt.comp` with
`PseudoPrime.AnalyticNumberTheory.Gamma.deriv_digamma_half_eq = π²/2`) gives `(1/2) * (π²/2) *
(1/2) = π²/8`, accounting for both chain-rule factors.
Role: the new odd-parity special value feeding the log kernel's `s = 0` residue closed form.
-/
theorem deriv_logDeriv_gammaFactor_zero_of_odd {N : ℕ} {χ : DirichletCharacter ℂ N} (hodd : χ.Odd) :
    deriv (logDeriv (DirichletCharacter.gammaFactor χ)) 0 = (Real.pi : ℂ) ^ 2 / 8 := by
  have heqΓ :
    (logDeriv (DirichletCharacter.gammaFactor χ)) =ᶠ[nhds (0 : ℂ)]
      (fun s : ℂ => -(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma ((s + 1) / 2) / 2) := by
    filter_upwards [eventually_half_ne_neg_nat_of_odd_near_zero] with s hs
    exact
      logDeriv_gammaFactor_eq_of_odd_of_half_ne_neg_nat
        hodd hs
  rw [heqΓ.deriv_eq]
  have hpoint : ((0 : ℂ) + 1) / 2 = (1 / 2 : ℂ) := by norm_num only
  have h1 : HasDerivAt (fun s : ℂ => (s + 1) / 2) (1 / 2 : ℂ) 0 := by
    have ha : HasDerivAt (fun s : ℂ => s + 1) 1 0 := (hasDerivAt_id (0 : ℂ)).add_const 1
    simpa only [one_div] using ha.div_const (2 : ℂ)
  have h2 :
    HasDerivAt Complex.digamma (deriv Complex.digamma (((0 : ℂ) + 1) / 2)) (((0 : ℂ) + 1) / 2) := by
    rw [hpoint];
    exact Gamma.differentiableAt_digamma_half.hasDerivAt
  have h3 :=
    HasDerivAt.comp (h₂ := Complex.digamma) (h := fun s : ℂ => (s + 1) / 2) (x := (0 : ℂ)) h2 h1
  have h4 :
    HasDerivAt (fun s : ℂ => -(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma ((s + 1) / 2) / 2)
      ((deriv Complex.digamma (((0 : ℂ) + 1) / 2) * (1 / 2 : ℂ)) / 2) 0 := by
    have hconst : HasDerivAt (fun _ : ℂ => -(Complex.log (Real.pi : ℂ)) / 2) 0 0 :=
      hasDerivAt_const 0 _
    have hcomp :
      HasDerivAt (fun s : ℂ => Complex.digamma ((s + 1) / 2))
        (deriv Complex.digamma (((0 : ℂ) + 1) / 2) * (1 / 2 : ℂ)) 0 := by
      convert h3 using 1
      rfl
    have hadd := hconst.add (hcomp.div_const 2)
    have hfun :
      (fun _ : ℂ => -(Complex.log (Real.pi : ℂ)) / 2) +
          (fun s : ℂ => Complex.digamma ((s + 1) / 2) / 2) =
        fun s : ℂ => -(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma ((s + 1) / 2) / 2 := by
      funext s; rfl
    rw [hfun, zero_add] at hadd
    exact hadd
  rw [hpoint, Gamma.deriv_digamma_half_eq] at h4
  rw [h4.deriv]
  ring

/--
Input/assumptions: `N ≥ 1`, `χ` primitive nontrivial odd.
Conclusion: `logDeriv (LFunction χ) =ᶠ[𝓝 0] fun s ↦ logDeriv (completedLFunction χ) s -
logDeriv (gammaFactor χ) s`.
Content: `F 0 ≠ 0` and continuity give `F` nonzero eventually near `0`; the odd gamma-factor's
pole-free neighborhood (`eventually_half_ne_neg_nat_of_odd_near_zero`) gives `Γ_χ` nonzero and
differentiable eventually near `0`; `logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor_of_
regular` applies pointwise on the intersection.
Role: the eventual (not just pointwise-at-0) completed-to-ordinary bridge needed to differentiate
`logDeriv L` at `s = 0` via `Filter.EventuallyEq.deriv_eq`.
-/
theorem eventuallyEq_logDeriv_LFunction_zero_of_odd {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hodd : χ.Odd) :
    (logDeriv (DirichletCharacter.LFunction χ)) =ᶠ[nhds (0 : ℂ)]
      (fun s : ℂ =>
        logDeriv (DirichletCharacter.completedLFunction χ) s -
          logDeriv (DirichletCharacter.gammaFactor χ) s) := by
  have hF0ne :=
    dirichletCompletedLFunction_zero_ne_zero_of_primitive
      hprimitive hne
  have hFcont := (DirichletCharacter.differentiable_completedLFunction hne).continuous
  have hFev : ∀ᶠ s : ℂ in nhds (0 : ℂ), DirichletCharacter.completedLFunction χ s ≠ 0 :=
    hFcont.continuousAt.eventually_ne hF0ne
  filter_upwards [hFev, eventually_half_ne_neg_nat_of_odd_near_zero] with s hFs hhalf
  have hΓne : DirichletCharacter.gammaFactor χ s ≠ 0 :=
    gammaFactor_ne_zero_of_odd_of_half_ne_neg_nat
      hodd hhalf
  have hdΓ : DifferentiableAt ℂ (DirichletCharacter.gammaFactor χ) s :=
    differentiableAt_gammaFactor_of_odd_of_half_ne_neg_nat
      hodd hhalf
  exact
    logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor_of_regular
      hne hFs hΓne hdΓ

/--
Input/assumptions: `N ≥ 1`, `χ` primitive nontrivial odd.
Conclusion: `deriv (logDeriv (LFunction χ)) 0 = deriv (logDeriv (completedLFunction χ)) 0 -
π² / 8`.
Content: differentiate `eventuallyEq_logDeriv_LFunction_zero_of_odd` via
`Filter.EventuallyEq.deriv_eq`, then split the difference's derivative
(`deriv_sub`, both summands differentiable at `0`: `F` via entirety, `Γ_χ` via the pole-free
neighborhood) and substitute `deriv_logDeriv_gammaFactor_zero_of_odd`.
Role: expresses the derivative term in the logarithmic kernel's residue at zero through
`(logDeriv F)'(0)` and the gamma special value `π²/8`.
-/
theorem deriv_logDeriv_LFunction_zero_of_odd {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hodd : χ.Odd) :
    deriv (logDeriv (DirichletCharacter.LFunction χ)) 0 =
      deriv (logDeriv (DirichletCharacter.completedLFunction χ)) 0 - (Real.pi : ℂ) ^ 2 / 8 := by
  rw [(eventuallyEq_logDeriv_LFunction_zero_of_odd hprimitive hne hodd).deriv_eq]
  have hFdiff : DifferentiableAt ℂ (logDeriv (DirichletCharacter.completedLFunction χ)) 0 :=
    differentiableAt_logDeriv_completedLFunction_zero
      hprimitive hne
  have hΓdiff : DifferentiableAt ℂ (logDeriv (DirichletCharacter.gammaFactor χ)) 0 := by
    have hhalf : ∀ m : ℕ, ((0 : ℂ) + 1) / 2 ≠ -(m : ℂ) :=
      eventually_half_ne_neg_nat_of_odd_near_zero.self_of_nhds
    have hΓne : DirichletCharacter.gammaFactor χ 0 ≠ 0 :=
      gammaFactor_ne_zero_of_odd_of_half_ne_neg_nat
        hodd hhalf
    rw [logDeriv]
    exact
      (analyticAt_gammaFactor_of_ne_zero
            hΓne).deriv.differentiableAt.div
        (analyticAt_gammaFactor_of_ne_zero
            hΓne).differentiableAt
        hΓne
  rw [show
      (fun s : ℂ =>
          logDeriv (DirichletCharacter.completedLFunction χ) s -
            logDeriv (DirichletCharacter.gammaFactor χ) s) =
        logDeriv (DirichletCharacter.completedLFunction χ) -
          logDeriv (DirichletCharacter.gammaFactor χ)
      from rfl,
    deriv_sub hFdiff hΓdiff, deriv_logDeriv_gammaFactor_zero_of_odd hodd]

/--
Input/assumptions: `χ.Odd`.
Conclusion: `(logDeriv (gammaFactor χ) 0).re = -log π / 2 - γ / 2 - log 2`.
Content:
`DirichletLFunction.logDeriv_gammaFactor_eq_of_odd_of_half_ne_neg_nat`
at `s = 0` gives `-log π / 2 +
digamma (1/2) / 2`; `Complex.digamma_one_half` evaluates `digamma (1/2) = -2 log 2 - γ`; taking
`.re` strips the real casts (`Complex.log_ofReal_re`, `Complex.add_re`/`Complex.sub_re` etc).
Role: the `s = 0` half of the odd gamma-factor special-value input to the residue closed form
at zero.
-/
theorem logDeriv_gammaFactor_zero_re_of_odd {N : ℕ} {χ : DirichletCharacter ℂ N} (hodd : χ.Odd) :
    (logDeriv (DirichletCharacter.gammaFactor χ) 0).re =
      -Real.log Real.pi / 2 - Real.eulerMascheroniConstant / 2 - Real.log 2 := by
  have hhalf : ∀ m : ℕ, ((0 : ℂ) + 1) / 2 ≠ -(m : ℂ) := by
    intro m hm
    have him : (((0 : ℂ) + 1) / 2).re = (-(m : ℂ)).re := congrArg Complex.re hm
    simp only [zero_add, Complex.div_re] at him
    have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    simp only [Complex.one_re, Complex.re_ofNat, one_mul, Complex.normSq_ofNat, div_self_mul_self',
      Complex.one_im, Complex.im_ofNat, mul_zero, zero_div, add_zero, Complex.neg_re,
      Complex.natCast_re] at him
    linarith
  rw [logDeriv_gammaFactor_eq_of_odd_of_half_ne_neg_nat
      hodd hhalf,
    zero_add, Complex.digamma_one_half]
  have heq :
    -Complex.log (Real.pi : ℂ) / 2 + (-2 * Complex.log 2 - (Real.eulerMascheroniConstant : ℂ)) / 2 =
      ((-Real.log Real.pi / 2 - Real.eulerMascheroniConstant / 2 - Real.log 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_log Real.pi_nonneg,
      show (2 : ℂ) = ((2 : ℝ) : ℂ) from by simp only [Complex.ofReal_ofNat], ←
      Complex.ofReal_log (by norm_num only : (0 : ℝ) ≤ 2)]
    push_cast
    ring
  rw [heq, Complex.ofReal_re]

/--
Input/assumptions: `χ.Odd`.
Conclusion: `(logDeriv (gammaFactor χ) 1).re = -log π / 2 - γ / 2`.
Content:
`DirichletLFunction.logDeriv_gammaFactor_eq_of_odd_of_half_ne_neg_nat`
at `s = 1` gives `-log π / 2 +
digamma 1 / 2`; `Complex.digamma_one` evaluates `digamma 1 = -γ`.
Role: the `s = 1` half of the odd gamma-factor special-value input to the residue closed form
at one.
-/
theorem logDeriv_gammaFactor_one_re_of_odd {N : ℕ} {χ : DirichletCharacter ℂ N} (hodd : χ.Odd) :
    (logDeriv (DirichletCharacter.gammaFactor χ) 1).re =
      -Real.log Real.pi / 2 - Real.eulerMascheroniConstant / 2 := by
  have hhalf : ∀ m : ℕ, ((1 : ℂ) + 1) / 2 ≠ -(m : ℂ) := by
    intro m hm
    have him : (((1 : ℂ) + 1) / 2).re = (-(m : ℂ)).re := congrArg Complex.re hm
    have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    simp only [add_self_div_two, Complex.one_re, Complex.neg_re, Complex.natCast_re] at him
    linarith
  rw [logDeriv_gammaFactor_eq_of_odd_of_half_ne_neg_nat
      hodd hhalf,
    show ((1 : ℂ) + 1) / 2 = 1 from by norm_num only, Complex.digamma_one]
  have heq :
    -Complex.log (Real.pi : ℂ) / 2 + (-(Real.eulerMascheroniConstant : ℂ)) / 2 =
      ((-Real.log Real.pi / 2 - Real.eulerMascheroniConstant / 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_log Real.pi_nonneg]
    push_cast
    ring
  rw [heq, Complex.ofReal_re]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
