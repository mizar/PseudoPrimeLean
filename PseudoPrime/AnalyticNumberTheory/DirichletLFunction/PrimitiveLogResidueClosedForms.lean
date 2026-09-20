/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveResidueClosedForms
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveEvenZeroLocalFactor
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.QuadraticFunctionalConsequences
import PseudoPrime.AnalyticNumberTheory.Gamma.TrigammaSpecialValues
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.OddZeroLogDeriv
import PseudoPrime.AnalyticNumberTheory.General.PoleResidueCalculus

/-!
# Closed forms for logarithmic-kernel residues at zero

For a primitive nontrivial odd character, the double-pole regularization of
`-(L'/L)(s)*x^s/s²` gives `-(logDeriv L)'(0)-logDeriv L(0)*log x`.
For the even branch, the canonical local factor gives a cubic-pole regularization,
whose residue is half its second derivative. The completed-function bridge and
gamma-factor special values express both formulas using completed logarithmic derivatives.
-/

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/--
Input/assumptions: `N ≥ 1`, `χ` primitive nontrivial odd mod `N`, `x > 0`.
Conclusion: `deriv
(PseudoPrime.AnalyticNumberTheory.DirichletLFunction.dirichletLogMellinZeroRegularization x χ) 0 =
-(deriv (logDeriv L) 0) - logDeriv L 0 * log x`.
Content: product rule (`HasDerivAt.mul`) on
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.dirichletLogMellinZeroRegularization x χ s =
-(logDeriv L s) * x^s`, with `deriv (x^·) 0 = log x` (`HasDerivAt.const_cpow`) and `x^0 = 1`.
`logDeriv L` is differentiable at `0` since `L` is entire and `L(0,χ) ≠ 0` for odd `χ`
(`DirichletLFunction.dirichletLFunction_zero_ne_zero_of_primitive_odd`).
Role: the product-rule half of the odd `s = 0` log-kernel residue — the "hard" completed-`L`
substitution is deferred to the next theorem.
-/
theorem deriv_dirichletLogMellinZeroRegularization_zero_of_odd_eq {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hodd : χ.Odd) {x : ℝ}
    (hx : 0 < x) :
    deriv (dirichletLogMellinZeroRegularization x χ) 0 =
      -(deriv (logDeriv (DirichletCharacter.LFunction χ)) 0) -
        logDeriv (DirichletCharacter.LFunction χ) 0 * Complex.log x := by
  have hxne : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hL0ne : DirichletCharacter.LFunction χ 0 ≠ 0 :=
    dirichletLFunction_zero_ne_zero_of_primitive_odd hprimitive hne hodd
  have hLanalytic : AnalyticAt ℂ (DirichletCharacter.LFunction χ) 0 :=
    (DirichletCharacter.differentiable_LFunction hne).analyticAt 0
  have hLdiff : DifferentiableAt ℂ (logDeriv (DirichletCharacter.LFunction χ)) 0 :=
    (hLanalytic.deriv.div hLanalytic hL0ne).differentiableAt
  have hL :
    HasDerivAt (logDeriv (DirichletCharacter.LFunction χ))
      (deriv (logDeriv (DirichletCharacter.LFunction χ)) 0) 0 :=
    hLdiff.hasDerivAt
  have hNegL :
    HasDerivAt (fun s : ℂ => -(logDeriv (DirichletCharacter.LFunction χ) s))
      (-(deriv (logDeriv (DirichletCharacter.LFunction χ)) 0)) 0 :=
    hL.neg
  have hxpow : HasDerivAt (fun s : ℂ => (x : ℂ) ^ s) (Complex.log x) 0 := by
    have h1 := (hasDerivAt_id (0 : ℂ)).const_cpow (c := (x : ℂ)) (Or.inl hxne)
    simpa only [id_eq, Complex.cpow_zero, one_mul, mul_one] using h1
  have hprod := hNegL.mul hxpow
  have hfun :
    dirichletLogMellinZeroRegularization x χ = fun s : ℂ =>
      -(logDeriv (DirichletCharacter.LFunction χ) s) * (x : ℂ) ^ s := by
    funext s
    rw [dirichletLogMellinZeroRegularization, logDeriv_apply]
  rw [hfun]
  have hval := hprod.deriv
  rw [show
      (fun s : ℂ => -(logDeriv (DirichletCharacter.LFunction χ) s)) * (fun s : ℂ => (x : ℂ) ^ s) =
        fun s : ℂ => -(logDeriv (DirichletCharacter.LFunction χ) s) * (x : ℂ) ^ s
      from rfl] at hval
  rw [hval]
  simp only [Complex.cpow_zero, mul_one]
  ring

/--
Input/assumptions: `N ≥ 1`, `χ` primitive nontrivial odd mod `N`, `x > 0`.
Conclusion:
`deriv (PseudoPrime.AnalyticNumberTheory.DirichletLFunction.dirichletLogMellinZeroRegularization x
χ) 0 = -(deriv (logDeriv F) 0) + π²/8 -
(logDeriv F 0 - logDeriv Γ_χ 0) * log x`.
Content: substitute
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.deriv_logDeriv_LFunction_zero_of_odd` (the
`deriv(logDeriv L)0` term) and the
pointwise completed-to-ordinary bridge at `s = 0`
(`DirichletLFunction.logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor_of_regular`)
into the product-rule
closed form.
Role: the fully completed-side raw closed form for the odd `s = 0` log-kernel residue.
-/
theorem deriv_dirichletLogMellinZeroRegularization_zero_of_odd_raw {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hodd : χ.Odd) {x : ℝ}
    (hx : 0 < x) :
    deriv (dirichletLogMellinZeroRegularization x χ) 0 =
      -(deriv (logDeriv (DirichletCharacter.completedLFunction χ)) 0) + (Real.pi : ℂ) ^ 2 / 8 -
        (logDeriv (DirichletCharacter.completedLFunction χ) 0 -
            logDeriv (DirichletCharacter.gammaFactor χ) 0) *
          Complex.log x := by
  rw [deriv_dirichletLogMellinZeroRegularization_zero_of_odd_eq hprimitive hne hodd hx,
    deriv_logDeriv_LFunction_zero_of_odd hprimitive hne hodd]
  have hΓ0ne : DirichletCharacter.gammaFactor χ 0 ≠ 0 :=
    gammaFactor_ne_zero_of_odd_of_half_ne_neg_nat hodd
      (by
        intro m hm
        have him := congrArg Complex.re hm
        simp only [zero_add] at him
        have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        simp only [one_div, Complex.inv_re, Complex.re_ofNat, Complex.normSq_ofNat,
          div_self_mul_self', Complex.neg_re, Complex.natCast_re] at him;
        linarith)
  have hdΓ0 : DifferentiableAt ℂ (DirichletCharacter.gammaFactor χ) 0 :=
    differentiableAt_gammaFactor_of_odd_of_half_ne_neg_nat hodd
      (by
        intro m hm
        have him := congrArg Complex.re hm
        simp only [zero_add] at him
        have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        simp only [one_div, Complex.inv_re, Complex.re_ofNat, Complex.normSq_ofNat,
          div_self_mul_self', Complex.neg_re, Complex.natCast_re] at him;
        linarith)
  have hF0ne := dirichletCompletedLFunction_zero_ne_zero_of_primitive hprimitive hne
  have hbridge0 :=
    logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor_of_regular hne hF0ne hΓ0ne hdΓ0
  rw [hbridge0]
  ring

/--
Input/assumptions: `N ≥ 2`, `χ` primitive nontrivial quadratic odd mod `N`, GRH, `χ⁻¹ ≠ 1`,
`x > 0`.
Conclusion:
`Re(residue) = -Re(deriv(logDeriv F) 0) + |Re B(χ)| log x + (1/2)(log N - log π) log x + π²/8 -
(log 2 + γ/2) log x`.
Content: take `.re` of
`DirichletLFunction.deriv_dirichletLogMellinZeroRegularization_zero_of_odd_raw`,
substituting
(F0)
(`DirichletLFunction.completedLFunction_logDeriv_zero_re_eq_neg_abs_BRe_sub_half_log`)
and (G0)
(`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.logDeriv_gammaFactor_zero_re_of_odd`);
`Complex.log x = ((log x : ℝ) : ℂ)` for `x > 0`
(`Complex.ofReal_log`) lets `Complex.re_ofReal_mul` extract the product's real part.
Role: gives the odd `s = 0` log-kernel residue's real part, keeping
`Re(deriv(logDeriv F) 0)` symbolic (bounded by `2|Re B(χ)|` separately) so the completed-side
derivative bound from `QuadraticFunctionalConsequences` can be substituted later.
-/
theorem re_deriv_dirichletLogMellinZeroRegularization_zero_of_odd_raw {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic)
    (hodd : χ.Odd) {x : ℝ} (hx : 0 < x) :
    (deriv (dirichletLogMellinZeroRegularization x χ) 0).re =
      -(deriv (logDeriv (DirichletCharacter.completedLFunction χ)) 0).re +
          |primitiveBRe χ| * Real.log x +
          (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x +
          (Real.pi : ℝ) ^ 2 / 8 -
        (Real.log 2 + Real.eulerMascheroniConstant / 2) * Real.log x := by
  rw [deriv_dirichletLogMellinZeroRegularization_zero_of_odd_raw hprimitive hne hodd hx]
  have hF0re :=
    completedLFunction_logDeriv_zero_re_eq_neg_abs_BRe_sub_half_log hN2 hGRH hprimitive hne hinv
      hquad
  have hG0re := logDeriv_gammaFactor_zero_re_of_odd hodd
  have hlogxC : Complex.log (x : ℂ) = ((Real.log x : ℝ) : ℂ) := (Complex.ofReal_log hx.le).symm
  have hAre :
    ((logDeriv (DirichletCharacter.completedLFunction χ) 0 -
            logDeriv (DirichletCharacter.gammaFactor χ) 0) *
          Complex.log (x : ℂ)).re =
      ((logDeriv (DirichletCharacter.completedLFunction χ) 0).re -
          (logDeriv (DirichletCharacter.gammaFactor χ) 0).re) *
        Real.log x := by
    rw [hlogxC, mul_comm, Complex.re_ofReal_mul, Complex.sub_re, mul_comm]
  have hpi8re : ((Real.pi : ℂ) ^ 2 / 8).re = (Real.pi : ℝ) ^ 2 / 8 := by
    rw [show ((Real.pi : ℂ) ^ 2 / 8) = (((Real.pi : ℝ) ^ 2 / 8 : ℝ) : ℂ) from by
        push_cast; ring,
      Complex.ofReal_re]
  rw [Complex.sub_re, Complex.add_re, Complex.neg_re, hpi8re, hAre, hF0re, hG0re]
  ring

/-! ### The even-character logarithmic-kernel residue at zero -/

/--
Input/assumptions: `N ≥ 1`, `χ` primitive nontrivial even mod `N`, `x : ℝ`.
Conclusion: `(s - 0) ^ 3 * K_log(s) =ᶠ[𝓝[≠] 0]
PseudoPrime.AnalyticNumberTheory.DirichletLFunction.dirichletLogEvenZeroRegularization x 1 G_χ`.
Content: mirrors
`DirichletLFunction.eventuallyEq_dirichletReciprocalEvenZeroRegularization_canonical`
exactly:
`logDeriv_congr_nhds` on `L =ᶠ[𝓝 0] fun s ↦ s · G_χ(s)`
(`eventuallyEq_dirichletLFunction_evenZeroLocalFactor`) plus `logDeriv_mul` gives `L'/L(s) = 1/s +
logDeriv G_χ(s)` on a punctured neighborhood; substituting into `s³ K_log(s) = -s·(L'/L)(s)·x^s`
and clearing denominators (`field_simp`) gives `-(1 + s·logDeriv G_χ(s))·x^s`, matching the
regularization at `m = 1` exactly (no `s - 1` factor, unlike the reciprocal kernel).
Role: the canonical-factor identity, letting the even log residue be computed directly from `G_χ`
without ever inspecting the witness selected by `Classical.choose`.
-/
theorem eventuallyEq_dirichletLogEvenZeroRegularization_canonical {N : ℕ} [NeZero N] {x : ℝ}
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (heven : χ.Even) :
    Filter.EventuallyEq (nhdsWithin (0 : ℂ) ({0}ᶜ : Set ℂ))
      (fun s => (s - 0) ^ 3 * dirichletLogContourKernel x χ s)
      (dirichletLogEvenZeroRegularization x 1 (dirichletEvenZeroLocalFactor χ)) := by
  obtain ⟨hGanalytic, hG0⟩ := analyticAt_and_ne_zero_dirichletEvenZeroLocalFactor hprimitive hne
  have heq := eventuallyEq_dirichletLFunction_evenZeroLocalFactor hprimitive hne heven
  have hlogeq := logDeriv_congr_nhds heq
  have hGnear : ∀ᶠ s in nhds (0 : ℂ), dirichletEvenZeroLocalFactor χ s ≠ 0 :=
    hGanalytic.continuousAt.eventually_ne hG0
  filter_upwards [hlogeq.filter_mono nhdsWithin_le_nhds, hGnear.filter_mono nhdsWithin_le_nhds,
    eventually_mem_nhdsWithin, hGanalytic.eventually_analyticAt.filter_mono nhdsWithin_le_nhds] with
    s hlogeqs hGsne hs0 hGsanalytic
  have hs0' : s ≠ 0 := Set.mem_compl_singleton_iff.mp hs0
  have hlogs' :
    deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s =
      (1 : ℂ) / (s - 0) + logDeriv (dirichletEvenZeroLocalFactor χ) s := by
    have hmul := logDeriv_mul s hs0' hGsne differentiableAt_id hGsanalytic.differentiableAt
    rw [← logDeriv_apply, hlogeqs,
      show (fun s : ℂ => s * dirichletEvenZeroLocalFactor χ s) = id * dirichletEvenZeroLocalFactor χ
        from by
        funext s
        rfl,
      hmul]
    congr 1
    rw [logDeriv_apply]
    simp only [deriv_id', id_eq, one_div, sub_zero]
  unfold dirichletLogContourKernel dirichletLogEvenZeroRegularization
  rw [hlogs']
  simp only [sub_zero]
  push_cast
  field_simp

/--
Input/assumptions: `N ≥ 1`, `χ`, `x > 0`, `s : ℂ` with `G_χ` analytic and nonzero at `s`.
Conclusion: `HasDerivAt h H(s) s`, where `h :=
PseudoPrime.AnalyticNumberTheory.DirichletLFunction.dirichletLogEvenZeroRegularization x 1 G_χ` and
`H(s) := -((q(s) + s·q'(s))·x^s + (1 + s·q(s))·(x^s·log x))`, `q := logDeriv G_χ`.
Content: product rule on `h(s) = -(1 + s·q(s))·x^s`: `A(s) := 1 + s·q(s)` has `HasDerivAt A (q(s) +
s·deriv q s) s` (product rule on `s·q(s)`, using `q` differentiable at `s` since `G_χ` is analytic
and nonzero there); `B(s) := x^s` has `HasDerivAt B (x^s·log x) s`
(`HasDerivAt.const_cpow`); combine via `HasDerivAt.mul` and negate.
Role: the pointwise (general-`s`) first-derivative formula, feeding both the `s = 0` evaluation and
(via `Filter.EventuallyEq.deriv_eq`) the second derivative at `0`.
-/
theorem hasDerivAt_dirichletLogEvenZeroRegularization {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} {x : ℝ} (hx : 0 < x) {s : ℂ}
    (hganalytic : AnalyticAt ℂ (dirichletEvenZeroLocalFactor χ) s)
    (hgne : dirichletEvenZeroLocalFactor χ s ≠ 0) :
    HasDerivAt (dirichletLogEvenZeroRegularization x 1 (dirichletEvenZeroLocalFactor χ))
      (-((logDeriv (dirichletEvenZeroLocalFactor χ) s +
              s * deriv (logDeriv (dirichletEvenZeroLocalFactor χ)) s) *
            (x : ℂ) ^ s +
          (1 + s * logDeriv (dirichletEvenZeroLocalFactor χ) s) * ((x : ℂ) ^ s * Complex.log x)))
      s := by
  have hqanalytic : AnalyticAt ℂ (logDeriv (dirichletEvenZeroLocalFactor χ)) s := by
    rw [logDeriv]
    exact hganalytic.deriv.div hganalytic hgne
  have hqHasDerivAt :
    HasDerivAt (logDeriv (dirichletEvenZeroLocalFactor χ))
      (deriv (logDeriv (dirichletEvenZeroLocalFactor χ)) s) s :=
    hqanalytic.differentiableAt.hasDerivAt
  have hA :
    HasDerivAt (fun t : ℂ => 1 + t * logDeriv (dirichletEvenZeroLocalFactor χ) t)
      (logDeriv (dirichletEvenZeroLocalFactor χ) s +
        s * deriv (logDeriv (dirichletEvenZeroLocalFactor χ)) s)
      s := by
    have hsq := (hasDerivAt_id s).mul hqHasDerivAt
    have hadd := (hasDerivAt_const s (1 : ℂ)).add hsq
    have hfun2 :
      (fun _ : ℂ => (1 : ℂ)) + id * logDeriv (dirichletEvenZeroLocalFactor χ) = fun t : ℂ =>
        1 + t * logDeriv (dirichletEvenZeroLocalFactor χ) t := by
      funext t; rfl
    rw [hfun2] at hadd
    simpa only [hasDerivAt_const_add_iff, one_mul, id_eq, zero_add] using hadd
  have hxne : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hB : HasDerivAt (fun t : ℂ => (x : ℂ) ^ t) ((x : ℂ) ^ s * Complex.log x) s := by
    have h1 := (hasDerivAt_id s).const_cpow (c := (x : ℂ)) (Or.inl hxne)
    simpa only [id_eq, mul_one] using h1
  have hfun :
    dirichletLogEvenZeroRegularization x 1 (dirichletEvenZeroLocalFactor χ) = fun t : ℂ =>
      -((1 + t * logDeriv (dirichletEvenZeroLocalFactor χ) t) * (x : ℂ) ^ t) := by
    funext t
    rw [dirichletLogEvenZeroRegularization]
    push_cast
    ring
  rw [hfun]
  exact (hA.mul hB).neg

/--
For a primitive nontrivial character and `x > 0`, put
`q = logDeriv (dirichletEvenZeroLocalFactor χ)` and
`h = dirichletLogEvenZeroRegularization x 1 (dirichletEvenZeroLocalFactor χ)`.
Then `iteratedDeriv 2 h 0 = -(2*q'(0)+2*q(0)*log x+(log x)²)`.
Differentiate the local first-derivative identity by the product rule. The canonical
factor is analytic and nonzero at zero without an evenness assumption. Its interpretation
as the local factor of `L(s)/s`, and hence as a cubic-pole residue, uses evenness separately.
-/
theorem iteratedDeriv_two_dirichletLogEvenZeroRegularization_zero_eq {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv 2 (dirichletLogEvenZeroRegularization x 1 (dirichletEvenZeroLocalFactor χ)) 0 =
      -(2 * deriv (logDeriv (dirichletEvenZeroLocalFactor χ)) 0 +
          2 * logDeriv (dirichletEvenZeroLocalFactor χ) 0 * Complex.log x +
          Complex.log x ^ 2) := by
  obtain ⟨hganalytic0, hg0ne⟩ := analyticAt_and_ne_zero_dirichletEvenZeroLocalFactor hprimitive hne
  have hqanalytic0 : AnalyticAt ℂ (logDeriv (dirichletEvenZeroLocalFactor χ)) 0 := by
    rw [logDeriv]; exact hganalytic0.deriv.div hganalytic0 hg0ne
  have hqHasDerivAt0 :
    HasDerivAt (logDeriv (dirichletEvenZeroLocalFactor χ))
      (deriv (logDeriv (dirichletEvenZeroLocalFactor χ)) 0) 0 :=
    hqanalytic0.differentiableAt.hasDerivAt
  have hqderivHasDerivAt0 :
    HasDerivAt (deriv (logDeriv (dirichletEvenZeroLocalFactor χ)))
      (deriv (deriv (logDeriv (dirichletEvenZeroLocalFactor χ))) 0) 0 :=
    hqanalytic0.deriv.differentiableAt.hasDerivAt
  set H1 : ℂ → ℂ := fun s =>
    -((logDeriv (dirichletEvenZeroLocalFactor χ) s +
            s * deriv (logDeriv (dirichletEvenZeroLocalFactor χ)) s) *
          (x : ℂ) ^ s +
        (1 + s * logDeriv (dirichletEvenZeroLocalFactor χ) s) * ((x : ℂ) ^ s * Complex.log x)) with
    hH1_def
  have hGnear : ∀ᶠ s in nhds (0 : ℂ), dirichletEvenZeroLocalFactor χ s ≠ 0 :=
    hganalytic0.continuousAt.eventually_ne hg0ne
  have hev :
    ∀ᶠ s in nhds (0 : ℂ),
      HasDerivAt (dirichletLogEvenZeroRegularization x 1 (dirichletEvenZeroLocalFactor χ)) (H1 s)
        s := by
    filter_upwards [hganalytic0.eventually_analyticAt, hGnear] with s hganalytic hgne
    exact hasDerivAt_dirichletLogEvenZeroRegularization hx hganalytic hgne
  have hderiveq :
    deriv (dirichletLogEvenZeroRegularization x 1 (dirichletEvenZeroLocalFactor χ)) =ᶠ[nhds (0 : ℂ)]
      H1 :=
    hev.mono (fun s hs => hs.deriv)
  have hxne : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hB0 : HasDerivAt (fun t : ℂ => (x : ℂ) ^ t) (Complex.log x) 0 := by
    have h1 := (hasDerivAt_id (0 : ℂ)).const_cpow (c := (x : ℂ)) (Or.inl hxne)
    simpa only [id_eq, Complex.cpow_zero, one_mul, mul_one] using h1
  have hBdash0 :
    HasDerivAt (fun t : ℂ => (x : ℂ) ^ t * Complex.log x) (Complex.log x * Complex.log x) 0 :=
    hB0.mul_const (Complex.log x)
  have hC0 :
    HasDerivAt
      (fun t : ℂ =>
        logDeriv (dirichletEvenZeroLocalFactor χ) t +
          t * deriv (logDeriv (dirichletEvenZeroLocalFactor χ)) t)
      (deriv (logDeriv (dirichletEvenZeroLocalFactor χ)) 0 +
        deriv (logDeriv (dirichletEvenZeroLocalFactor χ)) 0)
      0 := by
    have hsq := (hasDerivAt_id (0 : ℂ)).mul hqderivHasDerivAt0
    have hadd := hqHasDerivAt0.add hsq
    have hfun2 :
      logDeriv (dirichletEvenZeroLocalFactor χ) +
          id * deriv (logDeriv (dirichletEvenZeroLocalFactor χ)) =
        fun t : ℂ =>
        logDeriv (dirichletEvenZeroLocalFactor χ) t +
          t * deriv (logDeriv (dirichletEvenZeroLocalFactor χ)) t := by
      funext t; rfl
    rw [hfun2] at hadd
    simpa only [one_mul, id_eq, zero_mul, add_zero] using hadd
  have hA0 :
    HasDerivAt (fun t : ℂ => 1 + t * logDeriv (dirichletEvenZeroLocalFactor χ) t)
      (logDeriv (dirichletEvenZeroLocalFactor χ) 0) 0 := by
    have hsq := (hasDerivAt_id (0 : ℂ)).mul hqHasDerivAt0
    have hadd := (hasDerivAt_const (0 : ℂ) (1 : ℂ)).add hsq
    have hfun2 :
      (fun _ : ℂ => (1 : ℂ)) + id * logDeriv (dirichletEvenZeroLocalFactor χ) = fun t : ℂ =>
        1 + t * logDeriv (dirichletEvenZeroLocalFactor χ) t := by
      funext t; rfl
    rw [hfun2] at hadd
    simpa only [hasDerivAt_const_add_iff, one_mul, id_eq, zero_mul, add_zero, zero_add] using hadd
  have hraw := ((hC0.mul hB0).add (hA0.mul hBdash0)).neg
  have hfunH1 :
    -(((fun t : ℂ =>
              logDeriv (dirichletEvenZeroLocalFactor χ) t +
                t * deriv (logDeriv (dirichletEvenZeroLocalFactor χ)) t) *
            fun t : ℂ => (x : ℂ) ^ t) +
          (fun t : ℂ => (1 : ℂ) + t * logDeriv (dirichletEvenZeroLocalFactor χ) t) * fun t : ℂ =>
            (x : ℂ) ^ t * Complex.log x) =
      H1 := by
    rw [hH1_def]; funext s; simp only [Pi.add_apply, Pi.neg_apply, Pi.mul_apply]
  have hH1deriv := hfunH1 ▸ hraw
  have hderiv2 :
    deriv (deriv (dirichletLogEvenZeroRegularization x 1 (dirichletEvenZeroLocalFactor χ))) 0 =
      deriv H1 0 :=
    hderiveq.deriv_eq
  rw [iteratedDeriv_succ, iteratedDeriv_one, hderiv2, hH1deriv.deriv]
  simp only [Complex.cpow_zero]
  ring

/--
Input/assumptions: `N ≥ 2`, `χ` primitive nontrivial quadratic mod `N`, GRH, `χ⁻¹ ≠ 1`,
`x > 0`.
Conclusion:
`Re(iteratedDeriv 2 h 0 / 2) = -Re(deriv(logDeriv F) 0) + |Re B(χ)| log x +
(1/2)(log N - log π) log x + π²/24 - (γ/2) log x - (1/2)(log x)²`,
`h := PseudoPrime.AnalyticNumberTheory.DirichletLFunction.dirichletLogEvenZeroRegularization x 1
G_χ`.
Content: substitute (B)
(`DirichletLFunction.deriv_logDeriv_dirichletEvenZeroLocalFactor_zero`)
and (G0)
(`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.logDeriv_dirichletEvenZeroLocalFactor_zero`)
into
`DirichletLFunction.iteratedDeriv_two_dirichletLogEvenZeroRegularization_zero_eq`,
simplify the resulting complex
identity via `ring`, then take `.re` using (F0)
(`DirichletLFunction.completedLFunction_logDeriv_zero_re_eq_neg_abs_BRe_sub_half_log`)
and `Complex.log x = ((log x :
ℝ) : ℂ)` (`Complex.ofReal_log`).
Role: gives half the second derivative of the canonical regularization. When the character
is even, this is the cubic-pole residue (the second Taylor coefficient), via
`PseudoPrime.AnalyticNumberTheory.General.dslope_dslope_same_eq_iteratedDeriv_two_div_two`; it
keeps `Re(deriv(logDeriv F) 0)` symbolic for
the same reason as the odd case.
-/
theorem re_iteratedDeriv_two_dirichletLogEvenZeroRegularization_zero_div_two_raw {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) {x : ℝ}
    (hx : 0 < x) :
    (iteratedDeriv 2 (dirichletLogEvenZeroRegularization x 1 (dirichletEvenZeroLocalFactor χ)) 0 /
          2).re =
      -(deriv (logDeriv (DirichletCharacter.completedLFunction χ)) 0).re +
          |primitiveBRe χ| * Real.log x +
          (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x +
          (Real.pi : ℝ) ^ 2 / 24 -
        (Real.eulerMascheroniConstant / 2) * Real.log x -
        (1 / 2) * Real.log x ^ 2 := by
  rw [iteratedDeriv_two_dirichletLogEvenZeroRegularization_zero_eq hprimitive hne hx,
    deriv_logDeriv_dirichletEvenZeroLocalFactor_zero hprimitive hne,
    logDeriv_dirichletEvenZeroLocalFactor_zero hprimitive hne]
  have hF0re :=
    completedLFunction_logDeriv_zero_re_eq_neg_abs_BRe_sub_half_log hN2 hGRH hprimitive hne hinv
      hquad
  have hlogxC : Complex.log (x : ℂ) = ((Real.log x : ℝ) : ℂ) := (Complex.ofReal_log hx.le).symm
  have hcomplex :
    (-(2 * (deriv (logDeriv (DirichletCharacter.completedLFunction χ)) 0 - (Real.pi : ℂ) ^ 2 / 24) +
            2 *
              (logDeriv (DirichletCharacter.completedLFunction χ) 0 +
                (Complex.log (Real.pi : ℂ) + (Real.eulerMascheroniConstant : ℂ)) / 2) *
              Complex.log (x : ℂ) +
            Complex.log (x : ℂ) ^ 2)) /
        2 =
      -deriv (logDeriv (DirichletCharacter.completedLFunction χ)) 0 + (Real.pi : ℂ) ^ 2 / 24 -
        logDeriv (DirichletCharacter.completedLFunction χ) 0 * Complex.log (x : ℂ) -
        (Complex.log (Real.pi : ℂ) + (Real.eulerMascheroniConstant : ℂ)) / 2 * Complex.log (x : ℂ) -
        Complex.log (x : ℂ) ^ 2 / 2 := by
    ring
  rw [hcomplex, hlogxC]
  simp only [Complex.sub_re, Complex.add_re, Complex.neg_re]
  have hpi24re : ((Real.pi : ℂ) ^ 2 / 24).re = (Real.pi : ℝ) ^ 2 / 24 := by
    rw [show ((Real.pi : ℂ) ^ 2 / 24) = (((Real.pi : ℝ) ^ 2 / 24 : ℝ) : ℂ) from by
        push_cast; ring,
      Complex.ofReal_re]
  have hAre :
    (logDeriv (DirichletCharacter.completedLFunction χ) 0 * ((Real.log x : ℝ) : ℂ)).re =
      (logDeriv (DirichletCharacter.completedLFunction χ) 0).re * Real.log x := by
    rw [mul_comm, Complex.re_ofReal_mul]; ring
  have hBre :
    ((Complex.log (Real.pi : ℂ) + (Real.eulerMascheroniConstant : ℂ)) / 2 *
          ((Real.log x : ℝ) : ℂ)).re =
      (Real.log Real.pi + Real.eulerMascheroniConstant) / 2 * Real.log x := by
    have heq :
      (Complex.log (Real.pi : ℂ) + (Real.eulerMascheroniConstant : ℂ)) / 2 =
        (((Real.log Real.pi + Real.eulerMascheroniConstant) / 2 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_log Real.pi_nonneg]; push_cast; ring
    rw [heq, mul_comm, Complex.re_ofReal_mul, Complex.ofReal_re]; ring
  have hSqre : (((Real.log x : ℝ) : ℂ) ^ 2 / 2).re = Real.log x ^ 2 / 2 := by
    rw [show (((Real.log x : ℝ) : ℂ) ^ 2 / 2) = (((Real.log x ^ 2 / 2 : ℝ)) : ℂ) from by
        push_cast; ring,
      Complex.ofReal_re]
  rw [hpi24re, hAre, hBre, hSqre, hF0re]
  ring

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
