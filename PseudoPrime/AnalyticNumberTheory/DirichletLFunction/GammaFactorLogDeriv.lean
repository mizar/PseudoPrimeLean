/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.Basic
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.Growth

/-!
# Completed-`L` to ordinary-`L` log-derivative bridge

Bridges the horizontal-strip bound on `logDeriv (completedLFunction χ)` to the ordinary
`logDeriv (LFunction χ)` used by contour kernels, via mathlib's
`DirichletCharacter.LFunction_eq_completed_div_
gammaFactor` and the Archimedean gamma factor `DirichletCharacter.gammaFactor`.

This file develops the argument in stages: nonvanishing and differentiability of the
gamma factor off the real axis, an exact closed form for `logDeriv Gammaℝ`, and finally the
completed-to-ordinary bridge itself.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-! ### Nonvanishing of the gamma factor -/

/-- `s / 2` avoids every nonpositive integer once `s.im ≠ 0` (those are all real). -/
theorem half_ne_neg_nat_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) (m : ℕ) : s / 2 ≠ -(m : ℂ) := by
  intro hm
  apply hs
  have h1 : (s / 2).im = (-(m : ℂ)).im := congrArg Complex.im hm
  simpa only [Complex.div_ofNat_im, Complex.neg_im, Complex.natCast_im, neg_zero, div_eq_zero_iff,
    OfNat.ofNat_ne_zero, or_false] using h1

/--
If `s/2` avoids every nonpositive integer, `Complex.Gammaℝ s` is nonzero.
Exclude the zeros characterized by `Gammaℝ_eq_zero_iff`. This supplies
nonvanishing at regular points, including real points on the left contour edge.
-/
theorem Gammaℝ_ne_zero_of_half_ne_neg_nat {s : ℂ} (hhalf : ∀ m : ℕ, s / 2 ≠ -(m : ℂ)) :
    Complex.Gammaℝ s ≠ 0 := by
  intro h
  rw [Complex.Gammaℝ_eq_zero_iff] at h
  obtain ⟨n, hn⟩ := h
  apply hhalf n
  rw [hn]
  ring

/--
Input/assumptions: a complex Dirichlet character `χ.Even`, a point `s` with `s / 2` avoiding
every nonpositive integer.
Conclusion: `gammaFactor χ s ≠ 0`.
Role: the even-parity regular-point nonvanishing fact, needed at the left-vertical line's `t = 0`
point where `s.im = 0` yet `s / 2` still avoids every pole (the left-vertical step's
quarter-lattice separation).
-/
theorem gammaFactor_ne_zero_of_even_of_half_ne_neg_nat {N : ℕ} {χ : DirichletCharacter ℂ N}
    (hχ : χ.Even) {s : ℂ} (hhalf : ∀ m : ℕ, s / 2 ≠ -(m : ℂ)) :
    DirichletCharacter.gammaFactor χ s ≠ 0 := by
  rw [hχ.gammaFactor_def]
  exact Gammaℝ_ne_zero_of_half_ne_neg_nat hhalf

/--
Input/assumptions: a complex Dirichlet character `χ.Odd`, a point `s` with `(s + 1) / 2` avoiding
every nonpositive integer.
Conclusion: `gammaFactor χ s ≠ 0`.
Role: the odd-parity regular-point nonvanishing fact.
-/
theorem gammaFactor_ne_zero_of_odd_of_half_ne_neg_nat {N : ℕ} {χ : DirichletCharacter ℂ N}
    (hχ : χ.Odd) {s : ℂ} (hhalf : ∀ m : ℕ, (s + 1) / 2 ≠ -(m : ℂ)) :
    DirichletCharacter.gammaFactor χ s ≠ 0 := by
  rw [hχ.gammaFactor_def]
  exact Gammaℝ_ne_zero_of_half_ne_neg_nat hhalf

/--
Input/assumptions: a complex Dirichlet character `χ`, a point `s` with `s.im ≠ 0`.
Conclusion: `gammaFactor χ s ≠ 0`.
Content: parity dispatch to
`DirichletLFunction.gammaFactor_ne_zero_of_even_of_half_ne_neg_nat`/`_odd_`,
using
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.half_ne_neg_nat_of_im_ne_zero` (`(s+1).im =
s.im ≠ 0` in the odd case too) to supply `hhalf`.
Role: supplies the denominator-nonvanishing side condition `logDeriv_div` needs for the
completed-to-ordinary bridge, off the real axis (in particular on every horizontal line
`Im s = T ≠ 0` the horizontal argument integrates over).
-/
theorem gammaFactor_ne_zero_of_im_ne_zero {N : ℕ} {χ : DirichletCharacter ℂ N} {s : ℂ}
    (hs : s.im ≠ 0) : DirichletCharacter.gammaFactor χ s ≠ 0 := by
  rcases χ.even_or_odd with heven | hodd
  · exact gammaFactor_ne_zero_of_even_of_half_ne_neg_nat heven (half_ne_neg_nat_of_im_ne_zero hs)
  · exact
      gammaFactor_ne_zero_of_odd_of_half_ne_neg_nat hodd
        (half_ne_neg_nat_of_im_ne_zero
          (by simpa only [Complex.add_im, Complex.one_im, add_zero, ne_eq] using hs))

/-! ### Differentiability of the gamma factor at regular points -/

/--
If `s/2` avoids every nonpositive integer, `Complex.Gammaℝ` is differentiable
at `s`. Differentiate the product of the entire power of π with `Gamma(s/2)`
away from its poles. This supports the regular-point logarithmic derivative formula.
-/
theorem differentiableAt_Gammaℝ_of_half_ne_neg_nat {s : ℂ} (hhalf : ∀ m : ℕ, s / 2 ≠ -(m : ℂ)) :
    DifferentiableAt ℂ Complex.Gammaℝ s := by
  change DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2)) s
  refine DifferentiableAt.mul ?_ ?_
  · exact
      (differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  · exact (Complex.differentiableAt_Gamma (s / 2) hhalf).comp s (differentiableAt_id.div_const 2)

/-- The even-parity regular-point differentiability fact for `gammaFactor`. -/
theorem differentiableAt_gammaFactor_of_even_of_half_ne_neg_nat {N : ℕ} {χ : DirichletCharacter ℂ N}
    (hχ : χ.Even) {s : ℂ} (hhalf : ∀ m : ℕ, s / 2 ≠ -(m : ℂ)) :
    DifferentiableAt ℂ (DirichletCharacter.gammaFactor χ) s := by
  have heq : DirichletCharacter.gammaFactor χ = Complex.Gammaℝ := by
    funext z
    exact hχ.gammaFactor_def z
  rw [heq]
  exact differentiableAt_Gammaℝ_of_half_ne_neg_nat hhalf

/-- The odd-parity regular-point differentiability fact for `gammaFactor`. -/
theorem differentiableAt_gammaFactor_of_odd_of_half_ne_neg_nat {N : ℕ} {χ : DirichletCharacter ℂ N}
    (hχ : χ.Odd) {s : ℂ} (hhalf : ∀ m : ℕ, (s + 1) / 2 ≠ -(m : ℂ)) :
    DifferentiableAt ℂ (DirichletCharacter.gammaFactor χ) s := by
  have heq : DirichletCharacter.gammaFactor χ = fun z => Complex.Gammaℝ (z + 1) := by
    funext z
    exact hχ.gammaFactor_def z
  rw [heq]
  exact
    (differentiableAt_Gammaℝ_of_half_ne_neg_nat hhalf).comp s ((differentiableAt_id).add_const 1)

/--
Input/assumptions: a complex Dirichlet character `χ`, a point `s` with `s.im ≠ 0`.
Conclusion: `gammaFactor χ` is complex-differentiable at `s`.
Content: parity dispatch to
`DirichletLFunction.differentiableAt_gammaFactor_of_even_of_half_ne_neg_nat`/`_odd_`.
Role: the denominator-differentiability side condition `logDeriv_div` needs.
-/
theorem differentiableAt_gammaFactor_of_im_ne_zero {N : ℕ} {χ : DirichletCharacter ℂ N} {s : ℂ}
    (hs : s.im ≠ 0) : DifferentiableAt ℂ (DirichletCharacter.gammaFactor χ) s := by
  rcases χ.even_or_odd with heven | hodd
  · exact
      differentiableAt_gammaFactor_of_even_of_half_ne_neg_nat heven
        (half_ne_neg_nat_of_im_ne_zero hs)
  · exact
      differentiableAt_gammaFactor_of_odd_of_half_ne_neg_nat hodd
        (half_ne_neg_nat_of_im_ne_zero
          (by simpa only [Complex.add_im, Complex.one_im, add_zero, ne_eq] using hs))

/-! ### Exact logarithmic derivative of `Gammaℝ` at regular points -/

/--
If `s/2` avoids every nonpositive integer, the logarithmic derivative of
`Gammaℝ` is `-log π / 2 + digamma(s/2) / 2`. Apply the product and composition
formulas to `π^(-s/2) * Gamma(s/2)`. This gives gamma estimates on horizontal
and left vertical contour edges, including regular real points.
-/
theorem logDeriv_Gammaℝ_of_half_ne_neg_nat {s : ℂ} (hhalf : ∀ m : ℕ, s / 2 ≠ -(m : ℂ)) :
    logDeriv Complex.Gammaℝ s = -(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma (s / 2) / 2 := by
  have hpiC_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hlin : HasDerivAt (fun z : ℂ => -z / 2) (-(1 : ℂ) / 2) s := by
    have := (hasDerivAt_id s).neg.div_const (2 : ℂ)
    simpa only [id_eq, Pi.neg_apply] using this
  have hpow_deriv :
    HasDerivAt (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2))
      ((Real.pi : ℂ) ^ (-s / 2) * Complex.log (Real.pi : ℂ) * (-(1 : ℂ) / 2)) s :=
    hlin.const_cpow (Or.inl hpiC_ne)
  have hpow_ne : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hpiC_ne)
  have hpow_logDeriv :
    logDeriv (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s = -(Complex.log (Real.pi : ℂ)) / 2 := by
    rw [logDeriv_apply, hpow_deriv.deriv]
    calc
      (Real.pi : ℂ) ^ (-s / 2) * Complex.log (Real.pi : ℂ) * (-1 / 2) / (Real.pi : ℂ) ^ (-s / 2) =
          Complex.log (Real.pi : ℂ) * (-1 / 2) :=
        by rw [mul_assoc, mul_div_cancel_left₀ _ hpow_ne]
      _ = -(Complex.log (Real.pi : ℂ)) / 2 := by ring
  have hhalf_deriv : HasDerivAt (fun z : ℂ => z / 2) ((1 : ℂ) / 2) s := by
    simpa only [id_eq] using (hasDerivAt_id s).div_const (2 : ℂ)
  have hgam_diff : DifferentiableAt ℂ Complex.Gamma (s / 2) :=
    Complex.differentiableAt_Gamma (s / 2) hhalf
  have hgam_comp_logDeriv :
    logDeriv (fun z : ℂ => Complex.Gamma (z / 2)) s = Complex.digamma (s / 2) / 2 := by
    have hcomp :=
      logDeriv_comp (f := Complex.Gamma) (g := fun z : ℂ => z / 2) (x := s) hgam_diff
        hhalf_deriv.differentiableAt
    rw [show (fun z : ℂ => Complex.Gamma (z / 2)) = Complex.Gamma ∘ fun z : ℂ => z / 2 from rfl,
      hcomp, hhalf_deriv.deriv, Complex.digamma_def]
    ring
  have hpow_diff : DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s :=
    hpow_deriv.differentiableAt
  have hgamcomp_diff : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z / 2)) s :=
    hgam_diff.comp s hhalf_deriv.differentiableAt
  have hgam_ne : Complex.Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero hhalf
  change logDeriv (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2)) s = _
  rw [show
      (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2)) =
        (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) * (fun z : ℂ => Complex.Gamma (z / 2))
      from by
      funext z
      simp only [Pi.mul_apply],
    logDeriv_mul s hpow_ne hgam_ne hpow_diff hgamcomp_diff, hpow_logDeriv, hgam_comp_logDeriv]

/-! ### Exact logarithmic derivative of the character gamma factor -/

/-- Even-character regular-point case of
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.logDeriv_Gammaℝ_of_half_ne_neg_nat` for
`gammaFactor`. -/
theorem logDeriv_gammaFactor_eq_of_even_of_half_ne_neg_nat {N : ℕ} {χ : DirichletCharacter ℂ N}
    (hχ : χ.Even) {s : ℂ} (hhalf : ∀ m : ℕ, s / 2 ≠ -(m : ℂ)) :
    logDeriv (DirichletCharacter.gammaFactor χ) s =
      -(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma (s / 2) / 2 := by
  have hgf : DirichletCharacter.gammaFactor χ = Complex.Gammaℝ := by
    funext z
    exact hχ.gammaFactor_def z
  rw [hgf]
  exact logDeriv_Gammaℝ_of_half_ne_neg_nat hhalf

/-- Odd-character regular-point case: the argument shifts by `1`, and the outer chain-rule factor
`deriv (· + 1) = 1` leaves the formula unchanged in shape. -/
theorem logDeriv_gammaFactor_eq_of_odd_of_half_ne_neg_nat {N : ℕ} {χ : DirichletCharacter ℂ N}
    (hχ : χ.Odd) {s : ℂ} (hhalf : ∀ m : ℕ, (s + 1) / 2 ≠ -(m : ℂ)) :
    logDeriv (DirichletCharacter.gammaFactor χ) s =
      -(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma ((s + 1) / 2) / 2 := by
  have hgf : DirichletCharacter.gammaFactor χ = fun z => Complex.Gammaℝ (z + 1) := by
    funext z
    exact hχ.gammaFactor_def z
  rw [hgf]
  have hcomp :=
    logDeriv_comp (f := Complex.Gammaℝ) (g := fun z : ℂ => z + 1) (x := s)
      (differentiableAt_Gammaℝ_of_half_ne_neg_nat hhalf) (differentiableAt_id.add_const 1)
  rw [show (fun z : ℂ => Complex.Gammaℝ (z + 1)) = Complex.Gammaℝ ∘ fun z : ℂ => z + 1 from rfl,
    hcomp]
  have hderiv1 : deriv (fun z : ℂ => z + 1) s = 1 := by
    simp only [differentiableAt_fun_id, differentiableAt_const, deriv_fun_add, deriv_id'',
      deriv_const', add_zero]
  rw [hderiv1, mul_one, logDeriv_Gammaℝ_of_half_ne_neg_nat hhalf]

/--
For an even character and `Im s ≠ 0`, the gamma-factor logarithmic derivative
is `-log π / 2 + digamma(s/2) / 2`. Specialize the regular-point formula
using parity and the nonzero imaginary part; this supplies horizontal estimates.
-/
theorem logDeriv_gammaFactor_eq_of_even {N : ℕ} {χ : DirichletCharacter ℂ N} (hχ : χ.Even) {s : ℂ}
    (hs : s.im ≠ 0) :
    logDeriv (DirichletCharacter.gammaFactor χ) s =
      -(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma (s / 2) / 2 :=
  logDeriv_gammaFactor_eq_of_even_of_half_ne_neg_nat hχ (half_ne_neg_nat_of_im_ne_zero hs)

/--
For an odd character and `Im s ≠ 0`, the gamma-factor logarithmic derivative
is `-log π / 2 + digamma((s+1)/2) / 2`. Specialize the shifted regular-point
formula using parity; this supplies horizontal estimates.
-/
theorem logDeriv_gammaFactor_eq_of_odd {N : ℕ} {χ : DirichletCharacter ℂ N} (hχ : χ.Odd) {s : ℂ}
    (hs : s.im ≠ 0) :
    logDeriv (DirichletCharacter.gammaFactor χ) s =
      -(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma ((s + 1) / 2) / 2 :=
  logDeriv_gammaFactor_eq_of_odd_of_half_ne_neg_nat hχ
    (half_ne_neg_nat_of_im_ne_zero
      (by simpa only [Complex.add_im, Complex.one_im, add_zero, ne_eq] using hs))

/-! ### Completed-to-ordinary logarithmic derivative at regular points -/

/--
Input/assumptions: `χ ≠ 1`, a point `s` with `completedLFunction χ s ≠ 0`, `gammaFactor χ s ≠ 0`,
and `gammaFactor χ` differentiable at `s`.
Conclusion: `logDeriv (LFunction χ) s = logDeriv (completedLFunction χ) s -
logDeriv (gammaFactor χ) s`.
Content:
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.dirichletCharacter_level_ne_one_of_ne_one hne`
gives `N ≠ 1`, so mathlib's
`DirichletLFunction.dirichletLFunction_eq_completed_div_gammaFactor`
applies at every `s` (not just `s ≠ 0`),
identifying `LFunction χ` with `completedLFunction χ / gammaFactor χ` as functions; `logDeriv_div`
then splits the quotient's log-derivative into a difference.
Role: the regular-point body of
`DirichletLFunction.logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor`
— the
`im ≠ 0` hypothesis was only ever used to derive the two nonvanishing/differentiability
side-conditions given here directly, so this version also covers the left-vertical line's `t = 0`
point (the left-vertical step).
-/
theorem logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor_of_regular {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hne : χ ≠ 1) {s : ℂ}
    (hF : DirichletCharacter.completedLFunction χ s ≠ 0)
    (hΓ : DirichletCharacter.gammaFactor χ s ≠ 0)
    (hdΓ : DifferentiableAt ℂ (DirichletCharacter.gammaFactor χ) s) :
    logDeriv (DirichletCharacter.LFunction χ) s =
      logDeriv (DirichletCharacter.completedLFunction χ) s -
        logDeriv (DirichletCharacter.gammaFactor χ) s := by
  have hfun :
    DirichletCharacter.LFunction χ = fun z =>
      DirichletCharacter.completedLFunction χ z / DirichletCharacter.gammaFactor χ z := by
    funext z
    exact
      dirichletLFunction_eq_completed_div_gammaFactor χ z
        (Or.inr (dirichletCharacter_level_ne_one_of_ne_one hne))
  rw [hfun]
  exact logDeriv_div s hF hΓ (DirichletCharacter.differentiable_completedLFunction hne s) hdΓ

/--
Input/assumptions: `χ ≠ 1`, a point `s` with `completedLFunction χ s ≠ 0` and `s.im ≠ 0`.
Conclusion: `logDeriv (LFunction χ) s = logDeriv (completedLFunction χ) s -
logDeriv (gammaFactor χ) s`.
Content: thin wrapper over
`DirichletLFunction.logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor_of_regular`,
using
`DirichletLFunction.gammaFactor_ne_zero_of_im_ne_zero`/
`DirichletLFunction.differentiableAt_gammaFactor_of_im_ne_zero`
for the
denominator side.
Role: the bridge: converts the bound on `logDeriv (completedLFunction χ)` into a
bound on `logDeriv (LFunction χ)`, the quantity the reciprocal contour kernel actually uses.
-/
theorem logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hne : χ ≠ 1) {s : ℂ}
    (hF : DirichletCharacter.completedLFunction χ s ≠ 0) (hs : s.im ≠ 0) :
    logDeriv (DirichletCharacter.LFunction χ) s =
      logDeriv (DirichletCharacter.completedLFunction χ) s -
        logDeriv (DirichletCharacter.gammaFactor χ) s :=
  logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor_of_regular hne hF
    (gammaFactor_ne_zero_of_im_ne_zero hs) (differentiableAt_gammaFactor_of_im_ne_zero hs)

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
