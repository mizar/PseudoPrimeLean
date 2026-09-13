/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveResidueClosedForms

/-!
# the residue evaluation (even, start): the generic even-zero regularization derivative

Character-free computation of `deriv (DirichletLFunction.dirichletReciprocalEvenZeroRegularization
x m g) 0` in
terms of `logDeriv g 0`, `m`, and `x`, via the product rule (three factors: the linear-affine
piece `-(m + s·logDeriv g s)`, the Mellin power `x^{s-1}`, and the simple-pole factor `(s-1)⁻¹`).
No character, GRH, or functional-equation content enters here — this is a pure calculus lemma,
isolated from the even-character analytic machinery (the residue evaluation, even block).
-/

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/--
Input/assumptions: `x > 0`, `m : ℕ`, `g : ℂ → ℂ` analytic at `0` with `g 0 ≠ 0`.
Conclusion: `deriv (DirichletLFunction.dirichletReciprocalEvenZeroRegularization x m g) 0 =
  (1/x) · (logDeriv g 0 + m · (log x + 1))`.
Content: `R(s) = A(s) B(s) C(s)` with `A(s) := -(m + s logDeriv g s)`, `B(s) := x^{s-1}`,
`C(s) := (s-1)⁻¹`. `A(0) = -m`, `A'(0) = -logDeriv g 0` (product rule on `s ↦ s · logDeriv g s`,
using `logDeriv g` differentiable at `0` since `g` is analytic and nonzero there — `AnalyticAt.div`
on `deriv g / g`); `B(0) = x⁻¹`, `B'(0) = x⁻¹ log x` (`HasDerivAt.const_cpow` on the affine
exponent `s - 1`); `C(0) = -1`, `C'(0) = -1`. The product rule combines these into
`R'(0) = x⁻¹ (logDeriv g 0 + m(log x + 1))`.
Role: the "(ER)" generic derivative formula, the character-free half of the even `s = 0` residue
closed form.
-/
theorem deriv_dirichletReciprocalEvenZeroRegularization_zero {x : ℝ} (hx : 0 < x) (m : ℕ)
    {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) (hg0 : g 0 ≠ 0) :
    deriv
        (dirichletReciprocalEvenZeroRegularization
          x m g)
        0 =
      (1 / x : ℂ) * (logDeriv g 0 + (m : ℂ) * (Complex.log x + 1)) := by
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hlogDerivG : DifferentiableAt ℂ (logDeriv g) 0 := by
    have : AnalyticAt ℂ (logDeriv g) 0 := by
      unfold logDeriv
      exact hg.deriv.div hg hg0
    exact this.differentiableAt
  have hA : HasDerivAt (fun s : ℂ => -((m : ℂ) + s * logDeriv g s)) (-(logDeriv g 0)) 0 := by
    have hmul : HasDerivAt (fun s : ℂ => (m : ℂ) + s * logDeriv g s) (logDeriv g 0) 0 := by
      have h1 :
        HasDerivAt (fun s : ℂ => s * logDeriv g s) (1 * logDeriv g 0 + 0 * deriv (logDeriv g) 0)
          0 :=
        (hasDerivAt_id (0 : ℂ)).mul hlogDerivG.hasDerivAt
      simpa only [one_mul, zero_mul, add_zero] using h1.const_add (m : ℂ)
    exact hmul.neg
  have hB :
    HasDerivAt (fun s : ℂ => (x : ℂ) ^ (s - 1)) ((x : ℂ) ^ ((0 : ℂ) - 1) * Complex.log x * 1) 0 :=
    (hasDerivAt_id (0 : ℂ)).sub_const 1 |>.const_cpow (Or.inl hxC)
  have hC : HasDerivAt (fun s : ℂ => (s - 1)⁻¹) (-(1 : ℂ) / ((0 : ℂ) - 1) ^ 2) 0 :=
    ((hasDerivAt_id (0 : ℂ)).sub_const 1).inv
      (by
        change (0 : ℂ) - 1 ≠ 0
        norm_num only)
  have hprod := (hA.mul hB).mul hC
  have hR :
    HasDerivAt
      (dirichletReciprocalEvenZeroRegularization
        x m g)
      ((-(logDeriv g 0) * (x : ℂ) ^ ((0 : ℂ) - 1) +
            (-((m : ℂ) + (0 : ℂ) * logDeriv g 0)) * ((x : ℂ) ^ ((0 : ℂ) - 1) * Complex.log x * 1)) *
          ((0 - 1 : ℂ))⁻¹ +
        (-((m : ℂ) + (0 : ℂ) * logDeriv g 0)) * (x : ℂ) ^ ((0 : ℂ) - 1) *
          (-(1 : ℂ) / ((0 : ℂ) - 1) ^ 2))
      0 := by
    apply hprod.congr_of_eventuallyEq
    filter_upwards with s
    unfold
      dirichletReciprocalEvenZeroRegularization
    simp only [Pi.mul_apply]
    ring
  rw [hR.deriv]
  have hpow0 : (x : ℂ) ^ ((0 : ℂ) - 1) = (x : ℂ)⁻¹ := by rw [zero_sub, Complex.cpow_neg_one]
  rw [hpow0]
  field_simp
  ring

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
