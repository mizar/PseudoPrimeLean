/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-! # Iterated derivatives of a complex power -/

public section

namespace PseudoPrime.Analysis

/-- The falling product `w (w-1) ... (w-(n-1))` used in the explicit
iterated-derivative formula for complex powers. It is a finite product and
has no dependence on a precomputed table. -/
noncomputable def complexFalling (w : ℂ) (n : ℕ) : ℂ :=
  ∏ j ∈ Finset.range n, (w - j)

/-- On the slit plane, the `n`-th complex derivative of `z ↦ z^w` is the
falling product times `z^(w-n)`. Induction differentiates the locally valid
formula and uses the principal-power derivative on the slit plane. -/
theorem iteratedDeriv_complex_cpow (w : ℂ) (n : ℕ) {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    iteratedDeriv n (fun u : ℂ ↦ u ^ w) z = complexFalling w n * z ^ (w - n) := by
  induction n generalizing z with
  | zero =>
    simp only [iteratedDeriv_zero, complexFalling, Finset.range_zero, Finset.prod_empty,
      Nat.cast_zero, sub_zero, one_mul]
  | succ n
    ih =>
    have hneigh : Filter.Eventually (fun u : ℂ ↦ u ∈ Complex.slitPlane) (nhds z) :=
      Complex.isOpen_slitPlane.mem_nhds hz
    have heq :
      Filter.EventuallyEq (nhds z) (iteratedDeriv n (fun u : ℂ ↦ u ^ w))
        (fun u : ℂ ↦ complexFalling w n * u ^ (w - n)) :=
      hneigh.mono (fun u hu ↦ ih hu)
    rw [iteratedDeriv_succ, heq.deriv_eq]
    have hd :=
      (Complex.hasStrictDerivAt_cpow_const (c := w - n) hz).hasDerivAt.const_mul
        (complexFalling w n)
    rw [hd.deriv]
    unfold complexFalling
    rw [Finset.prod_range_succ, Nat.cast_add, Nat.cast_one]
    have hexp : w - ((n : ℂ) + 1) = (w - n) - 1 := by ring
    rw [hexp]
    ring

/-- The iterated derivative of a complex power multiplied by an exponential,
on the slit plane, as a finite sum. This is the coefficient formula used in
Taylor quadrature of the finite theta Mellin integrand. -/
theorem iteratedDeriv_cpow_exp (w c : ℂ) (n : ℕ) {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    iteratedDeriv n (fun u : ℂ ↦ u ^ w * Complex.exp (c * u)) z =
      ∑ j ∈ Finset.range (n + 1),
        (n.choose j : ℂ) * (complexFalling w j * z ^ (w - j)) *
          (c ^ (n - j) * Complex.exp (c * z)) := by
  have hf : ContDiffAt ℂ n (fun u : ℂ ↦ u ^ w) z :=
    (analyticAt_id.cpow analyticAt_const hz).contDiffAt
  have hg : ContDiffAt ℂ n (fun u : ℂ ↦ Complex.exp (c * u)) z :=
    (analyticAt_const.mul analyticAt_id).cexp'.contDiffAt
  rw [iteratedDeriv_fun_mul hf hg]
  apply Finset.sum_congr rfl
  intro j hj
  rw [iteratedDeriv_complex_cpow w j hz, iteratedDeriv_cexp_const_mul]

end PseudoPrime.Analysis
