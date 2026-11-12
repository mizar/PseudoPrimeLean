/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.LSeries.HurwitzZetaEven

/-! # Products of rapidly decreasing kernels -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- If `f - a` and `g - b` both decay faster than every real power at
infinity, then so does `f * g - a * b`. This supplies the asymptotic
condition for the product of two weak functional-equation pairs. -/
theorem rapid_product_sub (f g : ℝ → ℂ) (a b : ℂ)
    (hf : ∀ r : ℝ, Asymptotics.IsBigO Filter.atTop (fun x ↦ f x - a) (fun x : ℝ ↦ x ^ r))
    (hg : ∀ r : ℝ, Asymptotics.IsBigO Filter.atTop (fun x ↦ g x - b) (fun x : ℝ ↦ x ^ r)) (r : ℝ) :
    Asymptotics.IsBigO Filter.atTop (fun x ↦ f x * g x - a * b) (fun x : ℝ ↦ x ^ r) := by
  have hg0 : Asymptotics.IsBigO Filter.atTop g (fun _ : ℝ ↦ (1 : ℝ)) := by
    have hc : Asymptotics.IsBigO Filter.atTop (fun _ : ℝ ↦ b) (fun x : ℝ ↦ x ^ (0 : ℝ)) := by
      simpa only [Real.rpow_zero] using (Asymptotics.isBigO_const_one ℝ b (Filter.atTop : Filter ℝ))
    have h := (hg 0).add hc
    simpa only [Real.rpow_zero, sub_add_cancel] using h
  have h₁ := (hf r).mul hg0
  have h₂ := (hg r).const_mul_left a
  have hid : (fun x ↦ f x * g x - a * b) = fun x ↦ (f x - a) * g x + a * (g x - b) := by
    funext x
    ring
  rw [hid]
  have h₁' : Asymptotics.IsBigO Filter.atTop (fun x ↦ (f x - a) * g x) (fun x : ℝ ↦ x ^ r) := by
    simpa only [mul_one] using h₁
  exact h₁'.add h₂

/-- Multiply the corresponding kernels of two weak functional-equation pairs
whose kernels are continuous on the positive half-line. The weights add and
the root numbers multiply; rapid decay follows from `rapid_product_sub`. -/
noncomputable def mulWeakFEPair (P Q : WeakFEPair ℂ) (hPf : ContinuousOn P.f (Set.Ioi 0))
    (hPg : ContinuousOn P.g (Set.Ioi 0)) (hQf : ContinuousOn Q.f (Set.Ioi 0))
    (hQg : ContinuousOn Q.g (Set.Ioi 0)) : WeakFEPair ℂ
    where
  f := fun x ↦ P.f x * Q.f x
  g := fun x ↦ P.g x * Q.g x
  k := P.k + Q.k
  ε := P.ε * Q.ε
  f₀ := P.f₀ * Q.f₀
  g₀ := P.g₀ * Q.g₀
  hf_int := (hPf.mul hQf).locallyIntegrableOn measurableSet_Ioi
  hg_int := (hPg.mul hQg).locallyIntegrableOn measurableSet_Ioi
  hk := add_pos P.hk Q.hk
  hε := mul_ne_zero P.hε Q.hε
  h_feq x hx := by
    rw [P.h_feq x hx, Q.h_feq x hx, Real.rpow_add hx]
    simp only [smul_eq_mul, Complex.ofReal_mul]
    ring
  hf_top := rapid_product_sub P.f Q.f P.f₀ Q.f₀ P.hf_top Q.hf_top
  hg_top := rapid_product_sub P.g Q.g P.g₀ Q.g₀ P.hg_top Q.hg_top

end PseudoPrime.Analysis
