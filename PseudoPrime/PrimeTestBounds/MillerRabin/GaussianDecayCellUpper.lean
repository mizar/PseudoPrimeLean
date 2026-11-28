/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianDirectMiddleResidual
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianDirectMiddleResidual

/-! # Interpolation of a signed decay term on a closed cell -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Upper endpoint bounds and an absolute second derivative bound give a
uniform upper bound for a normalized exponential-polynomial term. -/
public theorem gaussian_decay_cell_upper (P : Polynomial ℝ) {r κ a b M m t : ℝ}
    (ht : t ∈ Set.Icc a b) (hκ : 0 ≤ κ) (hM : 0 ≤ M) (ha : κ * Real.exp (-r * a) * P.eval a ≤ m)
    (hb : κ * Real.exp (-r * b) * P.eval b ≤ m)
    (hc :
      ∀ x ∈ Set.Ioo a b,
        κ * Real.exp (-r * x) * |(gaussianDecayDeriv r (gaussianDecayDeriv r P)).eval x| ≤ M) :
    κ * Real.exp (-r * t) * P.eval t ≤ m + M * (b - a) ^ 2 / 8 := by
  let f := fun x ↦ -κ * (Real.exp (-r * x) * P.eval x)
  let f' := fun x ↦ -κ * (Real.exp (-r * x) * (gaussianDecayDeriv r P).eval x)
  let f'' := fun x ↦
    -κ * (Real.exp (-r * x) * (gaussianDecayDeriv r (gaussianDecayDeriv r P)).eval x)
  have h₁ (x : ℝ) : HasDerivAt f (f' x) x := (gaussian_decay_hasDerivAt r P x).const_mul (-κ)
  have h₂ (x : ℝ) : HasDerivAt f' (f'' x) x :=
    (gaussian_decay_hasDerivAt r (gaussianDecayDeriv r P) x).const_mul (-κ)
  have hcurv (x : ℝ) (hx : x ∈ Set.Ioo a b) : f'' x ≤ M := by
    dsimp only [f'']
    rw [neg_mul, ← mul_assoc, ← mul_neg]
    exact
      (mul_le_mul_of_nonneg_left (neg_le_abs _) (mul_nonneg hκ (Real.exp_pos _).le)).trans (hc x hx)
  have h :=
    Analysis.cell_lower_of_curvature ht hM (fun x _ ↦ (h₁ x).continuousAt.continuousWithinAt)
      (fun x _ ↦ h₁ x) (fun x _ ↦ h₂ x) hcurv
      (show -m ≤ f a by simpa only [f, neg_mul, ← mul_assoc] using neg_le_neg ha)
      (show -m ≤ f b by simpa only [f, neg_mul, ← mul_assoc] using neg_le_neg hb)
  simp only [f, neg_mul, ← mul_assoc] at h ⊢
  linarith only [h]

end PseudoPrime.PrimeTestBounds.MillerRabin
