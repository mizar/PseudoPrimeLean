/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalGapScalarPrefixBounds

/-! # Coupled conductor cancellation in pole and signed left budgets -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Totalized normalized conductor difference (1-x^(-h))/h.
For h>0,x>=1 it lies between zero and log x. This retains the cancellation shared
by the pole and left-contour conductor terms when the gap is allowed to vary. -/
noncomputable def reciprocalGapLogQuotient (h x : ℝ) : ℝ :=
  (1 - x ^ (-h)) / h

/-- For h,x>0, the normalized conductor difference (1-x^(-h))/h is at most log x.
Apply 1+u<=exp u at u=-h*log x. This controls the conductor cancellation before
separate pole and left-contour estimates introduce large inverse-gap terms. -/
theorem reciprocalGapLogQuotient_le_log {h x : ℝ} (hh : 0 < h) (hx : 0 < x) :
    reciprocalGapLogQuotient h x ≤ Real.log x := by
  unfold reciprocalGapLogQuotient
  have he := Real.add_one_le_exp (-h * Real.log x)
  rw [Real.rpow_def_of_pos hx]
  rw [mul_comm (-h) (Real.log x)] at he
  exact (div_le_iff₀ hh).mpr (by linarith only [he])

/-- For x>0, split x^(-1/2-h) into x^(-h)/sqrt(x). No restriction on h is needed.
Use real-power addition and the square-root power identity. This normalizes the
signed left budget to the same denominator as the pole budget. -/
theorem reciprocalGap_left_power_factor {h x : ℝ} (hx : 0 < x) :
    x ^ (-1 / 2 - h) = x ^ (-h) / Real.sqrt x := by
  rw [show (-1 / 2 - h : ℝ) = -h + -(1 / 2) by ring, Real.rpow_add hx, Real.rpow_neg hx.le (1 / 2),
    ← Real.sqrt_eq_rpow]
  rfl

/-- For h>0 and x>=1, the normalized conductor difference is nonnegative.
Bound x^(-h) by one and divide by positive h. This records the sign retained
when combining the pole and signed left-contour conductor terms. -/
theorem reciprocalGapLogQuotient_nonneg {h x : ℝ} (hh : 0 < h) (hx : 1 ≤ x) :
    0 ≤ reciprocalGapLogQuotient h x := by
  exact
    div_nonneg (sub_nonneg.mpr (Real.rpow_le_one_of_one_le_of_nonpos hx (neg_nonpos.mpr hh.le)))
      hh.le

/-- For h,x>0, combine the scalar pole and signed real-axis left budgets exactly.
The conductor factor becomes the normalized difference plus r/h; the Euler/Gamma
residuals remain explicit with their signs. Other real scalar inputs are arbitrary.
This algebraic identity supports varying the gap and comparison offset together. -/
theorem reciprocalGap_pole_add_left_budget_eq {h x : ℝ} (hh : 0 < h) (hx : 0 < x) (r : ℝ) (q : ℕ)
    (M₁ G₁ K₁ M₂ G₂ : ℝ) :
    reciprocalGapScalarPoleBudget h r q x M₁ G₁ K₁ + reciprocalGapRealAxisBudget h q x M₂ G₂ =
      (reciprocalGapLogQuotient h x + r / h) * Real.log q / Real.sqrt x +
        ((1 + 2 * r) * (G₁ + M₁ - K₁) + x ^ (-h) * (M₂ - G₂)) / (h * Real.sqrt x) := by
  rw [reciprocalGapRealAxisBudget, reciprocalGap_left_power_factor hx]
  unfold reciprocalGapScalarPoleBudget reciprocalGapLogQuotient
  have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  field_simp [hh.ne', hs]
  ring

/-- Pole-left budget after coupling the offset r to the positive gap h by r<=kappa*h.
The conductor coefficient is (log x+kappa)/sqrt(x). Remaining signed Euler/Gamma
inputs M1,G1,K1,M2,G2 are retained over the common denominator h*sqrt(x).
The formula is totalized; comparison theorems supply its analytic hypotheses. -/
noncomputable def reciprocalGapCoupledPoleLeftBudget (h r κ : ℝ) (q : ℕ) (x M₁ G₁ K₁ M₂ G₂ : ℝ) :
    ℝ :=
  (Real.log x + κ) * Real.log q / Real.sqrt x +
    ((1 + 2 * r) * (G₁ + M₁ - K₁) + x ^ (-h) * (M₂ - G₂)) / (h * Real.sqrt x)

/-- For h>0,x>=1,q>=1 and r<=kappa*h, the pole plus signed left budget is at most
the coupled budget. Bound only the normalized conductor difference and r/h.
The Euler/Gamma residuals and the finite positive-prefix lower scalar are unchanged;
no absolute value or discarded inverse-gap residual is hidden in this bound. -/
theorem reciprocalGap_pole_add_left_le_coupled {h x r κ : ℝ} (hh : 0 < h) (hx : 1 ≤ x)
    (hr : r ≤ κ * h) {q : ℕ} (hq : 1 ≤ q) (M₁ G₁ K₁ M₂ G₂ : ℝ) :
    reciprocalGapScalarPoleBudget h r q x M₁ G₁ K₁ + reciprocalGapRealAxisBudget h q x M₂ G₂ ≤
      reciprocalGapCoupledPoleLeftBudget h r κ q x M₁ G₁ K₁ M₂ G₂ := by
  have hx0 := zero_lt_one.trans_le hx
  have hd := reciprocalGapLogQuotient_le_log hh hx0
  have hκ : r / h ≤ κ := (div_le_iff₀ hh).mpr hr
  have hq0 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hl : 0 ≤ Real.log q := Real.log_nonneg hq0
  have hm :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (add_le_add hd hκ) hl)
      (Real.sqrt_nonneg x)
  rw [reciprocalGap_pole_add_left_budget_eq hh hx0 r q]
  unfold reciprocalGapCoupledPoleLeftBudget
  exact add_le_add hm (le_refl _)

end PseudoPrime.LLS.PaperStatements
