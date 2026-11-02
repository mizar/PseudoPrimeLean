/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.RationalPoleCommonScale
public import Mathlib.Analysis.SpecialFunctions.Log.Monotone

/-! # Reduced finite entrances for the selected fourth-pole scalar budget

The estimates here retain the already constructed fourth-pole kernel and its explicit error
coefficients. Varying the final coefficient does not make these application-specific numerical
inequalities general analysis API. They stay in LLS; actual quadratic maxima and Selfridge
transfers are supplied by consumer modules. No finite arithmetic certificate is regenerated.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The existing full fourth-pole scalar error at a coefficient and common scale.
Input: real coefficient, scale, conductor logarithm and original-level logarithm.
Definition: the fixed principal, character and local error terms at `x = c * L^2`.
Output: their total budget. Role: share one explicit inequality across three finite entrances. -/
noncomputable def fourPoleScaledBudget (c L F G : ℝ) : ℝ :=
  let x := c * L ^ 2
  (2501 / 10000 : ℝ) * F + 1003 + (24 * F + 793) * x ^ (-3 / 4 : ℝ) +
    (65 * x ^ (1 / 4 : ℝ) + 120 / Real.sqrt x) +
    (20 / Real.sqrt x) * (Real.log x / Real.log 2) * G

/-- The chosen logarithmic base lies in the decreasing range and has a small logarithm.
Claim: its logarithm is between two and seventy-two.
Proof: compare powers of two and ten with the base and use logarithm bounds.
Role: certify a reusable half-line estimate for the selected finite-entrance budget. -/
private theorem fourPole_log_base_bounds :
    (2 : ℝ) ≤ Real.log 100000000 ∧ Real.log (100000000 : ℝ) ≤ 72 := by
  constructor
  · have h :=
      Real.log_le_log (by norm_num only : (0 : ℝ) < 8) (by norm_num only : (8 : ℝ) ≤ 100000000)
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num only, Real.log_pow] at h
    norm_num only at h
    linarith only [h, Real.log_two_gt_d9]
  · have h := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 10)
    rw [show (100000000 : ℝ) = 10 ^ (8 : ℕ) by norm_num only, Real.log_pow]
    norm_num only
    linarith only [h]

/-- Above the selected base, the logarithm is at most one hundredth of the square root.
Input: a real scale at least one hundred million. Claim: the stated half-line bound.
Proof: transfer the logarithm-to-square-root ratio by antitonicity.
Role: retain the local-exclusion term within the reduced fourth-pole error budget. -/
theorem fourPole_log_le_sqrt {L : ℝ} (hL : 100000000 ≤ L) : Real.log L ≤ Real.sqrt L / 100 := by
  have hb := fourPole_log_base_bounds
  have hb0 : (0 : ℝ) < 100000000 := by norm_num only
  have hL0 := hb0.trans_le hL
  have he : Real.exp 2 ≤ (100000000 : ℝ) := (Real.le_log_iff_exp_le hb0).mp hb.1
  have ht := Real.log_div_sqrt_antitoneOn he (he.trans hL) hL
  have hs : (10000 : ℝ) ≤ Real.sqrt 100000000 := Real.le_sqrt_of_sq_le (by norm_num only)
  have hr : Real.log (100000000 : ℝ) / Real.sqrt 100000000 ≤ 1 / 100 :=
    (div_le_iff₀ (Real.sqrt_pos.mpr hb0)).mpr (by linarith only [hb.2, hs])
  have h := (div_le_iff₀ (Real.sqrt_pos.mpr hL0)).mp (ht.trans hr)
  linarith only [h]

/-- The selected coefficient range has explicit common-scale power and logarithm bounds.
Input: a scale above one hundred million, a coefficient from 777/1000 through one,
and a nonnegative upper fourth root of that coefficient. Claim: all listed scale bounds.
Proof: monotonicity of powers, square roots and logarithms.
Role: evaluate the full scalar error without changing the fourth-pole kernel. -/
theorem fourPole_scaled_bounds {c s L : ℝ} (hL : 100000000 ≤ L) (hc : (777 / 1000 : ℝ) ≤ c)
    (hc1 : c ≤ 1) (hs : 0 ≤ s) (hcs : c ≤ s ^ 4) :
    let x := c * L ^ 2
    L ≤ x ∧
      x ≤ L ^ 2 ∧
      (22 / 25 : ℝ) * L ≤ Real.sqrt x ∧
      x ^ (1 / 4 : ℝ) ≤ s * Real.sqrt L ∧
      x ^ (-3 / 4 : ℝ) ≤ 2 / L ∧ Real.log x ≤ Real.sqrt L / 50 := by
  let x := c * L ^ 2
  have hL0 : 0 < L := (by norm_num only : (0 : ℝ) < 100000000).trans_le hL
  have hL2 : 2 ≤ L := by linarith only [hL]
  have hxl : L ≤ x := by
    have hm := mul_le_mul_of_nonneg_right hc (sq_nonneg L)
    dsimp only [x]
    nlinarith only [hm, hL, sq_nonneg (L - 2)]
  have hxu : x ≤ L ^ 2 := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hc1 (sq_nonneg L)
  have hx0 : 0 < x := hL0.trans_le hxl
  have hsl : (22 / 25 : ℝ) * L ≤ Real.sqrt x := by
    apply (Real.le_sqrt (mul_nonneg (by norm_num only) hL0.le) hx0.le).mpr
    have hm := mul_le_mul_of_nonneg_right hc (sq_nonneg L)
    dsimp only [x]
    nlinarith only [hm, sq_nonneg L]
  have hquarter : x ^ (1 / 4 : ℝ) ≤ s * Real.sqrt L := by
    have hsL4 : (Real.sqrt L) ^ 4 = L ^ 2 :=
      calc
        _ = ((Real.sqrt L) ^ 2) ^ 2 := by ring
        _ = L ^ 2 := congrArg (fun z : ℝ ↦ z ^ 2) (Real.sq_sqrt hL0.le)
    have hbound : x ≤ (s * Real.sqrt L) ^ 4 := by
      rw [mul_pow, hsL4]
      exact mul_le_mul_of_nonneg_right hcs (sq_nonneg L)
    have h := Real.rpow_le_rpow hx0.le hbound (by norm_num only : (0 : ℝ) ≤ 1 / 4)
    rw [← Real.rpow_natCast (s * Real.sqrt L) 4, ←
      Real.rpow_mul (mul_nonneg hs (Real.sqrt_nonneg L))] at h
    norm_num only [Real.rpow_one] at h
    exact h
  have hnegative : x ^ (-3 / 4 : ℝ) ≤ 2 / L := by
    have hx1 : 1 ≤ x := (by norm_num only : (1 : ℝ) ≤ 2).trans (hL2.trans hxl)
    have h := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num only : (-3 / 4 : ℝ) ≤ -(1 / 2))
    rw [Real.rpow_neg hx0.le] at h
    have hn : x ^ (-3 / 4 : ℝ) ≤ 1 / Real.sqrt x := by
      simpa only [Real.sqrt_eq_rpow, one_div] using h
    have hd : 1 / Real.sqrt x ≤ 2 / L :=
      (div_le_div_iff₀ (Real.sqrt_pos.mpr hx0) hL0).mpr (by linarith only [hsl, hL0])
    exact hn.trans hd
  have hlog : Real.log x ≤ Real.sqrt L / 50 := by
    have h := Real.log_le_log hx0 hxu
    rw [Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h, fourPole_log_le_sqrt hL]
  exact ⟨hxl, hxu, hsl, hquarter, hnegative, hlog⟩

/-- The local exclusion budget occupies at most seven tenths of the square-root allowance.
Input: a large scale, its lower square-root comparison and its logarithmic cap.
Claim: the fixed local-cost term is bounded. Proof: clear positive denominators.
Role: isolate the local term in the reduced fourth-pole budget. -/
private theorem fourPole_scaled_local {x L G : ℝ} (hL : 100000000 ≤ L) (hxl : L ≤ x)
    (hsl : (22 / 25 : ℝ) * L ≤ Real.sqrt x) (hlog : Real.log x ≤ Real.sqrt L / 50)
    (hG : G ≤ L + 2) :
    (20 / Real.sqrt x) * (Real.log x / Real.log 2) * G ≤ (7 / 10 : ℝ) * Real.sqrt L := by
  have hL0 : 0 < L := (by norm_num only : (0 : ℝ) < 100000000).trans_le hL
  have hx0 : 0 < x := hL0.trans_le hxl
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hlog0 : 0 ≤ Real.log x :=
    Real.log_nonneg ((by norm_num only : (1 : ℝ) ≤ 100000000).trans (hL.trans hxl))
  have htwo : (69 / 100 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have htwo0 : 0 < Real.log 2 := Real.log_pos (by norm_num only : (1 : ℝ) < 2)
  have hden : 20 / Real.sqrt x ≤ 23 / L :=
    (div_le_div_iff₀ hsx hL0).mpr (by linarith only [hsl, hL0])
  have hlogcap : Real.log x / Real.log 2 ≤ Real.sqrt L / 34 := by
    apply (div_le_iff₀ htwo0).mpr
    have hm := mul_le_mul_of_nonneg_right htwo (Real.sqrt_nonneg L)
    nlinarith only [hlog, hm, Real.sqrt_nonneg L]
  have hr : (23 / L) * (Real.sqrt L / 34) * (L + 2) ≤ (7 / 10 : ℝ) * Real.sqrt L :=
    calc
      _ = ((23 / 34 : ℝ) * (L + 2) / L) * Real.sqrt L := by ring
      _ ≤ _ :=
        mul_le_mul_of_nonneg_right ((div_le_iff₀ hL0).mpr (by linarith only [hL]))
          (Real.sqrt_nonneg L)
  calc
    _ ≤ (20 / Real.sqrt x) * (Real.log x / Real.log 2) * (L + 2) :=
      mul_le_mul_of_nonneg_left hG
        (mul_nonneg (div_nonneg (by norm_num only) hsx.le) (div_nonneg hlog0 htwo0.le))
    _ ≤ (20 / Real.sqrt x) * (Real.sqrt L / 34) * (L + 2) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlogcap (div_nonneg (by norm_num only) hsx.le))
        (by linarith only [hL])
    _ ≤ (23 / L) * (Real.sqrt L / 34) * (L + 2) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hden (div_nonneg (Real.sqrt_nonneg L) (by norm_num only)))
        (by linarith only [hL])
    _ ≤ _ := hr

/-- The full selected fourth-pole budget has a reduced square-root error allowance.
Input: a large common scale, a coefficient from 777/1000 through one, a nonnegative
upper fourth root, and conductor and level logarithms at most the scale plus two.
Claim: the budget is at most its linear term plus `(65*s+1)*sqrt L`.
Proof: use the scale bounds, bound the negative-power term by forty-nine and absorb constants.
Role: one common scalar estimate for all three improved finite entrances. -/
theorem fourPole_scale_budget_le {c s L F G : ℝ} (hL : 100000000 ≤ L) (hc : (777 / 1000 : ℝ) ≤ c)
    (hc1 : c ≤ 1) (hs : 0 ≤ s) (hcs : c ≤ s ^ 4) (hF : F ≤ L + 2) (hG : G ≤ L + 2) :
    fourPoleScaledBudget c L F G ≤ (2501 / 10000 : ℝ) * L + (65 * s + 1) * Real.sqrt L := by
  let x := c * L ^ 2
  obtain ⟨hxl, _hxu, hsl, hp, hn, hlog⟩ := fourPole_scaled_bounds hL hc hc1 hs hcs
  have hL0 : 0 < L := (by norm_num only : (0 : ℝ) < 100000000).trans_le hL
  have hx0 : 0 < x := hL0.trans_le hxl
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hnegative : (24 * F + 793) * x ^ (-3 / 4 : ℝ) ≤ 49 := by
    calc
      _ ≤ (24 * L + 841) * x ^ (-3 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith only [hF]) (Real.rpow_nonneg hx0.le _)
      _ ≤ (24 * L + 841) * (2 / L) := mul_le_mul_of_nonneg_left hn (by linarith only [hL])
      _ = (48 * L + 1682) / L := by ring
      _ ≤ 49 := (div_le_iff₀ hL0).mpr (by linarith only [hL])
  have hi : 120 / Real.sqrt x ≤ (1 : ℝ) := (div_le_iff₀ hsx).mpr (by linarith only [hsl, hL])
  have hquarter := mul_le_mul_of_nonneg_left hp (by norm_num only : (0 : ℝ) ≤ 65)
  have hlocal := fourPole_scaled_local hL hxl hsl hlog hG
  have hmain := mul_le_mul_of_nonneg_left hF (by norm_num only : (0 : ℝ) ≤ 2501 / 10000)
  have hsL : (10000 : ℝ) ≤ Real.sqrt L :=
    Real.le_sqrt_of_sq_le
      (by
        norm_num only; exact hL)
  change
    (2501 / 10000 : ℝ) * F + 1003 + (24 * F + 793) * x ^ (-3 / 4 : ℝ) +
        (65 * x ^ (1 / 4 : ℝ) + 120 / Real.sqrt x) +
        (20 / Real.sqrt x) * (Real.log x / Real.log 2) * G ≤
      (2501 / 10000 : ℝ) * L + (65 * s + 1) * Real.sqrt L
  nlinarith only [hnegative, hi, hquarter, hlocal, hmain, hsL]

/-- A rational lower square root and a positive entrance margin close the scalar gap.
Input: the selected coefficient range, root bounds, a scale above the squared entrance,
and a strict rational margin at that entrance. Claim: the complete error is below the
actual fourth-pole principal gap. Proof: transfer the entrance margin along the half-line.
Role: use one proof for all three reduced finite-entrance certificates. -/
theorem fourPole_scale_gap {c r s t L F G : ℝ} (hL : 100000000 ≤ L) (hc : (777 / 1000 : ℝ) ≤ c)
    (hc1 : c ≤ 1) (hr : 0 ≤ r) (hs : 0 ≤ s) (hrc : r ^ 2 ≤ c) (hcs : c ≤ s ^ 4) (ht : 0 ≤ t)
    (hLt : t ^ 2 ≤ L) (hmargin : 65 * s + 1 < ((28379 / 100000 : ℝ) * r - 2501 / 10000) * t)
    (hF : F ≤ L + 2) (hG : G ≤ L + 2) :
    fourPoleScaledBudget c L F G <
      Real.sqrt (c * L ^ 2) *
        (2 * ((484820459 / 528581976 : ℝ) * Real.exp (-(14 / 13))) -
          (2 * (13 / 25 : ℝ) * Real.exp (14 / 25) / (1 + 13 / 25) ^ 4)) := by
  let x := c * L ^ 2
  have hL0 : 0 < L := (by norm_num only : (0 : ℝ) < 100000000).trans_le hL
  have hbounds := fourPole_scaled_bounds hL hc hc1 hs hcs
  have hx0 : 0 < x := hL0.trans_le hbounds.1
  have hsqrt : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL0
  have hsbig : t ≤ Real.sqrt L := (Real.le_sqrt ht hL0.le).mpr hLt
  have hmargin0 : 0 < ((28379 / 100000 : ℝ) * r - 2501 / 10000) * t :=
    (show 0 < 65 * s + 1 by nlinarith only [hs]).trans hmargin
  have hD : 0 < (28379 / 100000 : ℝ) * r - 2501 / 10000 := pos_of_mul_pos_left hmargin0 ht
  have hsmall := hmargin.trans_le (mul_le_mul_of_nonneg_left hsbig hD.le)
  have hprod := mul_lt_mul_of_pos_right hsmall hsqrt
  rw [mul_assoc, ← pow_two, Real.sq_sqrt hL0.le] at hprod
  have hb := fourPole_scale_budget_le hL hc hc1 hs hcs hF hG
  have hroot : r * L ≤ Real.sqrt x :=
    (Real.le_sqrt (mul_nonneg hr hL0.le) hx0.le).mpr
      (by simpa only [mul_pow] using mul_le_mul_of_nonneg_right hrc (sq_nonneg L))
  calc
    _ < (28379 / 100000 : ℝ) * (r * L) := by nlinarith only [hb, hprod]
    _ ≤ (28379 / 100000 : ℝ) * Real.sqrt x :=
      mul_le_mul_of_nonneg_left hroot (by norm_num only : (0 : ℝ) ≤ 28379 / 100000)
    _ = Real.sqrt x * (28379 / 100000 : ℝ) := mul_comm _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left fourPole_sharp_principal_gap (Real.sqrt_nonneg x)

end PseudoPrime.LLS.PaperStatements
