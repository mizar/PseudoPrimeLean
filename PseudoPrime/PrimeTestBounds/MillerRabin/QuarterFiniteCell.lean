/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFiniteMajorant
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerTailInterval
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFiniteScalar

/-! # Endpoint-certified finite uniform quarter budgets -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- On a positive radius interval, endpoint bounds for the logarithm and negative
powers and a rational budget certify the scalar condition for every radius. -/
theorem quarter_finite_budget_cell {a b r L P Q V R H J : ℝ} (ha : 1 ≤ a) (har : a ≤ r)
    (hrb : r ≤ b) (hlog : Real.log (b ^ 2) ≤ L) (hP : (a ^ 2) ^ (-(27 / 25 : ℝ)) ≤ P)
    (hQ : (a ^ 2) ^ (-(29 / 50 : ℝ)) ≤ Q) (hV : (a ^ 2) ^ (-(83 / 100 : ℝ)) ≤ V)
    (hR : ((27 / 25 : ℝ) ^ 5 / 120) * (58721 / 1000000) * P * ((21 / 8 : ℝ) + L) ^ 5 ≤ R)
    (hH :
      ((27 / 25 : ℝ) ^ 5 / 120) * (58721 / 1000000) * P *
          quarterMomentPolynomial ((21 / 8 : ℝ) + L) ≤
        H)
    (hJ : quarterEulerClosedUpper L Q V ≤ J)
    (hcert :
      (27 / 25 : ℝ) ^ 5 * ((3117 / 400 : ℝ) - 7 / 200 - (29631 / 200 : ℝ) / a) -
          (15537999327 / 488281250000 : ℝ) * b -
          (4 * b + 3 * (1839 / 1000 : ℝ)) * R -
          H -
          4 * J -
          (39 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 ≥
        0) :
    (4 * r) * quarterReflectedScale r + (39 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 + quarterMomentScale r +
            (3 / 4 : ℝ) * r -
          (3117 / 400 : ℝ) * (27 / 25 : ℝ) ^ 5 +
        4 * quarterEulerClosedTailCap (r ^ 2) ≤
      (27 / 25 : ℝ) ^ 5 * ((24439 / 50000 : ℝ) * r - 7 / 200 - (29631 / 200 : ℝ) / r) -
        3 * Real.log (2 * Real.pi) * quarterReflectedScale r := by
  have ha0 : 0 < a := by linarith only [ha]
  have hr : 1 ≤ r := ha.trans har
  have hmin : a ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (by linarith only [ha]) har 2
  have hmax : r ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ (by linarith only [hr]) hrb 2
  have hlogr := (Real.log_le_log (sq_pos_of_pos (by linarith only [hr])) hmax).trans hlog
  have hp :=
    (Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos ha0) hmin
          (by norm_num only : (-(27 / 25 : ℝ)) ≤ 0)).trans
      hP
  have hq :=
    (Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos ha0) hmin
          (by norm_num only : (-(29 / 50 : ℝ)) ≤ 0)).trans
      hQ
  have hv :=
    (Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos ha0) hmin
          (by norm_num only : (-(83 / 100 : ℝ)) ≤ 0)).trans
      hV
  have hq0 : 0 ≤ Q := (Real.rpow_nonneg (sq_nonneg r) _).trans hq
  have hv0 : 0 ≤ V := (Real.rpow_nonneg (sq_nonneg r) _).trans hv
  have hru := quarter_finite_reflected_upper hr hlogr hp
  have hju :=
    quarter_euler_closed_upper (show (1 : ℝ) ≤ r ^ 2 by nlinarith only [hr]) hlogr hq0 hv0 hq hv
  have hR0 : 0 ≤ quarterReflectedScale r := by
    dsimp only [quarterReflectedScale]
    have hz : 0 ≤ (21 / 8 : ℝ) + Real.log (r ^ 2) := by
      have h := Real.log_nonneg (show (1 : ℝ) ≤ r ^ 2 by nlinarith only [hr])
      linarith only [h]
    positivity
  exact
    quarter_finite_budget_of_bounds ha0 har hrb hR0 (hru.1.trans hR) (hru.2.trans hH) (hju.trans hJ)
      hcert

end PseudoPrime.PrimeTestBounds.MillerRabin
