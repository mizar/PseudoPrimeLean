/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.HeightRatioPowerBounds

/-! # Explicit finite-fiber band parameters and coefficients -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- Growth order for degree m and precision c. At precision 20, write
g=20(m-1) and add the least positive integer at least 266g/1000. The paired
moment order below is chosen from the exact strict height-loss inequality.
Other precisions retain the original order c(m-1)+1. -/
def fiberBandGrowthOrder (m c : ℕ) : ℕ :=
  if c = 20 then 20 * (m - 1) + max 1 ((266 * (20 * (m - 1)) + 999) / 1000) else c * (m - 1) + 1

/-- Moment order paired with `fiberBandGrowthOrder`. At precision 20, use
the least integer strictly above 4gn²/s, where g=20(m-1), n=g+s, and s is
the added growth order; elsewhere retain 4cn²(m-1)+1. -/
def fiberBandMomentOrder (m c : ℕ) : ℕ :=
  if c = 20 then
    let g := 20 * (m - 1)
    let s := max 1 ((266 * g + 999) / 1000)
    (4 * g * (g + s) ^ 2) / s + 1
  else 4 * c * (fiberBandGrowthOrder m c) ^ 2 * (m - 1) + 1

/-- Positive natural coefficient 5(Q_r^(n²(m-1))+1)+1, with the explicit
growth and moment orders for m,c. The factorials remain symbolic, permitting
uniform numerical bounds without evaluating enormous natural numbers. -/
def fiberBandCoefficient (m c : ℕ) : ℕ :=
  5 *
      (quotientPowerBoundConstant (fiberBandMomentOrder m c) ^
          ((fiberBandGrowthOrder m c) ^ 2 * (m - 1)) +
        1) +
    1

/-- The prescribed growth order is positive for all m,c. Its final unit
summand supplies positivity for every later root extraction. -/
theorem fiberBandGrowthOrder_pos (m c : ℕ) : 0 < fiberBandGrowthOrder m c := by
  unfold fiberBandGrowthOrder
  split <;> omega

/-- The prescribed moment order is positive for all m,c. Its final unit
summand supplies positivity for the divisor-power estimate. -/
theorem fiberBandMomentOrder_pos (m c : ℕ) : 0 < fiberBandMomentOrder m c := by
  unfold fiberBandMomentOrder
  split <;> exact Nat.succ_pos _

/-- The explicit band coefficient is positive independently of m,c. Its
final unit summand also handles trivial growth-support exponents. -/
theorem fiberBandCoefficient_pos (m c : ℕ) : 0 < fiberBandCoefficient m c := by exact Nat.succ_pos _

/-- For positive degree m, the prescribed orders leave the exact height
gap m. Expand the definitions and use polynomial arithmetic. This replaces
the existential order choice in the uniform finite-fiber band theorem. -/
theorem fiberBand_parameters_small_loss {m : ℕ} (hm : 0 < m) (c : ℕ) :
    c * heightRatioLossExponent m (fiberBandGrowthOrder m c) (fiberBandMomentOrder m c) <
      fiberBandGrowthOrder m c * m * fiberBandMomentOrder m c := by
  by_cases hc : c = 20
  · subst c
    let g : ℕ := 20 * (m - 1)
    let s : ℕ := max 1 ((266 * g + 999) / 1000)
    let n : ℕ := fiberBandGrowthOrder m 20
    let r : ℕ := fiberBandMomentOrder m 20
    have hn : n = g + s := by
      dsimp only [n, g, s, fiberBandGrowthOrder]
      rw [ite_eq_left rfl]
    have hr : r = (4 * g * (g + s) ^ 2) / s + 1 := by
      dsimp only [r, n, fiberBandMomentOrder]
      rw [ite_eq_left rfl]
    have hs : 0 < s := by
      dsimp only [s]
      omega
    have hgap : 4 * g * n ^ 2 < s * r := by
      rw [hr, hn]
      have hdiv := (Nat.div_lt_iff_lt_mul hs).mp (Nat.lt_succ_self ((4 * g * (g + s) ^ 2) / s))
      simpa only [Nat.succ_eq_add_one, Nat.mul_comm] using hdiv
    have hmain := Nat.mul_lt_mul_of_pos_right hgap hm
    calc
      _ = g * m * r + (4 * g * n ^ 2) * m := by
        dsimp only [heightRatioLossExponent, g]
        ring
      _ < g * m * r + (s * r) * m := Nat.add_lt_add_left hmain _
      _ = n * m * r := by
        rw [hn]; ring
  · simp only [fiberBandGrowthOrder, fiberBandMomentOrder, ite_eq_right hc]
    have he :
      (c * (m - 1) + 1) * m * (4 * c * (c * (m - 1) + 1) ^ 2 * (m - 1) + 1) =
        c *
            heightRatioLossExponent m (c * (m - 1) + 1)
              (4 * c * (c * (m - 1) + 1) ^ 2 * (m - 1) + 1) +
          m := by
      dsimp only [heightRatioLossExponent]
      ring
    rw [he]
    exact Nat.lt_add_of_pos_right hm

end PseudoPrime.NumberTheory.Heilbronn
