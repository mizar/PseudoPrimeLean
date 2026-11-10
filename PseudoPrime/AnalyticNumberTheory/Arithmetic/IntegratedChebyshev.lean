/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PowerLogBoundarySummation

/-! # Integrated Chebyshev function

Finite-sum and endpoint estimates for the integrated Chebyshev function.
-/

public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- The integrated Chebyshev function, expressed as a finite weighted sum.
For a real endpoint `x`, this is `x * ψ(x)` minus the first moment of the
von Mangoldt weights. Its difference and smoothing estimates are used to
transfer bounds on the integrated function to bounds on `ψ`. -/
noncomputable def psiIntegralSum (x : ℝ) : ℝ :=
  x * Chebyshev.psi x - ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt m * (m : ℝ)

/-- For `0 < a ≤ b`, express the difference of the integrated Chebyshev
function using the logarithmically weighted Mangoldt sum. The proof specializes
partial summation at exponent `-1`. -/
theorem psi1_diff {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    psiIntegralSum b - psiIntegralSum a =
      b * logWeightedMangoldtSum b - a * logWeightedMangoldtSum a -
        ∫ t in a..b, logWeightedMangoldtSum t := by
  have h := power_mangoldt_tail_eq_log_integral (-1) ha hab
  norm_num only [neg_neg, neg_one_sq, sub_self, Real.rpow_zero, mul_one, Real.rpow_one,
    neg_one_mul] at h
  have hsplit := power_prefix_sum_split hab (fun m ↦ ArithmeticFunction.vonMangoldt m * (m : ℝ))
  dsimp only [psiIntegralSum]
  linarith only [h, hsplit]

/-- Express the integrated Chebyshev function as the finite sum of the
von Mangoldt weights times `x - m`. Distribute the defining sums. -/
theorem psi1_eq_sum (x : ℝ) :
    psiIntegralSum x = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt m * (x - m) := by
  rw [psiIntegralSum, psi_eq_positive_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  ring

/-- For `0 < a ≤ b`, bound the integrated Chebyshev difference above and
below by the interval length times the endpoint values of `ψ`. Positivity of
the Mangoldt weights gives the bounds term by term. -/
theorem psi1_bounds {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (b - a) * Chebyshev.psi a ≤ psiIntegralSum b - psiIntegralSum a ∧
      psiIntegralSum b - psiIntegralSum a ≤ (b - a) * Chebyshev.psi b := by
  let S := Finset.Ioc ⌊a⌋₊ ⌊b⌋₊
  have haTail :
    a * (∑ m ∈ S, ArithmeticFunction.vonMangoldt m) ≤
      ∑ m ∈ S, ArithmeticFunction.vonMangoldt m * (m : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m hm
    have hm' := Finset.mem_Ioc.mp hm
    have hma : a ≤ (m : ℝ) := (Nat.floor_lt ha.le).mp hm'.1 |>.le
    nlinarith only [hma, ArithmeticFunction.vonMangoldt_nonneg (n := m)]
  have hbTail :
    (∑ m ∈ S, ArithmeticFunction.vonMangoldt m * (m : ℝ)) ≤
      b * (∑ m ∈ S, ArithmeticFunction.vonMangoldt m) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m hm
    have hm' := Finset.mem_Ioc.mp hm
    have hmb : (m : ℝ) ≤ b := (Nat.cast_le.mpr hm'.2).trans (Nat.floor_le (le_trans ha.le hab))
    nlinarith only [hmb, ArithmeticFunction.vonMangoldt_nonneg (n := m)]
  have hpsi := power_prefix_sum_split hab (fun m ↦ ArithmeticFunction.vonMangoldt m)
  have hweight := power_prefix_sum_split hab (fun m ↦ ArithmeticFunction.vonMangoldt m * (m : ℝ))
  rw [← psi_eq_positive_sum, ← psi_eq_positive_sum] at hpsi
  change Chebyshev.psi b = Chebyshev.psi a + ∑ m ∈ S, ArithmeticFunction.vonMangoldt m at hpsi
  change
    (∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, ArithmeticFunction.vonMangoldt m * (m : ℝ)) =
      (∑ m ∈ Finset.Ioc 0 ⌊a⌋₊, ArithmeticFunction.vonMangoldt m * (m : ℝ)) +
        ∑ m ∈ S, ArithmeticFunction.vonMangoldt m * (m : ℝ) at hweight
  have hpa := congrArg (fun x : ℝ ↦ a * x) hpsi
  have hpb := congrArg (fun x : ℝ ↦ b * x) hpsi
  dsimp only [psiIntegralSum]
  constructor <;> nlinarith only [hpa, hpb, hweight, haTail, hbTail]

/-- Given error bounds for the integrated Chebyshev function at positive
endpoints `a < b`, bound `ψ` at both endpoints. The proof combines the
finite-sum sandwich with the endpoint errors and divides by `b - a`. -/
theorem psi1_squeeze {a b Ea Eb : ℝ} (ha : 0 < a) (hab : a < b)
    (hea : |psiIntegralSum a - a ^ 2 / 2| ≤ Ea) (heb : |psiIntegralSum b - b ^ 2 / 2| ≤ Eb) :
    Chebyshev.psi a ≤ (a + b) / 2 + (Ea + Eb) / (b - a) ∧
      (a + b) / 2 - (Ea + Eb) / (b - a) ≤ Chebyshev.psi b := by
  have bounds := psi1_bounds ha hab.le
  have hea' := abs_le.mp hea
  have heb' := abs_le.mp heb
  have hh : 0 < b - a := sub_pos.mpr hab
  have hupper : (b - a) * Chebyshev.psi a ≤ (b ^ 2 - a ^ 2) / 2 + (Ea + Eb) := by
    linarith only [bounds.1, hea'.1, heb'.2]
  have hlower : (b ^ 2 - a ^ 2) / 2 - (Ea + Eb) ≤ (b - a) * Chebyshev.psi b := by
    linarith only [bounds.2, hea'.2, heb'.1]
  have hu : Chebyshev.psi a - (a + b) / 2 ≤ (Ea + Eb) / (b - a) :=
    (le_div_iff₀ hh).2 (by nlinarith only [hupper])
  have hl : -(Ea + Eb) / (b - a) ≤ Chebyshev.psi b - (a + b) / 2 :=
    (div_le_iff₀ hh).2 (by nlinarith only [hlower])
  rw [neg_div] at hl
  constructor <;> linarith only [hu, hl]

/-- For positive endpoints `a < b`, a bound for the centered integrated
Chebyshev difference gives upper and lower bounds for the endpoint values of
`ψ`. This form preserves cancellation in the explicit formula for the
difference and divides the resulting error by the interval length. -/
theorem psi1_difference_squeeze {a b E : ℝ} (ha : 0 < a) (hab : a < b)
    (he : |(psiIntegralSum b - psiIntegralSum a) - (b ^ 2 - a ^ 2) / 2| ≤ E) :
    Chebyshev.psi a ≤ (a + b) / 2 + E / (b - a) ∧ (a + b) / 2 - E / (b - a) ≤ Chebyshev.psi b := by
  have bounds := psi1_bounds ha hab.le
  have he' := abs_le.mp he
  have hh : 0 < b - a := sub_pos.mpr hab
  have hu : Chebyshev.psi a - (a + b) / 2 ≤ E / (b - a) :=
    (le_div_iff₀ hh).2 (by nlinarith only [bounds.1, he'.2])
  have hl : -E / (b - a) ≤ Chebyshev.psi b - (a + b) / 2 :=
    (div_le_iff₀ hh).2 (by nlinarith only [bounds.2, he'.1])
  rw [neg_div] at hl
  constructor <;> linarith only [hu, hl]

/-- If `0 < h < x` and both adjacent centered integrated differences have
error at most `E`, then the error in `ψ(x)` is at most `h / 2 + E / h`.
Apply the endpoint bounds on each side of `x`; this is the smoothing step
for a centered explicit-formula difference. -/
theorem psi1_symmetric_squeeze {x h E : ℝ} (hx : h < x) (hh : 0 < h)
    (hl : |(psiIntegralSum x - psiIntegralSum (x - h)) - (x ^ 2 - (x - h) ^ 2) / 2| ≤ E)
    (hu : |(psiIntegralSum (x + h) - psiIntegralSum x) - ((x + h) ^ 2 - x ^ 2) / 2| ≤ E) :
    |Chebyshev.psi x - x| ≤ h / 2 + E / h := by
  have hx0 : 0 < x := by linarith only [hx, hh]
  have hxm : 0 < x - h := sub_pos.mpr hx
  have hl' := (psi1_difference_squeeze hxm (by linarith only [hh]) hl).2
  have hu' := (psi1_difference_squeeze hx0 (by linarith only [hh]) hu).1
  have h1 : x - (x - h) = h := by ring
  have h2 : x + h - x = h := by ring
  rw [h1] at hl'
  rw [h2] at hu'
  apply abs_le.mpr
  constructor <;> linarith only [hl', hu']

end PseudoPrime.AnalyticNumberTheory.Arithmetic
