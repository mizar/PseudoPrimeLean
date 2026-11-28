/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import PseudoPrime.Analysis.LogTaylorBounds

/-! # Curvature bounds for the central quarter comparison -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The polynomial controlling the second derivative of a power times a log power. -/
def quarterPsi08LogCurvature (p k z : ℝ) : ℝ :=
  p * (p + 1) * z ^ 2 - 2 * k * (2 * p + 1) * z + 4 * k * (k - 1)

/-- The two extremal curvature polynomials in the central quarter comparison
are positive above their respective logarithmic thresholds. -/
theorem quarter_psi08_curvature {t : ℝ} (ht : 0 ≤ t) :
    0 < quarterPsi08LogCurvature (29 / 25) 5 (101 / 10 + t) ∧
      0 < quarterPsi08LogCurvature (29 / 25) 2 (7 + t) := by
  constructor <;> unfold quarterPsi08LogCurvature <;> nlinarith only [ht, sq_nonneg t]

/-- The box estimate and two endpoint estimates cover the central log interval
once the comparison function is concave from radius 42 onward. -/
theorem quarter_psi08_pos {G : ℝ → ℝ} {L : ℝ} (hL : L ∈ Set.Icc 76 533)
    (hbox : ∀ r ∈ Set.Icc 37 42, 2 < G r) (hG : ConcaveOn ℝ (Set.Ici 42) G) (hl : 3.65 < G 42)
    (hr : 1 / 2000 < G (533 / 2)) : 0 < G (L / 2) := by
  have hmin : (76 : ℝ) ≤ L := hL.1
  have hmax : L ≤ (533 : ℝ) := hL.2
  by_cases h : L / 2 ≤ 42
  · exact lt_trans (by norm_num only) (hbox _ ⟨by linarith only [hmin], h⟩)
  have hseg : L / 2 ∈ segment ℝ 42 (533 / 2) := by
    rw [segment_eq_Icc (by norm_num only : (42 : ℝ) ≤ 533 / 2)]
    exact ⟨le_of_not_ge h, by linarith only [hmax]⟩
  exact
    (lt_min (lt_trans (by norm_num only) hl) (lt_trans (by norm_num only) hr)).trans_le
      (hG.ge_on_segment (by norm_num only [Set.mem_Ici]) (by norm_num only [Set.mem_Ici]) hseg)

/-- Differentiate the power part and the logarithmic part of a central error term. -/
theorem quarter_logPower_hasDerivAt {r p b : ℝ} (hr : 0 < r) (k : ℕ) :
    HasDerivAt (fun x : ℝ ↦ x ^ (-p) * (b + 2 * Real.log x) ^ k)
      ((-p * r ^ (-p - 1)) * (b + 2 * Real.log r) ^ k +
        r ^ (-p) * ((k : ℝ) * (b + 2 * Real.log r) ^ (k - 1) * (2 * r⁻¹)))
      r := by
  have hlog := (Real.hasDerivAt_log hr.ne').const_mul 2
  have hz := (hlog.const_add b).pow k
  exact (Real.hasDerivAt_rpow_const (Or.inl hr.ne')).mul hz

/-- For positive log degree the derivative factors into one real power,
one natural power and a linear polynomial in the shifted logarithm. -/
theorem quarter_logPower_deriv_succ {r p b : ℝ} (hr : 0 < r) (k : ℕ) :
    deriv (fun x : ℝ ↦ x ^ (-p) * (b + 2 * Real.log x) ^ (k + 1)) r =
      r ^ (-p - 1) * (b + 2 * Real.log r) ^ k * (2 * ((k : ℝ) + 1) - p * (b + 2 * Real.log r)) := by
  rw [(quarter_logPower_hasDerivAt (p := p) (b := b) hr (k + 1)).deriv, Nat.add_sub_cancel,
    Nat.cast_add, Nat.cast_one, pow_succ, Real.rpow_sub hr, Real.rpow_one, div_eq_mul_inv]
  ring

/-- For logarithmic degree at least two, the second derivative factors
through the curvature polynomial used by the central comparison. -/
theorem quarter_logPower_deriv2 {r p b : ℝ} (hr : 0 < r) (k : ℕ) :
    deriv (deriv (fun x : ℝ ↦ x ^ (-p) * (b + 2 * Real.log x) ^ (k + 2))) r =
      r ^ (-p - 2) * (b + 2 * Real.log r) ^ k *
        quarterPsi08LogCurvature p ((k : ℝ) + 2) (b + 2 * Real.log r) := by
  have hlog := ((Real.hasDerivAt_log hr.ne').const_mul 2).const_add b
  have hp := Real.hasDerivAt_rpow_const (p := -p - 1) (Or.inl hr.ne')
  have h := (hp.mul (hlog.pow (k + 1))).mul (((hlog.const_mul p).neg).const_add (2 * ((k : ℝ) + 2)))
  have he :
    deriv (fun x : ℝ ↦ x ^ (-p) * (b + 2 * Real.log x) ^ (k + 2)) =ᶠ[nhds r] fun x ↦
      x ^ (-p - 1) * (b + 2 * Real.log x) ^ (k + 1) *
        (2 * ((k : ℝ) + 2) + -(p * (b + 2 * Real.log x))) := by
    filter_upwards [Ioi_mem_nhds hr] with x hx
    have hx' : 0 < x := hx
    rw [quarter_logPower_deriv_succ hx' (k + 1), Nat.cast_add, Nat.cast_one]
    ring
  rw [he.deriv_eq]
  simp only [Pi.mul_apply, Pi.pow_apply, Pi.neg_apply] at h
  refine h.deriv.trans ?_
  rw [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]
  have hf : r ^ (-p - 1) * r⁻¹ = r ^ (-p - 1 - 1) := by
    conv_rhs => rw [Real.rpow_sub hr, Real.rpow_one, div_eq_mul_inv]
  rw [show -p - 1 - 1 = -p - 2 by ring] at hf ⊢
  unfold quarterPsi08LogCurvature
  linear_combination
    ((k : ℝ) + 1) * 2 * (b + 2 * Real.log r) ^ k *
        (2 * ((k : ℝ) + 2) + -(p * (b + 2 * Real.log r))) *
        hf -
      (b + 2 * Real.log r) ^ k * (b + 2 * Real.log r) * (p * 2) * hf

/-- The zero-degree term is a real power, with the usual second derivative. -/
theorem quarter_logPower_deriv2_zero {r p : ℝ} (hr : 0 < r) :
    deriv (deriv (fun x : ℝ ↦ x ^ (-p))) r = r ^ (-p - 2) * (p * (p + 1)) := by
  have he : deriv (fun x : ℝ ↦ x ^ (-p)) =ᶠ[nhds r] (fun x : ℝ ↦ -p * x ^ (-p - 1)) := by
    filter_upwards [Ioi_mem_nhds hr] with x hx
    exact (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hx))).deriv
  rw [he.deriv_eq]
  refine ((Real.hasDerivAt_rpow_const (p := -p - 1) (Or.inl hr.ne')).const_mul (-p)).deriv.trans ?_
  rw [show -p - 1 - 1 = -p - 2 by ring]
  ring

/-- At degree one, the second derivative has a linear logarithmic factor. -/
theorem quarter_logPower_deriv2_one {r p b : ℝ} (hr : 0 < r) :
    deriv (deriv (fun x : ℝ ↦ x ^ (-p) * (b + 2 * Real.log x))) r =
      r ^ (-p - 2) * (p * (p + 1) * (b + 2 * Real.log r) - 2 * (2 * p + 1)) := by
  have he :
    deriv (fun x : ℝ ↦ x ^ (-p) * (b + 2 * Real.log x)) =ᶠ[nhds r]
      (fun x : ℝ ↦ x ^ (-p - 1) * (2 + -(p * (b + 2 * Real.log x)))) := by
    filter_upwards [Ioi_mem_nhds hr] with x hx
    have hx' : 0 < x := hx
    simpa only [Nat.zero_add, pow_one, pow_zero, mul_one, Nat.cast_zero, zero_add,
      sub_eq_add_neg] using quarter_logPower_deriv_succ (p := p) (b := b) hx' 0
  rw [he.deriv_eq]
  have hlog := ((Real.hasDerivAt_log hr.ne').const_mul 2).const_add b
  have hp := Real.hasDerivAt_rpow_const (p := -p - 1) (Or.inl hr.ne')
  refine (hp.mul (((hlog.const_mul p).neg).const_add 2)).deriv.trans ?_
  have hf : r ^ (-p - 1) * r⁻¹ = r ^ (-p - 1 - 1) := by
    conv_rhs => rw [Real.rpow_sub hr, Real.rpow_one, div_eq_mul_inv]
  rw [show -p - 1 - 1 = -p - 2 by ring] at hf ⊢
  simp only [Pi.neg_apply]
  linear_combination (-2 * p) * hf

/-- In the central comparison, increasing the power exponent or decreasing the
logarithmic degree preserves the lower curvature bound. -/
private theorem curvature_compare {p k K z : ℝ} (hp : 29 / 25 ≤ p) (hkK : k ≤ K) (hK : K ≤ 5)
    (hz : 7 ≤ z) : quarterPsi08LogCurvature (29 / 25) K z ≤ quarterPsi08LogCurvature p k z := by
  have hpz : 0 ≤ (p + 29 / 25 + 1) * z - 4 * k := by
    nlinarith only [hp, hkK, hK, hz, mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hz)]
  have hkz : 0 ≤ 2 * (2 * (29 / 25 : ℝ) + 1) * z - 4 * (K + k - 1) := by linarith only [hkK, hK, hz]
  have h₁ := mul_nonneg (sub_nonneg.mpr hp) (mul_nonneg (show 0 ≤ z by linarith only [hz]) hpz)
  have h₂ := mul_nonneg (sub_nonneg.mpr hkK) hkz
  unfold quarterPsi08LogCurvature
  linarith only [h₁, h₂]

/-- Every curvature polynomial of the central main comparison is positive
above its shifted-logarithm threshold. -/
theorem quarter_psi08_main_curvature {p k z : ℝ} (hp : 29 / 25 ≤ p) (hK : k ≤ 5)
    (hz : 101 / 10 ≤ z) : 0 < quarterPsi08LogCurvature p k z := by
  have h := (quarter_psi08_curvature (sub_nonneg.mpr hz)).1
  rw [show 101 / 10 + (z - 101 / 10) = z by ring] at h
  exact h.trans_le (curvature_compare hp hK (le_refl _) (by linarith only [hz]))

/-- The closed Euler tail uses degrees at most two and an unshifted logarithm,
for which the smaller threshold suffices. -/
theorem quarter_psi08_tail_curvature {p k z : ℝ} (hp : 29 / 25 ≤ p) (hK : k ≤ 2) (hz : 7 ≤ z) :
    0 < quarterPsi08LogCurvature p k z := by
  have h := (quarter_psi08_curvature (sub_nonneg.mpr hz)).2
  rw [show 7 + (z - 7) = z by ring] at h
  exact h.trans_le (curvature_compare hp hK (by norm_num only) hz)

/-- A shifted logarithmic power times a real power is convex on a positive
ray where the curvature polynomial and shifted logarithm are nonnegative. -/
theorem quarter_logPower_convex {a p b : ℝ} (ha : 0 < a) (k : ℕ)
    (hz : ∀ x ∈ Set.Ici a, 0 < b + 2 * Real.log x)
    (hc : ∀ x ∈ Set.Ici a, 0 ≤ quarterPsi08LogCurvature p k (b + 2 * Real.log x)) :
    ConvexOn ℝ (Set.Ici a) (fun x : ℝ ↦ x ^ (-p) * (b + 2 * Real.log x) ^ k) := by
  apply convexOn_of_deriv2_nonneg' (convex_Ici a)
  · exact fun x hx ↦
      (quarter_logPower_hasDerivAt (ha.trans_le hx) k) |>.differentiableAt.differentiableWithinAt
  · intro x hx
    have hp : 0 < x := ha.trans_le hx
    have he :
      deriv (fun t : ℝ ↦ t ^ (-p) * (b + 2 * Real.log t) ^ k) =ᶠ[nhds x] fun t ↦
        (-p * t ^ (-p - 1)) * (b + 2 * Real.log t) ^ k +
          t ^ (-p) * ((k : ℝ) * (b + 2 * Real.log t) ^ (k - 1) * (2 * t⁻¹)) := by
      filter_upwards [Ioi_mem_nhds hp] with t ht
      exact (quarter_logPower_hasDerivAt ht k).deriv
    apply (DifferentiableAt.congr_of_eventuallyEq ?_ he).differentiableWithinAt
    have hn : x ≠ 0 := hp.ne'
    fun_prop (disch := assumption)
  · intro x hx
    have hp : 0 < x := ha.trans_le hx
    have h := hc x hx
    have hy := hz x hx
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
    rcases k with _ | _ | k
    · simp only [pow_zero, mul_one] at ⊢
      rw [quarter_logPower_deriv2_zero hp]
      apply mul_nonneg (Real.rpow_nonneg hp.le _)
      apply nonneg_of_mul_nonneg_left _ (sq_pos_of_pos hy)
      norm_num only [quarterPsi08LogCurvature, Nat.cast_zero, zero_mul, sub_zero, add_zero] at h
      linarith only [h]
    · change 0 ≤ deriv (deriv (fun t : ℝ ↦ t ^ (-p) * (b + 2 * Real.log t) ^ (1 : ℕ))) x
      rw [show
          (fun t : ℝ ↦ t ^ (-p) * (b + 2 * Real.log t) ^ (1 : ℕ)) =
            (fun t : ℝ ↦ t ^ (-p) * (b + 2 * Real.log t))
          from funext (fun _ ↦ congrArg _ (pow_one _))]
      rw [quarter_logPower_deriv2_one hp]
      apply mul_nonneg (Real.rpow_nonneg hp.le _)
      apply nonneg_of_mul_nonneg_left _ hy
      norm_num only [quarterPsi08LogCurvature, Nat.cast_one, sub_self, mul_zero, add_zero] at h
      linarith only [h]
    · rw [quarter_logPower_deriv2 hp]
      exact
        mul_nonneg (mul_nonneg (Real.rpow_nonneg hp.le _) (pow_nonneg hy.le _))
          (by
            simpa only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, add_assoc,
              one_add_one_eq_two] using h)

/-- A rational Taylor certificate supplies the central logarithm threshold. -/
private theorem log_42_lower : (299 / 80 : ℝ) ≤ Real.log 42 := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound (N := 42) (j := 6) (n := 20) (lo := 299 / 80) (hi := 4)
        (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

/-- All shifted logarithmic monomials needed by the main comparison are convex
from radius 42 upward. -/
theorem quarter_psi08_main_convex {p : ℝ} (hp : 29 / 25 ≤ p) {k : ℕ} (hk : k ≤ 5) :
    ConvexOn ℝ (Set.Ici 42) (fun r : ℝ ↦ r ^ (-p) * (21 / 8 + 2 * Real.log r) ^ k) := by
  apply quarter_logPower_convex (by norm_num only) k
  · intro r hr
    have h := log_42_lower.trans (Real.log_le_log (by norm_num only) hr)
    linarith only [h]
  · intro r hr
    have h := log_42_lower.trans (Real.log_le_log (by norm_num only) hr)
    exact (quarter_psi08_main_curvature hp (by exact_mod_cast hk) (by linarith only [h])).le

/-- All unshifted logarithmic monomials needed by the Euler tail are convex
from radius 42 upward. -/
theorem quarter_psi08_tail_convex {p : ℝ} (hp : 29 / 25 ≤ p) {k : ℕ} (hk : k ≤ 2) :
    ConvexOn ℝ (Set.Ici 42) (fun r : ℝ ↦ r ^ (-p) * (2 * Real.log r) ^ k) := by
  have hlog (r : ℝ) (hr : r ∈ Set.Ici (42 : ℝ)) : (7 : ℝ) ≤ 2 * Real.log r := by
    have h := log_42_lower.trans (Real.log_le_log (by norm_num only) hr)
    linarith only [h]
  have h :=
    quarter_logPower_convex (a := 42) (p := p) (b := 0) (by norm_num only) k
      (fun r hr ↦ by linarith only [hlog r hr])
      (fun r hr ↦
        (quarter_psi08_tail_curvature hp (by exact_mod_cast hk)
            (by simpa only [zero_add] using hlog r hr)).le)
  simpa only [zero_add] using h

end PseudoPrime.PrimeTestBounds.MillerRabin
