/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.PSeriesComplex

/-! # Right half-plane bounds for the Riemann zeta function -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The tail of the real Dirichlet series of exponent `3/2`, starting at
three, is at most `2 / sqrt 2`. Compare the decreasing positive terms with
the integral over `[2, ∞)`. -/
theorem zeta_three_halves_tail :
    (∑' n : ℕ, (((n + 3 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)))) ≤ (Real.sqrt 2)⁻¹ * 2 := by
  have ha : AntitoneOn (fun x : ℝ ↦ x ^ (-(3 / 2 : ℝ))) (Set.Ici (2 : ℝ)) := by
    intro x hx y hy hxy
    change (2 : ℝ) ≤ x at hx
    exact Real.rpow_le_rpow_of_nonpos (by linarith only [hx]) hxy (by norm_num only)
  have hi :=
    integrableOn_Ioi_rpow_of_lt (a := (-(3 / 2 : ℝ))) (c := 2) (by norm_num only) (by norm_num only)
  have hn : ∀ x ∈ Set.Ioi (2 : ℝ), 0 ≤ x ^ (-(3 / 2 : ℝ)) := by
    intro x hx
    change (2 : ℝ) < x at hx
    exact Real.rpow_nonneg (by linarith only [hx]) _
  have ht := ha.tsum_comp_add_le_integral 2 hi hn
  norm_num only [Nat.cast_ofNat] at ht
  have heval :=
    integral_Ioi_rpow_of_lt (a := (-(3 / 2 : ℝ))) (c := 2) (by norm_num only) (by norm_num only)
  have hhalf : (-(3 / 2 : ℝ)) + 1 = -(1 / 2 : ℝ) := by norm_num only
  rw [hhalf, Real.rpow_neg (by norm_num only), ← Real.sqrt_eq_rpow] at heval
  have hi' : ∫ x in Set.Ioi (2 : ℝ), x ^ (-(3 / 2 : ℝ)) = (Real.sqrt 2)⁻¹ * 2 := by
    linarith only [heval]
  rw [hi'] at ht
  simpa only [Nat.add_assoc, show 2 + 1 = 3 by rfl] using ht

/-- The real Dirichlet series of exponent `3/2` is at most
`1 + (5/2) / sqrt 2`. Split off the first two terms and apply the integral
bound for the remaining tail. -/
theorem zeta_three_halves_series_le :
    (∑' n : ℕ, (((n + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)))) ≤ 1 + (5 / 2 : ℝ) * (Real.sqrt 2)⁻¹ := by
  have hs : Summable (fun n : ℕ ↦ (((n + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)))) :=
    (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by norm_num only))
  have hs' : Summable (fun n : ℕ ↦ (((n + 2 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)))) :=
    (summable_nat_add_iff 2).mpr (Real.summable_nat_rpow.mpr (by norm_num only))
  have hsplit := hs.tsum_eq_zero_add
  have hsplit' := hs'.tsum_eq_zero_add
  have heq2 : (2 : ℝ) ^ (-(3 / 2 : ℝ)) = (1 / 2 : ℝ) * (Real.sqrt 2)⁻¹ := by
    rw [show (-(3 / 2 : ℝ)) = -(1 + 1 / 2) by norm_num only, Real.rpow_neg (by norm_num only),
      Real.rpow_add (by norm_num only), Real.rpow_one, ← Real.sqrt_eq_rpow]
    ring
  have htail := zeta_three_halves_tail
  norm_num only [Nat.zero_add, Nat.cast_one, Real.one_rpow] at hsplit
  norm_num only [Nat.zero_add, Nat.cast_ofNat] at hsplit'
  have hchange :
    (∑' n : ℕ, (((n + 1 + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)))) =
      ∑' n : ℕ, (((n + 2 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) := by
    simp only [Nat.add_assoc, show 1 + 1 = 2 by rfl]
  have hchange' :
    (∑' n : ℕ, (((n + 1 + 2 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)))) =
      ∑' n : ℕ, (((n + 3 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) := by
    simp only [Nat.add_assoc, show 1 + 2 = 3 by rfl]
  rw [hchange] at hsplit
  rw [hchange'] at hsplit'
  rw [heq2] at hsplit'
  linarith only [hsplit, hsplit', htail]

/-- On the half-plane `Re s ≥ 3/2`, the norm of zeta is bounded by the real
Dirichlet series at `3/2`. Absolute convergence and monotonicity of real
powers give the termwise comparison. -/
theorem norm_zeta_le_three_halves_series {s : ℂ} (hs : (3 / 2 : ℝ) ≤ s.re) :
    ‖riemannZeta s‖ ≤ ∑' n : ℕ, (((n + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) := by
  have hs1 : 1 < s.re := by linarith only [hs]
  have hc : Summable (fun n : ℕ ↦ (1 : ℂ) / (n + 1 : ℂ) ^ s) := by
    have h := (summable_nat_add_iff 1).mpr (Complex.summable_one_div_nat_cpow.mpr hs1)
    simpa only [one_div, Nat.cast_add, Nat.cast_one] using h
  have hr : Summable (fun n : ℕ ↦ (((n + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)))) :=
    (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by norm_num only))
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs1]
  refine (norm_tsum_le_tsum_norm hc.norm).trans ?_
  apply hc.norm.tsum_le_tsum _ hr
  intro n
  have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.zero_lt_succ n
  have hb : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have heq : (n + 1 : ℂ) = ((((n + 1 : ℕ) : ℝ)) : ℂ) := by
    simp only [Nat.cast_add, Nat.cast_one, Complex.ofReal_add, Complex.ofReal_natCast,
      Complex.ofReal_one]
  rw [norm_div, norm_one, heq, Complex.norm_cpow_eq_rpow_re_of_pos hn, one_div, ←
    Real.rpow_neg hn.le s.re]
  apply Real.rpow_le_rpow_of_exponent_le hb
  linarith only [hs]

/-- For every complex `s` with `Re s ≥ 3/2`, the norm of the Riemann zeta
function is strictly less than `14/5`. The real Dirichlet-series estimate
and the rational inequality `25/18 < sqrt 2` give this uniform bound. -/
theorem norm_zeta_lt_fourteen_fifths {s : ℂ} (hs : (3 / 2 : ℝ) ≤ s.re) :
    ‖riemannZeta s‖ < (14 / 5 : ℝ) := by
  have hs0 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num only)
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num only)
  have hlow : (25 / 18 : ℝ) < Real.sqrt 2 := by nlinarith only [hs0, hs2]
  have hinv := one_div_lt_one_div_of_lt (by norm_num only : (0 : ℝ) < 25 / 18) hlow
  norm_num only [one_div] at hinv
  have hscalar : 1 + (5 / 2 : ℝ) * (Real.sqrt 2)⁻¹ < 14 / 5 := by linarith only [hinv]
  exact ((norm_zeta_le_three_halves_series hs).trans zeta_three_halves_series_le).trans_lt hscalar

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
