/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevLcmBounds
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevIntervalPrefix
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrtChecker

/-! # Square-root psi error near 1423 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
-- The kernel checks both bounds for this finite LCM.
private theorem psi_1423_bounds :
    (1399464 : ℝ) / 1000 ≤ Chebyshev.psi 1423 ∧ Chebyshev.psi 1423 ≤ (1400158 : ℝ) / 1000 := by
  have hl : 2 ^ 2019 ≤ Nat.lcmUpto 1423 := by decide +kernel
  have hu : Nat.lcmUpto 1423 ≤ 2 ^ (2019 + 1) := by decide +kernel
  have h := psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor
  · linarith only [h.1, Real.log_two_gt_d9]
  · linarith only [h.2, Real.log_two_lt_d9]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
-- The kernel checks both bounds for this finite LCM.
private theorem psi_1428_bounds :
    (1407088 : ℝ) / 1000 ≤ Chebyshev.psi 1428 ∧ Chebyshev.psi 1428 ≤ (1407782 : ℝ) / 1000 := by
  have hl : 2 ^ 2030 ≤ Nat.lcmUpto 1428 := by decide +kernel
  have hu : Nat.lcmUpto 1428 ≤ 2 ^ (2030 + 1) := by decide +kernel
  have h := psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor
  · linarith only [h.1, Real.log_two_gt_d9]
  · linarith only [h.2, Real.log_two_lt_d9]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
-- The kernel checks both bounds for this finite LCM.
private theorem psi_1429_bounds :
    (1414020 : ℝ) / 1000 ≤ Chebyshev.psi 1429 ∧ Chebyshev.psi 1429 ≤ (1414714 : ℝ) / 1000 := by
  have hl : 2 ^ 2040 ≤ Nat.lcmUpto 1429 := by decide +kernel
  have hu : Nat.lcmUpto 1429 ≤ 2 ^ (2040 + 1) := by decide +kernel
  have h := psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor
  · linarith only [h.1, Real.log_two_gt_d9]
  · linarith only [h.2, Real.log_two_lt_d9]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
-- The kernel checks both bounds for this finite LCM.
private theorem psi_1443_bounds :
    (1428576 : ℝ) / 1000 ≤ Chebyshev.psi 1443 ∧ Chebyshev.psi 1443 ≤ (1429270 : ℝ) / 1000 := by
  have hl : 2 ^ 2061 ≤ Nat.lcmUpto 1443 := by decide +kernel
  have hu : Nat.lcmUpto 1443 ≤ 2 ^ (2061 + 1) := by decide +kernel
  have h := psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor
  · linarith only [h.1, Real.log_two_gt_d9]
  · linarith only [h.2, Real.log_two_lt_d9]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
-- The kernel checks both bounds for this finite LCM.
private theorem psi_1444_bounds :
    (1428576 : ℝ) / 1000 ≤ Chebyshev.psi 1444 ∧ Chebyshev.psi 1444 ≤ (1429270 : ℝ) / 1000 := by
  have hl : 2 ^ 2061 ≤ Nat.lcmUpto 1444 := by decide +kernel
  have hu : Nat.lcmUpto 1444 ≤ 2 ^ (2061 + 1) := by decide +kernel
  have h := psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor
  · linarith only [h.1, Real.log_two_gt_d9]
  · linarith only [h.2, Real.log_two_lt_d9]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
-- The kernel checks both bounds for this finite LCM.
private theorem psi_1458_bounds :
    (1450757 : ℝ) / 1000 ≤ Chebyshev.psi 1458 ∧ Chebyshev.psi 1458 ≤ (1451451 : ℝ) / 1000 := by
  have hl : 2 ^ 2093 ≤ Nat.lcmUpto 1458 := by decide +kernel
  have hu : Nat.lcmUpto 1458 ≤ 2 ^ (2093 + 1) := by decide +kernel
  have h := psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor
  · linarith only [h.1, Real.log_two_gt_d9]
  · linarith only [h.2, Real.log_two_lt_d9]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
-- The kernel checks both bounds for this finite LCM.
private theorem psi_1459_bounds :
    (1457688 : ℝ) / 1000 ≤ Chebyshev.psi 1459 ∧ Chebyshev.psi 1459 ≤ (1458382 : ℝ) / 1000 := by
  have hl : 2 ^ 2103 ≤ Nat.lcmUpto 1459 := by decide +kernel
  have hu : Nat.lcmUpto 1459 ≤ 2 ^ (2103 + 1) := by decide +kernel
  have h := psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor
  · linarith only [h.1, Real.log_two_gt_d9]
  · linarith only [h.2, Real.log_two_lt_d9]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
-- The kernel checks both bounds for this finite LCM.
private theorem psi_1487_bounds :
    (1486800 : ℝ) / 1000 ≤ Chebyshev.psi 1487 ∧ Chebyshev.psi 1487 ≤ (1487494 : ℝ) / 1000 := by
  have hl : 2 ^ 2145 ≤ Nat.lcmUpto 1487 := by decide +kernel
  have hu : Nat.lcmUpto 1487 ≤ 2 ^ (2145 + 1) := by decide +kernel
  have h := psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor
  · linarith only [h.1, Real.log_two_gt_d9]
  · linarith only [h.2, Real.log_two_lt_d9]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
-- The kernel checks both bounds for this finite LCM.
private theorem psi_1488_bounds :
    (1486800 : ℝ) / 1000 ≤ Chebyshev.psi 1488 ∧ Chebyshev.psi 1488 ≤ (1487494 : ℝ) / 1000 := by
  have hl : 2 ^ 2145 ≤ Nat.lcmUpto 1488 := by decide +kernel
  have hu : Nat.lcmUpto 1488 ≤ 2 ^ (2145 + 1) := by decide +kernel
  have h := psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor
  · linarith only [h.1, Real.log_two_gt_d9]
  · linarith only [h.2, Real.log_two_lt_d9]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
-- The kernel checks both bounds for this finite LCM.
private theorem psi_1509_bounds :
    (1508981 : ℝ) / 1000 ≤ Chebyshev.psi 1509 ∧ Chebyshev.psi 1509 ≤ (1509675 : ℝ) / 1000 := by
  have hl : 2 ^ 2177 ≤ Nat.lcmUpto 1509 := by decide +kernel
  have hu : Nat.lcmUpto 1509 ≤ 2 ^ (2177 + 1) := by decide +kernel
  have h := psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor
  · linarith only [h.1, Real.log_two_gt_d9]
  · linarith only [h.2, Real.log_two_lt_d9]

/-- Internal cell candidates; soundness checks both their arithmetic and psi endpoints. -/
private def cells : List PsiSqrtCell :=
  [⟨1423, 1429, 1399464, 1407782, 30178, 30241⟩, ⟨1429, 1444, 1414020, 1429270, 30241, 30400⟩,
    ⟨1444, 1459, 1428576, 1451451, 30400, 30557⟩, ⟨1459, 1488, 1457688, 1487494, 30557, 30859⟩,
    ⟨1488, 1510, 1486800, 1509675, 30859, 31086⟩]

/-- The kernel checks all adjacent cells and their integer guards. -/
private theorem cells_checked : psiSqrtChainCheck 1423 1510 cells = true := by decide +kernel

/-- Every candidate has its lower psi endpoint certified. -/
private theorem cells_lower : ∀ r ∈ cells, (r.lo : ℝ) / 1000 ≤ Chebyshev.psi r.a := by
  intro r hr
  simp only [cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact psi_1423_bounds.1
  · exact psi_1429_bounds.1
  · exact psi_1444_bounds.1
  · exact psi_1459_bounds.1
  · exact psi_1488_bounds.1

/-- Every candidate has its upper psi endpoint certified. -/
private theorem cells_upper : ∀ r ∈ cells, Chebyshev.psi (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact psi_1428_bounds.2
  · exact psi_1443_bounds.2
  · exact psi_1458_bounds.2
  · exact psi_1487_bounds.2
  · exact psi_1509_bounds.2

/-- The psi value at 1510 has the displayed rational bounds. The previously
certified endpoint at 1509 has the same psi value because 1510 is not a prime
power; this seed can be reused by subsequent interval increments. -/
theorem psi_1510_bounds :
    (1508981 : ℝ) / 1000 ≤ Chebyshev.psi ((1510 : ℕ) : ℝ) ∧
      Chebyshev.psi ((1510 : ℕ) : ℝ) ≤ (1509675 : ℝ) / 1000 := by
  rw [psi_eq_of_no_prime_power (a := 1509) (b := 1510) (by decide) (by decide +kernel)]
  exact psi_1509_bounds

/-- The unconditional psi error is at most four fifths of the square root on
`[1423, 1510)`. Kernel-checked endpoints and adjacent arithmetic guards provide
the real interval result without indexing the candidate list. -/
theorem psi_four_fifths_1423_1510 {x : ℝ} (ha : 1423 ≤ x) (hb : x < 1510) :
    |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x := by
  exact psi_sqrt_chain_sound cells_checked cells_lower cells_upper ha hb

end PseudoPrime.AnalyticNumberTheory.Arithmetic
