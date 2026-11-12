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
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSmallDefect32768
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalEnvelope16384
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalMonotone
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalChecker

/-! # Batch certificate for Lee–Nosal theta cells -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The local cells store endpoint bounds in thousandths. -/
def theta31785Cells : List LeeNosalCell :=
  [⟨31785, 31878, 31513909, 31812684, 365000, 365000⟩,
    ⟨31878, 31951, 31586689, 31843875, 365000, 365000⟩,
    ⟨31951, 31982, 31617881, 31884771, 365000, 365000⟩,
    ⟨31982, 32023, 31658777, 31915962, 365000, 365000⟩,
    ⟨32023, 32054, 31689968, 31952699, 365000, 365000⟩,
    ⟨32054, 32091, 31726705, 32024787, 365000, 365000⟩,
    ⟨32091, 32163, 31798792, 32087170, 365000, 365000⟩,
    ⟨32163, 32226, 31861176, 32149553, 365000, 365000⟩,
    ⟨32226, 32288, 31923559, 32201539, 365000, 365000⟩,
    ⟨32288, 32340, 31975545, 32274320, 365000, 365000⟩,
    ⟨32340, 32413, 32048325, 32378292, 365000, 365000⟩,
    ⟨32413, 32527, 32162695, 32492661, 365000, 365000⟩]

/-- The kernel-checked prefix bounds for 31771. -/
theorem theta31785_psi_31771_bounds :
    (31739209 : ℝ) / 1000 ≤ Chebyshev.psi 31771 ∧ Chebyshev.psi 31771 ≤ (31739903 : ℝ) / 1000 := by
  have hl : 2 ^ 45790 ≤ Nat.lcmUpto 31771 := by decide +kernel
  have hu : Nat.lcmUpto 31771 ≤ 2 ^ (45790 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 31873. -/
theorem theta31785_psi_31873_bounds :
    (31811989 : ℝ) / 1000 ≤ Chebyshev.psi 31873 ∧ Chebyshev.psi 31873 ≤ (31812684 : ℝ) / 1000 := by
  have hl : 2 ^ 45895 ≤ Nat.lcmUpto 31873 := by decide +kernel
  have hu : Nat.lcmUpto 31873 ≤ 2 ^ (45895 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 31907. -/
theorem theta31785_psi_31907_bounds :
    (31843181 : ℝ) / 1000 ≤ Chebyshev.psi 31907 ∧ Chebyshev.psi 31907 ≤ (31843875 : ℝ) / 1000 := by
  have hl : 2 ^ 45940 ≤ Nat.lcmUpto 31907 := by decide +kernel
  have hu : Nat.lcmUpto 31907 ≤ 2 ^ (45940 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 31981. -/
theorem theta31785_psi_31981_bounds :
    (31884077 : ℝ) / 1000 ≤ Chebyshev.psi 31981 ∧ Chebyshev.psi 31981 ≤ (31884771 : ℝ) / 1000 := by
  have hl : 2 ^ 45999 ≤ Nat.lcmUpto 31981 := by decide +kernel
  have hu : Nat.lcmUpto 31981 ≤ 2 ^ (45999 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 32009. -/
theorem theta31785_psi_32009_bounds :
    (31915268 : ℝ) / 1000 ≤ Chebyshev.psi 32009 ∧ Chebyshev.psi 32009 ≤ (31915962 : ℝ) / 1000 := by
  have hl : 2 ^ 46044 ≤ Nat.lcmUpto 32009 := by decide +kernel
  have hu : Nat.lcmUpto 32009 ≤ 2 ^ (46044 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 32051. -/
theorem theta31785_psi_32051_bounds :
    (31952005 : ℝ) / 1000 ≤ Chebyshev.psi 32051 ∧ Chebyshev.psi 32051 ≤ (31952699 : ℝ) / 1000 := by
  have hl : 2 ^ 46097 ≤ Nat.lcmUpto 32051 := by decide +kernel
  have hu : Nat.lcmUpto 32051 ≤ 2 ^ (46097 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 32089. -/
theorem theta31785_psi_32089_bounds :
    (32024092 : ℝ) / 1000 ≤ Chebyshev.psi 32089 ∧ Chebyshev.psi 32089 ≤ (32024787 : ℝ) / 1000 := by
  have hl : 2 ^ 46201 ≤ Nat.lcmUpto 32089 := by decide +kernel
  have hu : Nat.lcmUpto 32089 ≤ 2 ^ (46201 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 32159. -/
theorem theta31785_psi_32159_bounds :
    (32086476 : ℝ) / 1000 ≤ Chebyshev.psi 32159 ∧ Chebyshev.psi 32159 ≤ (32087170 : ℝ) / 1000 := by
  have hl : 2 ^ 46291 ≤ Nat.lcmUpto 32159 := by decide +kernel
  have hu : Nat.lcmUpto 32159 ≤ 2 ^ (46291 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 32213. -/
theorem theta31785_psi_32213_bounds :
    (32148859 : ℝ) / 1000 ≤ Chebyshev.psi 32213 ∧ Chebyshev.psi 32213 ≤ (32149553 : ℝ) / 1000 := by
  have hl : 2 ^ 46381 ≤ Nat.lcmUpto 32213 := by decide +kernel
  have hu : Nat.lcmUpto 32213 ≤ 2 ^ (46381 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 32261. -/
theorem theta31785_psi_32261_bounds :
    (32200845 : ℝ) / 1000 ≤ Chebyshev.psi 32261 ∧ Chebyshev.psi 32261 ≤ (32201539 : ℝ) / 1000 := by
  have hl : 2 ^ 46456 ≤ Nat.lcmUpto 32261 := by decide +kernel
  have hu : Nat.lcmUpto 32261 ≤ 2 ^ (46456 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 32327. -/
theorem theta31785_psi_32327_bounds :
    (32273625 : ℝ) / 1000 ≤ Chebyshev.psi 32327 ∧ Chebyshev.psi 32327 ≤ (32274320 : ℝ) / 1000 := by
  have hl : 2 ^ 46561 ≤ Nat.lcmUpto 32327 := by decide +kernel
  have hu : Nat.lcmUpto 32327 ≤ 2 ^ (46561 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 32411. -/
theorem theta31785_psi_32411_bounds :
    (32377597 : ℝ) / 1000 ≤ Chebyshev.psi 32411 ∧ Chebyshev.psi 32411 ≤ (32378292 : ℝ) / 1000 := by
  have hl : 2 ^ 46711 ≤ Nat.lcmUpto 32411 := by decide +kernel
  have hu : Nat.lcmUpto 32411 ≤ 2 ^ (46711 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 32413. -/
theorem theta31785_psi_32413_bounds :
    (32387995 : ℝ) / 1000 ≤ Chebyshev.psi 32413 ∧ Chebyshev.psi 32413 ≤ (32388689 : ℝ) / 1000 := by
  have hl : 2 ^ 46726 ≤ Nat.lcmUpto 32413 := by decide +kernel
  have hu : Nat.lcmUpto 32413 ≤ 2 ^ (46726 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 32507. -/
theorem theta31785_psi_32507_bounds :
    (32491967 : ℝ) / 1000 ≤ Chebyshev.psi 32507 ∧ Chebyshev.psi 32507 ≤ (32492661 : ℝ) / 1000 := by
  have hl : 2 ^ 46876 ≤ Nat.lcmUpto 32507 := by decide +kernel
  have hu : Nat.lcmUpto 32507 ≤ 2 ^ (46876 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- Every batch cell has a checked theta lower bound. -/
theorem theta31785_lower : ∀ r ∈ theta31785Cells, (r.lo : ℝ) / 1000 ≤ Chebyshev.theta r.a := by
  intro r hr
  simp only [theta31785Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (31513909 : ℝ) / 1000 ≤ Chebyshev.theta (↑(31785 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 31785) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 31771) (b := 31785) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta31785_psi_31771_bounds.1]
  · change (31586689 : ℝ) / 1000 ≤ Chebyshev.theta (↑(31878 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 31878) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 31873) (b := 31878) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta31785_psi_31873_bounds.1]
  · change (31617881 : ℝ) / 1000 ≤ Chebyshev.theta (↑(31951 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 31951) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 31907) (b := 31951) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta31785_psi_31907_bounds.1]
  · change (31658777 : ℝ) / 1000 ≤ Chebyshev.theta (↑(31982 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 31982) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 31981) (b := 31982) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta31785_psi_31981_bounds.1]
  · change (31689968 : ℝ) / 1000 ≤ Chebyshev.theta (↑(32023 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 32023) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 32009) (b := 32023) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta31785_psi_32009_bounds.1]
  · change (31726705 : ℝ) / 1000 ≤ Chebyshev.theta (↑(32054 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 32054) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 32051) (b := 32054) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta31785_psi_32051_bounds.1]
  · change (31798792 : ℝ) / 1000 ≤ Chebyshev.theta (↑(32091 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 32091) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 32089) (b := 32091) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta31785_psi_32089_bounds.1]
  · change (31861176 : ℝ) / 1000 ≤ Chebyshev.theta (↑(32163 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 32163) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 32159) (b := 32163) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta31785_psi_32159_bounds.1]
  · change (31923559 : ℝ) / 1000 ≤ Chebyshev.theta (↑(32226 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 32226) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 32213) (b := 32226) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta31785_psi_32213_bounds.1]
  · change (31975545 : ℝ) / 1000 ≤ Chebyshev.theta (↑(32288 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 32288) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 32261) (b := 32288) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta31785_psi_32261_bounds.1]
  · change (32048325 : ℝ) / 1000 ≤ Chebyshev.theta (↑(32340 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 32340) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 32327) (b := 32340) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta31785_psi_32327_bounds.1]
  · change (32162695 : ℝ) / 1000 ≤ Chebyshev.theta (↑(32413 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 32413) (by norm_num only) (by norm_num only)
    linarith only [hd, theta31785_psi_32413_bounds.1]

/-- Every batch cell has a checked theta upper bound. -/
theorem theta31785_upper :
    ∀ r ∈ theta31785Cells, Chebyshev.theta (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [theta31785Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Chebyshev.theta (↑(31877 : ℕ) : ℝ) ≤ (31812684 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 31877
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 31873) (b := 31877) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta31785_psi_31873_bounds.2]
  · change Chebyshev.theta (↑(31950 : ℕ) : ℝ) ≤ (31843875 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 31950
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 31907) (b := 31950) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta31785_psi_31907_bounds.2]
  · change Chebyshev.theta (↑(31981 : ℕ) : ℝ) ≤ (31884771 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 31981
    linarith only [hd, theta31785_psi_31981_bounds.2]
  · change Chebyshev.theta (↑(32022 : ℕ) : ℝ) ≤ (31915962 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 32022
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 32009) (b := 32022) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta31785_psi_32009_bounds.2]
  · change Chebyshev.theta (↑(32053 : ℕ) : ℝ) ≤ (31952699 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 32053
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 32051) (b := 32053) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta31785_psi_32051_bounds.2]
  · change Chebyshev.theta (↑(32090 : ℕ) : ℝ) ≤ (32024787 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 32090
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 32089) (b := 32090) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta31785_psi_32089_bounds.2]
  · change Chebyshev.theta (↑(32162 : ℕ) : ℝ) ≤ (32087170 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 32162
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 32159) (b := 32162) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta31785_psi_32159_bounds.2]
  · change Chebyshev.theta (↑(32225 : ℕ) : ℝ) ≤ (32149553 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 32225
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 32213) (b := 32225) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta31785_psi_32213_bounds.2]
  · change Chebyshev.theta (↑(32287 : ℕ) : ℝ) ≤ (32201539 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 32287
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 32261) (b := 32287) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta31785_psi_32261_bounds.2]
  · change Chebyshev.theta (↑(32339 : ℕ) : ℝ) ≤ (32274320 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 32339
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 32327) (b := 32339) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta31785_psi_32327_bounds.2]
  · change Chebyshev.theta (↑(32412 : ℕ) : ℝ) ≤ (32378292 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 32412
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 32411) (b := 32412) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta31785_psi_32411_bounds.2]
  · change Chebyshev.theta (↑(32526 : ℕ) : ℝ) ≤ (32492661 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 32526
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 32507) (b := 32526) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta31785_psi_32507_bounds.2]

/-- The envelope bound applies at every cell a endpoint. -/
theorem theta31785_a :
    ∀ r ∈ theta31785Cells,
      (r.ca : ℝ) / 1000 ≤
        Real.sqrt r.a *
          (Real.log r.a * (Real.log r.a - Real.log (Real.log r.a)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta31785Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 31785 *
          (Real.log 31785 * (Real.log 31785 - Real.log (Real.log 31785)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 31878 *
          (Real.log 31878 * (Real.log 31878 - Real.log (Real.log 31878)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 31951 *
          (Real.log 31951 * (Real.log 31951 - Real.log (Real.log 31951)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 31982 *
          (Real.log 31982 * (Real.log 31982 - Real.log (Real.log 31982)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 32023 *
          (Real.log 32023 * (Real.log 32023 - Real.log (Real.log 32023)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 32054 *
          (Real.log 32054 * (Real.log 32054 - Real.log (Real.log 32054)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 32091 *
          (Real.log 32091 * (Real.log 32091 - Real.log (Real.log 32091)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 32163 *
          (Real.log 32163 * (Real.log 32163 - Real.log (Real.log 32163)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 32226 *
          (Real.log 32226 * (Real.log 32226 - Real.log (Real.log 32226)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 32288 *
          (Real.log 32288 * (Real.log 32288 - Real.log (Real.log 32288)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 32340 *
          (Real.log 32340 * (Real.log 32340 - Real.log (Real.log 32340)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 32413 *
          (Real.log 32413 * (Real.log 32413 - Real.log (Real.log 32413)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)

/-- The envelope bound applies at every cell b endpoint. -/
theorem theta31785_b :
    ∀ r ∈ theta31785Cells,
      (r.cb : ℝ) / 1000 ≤
        Real.sqrt r.b *
          (Real.log r.b * (Real.log r.b - Real.log (Real.log r.b)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta31785Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 31878 *
          (Real.log 31878 * (Real.log 31878 - Real.log (Real.log 31878)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 31951 *
          (Real.log 31951 * (Real.log 31951 - Real.log (Real.log 31951)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 31982 *
          (Real.log 31982 * (Real.log 31982 - Real.log (Real.log 31982)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 32023 *
          (Real.log 32023 * (Real.log 32023 - Real.log (Real.log 32023)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 32054 *
          (Real.log 32054 * (Real.log 32054 - Real.log (Real.log 32054)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 32091 *
          (Real.log 32091 * (Real.log 32091 - Real.log (Real.log 32091)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 32163 *
          (Real.log 32163 * (Real.log 32163 - Real.log (Real.log 32163)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 32226 *
          (Real.log 32226 * (Real.log 32226 - Real.log (Real.log 32226)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 32288 *
          (Real.log 32288 * (Real.log 32288 - Real.log (Real.log 32288)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 32340 *
          (Real.log 32340 * (Real.log 32340 - Real.log (Real.log 32340)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 32413 *
          (Real.log 32413 * (Real.log 32413 - Real.log (Real.log 32413)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 32527 *
          (Real.log 32527 * (Real.log 32527 - Real.log (Real.log 32527)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)

/-- The cells form a checked chain covering `[31785, 32527)`. -/
theorem theta31785_check : leeNosalChainCheck 31785 32527 theta31785Cells = true := by
  decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
