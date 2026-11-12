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
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSmallDefect16384
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalEnvelope10000
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalMonotone
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalChecker

/-! # Batch certificate for Lee–Nosal theta cells -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The local cells store endpoint bounds in thousandths. -/
def theta12995Cells : List LeeNosalCell :=
  [⟨12995, 13109, 12854392, 13126822, 255000, 255000⟩,
    ⟨13109, 13232, 12977079, 13259213, 255000, 255000⟩,
    ⟨13232, 13355, 13100459, 13373582, 255000, 255000⟩,
    ⟨13355, 13469, 13214828, 13478247, 255000, 255000⟩,
    ⟨13469, 13583, 13328504, 13573209, 255000, 255000⟩,
    ⟨13583, 13669, 13414454, 13639751, 255000, 255000⟩,
    ⟨13669, 13745, 13490701, 13754120, 255000, 255000⟩,
    ⟨13745, 13850, 13595366, 13858785, 255000, 255000⟩,
    ⟨13850, 13955, 13700031, 13973155, 255000, 255000⟩,
    ⟨13955, 14069, 13814400, 14068809, 255000, 255000⟩,
    ⟨14069, 14165, 13910055, 14154759, 255000, 255000⟩,
    ⟨14165, 14251, 13996005, 14221994, 255000, 255000⟩]

/-- The kernel-checked prefix bounds for 12983. -/
theorem theta12995_psi_12983_bounds :
    (13012452 : ℝ) / 1000 ≤ Chebyshev.psi 12983 ∧ Chebyshev.psi 12983 ≤ (13013146 : ℝ) / 1000 := by
  have hl : 2 ^ 18773 ≤ Nat.lcmUpto 12983 := by decide +kernel
  have hu : Nat.lcmUpto 12983 ≤ 2 ^ (18773 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 13103. -/
theorem theta12995_psi_13103_bounds :
    (13126128 : ℝ) / 1000 ≤ Chebyshev.psi 13103 ∧ Chebyshev.psi 13103 ≤ (13126822 : ℝ) / 1000 := by
  have hl : 2 ^ 18937 ≤ Nat.lcmUpto 13103 := by decide +kernel
  have hu : Nat.lcmUpto 13103 ≤ 2 ^ (18937 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 13109. -/
theorem theta12995_psi_13109_bounds :
    (13135139 : ℝ) / 1000 ≤ Chebyshev.psi 13109 ∧ Chebyshev.psi 13109 ≤ (13135833 : ℝ) / 1000 := by
  have hl : 2 ^ 18950 ≤ Nat.lcmUpto 13109 := by decide +kernel
  have hu : Nat.lcmUpto 13109 ≤ 2 ^ (18950 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 13229. -/
theorem theta12995_psi_13229_bounds :
    (13258519 : ℝ) / 1000 ≤ Chebyshev.psi 13229 ∧ Chebyshev.psi 13229 ≤ (13259213 : ℝ) / 1000 := by
  have hl : 2 ^ 19128 ≤ Nat.lcmUpto 13229 := by decide +kernel
  have hu : Nat.lcmUpto 13229 ≤ 2 ^ (19128 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 13339. -/
theorem theta12995_psi_13339_bounds :
    (13372888 : ℝ) / 1000 ≤ Chebyshev.psi 13339 ∧ Chebyshev.psi 13339 ≤ (13373582 : ℝ) / 1000 := by
  have hl : 2 ^ 19293 ≤ Nat.lcmUpto 13339 := by decide +kernel
  have hu : Nat.lcmUpto 13339 ≤ 2 ^ (19293 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 13463. -/
theorem theta12995_psi_13463_bounds :
    (13477553 : ℝ) / 1000 ≤ Chebyshev.psi 13463 ∧ Chebyshev.psi 13463 ≤ (13478247 : ℝ) / 1000 := by
  have hl : 2 ^ 19444 ≤ Nat.lcmUpto 13463 := by decide +kernel
  have hu : Nat.lcmUpto 13463 ≤ 2 ^ (19444 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 13469. -/
theorem theta12995_psi_13469_bounds :
    (13486564 : ℝ) / 1000 ≤ Chebyshev.psi 13469 ∧ Chebyshev.psi 13469 ≤ (13487258 : ℝ) / 1000 := by
  have hl : 2 ^ 19457 ≤ Nat.lcmUpto 13469 := by decide +kernel
  have hu : Nat.lcmUpto 13469 ≤ 2 ^ (19457 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 13577. -/
theorem theta12995_psi_13577_bounds :
    (13572514 : ℝ) / 1000 ≤ Chebyshev.psi 13577 ∧ Chebyshev.psi 13577 ≤ (13573209 : ℝ) / 1000 := by
  have hl : 2 ^ 19581 ≤ Nat.lcmUpto 13577 := by decide +kernel
  have hu : Nat.lcmUpto 13577 ≤ 2 ^ (19581 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 13649. -/
theorem theta12995_psi_13649_bounds :
    (13639057 : ℝ) / 1000 ≤ Chebyshev.psi 13649 ∧ Chebyshev.psi 13649 ≤ (13639751 : ℝ) / 1000 := by
  have hl : 2 ^ 19677 ≤ Nat.lcmUpto 13649 := by decide +kernel
  have hu : Nat.lcmUpto 13649 ≤ 2 ^ (19677 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 13669. -/
theorem theta12995_psi_13669_bounds :
    (13648761 : ℝ) / 1000 ≤ Chebyshev.psi 13669 ∧ Chebyshev.psi 13669 ≤ (13649455 : ℝ) / 1000 := by
  have hl : 2 ^ 19691 ≤ Nat.lcmUpto 13669 := by decide +kernel
  have hu : Nat.lcmUpto 13669 ≤ 2 ^ (19691 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 13729. -/
theorem theta12995_psi_13729_bounds :
    (13753426 : ℝ) / 1000 ≤ Chebyshev.psi 13729 ∧ Chebyshev.psi 13729 ≤ (13754120 : ℝ) / 1000 := by
  have hl : 2 ^ 19842 ≤ Nat.lcmUpto 13729 := by decide +kernel
  have hu : Nat.lcmUpto 13729 ≤ 2 ^ (19842 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 13841. -/
theorem theta12995_psi_13841_bounds :
    (13858091 : ℝ) / 1000 ≤ Chebyshev.psi 13841 ∧ Chebyshev.psi 13841 ≤ (13858785 : ℝ) / 1000 := by
  have hl : 2 ^ 19993 ≤ Nat.lcmUpto 13841 := by decide +kernel
  have hu : Nat.lcmUpto 13841 ≤ 2 ^ (19993 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 13933. -/
theorem theta12995_psi_13933_bounds :
    (13972460 : ℝ) / 1000 ≤ Chebyshev.psi 13933 ∧ Chebyshev.psi 13933 ≤ (13973155 : ℝ) / 1000 := by
  have hl : 2 ^ 20158 ≤ Nat.lcmUpto 13933 := by decide +kernel
  have hu : Nat.lcmUpto 13933 ≤ 2 ^ (20158 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 14057. -/
theorem theta12995_psi_14057_bounds :
    (14068115 : ℝ) / 1000 ≤ Chebyshev.psi 14057 ∧ Chebyshev.psi 14057 ≤ (14068809 : ℝ) / 1000 := by
  have hl : 2 ^ 20296 ≤ Nat.lcmUpto 14057 := by decide +kernel
  have hu : Nat.lcmUpto 14057 ≤ 2 ^ (20296 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 14159. -/
theorem theta12995_psi_14159_bounds :
    (14154065 : ℝ) / 1000 ≤ Chebyshev.psi 14159 ∧ Chebyshev.psi 14159 ≤ (14154759 : ℝ) / 1000 := by
  have hl : 2 ^ 20420 ≤ Nat.lcmUpto 14159 := by decide +kernel
  have hu : Nat.lcmUpto 14159 ≤ 2 ^ (20420 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 14249. -/
theorem theta12995_psi_14249_bounds :
    (14221300 : ℝ) / 1000 ≤ Chebyshev.psi 14249 ∧ Chebyshev.psi 14249 ≤ (14221994 : ℝ) / 1000 := by
  have hl : 2 ^ 20517 ≤ Nat.lcmUpto 14249 := by decide +kernel
  have hu : Nat.lcmUpto 14249 ≤ 2 ^ (20517 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- Every batch cell has a checked theta lower bound. -/
theorem theta12995_lower : ∀ r ∈ theta12995Cells, (r.lo : ℝ) / 1000 ≤ Chebyshev.theta r.a := by
  intro r hr
  simp only [theta12995Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (12854392 : ℝ) / 1000 ≤ Chebyshev.theta (↑(12995 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 12995) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 12983) (b := 12995) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta12995_psi_12983_bounds.1]
  · change (12977079 : ℝ) / 1000 ≤ Chebyshev.theta (↑(13109 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 13109) (by norm_num only) (by norm_num only)
    linarith only [hd, theta12995_psi_13109_bounds.1]
  · change (13100459 : ℝ) / 1000 ≤ Chebyshev.theta (↑(13232 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 13232) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 13229) (b := 13232) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta12995_psi_13229_bounds.1]
  · change (13214828 : ℝ) / 1000 ≤ Chebyshev.theta (↑(13355 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 13355) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 13339) (b := 13355) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta12995_psi_13339_bounds.1]
  · change (13328504 : ℝ) / 1000 ≤ Chebyshev.theta (↑(13469 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 13469) (by norm_num only) (by norm_num only)
    linarith only [hd, theta12995_psi_13469_bounds.1]
  · change (13414454 : ℝ) / 1000 ≤ Chebyshev.theta (↑(13583 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 13583) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 13577) (b := 13583) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta12995_psi_13577_bounds.1]
  · change (13490701 : ℝ) / 1000 ≤ Chebyshev.theta (↑(13669 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 13669) (by norm_num only) (by norm_num only)
    linarith only [hd, theta12995_psi_13669_bounds.1]
  · change (13595366 : ℝ) / 1000 ≤ Chebyshev.theta (↑(13745 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 13745) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 13729) (b := 13745) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta12995_psi_13729_bounds.1]
  · change (13700031 : ℝ) / 1000 ≤ Chebyshev.theta (↑(13850 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 13850) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 13841) (b := 13850) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta12995_psi_13841_bounds.1]
  · change (13814400 : ℝ) / 1000 ≤ Chebyshev.theta (↑(13955 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 13955) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 13933) (b := 13955) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta12995_psi_13933_bounds.1]
  · change (13910055 : ℝ) / 1000 ≤ Chebyshev.theta (↑(14069 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 14069) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 14057) (b := 14069) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta12995_psi_14057_bounds.1]
  · change (13996005 : ℝ) / 1000 ≤ Chebyshev.theta (↑(14165 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 14165) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 14159) (b := 14165) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta12995_psi_14159_bounds.1]

/-- Every batch cell has a checked theta upper bound. -/
theorem theta12995_upper :
    ∀ r ∈ theta12995Cells, Chebyshev.theta (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [theta12995Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Chebyshev.theta (↑(13108 : ℕ) : ℝ) ≤ (13126822 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 13108
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 13103) (b := 13108) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta12995_psi_13103_bounds.2]
  · change Chebyshev.theta (↑(13231 : ℕ) : ℝ) ≤ (13259213 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 13231
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 13229) (b := 13231) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta12995_psi_13229_bounds.2]
  · change Chebyshev.theta (↑(13354 : ℕ) : ℝ) ≤ (13373582 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 13354
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 13339) (b := 13354) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta12995_psi_13339_bounds.2]
  · change Chebyshev.theta (↑(13468 : ℕ) : ℝ) ≤ (13478247 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 13468
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 13463) (b := 13468) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta12995_psi_13463_bounds.2]
  · change Chebyshev.theta (↑(13582 : ℕ) : ℝ) ≤ (13573209 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 13582
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 13577) (b := 13582) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta12995_psi_13577_bounds.2]
  · change Chebyshev.theta (↑(13668 : ℕ) : ℝ) ≤ (13639751 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 13668
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 13649) (b := 13668) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta12995_psi_13649_bounds.2]
  · change Chebyshev.theta (↑(13744 : ℕ) : ℝ) ≤ (13754120 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 13744
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 13729) (b := 13744) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta12995_psi_13729_bounds.2]
  · change Chebyshev.theta (↑(13849 : ℕ) : ℝ) ≤ (13858785 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 13849
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 13841) (b := 13849) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta12995_psi_13841_bounds.2]
  · change Chebyshev.theta (↑(13954 : ℕ) : ℝ) ≤ (13973155 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 13954
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 13933) (b := 13954) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta12995_psi_13933_bounds.2]
  · change Chebyshev.theta (↑(14068 : ℕ) : ℝ) ≤ (14068809 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 14068
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 14057) (b := 14068) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta12995_psi_14057_bounds.2]
  · change Chebyshev.theta (↑(14164 : ℕ) : ℝ) ≤ (14154759 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 14164
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 14159) (b := 14164) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta12995_psi_14159_bounds.2]
  · change Chebyshev.theta (↑(14250 : ℕ) : ℝ) ≤ (14221994 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 14250
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 14249) (b := 14250) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta12995_psi_14249_bounds.2]

/-- The envelope bound applies at every cell a endpoint. -/
theorem theta12995_a :
    ∀ r ∈ theta12995Cells,
      (r.ca : ℝ) / 1000 ≤
        Real.sqrt r.a *
          (Real.log r.a * (Real.log r.a - Real.log (Real.log r.a)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta12995Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 12995 *
          (Real.log 12995 * (Real.log 12995 - Real.log (Real.log 12995)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 13109 *
          (Real.log 13109 * (Real.log 13109 - Real.log (Real.log 13109)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 13232 *
          (Real.log 13232 * (Real.log 13232 - Real.log (Real.log 13232)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 13355 *
          (Real.log 13355 * (Real.log 13355 - Real.log (Real.log 13355)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 13469 *
          (Real.log 13469 * (Real.log 13469 - Real.log (Real.log 13469)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 13583 *
          (Real.log 13583 * (Real.log 13583 - Real.log (Real.log 13583)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 13669 *
          (Real.log 13669 * (Real.log 13669 - Real.log (Real.log 13669)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 13745 *
          (Real.log 13745 * (Real.log 13745 - Real.log (Real.log 13745)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 13850 *
          (Real.log 13850 * (Real.log 13850 - Real.log (Real.log 13850)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 13955 *
          (Real.log 13955 * (Real.log 13955 - Real.log (Real.log 13955)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 14069 *
          (Real.log 14069 * (Real.log 14069 - Real.log (Real.log 14069)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 14165 *
          (Real.log 14165 * (Real.log 14165 - Real.log (Real.log 14165)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)

/-- The envelope bound applies at every cell b endpoint. -/
theorem theta12995_b :
    ∀ r ∈ theta12995Cells,
      (r.cb : ℝ) / 1000 ≤
        Real.sqrt r.b *
          (Real.log r.b * (Real.log r.b - Real.log (Real.log r.b)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta12995Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 13109 *
          (Real.log 13109 * (Real.log 13109 - Real.log (Real.log 13109)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 13232 *
          (Real.log 13232 * (Real.log 13232 - Real.log (Real.log 13232)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 13355 *
          (Real.log 13355 * (Real.log 13355 - Real.log (Real.log 13355)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 13469 *
          (Real.log 13469 * (Real.log 13469 - Real.log (Real.log 13469)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 13583 *
          (Real.log 13583 * (Real.log 13583 - Real.log (Real.log 13583)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 13669 *
          (Real.log 13669 * (Real.log 13669 - Real.log (Real.log 13669)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 13745 *
          (Real.log 13745 * (Real.log 13745 - Real.log (Real.log 13745)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 13850 *
          (Real.log 13850 * (Real.log 13850 - Real.log (Real.log 13850)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 13955 *
          (Real.log 13955 * (Real.log 13955 - Real.log (Real.log 13955)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 14069 *
          (Real.log 14069 * (Real.log 14069 - Real.log (Real.log 14069)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 14165 *
          (Real.log 14165 * (Real.log 14165 - Real.log (Real.log 14165)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 14251 *
          (Real.log 14251 * (Real.log 14251 - Real.log (Real.log 14251)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)

/-- The cells form a checked chain covering `[12995, 14251)`. -/
theorem theta12995_check : leeNosalChainCheck 12995 14251 theta12995Cells = true := by
  decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
