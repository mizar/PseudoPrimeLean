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
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalEnvelope7776
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalMonotone
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalChecker

/-! # Batch certificate for Lee–Nosal theta cells -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The local cells store endpoint bounds in thousandths. -/
def theta7776Cells : List LeeNosalCell :=
  [⟨7776, 7837, 7626675, 7830484, 211000, 211000⟩, ⟨7837, 7882, 7671730, 7884550, 211000, 211000⟩,
    ⟨7882, 7936, 7725796, 7942774, 211000, 211000⟩, ⟨7936, 7995, 7784020, 7987829, 211000, 211000⟩,
    ⟨7995, 8040, 7829074, 8023872, 211000, 211000⟩, ⟨8040, 8076, 7865118, 8050905, 211000, 211000⟩,
    ⟨8076, 8103, 7892151, 8095266, 211000, 211000⟩, ⟨8103, 8147, 7936512, 8122299, 211000, 211000⟩,
    ⟨8147, 8183, 7972556, 8167354, 211000, 211000⟩, ⟨8183, 8219, 8008600, 8186069, 211000, 211000⟩,
    ⟨8219, 8247, 8036325, 8240134, 211000, 211000⟩, ⟨8247, 8292, 8081380, 8285189, 211000, 211000⟩]

/-- The kernel-checked prefix bounds for 7759. -/
theorem theta7776_psi_7759_bounds :
    (7784735 : ℝ) / 1000 ≤ Chebyshev.psi 7759 ∧ Chebyshev.psi 7759 ≤ (7785430 : ℝ) / 1000 := by
  have hl : 2 ^ 11231 ≤ Nat.lcmUpto 7759 := by decide +kernel
  have hu : Nat.lcmUpto 7759 ≤ 2 ^ (11231 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 7829. -/
theorem theta7776_psi_7829_bounds :
    (7829790 : ℝ) / 1000 ≤ Chebyshev.psi 7829 ∧ Chebyshev.psi 7829 ≤ (7830484 : ℝ) / 1000 := by
  have hl : 2 ^ 11296 ≤ Nat.lcmUpto 7829 := by decide +kernel
  have hu : Nat.lcmUpto 7829 ≤ 2 ^ (11296 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 7879. -/
theorem theta7776_psi_7879_bounds :
    (7883856 : ℝ) / 1000 ≤ Chebyshev.psi 7879 ∧ Chebyshev.psi 7879 ≤ (7884550 : ℝ) / 1000 := by
  have hl : 2 ^ 11374 ≤ Nat.lcmUpto 7879 := by decide +kernel
  have hu : Nat.lcmUpto 7879 ≤ 2 ^ (11374 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 7933. -/
theorem theta7776_psi_7933_bounds :
    (7942080 : ℝ) / 1000 ≤ Chebyshev.psi 7933 ∧ Chebyshev.psi 7933 ≤ (7942774 : ℝ) / 1000 := by
  have hl : 2 ^ 11458 ≤ Nat.lcmUpto 7933 := by decide +kernel
  have hu : Nat.lcmUpto 7933 ≤ 2 ^ (11458 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 7993. -/
theorem theta7776_psi_7993_bounds :
    (7987134 : ℝ) / 1000 ≤ Chebyshev.psi 7993 ∧ Chebyshev.psi 7993 ≤ (7987829 : ℝ) / 1000 := by
  have hl : 2 ^ 11523 ≤ Nat.lcmUpto 7993 := by decide +kernel
  have hu : Nat.lcmUpto 7993 ≤ 2 ^ (11523 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 8039. -/
theorem theta7776_psi_8039_bounds :
    (8023178 : ℝ) / 1000 ≤ Chebyshev.psi 8039 ∧ Chebyshev.psi 8039 ≤ (8023872 : ℝ) / 1000 := by
  have hl : 2 ^ 11575 ≤ Nat.lcmUpto 8039 := by decide +kernel
  have hu : Nat.lcmUpto 8039 ≤ 2 ^ (11575 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 8069. -/
theorem theta7776_psi_8069_bounds :
    (8050211 : ℝ) / 1000 ≤ Chebyshev.psi 8069 ∧ Chebyshev.psi 8069 ≤ (8050905 : ℝ) / 1000 := by
  have hl : 2 ^ 11614 ≤ Nat.lcmUpto 8069 := by decide +kernel
  have hu : Nat.lcmUpto 8069 ≤ 2 ^ (11614 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 8101. -/
theorem theta7776_psi_8101_bounds :
    (8094572 : ℝ) / 1000 ≤ Chebyshev.psi 8101 ∧ Chebyshev.psi 8101 ≤ (8095266 : ℝ) / 1000 := by
  have hl : 2 ^ 11678 ≤ Nat.lcmUpto 8101 := by decide +kernel
  have hu : Nat.lcmUpto 8101 ≤ 2 ^ (11678 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 8123. -/
theorem theta7776_psi_8123_bounds :
    (8121605 : ℝ) / 1000 ≤ Chebyshev.psi 8123 ∧ Chebyshev.psi 8123 ≤ (8122299 : ℝ) / 1000 := by
  have hl : 2 ^ 11717 ≤ Nat.lcmUpto 8123 := by decide +kernel
  have hu : Nat.lcmUpto 8123 ≤ 2 ^ (11717 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 8147. -/
theorem theta7776_psi_8147_bounds :
    (8130616 : ℝ) / 1000 ≤ Chebyshev.psi 8147 ∧ Chebyshev.psi 8147 ≤ (8131310 : ℝ) / 1000 := by
  have hl : 2 ^ 11730 ≤ Nat.lcmUpto 8147 := by decide +kernel
  have hu : Nat.lcmUpto 8147 ≤ 2 ^ (11730 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 8179. -/
theorem theta7776_psi_8179_bounds :
    (8166660 : ℝ) / 1000 ≤ Chebyshev.psi 8179 ∧ Chebyshev.psi 8179 ≤ (8167354 : ℝ) / 1000 := by
  have hl : 2 ^ 11782 ≤ Nat.lcmUpto 8179 := by decide +kernel
  have hu : Nat.lcmUpto 8179 ≤ 2 ^ (11782 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 8209. -/
theorem theta7776_psi_8209_bounds :
    (8185375 : ℝ) / 1000 ≤ Chebyshev.psi 8209 ∧ Chebyshev.psi 8209 ≤ (8186069 : ℝ) / 1000 := by
  have hl : 2 ^ 11809 ≤ Nat.lcmUpto 8209 := by decide +kernel
  have hu : Nat.lcmUpto 8209 ≤ 2 ^ (11809 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 8219. -/
theorem theta7776_psi_8219_bounds :
    (8194385 : ℝ) / 1000 ≤ Chebyshev.psi 8219 ∧ Chebyshev.psi 8219 ≤ (8195080 : ℝ) / 1000 := by
  have hl : 2 ^ 11822 ≤ Nat.lcmUpto 8219 := by decide +kernel
  have hu : Nat.lcmUpto 8219 ≤ 2 ^ (11822 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 8243. -/
theorem theta7776_psi_8243_bounds :
    (8239440 : ℝ) / 1000 ≤ Chebyshev.psi 8243 ∧ Chebyshev.psi 8243 ≤ (8240134 : ℝ) / 1000 := by
  have hl : 2 ^ 11887 ≤ Nat.lcmUpto 8243 := by decide +kernel
  have hu : Nat.lcmUpto 8243 ≤ 2 ^ (11887 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 8291. -/
theorem theta7776_psi_8291_bounds :
    (8284495 : ℝ) / 1000 ≤ Chebyshev.psi 8291 ∧ Chebyshev.psi 8291 ≤ (8285189 : ℝ) / 1000 := by
  have hl : 2 ^ 11952 ≤ Nat.lcmUpto 8291 := by decide +kernel
  have hu : Nat.lcmUpto 8291 ≤ 2 ^ (11952 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- Every batch cell has a checked theta lower bound. -/
theorem theta7776_lower : ∀ r ∈ theta7776Cells, (r.lo : ℝ) / 1000 ≤ Chebyshev.theta r.a := by
  intro r hr
  simp only [theta7776Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (7626675 : ℝ) / 1000 ≤ Chebyshev.theta (↑(7776 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 7776) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 7759) (b := 7776) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta7776_psi_7759_bounds.1]
  · change (7671730 : ℝ) / 1000 ≤ Chebyshev.theta (↑(7837 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 7837) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 7829) (b := 7837) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta7776_psi_7829_bounds.1]
  · change (7725796 : ℝ) / 1000 ≤ Chebyshev.theta (↑(7882 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 7882) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 7879) (b := 7882) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta7776_psi_7879_bounds.1]
  · change (7784020 : ℝ) / 1000 ≤ Chebyshev.theta (↑(7936 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 7936) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 7933) (b := 7936) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta7776_psi_7933_bounds.1]
  · change (7829074 : ℝ) / 1000 ≤ Chebyshev.theta (↑(7995 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 7995) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 7993) (b := 7995) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta7776_psi_7993_bounds.1]
  · change (7865118 : ℝ) / 1000 ≤ Chebyshev.theta (↑(8040 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 8040) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 8039) (b := 8040) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta7776_psi_8039_bounds.1]
  · change (7892151 : ℝ) / 1000 ≤ Chebyshev.theta (↑(8076 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 8076) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 8069) (b := 8076) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta7776_psi_8069_bounds.1]
  · change (7936512 : ℝ) / 1000 ≤ Chebyshev.theta (↑(8103 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 8103) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 8101) (b := 8103) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta7776_psi_8101_bounds.1]
  · change (7972556 : ℝ) / 1000 ≤ Chebyshev.theta (↑(8147 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 8147) (by norm_num only) (by norm_num only)
    linarith only [hd, theta7776_psi_8147_bounds.1]
  · change (8008600 : ℝ) / 1000 ≤ Chebyshev.theta (↑(8183 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 8183) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 8179) (b := 8183) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta7776_psi_8179_bounds.1]
  · change (8036325 : ℝ) / 1000 ≤ Chebyshev.theta (↑(8219 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 8219) (by norm_num only) (by norm_num only)
    linarith only [hd, theta7776_psi_8219_bounds.1]
  · change (8081380 : ℝ) / 1000 ≤ Chebyshev.theta (↑(8247 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 8247) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 8243) (b := 8247) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta7776_psi_8243_bounds.1]

/-- Every batch cell has a checked theta upper bound. -/
theorem theta7776_upper :
    ∀ r ∈ theta7776Cells, Chebyshev.theta (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [theta7776Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Chebyshev.theta (↑(7836 : ℕ) : ℝ) ≤ (7830484 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 7836
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 7829) (b := 7836) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta7776_psi_7829_bounds.2]
  · change Chebyshev.theta (↑(7881 : ℕ) : ℝ) ≤ (7884550 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 7881
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 7879) (b := 7881) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta7776_psi_7879_bounds.2]
  · change Chebyshev.theta (↑(7935 : ℕ) : ℝ) ≤ (7942774 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 7935
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 7933) (b := 7935) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta7776_psi_7933_bounds.2]
  · change Chebyshev.theta (↑(7994 : ℕ) : ℝ) ≤ (7987829 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 7994
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 7993) (b := 7994) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta7776_psi_7993_bounds.2]
  · change Chebyshev.theta (↑(8039 : ℕ) : ℝ) ≤ (8023872 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 8039
    linarith only [hd, theta7776_psi_8039_bounds.2]
  · change Chebyshev.theta (↑(8075 : ℕ) : ℝ) ≤ (8050905 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 8075
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 8069) (b := 8075) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta7776_psi_8069_bounds.2]
  · change Chebyshev.theta (↑(8102 : ℕ) : ℝ) ≤ (8095266 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 8102
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 8101) (b := 8102) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta7776_psi_8101_bounds.2]
  · change Chebyshev.theta (↑(8146 : ℕ) : ℝ) ≤ (8122299 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 8146
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 8123) (b := 8146) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta7776_psi_8123_bounds.2]
  · change Chebyshev.theta (↑(8182 : ℕ) : ℝ) ≤ (8167354 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 8182
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 8179) (b := 8182) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta7776_psi_8179_bounds.2]
  · change Chebyshev.theta (↑(8218 : ℕ) : ℝ) ≤ (8186069 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 8218
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 8209) (b := 8218) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta7776_psi_8209_bounds.2]
  · change Chebyshev.theta (↑(8246 : ℕ) : ℝ) ≤ (8240134 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 8246
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 8243) (b := 8246) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta7776_psi_8243_bounds.2]
  · change Chebyshev.theta (↑(8291 : ℕ) : ℝ) ≤ (8285189 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 8291
    linarith only [hd, theta7776_psi_8291_bounds.2]

/-- The envelope bound applies at every cell a endpoint. -/
theorem theta7776_a :
    ∀ r ∈ theta7776Cells,
      (r.ca : ℝ) / 1000 ≤
        Real.sqrt r.a *
          (Real.log r.a * (Real.log r.a - Real.log (Real.log r.a)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta7776Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 7776 *
          (Real.log 7776 * (Real.log 7776 - Real.log (Real.log 7776)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 7837 *
          (Real.log 7837 * (Real.log 7837 - Real.log (Real.log 7837)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 7882 *
          (Real.log 7882 * (Real.log 7882 - Real.log (Real.log 7882)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 7936 *
          (Real.log 7936 * (Real.log 7936 - Real.log (Real.log 7936)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 7995 *
          (Real.log 7995 * (Real.log 7995 - Real.log (Real.log 7995)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8040 *
          (Real.log 8040 * (Real.log 8040 - Real.log (Real.log 8040)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8076 *
          (Real.log 8076 * (Real.log 8076 - Real.log (Real.log 8076)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8103 *
          (Real.log 8103 * (Real.log 8103 - Real.log (Real.log 8103)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8147 *
          (Real.log 8147 * (Real.log 8147 - Real.log (Real.log 8147)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8183 *
          (Real.log 8183 * (Real.log 8183 - Real.log (Real.log 8183)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8219 *
          (Real.log 8219 * (Real.log 8219 - Real.log (Real.log 8219)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8247 *
          (Real.log 8247 * (Real.log 8247 - Real.log (Real.log 8247)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)

/-- The envelope bound applies at every cell b endpoint. -/
theorem theta7776_b :
    ∀ r ∈ theta7776Cells,
      (r.cb : ℝ) / 1000 ≤
        Real.sqrt r.b *
          (Real.log r.b * (Real.log r.b - Real.log (Real.log r.b)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta7776Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 7837 *
          (Real.log 7837 * (Real.log 7837 - Real.log (Real.log 7837)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 7882 *
          (Real.log 7882 * (Real.log 7882 - Real.log (Real.log 7882)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 7936 *
          (Real.log 7936 * (Real.log 7936 - Real.log (Real.log 7936)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 7995 *
          (Real.log 7995 * (Real.log 7995 - Real.log (Real.log 7995)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8040 *
          (Real.log 8040 * (Real.log 8040 - Real.log (Real.log 8040)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8076 *
          (Real.log 8076 * (Real.log 8076 - Real.log (Real.log 8076)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8103 *
          (Real.log 8103 * (Real.log 8103 - Real.log (Real.log 8103)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8147 *
          (Real.log 8147 * (Real.log 8147 - Real.log (Real.log 8147)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8183 *
          (Real.log 8183 * (Real.log 8183 - Real.log (Real.log 8183)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8219 *
          (Real.log 8219 * (Real.log 8219 - Real.log (Real.log 8219)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8247 *
          (Real.log 8247 * (Real.log 8247 - Real.log (Real.log 8247)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8292 *
          (Real.log 8292 * (Real.log 8292 - Real.log (Real.log 8292)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)

/-- The cells form a checked chain covering `[7776, 8292)`. -/
theorem theta7776_check : leeNosalChainCheck 7776 8292 theta7776Cells = true := by decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
