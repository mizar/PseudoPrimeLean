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
def theta18085Cells : List LeeNosalCell :=
  [⟨18085, 18232, 17867920, 18260270, 365000, 365000⟩,
    ⟨18232, 18399, 18034276, 18437022, 365000, 365000⟩,
    ⟨18399, 18576, 18211028, 18613775, 365000, 365000⟩,
    ⟨18576, 18752, 18387781, 18761415, 365000, 365000⟩,
    ⟨18752, 18900, 18535421, 18864694, 365000, 365000⟩,
    ⟨18900, 19003, 18638700, 18953417, 365000, 365000⟩,
    ⟨19003, 19092, 18727423, 19051844, 365000, 365000⟩,
    ⟨19092, 19190, 18825850, 19121159, 365000, 365000⟩,
    ⟨19190, 19260, 18895164, 19199484, 365000, 365000⟩,
    ⟨19260, 19338, 18973490, 19273651, 365000, 365000⟩,
    ⟨19338, 19412, 19047657, 19333262, 365000, 365000⟩,
    ⟨19412, 19472, 19107268, 19451790, 365000, 365000⟩]

/-- The kernel-checked prefix bounds for 18077. -/
theorem theta18085_psi_18077_bounds :
    (18093220 : ℝ) / 1000 ≤ Chebyshev.psi 18077 ∧ Chebyshev.psi 18077 ≤ (18093915 : ℝ) / 1000 := by
  have hl : 2 ^ 26103 ≤ Nat.lcmUpto 18077 := by decide +kernel
  have hu : Nat.lcmUpto 18077 ≤ 2 ^ (26103 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 18229. -/
theorem theta18085_psi_18229_bounds :
    (18259576 : ℝ) / 1000 ≤ Chebyshev.psi 18229 ∧ Chebyshev.psi 18229 ≤ (18260270 : ℝ) / 1000 := by
  have hl : 2 ^ 26343 ≤ Nat.lcmUpto 18229 := by decide +kernel
  have hu : Nat.lcmUpto 18229 ≤ 2 ^ (26343 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 18397. -/
theorem theta18085_psi_18397_bounds :
    (18436328 : ℝ) / 1000 ≤ Chebyshev.psi 18397 ∧ Chebyshev.psi 18397 ≤ (18437022 : ℝ) / 1000 := by
  have hl : 2 ^ 26598 ≤ Nat.lcmUpto 18397 := by decide +kernel
  have hu : Nat.lcmUpto 18397 ≤ 2 ^ (26598 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 18553. -/
theorem theta18085_psi_18553_bounds :
    (18613081 : ℝ) / 1000 ≤ Chebyshev.psi 18553 ∧ Chebyshev.psi 18553 ≤ (18613775 : ℝ) / 1000 := by
  have hl : 2 ^ 26853 ≤ Nat.lcmUpto 18553 := by decide +kernel
  have hu : Nat.lcmUpto 18553 ≤ 2 ^ (26853 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 18749. -/
theorem theta18085_psi_18749_bounds :
    (18760721 : ℝ) / 1000 ≤ Chebyshev.psi 18749 ∧ Chebyshev.psi 18749 ≤ (18761415 : ℝ) / 1000 := by
  have hl : 2 ^ 27066 ≤ Nat.lcmUpto 18749 := by decide +kernel
  have hu : Nat.lcmUpto 18749 ≤ 2 ^ (27066 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 18899. -/
theorem theta18085_psi_18899_bounds :
    (18864000 : ℝ) / 1000 ≤ Chebyshev.psi 18899 ∧ Chebyshev.psi 18899 ≤ (18864694 : ℝ) / 1000 := by
  have hl : 2 ^ 27215 ≤ Nat.lcmUpto 18899 := by decide +kernel
  have hu : Nat.lcmUpto 18899 ≤ 2 ^ (27215 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 19001. -/
theorem theta18085_psi_19001_bounds :
    (18952723 : ℝ) / 1000 ≤ Chebyshev.psi 19001 ∧ Chebyshev.psi 19001 ≤ (18953417 : ℝ) / 1000 := by
  have hl : 2 ^ 27343 ≤ Nat.lcmUpto 19001 := by decide +kernel
  have hu : Nat.lcmUpto 19001 ≤ 2 ^ (27343 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 19087. -/
theorem theta18085_psi_19087_bounds :
    (19051150 : ℝ) / 1000 ≤ Chebyshev.psi 19087 ∧ Chebyshev.psi 19087 ≤ (19051844 : ℝ) / 1000 := by
  have hl : 2 ^ 27485 ≤ Nat.lcmUpto 19087 := by decide +kernel
  have hu : Nat.lcmUpto 19087 ≤ 2 ^ (27485 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 19183. -/
theorem theta18085_psi_19183_bounds :
    (19120464 : ℝ) / 1000 ≤ Chebyshev.psi 19183 ∧ Chebyshev.psi 19183 ≤ (19121159 : ℝ) / 1000 := by
  have hl : 2 ^ 27585 ≤ Nat.lcmUpto 19183 := by decide +kernel
  have hu : Nat.lcmUpto 19183 ≤ 2 ^ (27585 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 19259. -/
theorem theta18085_psi_19259_bounds :
    (19198790 : ℝ) / 1000 ≤ Chebyshev.psi 19259 ∧ Chebyshev.psi 19259 ≤ (19199484 : ℝ) / 1000 := by
  have hl : 2 ^ 27698 ≤ Nat.lcmUpto 19259 := by decide +kernel
  have hu : Nat.lcmUpto 19259 ≤ 2 ^ (27698 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 19333. -/
theorem theta18085_psi_19333_bounds :
    (19272957 : ℝ) / 1000 ≤ Chebyshev.psi 19333 ∧ Chebyshev.psi 19333 ≤ (19273651 : ℝ) / 1000 := by
  have hl : 2 ^ 27805 ≤ Nat.lcmUpto 19333 := by decide +kernel
  have hu : Nat.lcmUpto 19333 ≤ 2 ^ (27805 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 19403. -/
theorem theta18085_psi_19403_bounds :
    (19332568 : ℝ) / 1000 ≤ Chebyshev.psi 19403 ∧ Chebyshev.psi 19403 ≤ (19333262 : ℝ) / 1000 := by
  have hl : 2 ^ 27891 ≤ Nat.lcmUpto 19403 := by decide +kernel
  have hu : Nat.lcmUpto 19403 ≤ 2 ^ (27891 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 19471. -/
theorem theta18085_psi_19471_bounds :
    (19451096 : ℝ) / 1000 ≤ Chebyshev.psi 19471 ∧ Chebyshev.psi 19471 ≤ (19451790 : ℝ) / 1000 := by
  have hl : 2 ^ 28062 ≤ Nat.lcmUpto 19471 := by decide +kernel
  have hu : Nat.lcmUpto 19471 ≤ 2 ^ (28062 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- Every batch cell has a checked theta lower bound. -/
theorem theta18085_lower : ∀ r ∈ theta18085Cells, (r.lo : ℝ) / 1000 ≤ Chebyshev.theta r.a := by
  intro r hr
  simp only [theta18085Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (17867920 : ℝ) / 1000 ≤ Chebyshev.theta (↑(18085 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 18085) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 18077) (b := 18085) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta18085_psi_18077_bounds.1]
  · change (18034276 : ℝ) / 1000 ≤ Chebyshev.theta (↑(18232 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 18232) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 18229) (b := 18232) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta18085_psi_18229_bounds.1]
  · change (18211028 : ℝ) / 1000 ≤ Chebyshev.theta (↑(18399 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 18399) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 18397) (b := 18399) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta18085_psi_18397_bounds.1]
  · change (18387781 : ℝ) / 1000 ≤ Chebyshev.theta (↑(18576 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 18576) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 18553) (b := 18576) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta18085_psi_18553_bounds.1]
  · change (18535421 : ℝ) / 1000 ≤ Chebyshev.theta (↑(18752 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 18752) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 18749) (b := 18752) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta18085_psi_18749_bounds.1]
  · change (18638700 : ℝ) / 1000 ≤ Chebyshev.theta (↑(18900 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 18900) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 18899) (b := 18900) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta18085_psi_18899_bounds.1]
  · change (18727423 : ℝ) / 1000 ≤ Chebyshev.theta (↑(19003 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 19003) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 19001) (b := 19003) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta18085_psi_19001_bounds.1]
  · change (18825850 : ℝ) / 1000 ≤ Chebyshev.theta (↑(19092 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 19092) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 19087) (b := 19092) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta18085_psi_19087_bounds.1]
  · change (18895164 : ℝ) / 1000 ≤ Chebyshev.theta (↑(19190 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 19190) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 19183) (b := 19190) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta18085_psi_19183_bounds.1]
  · change (18973490 : ℝ) / 1000 ≤ Chebyshev.theta (↑(19260 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 19260) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 19259) (b := 19260) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta18085_psi_19259_bounds.1]
  · change (19047657 : ℝ) / 1000 ≤ Chebyshev.theta (↑(19338 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 19338) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 19333) (b := 19338) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta18085_psi_19333_bounds.1]
  · change (19107268 : ℝ) / 1000 ≤ Chebyshev.theta (↑(19412 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 19412) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 19403) (b := 19412) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta18085_psi_19403_bounds.1]

/-- Every batch cell has a checked theta upper bound. -/
theorem theta18085_upper :
    ∀ r ∈ theta18085Cells, Chebyshev.theta (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [theta18085Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Chebyshev.theta (↑(18231 : ℕ) : ℝ) ≤ (18260270 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 18231
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 18229) (b := 18231) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta18085_psi_18229_bounds.2]
  · change Chebyshev.theta (↑(18398 : ℕ) : ℝ) ≤ (18437022 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 18398
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 18397) (b := 18398) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta18085_psi_18397_bounds.2]
  · change Chebyshev.theta (↑(18575 : ℕ) : ℝ) ≤ (18613775 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 18575
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 18553) (b := 18575) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta18085_psi_18553_bounds.2]
  · change Chebyshev.theta (↑(18751 : ℕ) : ℝ) ≤ (18761415 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 18751
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 18749) (b := 18751) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta18085_psi_18749_bounds.2]
  · change Chebyshev.theta (↑(18899 : ℕ) : ℝ) ≤ (18864694 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 18899
    linarith only [hd, theta18085_psi_18899_bounds.2]
  · change Chebyshev.theta (↑(19002 : ℕ) : ℝ) ≤ (18953417 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 19002
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 19001) (b := 19002) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta18085_psi_19001_bounds.2]
  · change Chebyshev.theta (↑(19091 : ℕ) : ℝ) ≤ (19051844 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 19091
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 19087) (b := 19091) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta18085_psi_19087_bounds.2]
  · change Chebyshev.theta (↑(19189 : ℕ) : ℝ) ≤ (19121159 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 19189
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 19183) (b := 19189) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta18085_psi_19183_bounds.2]
  · change Chebyshev.theta (↑(19259 : ℕ) : ℝ) ≤ (19199484 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 19259
    linarith only [hd, theta18085_psi_19259_bounds.2]
  · change Chebyshev.theta (↑(19337 : ℕ) : ℝ) ≤ (19273651 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 19337
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 19333) (b := 19337) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta18085_psi_19333_bounds.2]
  · change Chebyshev.theta (↑(19411 : ℕ) : ℝ) ≤ (19333262 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 19411
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 19403) (b := 19411) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta18085_psi_19403_bounds.2]
  · change Chebyshev.theta (↑(19471 : ℕ) : ℝ) ≤ (19451790 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 19471
    linarith only [hd, theta18085_psi_19471_bounds.2]

/-- The envelope bound applies at every cell a endpoint. -/
theorem theta18085_a :
    ∀ r ∈ theta18085Cells,
      (r.ca : ℝ) / 1000 ≤
        Real.sqrt r.a *
          (Real.log r.a * (Real.log r.a - Real.log (Real.log r.a)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta18085Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 18085 *
          (Real.log 18085 * (Real.log 18085 - Real.log (Real.log 18085)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 18232 *
          (Real.log 18232 * (Real.log 18232 - Real.log (Real.log 18232)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 18399 *
          (Real.log 18399 * (Real.log 18399 - Real.log (Real.log 18399)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 18576 *
          (Real.log 18576 * (Real.log 18576 - Real.log (Real.log 18576)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 18752 *
          (Real.log 18752 * (Real.log 18752 - Real.log (Real.log 18752)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 18900 *
          (Real.log 18900 * (Real.log 18900 - Real.log (Real.log 18900)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 19003 *
          (Real.log 19003 * (Real.log 19003 - Real.log (Real.log 19003)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 19092 *
          (Real.log 19092 * (Real.log 19092 - Real.log (Real.log 19092)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 19190 *
          (Real.log 19190 * (Real.log 19190 - Real.log (Real.log 19190)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 19260 *
          (Real.log 19260 * (Real.log 19260 - Real.log (Real.log 19260)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 19338 *
          (Real.log 19338 * (Real.log 19338 - Real.log (Real.log 19338)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 19412 *
          (Real.log 19412 * (Real.log 19412 - Real.log (Real.log 19412)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)

/-- The envelope bound applies at every cell b endpoint. -/
theorem theta18085_b :
    ∀ r ∈ theta18085Cells,
      (r.cb : ℝ) / 1000 ≤
        Real.sqrt r.b *
          (Real.log r.b * (Real.log r.b - Real.log (Real.log r.b)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta18085Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 18232 *
          (Real.log 18232 * (Real.log 18232 - Real.log (Real.log 18232)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 18399 *
          (Real.log 18399 * (Real.log 18399 - Real.log (Real.log 18399)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 18576 *
          (Real.log 18576 * (Real.log 18576 - Real.log (Real.log 18576)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 18752 *
          (Real.log 18752 * (Real.log 18752 - Real.log (Real.log 18752)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 18900 *
          (Real.log 18900 * (Real.log 18900 - Real.log (Real.log 18900)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 19003 *
          (Real.log 19003 * (Real.log 19003 - Real.log (Real.log 19003)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 19092 *
          (Real.log 19092 * (Real.log 19092 - Real.log (Real.log 19092)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 19190 *
          (Real.log 19190 * (Real.log 19190 - Real.log (Real.log 19190)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 19260 *
          (Real.log 19260 * (Real.log 19260 - Real.log (Real.log 19260)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 19338 *
          (Real.log 19338 * (Real.log 19338 - Real.log (Real.log 19338)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 19412 *
          (Real.log 19412 * (Real.log 19412 - Real.log (Real.log 19412)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 19472 *
          (Real.log 19472 * (Real.log 19472 - Real.log (Real.log 19472)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)

/-- The cells form a checked chain covering `[18085, 19472)`. -/
theorem theta18085_check : leeNosalChainCheck 18085 19472 theta18085Cells = true := by
  decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
