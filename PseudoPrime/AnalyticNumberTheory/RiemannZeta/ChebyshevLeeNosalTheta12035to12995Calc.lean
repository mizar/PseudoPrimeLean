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
def theta12035Cells : List LeeNosalCell :=
  [⟨12035, 12091, 11836851, 12051751, 255000, 255000⟩,
    ⟨12091, 12147, 11892996, 12117600, 255000, 255000⟩,
    ⟨12147, 12213, 11958845, 12186914, 255000, 255000⟩,
    ⟨12213, 12283, 12028160, 12271478, 255000, 255000⟩,
    ⟨12283, 12367, 12112724, 12328316, 255000, 255000⟩,
    ⟨12367, 12424, 12169562, 12403176, 255000, 255000⟩,
    ⟨12424, 12499, 12244422, 12488433, 255000, 255000⟩,
    ⟨12499, 12584, 12329679, 12592405, 255000, 255000⟩,
    ⟨12584, 12688, 12433651, 12695684, 255000, 255000⟩,
    ⟨12688, 12791, 12536930, 12795497, 255000, 255000⟩,
    ⟨12791, 12900, 12645754, 12899470, 255000, 255000⟩,
    ⟨12900, 12995, 12740715, 13013146, 255000, 255000⟩]

/-- The kernel-checked prefix bounds for 12011. -/
theorem theta12035_psi_12011_bounds :
    (11994911 : ℝ) / 1000 ≤ Chebyshev.psi 12011 ∧ Chebyshev.psi 12011 ≤ (11995606 : ℝ) / 1000 := by
  have hl : 2 ^ 17305 ≤ Nat.lcmUpto 12011 := by decide +kernel
  have hu : Nat.lcmUpto 12011 ≤ 2 ^ (17305 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 12073. -/
theorem theta12035_psi_12073_bounds :
    (12051056 : ℝ) / 1000 ≤ Chebyshev.psi 12073 ∧ Chebyshev.psi 12073 ≤ (12051751 : ℝ) / 1000 := by
  have hl : 2 ^ 17386 ≤ Nat.lcmUpto 12073 := by decide +kernel
  have hu : Nat.lcmUpto 12073 ≤ 2 ^ (17386 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 12143. -/
theorem theta12035_psi_12143_bounds :
    (12116905 : ℝ) / 1000 ≤ Chebyshev.psi 12143 ∧ Chebyshev.psi 12143 ≤ (12117600 : ℝ) / 1000 := by
  have hl : 2 ^ 17481 ≤ Nat.lcmUpto 12143 := by decide +kernel
  have hu : Nat.lcmUpto 12143 ≤ 2 ^ (17481 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 12211. -/
theorem theta12035_psi_12211_bounds :
    (12186220 : ℝ) / 1000 ≤ Chebyshev.psi 12211 ∧ Chebyshev.psi 12211 ≤ (12186914 : ℝ) / 1000 := by
  have hl : 2 ^ 17581 ≤ Nat.lcmUpto 12211 := by decide +kernel
  have hu : Nat.lcmUpto 12211 ≤ 2 ^ (17581 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 12281. -/
theorem theta12035_psi_12281_bounds :
    (12270784 : ℝ) / 1000 ≤ Chebyshev.psi 12281 ∧ Chebyshev.psi 12281 ≤ (12271478 : ℝ) / 1000 := by
  have hl : 2 ^ 17703 ≤ Nat.lcmUpto 12281 := by decide +kernel
  have hu : Nat.lcmUpto 12281 ≤ 2 ^ (17703 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 12347. -/
theorem theta12035_psi_12347_bounds :
    (12327622 : ℝ) / 1000 ≤ Chebyshev.psi 12347 ∧ Chebyshev.psi 12347 ≤ (12328316 : ℝ) / 1000 := by
  have hl : 2 ^ 17785 ≤ Nat.lcmUpto 12347 := by decide +kernel
  have hu : Nat.lcmUpto 12347 ≤ 2 ^ (17785 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 12421. -/
theorem theta12035_psi_12421_bounds :
    (12402482 : ℝ) / 1000 ≤ Chebyshev.psi 12421 ∧ Chebyshev.psi 12421 ≤ (12403176 : ℝ) / 1000 := by
  have hl : 2 ^ 17893 ≤ Nat.lcmUpto 12421 := by decide +kernel
  have hu : Nat.lcmUpto 12421 ≤ 2 ^ (17893 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 12497. -/
theorem theta12035_psi_12497_bounds :
    (12487739 : ℝ) / 1000 ≤ Chebyshev.psi 12497 ∧ Chebyshev.psi 12497 ≤ (12488433 : ℝ) / 1000 := by
  have hl : 2 ^ 18016 ≤ Nat.lcmUpto 12497 := by decide +kernel
  have hu : Nat.lcmUpto 12497 ≤ 2 ^ (18016 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 12583. -/
theorem theta12035_psi_12583_bounds :
    (12591711 : ℝ) / 1000 ≤ Chebyshev.psi 12583 ∧ Chebyshev.psi 12583 ≤ (12592405 : ℝ) / 1000 := by
  have hl : 2 ^ 18166 ≤ Nat.lcmUpto 12583 := by decide +kernel
  have hu : Nat.lcmUpto 12583 ≤ 2 ^ (18166 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 12671. -/
theorem theta12035_psi_12671_bounds :
    (12694990 : ℝ) / 1000 ≤ Chebyshev.psi 12671 ∧ Chebyshev.psi 12671 ≤ (12695684 : ℝ) / 1000 := by
  have hl : 2 ^ 18315 ≤ Nat.lcmUpto 12671 := by decide +kernel
  have hu : Nat.lcmUpto 12671 ≤ 2 ^ (18315 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 12781. -/
theorem theta12035_psi_12781_bounds :
    (12794803 : ℝ) / 1000 ≤ Chebyshev.psi 12781 ∧ Chebyshev.psi 12781 ≤ (12795497 : ℝ) / 1000 := by
  have hl : 2 ^ 18459 ≤ Nat.lcmUpto 12781 := by decide +kernel
  have hu : Nat.lcmUpto 12781 ≤ 2 ^ (18459 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 12791. -/
theorem theta12035_psi_12791_bounds :
    (12803814 : ℝ) / 1000 ≤ Chebyshev.psi 12791 ∧ Chebyshev.psi 12791 ≤ (12804508 : ℝ) / 1000 := by
  have hl : 2 ^ 18472 ≤ Nat.lcmUpto 12791 := by decide +kernel
  have hu : Nat.lcmUpto 12791 ≤ 2 ^ (18472 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 12899. -/
theorem theta12035_psi_12899_bounds :
    (12898775 : ℝ) / 1000 ≤ Chebyshev.psi 12899 ∧ Chebyshev.psi 12899 ≤ (12899470 : ℝ) / 1000 := by
  have hl : 2 ^ 18609 ≤ Nat.lcmUpto 12899 := by decide +kernel
  have hu : Nat.lcmUpto 12899 ≤ 2 ^ (18609 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 12983. -/
theorem theta12035_psi_12983_bounds :
    (13012452 : ℝ) / 1000 ≤ Chebyshev.psi 12983 ∧ Chebyshev.psi 12983 ≤ (13013146 : ℝ) / 1000 := by
  have hl : 2 ^ 18773 ≤ Nat.lcmUpto 12983 := by decide +kernel
  have hu : Nat.lcmUpto 12983 ≤ 2 ^ (18773 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- Every batch cell has a checked theta lower bound. -/
theorem theta12035_lower : ∀ r ∈ theta12035Cells, (r.lo : ℝ) / 1000 ≤ Chebyshev.theta r.a := by
  intro r hr
  simp only [theta12035Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (11836851 : ℝ) / 1000 ≤ Chebyshev.theta (↑(12035 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 12035) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 12011) (b := 12035) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta12035_psi_12011_bounds.1]
  · change (11892996 : ℝ) / 1000 ≤ Chebyshev.theta (↑(12091 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 12091) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 12073) (b := 12091) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta12035_psi_12073_bounds.1]
  · change (11958845 : ℝ) / 1000 ≤ Chebyshev.theta (↑(12147 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 12147) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 12143) (b := 12147) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta12035_psi_12143_bounds.1]
  · change (12028160 : ℝ) / 1000 ≤ Chebyshev.theta (↑(12213 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 12213) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 12211) (b := 12213) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta12035_psi_12211_bounds.1]
  · change (12112724 : ℝ) / 1000 ≤ Chebyshev.theta (↑(12283 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 12283) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 12281) (b := 12283) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta12035_psi_12281_bounds.1]
  · change (12169562 : ℝ) / 1000 ≤ Chebyshev.theta (↑(12367 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 12367) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 12347) (b := 12367) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta12035_psi_12347_bounds.1]
  · change (12244422 : ℝ) / 1000 ≤ Chebyshev.theta (↑(12424 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 12424) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 12421) (b := 12424) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta12035_psi_12421_bounds.1]
  · change (12329679 : ℝ) / 1000 ≤ Chebyshev.theta (↑(12499 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 12499) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 12497) (b := 12499) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta12035_psi_12497_bounds.1]
  · change (12433651 : ℝ) / 1000 ≤ Chebyshev.theta (↑(12584 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 12584) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 12583) (b := 12584) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta12035_psi_12583_bounds.1]
  · change (12536930 : ℝ) / 1000 ≤ Chebyshev.theta (↑(12688 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 12688) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 12671) (b := 12688) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta12035_psi_12671_bounds.1]
  · change (12645754 : ℝ) / 1000 ≤ Chebyshev.theta (↑(12791 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 12791) (by norm_num only) (by norm_num only)
    linarith only [hd, theta12035_psi_12791_bounds.1]
  · change (12740715 : ℝ) / 1000 ≤ Chebyshev.theta (↑(12900 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 12900) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 12899) (b := 12900) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta12035_psi_12899_bounds.1]

/-- Every batch cell has a checked theta upper bound. -/
theorem theta12035_upper :
    ∀ r ∈ theta12035Cells, Chebyshev.theta (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [theta12035Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Chebyshev.theta (↑(12090 : ℕ) : ℝ) ≤ (12051751 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 12090
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 12073) (b := 12090) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta12035_psi_12073_bounds.2]
  · change Chebyshev.theta (↑(12146 : ℕ) : ℝ) ≤ (12117600 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 12146
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 12143) (b := 12146) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta12035_psi_12143_bounds.2]
  · change Chebyshev.theta (↑(12212 : ℕ) : ℝ) ≤ (12186914 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 12212
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 12211) (b := 12212) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta12035_psi_12211_bounds.2]
  · change Chebyshev.theta (↑(12282 : ℕ) : ℝ) ≤ (12271478 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 12282
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 12281) (b := 12282) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta12035_psi_12281_bounds.2]
  · change Chebyshev.theta (↑(12366 : ℕ) : ℝ) ≤ (12328316 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 12366
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 12347) (b := 12366) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta12035_psi_12347_bounds.2]
  · change Chebyshev.theta (↑(12423 : ℕ) : ℝ) ≤ (12403176 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 12423
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 12421) (b := 12423) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta12035_psi_12421_bounds.2]
  · change Chebyshev.theta (↑(12498 : ℕ) : ℝ) ≤ (12488433 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 12498
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 12497) (b := 12498) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta12035_psi_12497_bounds.2]
  · change Chebyshev.theta (↑(12583 : ℕ) : ℝ) ≤ (12592405 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 12583
    linarith only [hd, theta12035_psi_12583_bounds.2]
  · change Chebyshev.theta (↑(12687 : ℕ) : ℝ) ≤ (12695684 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 12687
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 12671) (b := 12687) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta12035_psi_12671_bounds.2]
  · change Chebyshev.theta (↑(12790 : ℕ) : ℝ) ≤ (12795497 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 12790
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 12781) (b := 12790) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta12035_psi_12781_bounds.2]
  · change Chebyshev.theta (↑(12899 : ℕ) : ℝ) ≤ (12899470 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 12899
    linarith only [hd, theta12035_psi_12899_bounds.2]
  · change Chebyshev.theta (↑(12994 : ℕ) : ℝ) ≤ (13013146 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 12994
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 12983) (b := 12994) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta12035_psi_12983_bounds.2]

/-- The envelope bound applies at every cell a endpoint. -/
theorem theta12035_a :
    ∀ r ∈ theta12035Cells,
      (r.ca : ℝ) / 1000 ≤
        Real.sqrt r.a *
          (Real.log r.a * (Real.log r.a - Real.log (Real.log r.a)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta12035Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 12035 *
          (Real.log 12035 * (Real.log 12035 - Real.log (Real.log 12035)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 12091 *
          (Real.log 12091 * (Real.log 12091 - Real.log (Real.log 12091)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 12147 *
          (Real.log 12147 * (Real.log 12147 - Real.log (Real.log 12147)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 12213 *
          (Real.log 12213 * (Real.log 12213 - Real.log (Real.log 12213)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 12283 *
          (Real.log 12283 * (Real.log 12283 - Real.log (Real.log 12283)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 12367 *
          (Real.log 12367 * (Real.log 12367 - Real.log (Real.log 12367)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 12424 *
          (Real.log 12424 * (Real.log 12424 - Real.log (Real.log 12424)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 12499 *
          (Real.log 12499 * (Real.log 12499 - Real.log (Real.log 12499)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 12584 *
          (Real.log 12584 * (Real.log 12584 - Real.log (Real.log 12584)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 12688 *
          (Real.log 12688 * (Real.log 12688 - Real.log (Real.log 12688)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 12791 *
          (Real.log 12791 * (Real.log 12791 - Real.log (Real.log 12791)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 12900 *
          (Real.log 12900 * (Real.log 12900 - Real.log (Real.log 12900)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)

/-- The envelope bound applies at every cell b endpoint. -/
theorem theta12035_b :
    ∀ r ∈ theta12035Cells,
      (r.cb : ℝ) / 1000 ≤
        Real.sqrt r.b *
          (Real.log r.b * (Real.log r.b - Real.log (Real.log r.b)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta12035Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 12091 *
          (Real.log 12091 * (Real.log 12091 - Real.log (Real.log 12091)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 12147 *
          (Real.log 12147 * (Real.log 12147 - Real.log (Real.log 12147)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 12213 *
          (Real.log 12213 * (Real.log 12213 - Real.log (Real.log 12213)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 12283 *
          (Real.log 12283 * (Real.log 12283 - Real.log (Real.log 12283)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 12367 *
          (Real.log 12367 * (Real.log 12367 - Real.log (Real.log 12367)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 12424 *
          (Real.log 12424 * (Real.log 12424 - Real.log (Real.log 12424)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 12499 *
          (Real.log 12499 * (Real.log 12499 - Real.log (Real.log 12499)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 12584 *
          (Real.log 12584 * (Real.log 12584 - Real.log (Real.log 12584)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 12688 *
          (Real.log 12688 * (Real.log 12688 - Real.log (Real.log 12688)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 12791 *
          (Real.log 12791 * (Real.log 12791 - Real.log (Real.log 12791)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 12900 *
          (Real.log 12900 * (Real.log 12900 - Real.log (Real.log 12900)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 12995 *
          (Real.log 12995 * (Real.log 12995 - Real.log (Real.log 12995)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)

/-- The cells form a checked chain covering `[12035, 12995)`. -/
theorem theta12035_check : leeNosalChainCheck 12035 12995 theta12035Cells = true := by
  decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
