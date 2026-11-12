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
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSmallDefect7776
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalEnvelope5625
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalMonotone
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalChecker

/-! # Batch certificate for Lee–Nosal theta cells -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The local cells store endpoint bounds in thousandths. -/
def theta6824Cells : List LeeNosalCell :=
  [⟨6824, 6868, 6703422, 6873941, 165000, 165000⟩, ⟨6868, 6924, 6759567, 6939790, 165000, 165000⟩,
    ⟨6924, 6990, 6825416, 7010491, 165000, 165000⟩, ⟨6990, 7061, 6896117, 7090203, 165000, 165000⟩,
    ⟨7061, 7140, 6975829, 7152586, 165000, 165000⟩, ⟨7140, 7203, 7038212, 7196948, 165000, 165000⟩,
    ⟨7203, 7247, 7082574, 7259331, 165000, 165000⟩, ⟨7247, 7318, 7153275, 7312703, 165000, 165000⟩]

/-- The kernel-checked prefix bounds for 6823. -/
theorem theta6824_psi_6823_bounds :
    (6817102 : ℝ) / 1000 ≤ Chebyshev.psi 6823 ∧ Chebyshev.psi 6823 ≤ (6817796 : ℝ) / 1000 := by
  have hl : 2 ^ 9835 ≤ Nat.lcmUpto 6823 := by decide +kernel
  have hu : Nat.lcmUpto 6823 ≤ 2 ^ (9835 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 6863. -/
theorem theta6824_psi_6863_bounds :
    (6873247 : ℝ) / 1000 ≤ Chebyshev.psi 6863 ∧ Chebyshev.psi 6863 ≤ (6873941 : ℝ) / 1000 := by
  have hl : 2 ^ 9916 ≤ Nat.lcmUpto 6863 := by decide +kernel
  have hu : Nat.lcmUpto 6863 ≤ 2 ^ (9916 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 6917. -/
theorem theta6824_psi_6917_bounds :
    (6939096 : ℝ) / 1000 ≤ Chebyshev.psi 6917 ∧ Chebyshev.psi 6917 ≤ (6939790 : ℝ) / 1000 := by
  have hl : 2 ^ 10011 ≤ Nat.lcmUpto 6917 := by decide +kernel
  have hu : Nat.lcmUpto 6917 ≤ 2 ^ (10011 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 6983. -/
theorem theta6824_psi_6983_bounds :
    (7009797 : ℝ) / 1000 ≤ Chebyshev.psi 6983 ∧ Chebyshev.psi 6983 ≤ (7010491 : ℝ) / 1000 := by
  have hl : 2 ^ 10113 ≤ Nat.lcmUpto 6983 := by decide +kernel
  have hu : Nat.lcmUpto 6983 ≤ 2 ^ (10113 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 7057. -/
theorem theta6824_psi_7057_bounds :
    (7089509 : ℝ) / 1000 ≤ Chebyshev.psi 7057 ∧ Chebyshev.psi 7057 ≤ (7090203 : ℝ) / 1000 := by
  have hl : 2 ^ 10228 ≤ Nat.lcmUpto 7057 := by decide +kernel
  have hu : Nat.lcmUpto 7057 ≤ 2 ^ (10228 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 7129. -/
theorem theta6824_psi_7129_bounds :
    (7151892 : ℝ) / 1000 ≤ Chebyshev.psi 7129 ∧ Chebyshev.psi 7129 ≤ (7152586 : ℝ) / 1000 := by
  have hl : 2 ^ 10318 ≤ Nat.lcmUpto 7129 := by decide +kernel
  have hu : Nat.lcmUpto 7129 ≤ 2 ^ (10318 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 7193. -/
theorem theta6824_psi_7193_bounds :
    (7196254 : ℝ) / 1000 ≤ Chebyshev.psi 7193 ∧ Chebyshev.psi 7193 ≤ (7196948 : ℝ) / 1000 := by
  have hl : 2 ^ 10382 ≤ Nat.lcmUpto 7193 := by decide +kernel
  have hu : Nat.lcmUpto 7193 ≤ 2 ^ (10382 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 7243. -/
theorem theta6824_psi_7243_bounds :
    (7258637 : ℝ) / 1000 ≤ Chebyshev.psi 7243 ∧ Chebyshev.psi 7243 ≤ (7259331 : ℝ) / 1000 := by
  have hl : 2 ^ 10472 ≤ Nat.lcmUpto 7243 := by decide +kernel
  have hu : Nat.lcmUpto 7243 ≤ 2 ^ (10472 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 7247. -/
theorem theta6824_psi_7247_bounds :
    (7266955 : ℝ) / 1000 ≤ Chebyshev.psi 7247 ∧ Chebyshev.psi 7247 ≤ (7267649 : ℝ) / 1000 := by
  have hl : 2 ^ 10484 ≤ Nat.lcmUpto 7247 := by decide +kernel
  have hu : Nat.lcmUpto 7247 ≤ 2 ^ (10484 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 7309. -/
theorem theta6824_psi_7309_bounds :
    (7312009 : ℝ) / 1000 ≤ Chebyshev.psi 7309 ∧ Chebyshev.psi 7309 ≤ (7312703 : ℝ) / 1000 := by
  have hl : 2 ^ 10549 ≤ Nat.lcmUpto 7309 := by decide +kernel
  have hu : Nat.lcmUpto 7309 ≤ 2 ^ (10549 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- Every batch cell has a checked theta lower bound. -/
theorem theta6824_lower : ∀ r ∈ theta6824Cells, (r.lo : ℝ) / 1000 ≤ Chebyshev.theta r.a := by
  intro r hr
  simp only [theta6824Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (6703422 : ℝ) / 1000 ≤ Chebyshev.theta (↑(6824 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_11368 (x := 6824) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 6823) (b := 6824) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta6824_psi_6823_bounds.1]
  · change (6759567 : ℝ) / 1000 ≤ Chebyshev.theta (↑(6868 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_11368 (x := 6868) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 6863) (b := 6868) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta6824_psi_6863_bounds.1]
  · change (6825416 : ℝ) / 1000 ≤ Chebyshev.theta (↑(6924 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_11368 (x := 6924) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 6917) (b := 6924) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta6824_psi_6917_bounds.1]
  · change (6896117 : ℝ) / 1000 ≤ Chebyshev.theta (↑(6990 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_11368 (x := 6990) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 6983) (b := 6990) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta6824_psi_6983_bounds.1]
  · change (6975829 : ℝ) / 1000 ≤ Chebyshev.theta (↑(7061 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_11368 (x := 7061) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 7057) (b := 7061) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta6824_psi_7057_bounds.1]
  · change (7038212 : ℝ) / 1000 ≤ Chebyshev.theta (↑(7140 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_11368 (x := 7140) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 7129) (b := 7140) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta6824_psi_7129_bounds.1]
  · change (7082574 : ℝ) / 1000 ≤ Chebyshev.theta (↑(7203 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_11368 (x := 7203) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 7193) (b := 7203) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta6824_psi_7193_bounds.1]
  · change (7153275 : ℝ) / 1000 ≤ Chebyshev.theta (↑(7247 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_11368 (x := 7247) (by norm_num only) (by norm_num only)
    linarith only [hd, theta6824_psi_7247_bounds.1]

/-- Every batch cell has a checked theta upper bound. -/
theorem theta6824_upper :
    ∀ r ∈ theta6824Cells, Chebyshev.theta (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [theta6824Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Chebyshev.theta (↑(6867 : ℕ) : ℝ) ≤ (6873941 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 6867
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 6863) (b := 6867) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta6824_psi_6863_bounds.2]
  · change Chebyshev.theta (↑(6923 : ℕ) : ℝ) ≤ (6939790 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 6923
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 6917) (b := 6923) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta6824_psi_6917_bounds.2]
  · change Chebyshev.theta (↑(6989 : ℕ) : ℝ) ≤ (7010491 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 6989
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 6983) (b := 6989) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta6824_psi_6983_bounds.2]
  · change Chebyshev.theta (↑(7060 : ℕ) : ℝ) ≤ (7090203 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 7060
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 7057) (b := 7060) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta6824_psi_7057_bounds.2]
  · change Chebyshev.theta (↑(7139 : ℕ) : ℝ) ≤ (7152586 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 7139
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 7129) (b := 7139) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta6824_psi_7129_bounds.2]
  · change Chebyshev.theta (↑(7202 : ℕ) : ℝ) ≤ (7196948 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 7202
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 7193) (b := 7202) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta6824_psi_7193_bounds.2]
  · change Chebyshev.theta (↑(7246 : ℕ) : ℝ) ≤ (7259331 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 7246
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 7243) (b := 7246) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta6824_psi_7243_bounds.2]
  · change Chebyshev.theta (↑(7317 : ℕ) : ℝ) ≤ (7312703 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 7317
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 7309) (b := 7317) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta6824_psi_7309_bounds.2]

/-- The envelope bound applies at every cell a endpoint. -/
theorem theta6824_a :
    ∀ r ∈ theta6824Cells,
      (r.ca : ℝ) / 1000 ≤
        Real.sqrt r.a *
          (Real.log r.a * (Real.log r.a - Real.log (Real.log r.a)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta6824Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 6824 *
          (Real.log 6824 * (Real.log 6824 - Real.log (Real.log 6824)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 6868 *
          (Real.log 6868 * (Real.log 6868 - Real.log (Real.log 6868)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 6924 *
          (Real.log 6924 * (Real.log 6924 - Real.log (Real.log 6924)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 6990 *
          (Real.log 6990 * (Real.log 6990 - Real.log (Real.log 6990)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 7061 *
          (Real.log 7061 * (Real.log 7061 - Real.log (Real.log 7061)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 7140 *
          (Real.log 7140 * (Real.log 7140 - Real.log (Real.log 7140)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 7203 *
          (Real.log 7203 * (Real.log 7203 - Real.log (Real.log 7203)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 7247 *
          (Real.log 7247 * (Real.log 7247 - Real.log (Real.log 7247)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)

/-- The envelope bound applies at every cell b endpoint. -/
theorem theta6824_b :
    ∀ r ∈ theta6824Cells,
      (r.cb : ℝ) / 1000 ≤
        Real.sqrt r.b *
          (Real.log r.b * (Real.log r.b - Real.log (Real.log r.b)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta6824Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 6868 *
          (Real.log 6868 * (Real.log 6868 - Real.log (Real.log 6868)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 6924 *
          (Real.log 6924 * (Real.log 6924 - Real.log (Real.log 6924)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 6990 *
          (Real.log 6990 * (Real.log 6990 - Real.log (Real.log 6990)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 7061 *
          (Real.log 7061 * (Real.log 7061 - Real.log (Real.log 7061)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 7140 *
          (Real.log 7140 * (Real.log 7140 - Real.log (Real.log 7140)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 7203 *
          (Real.log 7203 * (Real.log 7203 - Real.log (Real.log 7203)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 7247 *
          (Real.log 7247 * (Real.log 7247 - Real.log (Real.log 7247)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 7318 *
          (Real.log 7318 * (Real.log 7318 - Real.log (Real.log 7318)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)

/-- The cells form a checked chain covering `[6824, 7318)`. -/
theorem theta6824_check : leeNosalChainCheck 6824 7318 theta6824Cells = true := by decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
