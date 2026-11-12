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
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalLogCheck
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalMonotone
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalChecker

/-! # Batch certificate for Lee–Nosal psi cells -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The local cells store endpoint bounds in thousandths. -/
private def batchCells : List LeeNosalCell :=
  [⟨6138, 6301, 6135738, 6306947, 175000, 175000⟩, ⟨6301, 6469, 6315263, 6473302, 175000, 175000⟩,
    ⟨6469, 6656, 6481619, 6641737, 175000, 175000⟩, ⟨6656, 6816, 6641043, 6808785, 175000, 175000⟩,
    ⟨6816, 6971, 6808091, 6984151, 175000, 175000⟩, ⟨6971, 7129, 6992468, 7143575, 175000, 175000⟩,
    ⟨7129, 7309, 7151892, 7303692, 175000, 175000⟩, ⟨7309, 7487, 7312009, 7445788, 175000, 175000⟩,
    ⟨7487, 7629, 7454104, 7633630, 175000, 175000⟩, ⟨7629, 7807, 7632936, 7803451, 175000, 175000⟩,
    ⟨7807, 7977, 7802757, 7978818, 175000, 175000⟩, ⟨7977, 8153, 7978124, 8131310, 175000, 175000⟩,
    ⟨8153, 8305, 8130616, 8303904, 175000, 175000⟩]

/-- The kernel-checked prefix bounds for 6133. -/
private theorem psi_6133_bounds :
    (6135738 : ℝ) / 1000 ≤ Chebyshev.psi 6133 ∧ Chebyshev.psi 6133 ≤ (6136432 : ℝ) / 1000 := by
  have hl : 2 ^ 8852 ≤ Nat.lcmUpto 6133 := by decide +kernel
  have hu : Nat.lcmUpto 6133 ≤ 2 ^ (8852 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 6299. -/
private theorem psi_6299_bounds :
    (6306253 : ℝ) / 1000 ≤ Chebyshev.psi 6299 ∧ Chebyshev.psi 6299 ≤ (6306947 : ℝ) / 1000 := by
  have hl : 2 ^ 9098 ≤ Nat.lcmUpto 6299 := by decide +kernel
  have hu : Nat.lcmUpto 6299 ≤ 2 ^ (9098 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 6301. -/
private theorem psi_6301_bounds :
    (6315263 : ℝ) / 1000 ≤ Chebyshev.psi 6301 ∧ Chebyshev.psi 6301 ≤ (6315958 : ℝ) / 1000 := by
  have hl : 2 ^ 9111 ≤ Nat.lcmUpto 6301 := by decide +kernel
  have hu : Nat.lcmUpto 6301 ≤ 2 ^ (9111 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 6451. -/
private theorem psi_6451_bounds :
    (6472608 : ℝ) / 1000 ≤ Chebyshev.psi 6451 ∧ Chebyshev.psi 6451 ≤ (6473302 : ℝ) / 1000 := by
  have hl : 2 ^ 9338 ≤ Nat.lcmUpto 6451 := by decide +kernel
  have hu : Nat.lcmUpto 6451 ≤ 2 ^ (9338 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 6469. -/
private theorem psi_6469_bounds :
    (6481619 : ℝ) / 1000 ≤ Chebyshev.psi 6469 ∧ Chebyshev.psi 6469 ≤ (6482313 : ℝ) / 1000 := by
  have hl : 2 ^ 9351 ≤ Nat.lcmUpto 6469 := by decide +kernel
  have hu : Nat.lcmUpto 6469 ≤ 2 ^ (9351 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 6653. -/
private theorem psi_6653_bounds :
    (6641043 : ℝ) / 1000 ≤ Chebyshev.psi 6653 ∧ Chebyshev.psi 6653 ≤ (6641737 : ℝ) / 1000 := by
  have hl : 2 ^ 9581 ≤ Nat.lcmUpto 6653 := by decide +kernel
  have hu : Nat.lcmUpto 6653 ≤ 2 ^ (9581 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 6803. -/
private theorem psi_6803_bounds :
    (6808091 : ℝ) / 1000 ≤ Chebyshev.psi 6803 ∧ Chebyshev.psi 6803 ≤ (6808785 : ℝ) / 1000 := by
  have hl : 2 ^ 9822 ≤ Nat.lcmUpto 6803 := by decide +kernel
  have hu : Nat.lcmUpto 6803 ≤ 2 ^ (9822 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 6967. -/
private theorem psi_6967_bounds :
    (6983457 : ℝ) / 1000 ≤ Chebyshev.psi 6967 ∧ Chebyshev.psi 6967 ≤ (6984151 : ℝ) / 1000 := by
  have hl : 2 ^ 10075 ≤ Nat.lcmUpto 6967 := by decide +kernel
  have hu : Nat.lcmUpto 6967 ≤ 2 ^ (10075 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 6971. -/
private theorem psi_6971_bounds :
    (6992468 : ℝ) / 1000 ≤ Chebyshev.psi 6971 ∧ Chebyshev.psi 6971 ≤ (6993162 : ℝ) / 1000 := by
  have hl : 2 ^ 10088 ≤ Nat.lcmUpto 6971 := by decide +kernel
  have hu : Nat.lcmUpto 6971 ≤ 2 ^ (10088 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 7127. -/
private theorem psi_7127_bounds :
    (7142881 : ℝ) / 1000 ≤ Chebyshev.psi 7127 ∧ Chebyshev.psi 7127 ≤ (7143575 : ℝ) / 1000 := by
  have hl : 2 ^ 10305 ≤ Nat.lcmUpto 7127 := by decide +kernel
  have hu : Nat.lcmUpto 7127 ≤ 2 ^ (10305 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 7129. -/
private theorem psi_7129_bounds :
    (7151892 : ℝ) / 1000 ≤ Chebyshev.psi 7129 ∧ Chebyshev.psi 7129 ≤ (7152586 : ℝ) / 1000 := by
  have hl : 2 ^ 10318 ≤ Nat.lcmUpto 7129 := by decide +kernel
  have hu : Nat.lcmUpto 7129 ≤ 2 ^ (10318 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 7307. -/
private theorem psi_7307_bounds :
    (7302998 : ℝ) / 1000 ≤ Chebyshev.psi 7307 ∧ Chebyshev.psi 7307 ≤ (7303692 : ℝ) / 1000 := by
  have hl : 2 ^ 10536 ≤ Nat.lcmUpto 7307 := by decide +kernel
  have hu : Nat.lcmUpto 7307 ≤ 2 ^ (10536 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 7309. -/
private theorem psi_7309_bounds :
    (7312009 : ℝ) / 1000 ≤ Chebyshev.psi 7309 ∧ Chebyshev.psi 7309 ≤ (7312703 : ℝ) / 1000 := by
  have hl : 2 ^ 10549 ≤ Nat.lcmUpto 7309 := by decide +kernel
  have hu : Nat.lcmUpto 7309 ≤ 2 ^ (10549 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 7481. -/
private theorem psi_7481_bounds :
    (7445093 : ℝ) / 1000 ≤ Chebyshev.psi 7481 ∧ Chebyshev.psi 7481 ≤ (7445788 : ℝ) / 1000 := by
  have hl : 2 ^ 10741 ≤ Nat.lcmUpto 7481 := by decide +kernel
  have hu : Nat.lcmUpto 7481 ≤ 2 ^ (10741 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 7487. -/
private theorem psi_7487_bounds :
    (7454104 : ℝ) / 1000 ≤ Chebyshev.psi 7487 ∧ Chebyshev.psi 7487 ≤ (7454798 : ℝ) / 1000 := by
  have hl : 2 ^ 10754 ≤ Nat.lcmUpto 7487 := by decide +kernel
  have hu : Nat.lcmUpto 7487 ≤ 2 ^ (10754 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 7621. -/
private theorem psi_7621_bounds :
    (7632936 : ℝ) / 1000 ≤ Chebyshev.psi 7621 ∧ Chebyshev.psi 7621 ≤ (7633630 : ℝ) / 1000 := by
  have hl : 2 ^ 11012 ≤ Nat.lcmUpto 7621 := by decide +kernel
  have hu : Nat.lcmUpto 7621 ≤ 2 ^ (11012 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 7793. -/
private theorem psi_7793_bounds :
    (7802757 : ℝ) / 1000 ≤ Chebyshev.psi 7793 ∧ Chebyshev.psi 7793 ≤ (7803451 : ℝ) / 1000 := by
  have hl : 2 ^ 11257 ≤ Nat.lcmUpto 7793 := by decide +kernel
  have hu : Nat.lcmUpto 7793 ≤ 2 ^ (11257 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 7963. -/
private theorem psi_7963_bounds :
    (7978124 : ℝ) / 1000 ≤ Chebyshev.psi 7963 ∧ Chebyshev.psi 7963 ≤ (7978818 : ℝ) / 1000 := by
  have hl : 2 ^ 11510 ≤ Nat.lcmUpto 7963 := by decide +kernel
  have hu : Nat.lcmUpto 7963 ≤ 2 ^ (11510 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 8147. -/
private theorem psi_8147_bounds :
    (8130616 : ℝ) / 1000 ≤ Chebyshev.psi 8147 ∧ Chebyshev.psi 8147 ≤ (8131310 : ℝ) / 1000 := by
  have hl : 2 ^ 11730 ≤ Nat.lcmUpto 8147 := by decide +kernel
  have hu : Nat.lcmUpto 8147 ≤ 2 ^ (11730 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 8297. -/
private theorem psi_8297_bounds :
    (8303210 : ℝ) / 1000 ≤ Chebyshev.psi 8297 ∧ Chebyshev.psi 8297 ≤ (8303904 : ℝ) / 1000 := by
  have hl : 2 ^ 11979 ≤ Nat.lcmUpto 8297 := by decide +kernel
  have hu : Nat.lcmUpto 8297 ≤ 2 ^ (11979 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- A rational certificate bounds the envelope from 6138 onward. -/
private theorem batch_envelope {t : ℝ} (ht : 6138 ≤ t) :
    (175 : ℝ) ≤
      Real.sqrt t * (Real.log t * (Real.log t - Real.log (Real.log t)) / (8 * Real.pi)) := by
  have h :=
    lee_nosal_envelope_of_log_checks (N := 6138) (lo := 872 / 100) (hi := 873 / 100) (vlo :=
      216 / 100) (vhi := 217 / 100) (c := 175) (j := 13) (k := 4) (n := 32) (m := 32)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by decide +kernel) (by decide +kernel) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact
    h.trans
      (lee_nosal_envelope_mono (x := 6138) (y := t)
        (Real.exp_one_lt_three.le.trans (by norm_num only)) ht)

/-- Every batch cell has a checked psi lower bound. -/
private theorem batch_lower : ∀ r ∈ batchCells, (r.lo : ℝ) / 1000 ≤ Chebyshev.psi r.a := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (6135738 : ℝ) / 1000 ≤ Chebyshev.psi (↑(6138 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 6133) (b := 6138) (by decide) (by decide +kernel)]
    exact psi_6133_bounds.1
  · change (6315263 : ℝ) / 1000 ≤ Chebyshev.psi (↑(6301 : ℕ) : ℝ)
    exact psi_6301_bounds.1
  · change (6481619 : ℝ) / 1000 ≤ Chebyshev.psi (↑(6469 : ℕ) : ℝ)
    exact psi_6469_bounds.1
  · change (6641043 : ℝ) / 1000 ≤ Chebyshev.psi (↑(6656 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 6653) (b := 6656) (by decide) (by decide +kernel)]
    exact psi_6653_bounds.1
  · change (6808091 : ℝ) / 1000 ≤ Chebyshev.psi (↑(6816 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 6803) (b := 6816) (by decide) (by decide +kernel)]
    exact psi_6803_bounds.1
  · change (6992468 : ℝ) / 1000 ≤ Chebyshev.psi (↑(6971 : ℕ) : ℝ)
    exact psi_6971_bounds.1
  · change (7151892 : ℝ) / 1000 ≤ Chebyshev.psi (↑(7129 : ℕ) : ℝ)
    exact psi_7129_bounds.1
  · change (7312009 : ℝ) / 1000 ≤ Chebyshev.psi (↑(7309 : ℕ) : ℝ)
    exact psi_7309_bounds.1
  · change (7454104 : ℝ) / 1000 ≤ Chebyshev.psi (↑(7487 : ℕ) : ℝ)
    exact psi_7487_bounds.1
  · change (7632936 : ℝ) / 1000 ≤ Chebyshev.psi (↑(7629 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 7621) (b := 7629) (by decide) (by decide +kernel)]
    exact psi_7621_bounds.1
  · change (7802757 : ℝ) / 1000 ≤ Chebyshev.psi (↑(7807 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 7793) (b := 7807) (by decide) (by decide +kernel)]
    exact psi_7793_bounds.1
  · change (7978124 : ℝ) / 1000 ≤ Chebyshev.psi (↑(7977 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 7963) (b := 7977) (by decide) (by decide +kernel)]
    exact psi_7963_bounds.1
  · change (8130616 : ℝ) / 1000 ≤ Chebyshev.psi (↑(8153 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 8147) (b := 8153) (by decide) (by decide +kernel)]
    exact psi_8147_bounds.1

/-- Every batch cell has a checked psi upper bound. -/
private theorem batch_upper :
    ∀ r ∈ batchCells, Chebyshev.psi (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Chebyshev.psi (↑(6300 : ℕ) : ℝ) ≤ (6306947 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 6299) (b := 6300) (by decide) (by decide +kernel)]
    exact psi_6299_bounds.2
  · change Chebyshev.psi (↑(6468 : ℕ) : ℝ) ≤ (6473302 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 6451) (b := 6468) (by decide) (by decide +kernel)]
    exact psi_6451_bounds.2
  · change Chebyshev.psi (↑(6655 : ℕ) : ℝ) ≤ (6641737 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 6653) (b := 6655) (by decide) (by decide +kernel)]
    exact psi_6653_bounds.2
  · change Chebyshev.psi (↑(6815 : ℕ) : ℝ) ≤ (6808785 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 6803) (b := 6815) (by decide) (by decide +kernel)]
    exact psi_6803_bounds.2
  · change Chebyshev.psi (↑(6970 : ℕ) : ℝ) ≤ (6984151 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 6967) (b := 6970) (by decide) (by decide +kernel)]
    exact psi_6967_bounds.2
  · change Chebyshev.psi (↑(7128 : ℕ) : ℝ) ≤ (7143575 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 7127) (b := 7128) (by decide) (by decide +kernel)]
    exact psi_7127_bounds.2
  · change Chebyshev.psi (↑(7308 : ℕ) : ℝ) ≤ (7303692 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 7307) (b := 7308) (by decide) (by decide +kernel)]
    exact psi_7307_bounds.2
  · change Chebyshev.psi (↑(7486 : ℕ) : ℝ) ≤ (7445788 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 7481) (b := 7486) (by decide) (by decide +kernel)]
    exact psi_7481_bounds.2
  · change Chebyshev.psi (↑(7628 : ℕ) : ℝ) ≤ (7633630 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 7621) (b := 7628) (by decide) (by decide +kernel)]
    exact psi_7621_bounds.2
  · change Chebyshev.psi (↑(7806 : ℕ) : ℝ) ≤ (7803451 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 7793) (b := 7806) (by decide) (by decide +kernel)]
    exact psi_7793_bounds.2
  · change Chebyshev.psi (↑(7976 : ℕ) : ℝ) ≤ (7978818 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 7963) (b := 7976) (by decide) (by decide +kernel)]
    exact psi_7963_bounds.2
  · change Chebyshev.psi (↑(8152 : ℕ) : ℝ) ≤ (8131310 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 8147) (b := 8152) (by decide) (by decide +kernel)]
    exact psi_8147_bounds.2
  · change Chebyshev.psi (↑(8304 : ℕ) : ℝ) ≤ (8303904 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 8297) (b := 8304) (by decide) (by decide +kernel)]
    exact psi_8297_bounds.2

/-- The envelope bound applies at every cell a endpoint. -/
private theorem batch_a :
    ∀ r ∈ batchCells,
      (r.ca : ℝ) / 1000 ≤
        Real.sqrt r.a *
          (Real.log r.a * (Real.log r.a - Real.log (Real.log r.a)) / (8 * Real.pi)) := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (175000 : ℝ) / 1000 ≤
        Real.sqrt 6138 *
          (Real.log 6138 * (Real.log 6138 - Real.log (Real.log 6138)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (175000 : ℝ) / 1000 ≤
        Real.sqrt 6301 *
          (Real.log 6301 * (Real.log 6301 - Real.log (Real.log 6301)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (175000 : ℝ) / 1000 ≤
        Real.sqrt 6469 *
          (Real.log 6469 * (Real.log 6469 - Real.log (Real.log 6469)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (175000 : ℝ) / 1000 ≤
        Real.sqrt 6656 *
          (Real.log 6656 * (Real.log 6656 - Real.log (Real.log 6656)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (175000 : ℝ) / 1000 ≤
        Real.sqrt 6816 *
          (Real.log 6816 * (Real.log 6816 - Real.log (Real.log 6816)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (175000 : ℝ) / 1000 ≤
        Real.sqrt 6971 *
          (Real.log 6971 * (Real.log 6971 - Real.log (Real.log 6971)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (175000 : ℝ) / 1000 ≤
        Real.sqrt 7129 *
          (Real.log 7129 * (Real.log 7129 - Real.log (Real.log 7129)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (175000 : ℝ) / 1000 ≤
        Real.sqrt 7309 *
          (Real.log 7309 * (Real.log 7309 - Real.log (Real.log 7309)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (175000 : ℝ) / 1000 ≤
        Real.sqrt 7487 *
          (Real.log 7487 * (Real.log 7487 - Real.log (Real.log 7487)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (175000 : ℝ) / 1000 ≤
        Real.sqrt 7629 *
          (Real.log 7629 * (Real.log 7629 - Real.log (Real.log 7629)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (175000 : ℝ) / 1000 ≤
        Real.sqrt 7807 *
          (Real.log 7807 * (Real.log 7807 - Real.log (Real.log 7807)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (175000 : ℝ) / 1000 ≤
        Real.sqrt 7977 *
          (Real.log 7977 * (Real.log 7977 - Real.log (Real.log 7977)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (175000 : ℝ) / 1000 ≤
        Real.sqrt 8153 *
          (Real.log 8153 * (Real.log 8153 - Real.log (Real.log 8153)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)

/-- The envelope bound applies at every cell b endpoint. -/
private theorem batch_b :
    ∀ r ∈ batchCells,
      (r.cb : ℝ) / 1000 ≤
        Real.sqrt r.b *
          (Real.log r.b * (Real.log r.b - Real.log (Real.log r.b)) / (8 * Real.pi)) := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (175000 : ℝ) / 1000 ≤
        Real.sqrt 6301 *
          (Real.log 6301 * (Real.log 6301 - Real.log (Real.log 6301)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (175000 : ℝ) / 1000 ≤
        Real.sqrt 6469 *
          (Real.log 6469 * (Real.log 6469 - Real.log (Real.log 6469)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (175000 : ℝ) / 1000 ≤
        Real.sqrt 6656 *
          (Real.log 6656 * (Real.log 6656 - Real.log (Real.log 6656)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (175000 : ℝ) / 1000 ≤
        Real.sqrt 6816 *
          (Real.log 6816 * (Real.log 6816 - Real.log (Real.log 6816)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (175000 : ℝ) / 1000 ≤
        Real.sqrt 6971 *
          (Real.log 6971 * (Real.log 6971 - Real.log (Real.log 6971)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (175000 : ℝ) / 1000 ≤
        Real.sqrt 7129 *
          (Real.log 7129 * (Real.log 7129 - Real.log (Real.log 7129)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (175000 : ℝ) / 1000 ≤
        Real.sqrt 7309 *
          (Real.log 7309 * (Real.log 7309 - Real.log (Real.log 7309)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (175000 : ℝ) / 1000 ≤
        Real.sqrt 7487 *
          (Real.log 7487 * (Real.log 7487 - Real.log (Real.log 7487)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (175000 : ℝ) / 1000 ≤
        Real.sqrt 7629 *
          (Real.log 7629 * (Real.log 7629 - Real.log (Real.log 7629)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (175000 : ℝ) / 1000 ≤
        Real.sqrt 7807 *
          (Real.log 7807 * (Real.log 7807 - Real.log (Real.log 7807)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (175000 : ℝ) / 1000 ≤
        Real.sqrt 7977 *
          (Real.log 7977 * (Real.log 7977 - Real.log (Real.log 7977)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (175000 : ℝ) / 1000 ≤
        Real.sqrt 8153 *
          (Real.log 8153 * (Real.log 8153 - Real.log (Real.log 8153)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (175000 : ℝ) / 1000 ≤
        Real.sqrt 8305 *
          (Real.log 8305 * (Real.log 8305 - Real.log (Real.log 8305)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)

/-- The checked batch proves the Lee–Nosal psi estimate on `[6138, 8305)`. -/
theorem psi_lee_nosal_6138_8305 {x : ℝ} (ha : 6138 ≤ x) (hb : x < 8305) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    lee_nosal_chain_sound Chebyshev.psi_mono Chebyshev.psi_eq_psi_coe_floor (by decide +kernel)
      batch_lower batch_upper batch_a batch_b ha hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
