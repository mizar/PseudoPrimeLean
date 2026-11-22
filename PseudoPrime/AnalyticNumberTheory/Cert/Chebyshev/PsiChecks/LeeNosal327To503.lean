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
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiChecks.LeeNosal219To327

/-! # Batch certificate for Lee–Nosal psi cells -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiChecks

/-- The local cells store endpoint bounds in thousandths. -/
private def batchCells : List RiemannZeta.LeeNosalCell :=
  [⟨327, 337, 321620, 328552, 16000, 16000⟩, ⟨337, 349, 333403, 341722, 16000, 16000⟩,
    ⟨349, 363, 347266, 362516, 16000, 16000⟩, ⟨363, 377, 361822, 374300, 16000, 16000⟩,
    ⟨377, 389, 373606, 386083, 16000, 16000⟩, ⟨389, 407, 391628, 404105, 16000, 16000⟩,
    ⟨407, 419, 403411, 410344, 16000, 16000⟩, ⟨419, 431, 415195, 422127, 16000, 16000⟩,
    ⟨431, 443, 427671, 440149, 16000, 16000⟩, ⟨443, 461, 445693, 458864, 16000, 16000⟩,
    ⟨461, 479, 464408, 476886, 16000, 16000⟩, ⟨479, 491, 482430, 489362, 16000, 16000⟩,
    ⟨491, 503, 494907, 501839, 16000, 16000⟩]

/-- The kernel-checked prefix bounds for 317. -/
private theorem psi_317_bounds :
    (321620 : ℝ) / 1000 ≤ Chebyshev.psi 317 ∧ Chebyshev.psi 317 ≤ (322314 : ℝ) / 1000 := by
  have hl : 2 ^ 464 ≤ Nat.lcmUpto 317 := by decide +kernel
  have hu : Nat.lcmUpto 317 ≤ 2 ^ (464 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 331. -/
private theorem psi_331_bounds :
    (327858 : ℝ) / 1000 ≤ Chebyshev.psi 331 ∧ Chebyshev.psi 331 ≤ (328552 : ℝ) / 1000 := by
  have hl : 2 ^ 473 ≤ Nat.lcmUpto 331 := by decide +kernel
  have hu : Nat.lcmUpto 331 ≤ 2 ^ (473 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 337. -/
private theorem psi_337_bounds :
    (333403 : ℝ) / 1000 ≤ Chebyshev.psi 337 ∧ Chebyshev.psi 337 ≤ (334097 : ℝ) / 1000 := by
  have hl : 2 ^ 481 ≤ Nat.lcmUpto 337 := by decide +kernel
  have hu : Nat.lcmUpto 337 ≤ 2 ^ (481 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 347. -/
private theorem psi_347_bounds :
    (341028 : ℝ) / 1000 ≤ Chebyshev.psi 347 ∧ Chebyshev.psi 347 ≤ (341722 : ℝ) / 1000 := by
  have hl : 2 ^ 492 ≤ Nat.lcmUpto 347 := by decide +kernel
  have hu : Nat.lcmUpto 347 ≤ 2 ^ (492 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 349. -/
private theorem psi_349_bounds :
    (347266 : ℝ) / 1000 ≤ Chebyshev.psi 349 ∧ Chebyshev.psi 349 ≤ (347960 : ℝ) / 1000 := by
  have hl : 2 ^ 501 ≤ Nat.lcmUpto 349 := by decide +kernel
  have hu : Nat.lcmUpto 349 ≤ 2 ^ (501 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 361. -/
private theorem psi_361_bounds :
    (361822 : ℝ) / 1000 ≤ Chebyshev.psi 361 ∧ Chebyshev.psi 361 ≤ (362516 : ℝ) / 1000 := by
  have hl : 2 ^ 522 ≤ Nat.lcmUpto 361 := by decide +kernel
  have hu : Nat.lcmUpto 361 ≤ 2 ^ (522 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 373. -/
private theorem psi_373_bounds :
    (373606 : ℝ) / 1000 ≤ Chebyshev.psi 373 ∧ Chebyshev.psi 373 ≤ (374300 : ℝ) / 1000 := by
  have hl : 2 ^ 539 ≤ Nat.lcmUpto 373 := by decide +kernel
  have hu : Nat.lcmUpto 373 ≤ 2 ^ (539 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 383. -/
private theorem psi_383_bounds :
    (385389 : ℝ) / 1000 ≤ Chebyshev.psi 383 ∧ Chebyshev.psi 383 ≤ (386083 : ℝ) / 1000 := by
  have hl : 2 ^ 556 ≤ Nat.lcmUpto 383 := by decide +kernel
  have hu : Nat.lcmUpto 383 ≤ 2 ^ (556 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 389. -/
private theorem psi_389_bounds :
    (391628 : ℝ) / 1000 ≤ Chebyshev.psi 389 ∧ Chebyshev.psi 389 ≤ (392322 : ℝ) / 1000 := by
  have hl : 2 ^ 565 ≤ Nat.lcmUpto 389 := by decide +kernel
  have hu : Nat.lcmUpto 389 ≤ 2 ^ (565 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 401. -/
private theorem psi_401_bounds :
    (403411 : ℝ) / 1000 ≤ Chebyshev.psi 401 ∧ Chebyshev.psi 401 ≤ (404105 : ℝ) / 1000 := by
  have hl : 2 ^ 582 ≤ Nat.lcmUpto 401 := by decide +kernel
  have hu : Nat.lcmUpto 401 ≤ 2 ^ (582 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 409. -/
private theorem psi_409_bounds :
    (409649 : ℝ) / 1000 ≤ Chebyshev.psi 409 ∧ Chebyshev.psi 409 ≤ (410344 : ℝ) / 1000 := by
  have hl : 2 ^ 591 ≤ Nat.lcmUpto 409 := by decide +kernel
  have hu : Nat.lcmUpto 409 ≤ 2 ^ (591 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 419. -/
private theorem psi_419_bounds :
    (415195 : ℝ) / 1000 ≤ Chebyshev.psi 419 ∧ Chebyshev.psi 419 ≤ (415889 : ℝ) / 1000 := by
  have hl : 2 ^ 599 ≤ Nat.lcmUpto 419 := by decide +kernel
  have hu : Nat.lcmUpto 419 ≤ 2 ^ (599 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 421. -/
private theorem psi_421_bounds :
    (421433 : ℝ) / 1000 ≤ Chebyshev.psi 421 ∧ Chebyshev.psi 421 ≤ (422127 : ℝ) / 1000 := by
  have hl : 2 ^ 608 ≤ Nat.lcmUpto 421 := by decide +kernel
  have hu : Nat.lcmUpto 421 ≤ 2 ^ (608 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 431. -/
private theorem psi_431_bounds :
    (427671 : ℝ) / 1000 ≤ Chebyshev.psi 431 ∧ Chebyshev.psi 431 ≤ (428365 : ℝ) / 1000 := by
  have hl : 2 ^ 617 ≤ Nat.lcmUpto 431 := by decide +kernel
  have hu : Nat.lcmUpto 431 ≤ 2 ^ (617 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 439. -/
private theorem psi_439_bounds :
    (439455 : ℝ) / 1000 ≤ Chebyshev.psi 439 ∧ Chebyshev.psi 439 ≤ (440149 : ℝ) / 1000 := by
  have hl : 2 ^ 634 ≤ Nat.lcmUpto 439 := by decide +kernel
  have hu : Nat.lcmUpto 439 ≤ 2 ^ (634 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 443. -/
private theorem psi_443_bounds :
    (445693 : ℝ) / 1000 ≤ Chebyshev.psi 443 ∧ Chebyshev.psi 443 ≤ (446387 : ℝ) / 1000 := by
  have hl : 2 ^ 643 ≤ Nat.lcmUpto 443 := by decide +kernel
  have hu : Nat.lcmUpto 443 ≤ 2 ^ (643 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 457. -/
private theorem psi_457_bounds :
    (458170 : ℝ) / 1000 ≤ Chebyshev.psi 457 ∧ Chebyshev.psi 457 ≤ (458864 : ℝ) / 1000 := by
  have hl : 2 ^ 661 ≤ Nat.lcmUpto 457 := by decide +kernel
  have hu : Nat.lcmUpto 457 ≤ 2 ^ (661 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 461. -/
private theorem psi_461_bounds :
    (464408 : ℝ) / 1000 ≤ Chebyshev.psi 461 ∧ Chebyshev.psi 461 ≤ (465102 : ℝ) / 1000 := by
  have hl : 2 ^ 670 ≤ Nat.lcmUpto 461 := by decide +kernel
  have hu : Nat.lcmUpto 461 ≤ 2 ^ (670 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 467. -/
private theorem psi_467_bounds :
    (476192 : ℝ) / 1000 ≤ Chebyshev.psi 467 ∧ Chebyshev.psi 467 ≤ (476886 : ℝ) / 1000 := by
  have hl : 2 ^ 687 ≤ Nat.lcmUpto 467 := by decide +kernel
  have hu : Nat.lcmUpto 467 ≤ 2 ^ (687 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 479. -/
private theorem psi_479_bounds :
    (482430 : ℝ) / 1000 ≤ Chebyshev.psi 479 ∧ Chebyshev.psi 479 ≤ (483124 : ℝ) / 1000 := by
  have hl : 2 ^ 696 ≤ Nat.lcmUpto 479 := by decide +kernel
  have hu : Nat.lcmUpto 479 ≤ 2 ^ (696 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 487. -/
private theorem psi_487_bounds :
    (488668 : ℝ) / 1000 ≤ Chebyshev.psi 487 ∧ Chebyshev.psi 487 ≤ (489362 : ℝ) / 1000 := by
  have hl : 2 ^ 705 ≤ Nat.lcmUpto 487 := by decide +kernel
  have hu : Nat.lcmUpto 487 ≤ 2 ^ (705 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 491. -/
private theorem psi_491_bounds :
    (494907 : ℝ) / 1000 ≤ Chebyshev.psi 491 ∧ Chebyshev.psi 491 ≤ (495601 : ℝ) / 1000 := by
  have hl : 2 ^ 714 ≤ Nat.lcmUpto 491 := by decide +kernel
  have hu : Nat.lcmUpto 491 ≤ 2 ^ (714 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 499. -/
private theorem psi_499_bounds :
    (501145 : ℝ) / 1000 ≤ Chebyshev.psi 499 ∧ Chebyshev.psi 499 ≤ (501839 : ℝ) / 1000 := by
  have hl : 2 ^ 723 ≤ Nat.lcmUpto 499 := by decide +kernel
  have hu : Nat.lcmUpto 499 ≤ 2 ^ (723 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- A rational certificate bounds the envelope from 327 onward. -/
private theorem batch_envelope {t : ℝ} (ht : 327 ≤ t) :
    (16 : ℝ) ≤
      Real.sqrt t * (Real.log t * (Real.log t - Real.log (Real.log t)) / (8 * Real.pi)) := by
  have h :=
    RiemannZeta.lee_nosal_envelope_of_log_checks (N := 327) (lo := 578 / 100) (hi := 579 / 100)
      (vlo := 175 / 100) (vhi := 176 / 100) (c := 16) (j := 9) (k := 3) (n := 32) (m := 32)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by decide +kernel) (by decide +kernel) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact
    h.trans
      (RiemannZeta.lee_nosal_envelope_mono (x := 327) (y := t)
        (Real.exp_one_lt_three.le.trans (by norm_num only)) ht)

/-- Every batch cell has a checked psi lower bound. -/
private theorem batch_lower : ∀ r ∈ batchCells, (r.lo : ℝ) / 1000 ≤ Chebyshev.psi r.a := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (321620 : ℝ) / 1000 ≤ Chebyshev.psi (↑(327 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 317) (b := 327) (by decide) (by decide +kernel)]
    exact psi_317_bounds.1
  · change (333403 : ℝ) / 1000 ≤ Chebyshev.psi (↑(337 : ℕ) : ℝ)
    exact psi_337_bounds.1
  · change (347266 : ℝ) / 1000 ≤ Chebyshev.psi (↑(349 : ℕ) : ℝ)
    exact psi_349_bounds.1
  · change (361822 : ℝ) / 1000 ≤ Chebyshev.psi (↑(363 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 361) (b := 363) (by decide) (by decide +kernel)]
    exact psi_361_bounds.1
  · change (373606 : ℝ) / 1000 ≤ Chebyshev.psi (↑(377 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 373) (b := 377) (by decide) (by decide +kernel)]
    exact psi_373_bounds.1
  · change (391628 : ℝ) / 1000 ≤ Chebyshev.psi (↑(389 : ℕ) : ℝ)
    exact psi_389_bounds.1
  · change (403411 : ℝ) / 1000 ≤ Chebyshev.psi (↑(407 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 401) (b := 407) (by decide) (by decide +kernel)]
    exact psi_401_bounds.1
  · change (415195 : ℝ) / 1000 ≤ Chebyshev.psi (↑(419 : ℕ) : ℝ)
    exact psi_419_bounds.1
  · change (427671 : ℝ) / 1000 ≤ Chebyshev.psi (↑(431 : ℕ) : ℝ)
    exact psi_431_bounds.1
  · change (445693 : ℝ) / 1000 ≤ Chebyshev.psi (↑(443 : ℕ) : ℝ)
    exact psi_443_bounds.1
  · change (464408 : ℝ) / 1000 ≤ Chebyshev.psi (↑(461 : ℕ) : ℝ)
    exact psi_461_bounds.1
  · change (482430 : ℝ) / 1000 ≤ Chebyshev.psi (↑(479 : ℕ) : ℝ)
    exact psi_479_bounds.1
  · change (494907 : ℝ) / 1000 ≤ Chebyshev.psi (↑(491 : ℕ) : ℝ)
    exact psi_491_bounds.1

/-- Every batch cell has a checked psi upper bound. -/
private theorem batch_upper :
    ∀ r ∈ batchCells, Chebyshev.psi (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Chebyshev.psi (↑(336 : ℕ) : ℝ) ≤ (328552 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 331) (b := 336) (by decide) (by decide +kernel)]
    exact psi_331_bounds.2
  · change Chebyshev.psi (↑(348 : ℕ) : ℝ) ≤ (341722 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 347) (b := 348) (by decide) (by decide +kernel)]
    exact psi_347_bounds.2
  · change Chebyshev.psi (↑(362 : ℕ) : ℝ) ≤ (362516 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 361) (b := 362) (by decide) (by decide +kernel)]
    exact psi_361_bounds.2
  · change Chebyshev.psi (↑(376 : ℕ) : ℝ) ≤ (374300 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 373) (b := 376) (by decide) (by decide +kernel)]
    exact psi_373_bounds.2
  · change Chebyshev.psi (↑(388 : ℕ) : ℝ) ≤ (386083 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 383) (b := 388) (by decide) (by decide +kernel)]
    exact psi_383_bounds.2
  · change Chebyshev.psi (↑(406 : ℕ) : ℝ) ≤ (404105 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 401) (b := 406) (by decide) (by decide +kernel)]
    exact psi_401_bounds.2
  · change Chebyshev.psi (↑(418 : ℕ) : ℝ) ≤ (410344 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 409) (b := 418) (by decide) (by decide +kernel)]
    exact psi_409_bounds.2
  · change Chebyshev.psi (↑(430 : ℕ) : ℝ) ≤ (422127 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 421) (b := 430) (by decide) (by decide +kernel)]
    exact psi_421_bounds.2
  · change Chebyshev.psi (↑(442 : ℕ) : ℝ) ≤ (440149 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 439) (b := 442) (by decide) (by decide +kernel)]
    exact psi_439_bounds.2
  · change Chebyshev.psi (↑(460 : ℕ) : ℝ) ≤ (458864 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 457) (b := 460) (by decide) (by decide +kernel)]
    exact psi_457_bounds.2
  · change Chebyshev.psi (↑(478 : ℕ) : ℝ) ≤ (476886 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 467) (b := 478) (by decide) (by decide +kernel)]
    exact psi_467_bounds.2
  · change Chebyshev.psi (↑(490 : ℕ) : ℝ) ≤ (489362 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 487) (b := 490) (by decide) (by decide +kernel)]
    exact psi_487_bounds.2
  · change Chebyshev.psi (↑(502 : ℕ) : ℝ) ≤ (501839 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 499) (b := 502) (by decide) (by decide +kernel)]
    exact psi_499_bounds.2

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
      (16000 : ℝ) / 1000 ≤
        Real.sqrt 327 * (Real.log 327 * (Real.log 327 - Real.log (Real.log 327)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (16000 : ℝ) / 1000 ≤
        Real.sqrt 337 * (Real.log 337 * (Real.log 337 - Real.log (Real.log 337)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (16000 : ℝ) / 1000 ≤
        Real.sqrt 349 * (Real.log 349 * (Real.log 349 - Real.log (Real.log 349)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (16000 : ℝ) / 1000 ≤
        Real.sqrt 363 * (Real.log 363 * (Real.log 363 - Real.log (Real.log 363)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (16000 : ℝ) / 1000 ≤
        Real.sqrt 377 * (Real.log 377 * (Real.log 377 - Real.log (Real.log 377)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (16000 : ℝ) / 1000 ≤
        Real.sqrt 389 * (Real.log 389 * (Real.log 389 - Real.log (Real.log 389)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (16000 : ℝ) / 1000 ≤
        Real.sqrt 407 * (Real.log 407 * (Real.log 407 - Real.log (Real.log 407)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (16000 : ℝ) / 1000 ≤
        Real.sqrt 419 * (Real.log 419 * (Real.log 419 - Real.log (Real.log 419)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (16000 : ℝ) / 1000 ≤
        Real.sqrt 431 * (Real.log 431 * (Real.log 431 - Real.log (Real.log 431)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (16000 : ℝ) / 1000 ≤
        Real.sqrt 443 * (Real.log 443 * (Real.log 443 - Real.log (Real.log 443)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (16000 : ℝ) / 1000 ≤
        Real.sqrt 461 * (Real.log 461 * (Real.log 461 - Real.log (Real.log 461)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (16000 : ℝ) / 1000 ≤
        Real.sqrt 479 * (Real.log 479 * (Real.log 479 - Real.log (Real.log 479)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (16000 : ℝ) / 1000 ≤
        Real.sqrt 491 * (Real.log 491 * (Real.log 491 - Real.log (Real.log 491)) / (8 * Real.pi))
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
      (16000 : ℝ) / 1000 ≤
        Real.sqrt 337 * (Real.log 337 * (Real.log 337 - Real.log (Real.log 337)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (16000 : ℝ) / 1000 ≤
        Real.sqrt 349 * (Real.log 349 * (Real.log 349 - Real.log (Real.log 349)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (16000 : ℝ) / 1000 ≤
        Real.sqrt 363 * (Real.log 363 * (Real.log 363 - Real.log (Real.log 363)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (16000 : ℝ) / 1000 ≤
        Real.sqrt 377 * (Real.log 377 * (Real.log 377 - Real.log (Real.log 377)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (16000 : ℝ) / 1000 ≤
        Real.sqrt 389 * (Real.log 389 * (Real.log 389 - Real.log (Real.log 389)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (16000 : ℝ) / 1000 ≤
        Real.sqrt 407 * (Real.log 407 * (Real.log 407 - Real.log (Real.log 407)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (16000 : ℝ) / 1000 ≤
        Real.sqrt 419 * (Real.log 419 * (Real.log 419 - Real.log (Real.log 419)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (16000 : ℝ) / 1000 ≤
        Real.sqrt 431 * (Real.log 431 * (Real.log 431 - Real.log (Real.log 431)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (16000 : ℝ) / 1000 ≤
        Real.sqrt 443 * (Real.log 443 * (Real.log 443 - Real.log (Real.log 443)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (16000 : ℝ) / 1000 ≤
        Real.sqrt 461 * (Real.log 461 * (Real.log 461 - Real.log (Real.log 461)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (16000 : ℝ) / 1000 ≤
        Real.sqrt 479 * (Real.log 479 * (Real.log 479 - Real.log (Real.log 479)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (16000 : ℝ) / 1000 ≤
        Real.sqrt 491 * (Real.log 491 * (Real.log 491 - Real.log (Real.log 491)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (16000 : ℝ) / 1000 ≤
        Real.sqrt 503 * (Real.log 503 * (Real.log 503 - Real.log (Real.log 503)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)

/-- The checked batch proves the Lee–Nosal psi estimate on `[327, 503)`. -/
theorem bound_327_503 {x : ℝ} (ha : 327 ≤ x) (hb : x < 503) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    RiemannZeta.lee_nosal_chain_sound Chebyshev.psi_mono Chebyshev.psi_eq_psi_coe_floor
      (by decide +kernel) batch_lower batch_upper batch_a batch_b ha hb

/-- Combining adjacent certified batches gives the estimate on `[101, 503)`. -/
theorem bound_101_503 {x : ℝ} (ha : 101 ≤ x) (hb : x < 503) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  by_cases h : x < 327
  · exact bound_101_327 ha h
  · exact bound_327_503 (le_of_not_gt h) hb

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiChecks
