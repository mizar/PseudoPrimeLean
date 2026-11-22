/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import all PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt81Checker
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevLcmBounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Chebyshev psi certificate on [348, 568) -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound

/-- LCM comparisons and the integer crossing check certify the cell starting at 348. -/
private theorem cell348 {x : ℝ} (ha : 348 ≤ x) (hb : x < 356) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (341028 : ℝ) / 1000 ≤ Chebyshev.psi 348 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 348) (k := 492) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 355 ≤ (353506 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 355) (k := 509) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨348, 356, 341028, 353506, 15110, 15283⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 356. -/
private theorem cell356 {x : ℝ} (ha : 356 ≤ x) (hb : x < 368) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (352811 : ℝ) / 1000 ≤ Chebyshev.psi 356 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 356) (k := 509) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 367 ≤ (368755 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 367) (k := 531) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨356, 368, 352811, 368755, 15283, 15538⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 368. -/
private theorem cell368 {x : ℝ} (ha : 368 ≤ x) (hb : x < 383) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (368061 : ℝ) / 1000 ≤ Chebyshev.psi 368 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 368) (k := 531) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 382 ≤ (380538 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 382) (k := 548) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨368, 383, 368061, 380538, 15538, 15852⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 383. -/
private theorem cell383 {x : ℝ} (ha : 383 ≤ x) (hb : x < 401) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (385389 : ℝ) / 1000 ≤ Chebyshev.psi 383 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 383) (k := 556) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 400 ≤ (397867 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 400) (k := 573) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨383, 401, 385389, 397867, 15852, 16220⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 401. -/
private theorem cell401 {x : ℝ} (ha : 401 ≤ x) (hb : x < 420) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (403411 : ℝ) / 1000 ≤ Chebyshev.psi 401 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 401) (k := 582) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 419 ≤ (415889 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 419) (k := 599) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨401, 420, 403411, 415889, 16220, 16600⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 420. -/
private theorem cell420 {x : ℝ} (ha : 420 ≤ x) (hb : x < 432) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (415195 : ℝ) / 1000 ≤ Chebyshev.psi 420 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 420) (k := 599) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 431 ≤ (428365 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 431) (k := 617) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨420, 432, 415195, 428365, 16600, 16835⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 432. -/
private theorem cell432 {x : ℝ} (ha : 432 ≤ x) (hb : x < 444) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (427671 : ℝ) / 1000 ≤ Chebyshev.psi 432 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 432) (k := 617) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 443 ≤ (446387 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 443) (k := 643) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨432, 444, 427671, 446387, 16835, 17067⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 444. -/
private theorem cell444 {x : ℝ} (ha : 444 ≤ x) (hb : x < 461) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (445693 : ℝ) / 1000 ≤ Chebyshev.psi 444 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 444) (k := 643) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 460 ≤ (458864 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 460) (k := 661) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨444, 461, 445693, 458864, 17067, 17391⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 461. -/
private theorem cell461 {x : ℝ} (ha : 461 ≤ x) (hb : x < 479) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (464408 : ℝ) / 1000 ≤ Chebyshev.psi 461 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 461) (k := 670) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 478 ≤ (476886 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 478) (k := 687) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨461, 479, 464408, 476886, 17391, 17727⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 479. -/
private theorem cell479 {x : ℝ} (ha : 479 ≤ x) (hb : x < 499) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (482430 : ℝ) / 1000 ≤ Chebyshev.psi 479 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 479) (k := 696) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 498 ≤ (495601 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 498) (k := 714) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨479, 499, 482430, 495601, 17727, 18094⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 499. -/
private theorem cell499 {x : ℝ} (ha : 499 ≤ x) (hb : x < 519) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (501145 : ℝ) / 1000 ≤ Chebyshev.psi 499 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 499) (k := 723) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 518 ≤ (515009 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 518) (k := 742) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨499, 519, 501145, 515009, 18094, 18453⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 519. -/
private theorem cell519 {x : ℝ} (ha : 519 ≤ x) (hb : x < 533) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (514315 : ℝ) / 1000 ≤ Chebyshev.psi 519 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 519) (k := 742) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 532 ≤ (530951 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 532) (k := 765) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨519, 533, 514315, 530951, 18453, 18700⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 533. -/
private theorem cell533 {x : ℝ} (ha : 533 ≤ x) (hb : x < 549) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (530257 : ℝ) / 1000 ≤ Chebyshev.psi 533 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 533) (k := 765) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 548 ≤ (543428 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 548) (k := 783) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨533, 549, 530257, 543428, 18700, 18978⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 549. -/
private theorem cell549 {x : ℝ} (ha : 549 ≤ x) (hb : x < 561) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (542734 : ℝ) / 1000 ≤ Chebyshev.psi 549 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 549) (k := 783) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 560 ≤ (549666 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 560) (k := 792) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨549, 561, 542734, 549666, 18978, 19185⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 561. -/
private theorem cell561 {x : ℝ} (ha : 561 ≤ x) (hb : x < 568) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (548972 : ℝ) / 1000 ≤ Chebyshev.psi 561 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 561) (k := 792) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 567 ≤ (555905 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 567) (k := 801) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨561, 568, 548972, 555905, 19185, 19304⟩ (by decide) hl hu ha hb

/-- The checked cells cover every real point in the half-open interval [348, 568). -/
theorem psi81_on_348_568 {x : ℝ} (ha : 348 ≤ x) (hb : x < 568) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ (81 / 100 : ℝ) := by
  have hx : 0 < x := by linarith only [ha]
  apply (div_le_iff₀ (Real.sqrt_pos.2 hx)).2
  by_cases h356 : x < 356
  · exact cell348 ha h356
  by_cases h368 : x < 368
  · exact cell356 (le_of_not_gt h356) h368
  by_cases h383 : x < 383
  · exact cell368 (le_of_not_gt h368) h383
  by_cases h401 : x < 401
  · exact cell383 (le_of_not_gt h383) h401
  by_cases h420 : x < 420
  · exact cell401 (le_of_not_gt h401) h420
  by_cases h432 : x < 432
  · exact cell420 (le_of_not_gt h420) h432
  by_cases h444 : x < 444
  · exact cell432 (le_of_not_gt h432) h444
  by_cases h461 : x < 461
  · exact cell444 (le_of_not_gt h444) h461
  by_cases h479 : x < 479
  · exact cell461 (le_of_not_gt h461) h479
  by_cases h499 : x < 499
  · exact cell479 (le_of_not_gt h479) h499
  by_cases h519 : x < 519
  · exact cell499 (le_of_not_gt h499) h519
  by_cases h533 : x < 533
  · exact cell519 (le_of_not_gt h519) h533
  by_cases h549 : x < 549
  · exact cell533 (le_of_not_gt h533) h549
  by_cases h561 : x < 561
  · exact cell549 (le_of_not_gt h549) h561
  exact cell561 (le_of_not_gt h561) hb

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound
