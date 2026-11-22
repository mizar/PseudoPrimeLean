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

/-! # Chebyshev psi certificate on [568, 815) -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound

/-- LCM comparisons and the integer crossing check certify the cell starting at 568. -/
private theorem cell568 {x : ℝ} (ha : 568 ≤ x) (hb : x < 574) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (555210 : ℝ) / 1000 ≤ Chebyshev.psi 568 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 568) (k := 801) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 573 ≤ (569074 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 573) (k := 820) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨568, 574, 555210, 569074, 19304, 19406⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 574. -/
private theorem cell574 {x : ℝ} (ha : 574 ≤ x) (hb : x < 588) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (568380 : ℝ) / 1000 ≤ Chebyshev.psi 574 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 574) (k := 820) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 587 ≤ (581551 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 587) (k := 838) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨574, 588, 568380, 581551, 19406, 19641⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 588. -/
private theorem cell588 {x : ℝ} (ha : 588 ≤ x) (hb : x < 600) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (580857 : ℝ) / 1000 ≤ Chebyshev.psi 588 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 588) (k := 838) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 599 ≤ (594028 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 599) (k := 856) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨588, 600, 580857, 594028, 19641, 19840⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 600. -/
private theorem cell600 {x : ℝ} (ha : 600 ≤ x) (hb : x < 613) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (593333 : ℝ) / 1000 ≤ Chebyshev.psi 600 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 600) (k := 856) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 612 ≤ (607197 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 612) (k := 875) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨600, 613, 593333, 607197, 19840, 20054⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 613. -/
private theorem cell613 {x : ℝ} (ha : 613 ≤ x) (hb : x < 631) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (612742 : ℝ) / 1000 ≤ Chebyshev.psi 613 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 613) (k := 884) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 630 ≤ (627992 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 630) (k := 905) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨613, 631, 612742, 627992, 20054, 20346⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 631. -/
private theorem cell631 {x : ℝ} (ha : 631 ≤ x) (hb : x < 647) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (633536 : ℝ) / 1000 ≤ Chebyshev.psi 631 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 631) (k := 914) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 646 ≤ (647400 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 646) (k := 933) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨631, 647, 633536, 647400, 20346, 20603⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 647. -/
private theorem cell647 {x : ℝ} (ha : 647 ≤ x) (hb : x < 661) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (652944 : ℝ) / 1000 ≤ Chebyshev.psi 647 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 647) (k := 942) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 660 ≤ (666808 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 660) (k := 961) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨647, 661, 652944, 666808, 20603, 20825⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 661. -/
private theorem cell661 {x : ℝ} (ha : 661 ≤ x) (hb : x < 677) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (672352 : ℝ) / 1000 ≤ Chebyshev.psi 661 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 661) (k := 970) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 676 ≤ (679978 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 676) (k := 980) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨661, 677, 672352, 679978, 20825, 21075⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 677. -/
private theorem cell677 {x : ℝ} (ha : 677 ≤ x) (hb : x < 691) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (685522 : ℝ) / 1000 ≤ Chebyshev.psi 677 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 677) (k := 989) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 690 ≤ (693148 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 690) (k := 999) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨677, 691, 685522, 693148, 21075, 21292⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 691. -/
private theorem cell691 {x : ℝ} (ha : 691 ≤ x) (hb : x < 709) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (698692 : ℝ) / 1000 ≤ Chebyshev.psi 691 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 691) (k := 1008) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 708 ≤ (705624 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 708) (k := 1017) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨691, 709, 698692, 705624, 21292, 21567⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 709. -/
private theorem cell709 {x : ℝ} (ha : 709 ≤ x) (hb : x < 733) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (711862 : ℝ) / 1000 ≤ Chebyshev.psi 709 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 709) (k := 1027) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 732 ≤ (726419 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 732) (k := 1047) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨709, 733, 711862, 726419, 21567, 21929⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 733. -/
private theorem cell733 {x : ℝ} (ha : 733 ≤ x) (hb : x < 754) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (732656 : ℝ) / 1000 ≤ Chebyshev.psi 733 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 733) (k := 1057) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 753 ≤ (753451 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 753) (k := 1086) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨733, 754, 732656, 753451, 21929, 22241⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 754. -/
private theorem cell754 {x : ℝ} (ha : 754 ≤ x) (hb : x < 773) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (752757 : ℝ) / 1000 ≤ Chebyshev.psi 754 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 754) (k := 1086) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 772 ≤ (772860 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 772) (k := 1114) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨754, 773, 752757, 772860, 22241, 22520⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 773. -/
private theorem cell773 {x : ℝ} (ha : 773 ≤ x) (hb : x < 802) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (779097 : ℝ) / 1000 ≤ Chebyshev.psi 773 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 773) (k := 1124) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 801 ≤ (792961 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 801) (k := 1143) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨773, 802, 779097, 792961, 22520, 22938⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 802. -/
private theorem cell802 {x : ℝ} (ha : 802 ≤ x) (hb : x < 815) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (792267 : ℝ) / 1000 ≤ Chebyshev.psi 802 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 802) (k := 1143) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 814 ≤ (806131 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 814) (k := 1162) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨802, 815, 792267, 806131, 22938, 23124⟩ (by decide) hl hu ha hb

/-- The checked cells cover every real point in the half-open interval [568, 815). -/
theorem psi81_on_568_815 {x : ℝ} (ha : 568 ≤ x) (hb : x < 815) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ (81 / 100 : ℝ) := by
  have hx : 0 < x := by linarith only [ha]
  apply (div_le_iff₀ (Real.sqrt_pos.2 hx)).2
  by_cases h574 : x < 574
  · exact cell568 ha h574
  by_cases h588 : x < 588
  · exact cell574 (le_of_not_gt h574) h588
  by_cases h600 : x < 600
  · exact cell588 (le_of_not_gt h588) h600
  by_cases h613 : x < 613
  · exact cell600 (le_of_not_gt h600) h613
  by_cases h631 : x < 631
  · exact cell613 (le_of_not_gt h613) h631
  by_cases h647 : x < 647
  · exact cell631 (le_of_not_gt h631) h647
  by_cases h661 : x < 661
  · exact cell647 (le_of_not_gt h647) h661
  by_cases h677 : x < 677
  · exact cell661 (le_of_not_gt h661) h677
  by_cases h691 : x < 691
  · exact cell677 (le_of_not_gt h677) h691
  by_cases h709 : x < 709
  · exact cell691 (le_of_not_gt h691) h709
  by_cases h733 : x < 733
  · exact cell709 (le_of_not_gt h709) h733
  by_cases h754 : x < 754
  · exact cell733 (le_of_not_gt h733) h754
  by_cases h773 : x < 773
  · exact cell754 (le_of_not_gt h754) h773
  by_cases h802 : x < 802
  · exact cell773 (le_of_not_gt h773) h802
  exact cell802 (le_of_not_gt h802) hb

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound
