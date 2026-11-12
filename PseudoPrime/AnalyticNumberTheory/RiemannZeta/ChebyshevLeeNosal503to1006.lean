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
  [⟨503, 523, 507383, 521247, 24000, 24000⟩, ⟨523, 550, 526791, 543428, 24000, 24000⟩,
    ⟨550, 566, 542734, 555905, 24000, 24000⟩, ⟨566, 579, 555210, 575313, 24000, 24000⟩,
    ⟨579, 598, 574619, 587789, 24000, 24000⟩, ⟨598, 611, 587095, 607197, 24000, 24000⟩,
    ⟨611, 630, 606503, 627992, 24000, 24000⟩, ⟨630, 651, 627298, 653638, 24000, 24000⟩,
    ⟨651, 673, 652944, 673046, 24000, 24000⟩, ⟨673, 691, 679284, 693148, 24000, 24000⟩,
    ⟨691, 719, 698692, 712556, 24000, 24000⟩, ⟨719, 742, 718100, 740282, 24000, 24000⟩,
    ⟨742, 761, 739588, 759690, 24000, 24000⟩, ⟨761, 787, 765927, 779791, 24000, 24000⟩,
    ⟨787, 810, 786028, 799892, 24000, 24000⟩, ⟨810, 823, 799198, 813062, 24000, 24000⟩,
    ⟨823, 843, 819299, 843561, 24000, 24000⟩, ⟨843, 863, 842866, 863662, 24000, 24000⟩,
    ⟨863, 883, 869899, 883763, 24000, 24000⟩, ⟨883, 911, 890000, 904558, 24000, 24000⟩,
    ⟨911, 934, 910795, 924659, 24000, 24000⟩, ⟨934, 947, 923965, 938522, 24000, 24000⟩,
    ⟨947, 968, 944759, 962782, 24000, 24000⟩, ⟨968, 986, 962088, 982883, 24000, 24000⟩,
    ⟨986, 1006, 982189, 996746, 24000, 24000⟩]

/-- The kernel-checked prefix bounds for 503. -/
private theorem psi_503_bounds :
    (507383 : ℝ) / 1000 ≤ Chebyshev.psi 503 ∧ Chebyshev.psi 503 ≤ (508077 : ℝ) / 1000 := by
  have hl : 2 ^ 732 ≤ Nat.lcmUpto 503 := by decide +kernel
  have hu : Nat.lcmUpto 503 ≤ 2 ^ (732 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 521. -/
private theorem psi_521_bounds :
    (520553 : ℝ) / 1000 ≤ Chebyshev.psi 521 ∧ Chebyshev.psi 521 ≤ (521247 : ℝ) / 1000 := by
  have hl : 2 ^ 751 ≤ Nat.lcmUpto 521 := by decide +kernel
  have hu : Nat.lcmUpto 521 ≤ 2 ^ (751 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 523. -/
private theorem psi_523_bounds :
    (526791 : ℝ) / 1000 ≤ Chebyshev.psi 523 ∧ Chebyshev.psi 523 ≤ (527486 : ℝ) / 1000 := by
  have hl : 2 ^ 760 ≤ Nat.lcmUpto 523 := by decide +kernel
  have hu : Nat.lcmUpto 523 ≤ 2 ^ (760 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 547. -/
private theorem psi_547_bounds :
    (542734 : ℝ) / 1000 ≤ Chebyshev.psi 547 ∧ Chebyshev.psi 547 ≤ (543428 : ℝ) / 1000 := by
  have hl : 2 ^ 783 ≤ Nat.lcmUpto 547 := by decide +kernel
  have hu : Nat.lcmUpto 547 ≤ 2 ^ (783 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 563. -/
private theorem psi_563_bounds :
    (555210 : ℝ) / 1000 ≤ Chebyshev.psi 563 ∧ Chebyshev.psi 563 ≤ (555905 : ℝ) / 1000 := by
  have hl : 2 ^ 801 ≤ Nat.lcmUpto 563 := by decide +kernel
  have hu : Nat.lcmUpto 563 ≤ 2 ^ (801 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 577. -/
private theorem psi_577_bounds :
    (574619 : ℝ) / 1000 ≤ Chebyshev.psi 577 ∧ Chebyshev.psi 577 ≤ (575313 : ℝ) / 1000 := by
  have hl : 2 ^ 829 ≤ Nat.lcmUpto 577 := by decide +kernel
  have hu : Nat.lcmUpto 577 ≤ 2 ^ (829 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 593. -/
private theorem psi_593_bounds :
    (587095 : ℝ) / 1000 ≤ Chebyshev.psi 593 ∧ Chebyshev.psi 593 ≤ (587789 : ℝ) / 1000 := by
  have hl : 2 ^ 847 ≤ Nat.lcmUpto 593 := by decide +kernel
  have hu : Nat.lcmUpto 593 ≤ 2 ^ (847 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 607. -/
private theorem psi_607_bounds :
    (606503 : ℝ) / 1000 ≤ Chebyshev.psi 607 ∧ Chebyshev.psi 607 ≤ (607197 : ℝ) / 1000 := by
  have hl : 2 ^ 875 ≤ Nat.lcmUpto 607 := by decide +kernel
  have hu : Nat.lcmUpto 607 ≤ 2 ^ (875 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 625. -/
private theorem psi_625_bounds :
    (627298 : ℝ) / 1000 ≤ Chebyshev.psi 625 ∧ Chebyshev.psi 625 ≤ (627992 : ℝ) / 1000 := by
  have hl : 2 ^ 905 ≤ Nat.lcmUpto 625 := by decide +kernel
  have hu : Nat.lcmUpto 625 ≤ 2 ^ (905 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 647. -/
private theorem psi_647_bounds :
    (652944 : ℝ) / 1000 ≤ Chebyshev.psi 647 ∧ Chebyshev.psi 647 ≤ (653638 : ℝ) / 1000 := by
  have hl : 2 ^ 942 ≤ Nat.lcmUpto 647 := by decide +kernel
  have hu : Nat.lcmUpto 647 ≤ 2 ^ (942 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 661. -/
private theorem psi_661_bounds :
    (672352 : ℝ) / 1000 ≤ Chebyshev.psi 661 ∧ Chebyshev.psi 661 ≤ (673046 : ℝ) / 1000 := by
  have hl : 2 ^ 970 ≤ Nat.lcmUpto 661 := by decide +kernel
  have hu : Nat.lcmUpto 661 ≤ 2 ^ (970 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 673. -/
private theorem psi_673_bounds :
    (679284 : ℝ) / 1000 ≤ Chebyshev.psi 673 ∧ Chebyshev.psi 673 ≤ (679978 : ℝ) / 1000 := by
  have hl : 2 ^ 980 ≤ Nat.lcmUpto 673 := by decide +kernel
  have hu : Nat.lcmUpto 673 ≤ 2 ^ (980 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 683. -/
private theorem psi_683_bounds :
    (692454 : ℝ) / 1000 ≤ Chebyshev.psi 683 ∧ Chebyshev.psi 683 ≤ (693148 : ℝ) / 1000 := by
  have hl : 2 ^ 999 ≤ Nat.lcmUpto 683 := by decide +kernel
  have hu : Nat.lcmUpto 683 ≤ 2 ^ (999 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 691. -/
private theorem psi_691_bounds :
    (698692 : ℝ) / 1000 ≤ Chebyshev.psi 691 ∧ Chebyshev.psi 691 ≤ (699386 : ℝ) / 1000 := by
  have hl : 2 ^ 1008 ≤ Nat.lcmUpto 691 := by decide +kernel
  have hu : Nat.lcmUpto 691 ≤ 2 ^ (1008 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 709. -/
private theorem psi_709_bounds :
    (711862 : ℝ) / 1000 ≤ Chebyshev.psi 709 ∧ Chebyshev.psi 709 ≤ (712556 : ℝ) / 1000 := by
  have hl : 2 ^ 1027 ≤ Nat.lcmUpto 709 := by decide +kernel
  have hu : Nat.lcmUpto 709 ≤ 2 ^ (1027 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 719. -/
private theorem psi_719_bounds :
    (718100 : ℝ) / 1000 ≤ Chebyshev.psi 719 ∧ Chebyshev.psi 719 ≤ (718794 : ℝ) / 1000 := by
  have hl : 2 ^ 1036 ≤ Nat.lcmUpto 719 := by decide +kernel
  have hu : Nat.lcmUpto 719 ≤ 2 ^ (1036 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 739. -/
private theorem psi_739_bounds :
    (739588 : ℝ) / 1000 ≤ Chebyshev.psi 739 ∧ Chebyshev.psi 739 ≤ (740282 : ℝ) / 1000 := by
  have hl : 2 ^ 1067 ≤ Nat.lcmUpto 739 := by decide +kernel
  have hu : Nat.lcmUpto 739 ≤ 2 ^ (1067 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 757. -/
private theorem psi_757_bounds :
    (758996 : ℝ) / 1000 ≤ Chebyshev.psi 757 ∧ Chebyshev.psi 757 ≤ (759690 : ℝ) / 1000 := by
  have hl : 2 ^ 1095 ≤ Nat.lcmUpto 757 := by decide +kernel
  have hu : Nat.lcmUpto 757 ≤ 2 ^ (1095 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 761. -/
private theorem psi_761_bounds :
    (765927 : ℝ) / 1000 ≤ Chebyshev.psi 761 ∧ Chebyshev.psi 761 ≤ (766621 : ℝ) / 1000 := by
  have hl : 2 ^ 1105 ≤ Nat.lcmUpto 761 := by decide +kernel
  have hu : Nat.lcmUpto 761 ≤ 2 ^ (1105 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 773. -/
private theorem psi_773_bounds :
    (779097 : ℝ) / 1000 ≤ Chebyshev.psi 773 ∧ Chebyshev.psi 773 ≤ (779791 : ℝ) / 1000 := by
  have hl : 2 ^ 1124 ≤ Nat.lcmUpto 773 := by decide +kernel
  have hu : Nat.lcmUpto 773 ≤ 2 ^ (1124 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 787. -/
private theorem psi_787_bounds :
    (786028 : ℝ) / 1000 ≤ Chebyshev.psi 787 ∧ Chebyshev.psi 787 ≤ (786723 : ℝ) / 1000 := by
  have hl : 2 ^ 1134 ≤ Nat.lcmUpto 787 := by decide +kernel
  have hu : Nat.lcmUpto 787 ≤ 2 ^ (1134 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 809. -/
private theorem psi_809_bounds :
    (799198 : ℝ) / 1000 ≤ Chebyshev.psi 809 ∧ Chebyshev.psi 809 ≤ (799892 : ℝ) / 1000 := by
  have hl : 2 ^ 1153 ≤ Nat.lcmUpto 809 := by decide +kernel
  have hu : Nat.lcmUpto 809 ≤ 2 ^ (1153 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 821. -/
private theorem psi_821_bounds :
    (812368 : ℝ) / 1000 ≤ Chebyshev.psi 821 ∧ Chebyshev.psi 821 ≤ (813062 : ℝ) / 1000 := by
  have hl : 2 ^ 1172 ≤ Nat.lcmUpto 821 := by decide +kernel
  have hu : Nat.lcmUpto 821 ≤ 2 ^ (1172 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 823. -/
private theorem psi_823_bounds :
    (819299 : ℝ) / 1000 ≤ Chebyshev.psi 823 ∧ Chebyshev.psi 823 ≤ (819994 : ℝ) / 1000 := by
  have hl : 2 ^ 1182 ≤ Nat.lcmUpto 823 := by decide +kernel
  have hu : Nat.lcmUpto 823 ≤ 2 ^ (1182 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 841. -/
private theorem psi_841_bounds :
    (842866 : ℝ) / 1000 ≤ Chebyshev.psi 841 ∧ Chebyshev.psi 841 ≤ (843561 : ℝ) / 1000 := by
  have hl : 2 ^ 1216 ≤ Nat.lcmUpto 841 := by decide +kernel
  have hu : Nat.lcmUpto 841 ≤ 2 ^ (1216 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 859. -/
private theorem psi_859_bounds :
    (862968 : ℝ) / 1000 ≤ Chebyshev.psi 859 ∧ Chebyshev.psi 859 ≤ (863662 : ℝ) / 1000 := by
  have hl : 2 ^ 1245 ≤ Nat.lcmUpto 859 := by decide +kernel
  have hu : Nat.lcmUpto 859 ≤ 2 ^ (1245 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 863. -/
private theorem psi_863_bounds :
    (869899 : ℝ) / 1000 ≤ Chebyshev.psi 863 ∧ Chebyshev.psi 863 ≤ (870593 : ℝ) / 1000 := by
  have hl : 2 ^ 1255 ≤ Nat.lcmUpto 863 := by decide +kernel
  have hu : Nat.lcmUpto 863 ≤ 2 ^ (1255 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 881. -/
private theorem psi_881_bounds :
    (883069 : ℝ) / 1000 ≤ Chebyshev.psi 881 ∧ Chebyshev.psi 881 ≤ (883763 : ℝ) / 1000 := by
  have hl : 2 ^ 1274 ≤ Nat.lcmUpto 881 := by decide +kernel
  have hu : Nat.lcmUpto 881 ≤ 2 ^ (1274 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 883. -/
private theorem psi_883_bounds :
    (890000 : ℝ) / 1000 ≤ Chebyshev.psi 883 ∧ Chebyshev.psi 883 ≤ (890695 : ℝ) / 1000 := by
  have hl : 2 ^ 1284 ≤ Nat.lcmUpto 883 := by decide +kernel
  have hu : Nat.lcmUpto 883 ≤ 2 ^ (1284 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 907. -/
private theorem psi_907_bounds :
    (903863 : ℝ) / 1000 ≤ Chebyshev.psi 907 ∧ Chebyshev.psi 907 ≤ (904558 : ℝ) / 1000 := by
  have hl : 2 ^ 1304 ≤ Nat.lcmUpto 907 := by decide +kernel
  have hu : Nat.lcmUpto 907 ≤ 2 ^ (1304 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 911. -/
private theorem psi_911_bounds :
    (910795 : ℝ) / 1000 ≤ Chebyshev.psi 911 ∧ Chebyshev.psi 911 ≤ (911489 : ℝ) / 1000 := by
  have hl : 2 ^ 1314 ≤ Nat.lcmUpto 911 := by decide +kernel
  have hu : Nat.lcmUpto 911 ≤ 2 ^ (1314 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 929. -/
private theorem psi_929_bounds :
    (923965 : ℝ) / 1000 ≤ Chebyshev.psi 929 ∧ Chebyshev.psi 929 ≤ (924659 : ℝ) / 1000 := by
  have hl : 2 ^ 1333 ≤ Nat.lcmUpto 929 := by decide +kernel
  have hu : Nat.lcmUpto 929 ≤ 2 ^ (1333 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 941. -/
private theorem psi_941_bounds :
    (937828 : ℝ) / 1000 ≤ Chebyshev.psi 941 ∧ Chebyshev.psi 941 ≤ (938522 : ℝ) / 1000 := by
  have hl : 2 ^ 1353 ≤ Nat.lcmUpto 941 := by decide +kernel
  have hu : Nat.lcmUpto 941 ≤ 2 ^ (1353 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 947. -/
private theorem psi_947_bounds :
    (944759 : ℝ) / 1000 ≤ Chebyshev.psi 947 ∧ Chebyshev.psi 947 ≤ (945453 : ℝ) / 1000 := by
  have hl : 2 ^ 1363 ≤ Nat.lcmUpto 947 := by decide +kernel
  have hu : Nat.lcmUpto 947 ≤ 2 ^ (1363 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 967. -/
private theorem psi_967_bounds :
    (962088 : ℝ) / 1000 ≤ Chebyshev.psi 967 ∧ Chebyshev.psi 967 ≤ (962782 : ℝ) / 1000 := by
  have hl : 2 ^ 1388 ≤ Nat.lcmUpto 967 := by decide +kernel
  have hu : Nat.lcmUpto 967 ≤ 2 ^ (1388 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 983. -/
private theorem psi_983_bounds :
    (982189 : ℝ) / 1000 ≤ Chebyshev.psi 983 ∧ Chebyshev.psi 983 ≤ (982883 : ℝ) / 1000 := by
  have hl : 2 ^ 1417 ≤ Nat.lcmUpto 983 := by decide +kernel
  have hu : Nat.lcmUpto 983 ≤ 2 ^ (1417 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 997. -/
private theorem psi_997_bounds :
    (996052 : ℝ) / 1000 ≤ Chebyshev.psi 997 ∧ Chebyshev.psi 997 ≤ (996746 : ℝ) / 1000 := by
  have hl : 2 ^ 1437 ≤ Nat.lcmUpto 997 := by decide +kernel
  have hu : Nat.lcmUpto 997 ≤ 2 ^ (1437 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- A rational certificate bounds the envelope from 503 onward. -/
private theorem batch_envelope {t : ℝ} (ht : 503 ≤ t) :
    (24 : ℝ) ≤
      Real.sqrt t * (Real.log t * (Real.log t - Real.log (Real.log t)) / (8 * Real.pi)) := by
  have h :=
    lee_nosal_envelope_of_log_checks (N := 503) (lo := 622 / 100) (hi := 623 / 100) (vlo :=
      182 / 100) (vhi := 183 / 100) (c := 24) (j := 9) (k := 3) (n := 32) (m := 32)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by decide +kernel) (by decide +kernel) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact
    h.trans
      (lee_nosal_envelope_mono (x := 503) (y := t)
        (Real.exp_one_lt_three.le.trans (by norm_num only)) ht)

/-- Every batch cell has a checked psi lower bound. -/
private theorem batch_lower : ∀ r ∈ batchCells, (r.lo : ℝ) / 1000 ≤ Chebyshev.psi r.a := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (507383 : ℝ) / 1000 ≤ Chebyshev.psi (↑(503 : ℕ) : ℝ)
    exact psi_503_bounds.1
  · change (526791 : ℝ) / 1000 ≤ Chebyshev.psi (↑(523 : ℕ) : ℝ)
    exact psi_523_bounds.1
  · change (542734 : ℝ) / 1000 ≤ Chebyshev.psi (↑(550 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 547) (b := 550) (by decide) (by decide +kernel)]
    exact psi_547_bounds.1
  · change (555210 : ℝ) / 1000 ≤ Chebyshev.psi (↑(566 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 563) (b := 566) (by decide) (by decide +kernel)]
    exact psi_563_bounds.1
  · change (574619 : ℝ) / 1000 ≤ Chebyshev.psi (↑(579 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 577) (b := 579) (by decide) (by decide +kernel)]
    exact psi_577_bounds.1
  · change (587095 : ℝ) / 1000 ≤ Chebyshev.psi (↑(598 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 593) (b := 598) (by decide) (by decide +kernel)]
    exact psi_593_bounds.1
  · change (606503 : ℝ) / 1000 ≤ Chebyshev.psi (↑(611 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 607) (b := 611) (by decide) (by decide +kernel)]
    exact psi_607_bounds.1
  · change (627298 : ℝ) / 1000 ≤ Chebyshev.psi (↑(630 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 625) (b := 630) (by decide) (by decide +kernel)]
    exact psi_625_bounds.1
  · change (652944 : ℝ) / 1000 ≤ Chebyshev.psi (↑(651 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 647) (b := 651) (by decide) (by decide +kernel)]
    exact psi_647_bounds.1
  · change (679284 : ℝ) / 1000 ≤ Chebyshev.psi (↑(673 : ℕ) : ℝ)
    exact psi_673_bounds.1
  · change (698692 : ℝ) / 1000 ≤ Chebyshev.psi (↑(691 : ℕ) : ℝ)
    exact psi_691_bounds.1
  · change (718100 : ℝ) / 1000 ≤ Chebyshev.psi (↑(719 : ℕ) : ℝ)
    exact psi_719_bounds.1
  · change (739588 : ℝ) / 1000 ≤ Chebyshev.psi (↑(742 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 739) (b := 742) (by decide) (by decide +kernel)]
    exact psi_739_bounds.1
  · change (765927 : ℝ) / 1000 ≤ Chebyshev.psi (↑(761 : ℕ) : ℝ)
    exact psi_761_bounds.1
  · change (786028 : ℝ) / 1000 ≤ Chebyshev.psi (↑(787 : ℕ) : ℝ)
    exact psi_787_bounds.1
  · change (799198 : ℝ) / 1000 ≤ Chebyshev.psi (↑(810 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 809) (b := 810) (by decide) (by decide +kernel)]
    exact psi_809_bounds.1
  · change (819299 : ℝ) / 1000 ≤ Chebyshev.psi (↑(823 : ℕ) : ℝ)
    exact psi_823_bounds.1
  · change (842866 : ℝ) / 1000 ≤ Chebyshev.psi (↑(843 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 841) (b := 843) (by decide) (by decide +kernel)]
    exact psi_841_bounds.1
  · change (869899 : ℝ) / 1000 ≤ Chebyshev.psi (↑(863 : ℕ) : ℝ)
    exact psi_863_bounds.1
  · change (890000 : ℝ) / 1000 ≤ Chebyshev.psi (↑(883 : ℕ) : ℝ)
    exact psi_883_bounds.1
  · change (910795 : ℝ) / 1000 ≤ Chebyshev.psi (↑(911 : ℕ) : ℝ)
    exact psi_911_bounds.1
  · change (923965 : ℝ) / 1000 ≤ Chebyshev.psi (↑(934 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 929) (b := 934) (by decide) (by decide +kernel)]
    exact psi_929_bounds.1
  · change (944759 : ℝ) / 1000 ≤ Chebyshev.psi (↑(947 : ℕ) : ℝ)
    exact psi_947_bounds.1
  · change (962088 : ℝ) / 1000 ≤ Chebyshev.psi (↑(968 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 967) (b := 968) (by decide) (by decide +kernel)]
    exact psi_967_bounds.1
  · change (982189 : ℝ) / 1000 ≤ Chebyshev.psi (↑(986 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 983) (b := 986) (by decide) (by decide +kernel)]
    exact psi_983_bounds.1

/-- Every batch cell has a checked psi upper bound. -/
private theorem batch_upper :
    ∀ r ∈ batchCells, Chebyshev.psi (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Chebyshev.psi (↑(522 : ℕ) : ℝ) ≤ (521247 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 521) (b := 522) (by decide) (by decide +kernel)]
    exact psi_521_bounds.2
  · change Chebyshev.psi (↑(549 : ℕ) : ℝ) ≤ (543428 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 547) (b := 549) (by decide) (by decide +kernel)]
    exact psi_547_bounds.2
  · change Chebyshev.psi (↑(565 : ℕ) : ℝ) ≤ (555905 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 563) (b := 565) (by decide) (by decide +kernel)]
    exact psi_563_bounds.2
  · change Chebyshev.psi (↑(578 : ℕ) : ℝ) ≤ (575313 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 577) (b := 578) (by decide) (by decide +kernel)]
    exact psi_577_bounds.2
  · change Chebyshev.psi (↑(597 : ℕ) : ℝ) ≤ (587789 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 593) (b := 597) (by decide) (by decide +kernel)]
    exact psi_593_bounds.2
  · change Chebyshev.psi (↑(610 : ℕ) : ℝ) ≤ (607197 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 607) (b := 610) (by decide) (by decide +kernel)]
    exact psi_607_bounds.2
  · change Chebyshev.psi (↑(629 : ℕ) : ℝ) ≤ (627992 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 625) (b := 629) (by decide) (by decide +kernel)]
    exact psi_625_bounds.2
  · change Chebyshev.psi (↑(650 : ℕ) : ℝ) ≤ (653638 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 647) (b := 650) (by decide) (by decide +kernel)]
    exact psi_647_bounds.2
  · change Chebyshev.psi (↑(672 : ℕ) : ℝ) ≤ (673046 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 661) (b := 672) (by decide) (by decide +kernel)]
    exact psi_661_bounds.2
  · change Chebyshev.psi (↑(690 : ℕ) : ℝ) ≤ (693148 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 683) (b := 690) (by decide) (by decide +kernel)]
    exact psi_683_bounds.2
  · change Chebyshev.psi (↑(718 : ℕ) : ℝ) ≤ (712556 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 709) (b := 718) (by decide) (by decide +kernel)]
    exact psi_709_bounds.2
  · change Chebyshev.psi (↑(741 : ℕ) : ℝ) ≤ (740282 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 739) (b := 741) (by decide) (by decide +kernel)]
    exact psi_739_bounds.2
  · change Chebyshev.psi (↑(760 : ℕ) : ℝ) ≤ (759690 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 757) (b := 760) (by decide) (by decide +kernel)]
    exact psi_757_bounds.2
  · change Chebyshev.psi (↑(786 : ℕ) : ℝ) ≤ (779791 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 773) (b := 786) (by decide) (by decide +kernel)]
    exact psi_773_bounds.2
  · change Chebyshev.psi (↑(809 : ℕ) : ℝ) ≤ (799892 : ℝ) / 1000
    exact psi_809_bounds.2
  · change Chebyshev.psi (↑(822 : ℕ) : ℝ) ≤ (813062 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 821) (b := 822) (by decide) (by decide +kernel)]
    exact psi_821_bounds.2
  · change Chebyshev.psi (↑(842 : ℕ) : ℝ) ≤ (843561 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 841) (b := 842) (by decide) (by decide +kernel)]
    exact psi_841_bounds.2
  · change Chebyshev.psi (↑(862 : ℕ) : ℝ) ≤ (863662 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 859) (b := 862) (by decide) (by decide +kernel)]
    exact psi_859_bounds.2
  · change Chebyshev.psi (↑(882 : ℕ) : ℝ) ≤ (883763 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 881) (b := 882) (by decide) (by decide +kernel)]
    exact psi_881_bounds.2
  · change Chebyshev.psi (↑(910 : ℕ) : ℝ) ≤ (904558 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 907) (b := 910) (by decide) (by decide +kernel)]
    exact psi_907_bounds.2
  · change Chebyshev.psi (↑(933 : ℕ) : ℝ) ≤ (924659 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 929) (b := 933) (by decide) (by decide +kernel)]
    exact psi_929_bounds.2
  · change Chebyshev.psi (↑(946 : ℕ) : ℝ) ≤ (938522 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 941) (b := 946) (by decide) (by decide +kernel)]
    exact psi_941_bounds.2
  · change Chebyshev.psi (↑(967 : ℕ) : ℝ) ≤ (962782 : ℝ) / 1000
    exact psi_967_bounds.2
  · change Chebyshev.psi (↑(985 : ℕ) : ℝ) ≤ (982883 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 983) (b := 985) (by decide) (by decide +kernel)]
    exact psi_983_bounds.2
  · change Chebyshev.psi (↑(1005 : ℕ) : ℝ) ≤ (996746 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 997) (b := 1005) (by decide) (by decide +kernel)]
    exact psi_997_bounds.2

/-- The envelope bound applies at every cell a endpoint. -/
private theorem batch_a :
    ∀ r ∈ batchCells,
      (r.ca : ℝ) / 1000 ≤
        Real.sqrt r.a *
          (Real.log r.a * (Real.log r.a - Real.log (Real.log r.a)) / (8 * Real.pi)) := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (24000 : ℝ) / 1000 ≤
        Real.sqrt 503 * (Real.log 503 * (Real.log 503 - Real.log (Real.log 503)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (24000 : ℝ) / 1000 ≤
        Real.sqrt 523 * (Real.log 523 * (Real.log 523 - Real.log (Real.log 523)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (24000 : ℝ) / 1000 ≤
        Real.sqrt 550 * (Real.log 550 * (Real.log 550 - Real.log (Real.log 550)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (24000 : ℝ) / 1000 ≤
        Real.sqrt 566 * (Real.log 566 * (Real.log 566 - Real.log (Real.log 566)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (24000 : ℝ) / 1000 ≤
        Real.sqrt 579 * (Real.log 579 * (Real.log 579 - Real.log (Real.log 579)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (24000 : ℝ) / 1000 ≤
        Real.sqrt 598 * (Real.log 598 * (Real.log 598 - Real.log (Real.log 598)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (24000 : ℝ) / 1000 ≤
        Real.sqrt 611 * (Real.log 611 * (Real.log 611 - Real.log (Real.log 611)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (24000 : ℝ) / 1000 ≤
        Real.sqrt 630 * (Real.log 630 * (Real.log 630 - Real.log (Real.log 630)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (24000 : ℝ) / 1000 ≤
        Real.sqrt 651 * (Real.log 651 * (Real.log 651 - Real.log (Real.log 651)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (24000 : ℝ) / 1000 ≤
        Real.sqrt 673 * (Real.log 673 * (Real.log 673 - Real.log (Real.log 673)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (24000 : ℝ) / 1000 ≤
        Real.sqrt 691 * (Real.log 691 * (Real.log 691 - Real.log (Real.log 691)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (24000 : ℝ) / 1000 ≤
        Real.sqrt 719 * (Real.log 719 * (Real.log 719 - Real.log (Real.log 719)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (24000 : ℝ) / 1000 ≤
        Real.sqrt 742 * (Real.log 742 * (Real.log 742 - Real.log (Real.log 742)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (24000 : ℝ) / 1000 ≤
        Real.sqrt 761 * (Real.log 761 * (Real.log 761 - Real.log (Real.log 761)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (24000 : ℝ) / 1000 ≤
        Real.sqrt 787 * (Real.log 787 * (Real.log 787 - Real.log (Real.log 787)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (24000 : ℝ) / 1000 ≤
        Real.sqrt 810 * (Real.log 810 * (Real.log 810 - Real.log (Real.log 810)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (24000 : ℝ) / 1000 ≤
        Real.sqrt 823 * (Real.log 823 * (Real.log 823 - Real.log (Real.log 823)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (24000 : ℝ) / 1000 ≤
        Real.sqrt 843 * (Real.log 843 * (Real.log 843 - Real.log (Real.log 843)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (24000 : ℝ) / 1000 ≤
        Real.sqrt 863 * (Real.log 863 * (Real.log 863 - Real.log (Real.log 863)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (24000 : ℝ) / 1000 ≤
        Real.sqrt 883 * (Real.log 883 * (Real.log 883 - Real.log (Real.log 883)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (24000 : ℝ) / 1000 ≤
        Real.sqrt 911 * (Real.log 911 * (Real.log 911 - Real.log (Real.log 911)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (24000 : ℝ) / 1000 ≤
        Real.sqrt 934 * (Real.log 934 * (Real.log 934 - Real.log (Real.log 934)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (24000 : ℝ) / 1000 ≤
        Real.sqrt 947 * (Real.log 947 * (Real.log 947 - Real.log (Real.log 947)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (24000 : ℝ) / 1000 ≤
        Real.sqrt 968 * (Real.log 968 * (Real.log 968 - Real.log (Real.log 968)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (24000 : ℝ) / 1000 ≤
        Real.sqrt 986 * (Real.log 986 * (Real.log 986 - Real.log (Real.log 986)) / (8 * Real.pi))
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
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (24000 : ℝ) / 1000 ≤
        Real.sqrt 523 * (Real.log 523 * (Real.log 523 - Real.log (Real.log 523)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (24000 : ℝ) / 1000 ≤
        Real.sqrt 550 * (Real.log 550 * (Real.log 550 - Real.log (Real.log 550)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (24000 : ℝ) / 1000 ≤
        Real.sqrt 566 * (Real.log 566 * (Real.log 566 - Real.log (Real.log 566)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (24000 : ℝ) / 1000 ≤
        Real.sqrt 579 * (Real.log 579 * (Real.log 579 - Real.log (Real.log 579)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (24000 : ℝ) / 1000 ≤
        Real.sqrt 598 * (Real.log 598 * (Real.log 598 - Real.log (Real.log 598)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (24000 : ℝ) / 1000 ≤
        Real.sqrt 611 * (Real.log 611 * (Real.log 611 - Real.log (Real.log 611)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (24000 : ℝ) / 1000 ≤
        Real.sqrt 630 * (Real.log 630 * (Real.log 630 - Real.log (Real.log 630)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (24000 : ℝ) / 1000 ≤
        Real.sqrt 651 * (Real.log 651 * (Real.log 651 - Real.log (Real.log 651)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (24000 : ℝ) / 1000 ≤
        Real.sqrt 673 * (Real.log 673 * (Real.log 673 - Real.log (Real.log 673)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (24000 : ℝ) / 1000 ≤
        Real.sqrt 691 * (Real.log 691 * (Real.log 691 - Real.log (Real.log 691)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (24000 : ℝ) / 1000 ≤
        Real.sqrt 719 * (Real.log 719 * (Real.log 719 - Real.log (Real.log 719)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (24000 : ℝ) / 1000 ≤
        Real.sqrt 742 * (Real.log 742 * (Real.log 742 - Real.log (Real.log 742)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (24000 : ℝ) / 1000 ≤
        Real.sqrt 761 * (Real.log 761 * (Real.log 761 - Real.log (Real.log 761)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (24000 : ℝ) / 1000 ≤
        Real.sqrt 787 * (Real.log 787 * (Real.log 787 - Real.log (Real.log 787)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (24000 : ℝ) / 1000 ≤
        Real.sqrt 810 * (Real.log 810 * (Real.log 810 - Real.log (Real.log 810)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (24000 : ℝ) / 1000 ≤
        Real.sqrt 823 * (Real.log 823 * (Real.log 823 - Real.log (Real.log 823)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (24000 : ℝ) / 1000 ≤
        Real.sqrt 843 * (Real.log 843 * (Real.log 843 - Real.log (Real.log 843)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (24000 : ℝ) / 1000 ≤
        Real.sqrt 863 * (Real.log 863 * (Real.log 863 - Real.log (Real.log 863)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (24000 : ℝ) / 1000 ≤
        Real.sqrt 883 * (Real.log 883 * (Real.log 883 - Real.log (Real.log 883)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (24000 : ℝ) / 1000 ≤
        Real.sqrt 911 * (Real.log 911 * (Real.log 911 - Real.log (Real.log 911)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (24000 : ℝ) / 1000 ≤
        Real.sqrt 934 * (Real.log 934 * (Real.log 934 - Real.log (Real.log 934)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (24000 : ℝ) / 1000 ≤
        Real.sqrt 947 * (Real.log 947 * (Real.log 947 - Real.log (Real.log 947)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (24000 : ℝ) / 1000 ≤
        Real.sqrt 968 * (Real.log 968 * (Real.log 968 - Real.log (Real.log 968)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (24000 : ℝ) / 1000 ≤
        Real.sqrt 986 * (Real.log 986 * (Real.log 986 - Real.log (Real.log 986)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (24000 : ℝ) / 1000 ≤
        Real.sqrt 1006 *
          (Real.log 1006 * (Real.log 1006 - Real.log (Real.log 1006)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)

/-- The checked batch proves the Lee–Nosal psi estimate on `[503, 1006)`. -/
theorem psi_lee_nosal_503_1006 {x : ℝ} (ha : 503 ≤ x) (hb : x < 1006) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    lee_nosal_chain_sound Chebyshev.psi_mono Chebyshev.psi_eq_psi_coe_floor (by decide +kernel)
      batch_lower batch_upper batch_a batch_b ha hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
