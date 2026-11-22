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

/-! # Chebyshev psi certificate on [815, 1109) -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound

/-- LCM comparisons and the integer crossing check certify the cell starting at 815. -/
private theorem cell815 {x : ℝ} (ha : 815 ≤ x) (hb : x < 828) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (805437 : ℝ) / 1000 ≤ Chebyshev.psi 815 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 815) (k := 1162) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 827 ≤ (826925 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 827) (k := 1192) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨815, 828, 805437, 826925, 23124, 23307⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 828. -/
private theorem cell828 {x : ℝ} (ha : 828 ≤ x) (hb : x < 849) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (826231 : ℝ) / 1000 ≤ Chebyshev.psi 828 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 828) (k := 1192) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 848 ≤ (843561 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 848) (k := 1216) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨828, 849, 826231, 843561, 23307, 23601⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 849. -/
private theorem cell849 {x : ℝ} (ha : 849 ≤ x) (hb : x < 866) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (842866 : ℝ) / 1000 ≤ Chebyshev.psi 849 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 849) (k := 1216) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 865 ≤ (870593 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 865) (k := 1255) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨849, 866, 842866, 870593, 23601, 23836⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 866. -/
private theorem cell866 {x : ℝ} (ha : 866 ≤ x) (hb : x < 883) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (869899 : ℝ) / 1000 ≤ Chebyshev.psi 866 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 866) (k := 1255) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 882 ≤ (883763 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 882) (k := 1274) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨866, 883, 869899, 883763, 23836, 24069⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 883. -/
private theorem cell883 {x : ℝ} (ha : 883 ≤ x) (hb : x < 911) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (890000 : ℝ) / 1000 ≤ Chebyshev.psi 883 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 883) (k := 1284) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 910 ≤ (904558 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 910) (k := 1304) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨883, 911, 890000, 904558, 24069, 24448⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 911. -/
private theorem cell911 {x : ℝ} (ha : 911 ≤ x) (hb : x < 935) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (910795 : ℝ) / 1000 ≤ Chebyshev.psi 911 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 911) (k := 1314) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 934 ≤ (924659 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 934) (k := 1333) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨911, 935, 910795, 924659, 24448, 24767⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 935. -/
private theorem cell935 {x : ℝ} (ha : 935 ≤ x) (hb : x < 948) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (923965 : ℝ) / 1000 ≤ Chebyshev.psi 935 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 935) (k := 1333) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 947 ≤ (945453 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 947) (k := 1363) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨935, 948, 923965, 945453, 24767, 24939⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 948. -/
private theorem cell948 {x : ℝ} (ha : 948 ≤ x) (hb : x < 969) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (944759 : ℝ) / 1000 ≤ Chebyshev.psi 948 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 948) (k := 1363) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 968 ≤ (962782 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 968) (k := 1388) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨948, 969, 944759, 962782, 24939, 25214⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 969. -/
private theorem cell969 {x : ℝ} (ha : 969 ≤ x) (hb : x < 987) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (962088 : ℝ) / 1000 ≤ Chebyshev.psi 969 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 969) (k := 1388) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 986 ≤ (982883 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 986) (k := 1417) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨969, 987, 962088, 982883, 25214, 25447⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 987. -/
private theorem cell987 {x : ℝ} (ha : 987 ≤ x) (hb : x < 1007) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (982189 : ℝ) / 1000 ≤ Chebyshev.psi 987 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 987) (k := 1417) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 1006 ≤ (996746 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 1006) (k := 1437) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact
    Arithmetic.psi81_cell_sound ⟨987, 1007, 982189, 996746, 25447, 25703⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 1007. -/
private theorem cell1007 {x : ℝ} (ha : 1007 ≤ x) (hb : x < 1021) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (996052 : ℝ) / 1000 ≤ Chebyshev.psi 1007 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 1007) (k := 1437) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 1020 ≤ (1017541 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 1020) (k := 1467) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact
    Arithmetic.psi81_cell_sound ⟨1007, 1021, 996052, 1017541, 25703, 25882⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 1021. -/
private theorem cell1021 {x : ℝ} (ha : 1021 ≤ x) (hb : x < 1049) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (1023778 : ℝ) / 1000 ≤ Chebyshev.psi 1021 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 1021) (k := 1477) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 1048 ≤ (1045960 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 1048) (k := 1508) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact
    Arithmetic.psi81_cell_sound ⟨1021, 1049, 1023778, 1045960, 25882, 26234⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 1049. -/
private theorem cell1049 {x : ℝ} (ha : 1049 ≤ x) (hb : x < 1069) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (1052197 : ℝ) / 1000 ≤ Chebyshev.psi 1049 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 1049) (k := 1518) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 1068 ≤ (1074379 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 1068) (k := 1549) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact
    Arithmetic.psi81_cell_sound ⟨1049, 1069, 1052197, 1074379, 26234, 26483⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 1069. -/
private theorem cell1069 {x : ℝ} (ha : 1069 ≤ x) (hb : x < 1093) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (1080616 : ℝ) / 1000 ≤ Chebyshev.psi 1069 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 1069) (k := 1559) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 1092 ≤ (1095173 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 1092) (k := 1579) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact
    Arithmetic.psi81_cell_sound ⟨1069, 1093, 1080616, 1095173, 26483, 26779⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 1093. -/
private theorem cell1093 {x : ℝ} (ha : 1093 ≤ x) (hb : x < 1109) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (1101410 : ℝ) / 1000 ≤ Chebyshev.psi 1093 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 1093) (k := 1589) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 1108 ≤ (1115967 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 1108) (k := 1609) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact
    Arithmetic.psi81_cell_sound ⟨1093, 1109, 1101410, 1115967, 26779, 26974⟩ (by decide) hl hu ha hb

/-- The checked cells cover every real point in the half-open interval [815, 1109). -/
theorem psi81_on_815_1109 {x : ℝ} (ha : 815 ≤ x) (hb : x < 1109) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ (81 / 100 : ℝ) := by
  have hx : 0 < x := by linarith only [ha]
  apply (div_le_iff₀ (Real.sqrt_pos.2 hx)).2
  by_cases h828 : x < 828
  · exact cell815 ha h828
  by_cases h849 : x < 849
  · exact cell828 (le_of_not_gt h828) h849
  by_cases h866 : x < 866
  · exact cell849 (le_of_not_gt h849) h866
  by_cases h883 : x < 883
  · exact cell866 (le_of_not_gt h866) h883
  by_cases h911 : x < 911
  · exact cell883 (le_of_not_gt h883) h911
  by_cases h935 : x < 935
  · exact cell911 (le_of_not_gt h911) h935
  by_cases h948 : x < 948
  · exact cell935 (le_of_not_gt h935) h948
  by_cases h969 : x < 969
  · exact cell948 (le_of_not_gt h948) h969
  by_cases h987 : x < 987
  · exact cell969 (le_of_not_gt h969) h987
  by_cases h1007 : x < 1007
  · exact cell987 (le_of_not_gt h987) h1007
  by_cases h1021 : x < 1021
  · exact cell1007 (le_of_not_gt h1007) h1021
  by_cases h1049 : x < 1049
  · exact cell1021 (le_of_not_gt h1021) h1049
  by_cases h1069 : x < 1069
  · exact cell1049 (le_of_not_gt h1049) h1069
  by_cases h1093 : x < 1093
  · exact cell1069 (le_of_not_gt h1069) h1093
  exact cell1093 (le_of_not_gt h1093) hb

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound
