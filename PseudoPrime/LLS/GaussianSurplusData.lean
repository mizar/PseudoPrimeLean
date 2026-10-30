/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GaussianSurplusIntervals

/-! # Kernel-checked finite Gaussian surplus payload -/

@[expose] public section

namespace PseudoPrime.LLS

/-- The 35 existing seed indices receive consecutive ten-millionth power endpoints.
Each row is checked separately by natural-number arithmetic below; no real oracle is used. -/
def gaussianSurplusNumerators (m : ℕ) : List ℕ :=
  if m = 2 then
    [4829681, 4367864, 4061261, 3855527, 3535533, 3298769, 2707437, 2176376, 2102241, 1533606,
      1435872, 1033062, 769465, 625000, 332615, 312500, 150405, 55242]
  else
    if m = 4 then
      [2332582, 1907824, 1649384, 1486508, 1250000, 1088188, 733021, 473661, 441941, 235194, 206173,
        106721, 59207, 39062, 11063, 9765, 2262, 305]
    else
      if m = 8 then
        [1126563, 833311, 669858, 573127, 441941, 358968, 198461, 103086, 92906, 36069, 29603,
          11025, 4555, 2441, 367, 305, 34, 1]
      else
        if m = 16 then
          [544094, 363979, 272047, 220970, 156250, 118415, 53732, 22435, 19531, 5531, 4250, 1138,
            350, 152, 12, 9, 0, 0]
        else
          if m = 32 then
            [262780, 158981, 110485, 85195, 55242, 39062, 14547, 4882, 4105, 848, 610, 117, 26, 9,
              0, 0, 0, 0]
          else
            if m = 64 then
              [126914, 69440, 44871, 32847, 19531, 12885, 3938, 1062, 863, 130, 87, 12, 2, 0, 0, 0,
                0, 0]
            else
              if m = 3 then
                [3155169, 2690544, 2397410, 2207792, 1924500, 1724272, 1260742, 891935, 844261,
                  512138, 461381, 273796, 171652, 123456, 45429, 41152, 12913, 2639]
              else
                if m = 9 then
                  [995509, 723902, 574757, 487434, 370370, 297311, 158947, 79554, 71277, 26228,
                    21287, 7496, 2946, 1524, 206, 169, 16, 0]
                else
                  if m = 27 then
                    [314100, 194769, 137792, 107615, 71277, 51264, 20039, 7095, 6017, 1343, 982,
                      205, 50, 18, 0, 0, 0, 0]
                  else
                    if m = 81 then
                      [99103, 52403, 33034, 23759, 13717, 8839, 2526, 632, 508, 68, 45, 5, 0, 0, 0,
                        0, 0, 0]
                    else
                      if m = 5 then
                        [1845361, 1461271, 1234067, 1093745, 894427, 761461, 481328, 289911, 267496,
                          128613, 110378, 51389, 25930, 16000, 3698, 3200, 585, 57]
                      else
                        if m = 25 then
                          [340535, 213531, 152292, 119627, 80000, 57982, 23167, 8404, 7155, 1654,
                            1218, 264, 67, 25, 1, 1, 0, 0]
                        else
                          if m = 7 then
                            [1296125, 977479, 796842, 688636, 539949, 444470, 255264, 138287,
                              125466, 51761, 43025, 17072, 7466, 4164, 708, 594, 76, 4]
                          else
                            if m = 49 then
                              [167994, 95546, 63495, 47422, 29154, 19755, 6515, 1912, 1574, 267,
                                185, 29, 5, 1, 0, 0, 0, 0]
                            else
                              if m = 11 then
                                [806376, 569555, 442781, 369900, 274101, 215661, 108886, 51160,
                                  45380, 15241, 12136, 3885, 1402, 683, 77, 62, 4, 0]
                              else
                                if m = 13 then
                                  [676642, 466485, 356347, 293986, 213346, 165078, 79472, 35426,
                                    31162, 9700, 7602, 2248, 755, 350, 33, 26, 1, 0]
                                else
                                  if m = 17 then
                                    [510538, 338542, 251429, 203297, 142668, 107468, 47929, 19634,
                                      17040, 4695, 3587, 933, 280, 119, 9, 7, 0, 0]
                                  else
                                    if m = 19 then
                                      [454264, 296407, 217580, 174467, 120745, 89948, 38864, 15372,
                                        13267, 3475, 2627, 648, 185, 76, 5, 4, 0, 0]
                                    else
                                      if m = 23 then
                                        [371694, 235903, 169728, 134160, 90658, 66257, 27110, 10097,
                                          8632, 2072, 1538, 347, 91, 35, 2, 1, 0, 0]
                                      else
                                        if m = 29 then
                                          [291395, 178827, 125569, 97544, 64032, 45725, 17513, 6063,
                                            5123, 1107, 804, 162, 38, 14, 0, 0, 0, 0]
                                        else
                                          if m = 31 then
                                            [271687, 165128, 115140, 88997, 57937, 41098, 15444,
                                              5236, 4409, 924, 667, 130, 30, 10, 0, 0, 0, 0]
                                          else
                                            if m = 37 then
                                              [225625, 133659, 91482, 69778, 44432, 30965, 11064,
                                                3547, 2961, 572, 406, 73, 15, 5, 0, 0, 0, 0]
                                            else
                                              if m = 41 then
                                                [202570, 118228, 80053, 60592, 38091, 26275, 9118,
                                                  2830, 2350, 433, 304, 52, 10, 3, 0, 0, 0, 0]
                                              else
                                                if m = 43 then
                                                  [192689, 111687, 75247, 56751, 35464, 24347, 8335,
                                                    2548, 2112, 381, 266, 44, 9, 2, 0, 0, 0, 0]
                                                else
                                                  if m = 47 then
                                                    [175508, 100425, 67030, 50218, 31035, 21117,
                                                      7048, 2095, 1728, 299, 208, 33, 6, 2, 0, 0, 0,
                                                      0]
                                                  else
                                                    if m = 53 then
                                                      [154707, 86994, 57337, 42571, 25917, 17424,
                                                        5620, 1609, 1319, 216, 148, 22, 4, 1, 0, 0,
                                                        0, 0]
                                                    else
                                                      if m = 59 then
                                                        [138230, 76530, 49876, 36734, 22065, 14676,
                                                          4591, 1270, 1036, 162, 110, 15, 2, 0, 0,
                                                          0, 0, 0]
                                                      else
                                                        if m = 61 then
                                                          [133476, 73541, 47760, 35089, 20989,
                                                            13914, 4311, 1181, 961, 148, 100, 14, 2,
                                                            0, 0, 0, 0, 0]
                                                        else
                                                          if m = 67 then
                                                            [120954, 65741, 42276, 30842, 18234,
                                                              11975, 3612, 960, 778, 114, 77, 10, 1,
                                                              0, 0, 0, 0, 0]
                                                          else
                                                            if m = 71 then
                                                              [113809, 61340, 39207, 28478, 16715,
                                                                10914, 3238, 845, 683, 98, 65, 8, 1,
                                                                0, 0, 0, 0, 0]
                                                            else
                                                              if m = 73 then
                                                                [110537, 59337, 37816, 27411, 16033,
                                                                  10439, 3073, 795, 641, 91, 60, 7,
                                                                  1, 0, 0, 0, 0, 0]
                                                              else
                                                                if m = 79 then
                                                                  [101739, 53992, 34125, 24590,
                                                                    14241, 9200, 2648, 668, 537, 73,
                                                                    48, 6, 0, 0, 0, 0, 0, 0]
                                                                else
                                                                  if m = 83 then
                                                                    [96597, 50898, 32003, 22975,
                                                                      13224, 8501, 2412, 599, 480,
                                                                      64, 42, 5, 0, 0, 0, 0, 0, 0]
                                                                  else
                                                                    if m = 89 then
                                                                      [89771, 46825, 29227, 20873,
                                                                        11910, 7602, 2115, 514, 411,
                                                                        53, 34, 4, 0, 0, 0, 0, 0, 0]
                                                                    else
                                                                      if m = 97 then
                                                                        [82014, 42248, 26133, 18543,
                                                                          10467, 6624, 1798, 425,
                                                                          338, 42, 27, 3, 0, 0, 0,
                                                                          0, 0, 0]
                                                                      else []

/-- Select the generated lower numerator at the fixed aggregated node order. -/
def gaussianSurplusNumerator (m : ℕ) (a : ℚ) : ℕ :=
  (gaussianSurplusNumerators m)[(gaussianSurplusCoefficients.map Prod.fst).idxOf a]?.getD 0

/-- The two rational power endpoints associated with a generated lower numerator. -/
def gaussianSurplusRatios (m : ℕ) (a : ℚ) : ℚ × ℚ :=
  ((gaussianSurplusNumerator m a : ℚ) / 10000000,
    ((gaussianSurplusNumerator m a + 1 : ℕ) : ℚ) / 10000000)

/-- Validate both integer power inequalities at all eighteen aggregated nodes.
The exponent is computed from the exact denominator-200 grid identity. -/
def gaussianSurplusNatCheck (m : ℕ) : Bool :=
  decide
    (gaussianSurplusCoefficients.Forall
      (fun ab ↦
        let q := gaussianSurplusNumerator m ab.1
        let e := Analysis.finiteEulerExponent 200 ab.1
        q ^ 200 * m ^ e ≤ (10000000 : ℕ) ^ 200 ∧ (10000000 : ℕ) ^ 200 ≤ (q + 1) ^ 200 * m ^ e))

/-- Every aggregated node has the displayed exact integer denominator-200 exponent. -/
theorem gaussianSurplus_exponents :
    gaussianSurplusCoefficients.Forall
      (fun ab ↦ (200 : ℚ) * (1 / 2 + ab.1) = (Analysis.finiteEulerExponent 200 ab.1 : ℚ)) := by
  decide +kernel

/-- Kernel-checked integer endpoint certificate for the existing seed index 2. -/
theorem gaussianSurplus_check_2 : gaussianSurplusNatCheck 2 = true := by decide +kernel

/-- Kernel-checked integer endpoint certificate for the existing seed index 4. -/
theorem gaussianSurplus_check_4 : gaussianSurplusNatCheck 4 = true := by decide +kernel

/-- Kernel-checked integer endpoint certificate for the existing seed index 8. -/
theorem gaussianSurplus_check_8 : gaussianSurplusNatCheck 8 = true := by decide +kernel

/-- Kernel-checked integer endpoint certificate for the existing seed index 16. -/
theorem gaussianSurplus_check_16 : gaussianSurplusNatCheck 16 = true := by decide +kernel

/-- Kernel-checked integer endpoint certificate for the existing seed index 32. -/
theorem gaussianSurplus_check_32 : gaussianSurplusNatCheck 32 = true := by decide +kernel

/-- Kernel-checked integer endpoint certificate for the existing seed index 64. -/
theorem gaussianSurplus_check_64 : gaussianSurplusNatCheck 64 = true := by decide +kernel

/-- Kernel-checked integer endpoint certificate for the existing seed index 3. -/
theorem gaussianSurplus_check_3 : gaussianSurplusNatCheck 3 = true := by decide +kernel

/-- Kernel-checked integer endpoint certificate for the existing seed index 9. -/
theorem gaussianSurplus_check_9 : gaussianSurplusNatCheck 9 = true := by decide +kernel

/-- Kernel-checked integer endpoint certificate for the existing seed index 27. -/
theorem gaussianSurplus_check_27 : gaussianSurplusNatCheck 27 = true := by decide +kernel

/-- Kernel-checked integer endpoint certificate for the existing seed index 81. -/
theorem gaussianSurplus_check_81 : gaussianSurplusNatCheck 81 = true := by decide +kernel

/-- Kernel-checked integer endpoint certificate for the existing seed index 5. -/
theorem gaussianSurplus_check_5 : gaussianSurplusNatCheck 5 = true := by decide +kernel

/-- Kernel-checked integer endpoint certificate for the existing seed index 25. -/
theorem gaussianSurplus_check_25 : gaussianSurplusNatCheck 25 = true := by decide +kernel

/-- Kernel-checked integer endpoint certificate for the existing seed index 7. -/
theorem gaussianSurplus_check_7 : gaussianSurplusNatCheck 7 = true := by decide +kernel

/-- Kernel-checked integer endpoint certificate for the existing seed index 49. -/
theorem gaussianSurplus_check_49 : gaussianSurplusNatCheck 49 = true := by decide +kernel

/-- Kernel-checked integer endpoint certificate for the existing seed index 11. -/
theorem gaussianSurplus_check_11 : gaussianSurplusNatCheck 11 = true := by decide +kernel

/-- Kernel-checked integer endpoint certificate for the existing seed index 13. -/
theorem gaussianSurplus_check_13 : gaussianSurplusNatCheck 13 = true := by decide +kernel

/-- Kernel-checked integer endpoint certificate for the existing seed index 17. -/
theorem gaussianSurplus_check_17 : gaussianSurplusNatCheck 17 = true := by decide +kernel

/-- Kernel-checked integer endpoint certificate for the existing seed index 19. -/
theorem gaussianSurplus_check_19 : gaussianSurplusNatCheck 19 = true := by decide +kernel

/-- Kernel-checked integer endpoint certificate for the existing seed index 23. -/
theorem gaussianSurplus_check_23 : gaussianSurplusNatCheck 23 = true := by decide +kernel

/-- Kernel-checked integer endpoint certificate for the existing seed index 29. -/
theorem gaussianSurplus_check_29 : gaussianSurplusNatCheck 29 = true := by decide +kernel

/-- Kernel-checked integer endpoint certificate for the existing seed index 31. -/
theorem gaussianSurplus_check_31 : gaussianSurplusNatCheck 31 = true := by decide +kernel

/-- Kernel-checked integer endpoint certificate for the existing seed index 37. -/
theorem gaussianSurplus_check_37 : gaussianSurplusNatCheck 37 = true := by decide +kernel

/-- Kernel-checked integer endpoint certificate for the existing seed index 41. -/
theorem gaussianSurplus_check_41 : gaussianSurplusNatCheck 41 = true := by decide +kernel

/-- Kernel-checked integer endpoint certificate for the existing seed index 43. -/
theorem gaussianSurplus_check_43 : gaussianSurplusNatCheck 43 = true := by decide +kernel

/-- Kernel-checked integer endpoint certificate for the existing seed index 47. -/
theorem gaussianSurplus_check_47 : gaussianSurplusNatCheck 47 = true := by decide +kernel

/-- Kernel-checked integer endpoint certificate for the existing seed index 53. -/
theorem gaussianSurplus_check_53 : gaussianSurplusNatCheck 53 = true := by decide +kernel

/-- Kernel-checked integer endpoint certificate for the existing seed index 59. -/
theorem gaussianSurplus_check_59 : gaussianSurplusNatCheck 59 = true := by decide +kernel

/-- Kernel-checked integer endpoint certificate for the existing seed index 61. -/
theorem gaussianSurplus_check_61 : gaussianSurplusNatCheck 61 = true := by decide +kernel

/-- Kernel-checked integer endpoint certificate for the existing seed index 67. -/
theorem gaussianSurplus_check_67 : gaussianSurplusNatCheck 67 = true := by decide +kernel

/-- Kernel-checked integer endpoint certificate for the existing seed index 71. -/
theorem gaussianSurplus_check_71 : gaussianSurplusNatCheck 71 = true := by decide +kernel

/-- Kernel-checked integer endpoint certificate for the existing seed index 73. -/
theorem gaussianSurplus_check_73 : gaussianSurplusNatCheck 73 = true := by decide +kernel

/-- Kernel-checked integer endpoint certificate for the existing seed index 79. -/
theorem gaussianSurplus_check_79 : gaussianSurplusNatCheck 79 = true := by decide +kernel

/-- Kernel-checked integer endpoint certificate for the existing seed index 83. -/
theorem gaussianSurplus_check_83 : gaussianSurplusNatCheck 83 = true := by decide +kernel

/-- Kernel-checked integer endpoint certificate for the existing seed index 89. -/
theorem gaussianSurplus_check_89 : gaussianSurplusNatCheck 89 = true := by decide +kernel

/-- Kernel-checked integer endpoint certificate for the existing seed index 97. -/
theorem gaussianSurplus_check_97 : gaussianSurplusNatCheck 97 = true := by decide +kernel

/-- All existing seed rows have separately checked integer power certificates. -/
theorem gaussianSurplus_all_checks :
    Analysis.smallSeedRows.Forall (fun r ↦ gaussianSurplusNatCheck r.index = true) := by
  norm_num only [Analysis.smallSeedRows, Analysis.smallSeedRow, Analysis.GammaFiniteEulerRow.index,
    Nat.reducePow, List.forall_cons, gaussianSurplus_check_2, gaussianSurplus_check_4,
    gaussianSurplus_check_8, gaussianSurplus_check_16, gaussianSurplus_check_32,
    gaussianSurplus_check_64, gaussianSurplus_check_3, gaussianSurplus_check_9,
    gaussianSurplus_check_27, gaussianSurplus_check_81, gaussianSurplus_check_5,
    gaussianSurplus_check_25, gaussianSurplus_check_7, gaussianSurplus_check_49,
    gaussianSurplus_check_11, gaussianSurplus_check_13, gaussianSurplus_check_17,
    gaussianSurplus_check_19, gaussianSurplus_check_23, gaussianSurplus_check_29,
    gaussianSurplus_check_31, gaussianSurplus_check_37, gaussianSurplus_check_41,
    gaussianSurplus_check_43, gaussianSurplus_check_47, gaussianSurplus_check_53,
    gaussianSurplus_check_59, gaussianSurplus_check_61, gaussianSurplus_check_67,
    gaussianSurplus_check_71, gaussianSurplus_check_73, gaussianSurplus_check_79,
    gaussianSurplus_check_83, gaussianSurplus_check_89, gaussianSurplus_check_97, and_self,
    true_and]
  exact True.intro

/-- Every signed rational Euler lower bound is nonnegative, and the total Mangoldt allowance
is at least 0.73. These checks involve only the small rational endpoint payload. -/
theorem gaussianSurplus_rational_checks :
    Analysis.smallSeedRows.Forall
        (fun r ↦
          0 ≤
            Analysis.finiteSignedEulerLower gaussianSurplusCoefficients
              (gaussianSurplusRatios r.index)) ∧
      (73 / 100 : ℚ) ≤
        (Analysis.smallSeedRows.map
            (fun r ↦
              r.logLower *
                Analysis.finiteSignedEulerLower gaussianSurplusCoefficients
                  (gaussianSurplusRatios r.index))).sum := by
  decide +kernel

end PseudoPrime.LLS
