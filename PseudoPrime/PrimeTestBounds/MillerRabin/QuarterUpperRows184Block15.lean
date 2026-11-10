/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWeightUpperCertificate

/-! # Upper principal rows at cutoff 184, block 15 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational weight certificates for a block of prime powers. -/
def quarterUpperRows184Block15 : List QuarterUpperWeightRow :=
  [⟨184, 2297, 4, 2523, 2526, 106, 111, 47927, 1111821874, 1⟩,
    ⟨184, 2309, 4, 2528, 2531, 101, 105, 48052, 1106276639, 1⟩,
    ⟨184, 2311, 4, 2529, 2532, 100, 104, 48072, 1105170916, 1⟩,
    ⟨184, 2333, 4, 2538, 2541, 90, 94, 48301, 1094174282, 1⟩,
    ⟨184, 2339, 4, 2541, 2544, 87, 91, 48363, 1090896678, 1⟩,
    ⟨184, 2341, 4, 2542, 2545, 86, 90, 48383, 1089806327, 1⟩,
    ⟨184, 2347, 4, 2544, 2547, 84, 88, 48445, 1087628892, 1⟩,
    ⟨184, 2351, 4, 2546, 2549, 82, 86, 48487, 1085455807, 1⟩,
    ⟨184, 2357, 4, 2549, 2552, 78, 83, 48548, 1081122658, 1⟩,
    ⟨184, 2371, 4, 2555, 2558, 72, 76, 48692, 1074655343, 1⟩,
    ⟨184, 2377, 4, 2557, 2560, 70, 74, 48754, 1072508180, 1⟩,
    ⟨184, 2381, 4, 2559, 2562, 68, 72, 48795, 1070365307, 1⟩,
    ⟨184, 2383, 4, 2560, 2563, 66, 71, 48815, 1068226716, 1⟩,
    ⟨184, 2389, 4, 2562, 2565, 64, 69, 48877, 1066092397, 1⟩,
    ⟨184, 2393, 4, 2564, 2567, 62, 66, 48918, 1063962343, 1⟩,
    ⟨184, 2399, 4, 2566, 2569, 60, 64, 48979, 1061836546, 1⟩,
    ⟨184, 2401, 4, 2567, 2570, 59, 63, 49000, 1060775238, 1⟩,
    ⟨184, 2411, 4, 2571, 2574, 55, 59, 49101, 1056540614, 1⟩,
    ⟨184, 2417, 4, 2574, 2577, 51, 56, 49162, 1052322891, 1⟩,
    ⟨184, 2423, 4, 2576, 2579, 49, 53, 49223, 1050220350, 1⟩,
    ⟨184, 2437, 4, 2582, 2585, 43, 47, 49365, 1043937894, 1⟩,
    ⟨184, 2441, 4, 2584, 2587, 41, 45, 49406, 1041852103, 1⟩,
    ⟨184, 2447, 4, 2586, 2589, 38, 43, 49467, 1038731231, 1⟩,
    ⟨184, 2459, 4, 2591, 2594, 33, 37, 49588, 1033550538, 1⟩,
    ⟨184, 2467, 4, 2594, 2597, 30, 34, 49668, 1030454533, 1⟩]

/-- Each listed row satisfies its rational weight checks. -/
theorem quarter_upper_rows184_block15_check :
    quarterUpperRows184Block15.all QuarterUpperWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
