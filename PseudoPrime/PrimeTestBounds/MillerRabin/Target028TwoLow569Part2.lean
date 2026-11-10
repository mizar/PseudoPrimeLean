/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GroupGrid

/-! # Checked low-weight grouped count -/

@[expose] public section

-- The finite chain has 95 short rows.
set_option maxRecDepth 65536

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The sampled base row for budget 174. -/
def target028TwoLow569Part2Base : Array ℕ :=
  #[28, 14634, 2223354]

/-- The final low-group count row for budget 174. -/
def target028TwoLow569Part2Row : Array ℕ :=
  #[28, 17294, 3741264]

/-- Intermediate rows for budget 174. -/
def target028TwoLow569Part2Rows : List (Array ℕ) :=
  [#[28, 17266, 3723970], #[28, 17238, 3706704], #[28, 17210, 3689466], #[28, 17182, 3672256],
    #[28, 17154, 3655074], #[28, 17126, 3637920], #[28, 17098, 3620794], #[28, 17070, 3603696],
    #[28, 17042, 3586626], #[28, 17014, 3569584], #[28, 16986, 3552570], #[28, 16958, 3535584],
    #[28, 16930, 3518626], #[28, 16902, 3501696], #[28, 16874, 3484794], #[28, 16846, 3467920],
    #[28, 16818, 3451074], #[28, 16790, 3434256], #[28, 16762, 3417466], #[28, 16734, 3400704],
    #[28, 16706, 3383970], #[28, 16678, 3367264], #[28, 16650, 3350586], #[28, 16622, 3333936],
    #[28, 16594, 3317314], #[28, 16566, 3300720], #[28, 16538, 3284154], #[28, 16510, 3267616],
    #[28, 16482, 3251106], #[28, 16454, 3234624], #[28, 16426, 3218170], #[28, 16398, 3201744],
    #[28, 16370, 3185346], #[28, 16342, 3168976], #[28, 16314, 3152634], #[28, 16286, 3136320],
    #[28, 16258, 3120034], #[28, 16230, 3103776], #[28, 16202, 3087546], #[28, 16174, 3071344],
    #[28, 16146, 3055170], #[28, 16118, 3039024], #[28, 16090, 3022906], #[28, 16062, 3006816],
    #[28, 16034, 2990754], #[28, 16006, 2974720], #[28, 15978, 2958714], #[28, 15950, 2942736],
    #[28, 15922, 2926786], #[28, 15894, 2910864], #[28, 15866, 2894970], #[28, 15838, 2879104],
    #[28, 15810, 2863266], #[28, 15782, 2847456], #[28, 15754, 2831674], #[28, 15726, 2815920],
    #[28, 15698, 2800194], #[28, 15670, 2784496], #[28, 15642, 2768826], #[28, 15614, 2753184],
    #[28, 15586, 2737570], #[28, 15558, 2721984], #[28, 15530, 2706426], #[28, 15502, 2690896],
    #[28, 15474, 2675394], #[28, 15446, 2659920], #[28, 15418, 2644474], #[28, 15390, 2629056],
    #[28, 15362, 2613666], #[28, 15334, 2598304], #[28, 15306, 2582970], #[28, 15278, 2567664],
    #[28, 15250, 2552386], #[28, 15222, 2537136], #[28, 15194, 2521914], #[28, 15166, 2506720],
    #[28, 15138, 2491554], #[28, 15110, 2476416], #[28, 15082, 2461306], #[28, 15054, 2446224],
    #[28, 15026, 2431170], #[28, 14998, 2416144], #[28, 14970, 2401146], #[28, 14942, 2386176],
    #[28, 14914, 2371234], #[28, 14886, 2356320], #[28, 14858, 2341434], #[28, 14830, 2326576],
    #[28, 14802, 2311746], #[28, 14774, 2296944], #[28, 14746, 2282170], #[28, 14718, 2267424],
    #[28, 14690, 2252706], #[28, 14662, 2238016], #[28, 14634, 2223354]]

-- The finite chain checks 95 short rows.
/-- The base and low-group recurrence rows pass their checks. -/
theorem target028TwoLow569Part2_checked :
    weightedGroupBaseCheck 70 34 500 2 primeSeed373Row14 target028TwoLow569Part2Base = true ∧
      weightedGroupRowsCheck 2 target028TwoLow569Part2Base target028TwoLow569Part2Row
          target028TwoLow569Part2Rows =
        true := by
  constructor <;> decide +kernel

/-- The row lower-bounds the weighted count after the 95 low-group labels. -/
theorem target028TwoLow569Part2_count :
    3741264 ≤ weightedPrimeCount id (List.replicate 95 70 ++ primeSeed373Weights) 174 := by
  have h :=
    target028_group_grid_general 70 34 2 95 (by decide) (by decide) target028TwoLow569Part2Base
      target028TwoLow569Part2Row target028TwoLow569Part2Rows (by decide)
      target028TwoLow569Part2_checked.1 target028TwoLow569Part2_checked.2
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
