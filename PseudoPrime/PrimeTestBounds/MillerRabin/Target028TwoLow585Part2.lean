/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GroupGrid

/-! # Checked low-weight grouped count -/

@[expose] public section

-- The finite chain has 109 short rows.
set_option maxRecDepth 65536

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The sampled base row for budget 185. -/
def target028TwoLow585Part2Base : Array ℕ :=
  #[87, 34271, 4581888]

/-- The final low-group count row for budget 185. -/
def target028TwoLow585Part2Row : Array ℕ :=
  #[87, 43754, 8838992]

/-- Intermediate rows for budget 185. -/
def target028TwoLow585Part2Rows : List (Array ℕ) :=
  [#[87, 43667, 8795238], #[87, 43580, 8751571], #[87, 43493, 8707991], #[87, 43406, 8664498],
    #[87, 43319, 8621092], #[87, 43232, 8577773], #[87, 43145, 8534541], #[87, 43058, 8491396],
    #[87, 42971, 8448338], #[87, 42884, 8405367], #[87, 42797, 8362483], #[87, 42710, 8319686],
    #[87, 42623, 8276976], #[87, 42536, 8234353], #[87, 42449, 8191817], #[87, 42362, 8149368],
    #[87, 42275, 8107006], #[87, 42188, 8064731], #[87, 42101, 8022543], #[87, 42014, 7980442],
    #[87, 41927, 7938428], #[87, 41840, 7896501], #[87, 41753, 7854661], #[87, 41666, 7812908],
    #[87, 41579, 7771242], #[87, 41492, 7729663], #[87, 41405, 7688171], #[87, 41318, 7646766],
    #[87, 41231, 7605448], #[87, 41144, 7564217], #[87, 41057, 7523073], #[87, 40970, 7482016],
    #[87, 40883, 7441046], #[87, 40796, 7400163], #[87, 40709, 7359367], #[87, 40622, 7318658],
    #[87, 40535, 7278036], #[87, 40448, 7237501], #[87, 40361, 7197053], #[87, 40274, 7156692],
    #[87, 40187, 7116418], #[87, 40100, 7076231], #[87, 40013, 7036131], #[87, 39926, 6996118],
    #[87, 39839, 6956192], #[87, 39752, 6916353], #[87, 39665, 6876601], #[87, 39578, 6836936],
    #[87, 39491, 6797358], #[87, 39404, 6757867], #[87, 39317, 6718463], #[87, 39230, 6679146],
    #[87, 39143, 6639916], #[87, 39056, 6600773], #[87, 38969, 6561717], #[87, 38882, 6522748],
    #[87, 38795, 6483866], #[87, 38708, 6445071], #[87, 38621, 6406363], #[87, 38534, 6367742],
    #[87, 38447, 6329208], #[87, 38360, 6290761], #[87, 38273, 6252401], #[87, 38186, 6214128],
    #[87, 38099, 6175942], #[87, 38012, 6137843], #[87, 37925, 6099831], #[87, 37838, 6061906],
    #[87, 37751, 6024068], #[87, 37664, 5986317], #[87, 37577, 5948653], #[87, 37490, 5911076],
    #[87, 37403, 5873586], #[87, 37316, 5836183], #[87, 37229, 5798867], #[87, 37142, 5761638],
    #[87, 37055, 5724496], #[87, 36968, 5687441], #[87, 36881, 5650473], #[87, 36794, 5613592],
    #[87, 36707, 5576798], #[87, 36620, 5540091], #[87, 36533, 5503471], #[87, 36446, 5466938],
    #[87, 36359, 5430492], #[87, 36272, 5394133], #[87, 36185, 5357861], #[87, 36098, 5321676],
    #[87, 36011, 5285578], #[87, 35924, 5249567], #[87, 35837, 5213643], #[87, 35750, 5177806],
    #[87, 35663, 5142056], #[87, 35576, 5106393], #[87, 35489, 5070817], #[87, 35402, 5035328],
    #[87, 35315, 4999926], #[87, 35228, 4964611], #[87, 35141, 4929383], #[87, 35054, 4894242],
    #[87, 34967, 4859188], #[87, 34880, 4824221], #[87, 34793, 4789341], #[87, 34706, 4754548],
    #[87, 34619, 4719842], #[87, 34532, 4685223], #[87, 34445, 4650691], #[87, 34358, 4616246],
    #[87, 34271, 4581888]]

set_option maxHeartbeats 0 in
-- The finite chain checks 109 short rows.
/-- The base and low-group recurrence rows pass their checks. -/
theorem target028TwoLow585Part2_checked :
    weightedGroupBaseCheck 70 45 500 2 target030Seed373Row14 target028TwoLow585Part2Base = true ∧
      weightedGroupRowsCheck 2 target028TwoLow585Part2Base target028TwoLow585Part2Row
          target028TwoLow585Part2Rows =
        true := by
  constructor <;> decide +kernel

/-- The row lower-bounds the weighted count after the 109 low-group labels. -/
theorem target028TwoLow585Part2_count :
    8838992 ≤ weightedPrimeCount id (List.replicate 109 70 ++ target030Seed373Weights) 185 := by
  have h :=
    target028_group_grid_general 70 45 2 109 (by decide) (by decide) target028TwoLow585Part2Base
      target028TwoLow585Part2Row target028TwoLow585Part2Rows (by decide)
      target028TwoLow585Part2_checked.1 target028TwoLow585Part2_checked.2
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
