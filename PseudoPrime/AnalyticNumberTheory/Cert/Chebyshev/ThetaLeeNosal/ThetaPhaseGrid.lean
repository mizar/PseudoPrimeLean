/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import Mathlib.Data.Nat.Basic

/-! # Generated Lee–Nosal phase grid

Adjacent ticks divided by 512 give the closed phase intervals.
Regenerate with generate_theta_phase_grid.py.
-/

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

/-- Endpoints in units of 1/512, shared by neighboring phase cells. -/
private def phaseTicks : Array Nat :=
  #[8960, 8969, 8978, 8987, 8996, 9005, 9014, 9023, 9032, 9041, 9050, 9059, 9068, 9077, 9086, 9095,
    9104, 9113, 9122, 9131, 9140, 9149, 9158, 9167, 9176, 9185, 9194, 9203, 9212, 9221, 9230, 9239,
    9248, 9257, 9266, 9275, 9284, 9293, 9302, 9311, 9320, 9329, 9338, 9347, 9356, 9365, 9374, 9383,
    9392, 9401, 9410, 9419, 9428, 9437, 9446, 9455, 9464, 9473, 9482, 9491, 9500, 9509, 9518, 9527,
    9536, 9545, 9554, 9563, 9572, 9581, 9590, 9599, 9608, 9617, 9626, 9635, 9644, 9653, 9662, 9671,
    9680, 9689, 9698, 9707, 9716, 9734, 9752, 9770, 9779, 9788, 9797, 9806, 9815, 9824, 9833, 9842,
    9851, 9860, 9869, 9878, 9896, 9914, 9932, 9950, 9968, 9977, 9986, 9995, 10004, 10022, 10031,
    10040, 10049, 10058, 10067, 10076, 10085, 10094, 10103, 10112, 10130, 10148, 10166, 10184,
    10202, 10220, 10238, 10256, 10265, 10274, 10283, 10292, 10301, 10310, 10319, 10328, 10337,
    10346, 10364, 10382, 10400, 10418, 10436, 10454, 10463, 10472, 10481, 10490, 10508, 10526,
    10544, 10562, 10580, 10598, 10616, 10634, 10652, 10670, 10688, 10706, 10715, 10724, 10733,
    10742, 10760, 10778, 10796, 10814, 10832, 10850, 10868, 10886, 10904, 10922, 10940, 10958,
    10976, 10994, 11012, 11030, 11048, 11066, 11084, 11102, 11120, 11138, 11156, 11174, 11192,
    11210, 11228, 11246, 11264, 11282, 11300, 11318, 11336, 11354, 11372, 11390, 11408, 11426,
    11444, 11462, 11480, 11498, 11516, 11534, 11552, 11570, 11588, 11606, 11624, 11642, 11660,
    11678, 11696, 11714, 11732, 11750, 11768, 11786, 11804, 11822, 11840, 11858, 11876, 11894,
    11912, 11930, 11948, 11966, 11984, 12002, 12020, 12038, 12056, 12074, 12092, 12110, 12128,
    12146, 12164, 12182, 12200, 12218, 12236, 12254, 12272, 12290, 12308, 12326, 12344, 12362,
    12380, 12398, 12416, 12434, 12452, 12470, 12488, 12506, 12524, 12542, 12560, 12578, 12596,
    12614, 12632, 12650, 12668, 12686, 12704, 12722, 12740, 12758, 12776, 12794, 12812, 12830,
    12848, 12866, 12884, 12902, 12920, 12938, 12956, 12974, 12992, 13010, 13028, 13046, 13064,
    13082, 13100, 13118, 13136, 13154, 13172, 13190, 13208, 13226, 13244, 13262, 13280, 13298,
    13316, 13334, 13352, 13370, 13388, 13406, 13424, 13442, 13460, 13478, 13496, 13514, 13532,
    13550, 13568]

private theorem phaseTicks_size : phaseTicks.size = 321 := by decide +kernel

/-- Read the scaled endpoint of index 0 through 320 for the phase checker. -/
public def phaseTick (i : Fin 321) : Nat :=
  phaseTicks[i.val]'(phaseTicks_size.symm ▸ i.isLt)

/-- The first grid endpoint is 35/2 in units of 1/512. -/
public theorem phaseTick_first : phaseTick 0 = 8960 := by decide +kernel

/-- The final grid endpoint is 53/2 in units of 1/512. -/
public theorem phaseTick_last : phaseTick (Fin.last 320) = 13568 := by decide +kernel

/-- Every cell advances by nine or eighteen ticks on the common grid. -/
public theorem phaseTick_step (i : Fin 320) :
    phaseTick i.succ = phaseTick i.castSucc + 9 ∨ phaseTick i.succ = phaseTick i.castSucc + 18 := by
  exact
    (show
        ∀ j : Fin 320,
          phaseTick j.succ = phaseTick j.castSucc + 9 ∨ phaseTick j.succ = phaseTick j.castSucc + 18
        from by decide +kernel)
      i

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
