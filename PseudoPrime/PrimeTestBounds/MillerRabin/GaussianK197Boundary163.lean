/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Boundary162
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.LowerPsiWalk

/-! # Signed Chebyshev bounds for compressed cell 163 -/

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def events1350247 : List (ℕ × ℕ × ℕ) :=
  ([1350257, 1350277, 1350287, 1350313, 1350317, 1350319, 1350331, 1350341, 1350343]).map
    (fun v ↦ (v, v, 1))

private theorem check_1350247 :
    lowerPsiEvents (-1000000000000000) 1350356 1350247 1349969144463903044 events1350247 =
      true := by
  decide +kernel

private theorem psi_ticks_1350356 :
    (1350096187062590006 : ℝ) ≤ scale * Chebyshev.psi (1350356 : ℕ) := by
  have h := lower_psi_events_exit events1350247 (by decide) psi_ticks_1350247 check_1350247
  have ht :
    events1350247.foldl (fun total row ↦ total + (certifiedTicks row.2.1).1) 1349969144463903044 =
      1350096187062590006 := by
    decide +kernel
  rw [ht] at h
  exact h

private def events1350356 : List (ℕ × ℕ × ℕ) :=
  ([1350367, 1350373, 1350379, 1350383, 1350403, 1350449, 1350457, 1350467, 1350469, 1350473,
          1350487, 1350509, 1350511, 1350521, 1350533, 1350541, 1350551, 1350553, 1350563, 1350593,
          1350607, 1350623, 1350641, 1350647, 1350677, 1350697, 1350703, 1350709, 1350731, 1350743,
          1350749, 1350751, 1350761, 1350773, 1350779, 1350799, 1350809, 1350823, 1350847, 1350851,
          1350857, 1350883, 1350889, 1350893, 1350911, 1350959, 1350961, 1350977, 1351019, 1351027,
          1351037, 1351039, 1351061, 1351069, 1351079, 1351087, 1351093, 1351099, 1351111, 1351117,
          1351121, 1351123, 1351127, 1351151, 1351169, 1351171, 1351183, 1351199, 1351213, 1351241,
          1351243, 1351247, 1351249, 1351253, 1351267, 1351283, 1351289, 1351291, 1351309, 1351327,
          1351373, 1351387, 1351397, 1351403, 1351417, 1351421, 1351423, 1351439, 1351459, 1351523,
          1351529, 1351541, 1351543, 1351547, 1351589, 1351621, 1351639, 1351663, 1351667, 1351697,
          1351703, 1351711, 1351747, 1351751, 1351781, 1351783, 1351799, 1351813, 1351829, 1351837,
          1351841, 1351843, 1351853, 1351897, 1351901, 1351913, 1351919, 1351921, 1351949, 1351957,
          1351967, 1351979, 1351981, 1351991, 1351997, 1352069, 1352093, 1352107, 1352111, 1352119,
          1352123, 1352149, 1352167, 1352171, 1352191, 1352201, 1352203, 1352207, 1352209, 1352227,
          1352257, 1352269, 1352279, 1352291, 1352293, 1352311, 1352317, 1352347, 1352359, 1352369,
          1352371, 1352383, 1352389, 1352419, 1352441, 1352443, 1352447, 1352459, 1352489, 1352521,
          1352543, 1352557]).map
      (fun v ↦ (v, v, 1)) ++
    [⟨1352569, 1163, 2⟩] ++
    ([1352597, 1352599, 1352627, 1352641, 1352657, 1352669]).map (fun v ↦ (v, v, 1))

private theorem check_1350356 :
    lowerPsiEvents (-283000000000000) 1352747 1350356 1350096187062590006 events1350356 = true := by
  decide +kernel

private theorem floor_1350356 {x : ℝ} (hx : 1350356 ≤ x) (hy : x ≤ 1352747) :
    -283 ≤ Chebyshev.psi x - x := by
  have h := lower_psi_events_sound events1350356 psi_ticks_1350356 check_1350356 hx hy
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  exact h

private theorem psi_ticks_1352747 :
    (1352474851669719458 : ℝ) ≤ scale * Chebyshev.psi (1352747 : ℕ) := by
  have h := lower_psi_events_exit events1350356 (by decide) psi_ticks_1350356 check_1350356
  have ht :
    events1350356.foldl (fun total row ↦ total + (certifiedTicks row.2.1).1) 1350096187062590006 =
      1352474851669719458 := by
    decide +kernel
  rw [ht] at h
  exact h

private def events1352747 : List (ℕ × ℕ × ℕ) :=
  []

private theorem check_1352747 :
    lowerPsiEvents (-275000000000000) 1352748 1352747 1352474851669719458 events1352747 = true := by
  decide +kernel

private theorem floor_1352747 {x : ℝ} (hx : 1352747 ≤ x) (hy : x ≤ 1352748) :
    -275 ≤ Chebyshev.psi x - x := by
  have h := lower_psi_events_sound events1352747 psi_ticks_1352747 check_1352747 hx hy
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  exact h

private theorem psi_ticks_1352748 :
    (1352474851669719458 : ℝ) ≤ scale * Chebyshev.psi (1352748 : ℕ) := by
  have h := lower_psi_events_exit events1352747 (by decide) psi_ticks_1352747 check_1352747
  have ht :
    events1352747.foldl (fun total row ↦ total + (certifiedTicks row.2.1).1) 1352474851669719458 =
      1352474851669719458 := by
    decide +kernel
  rw [ht] at h
  exact h

private def events1352748 : List (ℕ × ℕ × ℕ) :=
  ([1352749, 1352753, 1352761, 1352773, 1352777, 1352779, 1352783, 1352803, 1352807, 1352839,
        1352849, 1352861, 1352863, 1352873, 1352881, 1352893, 1352903, 1352917, 1352921, 1352957,
        1352963, 1352969, 1352977, 1352987, 1352993, 1352999, 1353007, 1353019, 1353029, 1353043,
        1353059, 1353089, 1353091, 1353101, 1353133, 1353137, 1353173, 1353179, 1353197, 1353221,
        1353223, 1353239, 1353241, 1353257, 1353259, 1353269, 1353277, 1353281, 1353293, 1353301,
        1353311, 1353329, 1353371, 1353377, 1353383, 1353397, 1353433, 1353449, 1353463, 1353479,
        1353487, 1353551, 1353581, 1353593, 1353607, 1353613, 1353629, 1353641, 1353679, 1353689,
        1353701, 1353707, 1353713, 1353733, 1353743, 1353763, 1353767, 1353791, 1353809, 1353827,
        1353839, 1353857, 1353881, 1353887, 1353893, 1353901, 1353917, 1353949, 1353967, 1353973,
        1353977, 1353983, 1354007, 1354009, 1354013, 1354019, 1354021, 1354037, 1354043, 1354051,
        1354057, 1354063, 1354069, 1354081, 1354127, 1354153, 1354159, 1354181, 1354193, 1354207,
        1354229, 1354231, 1354247, 1354267, 1354289, 1354291, 1354303, 1354307, 1354321, 1354333,
        1354337, 1354343, 1354349, 1354361, 1354391, 1354393, 1354471, 1354481, 1354487, 1354499,
        1354501, 1354523, 1354547, 1354571, 1354583, 1354589, 1354601, 1354603, 1354637, 1354649,
        1354651, 1354663, 1354687, 1354711, 1354741, 1354777, 1354811, 1354813, 1354819, 1354823,
        1354841, 1354853, 1354877, 1354889, 1354901, 1354931, 1354937, 1354939, 1354943, 1354949,
        1354957, 1354981, 1354987, 1355021, 1355047, 1355063, 1355071, 1355089, 1355113, 1355119,
        1355129, 1355131]).map
    (fun v ↦ (v, v, 1))

private theorem check_1352748 :
    lowerPsiEvents (-275000000000000) 1355142 1352748 1352474851669719458 events1352748 = true := by
  decide +kernel

private theorem floor_1352748 {x : ℝ} (hx : 1352748 ≤ x) (hy : x ≤ 1355142) :
    -275 ≤ Chebyshev.psi x - x := by
  have h := lower_psi_events_sound events1352748 psi_ticks_1352748 check_1352748 hx hy
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  exact h

/-- The signed Chebyshev bound on this part of compressed cell 163. -/
public theorem psi_gaussian_part163_0 {x : ℝ} (hl : 1350356 ≤ x) (hu : x ≤ 1352748) :
    -283 ≤ Chebyshev.psi x - x := by
  by_cases h1352747 : x ≤ 1352747
  · exact floor_1350356 hl h1352747
  exact (by norm_num only : (-283 : ℝ) ≤ -275).trans (floor_1352747 (le_of_not_ge h1352747) hu)

/-- The signed Chebyshev bound on this part of compressed cell 163. -/
public theorem psi_gaussian_part163_1 {x : ℝ} (hl : 1352747 ≤ x) (hu : x ≤ 1355142) :
    -275 ≤ Chebyshev.psi x - x := by
  by_cases h1352748 : x ≤ 1352748
  · exact floor_1352747 hl h1352748
  exact floor_1352748 (le_of_not_ge h1352748) hu

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
