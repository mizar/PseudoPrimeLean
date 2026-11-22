/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.LowPrefix

/-! # Joint prefix verification from 101 through 1422 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private theorem checkedSegment {a b : ℕ} (hu : b ≤ 1000001) (extra : ℕ → ℕ) (count : ℕ) {s t : Edge}
    (hg : batchAccepted a b extra (fun _ ↦ (81, 100)) count s t = true) :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x) s t := by
  exact accepted_segment hu (fun _ _ _ _ _ _ h ↦ h.1) hg

private def extra101 : ℕ → ℕ
  | 101 => 2
  | 104 => 4
  | 109 => 3
  | 113 => 7
  | 121 => 4
  | 126 => 1
  | 128 => 5
  | 134 => 4
  | 139 => 9
  | 149 => 5
  | 155 => 4
  | 160 => 4
  | _ => 0

private theorem part101 :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x)
      ⟨101, 94045306083764, 94045894722428, 10316920830281, 10316920830303⟩
      ⟨165, 161832247362565, 161834062362999, 15017401196067, 15017401196098⟩ := by
  apply checkedSegment (a := 101) (b := 165) (by decide) extra101 12
  decide +kernel

private def extra165 : ℕ → ℕ
  | 165 => 5
  | 171 => 7
  | 179 => 9
  | 189 => 5
  | 195 => 3
  | 199 => 11
  | 211 => 11
  | 223 => 5
  | _ => 0

private theorem part165 :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x)
      ⟨165, 161832247362565, 161834062362999, 15017401196067, 15017401196098⟩
      ⟨229, 222329808061730, 222332525689894, 17582350553525, 17582350553560⟩ := by
  apply checkedSegment (a := 165) (b := 229) (by decide) extra165 8
  decide +kernel

private def extra229 : ℕ → ℕ
  | 229 => 10
  | 240 => 10
  | 251 => 11
  | 263 => 12
  | 276 => 6
  | 283 => 9
  | _ => 0

private theorem part229 :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x)
      ⟨229, 222329808061730, 222332525689894, 17582350553525, 17582350553560⟩
      ⟨293, 293552115317843, 293556159573925, 22207323366803, 22207323366847⟩ := by
  apply checkedSegment (a := 229) (b := 293) (by decide) extra229 6
  decide +kernel

private def extra293 : ℕ → ℕ
  | 293 => 17
  | 311 => 13
  | 325 => 11
  | 337 => 10
  | 348 => 7
  | _ => 0

private theorem part293 :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x)
      ⟨293, 293552115317843, 293556159573925, 22207323366803, 22207323366847⟩
      ⟨356, 353343000855909, 353347837112421, 24153233515856, 24153233515903⟩ := by
  apply checkedSegment (a := 293) (b := 356) (by decide) extra293 5
  decide +kernel

private def extra356 : ℕ → ℕ
  | 356 => 11
  | 368 => 14
  | 383 => 17
  | 401 => 18
  | _ => 0

private theorem part356 :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x)
      ⟨356, 353343000855909, 353347837112421, 24153233515856, 24153233515903⟩
      ⟨420, 415876327149097, 415882045861262, 27097672495018, 27097672495070⟩ := by
  apply checkedSegment (a := 356) (b := 420) (by decide) extra356 4
  decide +kernel

private def extra420 : ℕ → ℕ
  | 420 => 11
  | 432 => 12
  | 445 => 15
  | 461 => 17
  | _ => 0

private theorem part420 :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x)
      ⟨420, 415876327149097, 415882045861262, 27097672495018, 27097672495070⟩
      ⟨479, 476883030326895, 476889318490450, 27097672495018, 27097672495070⟩ := by
  apply checkedSegment (a := 420) (b := 479) (by decide) extra420 4
  decide +kernel

private def extra479 : ℕ → ℕ
  | 479 => 19
  | 499 => 20
  | 520 => 12
  | _ => 0

private theorem part479 :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x)
      ⟨479, 476883030326895, 476889318490450, 27097672495018, 27097672495070⟩
      ⟨533, 530449047820924, 530456123561927, 30926313891502, 30926313891561⟩ := by
  apply checkedSegment (a := 479) (b := 533) (by decide) extra479 3
  decide +kernel

private def extra533 : ℕ → ℕ
  | 533 => 15
  | 549 => 12
  | 562 => 5
  | 568 => 6
  | 575 => 12
  | _ => 0

private theorem part533 :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x)
      ⟨533, 530449047820924, 530456123561927, 30926313891502, 30926313891561⟩
      ⟨588, 581126881892028, 581135081750669, 30926313891502, 30926313891561⟩ := by
  apply checkedSegment (a := 533) (b := 588) (by decide) extra533 5
  decide +kernel

private def extra588 : ℕ → ℕ
  | 588 => 11
  | 600 => 12
  | 613 => 17
  | 631 => 15
  | _ => 0

private theorem part588 :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x)
      ⟨588, 581126881892028, 581135081750669, 30926313891502, 30926313891561⟩
      ⟨647, 646971708072803, 646980797993453, 32535751803934, 32535751803996⟩ := by
  apply checkedSegment (a := 588) (b := 647) (by decide) extra588 4
  decide +kernel

private def extra647 : ℕ → ℕ
  | 647 => 13
  | 661 => 15
  | 677 => 13
  | _ => 0

private theorem part647 :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x)
      ⟨647, 646971708072803, 646980797993453, 32535751803934, 32535751803996⟩
      ⟨691, 692466015388187, 692475573686627, 32535751803934, 32535751803996⟩ := by
  apply checkedSegment (a := 647) (b := 691) (by decide) extra647 3
  decide +kernel

private def extra691 : ℕ → ℕ
  | 691 => 27
  | 719 => 20
  | _ => 0

private theorem part691 :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x)
      ⟨691, 692466015388187, 692475573686627, 32535751803934, 32535751803996⟩
      ⟨740, 739588354572407, 739598571675835, 33634364092601, 33634364092665⟩ := by
  apply checkedSegment (a := 691) (b := 740) (by decide) extra691 2
  decide +kernel

private def extra740 : ℕ → ℕ
  | 740 => 20
  | 761 => 25
  | _ => 0

private theorem part740 :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x)
      ⟨740, 739588354572407, 739598571675835, 33634364092601, 33634364092665⟩
      ⟨787, 779379819078068, 779390404853123, 33634364092601, 33634364092665⟩ := by
  apply checkedSegment (a := 740) (b := 787) (by decide) extra740 2
  decide +kernel

private def extra787 : ℕ → ℕ
  | 787 => 21
  | 809 => 12
  | 822 => 13
  | _ => 0

private theorem part787 :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x)
      ⟨787, 779379819078068, 779390404853123, 33634364092601, 33634364092665⟩
      ⟨836, 832984467862898, 832995629579351, 33634364092601, 33634364092665⟩ := by
  apply checkedSegment (a := 787) (b := 836) (by decide) extra787 3
  decide +kernel

private def extra836 : ℕ → ℕ
  | 836 => 19
  | 856 => 16
  | 873 => 13
  | _ => 0

private theorem part836 :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x)
      ⟨836, 832984467862898, 832995629579351, 33634364092601, 33634364092665⟩
      ⟨887, 890443240958954, 890454872000790, 37001659922583, 37001659922652⟩ := by
  apply checkedSegment (a := 836) (b := 887) (by decide) extra836 3
  decide +kernel

private def extra887 : ℕ → ℕ
  | 887 => 31
  | 919 => 22
  | _ => 0

private theorem part887 :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x)
      ⟨887, 890443240958954, 890454872000790, 37001659922583, 37001659922652⟩
      ⟨942, 938202788890047, 938214842246607, 37001659922583, 37001659922652⟩ := by
  apply checkedSegment (a := 887) (b := 942) (by decide) extra887 2
  decide +kernel

private def extra942 : ℕ → ℕ
  | 942 => 20
  | 963 => 16
  | 980 => 20
  | _ => 0

private theorem part942 :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x)
      ⟨942, 938202788890047, 938214842246607, 37001659922583, 37001659922652⟩
      ⟨1001, 996680773846838, 996693126979601, 40435647127064, 40435647127138⟩ := by
  apply checkedSegment (a := 942) (b := 1001) (by decide) extra942 3
  decide +kernel

private def extra1001 : ℕ → ℕ
  | 1001 => 20
  | 1022 => 26
  | _ => 0

private theorem part1001 :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x)
      ⟨1001, 996680773846838, 996693126979601, 40435647127064, 40435647127138⟩
      ⟨1049, 1045890940801708, 1045903618713757, 41128794307623, 41128794307699⟩ := by
  apply checkedSegment (a := 1001) (b := 1049) (by decide) extra1001 2
  decide +kernel

private def extra1049 : ℕ → ℕ
  | 1049 => 19
  | 1069 => 23
  | 1093 => 15
  | _ => 0

private theorem part1049 :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x)
      ⟨1049, 1045890940801708, 1045903618713757, 41128794307623, 41128794307699⟩
      ⟨1109, 1115703138203154, 1115717145209435, 41128794307623, 41128794307699⟩ := by
  apply checkedSegment (a := 1049) (b := 1109) (by decide) extra1049 3
  decide +kernel

private def extra1109 : ℕ → ℕ
  | 1109 => 13
  | 1123 => 27
  | _ => 0

private theorem part1109 :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x)
      ⟨1109, 1115703138203154, 1115717145209435, 41128794307623, 41128794307699⟩
      ⟨1151, 1143785591778648, 1143800176160918, 41128794307623, 41128794307699⟩ := by
  apply checkedSegment (a := 1109) (b := 1151) (by decide) extra1109 2
  decide +kernel

private def extra1151 : ℕ → ℕ
  | 1151 => 26
  | 1178 => 21
  | _ => 0

private theorem part1151 :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x)
      ⟨1151, 1143785591778648, 1143800176160918, 41128794307623, 41128794307699⟩
      ⟨1200, 1193245985796177, 1193261484161027, 41128794307623, 41128794307699⟩ := by
  apply checkedSegment (a := 1151) (b := 1200) (by decide) extra1151 2
  decide +kernel

private def extra1200 : ℕ → ℕ
  | 1200 => 20
  | 1221 => 21
  | _ => 0

private theorem part1200 :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x)
      ⟨1200, 1193245985796177, 1193261484161027, 41128794307623, 41128794307699⟩
      ⟨1243, 1243000927795610, 1243017128455908, 41128794307623, 41128794307699⟩ := by
  apply checkedSegment (a := 1200) (b := 1243) (by decide) extra1200 2
  decide +kernel

private def extra1243 : ℕ → ℕ
  | 1243 => 27
  | 1271 => 14
  | 1286 => 20
  | _ => 0

private theorem part1243 :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x)
      ⟨1243, 1243000927795610, 1243017128455908, 41128794307623, 41128794307699⟩
      ⟨1307, 1314568061177083, 1314585328100813, 41128794307623, 41128794307699⟩ := by
  apply checkedSegment (a := 1243) (b := 1307) (by decide) extra1243 3
  decide +kernel

private def extra1307 : ℕ → ℕ
  | 1307 => 19
  | 1327 => 39
  | _ => 0

private theorem part1307 :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x)
      ⟨1307, 1314568061177083, 1314585328100813, 41128794307623, 41128794307699⟩
      ⟨1367, 1352918866258204, 1352936538768432, 43526689580418, 43526689580498⟩ := by
  apply checkedSegment (a := 1307) (b := 1367) (by decide) extra1307 2
  decide +kernel

private def extra1367 : ℕ → ℕ
  | 1367 => 22
  | 1390 => 17
  | 1408 => 6
  | 1415 => 7
  | _ => 0

private theorem part1367 :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x)
      ⟨1367, 1352918866258204, 1352936538768432, 43526689580418, 43526689580498⟩
      ⟨1423, 1392699616554902, 1392717814837628, 47137607493057, 47137607493143⟩ := by
  apply checkedSegment (a := 1367) (b := 1423) (by decide) extra1367 4
  decide +kernel

/-- The incoming prefix extends to 1423 with the stated psi estimate. -/
theorem middle_prefix :
    Valid ⟨1423, 1392699616554902, 1392717814837628, 47137607493057, 47137607493143⟩ ∧
      ∀ x : ℝ, 101 ≤ x → x < 1423 → |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have joined0 := segment_comp part101 part165
  have joined1 := segment_comp part229 part293
  have joined2 := segment_comp part356 part420
  have joined3 := segment_comp part479 part533
  have joined4 := segment_comp part588 part647
  have joined5 := segment_comp part691 part740
  have joined6 := segment_comp part787 part836
  have joined7 := segment_comp part887 part942
  have joined8 := segment_comp part1001 part1049
  have joined9 := segment_comp part1109 part1151
  have joined10 := segment_comp part1200 part1243
  have joined11 := segment_comp part1307 part1367
  have joined12 := segment_comp joined0 joined1
  have joined13 := segment_comp joined2 joined3
  have joined14 := segment_comp joined4 joined5
  have joined15 := segment_comp joined6 joined7
  have joined16 := segment_comp joined8 joined9
  have joined17 := segment_comp joined10 joined11
  have joined18 := segment_comp joined12 joined13
  have joined19 := segment_comp joined14 joined15
  have joined20 := segment_comp joined16 joined17
  have joined21 := segment_comp joined18 joined19
  have joined22 := segment_comp joined21 joined20
  exact joined22 low_prefix.1

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
