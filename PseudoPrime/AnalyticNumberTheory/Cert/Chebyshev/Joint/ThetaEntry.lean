/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.MiddlePrefix

/-! # Joint prefix verification from 1423 through 2656 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private theorem checkedSegment {a b : ℕ} (hu : b ≤ 1000001) (extra : ℕ → ℕ) (count : ℕ) {s t : Edge}
    (hg : batchAccepted a b extra (fun _ ↦ (4, 5)) count s t = true) :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x) s t := by
  exact accepted_segment hu (fun _ _ _ _ _ _ h ↦ h.1) hg

private def extra1423 : ℕ → ℕ
  | 1423 => 6
  | 1430 => 13
  | 1444 => 14
  | _ => 0

private theorem part1423 :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x)
      ⟨1423, 1392699616554902, 1392717814837628, 47137607493057, 47137607493143⟩
      ⟨1459, 1450866061650910, 1450885000703990, 47137607493057, 47137607493143⟩ := by
  apply checkedSegment (a := 1423) (b := 1459) (by decide) extra1423 3
  decide +kernel

private def extra1459 : ℕ → ℕ
  | 1459 => 29
  | 1489 => 33
  | _ => 0

private theorem part1459 :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x)
      ⟨1459, 1450866061650910, 1450885000703990, 47137607493057, 47137607493143⟩
      ⟨1523, 1516599552188812, 1516619256049537, 47137607493057, 47137607493143⟩ := by
  apply checkedSegment (a := 1459) (b := 1523) (by decide) extra1459 2
  decide +kernel

private def extra1523 : ℕ → ℕ
  | 1523 => 15
  | 1539 => 22
  | _ => 0

private theorem part1523 :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x)
      ⟨1523, 1516599552188812, 1516619256049537, 47137607493057, 47137607493143⟩
      ⟨1562, 1560648253966443, 1560668418319781, 47137607493057, 47137607493143⟩ := by
  apply checkedSegment (a := 1523) (b := 1562) (by decide) extra1523 2
  decide +kernel

private def extra1562 : ℕ → ℕ
  | 1562 => 29
  | 1592 => 20
  | _ => 0

private theorem part1562 :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x)
      ⟨1562, 1560648253966443, 1560668418319781, 47137607493057, 47137607493143⟩
      ⟨1613, 1619616017022111, 1619636653849409, 47137607493057, 47137607493143⟩ := by
  apply checkedSegment (a := 1562) (b := 1613) (by decide) extra1562 2
  decide +kernel

private def extra1613 : ℕ → ℕ
  | 1613 => 13
  | 1627 => 29
  | _ => 0

private theorem part1613 :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x)
      ⟨1613, 1619616017022111, 1619636653849409, 47137607493057, 47137607493143⟩
      ⟨1657, 1656577341191528, 1656598314743341, 47137607493057, 47137607493143⟩ := by
  apply checkedSegment (a := 1613) (b := 1657) (by decide) extra1613 2
  decide +kernel

private def extra1657 : ℕ → ℕ
  | 1657 => 23
  | 1681 => 27
  | _ => 0

private theorem part1657 :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x)
      ⟨1657, 1656577341191528, 1656598314743341, 47137607493057, 47137607493143⟩
      ⟨1709, 1712267481138493, 1712288912170931, 50851179559756, 50851179559848⟩ := by
  apply checkedSegment (a := 1657) (b := 1709) (by decide) extra1657 2
  decide +kernel

private def extra1709 : ℕ → ℕ
  | 1709 => 23
  | 1733 => 25
  | _ => 0

private theorem part1709 :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x)
      ⟨1709, 1712267481138493, 1712288912170931, 50851179559756, 50851179559848⟩
      ⟨1759, 1764468187157278, 1764490080518781, 50851179559756, 50851179559848⟩ := by
  apply checkedSegment (a := 1709) (b := 1759) (by decide) extra1709 2
  decide +kernel

private def extra1759 : ℕ → ℕ
  | 1759 => 27
  | 1787 => 35
  | _ => 0

private theorem part1759 :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x)
      ⟨1759, 1764468187157278, 1764490080518781, 50851179559756, 50851179559848⟩
      ⟨1823, 1816884853716687, 1816907362276714, 50851179559756, 50851179559848⟩ := by
  apply checkedSegment (a := 1759) (b := 1823) (by decide) extra1759 2
  decide +kernel

private def extra1823 : ℕ → ℕ
  | 1823 => 34
  | 1858 => 18
  | _ => 0

private theorem part1823 :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x)
      ⟨1823, 1816884853716687, 1816907362276714, 50851179559756, 50851179559848⟩
      ⟨1877, 1873318707671451, 1873341548525134, 54612379675444, 54612379675542⟩ := by
  apply checkedSegment (a := 1823) (b := 1877) (by decide) extra1823 2
  decide +kernel

private def extra1877 : ℕ → ℕ
  | 1877 => 35
  | _ => 0

private theorem part1877 :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x)
      ⟨1877, 1873318707671451, 1873341548525134, 54612379675444, 54612379675542⟩
      ⟨1913, 1911041855970202, 1911064912102060, 54612379675444, 54612379675542⟩ := by
  apply checkedSegment (a := 1877) (b := 1913) (by decide) extra1877 1
  decide +kernel

private def extra1913 : ℕ → ℕ
  | 1913 => 37
  | _ => 0

private theorem part1913 :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x)
      ⟨1913, 1911041855970202, 1911064912102060, 54612379675444, 54612379675542⟩
      ⟨1951, 1941305975333331, 1941329272535927, 54612379675444, 54612379675542⟩ := by
  apply checkedSegment (a := 1913) (b := 1951) (by decide) extra1913 1
  decide +kernel

private def extra1951 : ℕ → ℕ
  | 1951 => 32
  | 1984 => 14
  | _ => 0

private theorem part1951 :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x)
      ⟨1951, 1941305975333331, 1941329272535927, 54612379675444, 54612379675542⟩
      ⟨1999, 1986850906225183, 1986874520202159, 54612379675444, 54612379675542⟩ := by
  apply checkedSegment (a := 1951) (b := 1999) (by decide) extra1951 2
  decide +kernel

private def extra1999 : ℕ → ℕ
  | 1999 => 30
  | _ => 0

private theorem part1999 :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x)
      ⟨1999, 1986850906225183, 1986874520202159, 54612379675444, 54612379675542⟩
      ⟨2030, 2032499072900811, 2032522889714669, 54612379675444, 54612379675542⟩ := by
  apply checkedSegment (a := 1999) (b := 2030) (by decide) extra1999 1
  decide +kernel

private def extra2030 : ℕ → ℕ
  | 2030 => 37
  | 2068 => 23
  | _ => 0

private theorem part2030 :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x)
      ⟨2030, 2032499072900811, 2032522889714669, 54612379675444, 54612379675542⟩
      ⟨2092, 2094276312488376, 2094300934313958, 55305526856003, 55305526856103⟩ := by
  apply checkedSegment (a := 2030) (b := 2092) (by decide) extra2030 2
  decide +kernel

private def extra2092 : ℕ → ℕ
  | 2092 => 38
  | _ => 0

private theorem part2092 :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x)
      ⟨2092, 2094276312488376, 2094300934313958, 55305526856003, 55305526856103⟩
      ⟨2131, 2124899702827796, 2124925140365708, 55305526856003, 55305526856103⟩ := by
  apply checkedSegment (a := 2092) (b := 2131) (by decide) extra2092 1
  decide +kernel

private def extra2131 : ℕ → ℕ
  | 2131 => 29
  | _ => 0

private theorem part2131 :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x)
      ⟨2131, 2124899702827796, 2124925140365708, 55305526856003, 55305526856103⟩
      ⟨2161, 2163244810407032, 2163270748892877, 55305526856003, 55305526856103⟩ := by
  apply checkedSegment (a := 2131) (b := 2161) (by decide) extra2131 1
  decide +kernel

private def extra2161 : ℕ → ℕ
  | 2161 => 46
  | _ => 0

private theorem part2161 :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x)
      ⟨2161, 2163244810407032, 2163270748892877, 55305526856003, 55305526856103⟩
      ⟨2208, 2197670278820532, 2197696665853579, 58969088502128, 58969088502234⟩ := by
  apply checkedSegment (a := 2161) (b := 2208) (by decide) extra2161 1
  decide +kernel

private def extra2208 : ℕ → ℕ
  | 2208 => 26
  | 2235 => 18
  | _ => 0

private theorem part2208 :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x)
      ⟨2208, 2197670278820532, 2197696665853579, 58969088502128, 58969088502234⟩
      ⟨2254, 2247789598868138, 2247817169294548, 62819236103833, 62819236103945⟩ := by
  apply checkedSegment (a := 2208) (b := 2254) (by decide) extra2208 2
  decide +kernel

private def extra2254 : ℕ → ℕ
  | 2254 => 31
  | 2286 => 30
  | _ => 0

private theorem part2254 :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x)
      ⟨2254, 2247789598868138, 2247817169294548, 62819236103833, 62819236103945⟩
      ⟨2317, 2317406091010977, 2317434924685470, 62819236103833, 62819236103945⟩ := by
  apply checkedSegment (a := 2254) (b := 2317) (by decide) extra2254 2
  decide +kernel

private def extra2317 : ℕ → ℕ
  | 2317 => 33
  | _ => 0

private theorem part2317 :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x)
      ⟨2317, 2317406091010977, 2317434924685470, 62819236103833, 62819236103945⟩
      ⟨2351, 2348437701397940, 2348467032772740, 62819236103833, 62819236103945⟩ := by
  apply checkedSegment (a := 2317) (b := 2351) (by decide) extra2317 1
  decide +kernel

private def extra2351 : ℕ → ℕ
  | 2351 => 31
  | 2383 => 27
  | _ => 0

private theorem part2351 :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x)
      ⟨2351, 2348437701397940, 2348467032772740, 62819236103833, 62819236103945⟩
      ⟨2411, 2420349137578809, 2420379165499031, 64765146252886, 64765146253001⟩ := by
  apply checkedSegment (a := 2351) (b := 2411) (by decide) extra2351 2
  decide +kernel

private def extra2411 : ℕ → ℕ
  | 2411 => 25
  | 2437 => 29
  | _ => 0

private theorem part2411 :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x)
      ⟨2411, 2420349137578809, 2420379165499031, 64765146252886, 64765146253001⟩
      ⟨2467, 2474928783255586, 2474959549477889, 64765146252886, 64765146253001⟩ := by
  apply checkedSegment (a := 2411) (b := 2467) (by decide) extra2411 2
  decide +kernel

private def extra2467 : ℕ → ℕ
  | 2467 => 53
  | _ => 0

private theorem part2467 :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x)
      ⟨2467, 2474928783255586, 2474959549477889, 64765146252886, 64765146253001⟩
      ⟨2521, 2506192772710229, 2506223959713295, 64765146252886, 64765146253001⟩ := by
  apply checkedSegment (a := 2467) (b := 2521) (by decide) extra2467 1
  decide +kernel

private def extra2521 : ℕ → ℕ
  | 2521 => 32
  | _ => 0

private theorem part2521 :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x)
      ⟨2521, 2506192772710229, 2506223959713295, 64765146252886, 64765146253001⟩
      ⟨2554, 2553229864098529, 2553261993474854, 64765146252886, 64765146253001⟩ := by
  apply checkedSegment (a := 2521) (b := 2554) (by decide) extra2521 1
  decide +kernel

private def extra2554 : ℕ → ℕ
  | 2554 => 38
  | _ => 0

private theorem part2554 :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x)
      ⟨2554, 2553229864098529, 2553261993474854, 64765146252886, 64765146253001⟩
      ⟨2593, 2576791404760033, 2576823933631859, 64765146252886, 64765146253001⟩ := by
  apply checkedSegment (a := 2554) (b := 2593) (by decide) extra2554 1
  decide +kernel

private def extra2593 : ℕ → ℕ
  | 2593 => 31
  | 2625 => 23
  | 2649 => 7
  | _ => 0

private theorem part2593 :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x)
      ⟨2593, 2576791404760033, 2576823933631859, 64765146252886, 64765146253001⟩
      ⟨2657, 2624016843000490, 2624050214203841, 64765146252886, 64765146253001⟩ := by
  apply checkedSegment (a := 2593) (b := 2657) (by decide) extra2593 3
  decide +kernel

/-- The incoming prefix extends to 2657 with the stated psi estimate. -/
theorem theta_entry :
    Valid ⟨2657, 2624016843000490, 2624050214203841, 64765146252886, 64765146253001⟩ ∧
      ∀ x : ℝ, 1423 ≤ x → x < 2657 → |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x := by
  have joined0 := segment_comp part1423 part1459
  have joined1 := segment_comp part1523 part1562
  have joined2 := segment_comp part1613 part1657
  have joined3 := segment_comp part1709 part1759
  have joined4 := segment_comp part1823 part1877
  have joined5 := segment_comp part1913 part1951
  have joined6 := segment_comp part1999 part2030
  have joined7 := segment_comp part2092 part2131
  have joined8 := segment_comp part2161 part2208
  have joined9 := segment_comp part2254 part2317
  have joined10 := segment_comp part2351 part2411
  have joined11 := segment_comp part2467 part2521
  have joined12 := segment_comp part2554 part2593
  have joined13 := segment_comp joined0 joined1
  have joined14 := segment_comp joined2 joined3
  have joined15 := segment_comp joined4 joined5
  have joined16 := segment_comp joined6 joined7
  have joined17 := segment_comp joined8 joined9
  have joined18 := segment_comp joined10 joined11
  have joined19 := segment_comp joined13 joined14
  have joined20 := segment_comp joined15 joined16
  have joined21 := segment_comp joined17 joined18
  have joined22 := segment_comp joined19 joined20
  have joined23 := segment_comp joined21 joined12
  have joined24 := segment_comp joined22 joined23
  exact joined24 middle_prefix.1

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
