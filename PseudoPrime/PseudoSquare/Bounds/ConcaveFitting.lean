/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ConcaveLogAffineCertificates

/-! # Checked concave fits above small-region polylines

The rational vertices come from a computational witness investigation through 100000.
This module certifies that the fitted curves dominate every polyline segment.
It does not prove witness coverage of the original finite enumeration.
-/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- Rational vertices of the finite baseline graph, including the terminal plateau. -/
def negativeSmallRegionVertices : List (ℚ × ℚ) :=
  [(549 / 500, 5), (677 / 250, 13), (451 / 100, 17), (1497 / 250, 31), (8021 / 1000, 41),
    (2489 / 250, 43), (85 / 8, 47), (1067 / 100, 53), (11513 / 1000, 53)]

/-- Rational polynomial fit and finite cap. Its checker certifies graph domination. -/
def negativeSmallRegionAffineFit : Analysis.ConcaveQuadraticFit :=
  { linear := 4919 / 1000
    curvature := 0
    constant := 773 / 500
    cap := 53
    left := 549 / 500
    right := 11513 / 1000
    vertices := negativeSmallRegionVertices }

/-- Kernel verification of the rational shape, domain and vertex inequalities. -/
theorem negativeSmallRegionAffineFit_checked : negativeSmallRegionAffineFit.check = true := by
  decide +kernel

/-- Rational polynomial fit and finite cap. Its checker certifies graph domination. -/
def negativeSmallRegionQuadraticFit : Analysis.ConcaveQuadraticFit :=
  { linear := 2919 / 500
    curvature := 7 / 100
    constant := (-661 / 500)
    cap := 53
    left := 549 / 500
    right := 11513 / 1000
    vertices := negativeSmallRegionVertices }

/-- Kernel verification of the rational shape, domain and vertex inequalities. -/
theorem negativeSmallRegionQuadraticFit_checked : negativeSmallRegionQuadraticFit.check = true := by
  decide +kernel

/-- Logarithmic affine fit with certified rational logarithm intervals at the vertices. -/
def negativeSmallRegionLogAffineFit : Analysis.ConcaveLogAffineFit :=
  { linear := 4637 / 1000
    logCoefficient := 49 / 25
    constant := (-137 / 500)
    cap := 53
    vertices :=
      [{  point := (549 / 500, 5), scale := 1, terms := 32
          lowerLog := 9349 / 100000, upperLog := 93491 / 1000000 },
        { point := (677 / 250, 13), scale := 2, terms := 32
          lowerLog := 99621 / 100000, upperLog := 996211 / 1000000 },
        { point := (451 / 100, 17), scale := 3, terms := 32
          lowerLog := 1506297 / 1000000, upperLog := 753149 / 500000 },
        { point := (1497 / 250, 31), scale := 3, terms := 32
          lowerLog := 1789757 / 1000000, upperLog := 894879 / 500000 },
        { point := (8021 / 1000, 41), scale := 4, terms := 32
          lowerLog := 2082063 / 1000000, upperLog := 130129 / 62500 },
        { point := (2489 / 250, 43), scale := 4, terms := 32
          lowerLog := 91927 / 40000, upperLog := 35909 / 15625 },
        { point := (85 / 8, 47), scale := 4, terms := 32
          lowerLog := 2363209 / 1000000, upperLog := 236321 / 100000 },
        { point := (1067 / 100, 53), scale := 4, terms := 32
          lowerLog := 591859 / 250000, upperLog := 2367437 / 1000000 },
        { point := (11513 / 1000, 53), scale := 4, terms := 32
          lowerLog := 610869 / 250000, upperLog := 2443477 / 1000000 }] }

/-- Kernel verification of the logarithm intervals and the rational vertex bounds. -/
theorem negativeSmallRegionLogAffineFit_checked : negativeSmallRegionLogAffineFit.check = true := by
  decide +kernel

/-- The logarithm records have exactly the same rational baseline vertices. -/
theorem negativeSmallRegionLogAffineFit_points :
    negativeSmallRegionLogAffineFit.vertices.map Analysis.LogAffineFitVertex.point =
      negativeSmallRegionVertices := by
  rfl

/-- Rational vertices of the finite baseline graph, including the terminal plateau. -/
def nonOneSmallRegionVertices : List (ℚ × ℚ) :=
  [(549 / 500, 3), (389 / 200, 5), (368 / 125, 7), (4369 / 1000, 11), (2901 / 500, 13),
    (6621 / 1000, 17), (1413 / 200, 19), (4283 / 500, 23), (9273 / 1000, 29), (4909 / 500, 31),
    (1127 / 100, 41), (11513 / 1000, 41)]

/-- Rational polynomial fit and finite cap. Its checker certifies graph domination. -/
def nonOneSmallRegionAffineFit : Analysis.ConcaveQuadraticFit :=
  { linear := 467 / 125
    curvature := 0
    constant := (-551 / 500)
    cap := 41
    left := 549 / 500
    right := 11513 / 1000
    vertices := nonOneSmallRegionVertices }

/-- Kernel verification of the rational shape, domain and vertex inequalities. -/
theorem nonOneSmallRegionAffineFit_checked : nonOneSmallRegionAffineFit.check = true := by
  decide +kernel

/-- The smallest of the three certified negative-witness graph fits, including their cap. -/
noncomputable def negativeSmallRegionEnvelope (L : ℝ) : ℝ :=
  min (negativeSmallRegionAffineFit.curve L)
    (min (negativeSmallRegionQuadraticFit.curve L) (negativeSmallRegionLogAffineFit.curve L))

/-- Every baseline chord lies below the fitted envelope; no interior sampling is used. -/
theorem negativeSmallRegionEnvelope_chord {p q : ℚ × ℚ} (hp : p ∈ negativeSmallRegionVertices)
    (hq : q ∈ negativeSmallRegionVertices) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hs : u + v = 1) :
    u * (p.2 : ℝ) + v * (q.2 : ℝ) ≤
      negativeSmallRegionEnvelope (u * (p.1 : ℝ) + v * (q.1 : ℝ)) := by
  have ha :=
    negativeSmallRegionAffineFit.chord_bound negativeSmallRegionAffineFit_checked hp hq hu hv hs
  have hb :=
    negativeSmallRegionQuadraticFit.chord_bound negativeSmallRegionQuadraticFit_checked hp hq hu hv
      hs
  have hc :=
    negativeSmallRegionLogAffineFit.point_chord_bound negativeSmallRegionLogAffineFit_checked
      (by simpa only [negativeSmallRegionLogAffineFit_points] using hp)
      (by simpa only [negativeSmallRegionLogAffineFit_points] using hq) hu hv hs
  exact le_min ha (le_min hb hc)

/-- The envelope is concave on positive logarithmic inputs. -/
theorem negativeSmallRegionEnvelope_concave :
    ConcaveOn ℝ (Set.Ioi 0) negativeSmallRegionEnvelope := by
  have ha :=
    (negativeSmallRegionAffineFit.concave negativeSmallRegionAffineFit_checked).subset
      (Set.subset_univ _) (convex_Ioi 0)
  have hb :=
    (negativeSmallRegionQuadraticFit.concave negativeSmallRegionQuadraticFit_checked).subset
      (Set.subset_univ _) (convex_Ioi 0)
  exact
    ha.inf
      (hb.inf (negativeSmallRegionLogAffineFit.concave negativeSmallRegionLogAffineFit_checked))

/-- The envelope is nondecreasing on its positive checked finite domain. -/
theorem negativeSmallRegionEnvelope_monotone {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (hy : y ≤ negativeSmallRegionQuadraticFit.right) :
    negativeSmallRegionEnvelope x ≤ negativeSmallRegionEnvelope y := by
  exact
    min_le_min (negativeSmallRegionAffineFit.monotone negativeSmallRegionAffineFit_checked hxy hy)
      (min_le_min
        (negativeSmallRegionQuadraticFit.monotone negativeSmallRegionQuadraticFit_checked hxy hy)
        (negativeSmallRegionLogAffineFit.monotone negativeSmallRegionLogAffineFit_checked hx hxy))

/-- The fitted envelope remains concave in n after substituting L = log n. -/
theorem negativeSmallRegionEnvelope_log_concave :
    ConcaveOn ℝ (Set.Ioc 1 (Real.exp (negativeSmallRegionQuadraticFit.right : ℝ)))
      (fun n => negativeSmallRegionEnvelope (Real.log n)) := by
  exact
    Analysis.concaveOn_log_comp_of_mono_below negativeSmallRegionEnvelope_concave
      (fun _ _ hx hxy hy => negativeSmallRegionEnvelope_monotone hx hxy hy)

/-- The non-one graph fit after merging the three identical proposed formulas. -/
noncomputable def nonOneSmallRegionEnvelope (L : ℝ) : ℝ :=
  nonOneSmallRegionAffineFit.curve L

/-- Every non-one baseline chord lies below the certified affine envelope. -/
theorem nonOneSmallRegionEnvelope_chord {p q : ℚ × ℚ} (hp : p ∈ nonOneSmallRegionVertices)
    (hq : q ∈ nonOneSmallRegionVertices) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hs : u + v = 1) :
    u * (p.2 : ℝ) + v * (q.2 : ℝ) ≤ nonOneSmallRegionEnvelope (u * (p.1 : ℝ) + v * (q.1 : ℝ)) := by
  exact nonOneSmallRegionAffineFit.chord_bound nonOneSmallRegionAffineFit_checked hp hq hu hv hs

/-- The non-one envelope is concave on the real logarithmic axis. -/
theorem nonOneSmallRegionEnvelope_concave : ConcaveOn ℝ Set.univ nonOneSmallRegionEnvelope := by
  exact nonOneSmallRegionAffineFit.concave nonOneSmallRegionAffineFit_checked

/-- The non-one envelope is nondecreasing below its checked right endpoint. -/
theorem nonOneSmallRegionEnvelope_monotone {x y : ℝ} (hxy : x ≤ y)
    (hy : y ≤ nonOneSmallRegionAffineFit.right) :
    nonOneSmallRegionEnvelope x ≤ nonOneSmallRegionEnvelope y := by
  exact nonOneSmallRegionAffineFit.monotone nonOneSmallRegionAffineFit_checked hxy hy

/-- The fitted envelope remains concave in n after substituting L = log n. -/
theorem nonOneSmallRegionEnvelope_log_concave :
    ConcaveOn ℝ (Set.Ioc 1 (Real.exp (nonOneSmallRegionAffineFit.right : ℝ)))
      (fun n => nonOneSmallRegionEnvelope (Real.log n)) := by
  have hf := nonOneSmallRegionEnvelope_concave.subset (Set.subset_univ _) (convex_Ioi 0)
  exact
    Analysis.concaveOn_log_comp_of_mono_below hf
      (fun _ _ _ hxy hy => nonOneSmallRegionEnvelope_monotone hxy hy)

end PseudoPrime.PseudoSquare
