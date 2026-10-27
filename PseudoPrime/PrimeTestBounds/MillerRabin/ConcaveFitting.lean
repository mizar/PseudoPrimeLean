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

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational vertices of the finite baseline graph, including the terminal plateau. -/
def mrSmallRegionVertices : List (ℚ × ℚ) :=
  [(2197 / 1000, 2), (953 / 125, 3), (11513 / 1000, 3)]

/-- Rational polynomial fit and finite cap. Its checker certifies graph domination. -/
def mrSmallRegionAffineFit : Analysis.ConcaveQuadraticFit :=
  { linear := 23 / 125
    curvature := 0
    constant := 799 / 500
    cap := 3
    left := 2197 / 1000
    right := 11513 / 1000
    vertices := mrSmallRegionVertices }

/-- Kernel verification of the rational shape, domain and vertex inequalities. -/
theorem mrSmallRegionAffineFit_checked : mrSmallRegionAffineFit.check = true := by decide +kernel

/-- Rational polynomial fit and finite cap. Its checker certifies graph domination. -/
def mrSmallRegionQuadraticFit : Analysis.ConcaveQuadraticFit :=
  { linear := 323 / 1000
    curvature := 7 / 500
    constant := 679 / 500
    cap := 3
    left := 2197 / 1000
    right := 11513 / 1000
    vertices := mrSmallRegionVertices }

/-- Kernel verification of the rational shape, domain and vertex inequalities. -/
theorem mrSmallRegionQuadraticFit_checked : mrSmallRegionQuadraticFit.check = true := by
  decide +kernel

/-- The smaller of the two nondominated proposed MR fits, including their cap. -/
noncomputable def mrSmallRegionEnvelope (L : ℝ) : ℝ :=
  min (mrSmallRegionAffineFit.curve L) (mrSmallRegionQuadraticFit.curve L)

/-- Every MR baseline chord lies below the certified envelope of both fits. -/
theorem mrSmallRegionEnvelope_chord {p q : ℚ × ℚ} (hp : p ∈ mrSmallRegionVertices)
    (hq : q ∈ mrSmallRegionVertices) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hs : u + v = 1) :
    u * (p.2 : ℝ) + v * (q.2 : ℝ) ≤ mrSmallRegionEnvelope (u * (p.1 : ℝ) + v * (q.1 : ℝ)) := by
  exact
    le_min (mrSmallRegionAffineFit.chord_bound mrSmallRegionAffineFit_checked hp hq hu hv hs)
      (mrSmallRegionQuadraticFit.chord_bound mrSmallRegionQuadraticFit_checked hp hq hu hv hs)

/-- The MR envelope is concave on the logarithmic axis. -/
theorem mrSmallRegionEnvelope_concave : ConcaveOn ℝ Set.univ mrSmallRegionEnvelope := by
  exact
    (mrSmallRegionAffineFit.concave mrSmallRegionAffineFit_checked).inf
      (mrSmallRegionQuadraticFit.concave mrSmallRegionQuadraticFit_checked)

/-- The MR envelope is nondecreasing below the checked finite right endpoint. -/
theorem mrSmallRegionEnvelope_monotone {x y : ℝ} (hxy : x ≤ y)
    (hy : y ≤ mrSmallRegionQuadraticFit.right) :
    mrSmallRegionEnvelope x ≤ mrSmallRegionEnvelope y := by
  exact
    min_le_min (mrSmallRegionAffineFit.monotone mrSmallRegionAffineFit_checked hxy hy)
      (mrSmallRegionQuadraticFit.monotone mrSmallRegionQuadraticFit_checked hxy hy)

/-- The fitted envelope remains concave in n after substituting L = log n. -/
theorem mrSmallRegionEnvelope_log_concave :
    ConcaveOn ℝ (Set.Ioc 1 (Real.exp (mrSmallRegionQuadraticFit.right : ℝ)))
      (fun n => mrSmallRegionEnvelope (Real.log n)) := by
  have hf := mrSmallRegionEnvelope_concave.subset (Set.subset_univ _) (convex_Ioi 0)
  exact
    Analysis.concaveOn_log_comp_of_mono_below hf
      (fun _ _ _ hxy hy => mrSmallRegionEnvelope_monotone hxy hy)

end PseudoPrime.PrimeTestBounds.MillerRabin
