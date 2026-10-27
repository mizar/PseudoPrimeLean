/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ConcaveLogarithmicFitting
public import PseudoPrime.Analysis.LogTaylorBounds

/-! # Rational certificates for capped logarithmic affine fits

Taylor interval checks certify the logarithm at each rational polyline vertex.
Concavity transfers those vertex inequalities to every segment interior.
These certificates compare curves with fixed graphs, independently of witness coverage.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- A lower bound for log x and an affine bound using that lower endpoint imply
an upper bound by the logarithmic affine curve, provided b is nonnegative.
Multiply the logarithm comparison and preserve order under addition. -/
theorem concaveLogAffine_ge_of_lower_log {a b c : ℚ} {x lo p : ℝ} (hb : 0 ≤ b)
    (hl : lo ≤ Real.log x) (hp : p ≤ (a : ℝ) * x + (b : ℝ) * lo + (c : ℝ)) :
    p ≤ concaveLogAffine x a b c := by
  have hm := mul_le_mul_of_nonneg_left hl (Rat.cast_nonneg.mpr hb)
  exact hp.trans (add_le_add (add_le_add (le_refl ((a : ℝ) * x)) hm) (le_refl (c : ℝ)))

/-- One rational polyline vertex and a Taylor interval certificate for its logarithm.
The scale, terms and endpoints describe a proposed check; validity is imposed by the checker.
This separates curve fitting from the source of the vertex data. -/
structure LogAffineFitVertex where
  /-- Rational abscissa and ordinate. -/
  point : ℚ × ℚ
  /-- Power-of-two scale for the logarithm interval. -/
  scale : ℕ
  /-- Number of Taylor terms. -/
  terms : ℕ
  /-- Proposed rational lower endpoint for log of the abscissa. -/
  lowerLog : ℚ
  /-- Proposed rational upper endpoint for the same logarithm. -/
  upperLog : ℚ

/-- Rational data for a capped logarithmic affine fit and its finite vertices.
The coefficients and cap define the curve. A successful check verifies their signs,
the positive vertex domain and every ordinate comparison.
This is a mathematical fitting certificate, independent of witness enumeration. -/
structure ConcaveLogAffineFit where
  /-- Positive coefficient of L after checking. -/
  linear : ℚ
  /-- Nonnegative coefficient of log L after checking. -/
  logCoefficient : ℚ
  /-- Signed constant term. -/
  constant : ℚ
  /-- Constant upper plateau. -/
  cap : ℚ
  /-- Finite vertices with their logarithm certificates. -/
  vertices : List LogAffineFitVertex

/-- Evaluate the smaller of the rational cap and a*L+b*log L+c.
The logarithmic domain is positive L. A successful certificate gives a nondecreasing
concave curve above every chord of its finite vertex graph. -/
noncomputable def ConcaveLogAffineFit.curve (d : ConcaveLogAffineFit) (L : ℝ) : ℝ :=
  min (d.cap : ℝ) (concaveLogAffine L d.linear d.logCoefficient d.constant)

/-- Check positive a and nonnegative b, then the rational logarithm interval and
both ordinate inequalities at each vertex. The curve is compared using the lower log endpoint.
This computable check certifies fitting, not witness enumeration. -/
def ConcaveLogAffineFit.check (d : ConcaveLogAffineFit) : Bool :=
  decide (0 < d.linear ∧ 0 ≤ d.logCoefficient) &&
    d.vertices.all fun v =>
      rationalLogIntervalCheck v.point.1 v.scale v.terms v.lowerLog v.upperLog &&
        decide
          (v.point.2 ≤ d.cap ∧
            v.point.2 ≤ d.linear * v.point.1 + d.logCoefficient * v.lowerLog + d.constant)

/-- A successful check supplies the rational coefficient signs.
Reflect its first Boolean conjunct. These conditions justify concavity and monotonicity. -/
theorem ConcaveLogAffineFit.guard {d : ConcaveLogAffineFit} (h : d.check = true) :
    0 < d.linear ∧ 0 ≤ d.logCoefficient :=
  of_decide_eq_true (Bool.and_eq_true_iff.mp h).1

/-- A successful check supplies the logarithm interval check and ordinate guards
at every listed vertex. Extract the local Boolean result and reflect its arithmetic.
The real vertex theorem consumes these facts. -/
theorem ConcaveLogAffineFit.vertex_checks {d : ConcaveLogAffineFit} (h : d.check = true)
    {v : LogAffineFitVertex} (hv : v ∈ d.vertices) :
    rationalLogIntervalCheck v.point.1 v.scale v.terms v.lowerLog v.upperLog = true ∧
      (v.point.2 ≤ d.cap ∧
        v.point.2 ≤ d.linear * v.point.1 + d.logCoefficient * v.lowerLog + d.constant) := by
  have hc := Bool.and_eq_true_iff.mp (List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).2 v hv)
  exact ⟨hc.1, of_decide_eq_true hc.2⟩

/-- Each checked vertex has positive abscissa, as required by the logarithm.
Reflect the positivity guard of the interval checker and cast it to the real numbers.
This supplies the domain membership for Jensen's inequality. -/
theorem ConcaveLogAffineFit.vertex_pos {d : ConcaveLogAffineFit} (h : d.check = true)
    {v : LogAffineFitVertex} (hv : v ∈ d.vertices) : (0 : ℝ) < v.point.1 := by
  have ht := d.vertex_checks h hv
  have hp := of_decide_eq_true ht.1
  exact (Rat.cast_pos).mpr hp.1

/-- Every checked vertex ordinate lies below the real capped logarithmic affine curve.
Cast the rational guard and transfer the certified logarithm lower endpoint.
These bounds imply domination of the whole polyline. -/
theorem ConcaveLogAffineFit.vertex_bound {d : ConcaveLogAffineFit} (h : d.check = true)
    {v : LogAffineFitVertex} (hv : v ∈ d.vertices) : (v.point.2 : ℝ) ≤ d.curve v.point.1 := by
  have ht := d.vertex_checks h hv
  apply le_min ((Rat.cast_le (K := ℝ)).mpr ht.2.1)
  have hp := (Rat.cast_le (K := ℝ)).mpr ht.2.2
  simp only [Rat.cast_add, Rat.cast_mul] at hp
  exact concaveLogAffine_ge_of_lower_log (d.guard h).2 (rationalLogIntervalCheck_sound ht.1).1 hp

/-- The checked capped logarithmic affine curve is concave on positive L.
Take the infimum with the constant cap. This preserves the segment-interior inequality. -/
theorem ConcaveLogAffineFit.concave {d : ConcaveLogAffineFit} (h : d.check = true) :
    ConcaveOn ℝ (Set.Ioi 0) d.curve := by
  have hc := concaveLogAffine_concave d.linear d.logCoefficient d.constant (d.guard h).2
  exact (concaveOn_const (d.cap : ℝ) (convex_Ioi 0)).inf hc

/-- A checked curve is nondecreasing for positive x ≤ y.
Use the coefficient signs in the logarithmic affine comparison and preserve order under minimum.
This permits conservative left rounding of record abscissas. -/
theorem ConcaveLogAffineFit.monotone {d : ConcaveLogAffineFit} (h : d.check = true) {x y : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) : d.curve x ≤ d.curve y :=
  min_le_min (le_refl (d.cap : ℝ)) (concaveLogAffine_mono (d.guard h).1.le (d.guard h).2 hx hxy)

/-- Every chord between two checked vertices lies below the fitted curve.
Weights are nonnegative and sum to one. Use checked domain membership and endpoint bounds
with the general concavity transfer theorem. -/
theorem ConcaveLogAffineFit.chord_bound {d : ConcaveLogAffineFit} (h : d.check = true)
    {p q : LogAffineFitVertex} (hp : p ∈ d.vertices) (hq : q ∈ d.vertices) {u v : ℝ} (hu : 0 ≤ u)
    (hv : 0 ≤ v) (hs : u + v = 1) :
    u * (p.point.2 : ℝ) + v * (q.point.2 : ℝ) ≤
      d.curve (u * (p.point.1 : ℝ) + v * (q.point.1 : ℝ)) :=
  chord_le_of_concave (d.concave h) (d.vertex_pos h hp) (d.vertex_pos h hq) hu hv hs
    (d.vertex_bound h hp) (d.vertex_bound h hq)

/-- The checked chord bound also holds for vertices presented as rational pairs.
Extract their certificate records from map membership and apply the vertex form.
This joins logarithmic affine and polynomial fits of the same baseline polyline. -/
theorem ConcaveLogAffineFit.point_chord_bound {d : ConcaveLogAffineFit} (h : d.check = true)
    {p q : ℚ × ℚ} (hp : p ∈ d.vertices.map LogAffineFitVertex.point)
    (hq : q ∈ d.vertices.map LogAffineFitVertex.point) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v = 1) : u * (p.2 : ℝ) + v * (q.2 : ℝ) ≤ d.curve (u * (p.1 : ℝ) + v * (q.1 : ℝ)) := by
  rcases List.mem_map.mp hp with ⟨vp, hvp, he⟩
  subst p
  rcases List.mem_map.mp hq with ⟨vq, hvq, he⟩
  subst q
  exact d.chord_bound h hvp hvq hu hv hs

end PseudoPrime.Analysis
