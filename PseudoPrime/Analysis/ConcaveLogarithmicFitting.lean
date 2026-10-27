/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Tactic.Linarith

/-! # Concave fits above finite logarithmic polylines

Concavity turns vertex inequalities into domination of every chord and hence every
segment of a piecewise linear graph. Rational guards certify the vertex comparisons
and the nondecreasing finite domain of capped concave quadratic fits.
This module proves curve comparisons, independently of finite witness enumeration.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The rational-parameter curve a*L+b*log L+c.
Its logarithmic domain is L > 0. Nonnegative b gives concavity, while nonnegative a and b
also give monotonicity. This is a smooth candidate for finite polyline fitting. -/
noncomputable def concaveLogAffine (L : ℝ) (a b c : ℚ) : ℝ :=
  (a : ℝ) * L + (b : ℝ) * Real.log L + (c : ℝ)

/-- The rational-parameter curve a*L-b*L^2+c.
Nonnegative b gives concavity on the real line. On L ≤ R, the guard 2*b*R ≤ a gives
monotonicity. This supplies a bounded-domain alternative to logarithmic affine fitting. -/
noncomputable def concaveQuadratic (L : ℝ) (a b c : ℚ) : ℝ :=
  (a : ℝ) * L - (b : ℝ) * L ^ 2 + (c : ℝ)

/-- For nonnegative b, the logarithmic affine curve is concave on positive L.
Combine logarithm concavity with its nonnegative coefficient and the affine terms.
This justifies checking only the polyline vertices. -/
theorem concaveLogAffine_concave (a b c : ℚ) (hb : 0 ≤ b) :
    ConcaveOn ℝ (Set.Ioi 0) (fun L => concaveLogAffine L a b c) := by
  refine ⟨convex_Ioi 0, ?_⟩
  intro x hx y hy u v hu hv huv
  have hl := strictConcaveOn_log_Ioi.concaveOn.2 hx hy hu hv huv
  have hbR : (0 : ℝ) ≤ b := Rat.cast_nonneg.mpr hb
  have hm := mul_le_mul_of_nonneg_left hl hbR
  have hconst := congrArg (fun t : ℝ => t * (c : ℝ)) huv
  simp only [smul_eq_mul] at hm ⊢
  unfold concaveLogAffine
  nlinarith only [hm, hconst]

/-- For nonnegative curvature b, the quadratic fit is concave on the real line.
Negate the weighted convex-square inequality and retain the affine constant identity.
The finite certificate uses this result for all segment interiors. -/
theorem concaveQuadratic_concave (a b c : ℚ) (hb : 0 ≤ b) :
    ConcaveOn ℝ Set.univ (fun L => concaveQuadratic L a b c) := by
  have hs : ConvexOn ℝ Set.univ (fun L : ℝ => L ^ 2) :=
    (show Even (2 : ℕ) from ⟨1, rfl⟩).convexOn_pow
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy u v hu hv huv
  have hsq := hs.2 hx hy hu hv huv
  have hbR : (0 : ℝ) ≤ b := Rat.cast_nonneg.mpr hb
  have hbsq := mul_le_mul_of_nonneg_left hsq hbR
  have hconst := congrArg (fun t : ℝ => t * (c : ℝ)) huv
  simp only [smul_eq_mul] at hbsq ⊢
  unfold concaveQuadratic
  nlinarith only [hbsq, hconst]

/-- With nonnegative a and b, positive x ≤ y gives ordered logarithmic affine values.
Multiply the two monotone input terms by their nonnegative coefficients.
This preserves an upper bound after rounding record abscissas to the left. -/
theorem concaveLogAffine_mono {a b c : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) {x y : ℝ} (hx : 0 < x)
    (hxy : x ≤ y) : concaveLogAffine x a b c ≤ concaveLogAffine y a b c := by
  have hl := Real.log_le_log hx hxy
  exact
    add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left hxy (Rat.cast_nonneg.mpr ha))
        (mul_le_mul_of_nonneg_left hl (Rat.cast_nonneg.mpr hb)))
      (le_refl (c : ℝ))

/-- For nonnegative b and x ≤ y ≤ R, the guard 2*b*R ≤ a orders the quadratic values.
Factor the difference as (y-x)*(a-b*(x+y)) and check both factors.
This supplies monotonicity on the fitted finite domain. -/
theorem concaveQuadratic_mono {a b c : ℚ} (hb : 0 ≤ b) {x y R : ℝ} (hxy : x ≤ y) (hy : y ≤ R)
    (ha : 2 * (b : ℝ) * R ≤ a) : concaveQuadratic x a b c ≤ concaveQuadratic y a b c := by
  have hbR : (0 : ℝ) ≤ b := Rat.cast_nonneg.mpr hb
  have hsum : x + y ≤ 2 * R := by linarith only [hxy, hy]
  have hm := mul_le_mul_of_nonneg_left hsum hbR
  have hterm : 0 ≤ (a : ℝ) - (b : ℝ) * (x + y) := by linarith only [hm, ha]
  have hd : 0 ≤ y - x := sub_nonneg.mpr hxy
  have hp := mul_nonneg hd hterm
  unfold concaveQuadratic
  nlinarith only [hp]

/-- For a concave function, endpoint upper bounds imply the upper bound for every chord point.
Nonnegative weights summing to one preserve endpoint order; Jensen gives the final step.
Adjacent vertices of any finite polyline are a special case. -/
theorem chord_le_of_concave {F : ℝ → ℝ} {s : Set ℝ} (hF : ConcaveOn ℝ s F) {x y u v p q : ℝ}
    (hx : x ∈ s) (hy : y ∈ s) (hu : 0 ≤ u) (hv : 0 ≤ v) (hweights : u + v = 1) (hp : p ≤ F x)
    (hq : q ≤ F y) : u * p + v * q ≤ F (u * x + v * y) := by
  have hc := hF.2 hx hy hu hv hweights
  have he := add_le_add (mul_le_mul_of_nonneg_left hp hu) (mul_le_mul_of_nonneg_left hq hv)
  simpa only [smul_eq_mul] using he.trans hc

/-- Rational data for a capped concave quadratic and its finite polyline.
Fields specify the polynomial, cap, domain and vertices. They impose no proof invariant
until check = true: the checker verifies shape, monotonicity and all vertex inequalities.
This structure certifies fitting only, not the coverage of a witness enumeration. -/
structure ConcaveQuadraticFit where
  /-- Coefficient of L. -/
  linear : ℚ
  /-- Nonnegative coefficient subtracted from L squared. -/
  curvature : ℚ
  /-- Signed constant term. -/
  constant : ℚ
  /-- Constant upper plateau. -/
  cap : ℚ
  /-- Positive left endpoint of the finite logarithmic domain. -/
  left : ℚ
  /-- Right endpoint at which the derivative guard is checked. -/
  right : ℚ
  /-- Rational abscissa and ordinate pairs of the baseline polyline. -/
  vertices : List (ℚ × ℚ)

/-- Evaluate the smaller of the rational cap and the quadratic fit.
The cap handles the finite plateau without changing vertex domination.
Successful validation gives a concave curve and its bounded monotonicity. -/
noncomputable def ConcaveQuadraticFit.curve (d : ConcaveQuadraticFit) (L : ℝ) : ℝ :=
  min (d.cap : ℝ) (concaveQuadratic L d.linear d.curvature d.constant)

/-- Check positive linear coefficient and left endpoint, nonnegative curvature,
ordered domain, and the derivative guard at right. Then check every vertex lies in the domain
and below both the cap and the rational polynomial. This is a finite curve certificate only. -/
def ConcaveQuadraticFit.check (d : ConcaveQuadraticFit) : Bool :=
  decide
      (0 < d.linear ∧
        0 ≤ d.curvature ∧ 0 < d.left ∧ d.left ≤ d.right ∧ 2 * d.curvature * d.right ≤ d.linear) &&
    d.vertices.all fun v =>
      decide
        (d.left ≤ v.1 ∧
          v.1 ≤ d.right ∧ v.2 ≤ d.cap ∧ v.2 ≤ d.linear * v.1 - d.curvature * v.1 ^ 2 + d.constant)

/-- A successful finite check supplies its rational domain and coefficient guards.
Reflect the first Boolean conjunct. These conditions feed concavity and monotonicity. -/
theorem ConcaveQuadraticFit.guard {d : ConcaveQuadraticFit} (h : d.check = true) :
    0 < d.linear ∧
      0 ≤ d.curvature ∧ 0 < d.left ∧ d.left ≤ d.right ∧ 2 * d.curvature * d.right ≤ d.linear :=
  of_decide_eq_true (Bool.and_eq_true_iff.mp h).1

/-- Every member vertex lies below the real curve after a successful rational check.
Reflect the local comparisons and preserve order under rational casting.
The chord theorem uses these endpoint bounds. -/
theorem ConcaveQuadraticFit.vertex_bound {d : ConcaveQuadraticFit} (h : d.check = true) {v : ℚ × ℚ}
    (hv : v ∈ d.vertices) : (v.2 : ℝ) ≤ d.curve v.1 := by
  have ht := of_decide_eq_true (List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).2 v hv)
  apply le_min ((Rat.cast_le (K := ℝ)).mpr ht.2.2.1)
  have hp := (Rat.cast_le (K := ℝ)).mpr ht.2.2.2
  simpa only [concaveQuadratic, Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_pow] using hp

/-- The checked capped curve is concave on the real line.
Take the infimum of a constant concave function and the checked concave quadratic.
This guarantees domination between the vertices. -/
theorem ConcaveQuadraticFit.concave {d : ConcaveQuadraticFit} (h : d.check = true) :
    ConcaveOn ℝ Set.univ d.curve := by
  have hc := concaveQuadratic_concave d.linear d.curvature d.constant (d.guard h).2.1
  exact (concaveOn_const (d.cap : ℝ) convex_univ).inf hc

/-- For x ≤ y ≤ the checked right endpoint, the capped curve is nondecreasing.
Cast the derivative guard, apply quadratic monotonicity and preserve order under minimum.
The finite input-to-polyline transfer uses this property. -/
theorem ConcaveQuadraticFit.monotone {d : ConcaveQuadraticFit} (h : d.check = true) {x y : ℝ}
    (hxy : x ≤ y) (hy : y ≤ d.right) : d.curve x ≤ d.curve y := by
  have hg := d.guard h
  have ha := (Rat.cast_le (K := ℝ)).mpr hg.2.2.2.2
  simp only [Rat.cast_mul, Rat.cast_ofNat] at ha
  exact min_le_min (le_refl (d.cap : ℝ)) (concaveQuadratic_mono hg.2.1 hxy hy ha)

/-- Every chord between two checked vertices is below the curve at its weighted abscissa.
Weights must be nonnegative and sum to one; apply concavity and the checked endpoint bounds.
This covers the whole graph, without sampling its interiors. -/
theorem ConcaveQuadraticFit.chord_bound {d : ConcaveQuadraticFit} (h : d.check = true) {p q : ℚ × ℚ}
    (hp : p ∈ d.vertices) (hq : q ∈ d.vertices) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v = 1) : u * (p.2 : ℝ) + v * (q.2 : ℝ) ≤ d.curve (u * (p.1 : ℝ) + v * (q.1 : ℝ)) :=
  chord_le_of_concave (d.concave h) (Set.mem_univ _) (Set.mem_univ _) hu hv hs (d.vertex_bound h hp)
    (d.vertex_bound h hq)

/-- A convex combination of logarithms of inputs above one is positive.
Use convexity of the positive half-line. This supplies the domain for a second concave curve. -/
theorem log_combination_pos {x y u v : ℝ} (hx : 1 < x) (hy : 1 < y) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u + v = 1) : 0 < u * Real.log x + v * Real.log y := by
  have hw := (convex_Ioi (0 : ℝ)) (Real.log_pos hx) (Real.log_pos hy) hu hv hs
  change 0 < u • Real.log x + v • Real.log y at hw
  simpa only [smul_eq_mul] using hw

/-- Inputs in (1,exp R] have a weighted arithmetic mean whose logarithm is at most R.
Use interval convexity and the logarithm-exponential order equivalence.
This keeps the composed fit within its checked monotonicity domain. -/
theorem log_combination_le_upper {x y u v R : ℝ} (hx : x ∈ Set.Ioc 1 (Real.exp R))
    (hy : y ∈ Set.Ioc 1 (Real.exp R)) (hu : 0 ≤ u) (hv : 0 ≤ v) (hs : u + v = 1) :
    Real.log (u * x + v * y) ≤ R := by
  have hz := (convex_Ioc (1 : ℝ) (Real.exp R)) hx hy hu hv hs
  simp only [smul_eq_mul] at hz
  exact (Real.log_le_iff_le_exp (zero_lt_one.trans hz.1)).mpr hz.2

/-- A positive-domain concave fit nondecreasing below R remains concave after composing with log
on (1,exp R]. Apply logarithm Jensen, then monotonicity and the fit's own Jensen inequality.
Thus concavity in L also supplies concavity in the original positive input on the finite domain. -/
theorem concaveOn_log_comp_of_mono_below {F : ℝ → ℝ} {R : ℝ} (hF : ConcaveOn ℝ (Set.Ioi 0) F)
    (hmono : ∀ x y : ℝ, 0 < x → x ≤ y → y ≤ R → F x ≤ F y) :
    ConcaveOn ℝ (Set.Ioc 1 (Real.exp R)) (fun n => F (Real.log n)) := by
  refine ⟨convex_Ioc 1 (Real.exp R), ?_⟩
  intro x hx y hy u v hu hv hs
  have hl :=
    strictConcaveOn_log_Ioi.concaveOn.2 (zero_lt_one.trans hx.1) (zero_lt_one.trans hy.1) hu hv hs
  have hj := hF.2 (Real.log_pos hx.1) (Real.log_pos hy.1) hu hv hs
  simp only [smul_eq_mul] at hl hj ⊢
  exact
    hj.trans
      (hmono _ _ (log_combination_pos hx.1 hy.1 hu hv hs) hl
        (log_combination_le_upper hx hy hu hv hs))

end PseudoPrime.Analysis
