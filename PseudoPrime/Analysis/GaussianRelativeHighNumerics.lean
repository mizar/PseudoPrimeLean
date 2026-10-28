/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianRelativeFour
public import PseudoPrime.Analysis.GaussianNextTripleNumerics

/-! # Exact-conductor Gaussian numerics at coefficient 0.28237 -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The Gaussian scale at real logarithmic parameter L; multiplying by 21/10
returns the coefficient-0.28237 cutoff used by the uniform triple branch. -/
noncomputable def gaussianRefinedTripleScale (L : ℝ) : ℝ :=
  (28237 / 210000 : ℝ) * L ^ 2

/-- For L at least two trillion, compare the scale roots with rational multiples
of L. Square comparisons give the radius floor and fourth-root bound needed by
the relative-width error estimate. -/
theorem gaussianRefinedTriple_roots {L : ℝ} (hL : (2000000000000 : ℝ) ≤ L) :
    let r := Real.sqrt (gaussianRefinedTripleScale L)
    let s := Real.sqrt r
    (36669 / 100000 : ℝ) * L ≤ r ∧ 100 ≤ r ∧ 10 ≤ s ∧ s ≤ (61 / 100 : ℝ) * L / 1400000 := by
  let x := gaussianRefinedTripleScale L
  let r := Real.sqrt x
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hx : 0 ≤ x := mul_nonneg (by norm_num only : (0 : ℝ) ≤ 28237 / 210000) (sq_nonneg L)
  have hr : (36669 / 100000 : ℝ) * L ≤ r := by
    apply (Real.le_sqrt (mul_nonneg (by norm_num only) hL0) hx).mpr
    dsimp only [x, gaussianRefinedTripleScale]
    nlinarith only [sq_nonneg L]
  have hr100 : 100 ≤ r := by linarith only [hr, hL]
  have hs10 : 10 ≤ Real.sqrt r := by
    apply (Real.le_sqrt (by norm_num only) (Real.sqrt_nonneg x)).mpr
    norm_num only
    exact hr100
  have hru : r ≤ (3721 / 10000 : ℝ) * L := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · exact mul_nonneg (by norm_num only) hL0
    · dsimp only [x, gaussianRefinedTripleScale]
      nlinarith only [sq_nonneg L]
  have hsu : Real.sqrt r ≤ (61 / 100 : ℝ) * Real.sqrt L := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · exact mul_nonneg (by norm_num only) (Real.sqrt_nonneg L)
    · nlinarith only [hru, Real.sq_sqrt hL0]
  have hm := mul_le_mul_of_nonneg_right (show (1960000000000 : ℝ) ≤ L by linarith only [hL]) hL0
  have hrootL : Real.sqrt L ≤ L / 1400000 := by
    nlinarith only [Real.sq_sqrt hL0, hm, Real.sqrt_nonneg L, hL0]
  have hmul := mul_le_mul_of_nonneg_left hrootL (by norm_num only : (0 : ℝ) ≤ 61 / 100)
  exact ⟨hr, hr100, hs10, by linarith only [hsu, hmul]⟩

/-- For log n at most L and L at least two trillion, bound the actual signed
50000-prefix error. The pole is at most four and the two certified tails sum
to at most 273/1000; this feeds the exact-conductor relative comparison. -/
theorem gaussianRefinedTriple_error {n : ℕ} {L : ℝ} (hL : (2000000000000 : ℝ) ≤ L)
    (hn : Real.log n ≤ L) :
    let r := Real.sqrt (gaussianRefinedTripleScale L)
    LLS.PaperStatements.gaussianPrefixError (489311 / 100000) n (r ^ 2) ≤
      (12871 / 1000 : ℝ) - 2 * (489311 / 100000) + 4 + 273 / 1000 := by
  let r := Real.sqrt (gaussianRefinedTripleScale L)
  have hroots := gaussianRefinedTriple_roots hL
  change
    (36669 / 100000 : ℝ) * L ≤ r ∧
      100 ≤ r ∧ 10 ≤ Real.sqrt r ∧ Real.sqrt r ≤ (61 / 100 : ℝ) * L / 1400000 at hroots
  have hrpos : 0 < r := by linarith only [hroots.2.1]
  have hpole : (2129 / 2000 : ℝ) * (((7 / 6 : ℝ) * Real.log n + 4) / r) ≤ 4 := by
    rw [← mul_div_assoc, div_le_iff₀ hrpos]
    linarith only [hroots.1, hL, hn]
  have ht := gaussian1000_tail hroots.2.1
  dsimp only [LLS.PaperStatements.gaussianPrefixError]
  rw [Real.sqrt_sq hrpos.le]
  linarith only [hpole, ht.1, ht.2]

/-- Given the certified root and error bounds at L at least two trillion, the
index-four relative scalar comparison is impossible. Bound both reciprocal
terms at their positive floors and use the strict rational leading margin.
This closes the actual high-range Gaussian comparison without a coarse conductor cost. -/
theorem gaussianRefinedTriple_contradiction {L : ℝ} (hL : (2000000000000 : ℝ) ≤ L) {r s A : ℝ}
    (hr : (36669 / 100000 : ℝ) * L ≤ r) (hr100 : 100 ≤ r) (hs10 : 10 ≤ s)
    (hs : s ≤ (61 / 100 : ℝ) * L / 1400000)
    (hA : A ≤ (12871 / 1000 : ℝ) - 2 * (489311 / 100000) + 4 + 273 / 1000)
    (hcmp :
      (10971611 / 5000000 : ℝ) * r ≤
        2 * (20115621 / 50000000 : ℝ) * L + (28794111 / 12500000 : ℝ) * s +
          4 *
            (21 * (2129 / 2000 : ℝ) / (10 * (2 / 5 : ℝ) * s) +
              1839 * (2129 / 2000 : ℝ) / (1000 * r)) +
          13 +
          3 * A) :
    False := by
  have hspos : 0 < s := by linarith only [hs10]
  have hrpos : 0 < r := by linarith only [hr100]
  have hleft : 21 * (2129 / 2000 : ℝ) / (10 * (2 / 5 : ℝ) * s) ≤ 21 * (2129 / 2000 : ℝ) / 40 := by
    apply (div_le_iff₀ (mul_pos (by norm_num only) hspos)).mpr
    nlinarith only [hs10]
  have hright : 1839 * (2129 / 2000 : ℝ) / (1000 * r) ≤ 1839 * (2129 / 2000 : ℝ) / 100000 := by
    apply (div_le_iff₀ (mul_pos (by norm_num only) hrpos)).mpr
    nlinarith only [hr100]
  nlinarith only [hcmp, hr, hs, hA, hleft, hright, hL]

end PseudoPrime.Analysis
