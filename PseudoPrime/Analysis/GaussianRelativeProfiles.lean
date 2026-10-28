/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianRelativeHighNumerics

/-! # Relative Gaussian profile certificates -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Rational input certificate for the index-four Gaussian comparison.
C is the final cutoff coefficient, T its entrance, a the radius lower slope,
and v the denominator controlling the fourth root. The margin is the exact
relative-conductor budget with independent scalar scale equal to one. -/
structure GaussianRelativeProfile where
  C : ℝ
  T : ℝ
  a : ℝ
  v : ℝ
  entry : 30000000000 ≤ T
  root : 36 / 100 ≤ a
  square : a ^ 2 ≤ C / (21 / 10)
  upper : C ≤ 28237 / 100000
  fourth : 0 < v ∧ v ^ 2 ≤ T
  margin :
    38 <
      ((10971611 / 5000000) * a - 2 * (20115621 / 50000000) -
          (61 / 100) * (28794111 / 12500000) / v) *
        T

/-- The common triple certificate proves coefficient 0.28237 from thirty billion. -/
noncomputable def gaussianRelativeCommon : GaussianRelativeProfile where
  C := 28237 / 100000
  T := 30000000000
  a := 36669 / 100000
  v := 170000
  entry := by norm_num only
  root := by norm_num only
  square := by norm_num only
  upper := by norm_num only
  fourth := by norm_num only [and_self]
  margin := by norm_num only

/-- The sharper triple certificate proves coefficient 0.2823622 from 1.82 trillion. -/
noncomputable def gaussianRelativeSharper : GaussianRelativeProfile where
  C := 1411811 / 5000000
  T := 1820000000000
  a := 36668541 / 100000000
  v := 1340000
  entry := by norm_num only
  root := by norm_num only
  square := by norm_num only
  upper := by norm_num only
  fourth := by norm_num only [and_self]
  margin := by norm_num only

/-- At L above a certified entrance, the actual Gaussian scale has radius
at least a L and 500. Its square root lies between ten and (61/100)L/v.
These bounds supply the relative width and reciprocal error floors. -/
theorem gaussianRelativeProfile_roots (f : GaussianRelativeProfile) {L : ℝ} (hL : f.T ≤ L) :
    let r := Real.sqrt (f.C / (21 / 10) * L ^ 2)
    let s := Real.sqrt r
    f.a * L ≤ r ∧ 500 ≤ r ∧ 10 ≤ s ∧ s ≤ (61 / 100 : ℝ) * L / f.v := by
  let x := f.C / (21 / 10) * L ^ 2
  let r := Real.sqrt x
  have hL0 : 0 ≤ L := by linarith only [hL, f.entry]
  have ha : 0 ≤ f.a := by linarith only [f.root]
  have hx : 0 ≤ x := mul_nonneg ((sq_nonneg f.a).trans f.square) (sq_nonneg L)
  have hr : f.a * L ≤ r := by
    apply (Real.le_sqrt (mul_nonneg ha hL0) hx).mpr
    dsimp only [x]
    nlinarith only [mul_le_mul_of_nonneg_right f.square (sq_nonneg L)]
  have hr500 : 500 ≤ r := by
    have hh := mul_le_mul_of_nonneg_right f.root hL0
    nlinarith only [hr, hh, hL, f.entry]
  have hs10 : 10 ≤ Real.sqrt r := by
    apply (Real.le_sqrt (by norm_num only) (Real.sqrt_nonneg x)).mpr
    norm_num only
    exact (by linarith only [hr500])
  have hru : r ≤ (3721 / 10000 : ℝ) * L := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · exact mul_nonneg (by norm_num only) hL0
    · dsimp only [x]
      nlinarith only [mul_le_mul_of_nonneg_right f.upper (sq_nonneg L)]
  have hsu : Real.sqrt r ≤ (61 / 100 : ℝ) * Real.sqrt L := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · exact mul_nonneg (by norm_num only) (Real.sqrt_nonneg L)
    · nlinarith only [hru, Real.sq_sqrt hL0]
  have hm := mul_le_mul_of_nonneg_right (f.fourth.2.trans hL) hL0
  have hrootL : Real.sqrt L ≤ L / f.v := by
    apply (le_div_iff₀ f.fourth.1).2
    have hsq := Real.sq_sqrt hL0
    have hpos := mul_nonneg (Real.sqrt_nonneg L) f.fourth.1.le
    nlinarith only [hsq, hm, hpos, hL0]
  have hmul := mul_le_mul_of_nonneg_left hrootL (by norm_num only : (0 : ℝ) ≤ 61 / 100)
  refine ⟨hr, hr500, hs10, ?_⟩
  change Real.sqrt r ≤ (61 / 100 : ℝ) * L / f.v
  simpa only [mul_div_assoc] using hsu.trans hmul

/-- The signed error at the actual profile scale is bounded by the old
50000-prefix, a pole budget of four, and the two certified tails. -/
theorem gaussianRelativeProfile_error (f : GaussianRelativeProfile) {n : ℕ} {L : ℝ} (hL : f.T ≤ L)
    (hn : Real.log n ≤ L) :
    let r := Real.sqrt (f.C / (21 / 10) * L ^ 2)
    LLS.PaperStatements.gaussianPrefixError (489311 / 100000) n (r ^ 2) ≤
      (12871 / 1000 : ℝ) - 2 * (489311 / 100000) + 4 + 273 / 1000 := by
  let r := Real.sqrt (f.C / (21 / 10) * L ^ 2)
  have hroots := gaussianRelativeProfile_roots f hL
  change f.a * L ≤ r ∧ 500 ≤ r ∧ 10 ≤ Real.sqrt r ∧ Real.sqrt r ≤ (61 / 100 : ℝ) * L / f.v at hroots
  have hrpos : 0 < r := by linarith only [hroots.2.1]
  have hL0 : 0 ≤ L := by linarith only [hL, f.entry]
  have hroot := mul_le_mul_of_nonneg_right f.root hL0
  have hpole : (2129 / 2000 : ℝ) * (((7 / 6 : ℝ) * Real.log n + 4) / r) ≤ 4 := by
    rw [← mul_div_assoc, div_le_iff₀ hrpos]
    linarith only [hroots.1, hroot, hL, f.entry, hn]
  have ht := gaussian1000_tail (show 100 ≤ r by linarith only [hroots.2.1])
  dsimp only [LLS.PaperStatements.gaussianPrefixError]
  rw [Real.sqrt_sq hrpos.le]
  change
    (12871 / 1000 : ℝ) - 2 * (489311 / 100000) + (512 / 27) / r ^ 2 +
        (2129 / 2000) * (((7 / 6) * Real.log n + 4) / r) +
        (473 / 10) * (r ^ 2) ^ (-9 / 16 : ℝ) ≤
      _
  linarith only [hpole, ht.1, ht.2]

/-- The certified radius and error bounds contradict the actual index-four
relative scalar comparison. The reciprocal floors leave a residual below 38;
the profile's strict entrance margin absorbs that residual. -/
theorem gaussianRelativeProfile_false (f : GaussianRelativeProfile) {L : ℝ} (hL : f.T ≤ L)
    {r s A : ℝ} (hr : f.a * L ≤ r) (hr500 : 500 ≤ r) (hs10 : 10 ≤ s)
    (hs : s ≤ (61 / 100 : ℝ) * L / f.v)
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
  have hrpos : 0 < r := by linarith only [hr500]
  have hleft : 21 * (2129 / 2000 : ℝ) / (10 * (2 / 5 : ℝ) * s) ≤ 21 * (2129 / 2000 : ℝ) / 40 := by
    apply (div_le_iff₀ (mul_pos (by norm_num only) hspos)).mpr
    nlinarith only [hs10]
  have hright : 1839 * (2129 / 2000 : ℝ) / (1000 * r) ≤ 1839 * (2129 / 2000 : ℝ) / 500000 := by
    apply (div_le_iff₀ (mul_pos (by norm_num only) hrpos)).mpr
    nlinarith only [hr500]
  let d :=
    (10971611 / 5000000 : ℝ) * f.a - 2 * (20115621 / 50000000 : ℝ) -
      (61 / 100 : ℝ) * (28794111 / 12500000 : ℝ) / f.v
  have hmargin : 38 < d * f.T := f.margin
  have hd : 0 < d := by
    have hT : 0 < f.T := by linarith only [f.entry]
    by_contra hn
    have hnp := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hT.le
    linarith only [hmargin, hnp]
  have hmul := mul_le_mul_of_nonneg_left hL hd.le
  have hbound : d * L ≤ (1869354731 / 50000000 : ℝ) := by
    dsimp only [d]
    simp only [div_eq_mul_inv] at hs ⊢
    nlinarith only [hcmp, hr, hs, hA, hleft, hright]
  linarith only [hmargin, hmul, hbound]

end PseudoPrime.Analysis
