/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Tactic

/-! # Lower bounds between samples from an upper bound on the second derivative

Subtracting a quadratic makes the function concave. Its chord controls the loss between
two lower-certified endpoints by one eighth of the second-derivative bound times the
squared interval length.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- On [a,b], subtracting M x²/2 from a twice differentiable function with f''≤M
produces a concave function. Compute the two corrected derivatives and apply the
second-derivative criterion. This supplies the chord used in sample interpolation. -/
theorem concaveOn_quadratic_correction_of_second_deriv_le {f f' f'' : ℝ → ℝ} {a b M : ℝ}
    (hf : ∀ x ∈ Set.Icc a b, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Set.Icc a b, HasDerivAt f' (f'' x) x) (hb : ∀ x ∈ Set.Icc a b, f'' x ≤ M) :
    ConcaveOn ℝ (Set.Icc a b) (fun x ↦ f x - M / 2 * x ^ 2) := by
  have hg (x : ℝ) (hx : x ∈ Set.Icc a b) :
    HasDerivAt (fun y ↦ f y - M / 2 * y ^ 2) (f' x - M * x) x := by
    have h := (hf x hx).sub (((hasDerivAt_id x).pow 2).const_mul (M / 2))
    have hd : f' x - M / 2 * ((2 : ℝ) * x ^ (2 - 1) * 1) = f' x - M * x := by ring
    convert h.congr_deriv hd using 1
    ext y
    rfl
  have hg' (x : ℝ) (hx : x ∈ Set.Icc a b) : HasDerivAt (fun y ↦ f' y - M * y) (f'' x - M) x := by
    convert (hf' x hx).sub ((hasDerivAt_id x).const_mul M) using 1
    · ext y
      rfl
    · simp only [mul_one]
  apply
    concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc a b)
      (fun x hx ↦ (hg x hx).continuousAt.continuousWithinAt)
      (fun x hx ↦ (hg x (interior_subset hx)).hasDerivWithinAt)
      (fun x hx ↦ (hg' x (interior_subset hx)).hasDerivWithinAt)
  intro x hx
  exact sub_nonpos.mpr (hb x (interior_subset hx))

/-- If f(x)-M x²/2 is concave on [a,b] with M≥0 and both endpoint values are at least c,
every convex combination has value at least c-M(b-a)²/8. The chord formula and
u(1-u)≤1/4 give the worst-case loss. This needs no differentiability hypothesis. -/
theorem lower_bound_of_concave_quadratic {f : ℝ → ℝ} {a b M c u : ℝ} (hab : a ≤ b) (hM : 0 ≤ M)
    (hc : ConcaveOn ℝ (Set.Icc a b) (fun x ↦ f x - M / 2 * x ^ 2)) (ha : c ≤ f a) (hb : c ≤ f b)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) : c - M * (b - a) ^ 2 / 8 ≤ f ((1 - u) * a + u * b) := by
  have hleft := mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr hu1)
  have hright := mul_le_mul_of_nonneg_left hb hu
  have hweighted : c ≤ (1 - u) * f a + u * f b := by nlinarith only [hleft, hright]
  have hchord :=
    hc.2 (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab) (sub_nonneg.mpr hu1) hu
      (by ring : 1 - u + u = 1)
  simp only [smul_eq_mul] at hchord
  have huquarter : u * (1 - u) ≤ 1 / 4 := by nlinarith only [sq_nonneg (u - 1 / 2)]
  have herror :=
    mul_le_mul_of_nonneg_left huquarter
      (show 0 ≤ M / 2 * (b - a) ^ 2 from
        mul_nonneg (div_nonneg hM (by norm_num only)) (sq_nonneg (b - a)))
  nlinarith only [hweighted, hchord, herror]

/-- Given two derivatives and f''≤M on [a,b], with M≥0 and endpoint lower bound c,
the value at any convex combination is at least c-M(b-a)²/8. Quadratic correction
reduces the claim to concavity. The bound supports rigorous finite sample certificates. -/
theorem lower_bound_of_second_deriv_le {f f' f'' : ℝ → ℝ} {a b M c u : ℝ} (hab : a ≤ b) (hM : 0 ≤ M)
    (hf : ∀ x ∈ Set.Icc a b, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Set.Icc a b, HasDerivAt f' (f'' x) x) (hbound : ∀ x ∈ Set.Icc a b, f'' x ≤ M)
    (ha : c ≤ f a) (hb : c ≤ f b) (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    c - M * (b - a) ^ 2 / 8 ≤ f ((1 - u) * a + u * b) := by
  exact
    lower_bound_of_concave_quadratic hab hM
      (concaveOn_quadratic_correction_of_second_deriv_le hf hf' hbound) ha hb hu hu1

/-- On a nondegenerate interval [a,b], a second-derivative upper bound M≥0 and
endpoint lower bound c imply f(x)≥c-M(b-a)²/8 for every x in the interval.
Use the barycentric coordinate (x-a)/(b-a) in the chord comparison. -/
theorem lower_bound_on_interval_of_second_deriv_le {f f' f'' : ℝ → ℝ} {a b M c x : ℝ} (hab : a < b)
    (hM : 0 ≤ M) (hf : ∀ y ∈ Set.Icc a b, HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Set.Icc a b, HasDerivAt f' (f'' y) y) (hbound : ∀ y ∈ Set.Icc a b, f'' y ≤ M)
    (ha : c ≤ f a) (hb : c ≤ f b) (hx : x ∈ Set.Icc a b) : c - M * (b - a) ^ 2 / 8 ≤ f x := by
  have hd : 0 < b - a := sub_pos.mpr hab
  have hu : 0 ≤ (x - a) / (b - a) := div_nonneg (sub_nonneg.mpr hx.1) hd.le
  have hu1 : (x - a) / (b - a) ≤ 1 := (div_le_one₀ hd).mpr (by linarith only [hx.2])
  have hp : (1 - (x - a) / (b - a)) * a + (x - a) / (b - a) * b = x := by
    field_simp (discharger := exact hd.ne')
    ring
  simpa only [hp] using lower_bound_of_second_deriv_le hab.le hM hf hf' hbound ha hb hu hu1

/-- For an interval of length at most 1/500, endpoint values at least 1/25000 and
second derivative at most 54 give the uniform lower bound 13/1000000.
Insert the exact rational constants into the general interpolation loss. This is the
sample-to-interval margin used by the Gamma resolvent certificate. -/
theorem lower_bound_on_interval_of_second_deriv_le_fifty_four {f f' f'' : ℝ → ℝ} {a b x : ℝ}
    (hab : a < b) (hwidth : b - a ≤ 1 / 500) (hf : ∀ y ∈ Set.Icc a b, HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Set.Icc a b, HasDerivAt f' (f'' y) y) (hbound : ∀ y ∈ Set.Icc a b, f'' y ≤ 54)
    (ha : 1 / 25000 ≤ f a) (hb : 1 / 25000 ≤ f b) (hx : x ∈ Set.Icc a b) :
    (13 / 1000000 : ℝ) ≤ f x := by
  have h :=
    lower_bound_on_interval_of_second_deriv_le hab (by norm_num only : (0 : ℝ) ≤ 54) hf hf' hbound
      ha hb hx
  have hs := pow_le_pow_left₀ (sub_nonneg.mpr hab.le) hwidth 2
  nlinarith only [h, hs]

/-- Every point of [0,16] lies in a grid cell of width 1/500 with left index below
8000. Use the floor of 500x, treating the right endpoint separately. This locates the
two sample values needed for the compact Gamma certificate. -/
theorem exists_cell_on_zero_sixteen_grid {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 16) :
    ∃ j : ℕ, j < 8000 ∧ x ∈ Set.Icc ((j : ℝ) / 500) (((j + 1 : ℕ) : ℝ) / 500) := by
  by_cases he : x = 16
  · refine ⟨7999, by norm_num only, ?_⟩
    rw [he]
    norm_num only [Set.mem_Icc, Nat.cast_add, Nat.cast_one, and_self]
  · have hl : x < 16 := lt_of_le_of_ne hx.2 he
    have hn : 0 ≤ 500 * x := mul_nonneg (by norm_num only) hx.1
    have hj : Nat.floor (500 * x) < 8000 :=
      (Nat.floor_lt hn).mpr
        (by
          norm_num only; linarith only [hl])
    refine ⟨Nat.floor (500 * x), hj, ?_⟩
    have hlo := Nat.floor_le hn
    have hhi := Nat.lt_floor_add_one (500 * x)
    constructor
    · exact (div_le_iff₀ (by norm_num only : (0 : ℝ) < 500)).mpr (by linarith only [hlo])
    · rw [Nat.cast_add, Nat.cast_one]
      exact (le_div_iff₀ (by norm_num only : (0 : ℝ) < 500)).mpr (by linarith only [hhi])

/-- On [0,16], twice differentiability, f''≤54 and sample values at least 1/25000
on the 8001 nodes j/500 imply f≥13/1000000 everywhere. Locate a grid cell and
apply the endpoint interpolation estimate. This converts finite node bounds into a
uniform compact-interval bound without trusting the sampling procedure. -/
theorem lower_bound_on_zero_sixteen_of_grid_and_second_deriv_le {f f' f'' : ℝ → ℝ}
    (hf : ∀ x ∈ Set.Icc (0 : ℝ) 16, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Set.Icc (0 : ℝ) 16, HasDerivAt f' (f'' x) x)
    (hbound : ∀ x ∈ Set.Icc (0 : ℝ) 16, f'' x ≤ 54)
    (hnodes : ∀ j : ℕ, j ≤ 8000 → 1 / 25000 ≤ f ((j : ℝ) / 500)) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 16) : (13 / 1000000 : ℝ) ≤ f x := by
  obtain ⟨j, hj, hcell⟩ := exists_cell_on_zero_sixteen_grid hx
  have hju : j + 1 ≤ 8000 := Nat.succ_le_iff.mpr hj
  have hjuR : ((j + 1 : ℕ) : ℝ) ≤ 8000 := by exact_mod_cast hju
  have hsub {y : ℝ} (hy : y ∈ Set.Icc ((j : ℝ) / 500) (((j + 1 : ℕ) : ℝ) / 500)) :
    y ∈ Set.Icc (0 : ℝ) 16 := by
    constructor
    · exact (div_nonneg (Nat.cast_nonneg j) (by norm_num only : (0 : ℝ) ≤ 500)).trans hy.1
    · have hu := hy.2
      linarith only [hu, hjuR]
  have hab : (j : ℝ) / 500 < ((j + 1 : ℕ) : ℝ) / 500 := by
    apply (div_lt_div_iff_of_pos_right (by norm_num only : (0 : ℝ) < 500)).mpr
    rw [Nat.cast_add, Nat.cast_one]
    exact lt_add_one _
  have hw : ((j + 1 : ℕ) : ℝ) / 500 - (j : ℝ) / 500 ≤ 1 / 500 := by
    rw [Nat.cast_add, Nat.cast_one]
    exact le_of_eq (by ring)
  exact
    lower_bound_on_interval_of_second_deriv_le_fifty_four hab hw (fun y hy ↦ hf y (hsub hy))
      (fun y hy ↦ hf' y (hsub hy)) (fun y hy ↦ hbound y (hsub hy)) (hnodes j hj.le)
      (hnodes (j + 1) hju) hcell

end PseudoPrime.Analysis
