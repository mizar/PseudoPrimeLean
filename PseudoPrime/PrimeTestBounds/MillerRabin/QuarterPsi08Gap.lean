/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPsi08Concavity
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentTailClosed
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterReflectedMoments

/-! # The central comparison with the four-fifths Chebyshev bound -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The central comparison at radius `r = log n / 2`. The existing reflected
moment polynomial and closed Euler tail supply the two nonlocal error terms. -/
noncomputable def quarterPsi08Gap (r : ℝ) : ℝ :=
  let a : ℝ := 27 / 25
  let C : ℝ := a ^ 5 / 120 * (58721 / 10 ^ 6)
  let c : ℝ := 3 / 4 - a ^ 5 * (24439 / 50000)
  let z : ℝ := 21 / 8 + 2 * Real.log r
  a ^ 5 * (3117 / 400 - 1151 / 5000 - 351 / (200 * r)) - c * r - 39 / 1000 * a ^ 2 -
    (4 * r + 5517 / 1000) * C * r ^ (-(54 / 25 : ℝ)) * z ^ 5 -
    C * r ^ (-(54 / 25 : ℝ)) * quarterMomentPolynomial z -
    4 * quarterEulerClosedTailCap (r ^ 2)

/-- Once the three numerical comparisons and concavity are verified for the
concrete gap, it is positive throughout the central log interval. -/
theorem quarter_psi08_gap_pos {L : ℝ} (hL : L ∈ Set.Icc 76 533)
    (hbox : ∀ r ∈ Set.Icc 37 42, 2 < quarterPsi08Gap r)
    (hc : ConcaveOn ℝ (Set.Ici 42) quarterPsi08Gap) (hl : 3.65 < quarterPsi08Gap 42)
    (hr : 1 / 2000 < quarterPsi08Gap (533 / 2)) : 0 < quarterPsi08Gap (L / 2) := by
  exact quarter_psi08_pos hL hbox hc hl hr

/-- The reflected error is a positive combination of the shifted logarithmic
monomials. The existing polynomial supplies its exact coefficients. -/
theorem quarter_psi08_reflected_convex :
    ConvexOn ℝ (Set.Ici 42)
      (fun r : ℝ ↦ r ^ (-(54 / 25 : ℝ)) * quarterMomentPolynomial (21 / 8 + 2 * Real.log r)) := by
  have term (c : ℝ) (k : ℕ) (hc : 0 ≤ c) (hk : k ≤ 5) :=
    (quarter_psi08_main_convex (p := 54 / 25) (by norm_num only) hk).smul hc
  refine
    ((term (1244 / 1000) 5 (by norm_num only) (by norm_num only)) |>.add
                  (term (14280 / 1000) 4 (by norm_num only) (by norm_num only)) |>.add
                (term (103820 / 1000) 3 (by norm_num only) (by norm_num only)) |>.add
              (term (546990 / 1000) 2 (by norm_num only) (by norm_num only)) |>.add
            (term (1905405 / 1000) 1 (by norm_num only) (by norm_num only)) |>.add
          (term (3295239 / 1000) 0 (by norm_num only) (by norm_num only))).congr
      ?_
  intro r _
  simp only [Pi.add_apply, smul_eq_mul, quarterMomentPolynomial, pow_zero, mul_one]
  ring

/-- The linear conductor factor shifts one exponent by one, giving a
positive combination of two shifted degree-five monomials. -/
theorem quarter_psi08_conductor_convex :
    ConvexOn ℝ (Set.Ici 42)
      (fun r : ℝ ↦
        (4 * r + 5517 / 1000) * r ^ (-(54 / 25 : ℝ)) * (21 / 8 + 2 * Real.log r) ^ 5) := by
  have h₁ :=
    (quarter_psi08_main_convex (p := 29 / 25) (k := 5) (by norm_num only) (by norm_num only)).smul
      (show (0 : ℝ) ≤ 4 by norm_num only)
  have h₂ :=
    (quarter_psi08_main_convex (p := 54 / 25) (k := 5) (by norm_num only) (by norm_num only)).smul
      (show (0 : ℝ) ≤ 5517 / 1000 by norm_num only)
  refine (h₁.add h₂).congr ?_
  intro r hr
  have hr' : (42 : ℝ) ≤ r := hr
  have hp : 0 < r := by linarith only [hr']
  have he : r * r ^ (-(54 / 25 : ℝ)) = r ^ (-(29 / 25 : ℝ)) := by
    calc
      r * r ^ (-(54 / 25 : ℝ)) = r ^ (1 : ℝ) * r ^ (-(54 / 25 : ℝ)) := by rw [Real.rpow_one]
      _ = r ^ (-(29 / 25 : ℝ)) := by
        rw [← Real.rpow_add hp, show 1 + -(54 / 25 : ℝ) = -(29 / 25 : ℝ) by norm_num only]
  simp only [Pi.add_apply, smul_eq_mul, add_mul, mul_assoc, he]

/-- Multiplying a positive-rate tail polynomial by a decaying real power
preserves convexity for the three degrees used in the Euler estimate. -/
private theorem tail_poly_convex {p α : ℝ} (hp : 29 / 25 ≤ p) (hα : 0 < α) (k : ℕ) (hk : k ≤ 2) :
    ConvexOn ℝ (Set.Ici 42)
      (fun r : ℝ ↦ r ^ (-p) * Analysis.logPowerTailPoly α k (2 * Real.log r)) := by
  induction k with
  | zero =>
    refine ((quarter_psi08_tail_convex hp hk).smul (one_div_nonneg.mpr hα.le)).congr ?_
    intro r _
    simp only [smul_eq_mul, pow_zero, mul_one, Analysis.logPowerTailPoly]
    ring
  | succ k ih =>
    have h₁ := (quarter_psi08_tail_convex hp hk).smul (one_div_nonneg.mpr hα.le)
    have h₂ := (ih (Nat.le_of_succ_le hk)).smul (div_nonneg (Nat.cast_nonneg (k + 1)) hα.le)
    refine (h₁.add h₂).congr ?_
    intro r _
    simp only [Pi.add_apply, smul_eq_mul, Analysis.logPowerTailPoly]
    ring

/-- Each closed Euler moment is convex on the central radius ray after the
square substitution converts its three terms to logarithmic monomials. -/
private theorem tail_moment_convex (k : ℕ) (hk : k ≤ 2) :
    ConvexOn ℝ (Set.Ici 42) (fun r : ℝ ↦ quarterMomentClosedTail k (r ^ 2)) := by
  have h₁ :=
    (quarter_psi08_tail_convex (p := 83 / 50) (by norm_num only) hk).smul
      (show (0 : ℝ) ≤ 2 by norm_num only)
  have h₂ :=
    tail_poly_convex (p := 29 / 25) (α := 29 / 50) (by norm_num only) (by norm_num only) k hk
  have h₃ :=
    (tail_poly_convex (p := 83 / 50) (α := 83 / 100) (by norm_num only) (by norm_num only) k
          hk).smul
      (show (0 : ℝ) ≤ 3 / 4 by norm_num only)
  refine ((h₁.add h₂).add h₃).congr ?_
  intro r hr
  have hr' : (42 : ℝ) ≤ r := hr
  have hp : 0 < r := by linarith only [hr']
  have he (s : ℝ) : (r ^ (2 : ℕ)) ^ s = r ^ (2 * s) := by rw [Real.rpow_mul hp.le, Real.rpow_ofNat]
  simp only [Pi.add_apply, smul_eq_mul, quarterMomentClosedTail,
    AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight, Real.log_pow, Nat.cast_ofNat, he]
  rw [show 2 * -(29 / 50 : ℝ) = -(29 / 25 : ℝ) by norm_num only,
    show 2 * -(83 / 100 : ℝ) = -(83 / 50 : ℝ) by norm_num only,
    show 2 * -(79 / 50 : ℝ) = -(79 / 25 : ℝ) by norm_num only,
    show 2 * (3 / 4 : ℝ) = 3 / 2 by norm_num only]
  have hh := Real.rpow_add hp (-(79 / 25 : ℝ)) (3 / 2)
  rw [show -(79 / 25 : ℝ) + 3 / 2 = -(83 / 50 : ℝ) by norm_num only] at hh
  linear_combination (2 * (2 * Real.log r) ^ k) * hh

/-- The three closed Euler moments have positive coefficients, so their
combined error is convex on the central radius ray. -/
theorem quarter_psi08_euler_convex :
    ConvexOn ℝ (Set.Ici 42) (fun r : ℝ ↦ quarterEulerClosedTailCap (r ^ 2)) := by
  have h₀ := (tail_moment_convex 0 (by norm_num only)).smul (show (0 : ℝ) ≤ 3 / 8 by norm_num only)
  have h₁ :=
    (tail_moment_convex 1 (by norm_num only)).smul (show (0 : ℝ) ≤ 81 / 200 by norm_num only)
  have h₂ :=
    (tail_moment_convex 2 (by norm_num only)).smul (show (0 : ℝ) ≤ 729 / 5000 by norm_num only)
  exact (h₀.add h₁).add h₂

/-- The central gap is concave on radii at least 42: its affine part is
reduced by convex reciprocal, conductor, reflected and Euler terms. -/
theorem quarter_psi08_gap_concave : ConcaveOn ℝ (Set.Ici 42) quarterPsi08Gap := by
  let a : ℝ := 27 / 25
  let C : ℝ := a ^ 5 / 120 * (58721 / 10 ^ 6)
  let c : ℝ := 3 / 4 - a ^ 5 * (24439 / 50000)
  have hC : 0 ≤ C := by norm_num only [C, a]
  have hc : 0 ≤ c := by norm_num only [c, a]
  have hi :=
    quarter_logPower_convex (a := 42) (p := 1) (b := 1) (by norm_num only) 0
      (fun r hr ↦ by
        have hh : (42 : ℝ) ≤ r := hr
        have hn : 0 ≤ Real.log r := Real.log_nonneg (by linarith only [hh])
        linarith only [hn])
      (fun r _ ↦ by
        rw [Nat.cast_zero]
        unfold quarterPsi08LogCurvature
        nlinarith only [sq_nonneg (1 + 2 * Real.log r)])
  have hi' : ConvexOn ℝ (Set.Ici 42) (fun r : ℝ ↦ r⁻¹) := by
    simpa only [pow_zero, mul_one, Real.rpow_neg_one] using hi
  have hlin :=
    (concaveOn_const (𝕜 := ℝ) (a ^ 5 * (3117 / 400 - 1151 / 5000) - 39 / 1000 * a ^ 2)
          (convex_Ici (42 : ℝ))).sub
      ((convexOn_id (𝕜 := ℝ) (convex_Ici (42 : ℝ))).smul hc)
  have hrec := hi'.smul (show 0 ≤ a ^ 5 * (351 / 200) by norm_num only [a])
  refine
    ((((hlin.sub hrec).sub (quarter_psi08_conductor_convex.smul hC)).sub
              (quarter_psi08_reflected_convex.smul hC)).sub
          (quarter_psi08_euler_convex.smul (show (0 : ℝ) ≤ 4 by norm_num only))).congr
      ?_
  intro r hr
  have hp : r ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 42) hr)
  simp only [Pi.sub_apply, smul_eq_mul, id_eq, quarterPsi08Gap, a, C, c]
  rw [show (351 / (200 * r) : ℝ) = (351 / 200) * r⁻¹ by field_simp [hp]]
  ring

end PseudoPrime.PrimeTestBounds.MillerRabin
