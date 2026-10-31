/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.AffineConductorLogBounds
public import PseudoPrime.LLS.RefinedConductorPrimeExclusionBounds
public import PseudoPrime.LLS.PaperStatements.RefinedConductorPrimeExclusionBounds

/-! # Conductor root witnesses from affine logarithmic comparison -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH for primitive χ of level q ≥ 3 and excluded m ≠ 0, any y ≥ 200
with the displayed strict affine comparison contains a non-one prime outside m.
Contradict the improved half-log comparison. This leaves the choice of cutoff generic. -/
theorem exists_prime_ne_one_of_affine_conductor_gap {q m : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 3 ≤ q) (hp : χ.IsPrimitive)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hm : m ≠ 0) {y : ℝ}
    (hy : 200 ≤ y)
    (hgap :
      ((21 / 4 : ℝ) * Real.log q + 607 / 10) * Real.sqrt y +
          (7 / 5 : ℝ) * (∑ r ∈ m.primeFactors, Real.log r) <
        y / 2) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ y ∧ ¬p ∣ m ∧ χ p ≠ 1 := by
  classical
  by_contra hnone
  have hno (p : ℕ) (hp : p.Prime) (hb : (p : ℝ) ≤ y) (hd : ¬p ∣ m) : χ p = 1 := by
    by_contra hne
    exact hnone ⟨p, hp, hb, hd, hne⟩
  exact (log_half_no_witness_affine_conductor_comparison χ hq hp hGRH hm hy hno).not_gt hgap

/-- For real B and D ≥ 0, the squared root radius is at most 4B²+2D.
Use the square-root identity and (B-sqrt(B²+D))² ≥ 0.
This gives a polynomial envelope with an arbitrary nonnegative tail cost. -/
theorem root_radius_sq_le_polynomial {B D : ℝ} (hD : 0 ≤ D) :
    (B + Real.sqrt (B ^ 2 + D)) ^ 2 ≤ 4 * B ^ 2 + 2 * D := by
  have hs := Real.sq_sqrt (add_nonneg (sq_nonneg B) hD)
  nlinarith only [hs, sq_nonneg (B - Real.sqrt (B ^ 2 + D))]

/-- Under GRH for primitive χ of level q ≥ 3 and m ≠ 0, a non-one prime outside
m lies below the displayed root bound with radius (21/4)log(q)+617/10 and tail
(14/5)E(m). Apply the strict root comparison to the retained exclusion coefficient.
The radius automatically meets the analytic starting scale. -/
theorem exists_prime_ne_one_le_affine_conductor_root {q m : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 3 ≤ q) (hp : χ.IsPrimitive)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hm : m ≠ 0) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤
          ((21 / 4 : ℝ) * Real.log q + 617 / 10 +
              Real.sqrt
                (((21 / 4 : ℝ) * Real.log q + 617 / 10) ^ 2 +
                  (14 / 5 : ℝ) * (∑ r ∈ m.primeFactors, Real.log r))) ^
            2 ∧
        ¬p ∣ m ∧ χ p ≠ 1 := by
  have hB : 617 / 10 ≤ (21 / 4 : ℝ) * Real.log q + 617 / 10 := by
    linarith only [Real.log_natCast_nonneg q]
  have hy :
    (200 : ℝ) ≤
      ((21 / 4 : ℝ) * Real.log q + 617 / 10 +
          Real.sqrt
            (((21 / 4 : ℝ) * Real.log q + 617 / 10) ^ 2 +
              (14 / 5 : ℝ) * (∑ r ∈ m.primeFactors, Real.log r))) ^
        2 := by
    nlinarith only [hB,
      Real.sqrt_nonneg
        (((21 / 4 : ℝ) * Real.log q + 617 / 10) ^ 2 +
          (14 / 5 : ℝ) * (∑ r ∈ m.primeFactors, Real.log r))]
  apply exists_prime_ne_one_of_affine_conductor_gap χ hq hp hGRH hm hy
  have h :=
    conductor_exclusion_unclipped_root_gap (A := (21 / 4 : ℝ) * Real.log q + 607 / 10) (E :=
      (7 / 10 : ℝ) * (∑ r ∈ m.primeFactors, Real.log r))
      (by linarith only [Real.log_natCast_nonneg q])
      (mul_nonneg (by norm_num only) (Finset.sum_nonneg (fun p _ ↦ Real.log_natCast_nonneg p)))
  have ha : (21 / 4 : ℝ) * Real.log q + 607 / 10 + 1 = (21 / 4 : ℝ) * Real.log q + 617 / 10 := by
    ring
  have htwo (E : ℝ) : 2 * ((7 / 10 : ℝ) * E) = (7 / 5 : ℝ) * E := by ring
  have hfour (E : ℝ) : 4 * ((7 / 10 : ℝ) * E) = (14 / 5 : ℝ) * E := by ring
  simpa only [ha, htwo, hfour] using h

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS.PaperStatements

/-- For nonnegative B₁, increasing the radius coefficient and the tail cannot
increase the smaller squared root radius past the larger one. Compare squares,
then square roots and nonnegative radii. This is a generic bound-comparison interface. -/
theorem root_radius_sq_mono {B₁ B₂ D₁ D₂ : ℝ} (hB₁ : 0 ≤ B₁) (hB : B₁ ≤ B₂) (hD : D₁ ≤ D₂) :
    (B₁ + Real.sqrt (B₁ ^ 2 + D₁)) ^ 2 ≤ (B₂ + Real.sqrt (B₂ ^ 2 + D₂)) ^ 2 := by
  have hsq := pow_le_pow_left₀ hB₁ hB 2
  have hs := Real.sqrt_le_sqrt (add_le_add hsq hD)
  exact pow_le_pow_left₀ (add_nonneg hB₁ (Real.sqrt_nonneg _)) (add_le_add hB hs) 2

/-- For nonnegative logarithmic conductor L and exclusion cost E, the affine
root bound is at most the preceding 12L+113 root bound. Apply generic monotonicity
to both coefficients. This certifies improvement on the complete input domain. -/
theorem affine_conductor_root_le_previous {L E : ℝ} (hL : 0 ≤ L) (hE : 0 ≤ E) :
    ((21 / 4 : ℝ) * L + 617 / 10 +
          Real.sqrt (((21 / 4 : ℝ) * L + 617 / 10) ^ 2 + (14 / 5 : ℝ) * E)) ^
        2 ≤
      (12 * L + 113 + Real.sqrt ((12 * L + 113) ^ 2 + 4 * E)) ^ 2 := by
  apply root_radius_sq_mono
  · linarith only [hL]
  · linarith only [hL]
  · linarith only [hE]

end PseudoPrime.LLS.PaperStatements
