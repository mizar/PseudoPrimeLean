/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028FiniteWeight

/-! # Weight monotonicity for all finite analytic cutoffs -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The common lower endpoint has logarithm below `57/10`. The rational
logarithm checker supplies the strict margin needed for the weight derivative. -/
theorem target028_log270_upper : Real.log 270 ≤ (57 / 10 : ℝ) := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 270 8 32 5 (57 / 10) = true from by
          decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
  exact h

/-- On the range used by the finite cutoffs, the principal weight is
nonincreasing. Its logarithmic coordinate stays between zero and nine, making
the explicit derivative nonpositive. This enables interval-wise lower bounds
for the finite principal sum. -/
theorem target028_weight_antitone_270 : AntitoneOn refinedWeight (Set.Icc (1 / 270 : ℝ) 1) := by
  apply
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc (1 / 270 : ℝ) 1)
      (fun u hu ↦
        (refinedWeight_hasDerivAt (by linarith only [hu.1])).continuousAt.continuousWithinAt)
      (fun u hu ↦
        (refinedWeight_hasDerivAt
            (by
              have h := interior_subset hu; linarith only [h.1])).hasDerivWithinAt)
  intro u hu
  have hm : u ∈ Set.Icc (1 / 270 : ℝ) 1 := interior_subset hu
  have hu0 : 0 < u := by linarith only [hm.1]
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 1 / 270) hm.1
  have hu1 := Real.log_nonpos hu0.le hm.2
  have hlog : -(57 / 10 : ℝ) ≤ Real.log u := by
    rw [show (1 / 270 : ℝ) = (270 : ℝ)⁻¹ by norm_num only, Real.log_inv] at hl
    linarith only [hl, target028_log270_upper]
  have hc0 : 0 ≤ refinedCoord u := by
    dsimp only [refinedCoord]
    linarith only [hu1]
  have hc9 : refinedCoord u ≤ 9 := by
    dsimp only [refinedCoord]
    linarith only [hlog]
  have hpoly : (29 / 50 : ℝ) * refinedCoord u ^ 5 - (27 / 5 : ℝ) * refinedCoord u ^ 4 ≤ 0 := by
    have h :=
      mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hc0 4)
        (show (29 / 50 : ℝ) * refinedCoord u - 27 / 5 ≤ 0 by linarith only [hc9])
    nlinarith only [h]
  dsimp only [refinedWeightDeriv]
  exact
    mul_nonpos_of_nonneg_of_nonpos
      (div_nonneg (Real.exp_pos _).le
        (mul_nonneg (mul_nonneg (by norm_num only) hu0.le) (Real.sqrt_nonneg _)))
      hpoly

/-- For every analytic cutoff up to 2701, the scaled principal weight is
nonincreasing between indices 11 and the cutoff. The interval starts above
`1/270` after scaling, so the common derivative bound applies. -/
theorem target028_weight_antitone_finite {X n b : ℝ} (hn : 11 ≤ n) (hnb : n ≤ b) (hb : b ≤ X)
    (hX : X ≤ 2701) : refinedScaledWeight X b ≤ refinedScaledWeight X n := by
  have hX0 : 0 < X := by linarith only [hn, hnb, hb]
  have hn0 : 0 < n / X := div_pos (by linarith only [hn]) hX0
  have hb0 : 0 < b / X := div_pos (by linarith only [hn, hnb]) hX0
  have hn1 : n / X ≤ 1 := (div_le_one hX0).mpr (by linarith only [hnb, hb])
  have hb1 : b / X ≤ 1 := (div_le_one hX0).mpr hb
  have hlo : (1 / 270 : ℝ) ≤ n / X := by
    apply (le_div_iff₀ hX0).mpr
    nlinarith only [hn, hX]
  have hln : Real.log (n / X) ≤ 21 / 8 := (Real.log_nonpos hn0.le hn1).trans (by norm_num only)
  have hlb : Real.log (b / X) ≤ 21 / 8 := (Real.log_nonpos hb0.le hb1).trans (by norm_num only)
  have hm :=
    target028_weight_antitone_270 (show n / X ∈ Set.Icc (1 / 270 : ℝ) 1 from ⟨hlo, hn1⟩)
      (show b / X ∈ Set.Icc (1 / 270 : ℝ) 1 from
        ⟨hlo.trans (div_le_div_of_nonneg_right hnb hX0.le), hb1⟩)
      (div_le_div_of_nonneg_right hnb hX0.le)
  dsimp only [refinedScaledWeight, refinedKernelWeight]
  rw [refinedKernelWeight_eq hn0 hln, refinedKernelWeight_eq hb0 hlb]
  exact div_le_div_of_nonneg_right hm (Real.sqrt_nonneg _)

/-- For a positive cutoff and an index in its support, the scaled weight has
the explicit single square-root denominator. The scale's square root cancels. -/
theorem target028_scaled_weight_eq {X b : ℝ} (hb : 0 < b) (hbX : b ≤ X) :
    refinedScaledWeight X b =
      refinedCoord (b / X) ^ 5 * Real.exp (-refinedCoord (b / X)) / (120 * Real.sqrt b) := by
  have hX : 0 < X := hb.trans_le hbX
  have hu : 0 < b / X := div_pos hb hX
  have hl : Real.log (b / X) ≤ 21 / 8 :=
    (Real.log_nonpos hu.le ((div_le_one hX).mpr hbX)).trans (by norm_num only)
  dsimp only [refinedScaledWeight, refinedKernelWeight]
  rw [refinedKernelWeight_eq hu hl, refinedWeight, Real.sqrt_div hb.le]
  have hs : Real.sqrt X ≠ 0 := (Real.sqrt_pos.mpr hX).ne'
  have ht : Real.sqrt b ≠ 0 := (Real.sqrt_pos.mpr hb).ne'
  field_simp

/-- Coordinate, exponential, and root bounds give a lower weight at any
positive cutoff. This transfers rational endpoint checks to later cells. -/
theorem target028_scaled_weight_lower {X b L E R : ℝ} (hb : 0 < b) (hbX : b ≤ X) (hL0 : 0 ≤ L)
    (hL : L ≤ refinedCoord (b / X)) (hE0 : 0 ≤ E) (hE : E ≤ Real.exp (-refinedCoord (b / X)))
    (hR : Real.sqrt b ≤ R) : L ^ 5 * E / (120 * R) ≤ refinedScaledWeight X b := by
  rw [target028_scaled_weight_eq hb hbX]
  have hc0 : 0 ≤ refinedCoord (b / X) := le_trans hL0 hL
  have hm : L ^ 5 * E ≤ refinedCoord (b / X) ^ 5 * Real.exp (-refinedCoord (b / X)) :=
    mul_le_mul (pow_le_pow_left₀ hL0 hL 5) hE hE0 (pow_nonneg hc0 5)
  exact
    div_le_div₀ (mul_nonneg (pow_nonneg hc0 5) (Real.exp_pos _).le) hm
      (mul_pos (by norm_num only) (Real.sqrt_pos.mpr hb))
      (mul_le_mul_of_nonneg_left hR (by norm_num only))

/-- Bounds for the reciprocal logarithm enclose the weight coordinate at any
positive cutoff. The logarithmic reciprocal identity gives both inequalities. -/
theorem target028_scaled_coord_bounds {X b lo hi : ℝ} (hb : 0 < b) (hX : 0 < X)
    (hlo : lo ≤ Real.log (X / b)) (hhi : Real.log (X / b) ≤ hi) :
    567 / 200 + (27 / 25) * lo ≤ refinedCoord (b / X) ∧
      refinedCoord (b / X) ≤ 567 / 200 + (27 / 25) * hi := by
  have heq : Real.log (b / X) = -Real.log (X / b) := by
    rw [← Real.log_inv]
    congr 1
    field_simp
  dsimp only [refinedCoord]
  rw [heq]
  constructor <;> linarith only [hlo, hhi]

end PseudoPrime.PrimeTestBounds.MillerRabin
