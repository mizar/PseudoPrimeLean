/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186GapShapes
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186GapCurvAffine
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186GapTaylor
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186GapEndpoint

import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186FiniteGap
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186GapShapes
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186GapExp
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186GapEndpoint

/-! # Fixed-point curvature polynomials in local cell coordinates -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Apply the two decay derivatives before normalizing the local coordinate. -/
noncomputable def k186CurvLocal (r : ℝ) (P : Polynomial ℝ) (a w : ℤ) : Polynomial ℝ :=
  (gaussianDecayDeriv r (gaussianDecayDeriv r P)).comp
    (Polynomial.C ((w : ℝ) / 32) * Polynomial.X + Polynomial.C ((a : ℝ) / 32))

/-- One decay derivative is additive. -/
private theorem decay_add (r : ℝ) (P Q : Polynomial ℝ) :
    gaussianDecayDeriv r (P + Q) = gaussianDecayDeriv r P + gaussianDecayDeriv r Q := by
  simp only [gaussianDecayDeriv, Polynomial.derivative_add]
  ring

/-- A constant scalar commutes with one decay derivative. -/
private theorem decay_scale (r c : ℝ) (P : Polynomial ℝ) :
    gaussianDecayDeriv r (Polynomial.C c * P) = Polynomial.C c * gaussianDecayDeriv r P := by
  simp only [gaussianDecayDeriv, Polynomial.derivative_C_mul]
  ring

/-- Translation commutes with one decay derivative, because the inner derivative is one. -/
private theorem decay_translate (r z : ℝ) (P : Polynomial ℝ) :
    gaussianDecayDeriv r (P.comp (Polynomial.X + Polynomial.C z)) =
      (gaussianDecayDeriv r P).comp (Polynomial.X + Polynomial.C z) := by
  simp only [gaussianDecayDeriv, Polynomial.derivative_comp, Polynomial.derivative_add,
    Polynomial.derivative_X, Polynomial.derivative_C, add_zero, one_mul, Polynomial.sub_comp,
    Polynomial.mul_comp, Polynomial.C_comp]

/-- Local curvature is additive. -/
theorem k186_curv_local_add (r : ℝ) (P Q : Polynomial ℝ) (a w : ℤ) :
    k186CurvLocal r (P + Q) a w = k186CurvLocal r P a w + k186CurvLocal r Q a w := by
  simp only [k186CurvLocal, decay_add, Polynomial.add_comp]

/-- Local curvature preserves a constant coefficient multiplier. -/
theorem k186_curv_local_scale (r c : ℝ) (P : Polynomial ℝ) (a w : ℤ) :
    k186CurvLocal r (Polynomial.C c * P) a w = Polynomial.C c * k186CurvLocal r P a w := by
  simp only [k186CurvLocal, decay_scale, Polynomial.mul_comp, Polynomial.C_comp]

/-- The normalized translated curvature uses the sum of the physical
and local offsets, with the width remaining fixed. -/
theorem k186_curv_translate_five (r : ℝ) (P : Polynomial ℝ) (a w : ℤ) :
    k186CurvLocal r (P.comp (Polynomial.X + Polynomial.C 5)) a w =
      k186CurvLocal r P (a + 160) w := by
  simp only [k186CurvLocal, decay_translate, Polynomial.comp_assoc, Polynomial.add_comp,
    Polynomial.X_comp, Polynomial.C_comp, add_assoc, ← Polynomial.C_add, Int.cast_add,
    Int.cast_ofNat]
  congr 3
  ring

/-- The rational twice-decayed row has the same coefficients as the real
local curvature of its source polynomial. -/
private theorem local_curv_cast (r : ℚ) (P : Polynomial ℚ) (a w : ℤ) :
    (((Polynomial.C (r ^ 2) * P - Polynomial.C (2 * r) * P.derivative +
                P.derivative.derivative).comp
            (Polynomial.C ((w : ℚ) / 32) * Polynomial.X + Polynomial.C ((a : ℚ) / 32))).map
        (Rat.castHom ℝ)) =
      k186CurvLocal (r : ℝ) (P.map (Rat.castHom ℝ)) a w := by
  have h :
    Polynomial.C (r ^ 2) * P - Polynomial.C (2 * r) * P.derivative + P.derivative.derivative =
      k186RatCurv r P := by
    unfold k186RatCurv
    ring
  rw [h, Polynomial.map_comp, k186_rat_curv_map]
  simp only [k186CurvLocal, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_X, Rat.coe_castHom, Rat.cast_div, Rat.cast_intCast, Rat.cast_ofNat]

/-- Combine the two normalized coefficient intervals of the first curvature cost. -/
def k186CurvNineTick (a w : ℤ) (i : ℕ) : Analysis.IntegerInterval :=
  let p := (k186GapExpNeg 1760).scaleRatio 20000000000 5196744155
  (Analysis.roundedProduct k186GapExpScale p (k186ProfileCurvTick 9 a w i)).add
    ((k186EulerNineCurvTick a w i).scale 4)

/-- The first combined tick encloses the normalized real coefficient. -/
theorem k186_curv_nine_tick_contains (a w : ℤ) (i : ℕ) :
    (k186CurvLocal (9 / 4) k186GapRateNine a w).natDegree ≤ 83 ∧
      (k186CurvNineTick a w i).Contains k186GapExpScale
        ((k186CurvLocal (9 / 4) k186GapRateNine a w).coeff i) := by
  have hG : 0 < k186GapExpScale := by decide +kernel
  have hB := k186_profile_curv_tick 9 a w i
  have hQ := k186_euler_nine_curv_tick a w i
  dsimp only at hB hQ
  rw [local_curv_cast] at hB hQ
  have hp :=
    Analysis.IntegerInterval.scaleRatio_contains (p := 20000000000) (d := 5196744155) hG (by decide)
      k186_gap_pref_contains
  have h :=
    Analysis.IntegerInterval.add_contains (Analysis.roundedProduct_contains hG hp hB.2)
      (Analysis.IntegerInterval.scale_contains (k := 4) hQ.2)
  change (k186CurvNineTick a w i).Contains k186GapExpScale _ at h
  rw [k186_gap_nine_rat]
  simp only [k186GapProfileRat, k186GapEulerNineRat, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_comp, Polynomial.map_add, Polynomial.map_X, Rat.coe_castHom, Rat.cast_ofNat,
    k186_curv_local_add, k186_curv_local_scale, k186_curv_translate_five, Polynomial.coeff_add,
    Polynomial.coeff_C_mul]
  have hratio :
    (20000000000 : ℝ) * Real.exp (-55 / 4) / 5196744155 =
      Real.exp (-55 / 4) * (2 / gaussianK186FarScale) := by
    norm_num only [gaussianK186FarScale]
    ring
  constructor
  · apply Polynomial.natDegree_add_le_of_degree_le
    · exact
        (Polynomial.natDegree_C_mul_le _ _).trans
          (by simpa only [Int.cast_ofNat, Rat.cast_ofNat, Rat.cast_div] using hB.1)
    · refine (Polynomial.natDegree_C_mul_le _ _).trans (?_ : _ ≤ 41) |>.trans (by decide)
      simpa only [Rat.cast_ofNat, Rat.cast_div] using hQ.1
  · simpa only [Int.cast_ofNat, Rat.cast_ofNat, Rat.cast_div, hratio] using h

/-- Combine the three normalized coefficient intervals of the second curvature cost. -/
def k186CurvElevenTick (a w : ℤ) (i : ℕ) : Analysis.IntegerInterval :=
  let c : Analysis.IntegerInterval := ⟨-4 * k186GapExpScale, -k186GapExpScale⟩
  let B := Analysis.roundedProduct k186GapExpScale c (k186ProfileCurvTick 11 a w i)
  let R := (k186EndpointCurvTick a w i).add B
  (Analysis.roundedProduct k186GapExpScale (k186GapExpNeg 1760) R).add
    (k186EulerElevenCurvTick a w i)

/-- The second combined tick encloses the normalized real coefficient. -/
theorem k186_curv_eleven_tick_contains (a w : ℤ) (i : ℕ) :
    (k186CurvLocal (11 / 4) k186GapRateEleven a w).natDegree ≤ 83 ∧
      (k186CurvElevenTick a w i).Contains k186GapExpScale
        ((k186CurvLocal (11 / 4) k186GapRateEleven a w).coeff i) := by
  have hG : 0 < k186GapExpScale := by decide +kernel
  have hB := k186_profile_curv_tick 11 a w i
  have hR := k186_endpoint_curv_tick a w i
  have hQ := k186_euler_eleven_curv_tick a w i
  dsimp only at hB hR hQ
  rw [local_curv_cast] at hB hR hQ
  have hR' :=
    Analysis.IntegerInterval.add_contains hR.2
      (Analysis.roundedProduct_contains hG k186_gap_log_contains hB.2)
  have h :=
    Analysis.IntegerInterval.add_contains
      (Analysis.roundedProduct_contains hG k186_gap_pref_contains hR') hQ.2
  change (k186CurvElevenTick a w i).Contains k186GapExpScale _ at h
  rw [k186_gap_eleven_rat]
  simp only [k186GapProfileRat, k186GapEndpointRat, k186GapEulerElevenRat, Polynomial.map_comp,
    Polynomial.map_add, Polynomial.map_X, Polynomial.map_C, Rat.coe_castHom, Rat.cast_ofNat,
    k186_curv_local_add, k186_curv_local_scale, k186_curv_translate_five, Polynomial.coeff_add,
    Polynomial.coeff_C_mul]
  constructor
  · apply Polynomial.natDegree_add_le_of_degree_le
    · apply (Polynomial.natDegree_C_mul_le _ _).trans
      apply Polynomial.natDegree_add_le_of_degree_le
      · simpa only [Rat.cast_ofNat, Rat.cast_div, Polynomial.map_add, k186_curv_local_add] using
          hR.1
      · exact
          (Polynomial.natDegree_C_mul_le _ _).trans
            (by simpa only [Int.cast_ofNat, Rat.cast_ofNat, Rat.cast_div] using hB.1)
    · exact (by simpa only [Rat.cast_ofNat, Rat.cast_div] using hQ.1 : _ ≤ 43).trans (by decide)
  · simpa only [Int.cast_ofNat, Rat.cast_ofNat, Rat.cast_div, Polynomial.map_add,
      k186_curv_local_add, Polynomial.coeff_add] using h

/-- The first signed Taylor sum has a single fixed-point scale. -/
def k186CurvNineLower (a w : ℤ) : ℤ :=
  k186TaylorTicks 83 (fun i ↦ (k186CurvNineTick a w i).lower)

/-- The second signed Taylor sum has the same fixed-point scale. -/
def k186CurvElevenLower (a w : ℤ) : ℤ :=
  k186TaylorTicks 83 (fun i ↦ (k186CurvElevenTick a w i).lower)

/-- Translate interval membership back to the unit coordinate used by the rows. -/
private theorem local_unit {a w : ℤ} (hw : 0 < w) {x : ℝ}
    (hx : x ∈ Set.Icc ((a : ℝ) / 32) (((a + w : ℤ) : ℝ) / 32)) :
    (32 * x - (a : ℝ)) / (w : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  have h : (0 : ℝ) < w := Int.cast_pos.mpr hw
  refine ⟨div_nonneg (by linarith only [hx.1]) h.le, (div_le_iff₀ h).mpr ?_⟩
  have hu := hx.2
  simp only [Int.cast_add] at hu
  linarith only [hu]

/-- Evaluating the normalized curvature at the local unit coordinate returns
the original polynomial factor evaluated at the cutoff. -/
private theorem local_eval (r : ℝ) (P : Polynomial ℝ) (a w : ℤ) {x : ℝ} (hw : 0 < w) :
    (k186CurvLocal r P a w).eval ((32 * x - (a : ℝ)) / (w : ℝ)) =
      (gaussianDecayDeriv r (gaussianDecayDeriv r P)).eval x := by
  have hn : (w : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hw.ne'
  simp only [k186CurvLocal, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_C]
  congr 1
  field_simp
  ring

/-- The two integer sums bound the actual curvature factors on the whole cell. -/
theorem k186_curv_bounds_of_ticks {a w : ℤ} (hw : 0 < w) {x : ℝ}
    (hx : x ∈ Set.Icc ((a : ℝ) / 32) (((a + w : ℤ) : ℝ) / 32)) :
    let d := (k186GapExpScale : ℝ)
    (k186CurvNineLower a w : ℝ) / d ≤
        (gaussianDecayDeriv (9 / 4) (gaussianDecayDeriv (9 / 4) k186GapRateNine)).eval x ∧
      (k186CurvElevenLower a w : ℝ) / d ≤
        (gaussianDecayDeriv (11 / 4) (gaussianDecayDeriv (11 / 4) k186GapRateEleven)).eval x := by
  have hG : 0 < k186GapExpScale := by decide +kernel
  refine ⟨?_, ?_⟩
  · have h :=
      k186_taylor_ticks_le hG (k186_curv_nine_tick_contains a w 0).1 (k186CurvNineTick a w)
        (fun i _ ↦ (k186_curv_nine_tick_contains a w i).2) (local_unit hw hx)
    exact h.trans_eq (local_eval _ _ a w hw)
  · have h :=
      k186_taylor_ticks_le hG (k186_curv_eleven_tick_contains a w 0).1 (k186CurvElevenTick a w)
        (fun i _ ↦ (k186_curv_eleven_tick_contains a w i).2) (local_unit hw hx)
    exact h.trans_eq (local_eval _ _ a w hw)

end PseudoPrime.PrimeTestBounds.MillerRabin
