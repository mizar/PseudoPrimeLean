/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186GapEval
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186GapShapes

import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186GapShapes
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186GapExp

/-! # Fixed-point bounds for the K186 residual endpoints -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The common scale is positive for the interval operations. -/
private theorem scale_pos : 0 < k186GapExpScale := by decide +kernel

/-- Multiply two intervals using the single fixed scale of the certificate. -/
private def gapProduct (I J : Analysis.IntegerInterval) : Analysis.IntegerInterval :=
  Analysis.roundedProduct k186GapExpScale I J

/-- Interpret a product at the common fixed scale. -/
private theorem gap_product_contains {I J : Analysis.IntegerInterval} {x y : ℝ}
    (hx : I.Contains k186GapExpScale x) (hy : J.Contains k186GapExpScale y) :
    (gapProduct I J).Contains k186GapExpScale (x * y) :=
  Analysis.roundedProduct_contains scale_pos hx hy

/-- The fixed factor multiplying the physical profile and its endpoint moment. -/
theorem k186_gap_pref_contains :
    (k186GapExpNeg 1760).Contains k186GapExpScale (Real.exp (-55 / 4)) := by
  simpa only [Nat.cast_ofNat, show -((1760 : ℝ) / 128) = -55 / 4 by ring] using
    k186_gap_exp_neg_contains 1760 (k186_gap_exp_lower_pos _)

/-- The first exponential-polynomial cost from the common profile and Euler evaluations. -/
def k186GapCostNine (j : ℕ) : Analysis.IntegerInterval :=
  let p := (k186GapExpNeg 1760).scaleRatio 20000000000 5196744155
  let q := (k186GapEulerNineAt j).scale 4
  gapProduct (k186GapExpNeg (9 * j)) ((gapProduct p (k186GapProfileAt j)).add q)

/-- Enclose the first signed cost at (x=j/32). -/
theorem k186_gap_cost_nine_contains (j : ℕ) (hj : 0 < (k186GapExp (9 * j)).lower) :
    let x := (j : ℝ) / 32
    (k186GapCostNine j).Contains k186GapExpScale
      (Real.exp (-(9 / 4 : ℝ) * x) * k186GapRateNine.eval x) := by
  intro x
  have hp :=
    Analysis.IntegerInterval.scaleRatio_contains (p := 20000000000) (d := 5196744155) scale_pos
      (by decide) k186_gap_pref_contains
  have hB := k186_gap_profile_at (j : ℤ)
  have hQ := Analysis.IntegerInterval.scale_contains (k := 4) (k186_gap_euler_nine_at (j : ℤ))
  have he := k186_gap_exp_neg_contains (9 * j) hj
  have h :=
    gap_product_contains he (Analysis.IntegerInterval.add_contains (gap_product_contains hp hB) hQ)
  change (k186GapCostNine j).Contains k186GapExpScale _ at h
  rw [k186_gap_nine_rat]
  simp only [k186GapProfileRat, k186GapEulerNineRat, Polynomial.map_comp, Polynomial.map_add,
    Polynomial.map_X, Polynomial.map_C, Polynomial.map_mul, Rat.coe_castHom, Rat.cast_ofNat,
    Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_C]
  convert h using 2 <;>
    norm_num only [x, k186GapCostNine, gaussianK186FarScale, Nat.cast_mul, Nat.cast_ofNat,
      Int.cast_natCast, Int.cast_ofNat] <;>
    ring_nf

/-- The interval of values of (3log(2pi)-7). -/
def k186GapLogInterval : Analysis.IntegerInterval :=
  ⟨-4 * k186GapExpScale, -k186GapExpScale⟩

/-- The real logarithmic coefficient lies in the shared interval. -/
theorem k186_gap_log_contains :
    k186GapLogInterval.Contains k186GapExpScale (3 * Real.log (2 * Real.pi) - 7) := by
  have h := k186_log_two_pi_mem
  have hG : (k186GapExpScale : ℝ) ≠ 0 := Int.cast_ne_zero.mpr scale_pos.ne'
  constructor
  · change ((-4 * k186GapExpScale : ℤ) : ℝ) / k186GapExpScale ≤ _
    rw [Int.cast_mul, Int.cast_neg, Int.cast_ofNat, mul_div_cancel_right₀ _ hG]
    linarith only [h.1]
  · change _ ≤ ((-k186GapExpScale : ℤ) : ℝ) / k186GapExpScale
    rw [Int.cast_neg, neg_div, div_self hG]
    linarith only [h.2]

/-- The rate-eleven-quarters term from the common endpoint and mass rows. -/
def k186GapCostEleven (j : ℕ) : Analysis.IntegerInterval :=
  let b := gapProduct k186GapLogInterval (k186GapProfileAt j)
  let p := gapProduct (k186GapExpNeg 1760) ((k186GapEndpointAt j).add b)
  let q := (k186GapMassAt j).scaleRatio ((j : ℤ) ^ 2) 1024
  let qH := (q.add (k186GapEulerElevenAt j)).scaleRatio 1 6
  gapProduct (k186GapExpNeg (11 * j)) (p.add qH)

/-- Enclose the second signed cost at (x=j/32). -/
theorem k186_gap_cost_eleven_contains (j : ℕ) (hj : 0 < (k186GapExp (11 * j)).lower) :
    let x := (j : ℝ) / 32
    (k186GapCostEleven j).Contains k186GapExpScale
      (Real.exp (-(11 / 4 : ℝ) * x) * k186GapRateEleven.eval x) := by
  intro x
  have hB := gap_product_contains k186_gap_log_contains (k186_gap_profile_at (j : ℤ))
  have hp :=
    gap_product_contains k186_gap_pref_contains
      (Analysis.IntegerInterval.add_contains (k186_gap_endpoint_at (j : ℤ)) hB)
  have hq :=
    Analysis.IntegerInterval.scaleRatio_contains (p := (j : ℤ) ^ 2) (d := 1024) scale_pos
      (by decide) (k186_gap_mass_at (j : ℤ))
  have hQ :=
    Analysis.IntegerInterval.scaleRatio_contains (p := 1) (d := 6) scale_pos (by decide)
      (Analysis.IntegerInterval.add_contains hq (k186_gap_euler_eleven_at (j : ℤ)))
  have h :=
    gap_product_contains (k186_gap_exp_neg_contains (11 * j) hj)
      (Analysis.IntegerInterval.add_contains hp hQ)
  change (k186GapCostEleven j).Contains k186GapExpScale _ at h
  rw [k186_gap_eleven_rat]
  simp only [k186GapProfileRat, k186GapEndpointRat, k186GapEulerElevenRat, Polynomial.map_comp,
    Polynomial.map_add, Polynomial.map_C, Polynomial.map_X, Polynomial.map_mul, Polynomial.map_pow,
    Rat.coe_castHom, Rat.cast_ofNat, Rat.cast_div, Rat.cast_one, Polynomial.eval_comp,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_pow] at h ⊢
  convert h using 2 <;>
    norm_num only [x, Nat.cast_mul, Nat.cast_ofNat, Int.cast_natCast, Int.cast_ofNat,
      Int.cast_pow] <;>
    ring_nf

/-- The endpoint residual after removing the exponentials and their signed costs. -/
private def gapQuadratic (j : ℕ) : ℚ :=
  let x := (j : ℚ) / 32
  94173 / 1250 - 3 / 100 - 3 / 16 - 6 / 5 - 301 / 20000 * x ^ 2 - (x + 5) ^ 2 / 6000

/-- Common-scale evaluation of all terms of the finite residual at (j/32). -/
def k186GapAt (j : ℕ) : Analysis.IntegerInterval :=
  let q := gapQuadratic j
  let c := Analysis.roundedConstant k186GapExpScale q.num q.den
  let p := (k186GapExp (2 * j)).scaleRatio 7827514344543 5196744155000000000000
  let t := (k186GapExpNeg (2 * (j + 160))).scale 78548
  (((c.add p).add ((k186GapCostNine j).scale (-1))).add ((k186GapCostEleven j).scale (-1))).add
    (t.scale (-1))

/-- The calculated scalar interval contains the analytic residual. -/
theorem k186_gap_at_contains (j : ℕ) (h₁ : 0 < (k186GapExp (9 * j)).lower)
    (h₂ : 0 < (k186GapExp (11 * j)).lower) (h₃ : 0 < (k186GapExp (2 * (j + 160))).lower) :
    (k186GapAt j).Contains k186GapExpScale (k186FiniteGap ((j : ℝ) / 32)) := by
  let x := (j : ℝ) / 32
  let q := gapQuadratic j
  have hc :=
    Analysis.roundedConstant_contains (p := q.num) scale_pos (Int.natCast_pos.mpr q.den_pos)
  rw [Int.cast_natCast, ← Rat.cast_def] at hc
  have hp :=
    Analysis.IntegerInterval.scaleRatio_contains (p := 7827514344543) (d := 5196744155000000000000)
      scale_pos (by decide) (k186_gap_exp_contains (2 * j))
  have hT :=
    Analysis.IntegerInterval.scale_contains (k := 78548)
      (k186_gap_exp_neg_contains (2 * (j + 160)) h₃)
  have hC₁ := Analysis.IntegerInterval.scale_contains (k := -1) (k186_gap_cost_nine_contains j h₁)
  have hC₂ := Analysis.IntegerInterval.scale_contains (k := -1) (k186_gap_cost_eleven_contains j h₂)
  have hN := Analysis.IntegerInterval.scale_contains (k := -1) hT
  have h :=
    Analysis.IntegerInterval.add_contains
      (Analysis.IntegerInterval.add_contains
        (Analysis.IntegerInterval.add_contains (Analysis.IntegerInterval.add_contains hc hp) hC₁)
        hC₂)
      hN
  change (k186GapAt j).Contains k186GapExpScale _ at h
  rw [k186_finite_gap_grouped]
  convert h using 2
  norm_num only [q, gapQuadratic, gaussianK186FarScale, Rat.cast_sub, Rat.cast_pow, Rat.cast_add,
    Rat.cast_mul, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat, Nat.cast_mul, Nat.cast_add,
    Nat.cast_ofNat, Int.cast_ofNat, Int.cast_neg]
  ring_nf

/-- One rational comparison against the rounded lower endpoint proves the
stated lower bound for the finite residual. -/
theorem k186_gap_lower_of_compare (j : ℕ) {v : ℚ} (h₁ : 0 < (k186GapExp (9 * j)).lower)
    (h₂ : 0 < (k186GapExp (11 * j)).lower) (h₃ : 0 < (k186GapExp (2 * (j + 160))).lower)
    (h : v ≤ ((k186GapAt j).lower : ℚ) / k186GapExpScale) :
    (v : ℝ) ≤ k186FiniteGap ((j : ℝ) / 32) := by
  have hc := (Rat.cast_le (K := ℝ)).mpr h
  simp only [Rat.cast_div, Rat.cast_intCast] at hc
  exact hc.trans (k186_gap_at_contains j h₁ h₂ h₃).1

end PseudoPrime.PrimeTestBounds.MillerRabin
