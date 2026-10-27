/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExponentialFixedPointSignedBounds
public import PseudoPrime.Analysis.GaussianGammaCutoffCurvature

/-! # Kernel-provable lower values at Gaussian midpoint nodes -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The fixed-point scale 10^40 used by the Gaussian midpoint certificate.
This scale is explicit in every outward-rounded arithmetic bound. -/
def gaussianCutoffNodeScale : ℕ :=
  10 ^ 40

/-- The natural fixed-point lower value of the Gaussian cutoff density at v=m/4000.
The cutoff is supplied as a rational numerator and denominator. Use 121 Taylor terms,
outward-rounded products, and the certified normalization 56418958/10^8. -/
def gaussianCutoffNodeLowerParam (a b : ℕ) (m : ℤ) : ℕ :=
  let S := gaussianCutoffNodeScale
  let G := S * S / expFixedPointUpperSum (m * m).toNat 16000000 S 121
  let T := expFixedPointSignedLower m 8000 S 121
  let Z := expFixedPointSignedLower (-m) 4000 S 121 * a / b
  let P := expFixedPointLowerSum Z S S 121
  let C := S - (S * S + P - 1) / P
  let V := G * T / S
  let V := V * C / S
  V * 56418958 / 100000000

/-- The established 21/10 node API is the corresponding rational-cutoff specialization. -/
def gaussianCutoffNodeLower (m : ℤ) : ℕ :=
  gaussianCutoffNodeLowerParam 21 10 m

/-- For |m|≤16000, the parameterized node value is at most 10^40 times the actual
Gaussian cutoff density at m/4000 and cutoff a/b. The proved exponential envelopes,
outward-rounded arithmetic, and pi bound discharge all analytic estimates. -/
theorem gaussianCutoffNodeLowerParam_le (a b : ℕ) (m : ℤ) (hm : |(m : ℝ)| ≤ 16000) :
    (gaussianCutoffNodeLowerParam a b m : ℝ) ≤
      (gaussianCutoffNodeScale : ℝ) *
        gaussianGammaCutoffIntegrand ((a : ℝ) / b) ((m : ℝ) / 4000) := by
  let S := gaussianCutoffNodeScale
  let v : ℝ := (m : ℝ) / 4000
  let G := S * S / expFixedPointUpperSum (m * m).toNat 16000000 S 121
  let T := expFixedPointSignedLower m 8000 S 121
  let Z := expFixedPointSignedLower (-m) 4000 S 121 * a / b
  let P := expFixedPointLowerSum Z S S 121
  let C := S - (S * S + P - 1) / P
  have hS : 0 < S := by norm_num only [S, gaussianCutoffNodeScale]
  have he : ((m * m).toNat : ℝ) = (m : ℝ) * m := by
    exact_mod_cast Int.toNat_of_nonneg (mul_self_nonneg m)
  have hsq : (m : ℝ) ^ 2 ≤ (16000 : ℝ) ^ 2 :=
    sq_le_sq.mpr (by simpa only [abs_of_pos (by norm_num only : (0 : ℝ) < 16000)] using hm)
  have hsize : (((m * m).toNat : ℝ) / 16000000) / (121 + 1 : ℕ) ≤ 1 / 2 := by
    rw [he]
    norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    nlinarith only [hsq]
  have hG : (G : ℝ) ≤ (S : ℝ) * Real.exp (-(v ^ 2)) := by
    have hu := expFixedPointUpperSum_ge_exp (m * m).toNat 16000000 S 121 (by norm_num only) hsize
    have hr := fixedPoint_reciprocal_exp_lower hS hu
    have hx : -(((m * m).toNat : ℝ) / 16000000) = -(v ^ 2) := by
      rw [he]
      dsimp only [v]
      ring
    simpa only [Nat.cast_ofNat, hx] using hr
  have htSize : (|(m : ℝ)| / 8000) / (121 + 1 : ℕ) ≤ 1 / 2 := by
    norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    linarith only [hm]
  have hT : (T : ℝ) ≤ (S : ℝ) * Real.exp (v / 2) := by
    have ht := expFixedPointSignedLower_le m 8000 S 121 (by norm_num only) hS htSize
    have hx : (m : ℝ) / 8000 = v / 2 := by
      dsimp only [v]; ring
    simpa only [Nat.cast_ofNat, hx] using ht
  have hzSize : (|((-m : ℤ) : ℝ)| / 4000) / (121 + 1 : ℕ) ≤ 1 / 2 := by
    simp only [Int.cast_neg, abs_neg]
    norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    linarith only [hm]
  have hZ : (Z : ℝ) ≤ (S : ℝ) * ((a : ℝ) / b * Real.exp (-v)) := by
    have hz := expFixedPointSignedLower_le (-m) 4000 S 121 (by norm_num only) hS hzSize
    have hx : ((-m : ℤ) : ℝ) / 4000 = -v := by
      rw [Int.cast_neg]
      dsimp only [v]
      ring
    simp only [Nat.cast_ofNat, hx] at hz
    exact fixedPoint_rational_mul_lower hz
  have hP : (P : ℝ) ≤ (S : ℝ) * Real.exp (((a : ℝ) / b) * Real.exp (-v)) := by
    have hp := expFixedPointLowerSum_le_exp Z S S 121
    have hz : (Z : ℝ) / S ≤ ((a : ℝ) / b) * Real.exp (-v) :=
      (div_le_iff₀ (Nat.cast_pos.mpr hS)).mpr (by simpa only [mul_comm] using hZ)
    exact hp.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hz) (Nat.cast_nonneg S))
  have hPpos : 0 < P := hS.trans_le (scale_le_expFixedPointLowerSum Z S S 121 (by norm_num only))
  have hcutoff : 0 ≤ (a : ℝ) / b := div_nonneg (Nat.cast_nonneg a) (Nat.cast_nonneg b)
  have hC : (C : ℝ) ≤ (S : ℝ) * (1 - Real.exp (-((a : ℝ) / b) * Real.exp (-v))) := by
    simpa only [neg_mul] using
      fixedPoint_cutoff_lower (mul_nonneg hcutoff (Real.exp_pos (-v)).le) hPpos hP
  have hGT := fixedPoint_mul_lower hS (Real.exp_pos (-(v ^ 2))).le hG hT
  have hGTC :=
    fixedPoint_mul_lower hS (mul_nonneg (Real.exp_pos (-(v ^ 2))).le (Real.exp_pos (v / 2)).le) hGT
      hC
  have hval := fixedPoint_rational_mul_lower (a := 56418958) (b := 100000000) hGTC
  have hpi : (56418958 : ℝ) / 100000000 ≤ 1 / Real.sqrt Real.pi := by
    have hs := Real.sq_sqrt Real.pi_pos.le
    have hp := Real.sqrt_pos.mpr Real.pi_pos
    apply (le_div_iff₀ hp).mpr
    nlinarith only [Real.pi_lt_d20, hs, hp]
  have hfactor :
    0 ≤
      Real.exp (-(v ^ 2)) * Real.exp (v / 2) * (1 - Real.exp (-((a : ℝ) / b) * Real.exp (-v))) := by
    apply mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    exact
      sub_nonneg.mpr
        (Real.exp_le_one_iff.mpr
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hcutoff) (Real.exp_pos _).le))
  have hnorm :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpi hfactor) (Nat.cast_nonneg S)
  have heq :
    (S : ℝ) *
        (1 / Real.sqrt Real.pi *
          (Real.exp (-(v ^ 2)) * Real.exp (v / 2) *
            (1 - Real.exp (-((a : ℝ) / b) * Real.exp (-v))))) =
      (S : ℝ) * gaussianGammaCutoffIntegrand ((a : ℝ) / b) v := by
    rw [gaussianGammaCutoffIntegrand, normalizedGaussianWeight]
    ring
  exact hval.trans (hnorm.trans_eq heq)

/-- Specialize the parameterized node estimate to the existing 21/10 cutoff API. -/
theorem gaussianCutoffNodeLower_le (m : ℤ) (hm : |(m : ℝ)| ≤ 16000) :
    (gaussianCutoffNodeLower m : ℝ) ≤
      (gaussianCutoffNodeScale : ℝ) * gaussianGammaCutoffIntegrand (21 / 10) ((m : ℝ) / 4000) := by
  simpa only [gaussianCutoffNodeLower, Nat.cast_ofNat] using
    gaussianCutoffNodeLowerParam_le 21 10 m hm

end PseudoPrime.Analysis
