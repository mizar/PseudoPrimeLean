/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighGammaTailBound
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186ReflectedBudget
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186GammaMajorant
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186GammaRayCert
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186XiBudget
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186CoarseH30
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighForwardMain

import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186GammaMajorant
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighCompensationPartition
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186DirectComparison

/-! # K186 common-contour loss beyond the Gamma correction boundary -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The whole far common contour can instead use the geometric derivative
polynomial, without any per-order Gamma checks beyond the common bound. -/
theorem k186_common_contour_geometric_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hn : χ ≠ 1) (hi : χ⁻¹ = χ) (he : χ.Even) {X : ℝ} (hX : 0 < X)
    (hz : 65 ≤ 5 + Real.log X) :
    highCommonContour .k186 X ≤
      Real.exp (-(11 / 4 : ℝ) * (5 + Real.log X)) *
        k186GammaGeometricPoly.eval (5 + Real.log X) := by
  let z := 5 + Real.log X
  have hz' : (profileCorrectionEnd .k186 : ℝ) ≤ z := by
    simpa only [profileCorrectionEnd, Int.cast_ofNat] using hz
  have hI := max_le (neg_nonpos.mpr (high_gamma_conv_cutoff_nonneg .k186)) (le_refl (0 : ℝ))
  have h :=
    high_common_contour_tail_le .k186 hp hn hi he hz' hI (fun j _ ↦ k186_gamma_coeff_geometric j)
  dsimp only at h
  have hzX : Real.exp (z - 5) = X := by
    change Real.exp (5 + Real.log X - 5) = X
    rw [add_sub_cancel_left, Real.exp_log hX]
  rw [hzX] at h
  simpa only [HighGaussianKernel.pole, Rat.cast_div, Rat.cast_ofNat, mul_zero, add_zero,
    k186GammaGeometricPoly, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    z] using h

/-- The geometric majorant's fixed coefficient sum bounds it on the entire
ray, independently of the character and the cutoff parameter. -/
theorem k186_gamma_geometric_ray_le {z : ℝ} (hz : 65 ≤ z) :
    Real.exp (-(11 / 4 : ℝ) * z) * k186GammaGeometricPoly.eval z ≤ 1 / 10 ^ 6 := by
  have h := decay_poly_le_shifted k186GammaGeometricPoly (by norm_num only : (0 : ℝ) < 11 / 4) hz
  dsimp only at h
  rw [k186_gamma_geometric_translate, Polynomial.natDegree_C_mul (by norm_num only)] at h
  have hw (i : ℕ) : (3 / 8 : ℝ) * (i : ℝ) / (11 / 4) = (3 / 22 : ℝ) * i := by ring
  have hm (v : ℝ) : max 0 ((7 / 2 : ℝ) * v) = (7 / 2 : ℝ) * max 0 v := by
    rw [mul_max_of_nonneg _ _ (by norm_num only : (0 : ℝ) ≤ 7 / 2), mul_zero]
  simp only [hw, Polynomial.coeff_C_mul, hm, mul_assoc, ← Finset.mul_sum] at h
  rw [mul_left_comm] at h
  exact h.trans k186_gamma_ray_coeff_cap

/-- The fixed Gamma coefficient sum bounds the common contour by one
millionth throughout the ray beyond the correction boundary. -/
theorem k186_common_contour_le_millionth {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hn : χ ≠ 1) (hi : χ⁻¹ = χ) (he : χ.Even) {X : ℝ} (hX : 0 < X)
    (hz : 65 ≤ 5 + Real.log X) : highCommonContour .k186 X ≤ 1 / 10 ^ 6 := by
  exact (k186_common_contour_geometric_le hp hn hi he hX hz).trans (k186_gamma_geometric_ray_le hz)

/-- Five width-six cells supply the three coarse moments for the damped H30
term in the far comparison. -/
private theorem k186_h30_charge_le_coarse : highH30Charge .k186 ≤ 10 ^ 12 := by
  obtain ⟨h₀, h₁, h₂⟩ := k186_coarse_moment_caps
  have h := high_h30_charge_le .k186 h₀ h₁ h₂
  norm_num only [HighGaussianKernel.pole, Rat.cast_div, Rat.cast_ofNat] at h
  linarith only [h]

/-- Beyond the Gamma correction boundary, the verified far cost bounds
leave a lower bound on the forward term as the remaining cost hypothesis.
The lower bound may spend a logarithmic-square error and a constant of 19850. -/
theorem uniform_k186_far_of_contour_budget {n : ℕ} {α : ℝ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 30000000000000 ≤ Real.log n) (hα : 0.7216056623106 ≤ α)
    (hf :
      let y := gaussianK186FarScale * Real.log n
      α * y - (7 / 20 * Real.log y ^ 2 + 19850) ≤ k186ForwardValue (y ^ 2))
    (hz : 65 ≤ 5 + Real.log ((gaussianK186FarScale * Real.log n) ^ 2)) :
    HasRejectingPrime n (gaussianWitnessCutoff (Real.log n)) := by
  let L := Real.log n
  let X := (gaussianK186FarScale * L) ^ 2
  let z := 5 + Real.log X
  have hsmall := (by norm_num only : (10 ^ 12 : ℝ) ≤ 30000000000000).trans hL
  have hL' := (by norm_num only : (7000000 : ℝ) ≤ 10 ^ 12).trans hsmall
  have hd := k186_direct_cutoff_domain hL'
  have hX : 0 < X := (by norm_num only : (0 : ℝ) < 1000000).trans_le hd.1
  have hz' : (profileCorrectionStart .k186 : ℝ) ≤ z := by
    exact
      (by norm_num only [profileCorrectionStart, Rat.cast_ofNat] :
            (profileCorrectionStart .k186 : ℝ) ≤ 65).trans
        hz
  have hcon := k186_far_conductor_le_200 hsmall
  have hxi := k186_xi_mass_le hGRH.riemann
  have href := k186_far_reflected_le_two hz k186_h30_charge_le_coarse
  have hw : HasRejectingPrime n X := by
    apply uniform_gaussian_witness_from_factors hn ho hu
    intro p q r _ _ _ _ _ _ _ _ _ _ hprod hp hq hr
    by_contra h
    have hpass (l : ℕ) (hl : l.Prime) (hle : (l : ℝ) ≤ X) :
      PrimeTest.StrongMillerRabinPass n (l : ZMod n) :=
      Classical.byContradiction (fun hf' ↦ h ⟨l, hl, hle, hf'⟩)
    obtain ⟨_, _, _, hχ, _, _, _⟩ := pair_data_of_uniform_pass hn ho hu hprod hp hq hr X hpass
    have hcont := k186_common_contour_le_millionth hχ.1 hχ.2.1 hχ.2.2.1 hχ.2.2.2 hX hz
    have hup :=
      k186_direct_inequality_from hGRH hn ho hu hprod hp hq hr hd.1 (Real.exp_pos 53)
        (by
          rw [Real.log_exp]; norm_num only)
        (k186_far_tail_anchor hsmall) hz' hpass
    have hs : k186DirectBaseLoss L X + 4 * k186TailCost (Real.exp 53) ≤ 150 := by
      dsimp only [k186DirectBaseLoss, L, X]
      dsimp only at hcon
      linarith only [hcon, hcont, href, hxi, k186_far_tail_budget]
    have hc :=
      gaussian_k186_far_comparison_anchor hα hL
        (show
          k186DirectBaseLoss L X + 4 * k186TailCost (Real.exp 53) +
              (7 / 20 * Real.log (gaussianK186FarScale * L) ^ 2 + 19850) ≤
            7 / 20 * Real.log (gaussianK186FarScale * L) ^ 2 + 20000
          by linarith only [hs])
    dsimp only [L, X] at hc
    dsimp only at hf
    linarith only [hf, hup, hc]
  exact hw.mono (gaussian_k186_far_cutoff ((by norm_num only : (2000000 : ℝ) ≤ 7000000).trans hL'))

/-- At input logarithm thirty trillion, the far cutoff exceeds the Gamma
correction boundary, and the same holds at larger inputs. -/
theorem k186_gamma_far_domain {L : ℝ} (hL : 30000000000000 ≤ L) :
    65 ≤ 5 + Real.log ((gaussianK186FarScale * L) ^ 2) := by
  have hρ : 0 < gaussianK186FarScale := by norm_num only [gaussianK186FarScale]
  have h : (11000000000000 : ℝ) ≤ gaussianK186FarScale * L :=
    (by norm_num only [gaussianK186FarScale] :
          (11000000000000 : ℝ) ≤ gaussianK186FarScale * 30000000000000).trans
      (mul_le_mul_of_nonneg_left hL hρ.le)
  have he : Real.exp 30 ≤ 11000000000000 := by
    have hr :=
      (middle_exp_upper_le 2400).trans
        (Rat.cast_le.mpr (by decide +kernel : middleExpUpper 2400 ≤ 11000000000000))
    norm_num only [Nat.cast_ofNat, Rat.cast_ofNat] at hr
    exact hr
  have hl := (Real.le_log_iff_exp_le (he.trans h |>.trans_lt' (Real.exp_pos _))).mpr (he.trans h)
  rw [Real.log_pow, Nat.cast_ofNat]
  linarith only [hl]

/-- On the far half-line the forward estimate in the shifted coordinate
already has the right error budget for the uniform witness theorem. -/
theorem uniform_k186_far_of_forward {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 30000000000000 ≤ Real.log n)
    (hf :
      let y := gaussianK186FarScale * Real.log n
      0.7216056623106 * y - (1 / 12 * (5 + Real.log (y ^ 2)) ^ 2 + 19800) ≤
        k186ForwardValue (y ^ 2)) :
    HasRejectingPrime n (gaussianWitnessCutoff (Real.log n)) := by
  refine
    uniform_k186_far_of_contour_budget hn ho hu hGRH hL (le_refl _) ?_ (k186_gamma_far_domain hL)
  let y := gaussianK186FarScale * Real.log n
  change 0.7216056623106 * y - (7 / 20 * Real.log y ^ 2 + 19850) ≤ k186ForwardValue (y ^ 2)
  change
    0.7216056623106 * y - (1 / 12 * (5 + Real.log (y ^ 2)) ^ 2 + 19800) ≤
      k186ForwardValue (y ^ 2) at hf
  rw [Real.log_pow, Nat.cast_ofNat, add_comm 5] at hf
  linarith only [hf, k186_forward_shifted_error (Real.log y)]

/-- The raw forward main term and the two compensation caps give the
compensated lower bound in the shifted coordinate. -/
theorem k186_forward_le_of_raw {y : ℝ} (hy : 0 < y)
    (hI : Real.exp (5 / 2) * highCompensationMain .k186 ≤ 13765063832627 / 500000000000000000)
    (hV : highCompensationVariation .k186 ≤ 1 / 4)
    (hraw :
      let K := HighGaussianKernel.k186
      let M := (middleMomentPoly K.ratProfile (K.pole + 1 / 2) 0).map (Rat.castHom ℝ)
      let z := 5 + Real.log (y ^ 2)
      y * (4 * Real.exp (-55 / 4) * M.eval 5 - Real.exp (5 / 2) * M.eval 0) - (z ^ 2 / 24 + 19800) ≤
        k186ForwardValue (y ^ 2) + 4 * highCompensationBound .k186 (y ^ 2)) :
    0.7216056623106 * y - (1 / 12 * (5 + Real.log (y ^ 2)) ^ 2 + 19800) ≤
      k186ForwardValue (y ^ 2) := by
  have hs := mul_le_mul_of_nonneg_left (k186_forward_slope hI) hy.le
  have hv := mul_le_mul_of_nonneg_left hV (sq_nonneg (5 + Real.log (y ^ 2)))
  have hlog : Real.log (y ^ 2 * Real.exp 5) = 5 + Real.log (y ^ 2) := by
    rw [Real.log_mul (pow_ne_zero _ hy.ne') (Real.exp_pos _).ne', Real.log_exp, add_comm]
  dsimp only at hraw hs
  rw [highCompensationBound, Real.sqrt_sq_eq_abs, abs_of_pos hy, hlog] at hraw
  linarith only [hraw, hs, hv]

end PseudoPrime.PrimeTestBounds.MillerRabin
