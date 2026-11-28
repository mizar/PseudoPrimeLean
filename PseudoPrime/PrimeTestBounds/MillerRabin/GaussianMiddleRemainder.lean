/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK141LowerCharge
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK156LowerCharge
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleTailCert
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianDirectMiddleRange

/-! # Physical nonspectral remainder bounds for the middle Gaussian kernels -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The inverse-square cutoff value costs less than one millionth for
both middle kernels, using the uniform boundary magnitude cap. -/
private theorem middle_cutoff_charge_le {κ s b x v : ℝ} (hκ : 0 ≤ κ) (hκ' : κ ≤ 1) (hs : 0 ≤ s)
    (hb : 0 ≤ b) (hx : 20 ≤ x) (hv : |v| ≤ 100000) :
    5 / 3 * (κ * Real.exp (-s * (x + b)) * Real.exp ((s - 1 / 2) * x)) * |v| * Real.exp (-2 * x) ≤
      1 / 10 ^ 6 := by
  have he : Real.exp (-s * (x + b)) * Real.exp ((s - 1 / 2) * x) ≤ 1 := by
    rw [← Real.exp_add]
    exact (Real.exp_le_exp.mpr (by nlinarith only [mul_nonneg hs hb, hx])).trans_eq Real.exp_zero
  have hκe : κ * Real.exp (-s * (x + b)) * Real.exp ((s - 1 / 2) * x) ≤ 1 := by
    rw [mul_assoc]
    exact (mul_le_of_le_one_right hκ he).trans hκ'
  have hE := middle_exp_neg_quarters_le 160
  have hdec : Real.exp (-2 * x) ≤ ((778801 / 10 ^ 6 : ℚ) ^ 160 : ℚ) := by
    refine (Real.exp_le_exp.mpr ?_).trans hE
    norm_num only
    linarith only [hx]
  have h :=
    mul_le_mul
      (mul_le_mul_of_nonneg_left (mul_le_mul hκe hv (abs_nonneg _) zero_le_one)
        (by norm_num only : (0 : ℝ) ≤ 5 / 3))
      hdec (Real.exp_nonneg _) (by norm_num only)
  have hnum : (5 / 3 : ℚ) * 100000 * (778801 / 10 ^ 6) ^ 160 ≤ 1 / 10 ^ 6 := by decide +kernel
  rw [← mul_assoc (5 / 3 : ℝ), one_mul] at h
  refine h.trans ?_
  simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_pow (10 : ℚ) 6, Rat.cast_ofNat,
    Rat.cast_one] using (Rat.cast_le (K := ℝ)).mpr hnum

/-- The K141 nonspectral remainder on its cutoff interval uses the checked lower,
upper and cutoff-boundary caps. -/
public theorem middle_k141_remainder_le (hRH : RiemannHypothesis) {x : ℝ} (hl : 20 ≤ x)
    (hr : x ≤ 25) :
    let B := middleK141Profile.map (Rat.castHom ℝ)
    let V := fun u : ℝ ↦ u ^ (3 / 2 : ℝ) * B.eval (7 / 2 - Real.log u)
    let F := fun u ↦ u * deriv V u
    let c := (middleK141Norm : ℝ) * Real.exp (-(2 : ℝ) * (x + 7 / 2)) * Real.exp ((3 / 2 : ℝ) * x)
    let X := Real.exp x
    c *
        |principalErrorFunctional (deriv F) gaussianLogZetaRemainder (F 1) X (Real.exp (7 / 2)) +
            3 * (∫ u in (0 : ℝ)..X⁻¹, (X * u - gaussianLogZetaConstant) * deriv F u)| ≤
      51 / 1000 := by
  have hκ : 0 ≤ (middleK141Norm : ℝ) := Rat.cast_nonneg.mpr (by decide +kernel)
  have h :=
    middle_physical_remainder_le (middleK141Profile.map (Rat.castHom ℝ)) hRH (s := 2) (b := 7 / 2)
      (L := 1 / 10 ^ 6) (U := 1 / 20) hκ (by norm_num only) (by norm_num only)
      ((by norm_num only : (0 : ℝ) ≤ 20).trans hl)
  have hd : (2 - 1 / 2 : ℝ) = 3 / 2 := by norm_num only
  dsimp only at h
  rw [hd] at h
  have hh :=
    h (by simpa only [hd] using middle_k141_lower_charge hl)
      (by simpa only [hd] using middle_k141_upper_charge hl hr)
  have hv := middle_k141_edge_le.trans (by norm_num only : (23500 : ℝ) ≤ 100000)
  have he :=
    middle_cutoff_charge_le (s := 2) (b := 7 / 2) hκ
      (by
        simpa only [Rat.cast_one] using
          (Rat.cast_le (K := ℝ)).mpr (by decide +kernel : middleK141Norm ≤ 1))
      (by norm_num only) (by norm_num only) hl hv
  rw [hd] at he
  dsimp only
  linarith only [hh, he]

/-- The K156 nonspectral remainder on its cutoff interval uses the checked lower,
upper and cutoff-boundary caps. -/
public theorem middle_k156_remainder_le (hRH : RiemannHypothesis) {x : ℝ} (hl : 24 ≤ x)
    (hr : x ≤ 121 / 4) :
    let B := middleK156Profile.map (Rat.castHom ℝ)
    let V := fun u : ℝ ↦ u ^ (39 / 20 : ℝ) * B.eval (7 / 2 - Real.log u)
    let F := fun u ↦ u * deriv V u
    let c :=
      (middleK156Norm : ℝ) * Real.exp (-(49 / 20 : ℝ) * (x + 7 / 2)) * Real.exp ((39 / 20 : ℝ) * x)
    let X := Real.exp x
    c *
        |principalErrorFunctional (deriv F) gaussianLogZetaRemainder (F 1) X (Real.exp (7 / 2)) +
            3 * (∫ u in (0 : ℝ)..X⁻¹, (X * u - gaussianLogZetaConstant) * deriv F u)| ≤
      41 / 1000 := by
  have hκ : 0 ≤ (middleK156Norm : ℝ) := Rat.cast_nonneg.mpr (by decide +kernel)
  have h :=
    middle_physical_remainder_le (middleK156Profile.map (Rat.castHom ℝ)) hRH (s := 49 / 20) (b :=
      7 / 2) (L := 1 / 10 ^ 6) (U := 1 / 25) hκ (by norm_num only) (by norm_num only)
      ((by norm_num only : (0 : ℝ) ≤ 24).trans hl)
  have hd : (49 / 20 - 1 / 2 : ℝ) = 39 / 20 := by norm_num only
  dsimp only at h
  rw [hd] at h
  have hh :=
    h (by simpa only [hd] using middle_k156_lower_charge hl)
      (by simpa only [hd] using middle_k156_upper_charge hl hr)
  have he :=
    middle_cutoff_charge_le (s := 49 / 20) (b := 7 / 2) hκ
      (by
        simpa only [Rat.cast_one] using
          (Rat.cast_le (K := ℝ)).mpr (by decide +kernel : middleK156Norm ≤ 1))
      (by norm_num only) (by norm_num only) ((by norm_num only : (20 : ℝ) ≤ 24).trans hl)
      middle_k156_edge_le
  rw [hd] at he
  dsimp only
  linarith only [hh, he]

/-- Combine a physical zero-series cap and a nonspectral remainder cap into
the anchored Abel error. The explicitly separated lower boundary is retained. -/
public theorem middle_principal_of_caps (B : Polynomial ℝ) (hRH : RiemannHypothesis)
    {κ s b x A R : ℝ} (hκ : 0 ≤ κ) (hs : 1 / 2 < s) (hb : 0 < b) (hx : 0 ≤ x) (hB : B.eval 0 = 0)
    (hB' : B.derivative.eval 0 = 0) :
    let X := Real.exp x
    let d := s - 1 / 2
    let k := κ * Real.exp (-s * (x + b))
    let c := k * Real.exp (d * x)
    let V := fun u : ℝ ↦ u ^ d * B.eval (b - Real.log u)
    let F := fun u ↦ u * deriv V u
    let P := fun t ↦ t * deriv (middlePrincipalWeight B k (x + b) d) t
    let H := fun t ↦
      AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t -
          (t - Real.log (2 * Real.pi) * Real.log t) +
        1
    |κ * Real.exp (-s * b) * ∑' ρ, principalCancelledTerm B d b X ρ| ≤ A →
      c *
          |principalErrorFunctional (deriv F) gaussianLogZetaRemainder (F 1) X (Real.exp b) +
              3 * (∫ u in (0 : ℝ)..X⁻¹, (X * u - gaussianLogZetaConstant) * deriv F u)| ≤
        R →
      |middleTruncPrincipal P H X (X * Real.exp b) - 3 * (gaussianLogZetaConstant - 1) * P 1| ≤
        A + R := by
  intro X d k c V F P H hA hR
  have hp : 0 < X := Real.exp_pos _
  have hlog : Real.log X = x := Real.log_exp _
  have hc : 0 ≤ c := mul_nonneg (mul_nonneg hκ (Real.exp_nonneg _)) (Real.exp_nonneg _)
  have hroot : Real.sqrt X = Real.exp (x / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hp, hlog]
    congr 1
    ring
  have hscale : k * X ^ d = c := by rw [Real.rpow_def_of_pos hp, hlog, mul_comm x d]
  have hscale' : c * Real.sqrt X = κ * Real.exp (-s * b) := by
    dsimp only [c, k, d]
    rw [hroot, mul_assoc κ, mul_assoc κ, ← Real.exp_add, ← Real.exp_add]
    congr 2
    ring
  have h := middle_principal_error_series B k hRH (sub_pos.mpr hs) hb (Real.one_le_exp hx) hB hB'
  dsimp only at h
  rw [hlog, hscale] at h
  rw [h, add_sub_cancel_right]
  rw [add_assoc, mul_add, ← mul_assoc c (Real.sqrt (Real.exp x))]
  change |(c * Real.sqrt X) * _ + c * _| ≤ A + R
  rw [hscale']
  exact (abs_add_le _ _).trans (add_le_add hA (by rwa [abs_mul, abs_of_nonneg hc]))

/-- The K141 principal Abel error, with the lower boundary shown separately,
is bounded uniformly on the physical cutoff interval under RH. -/
public theorem middle_k141_principal_le (hRH : RiemannHypothesis) {x : ℝ} (hl : 20 ≤ x)
    (hr : x ≤ 25) :
    let B := middleK141Profile.map (Rat.castHom ℝ)
    let X := Real.exp x
    let k := (middleK141Norm : ℝ) * Real.exp (-(2 : ℝ) * (x + 7 / 2))
    let P := fun t ↦ t * deriv (middlePrincipalWeight B k (x + 7 / 2) (3 / 2)) t
    let H := fun t ↦
      AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t -
          (t - Real.log (2 * Real.pi) * Real.log t) +
        1
    |middleTruncPrincipal P H X (X * Real.exp (7 / 2)) - 3 * (gaussianLogZetaConstant - 1) * P 1| ≤
      76739 / 10 ^ 6 := by
  have hd : (2 - 1 / 2 : ℝ) = 3 / 2 := by norm_num only
  have he : (-(2) * (7 / 2) : ℝ) = -(7) := by norm_num only
  have h :=
    middle_principal_of_caps _ hRH (κ := (middleK141Norm : ℝ)) (s := 2) (b := 7 / 2) (x := x) (A :=
      25739 / 10 ^ 6) (R := 51 / 1000) (Rat.cast_nonneg.mpr (by decide +kernel)) (by norm_num only)
      (by norm_num only) ((by norm_num only : (0 : ℝ) ≤ 20).trans hl) middle_k141_profile_jet.1
      middle_k141_profile_jet.2
  dsimp only at h
  rw [hd, he] at h
  exact
    (h (middle_k141_spectral_le hRH (Real.exp_pos x)) (middle_k141_remainder_le hRH hl hr)).trans
      (by norm_num only)

/-- The K156 principal Abel error, with the lower boundary shown separately,
is bounded uniformly on the physical cutoff interval under RH. -/
public theorem middle_k156_principal_le (hRH : RiemannHypothesis) {x : ℝ} (hl : 24 ≤ x)
    (hr : x ≤ 121 / 4) :
    let B := middleK156Profile.map (Rat.castHom ℝ)
    let X := Real.exp x
    let k := (middleK156Norm : ℝ) * Real.exp (-(49 / 20 : ℝ) * (x + 7 / 2))
    let P := fun t ↦ t * deriv (middlePrincipalWeight B k (x + 7 / 2) (39 / 20)) t
    let H := fun t ↦
      AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t -
          (t - Real.log (2 * Real.pi) * Real.log t) +
        1
    |middleTruncPrincipal P H X (X * Real.exp (7 / 2)) - 3 * (gaussianLogZetaConstant - 1) * P 1| ≤
      94703 / 10 ^ 6 := by
  have hd : (49 / 20 - 1 / 2 : ℝ) = 39 / 20 := by norm_num only
  have he : (-(49 / 20) * (7 / 2) : ℝ) = -(343 / 40) := by norm_num only
  have h :=
    middle_principal_of_caps _ hRH (κ := (middleK156Norm : ℝ)) (s := 49 / 20) (b := 7 / 2) (x := x)
      (A := 53703 / 10 ^ 6) (R := 41 / 1000) (Rat.cast_nonneg.mpr (by decide +kernel))
      (by norm_num only) (by norm_num only) ((by norm_num only : (0 : ℝ) ≤ 24).trans hl)
      middle_k156_profile_jet.1 middle_k156_profile_jet.2
  dsimp only at h
  rw [hd, he] at h
  exact
    (h (middle_k156_spectral_le hRH (Real.exp_pos x)) (middle_k156_remainder_le hRH hl hr)).trans
      (by norm_num only)

/-- Transfer a scalar Abel error bound to the weighted principal prime-power
sum. The main integrals, the cutoff term and both lower endpoint terms are retained. -/
public theorem middle_principal_sum_lower (B : Polynomial ℝ) (k z d X R : ℝ) (hX : 1 ≤ X)
    (hXZ : X ≤ Real.exp z) (hB : B.eval 0 = 0) (hB' : B.derivative.eval 0 = 0) :
    let c := Real.log (2 * Real.pi)
    let W := middlePrincipalWeight B k z d
    let P := fun t ↦ t * deriv W t
    let H := fun t ↦
      AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t - (t - c * Real.log t) + 1
    |middleTruncPrincipal P H X (Real.exp z) - 3 * (gaussianLogZetaConstant - 1) * P 1| ≤ R →
      (4 * (∫ t in (1 : ℝ)..X, W t) - (∫ t in (1 : ℝ)..Real.exp z, W t)) +
            4 * (W X * (Chebyshev.psi X - X + c)) +
            3 * (1 - c) * W 1 +
            3 * (gaussianLogZetaConstant - 1) * P 1 -
          R ≤
        4 * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, ArithmeticFunction.vonMangoldt n * W n) -
          (∑ n ∈ Finset.Ioc 0 ⌊Real.exp z⌋₊, ArithmeticFunction.vonMangoldt n * W n) := by
  intro c W P H hR
  have h := middle_centered_anchored B k z d X c hX hXZ hB hB'
  dsimp only at h
  rw [h]
  have hlower := (abs_le.mp hR).1
  rw [middleTruncPrincipal] at hlower
  linarith only [hlower]

/-- The K141 principal prime-power sum has the stated lower bound throughout
its physical cutoff interval under RH. -/
public theorem middle_k141_principal_sum (hRH : RiemannHypothesis) {x : ℝ} (hl : 20 ≤ x)
    (hr : x ≤ 25) :
    let z := x + 7 / 2
    let X := Real.exp x
    let Z := Real.exp z
    let k := (middleK141Norm : ℝ) * Real.exp (-(2 : ℝ) * z)
    let W := middlePrincipalWeight (middleK141Profile.map (Rat.castHom ℝ)) k z (3 / 2)
    let c := Real.log (2 * Real.pi)
    let M := (middleMomentPoly middleK141Profile (5 / 2) 0).map (Rat.castHom ℝ)
    (Real.exp (x / 2) * (72170863822 / 10 ^ 11) - 3 * (k * M.eval z)) +
          4 * (W X * (Chebyshev.psi X - X + c)) +
          3 * (1 - c) * W 1 +
          3 * (gaussianLogZetaConstant - 1) * (1 * deriv W 1) -
        76739 / 10 ^ 6 ≤
      4 * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, ArithmeticFunction.vonMangoldt n * W n) -
        (∑ n ∈ Finset.Ioc 0 ⌊Z⌋₊, ArithmeticFunction.vonMangoldt n * W n) := by
  have hx := (by norm_num only : (0 : ℝ) ≤ 20).trans hl
  have hz : Real.exp (x + 7 / 2) = Real.exp x * Real.exp (7 / 2) := Real.exp_add _ _
  have h :=
    middle_principal_sum_lower (middleK141Profile.map (Rat.castHom ℝ))
      ((middleK141Norm : ℝ) * Real.exp (-(2 : ℝ) * (x + 7 / 2))) (x + 7 / 2) (3 / 2) (Real.exp x)
      (76739 / 10 ^ 6) (Real.one_le_exp hx)
      (Real.exp_le_exp.mpr (le_add_of_nonneg_right (by norm_num only))) middle_k141_profile_jet.1
      middle_k141_profile_jet.2
  dsimp only at h
  have hh := h (by simpa only [hz] using middle_k141_principal_le hRH hl hr)
  have hs :=
    middle_principal_main_slope middleK141Profile (middleK141Norm : ℝ) (7 / 2) x (σ := 5 / 2)
      (by norm_num only) hx (by norm_num only)
  dsimp only at hs
  have ha : (((5 / 2 : ℚ) : ℝ) - 1 / 2) = 2 := by norm_num only [Rat.cast_div, Rat.cast_ofNat]
  have hd : (((5 / 2 : ℚ) : ℝ) - 1) = 3 / 2 := by norm_num only [Rat.cast_div, Rat.cast_ofNat]
  rw [ha, hd] at hs
  let M := (middleMomentPoly middleK141Profile (5 / 2) 0).map (Rat.castHom ℝ)
  have hp : (501705565937097 / 10 ^ 10 : ℝ) ≤ M.eval (7 / 2) := by
    have hm :=
      Polynomial.eval_map_apply (p := middleMomentPoly middleK141Profile (5 / 2) 0) (Rat.castHom ℝ)
        (7 / 2 : ℚ)
    have he :
      M.eval (7 / 2) = (((middleMomentPoly middleK141Profile (5 / 2) 0).eval (7 / 2) : ℚ) : ℝ) := by
      simpa only [Rat.coe_castHom, Rat.cast_div, Rat.cast_ofNat] using hm
    rw [he]
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow] using
      (Rat.cast_le (K := ℝ)).mpr middle_k141_principal_slope.1
  have hK : (middleK141Norm : ℝ) * M.eval 0 ≤ 60099052035064 / 10 ^ 15 := by
    have hm :=
      Polynomial.eval_map_apply (p := middleMomentPoly middleK141Profile (5 / 2) 0) (Rat.castHom ℝ)
        (0 : ℚ)
    have he : M.eval 0 = (((middleMomentPoly middleK141Profile (5 / 2) 0).eval (0) : ℚ) : ℝ) := by
      simpa only [Rat.coe_castHom, Rat.cast_zero] using hm
    rw [he]
    simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow] using
      (Rat.cast_le (K := ℝ)).mpr middle_k141_principal_slope.2
  have he : (-(2 : ℝ) * (7 / 2)) = -(7) := by norm_num only
  have hb : ((7 / 2 : ℝ) / 2) = 7 / 4 := by norm_num only
  rw [he, hb] at hs
  have hδ := mul_le_mul_of_nonneg_left (k141_delta_of_caps hp hK) (Real.exp_nonneg (x / 2))
  rw [hs] at hh
  dsimp only
  linarith only [hh, hδ]

/-- The K156 principal prime-power sum has the stated lower bound throughout
its physical cutoff interval under RH. -/
public theorem middle_k156_principal_sum (hRH : RiemannHypothesis) {x : ℝ} (hl : 24 ≤ x)
    (hr : x ≤ 121 / 4) :
    let z := x + 7 / 2
    let X := Real.exp x
    let Z := Real.exp z
    let k := (middleK156Norm : ℝ) * Real.exp (-(49 / 20 : ℝ) * z)
    let W := middlePrincipalWeight (middleK156Profile.map (Rat.castHom ℝ)) k z (39 / 20)
    let c := Real.log (2 * Real.pi)
    let M := (middleMomentPoly middleK156Profile (59 / 20) 0).map (Rat.castHom ℝ)
    (Real.exp (x / 2) * (72170932589 / 10 ^ 11) - 3 * (k * M.eval z)) +
          4 * (W X * (Chebyshev.psi X - X + c)) +
          3 * (1 - c) * W 1 +
          3 * (gaussianLogZetaConstant - 1) * (1 * deriv W 1) -
        94703 / 10 ^ 6 ≤
      4 * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, ArithmeticFunction.vonMangoldt n * W n) -
        (∑ n ∈ Finset.Ioc 0 ⌊Z⌋₊, ArithmeticFunction.vonMangoldt n * W n) := by
  have hx := (by norm_num only : (0 : ℝ) ≤ 24).trans hl
  have hz : Real.exp (x + 7 / 2) = Real.exp x * Real.exp (7 / 2) := Real.exp_add _ _
  have h :=
    middle_principal_sum_lower (middleK156Profile.map (Rat.castHom ℝ))
      ((middleK156Norm : ℝ) * Real.exp (-(49 / 20 : ℝ) * (x + 7 / 2))) (x + 7 / 2) (39 / 20)
      (Real.exp x) (94703 / 10 ^ 6) (Real.one_le_exp hx)
      (Real.exp_le_exp.mpr (le_add_of_nonneg_right (by norm_num only))) middle_k156_profile_jet.1
      middle_k156_profile_jet.2
  dsimp only at h
  have hh := h (by simpa only [hz] using middle_k156_principal_le hRH hl hr)
  have hs :=
    middle_principal_main_slope middleK156Profile (middleK156Norm : ℝ) (7 / 2) x (σ := 59 / 20)
      (by norm_num only) hx (by norm_num only)
  dsimp only at hs
  have ha : (((59 / 20 : ℚ) : ℝ) - 1 / 2) = 49 / 20 := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
  have hd : (((59 / 20 : ℚ) : ℝ) - 1) = 39 / 20 := by norm_num only [Rat.cast_div, Rat.cast_ofNat]
  rw [ha, hd] at hs
  let M := (middleMomentPoly middleK156Profile (59 / 20) 0).map (Rat.castHom ℝ)
  have hp : (212966675878402 / 10 ^ 9 : ℝ) ≤ M.eval (7 / 2) := by
    have hm :=
      Polynomial.eval_map_apply (p := middleMomentPoly middleK156Profile (59 / 20) 0)
        (Rat.castHom ℝ) (7 / 2 : ℚ)
    have he :
      M.eval (7 / 2) =
        (((middleMomentPoly middleK156Profile (59 / 20) 0).eval (7 / 2) : ℚ) : ℝ) := by
      simpa only [Rat.coe_castHom, Rat.cast_div, Rat.cast_ofNat] using hm
    rw [he]
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow] using
      (Rat.cast_le (K := ℝ)).mpr middle_k156_principal_slope.1
  have hK : (middleK156Norm : ℝ) * M.eval 0 ≤ 60114635943415 / 10 ^ 15 := by
    have hm :=
      Polynomial.eval_map_apply (p := middleMomentPoly middleK156Profile (59 / 20) 0)
        (Rat.castHom ℝ) (0 : ℚ)
    have he : M.eval 0 = (((middleMomentPoly middleK156Profile (59 / 20) 0).eval (0) : ℚ) : ℝ) := by
      simpa only [Rat.coe_castHom, Rat.cast_zero] using hm
    rw [he]
    simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow] using
      (Rat.cast_le (K := ℝ)).mpr middle_k156_principal_slope.2
  have he : (-(49 / 20 : ℝ) * (7 / 2)) = -(343 / 40) := by norm_num only
  have hb : ((7 / 2 : ℝ) / 2) = 7 / 4 := by norm_num only
  rw [he, hb] at hs
  have hδ := mul_le_mul_of_nonneg_left (k156_delta_of_caps hp hK) (Real.exp_nonneg (x / 2))
  rw [hs] at hh
  dsimp only
  linarith only [hh, hδ]

end PseudoPrime.PrimeTestBounds.MillerRabin
