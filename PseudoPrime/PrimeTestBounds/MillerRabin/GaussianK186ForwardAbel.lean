/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186DirectComparison
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighForwardMain
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleBoundary
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleTailBudget
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186ContourBudget
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186PsiEndpoint

import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleTailBudget
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186DirectComparison
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186GammaMajorant
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighCompensationPartition

/-! # Abel decomposition of the K186 forward sum -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Remove the compensation and rewrite both finite sums in the weight
used by the principal Abel identity. Only positive indices occur. -/
private theorem k186_forward_raw_eq (x : ℝ) :
    let X := Real.exp x
    let z := x + 5
    let B := HighGaussianKernel.k186.realProfile
    let W := middlePrincipalWeight B (Real.exp (-(11 / 4 : ℝ) * z)) z (9 / 4)
    k186ForwardValue X + 4 * highCompensationBound .k186 X =
      4 * (∑ m ∈ Finset.Ioc 0 ⌊X⌋₊, ArithmeticFunction.vonMangoldt m * W m) -
        (∑ m ∈ Finset.Ioc 0 ⌊Real.exp z⌋₊, ArithmeticFunction.vonMangoldt m * W m) := by
  intro X z B W
  unfold k186ForwardValue
  dsimp only
  rw [sub_add_cancel, ← Real.exp_add]
  have hsum (Y : ℝ) :
    (∑ m ∈ Finset.Ioc 0 ⌊Y⌋₊,
        let v := 5 - Real.log ((m : ℝ) / X)
        ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-(1 / 2) : ℝ) *
          Real.exp (-(HighGaussianKernel.k186.pole : ℝ) * v) *
          B.eval v) =
      ∑ m ∈ Finset.Ioc 0 ⌊Y⌋₊, ArithmeticFunction.vonMangoldt m * W m := by
    apply Finset.sum_congr rfl
    intro m hm
    have ht : (0 : ℝ) < m := Nat.cast_pos.mpr (Finset.mem_Ioc.mp hm).1
    have h := high_forward_weight_eq .k186 x ht
    norm_num only [HighGaussianKernel.pole, Rat.cast_div, Rat.cast_ofNat] at h
    simpa only [W, B, z, X, mul_assoc, HighGaussianKernel.pole, Rat.cast_div, Rat.cast_ofNat] using
      congrArg (fun v : ℝ ↦ ArithmeticFunction.vonMangoldt m * v) h
  rw [hsum, hsum]

/-- The uncompensated K186 forward sum is the explicit main integral,
the anchored Abel residual, and the two endpoint terms. -/
theorem k186_forward_abel {x : ℝ} (hx : 0 ≤ x) :
    let X := Real.exp x
    let z := x + 5
    let B := HighGaussianKernel.k186.realProfile
    let W := middlePrincipalWeight B (Real.exp (-(11 / 4 : ℝ) * z)) z (9 / 4)
    let P := fun t ↦ t * deriv W t
    let c := Real.log (2 * Real.pi)
    let H := fun t ↦ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t -
      (t - c * Real.log t) + 1
    k186ForwardValue X + 4 * highCompensationBound .k186 X =
      (let K := HighGaussianKernel.k186
       let M := (middleMomentPoly K.ratProfile (K.pole + 1 / 2) 0).map (Rat.castHom ℝ)
       Real.exp (x / 2) * (4 * Real.exp (-55 / 4) * M.eval 5 -
         Real.exp (5 / 2) * M.eval 0) - 3 * (Real.exp (-(11 / 4 : ℝ) * z) * M.eval z)) +
      (4 * (∫ t in (1 : ℝ)..X, H t * deriv P t) -
        (∫ t in (1 : ℝ)..Real.exp z, H t * deriv P t) - 4 * (P X * H X)) +
      4 * (W X * (Chebyshev.psi X - X + c)) + 3 * (1 - c) * W 1 := by
  intro X z B W P c H
  rw [k186_forward_raw_eq x]
  have ha := middle_centered_anchored B (Real.exp (-(11 / 4 : ℝ) * z)) z (9 / 4) X c
    (Real.one_le_exp hx) (Real.exp_le_exp.mpr (le_add_of_nonneg_right (by norm_num only)))
    (high_real_profile_at_zero .k186).1 (high_real_profile_at_zero .k186).2
  have hm := high_forward_main_integral .k186 hx
  norm_num only [HighGaussianKernel.pole, Rat.cast_div, Rat.cast_ofNat] at hm
  dsimp only at ha ⊢
  rw [ha]
  change (4 * (∫ t in (1 : ℝ)..X, W t) - (∫ t in (1 : ℝ)..Real.exp z, W t)) = _ at hm
  rw [hm]
  have hr : HighGaussianKernel.k186.pole + 1 / 2 = (13 / 4 : ℚ) := by
    norm_num only [HighGaussianKernel.pole]
  rw [hr, show (-55 / 4 : ℝ) = -(55 / 4) by ring]

/-- The exponential at the fixed profile coordinate admits a coarse rational upper bound. -/
theorem k186_exp_neg_pole_le : Real.exp (-55 / 4) ≤ (1 / 800000 : ℝ) := by
  have h := middle_tail_exp_le 1100 (by decide +kernel)
  have hc := (Rat.cast_le (K := ℝ)).mpr (by decide +kernel : 1 / middleTailExpDen 1100 ≤ 1 / 800000)
  have hz : -((1100 : ℝ) / 80) = -55 / 4 := by norm_num only
  simp only [Nat.cast_ofNat, hz] at h
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h.trans hc

/-- The RH Chebyshev error at the moving lower cutoff spends at most
301/20000 of the square of its logarithm. -/
private theorem k186_psi_endpoint_sharp (hRH : RiemannHypothesis) {x : ℝ} (hx : 20 ≤ x) :
    let X := Real.exp x
    let w := Real.exp (-55 / 4) * HighGaussianKernel.k186.realProfile.eval 5
    let c := Real.log (2 * Real.pi)
    (-(301 / 20000 * x ^ 2) ≤ 4 * (w / Real.sqrt X) * (Chebyshev.psi X - X + c)) := by
  intro X w c
  have hB := high_real_profile_at_five_pos .k186
  have hw : 0 ≤ w := mul_nonneg (Real.exp_nonneg _) hB.le
  have hExp : Real.exp (-55 / 4) ≤ (1068 / 10 ^ 9 : ℝ) := by
    have h :=
      (middle_tail_exp_le 1100 (by decide +kernel)).trans
        (Rat.cast_le.mpr (by decide +kernel : 1 / middleTailExpDen 1100 ≤ 1068 / 10 ^ 9))
    norm_num only [Nat.cast_ofNat, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] at h ⊢
    exact h
  have hcap : w ≤ 903 / 10000 := by
    exact
      (mul_le_mul hExp k186_profile_five_le_sharp hB.le (by norm_num only)).trans (by norm_num only)
  have hψ :=
    middle_exp_psi_boundary_le hRH hx (b := 0) (w := w) (c := 0) (β := 301 / 5000) le_rfl hw le_rfl
      (by linarith only [hcap])
  simp only [mul_zero, zero_mul, add_zero] at hψ
  change 4 * w * (|Chebyshev.psi X - X| / Real.sqrt X) ≤ 301 / 5000 * (x / 2) ^ 2 at hψ
  have h1 :=
    mul_le_mul_of_nonneg_left (neg_abs_le (Chebyshev.psi X - X))
      (show 0 ≤ 4 * (w / Real.sqrt X) by
        exact mul_nonneg (by norm_num only) (div_nonneg hw (Real.sqrt_nonneg _)))
  have hc : 0 ≤ c := Real.log_nonneg (by linarith only [Real.pi_gt_three])
  have h2 :=
    mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4) (div_nonneg hw (Real.sqrt_nonneg X))) hc
  calc
    -(301 / 20000 * x ^ 2) ≤ 4 * (w / Real.sqrt X) * -|Chebyshev.psi X - X| := by
      convert neg_le_neg hψ using 1 <;> ring
    _ ≤ 4 * (w / Real.sqrt X) * (Chebyshev.psi X - X) := h1
    _ ≤ _ := by
      rw [mul_add]; exact le_add_of_nonneg_right h2

/-- The coarse RH Chebyshev error bound at the fixed K186 weight. -/
theorem k186_psi_endpoint_lower (hRH : RiemannHypothesis) {x : ℝ} (hx : 20 ≤ x) :
    let X := Real.exp x
    let w := Real.exp (-55 / 4) * HighGaussianKernel.k186.realProfile.eval 5
    let c := Real.log (2 * Real.pi)
    (-(x ^ 2 / 48) ≤ 4 * (w / Real.sqrt X) * (Chebyshev.psi X - X + c)) := by
  have hs := k186_psi_endpoint_sharp hRH hx
  linarith only [hs, sq_nonneg x]

/-- At the moving cutoff the Abel weight is the fixed endpoint
profile divided by the square root of the cutoff. -/
private theorem k186_abel_endpoint_sharp (hRH : RiemannHypothesis) {x : ℝ} (hx : 20 ≤ x) :
    let X := Real.exp x
    let z := x + 5
    let W :=
      middlePrincipalWeight HighGaussianKernel.k186.realProfile (Real.exp (-(11 / 4 : ℝ) * z)) z
        (9 / 4)
    (-(301 / 20000 * x ^ 2) ≤ 4 * (W X * (Chebyshev.psi X - X + Real.log (2 * Real.pi)))) := by
  intro X z W
  have hw := high_forward_weight_eq .k186 x (t := X) (Real.exp_pos x)
  have hX : X ≠ 0 := (Real.exp_pos x).ne'
  have heX : X / Real.exp x = 1 := div_self hX
  have h :
    (X ^ (-(1 / 2) : ℝ)) * Real.exp (-(55 / 4 : ℝ)) * HighGaussianKernel.k186.realProfile.eval 5 =
      W X := by
    dsimp only at hw
    rw [heX, Real.log_one, sub_zero] at hw
    norm_num only [HighGaussianKernel.pole, Rat.cast_div, Rat.cast_ofNat] at hw
    exact hw
  have hX0 : 0 ≤ X := (Real.exp_pos x).le
  rw [← h, Real.rpow_neg hX0, ← Real.sqrt_eq_rpow]
  have h' := k186_psi_endpoint_sharp hRH hx
  change
    -(301 / 20000 * x ^ 2) ≤
      4 * (Real.exp (-55 / 4) * HighGaussianKernel.k186.realProfile.eval 5 / Real.sqrt X) *
        (Chebyshev.psi X - X + Real.log (2 * Real.pi)) at h'
  rw [show -(55 / 4 : ℝ) = -55 / 4 by ring]
  convert h' using 1
  ring

/-- The fixed RH endpoint bound used in the far Abel budget. -/
theorem k186_abel_endpoint_lower (hRH : RiemannHypothesis) {x : ℝ} (hx : 20 ≤ x) :
    let X := Real.exp x
    let z := x + 5
    let W :=
      middlePrincipalWeight HighGaussianKernel.k186.realProfile (Real.exp (-(11 / 4 : ℝ) * z)) z
        (9 / 4)
    (-(x ^ 2 / 48) ≤ 4 * (W X * (Chebyshev.psi X - X + Real.log (2 * Real.pi)))) := by
  have hs := k186_abel_endpoint_sharp hRH hx
  linarith only [hs, sq_nonneg x]

/-- On the positive profile ray, decreasing the Laplace rate increases
the moment because every derivative at the cutoff is nonnegative. -/
private theorem k186_forward_moment_le_gamma {z : ℝ} (hz : 65 ≤ z) :
    (middleMomentPoly HighGaussianKernel.k186.realProfile (13 / 4) 0).eval z ≤
      (middleMomentPoly HighGaussianKernel.k186.realProfile (7 / 4) 0).eval z := by
  let B := HighGaussianKernel.k186.realProfile
  simp only [middleMomentPoly, Polynomial.C_0, add_zero, Polynomial.comp_X,
    Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]
  apply Finset.sum_le_sum
  intro i _
  have hd :=
    high_int_profile_sign .k186 65 k186_profile_grid_check i (show ((65 : ℤ) : ℝ) ≤ z from hz)
  have he :=
    congrArg (fun P : Polynomial ℝ ↦ P.eval z)
      (congrFun (Polynomial.factorial_smul_hasseDeriv (R := ℝ) (k := i)) B)
  change (i.factorial • Polynomial.hasseDeriv i B).eval z = _ at he
  simp only [nsmul_eq_mul, Polynomial.eval_natCast_mul] at he
  change 0 ≤ ((Polynomial.derivative^[i]) B).eval z at hd
  rw [← he] at hd
  change
    (Polynomial.hasseDeriv i B).eval z * ((i.factorial : ℝ) / (13 / 4) ^ (i + 1)) ≤
      (Polynomial.hasseDeriv i B).eval z * ((i.factorial : ℝ) / (7 / 4) ^ (i + 1))
  rw [← mul_div_assoc, ← mul_div_assoc,
    mul_comm ((Polynomial.hasseDeriv i B).eval z) (i.factorial : ℝ)]
  exact
    div_le_div_of_nonneg_left hd (pow_pos (by norm_num only) _)
      (pow_le_pow_left₀ (by norm_num only) (by norm_num only) _)

/-- The lower integration endpoint of the forward main term costs at
most one millionth beyond 65, using the already checked Gamma majorant. -/
theorem k186_forward_fixed_endpoint_le {z : ℝ} (hz : 65 ≤ z) :
    3 *
        (Real.exp (-(11 / 4 : ℝ) * z) *
          (middleMomentPoly HighGaussianKernel.k186.realProfile (13 / 4) 0).eval z) ≤
      1 / 10 ^ 6 := by
  have hg := k186_gamma_geometric_ray_le hz
  have he := congrArg (fun P : Polynomial ℝ ↦ P.eval z) (k186_gamma_geometric_translate 0)
  simp only [Polynomial.C_0, add_zero, Polynomial.comp_X, Polynomial.eval_mul,
    Polynomial.eval_C] at he
  rw [he] at hg
  have hm :=
    mul_le_mul_of_nonneg_left (k186_forward_moment_le_gamma hz)
      (Real.exp_nonneg (-(11 / 4 : ℝ) * z))
  have hpos : 0 ≤ k186GammaGeometricPoly.eval z := by
    unfold k186GammaGeometricPoly
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]
    apply Finset.sum_nonneg
    intro j _
    exact
      mul_nonneg (mul_nonneg (by norm_num only) (pow_nonneg (by norm_num only) _))
        (high_int_profile_sign .k186 65 k186_profile_grid_check j (show ((65 : ℤ) : ℝ) ≤ z from hz))
  have hp := mul_nonneg (Real.exp_nonneg (-(11 / 4 : ℝ) * z)) hpos
  rw [he] at hp
  linarith only [hg, hm, hp]

/-- The constant Abel endpoint at one contributes at least minus one.
The zeroth term of the checked geometric majorant bounds the weight. -/
private theorem k186_abel_at_one_lower {z : ℝ} (hz : 65 ≤ z) :
    let B := HighGaussianKernel.k186.realProfile
    let W := middlePrincipalWeight B (Real.exp (-(11 / 4 : ℝ) * z)) z (9 / 4)
    (-1 ≤ 3 * (1 - Real.log (2 * Real.pi)) * W 1) := by
  intro B W
  have hsign (j : ℕ) :=
    high_int_profile_sign .k186 65 k186_profile_grid_check j (show ((65 : ℤ) : ℝ) ≤ z from hz)
  have hb : 0 ≤ B.eval z := by simpa only [Function.iterate_zero, id_eq] using hsign 0
  have hmajor : 2 * B.eval z ≤ k186GammaGeometricPoly.eval z := by
    unfold k186GammaGeometricPoly
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]
    have hs :=
      Finset.single_le_sum (f := fun j ↦
        2 * (4 / 7 : ℝ) ^ j * ((Polynomial.derivative^[j]) B).eval z) (s :=
        Finset.range (B.natDegree + 1))
        (fun j _ ↦
          mul_nonneg (mul_nonneg (by norm_num only) (pow_nonneg (by norm_num only) _)) (hsign j))
        (Finset.mem_range.mpr (Nat.succ_pos B.natDegree) : 0 ∈ _)
    simpa only [pow_zero, mul_one, Function.iterate_zero, id_eq, B] using hs
  have hm := mul_le_mul_of_nonneg_left hmajor (Real.exp_nonneg (-(11 / 4 : ℝ) * z))
  have he : W 1 = Real.exp (-(11 / 4 : ℝ) * z) * B.eval z := by
    simp only [W, middlePrincipalWeight, Real.log_one, Real.one_rpow, sub_zero, one_mul]
  have hw₀ : 0 ≤ W 1 := by
    rw [he]
    exact mul_nonneg (Real.exp_nonneg _) hb
  have hw₁ : W 1 ≤ 1 / 100 := by
    rw [he]
    linarith only [hm, k186_gamma_geometric_ray_le hz]
  have hc : Real.log (2 * Real.pi) ≤ 4 := by
    have h : 2 * Real.pi ≤ Real.exp 4 :=
      (show 2 * Real.pi ≤ 1 + 4 + 4 ^ 2 / 2 by linarith only [Real.pi_lt_four]).trans
        (Real.quadratic_le_exp_of_nonneg (by norm_num only))
    simpa only [Real.log_exp] using Real.log_le_log (mul_pos (by norm_num only) Real.pi_pos) h
  have hm₀ :=
    mul_le_mul_of_nonneg_right
      (show (-9 : ℝ) ≤ 3 * (1 - Real.log (2 * Real.pi)) by linarith only [hc]) hw₀
  have hm₁ := mul_le_mul_of_nonpos_left hw₁ (show (-9 : ℝ) ≤ 0 by norm_num only)
  linarith only [hm₀, hm₁]

/-- Casting the rational main moment yields its real-rate representation. -/
private theorem k186_forward_moment_map :
    (middleMomentPoly HighGaussianKernel.k186.ratProfile (HighGaussianKernel.k186.pole + 1 / 2)
            0).map
        (Rat.castHom ℝ) =
      middleMomentPoly HighGaussianKernel.k186.realProfile (13 / 4) 0 := by
  have hd :=
    Polynomial.natDegree_map_eq_of_injective (Rat.castHom ℝ).injective (p :=
      HighGaussianKernel.k186.ratProfile)
  rw [high_comp_profile_map] at hd
  have hr : ((HighGaussianKernel.k186.pole + 1 / 2 : ℚ) : ℝ) = 13 / 4 := by
    norm_num only [HighGaussianKernel.pole, Rat.cast_add, Rat.cast_div, Rat.cast_ofNat,
      Rat.cast_one]
  simp only [middleMomentPoly, Polynomial.map_comp, Polynomial.map_sum, Polynomial.map_add,
    Polynomial.map_X, Polynomial.map_C, Polynomial.map_mul, Rat.coe_castHom,
    ← Polynomial.hasseDeriv_map, hd, high_comp_profile_map, Rat.cast_div, Rat.cast_natCast,
    Rat.cast_zero, Rat.cast_pow, hr]

/-- The anchored Abel residual combines two integrals and the contribution
of the log-weighted error at the cutoff. -/
noncomputable def k186AbelResidual (x : ℝ) : ℝ :=
  let X := Real.exp x
  let z := x + 5
  let W :=
    middlePrincipalWeight HighGaussianKernel.k186.realProfile (Real.exp (-(11 / 4 : ℝ) * z)) z
      (9 / 4)
  let P := fun t ↦ t * deriv W t
  let c := Real.log (2 * Real.pi)
  let H := fun t ↦
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t - (t - c * Real.log t) + 1
  4 * (∫ t in (1 : ℝ)..X, H t * deriv P t) - (∫ t in (1 : ℝ)..Real.exp z, H t * deriv P t) -
    4 * (P X * H X)

/-- The two lower-limit contributions to the K186 Abel formula,
written as a polynomial multiplied by the common exponential factor. -/
noncomputable def k186ForwardEndpoint (z : ℝ) : ℝ :=
  let B := HighGaussianKernel.k186.realProfile
  Real.exp (-(11 / 4 : ℝ) * z) *
    (3 * (middleMomentPoly B (13 / 4) 0).eval z - 3 * (1 - Real.log (2 * Real.pi)) * B.eval z)

/-- The scalar forward budget uses the certified main slope and retains
the exact moving-tail residual and lower-limit polynomial. -/
noncomputable def k186FiniteForward (x : ℝ) : ℝ :=
  0.7216056623106 * Real.exp (x / 2) - 301 / 20000 * x ^ 2 - (x + 5) ^ 2 / 6000 -
      k186ForwardEndpoint (x + 5) +
    k186AbelResidual x

/-- Under RH, a compensation variation cap of 1/1000 suffices for the
finite forward budget. The main compensation only changes the slope. -/
theorem k186_finite_forward_le (hRH : RiemannHypothesis) {x : ℝ} (hx : 20 ≤ x)
    (hI : Real.exp (5 / 2) * highCompensationMain .k186 ≤ 13765063832627 / 500000000000000000)
    (hV : highCompensationVariation .k186 ≤ 1 / 1000) :
    k186FiniteForward x ≤ k186ForwardValue (Real.exp x) := by
  have ha := k186_forward_abel ((by norm_num only : (0 : ℝ) ≤ 20).trans hx)
  have hp := k186_abel_endpoint_sharp hRH hx
  have hs := mul_le_mul_of_nonneg_left (k186_forward_slope hI) (Real.exp_nonneg (x / 2))
  have hv := mul_le_mul_of_nonneg_left hV (sq_nonneg (x + 5))
  dsimp only at ha hp hs
  rw [k186_forward_moment_map] at ha hs
  rw [highCompensationBound, ← Real.exp_add, Real.log_exp, Real.sqrt_eq_rpow,
    Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, show x * (1 / 2 : ℝ) = x / 2 by ring] at ha
  simp only [middlePrincipalWeight, Real.log_one, Real.one_rpow, sub_zero, one_mul] at ha hp
  unfold k186FiniteForward k186ForwardEndpoint k186AbelResidual
  simp only [Real.log_exp]
  linarith only [ha, hp, hs, hv]

/-- After the endpoint bounds, the forward arithmetic sum only needs a
constant lower bound on the anchored Abel residual to fit its far budget. -/
theorem k186_forward_raw_of_residual (hRH : RiemannHypothesis) {x : ℝ} (hx : 60 ≤ x)
    (hR : -19798 ≤ k186AbelResidual x) :
    let K := HighGaussianKernel.k186
    let M := (middleMomentPoly K.ratProfile (K.pole + 1 / 2) 0).map (Rat.castHom ℝ)
    let X := Real.exp x
    Real.exp (x / 2) * (4 * Real.exp (-55 / 4) * M.eval 5 - Real.exp (5 / 2) * M.eval 0) -
        ((x + 5) ^ 2 / 24 + 19800) ≤
      k186ForwardValue X + 4 * highCompensationBound .k186 X := by
  have hx₀ : 0 ≤ x := (by norm_num only : (0 : ℝ) ≤ 60).trans hx
  have hz : 65 ≤ x + 5 := by linarith only [hx]
  have ha := k186_forward_abel hx₀
  have hp := k186_abel_endpoint_lower hRH ((by norm_num only : (20 : ℝ) ≤ 60).trans hx)
  have hm := k186_forward_fixed_endpoint_le hz
  rw [← k186_forward_moment_map] at hm
  have he := k186_abel_at_one_lower hz
  have hsq := pow_le_pow_left₀ hx₀ (le_add_of_nonneg_right (show (0 : ℝ) ≤ 5 by norm_num only)) 2
  dsimp only [k186AbelResidual] at ha hp he hR ⊢
  linarith only [ha, hp, hm, he, hR, hsq, sq_nonneg (x + 5)]

/-- The far uniform case follows from the two compensation caps and the
anchored Abel residual at the selected cutoff. -/
theorem uniform_k186_far_of_abel {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 30000000000000 ≤ Real.log n)
    (hI : Real.exp (5 / 2) * highCompensationMain .k186 ≤ 13765063832627 / 500000000000000000)
    (hV : highCompensationVariation .k186 ≤ 1 / 4)
    (hR : -19798 ≤ k186AbelResidual (Real.log ((gaussianK186FarScale * Real.log n) ^ 2))) :
    HasRejectingPrime n (gaussianWitnessCutoff (Real.log n)) := by
  let y := gaussianK186FarScale * Real.log n
  let x := Real.log (y ^ 2)
  have hy : 0 < y :=
    mul_pos (by norm_num only [gaussianK186FarScale])
      ((by norm_num only : (0 : ℝ) < 30000000000000).trans_le hL)
  have hx : 60 ≤ x := by
    have h := k186_gamma_far_domain hL
    change 65 ≤ 5 + x at h
    linarith only [h]
  have he : Real.exp x = y ^ 2 := Real.exp_log (pow_pos hy _)
  have hy' : Real.exp (x / 2) = y := by
    have h : x / 2 = Real.log y := by
      dsimp only [x]
      rw [Real.log_pow, Nat.cast_ofNat]
      ring
    rw [h, Real.exp_log hy]
  apply uniform_k186_far_of_forward hn ho hu hGRH hL
  apply k186_forward_le_of_raw hy hI hV
  have h := k186_forward_raw_of_residual hGRH.riemann hx hR
  dsimp only at h ⊢
  rw [he, hy'] at h
  rw [show 5 + Real.log (y ^ 2) = x + 5 from add_comm 5 x]
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
