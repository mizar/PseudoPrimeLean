/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleResidualProfile
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleResidualProfile
import PseudoPrime.Analysis.NumericalLogBounds

/-! # Rational lower profiles for the direct middle residual -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational endpoint profile replaces the logarithmic factors by upper
costs. All coefficients in the replacement depend on the pole rate alone. -/
public noncomputable def middleRatEndpoint (B M : Polynomial ℝ) (d : ℝ) : Polynomial ℝ :=
  Polynomial.C (-3) * M - Polynomial.C (3 * (839 / 1000 + d)) * B

/-- On the nonnegative increasing part of the profile, the lower endpoint
term dominates the rational replacement under RH. -/
public theorem middle_rat_endpoint_le (hRH : RiemannHypothesis) (B M : Polynomial ℝ) {d z : ℝ}
    (hd : 0 ≤ d) (hB : 0 ≤ B.eval z) (hD : 0 ≤ B.derivative.eval z) :
    (middleRatEndpoint B M d).eval z ≤ (middleLowerEndpointPoly B M d).eval z := by
  obtain ⟨h₀, h₁⟩ := gaussian_log_zeta_constant_bounds hRH
  have hlog := mul_nonneg hB (sub_nonneg.mpr Analysis.log_two_mul_pi_lt.le)
  have hmul := mul_nonneg (mul_nonneg hd hB) h₀.le
  have hder := mul_nonneg hD (sub_nonneg.mpr (h₁.le.trans (by norm_num only : (16 / 25 : ℝ) ≤ 1)))
  simp only [middleRatEndpoint, middleLowerEndpointPoly, Polynomial.eval_sub, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C]
  nlinarith only [hlog, hmul, hder]

/-- The rational endpoint polynomial is nonpositive when the profile and
its forward moment are nonnegative. This permits using the upper scale. -/
public theorem middle_rat_endpoint_nonpos (B M : Polynomial ℝ) {d z : ℝ} (hd : 0 ≤ d)
    (hB : 0 ≤ B.eval z) (hM : 0 ≤ M.eval z) : (middleRatEndpoint B M d).eval z ≤ 0 := by
  have h := mul_nonneg (add_nonneg (by norm_num only : (0 : ℝ) ≤ 839 / 1000) hd) hB
  simp only [middleRatEndpoint, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
  nlinarith only [hM, h]

/-- The upper normalization scale suffices for lower-bounding the endpoint
term, even when the analytic endpoint polynomial does not have a known sign. -/
public theorem middle_rat_scaled_endpoint_le (hRH : RiemannHypothesis) (B M : Polynomial ℝ)
    {d z p k : ℝ} (hd : 0 ≤ d) (hB : 0 ≤ B.eval z) (hD : 0 ≤ B.derivative.eval z)
    (hM : 0 ≤ M.eval z) (hk : 0 ≤ k) (hp : k ≤ p) :
    p * (middleRatEndpoint B M d).eval z ≤ k * (middleLowerEndpointPoly B M d).eval z := by
  exact
    (mul_le_mul_of_nonpos_right hp (middle_rat_endpoint_nonpos B M hd hB hM)).trans
      (mul_le_mul_of_nonneg_left (middle_rat_endpoint_le hRH B M hd hB hD) hk)

/-- Two polynomial profiles for the rational residual. The first combines
the reflected Euler moment with the rational lower endpoint polynomial. -/
public noncomputable def middleRatProfiles (a b p : ℝ) (B M : Polynomial ℝ) :
    Fin 2 → Polynomial ℝ :=
  Fin.cases
    (Polynomial.C (6 * p) * middleReflectionPoly B (a + 1 / 2) b -
      Polynomial.C p * (middleRatEndpoint B M (a - 1 / 2)).comp (Polynomial.X + Polynomial.C b))
    (fun _ ↦ Polynomial.C (2 * p / gaussianDirectScale) * B.comp (Polynomial.X + Polynomial.C b))

/-- The rational residual is a pointwise lower bound for the analytic
residual. Only the upper normalization scale and local profile signs enter. -/
public theorem middle_rat_residual_le (hRH : RiemannHypothesis) (B M : Polynomial ℝ)
    {a b κ p s β x : ℝ} (ha : 1 / 2 ≤ a) (hκ : 0 ≤ κ) (hp : κ * Real.exp (-a * b) ≤ p)
    (hB : 0 ≤ B.eval (x + b)) (hD : 0 ≤ B.derivative.eval (x + b)) (hM : 0 ≤ M.eval (x + b)) :
    let P := middleLowerEndpointPoly B M (a - 1 / 2)
    let E := middleEulerDecay B P κ a b p
    gaussianMidResidual s 0 β (middleResidualRates a) (middleRatProfiles a b p B M) x ≤
      gaussianMidResidual s 0 β (middleResidualRates a) (middleResidualProfiles a b κ B E) x := by
  intro P E
  have he :=
    middle_rat_scaled_endpoint_le hRH B M (sub_nonneg.mpr ha) hB hD hM
      (mul_nonneg hκ (Real.exp_pos _).le) hp
  have hρ : (0 : ℝ) ≤ gaussianDirectScale := by norm_num only [gaussianDirectScale]
  have hq :=
    mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by norm_num only : (0 : ℝ) ≤ 2))
        hρ)
      hB
  rw [middle_residual_profiles_eq, gaussianMidResidual, gaussianDecaySum, Fin.sum_univ_two]
  have hr : middleResidualRates a 1 = a - 1 / 2 := rfl
  have h₀ :
    middleRatProfiles a b p B M 0 =
      Polynomial.C (6 * p) * middleReflectionPoly B (a + 1 / 2) b -
        Polynomial.C p * (middleRatEndpoint B M (a - 1 / 2)).comp (Polynomial.X + Polynomial.C b) :=
    rfl
  have h₁ :
    middleRatProfiles a b p B M 1 =
      Polynomial.C (2 * p / gaussianDirectScale) * B.comp (Polynomial.X + Polynomial.C b) :=
    rfl
  rw [hr, h₀, h₁]
  simp only [middleResidualRates, Fin.cases_zero, middleEulerDecay, E, P, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, add_zero]
  have hh := mul_le_mul_of_nonneg_left he (Real.exp_pos (-a * x)).le
  have hc := mul_le_mul_of_nonneg_left hq (Real.exp_pos (-(a - 1 / 2) * x)).le
  linear_combination hh + hc

/-- The forward moment is nonnegative when its input profile is nonnegative
from the evaluation point onward. Use the integral representation once. -/
public theorem middle_forward_moment_nonneg (B : Polynomial ℚ) (r : ℚ) (z : ℝ) (hr : 0 < (r : ℝ))
    (hB : ∀ t, z ≤ t → 0 ≤ (B.map (Rat.castHom ℝ)).eval t) :
    0 ≤ ((middleMomentPoly B r 0).map (Rat.castHom ℝ)).eval z := by
  let P := B.map (Rat.castHom ℝ)
  let Q := P.comp (Polynomial.X + Polynomial.C z)
  have hdeg :=
    Polynomial.natDegree_map_eq_of_injective (f := Rat.castHom ℝ) Rat.cast_injective (p := B)
  have he :
    ((middleMomentPoly B r 0).map (Rat.castHom ℝ)).eval z =
      ∑ i ∈ Finset.range (Q.natDegree + 1),
        Q.coeff i * ((i.factorial : ℝ) / (r : ℝ) ^ (i + 1)) := by
    rw [show Q = Polynomial.taylor z P from (Polynomial.taylor_apply _ _).symm]
    simp only [middleMomentPoly, Polynomial.C_0, add_zero, Polynomial.comp_X, Polynomial.map_sum,
      Polynomial.map_mul, Polynomial.map_C, ← Polynomial.hasseDeriv_map, Rat.coe_castHom,
      Rat.cast_div, Rat.cast_natCast, Rat.cast_pow, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.natDegree_taylor, Polynomial.taylor_coeff, P, hdeg]
  rw [he, ← polynomial_laplace_tail P z hr]
  apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
  intro t ht
  exact mul_nonneg (hB _ (le_add_of_nonneg_right (Set.mem_Ioi.mp ht).le)) (Real.exp_nonneg _)

/-- Passage at the direct K141 cutoff bounds the residual with rational
polynomial profiles. This is the conclusion used by the cell comparisons. -/
public theorem middle_k141_rat_ceiling
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n p q r : ℕ} [NeZero p]
    [NeZero q] [NeZero r] [NeZero n] [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)]
    [Fact (2 < q)] [Fact (2 < r)] (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hprod : n = p * q * r) (hp : Odd p) (hq : Odd q) (hrOdd : Odd r)
    (hL : Real.log n ∈ Set.Icc (42410 : ℝ) 400000)
    (hpass :
      ∀ l : ℕ,
        l.Prime →
          (l : ℝ) ≤ (gaussianDirectScale * Real.log n) ^ 2 →
          PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    let x := Real.log ((gaussianDirectScale * Real.log n) ^ 2)
    let a : ℝ := 2
    let b : ℝ := 7 / 2
    let B := middleK141Profile.map (Rat.castHom ℝ)
    let M := (middleMomentPoly middleK141Profile (5 / 2) 0).map (Rat.castHom ℝ)
    gaussianMidResidual ((7215924929 / 10 ^ 10) - 3 / 8 / gaussianDirectScale) 0 (61 / 1000)
        (middleResidualRates a) (middleRatProfiles a b (middleK141Scale : ℝ) B M) x ≤
      -(118 / 5) := by
  intro x a b B M
  have hx : 20 ≤ x := (gaussian_k141_log_range hL).1
  have hz : 20 ≤ x + b := by
    dsimp only [b]; linarith only [hx]
  have hB : 0 ≤ B.eval (x + b) := middle_k141_tail_sign 0 hz
  have hD : 0 ≤ B.derivative.eval (x + b) := middle_k141_tail_sign 1 hz
  have hm : 0 ≤ M.eval (x + b) :=
    middle_forward_moment_nonneg _ (5 / 2) _ (by norm_num only [Rat.cast_div, Rat.cast_ofNat])
      (fun _ ht ↦ middle_k141_tail_sign 0 (hz.trans ht))
  have hsc : (middleK141Norm : ℝ) * Real.exp (-a * b) ≤ (middleK141Scale : ℝ) := by
    rw [show -a * b = -(7) by norm_num only [a, b]]
    exact middle_k141_scale_le
  have hk : (0 : ℝ) ≤ middleK141Norm := Rat.cast_nonneg.mpr (by decide +kernel)
  exact
    (middle_rat_residual_le hGRH.riemann B M (by norm_num only [a]) hk hsc hB hD hm).trans
      (middle_k141_profile_ceiling hGRH hn ho hu hprod hp hq hrOdd hL hpass)

/-- Passage at the direct K156 cutoff bounds the residual with rational
polynomial profiles. This is the conclusion used by the cell comparisons. -/
public theorem middle_k156_rat_ceiling
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n p q r : ℕ} [NeZero p]
    [NeZero q] [NeZero r] [NeZero n] [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)]
    [Fact (2 < q)] [Fact (2 < r)] (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hprod : n = p * q * r) (hp : Odd p) (hq : Odd q) (hrOdd : Odd r)
    (hL : Real.log n ∈ Set.Icc (400000 : ℝ) 7000000)
    (hpass :
      ∀ l : ℕ,
        l.Prime →
          (l : ℝ) ≤ (gaussianDirectScale * Real.log n) ^ 2 →
          PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    let x := Real.log ((gaussianDirectScale * Real.log n) ^ 2)
    let a : ℝ := 49 / 20
    let b : ℝ := 7 / 2
    let B := middleK156Profile.map (Rat.castHom ℝ)
    let M := (middleMomentPoly middleK156Profile (59 / 20) 0).map (Rat.castHom ℝ)
    gaussianMidResidual ((721603265 / 10 ^ 9) - 3 / 8 / gaussianDirectScale) 0 (61 / 1000)
        (middleResidualRates a) (middleRatProfiles a b (middleK156Scale : ℝ) B M) x ≤
      if 29 ≤ x then -(901 / 20) else -(4407 / 100) := by
  intro x a b B M
  have hx : 24 ≤ x := (gaussian_k156_log_range hL).1
  have hz : 25 ≤ x + b := by
    dsimp only [b]; linarith only [hx]
  have hB : 0 ≤ B.eval (x + b) := middle_k156_tail_sign 0 hz
  have hD : 0 ≤ B.derivative.eval (x + b) := middle_k156_tail_sign 1 hz
  have hm : 0 ≤ M.eval (x + b) :=
    middle_forward_moment_nonneg _ (59 / 20) _ (by norm_num only [Rat.cast_div, Rat.cast_ofNat])
      (fun _ ht ↦ middle_k156_tail_sign 0 (hz.trans ht))
  have hsc : (middleK156Norm : ℝ) * Real.exp (-a * b) ≤ (middleK156Scale : ℝ) := by
    rw [show -a * b = -(343 / 40) by norm_num only [a, b]]
    exact middle_k156_scale_le
  have hk : (0 : ℝ) ≤ middleK156Norm := Rat.cast_nonneg.mpr (by decide +kernel)
  exact
    (middle_rat_residual_le hGRH.riemann B M (by norm_num only [a]) hk hsc hB hD hm).trans
      (middle_k156_profile_ceiling hGRH hn ho hu hprod hp hq hrOdd hL hpass)

end PseudoPrime.PrimeTestBounds.MillerRabin
