/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleHalfPoint
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianDirectMiddleResidual

/-! # Two decay profiles for the middle Gaussian residual -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The Euler term decays at the pole rate and the reflected conductor
term at the pole rate minus one half. -/
public noncomputable def middleResidualRates (a : ℝ) : Fin 2 → ℝ :=
  Fin.cases a (fun _ ↦ a - 1 / 2)

/-- In the subtracted decay sum the Euler lower polynomial has negative
sign and the shifted reflected conductor polynomial has positive sign. -/
public noncomputable def middleResidualProfiles (a b κ : ℝ) (B E : Polynomial ℝ) :
    Fin 2 → Polynomial ℝ :=
  Fin.cases (-E)
    (fun _ ↦
      Polynomial.C (2 * κ * Real.exp (-a * b) / gaussianDirectScale) *
        B.comp (Polynomial.X + Polynomial.C b))

/-- The two profiles put the scalar inequality in the same residual form
used by the endpoint and curvature lemmas. -/
public theorem middle_residual_profiles_eq (a b κ s β : ℝ) (B E : Polynomial ℝ) (x : ℝ) :
    gaussianMidResidual s 0 β (middleResidualRates a) (middleResidualProfiles a b κ B E) x =
      s * Real.exp (x / 2) - β / 4 * x ^ 2 + Real.exp (-a * x) * E.eval x -
        Real.exp (-(a - 1 / 2) * x) *
          ((2 * κ * Real.exp (-a * b) / gaussianDirectScale) * B.eval (x + b)) := by
  have h₁ : middleResidualRates a 1 = a - 1 / 2 := rfl
  have hP :
    middleResidualProfiles a b κ B E 1 =
      Polynomial.C (2 * κ * Real.exp (-a * b) / gaussianDirectScale) *
        B.comp (Polynomial.X + Polynomial.C b) :=
    rfl
  rw [gaussianMidResidual, gaussianDecaySum, Fin.sum_univ_two, h₁, hP]
  simp only [middleResidualRates, middleResidualProfiles, Fin.cases_zero, Polynomial.eval_neg,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, add_zero, mul_neg]
  ring

/-- For K141, passage bounds the two-profile residual used by interval checks. -/
public theorem middle_k141_profile_ceiling
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
    let κ := (middleK141Norm : ℝ)
    let B := middleK141Profile.map (Rat.castHom ℝ)
    let M := (middleMomentPoly middleK141Profile (5 / 2) 0).map (Rat.castHom ℝ)
    let P := middleLowerEndpointPoly B M (a - 1 / 2)
    let E := middleEulerDecay B P κ a b (middleK141Scale : ℝ)
    gaussianMidResidual ((7215924929 / 10 ^ 10) - 3 / 8 / gaussianDirectScale) 0 (61 / 1000)
        (middleResidualRates a) (middleResidualProfiles a b κ B E) x ≤
      -(118 / 5) := by
  intro x a b κ B M P E
  rw [middle_residual_profiles_eq]
  exact middle_k141_residual_ceiling hGRH hn ho hu hprod hp hq hrOdd hL hpass

/-- For K156, passage bounds the two-profile residual used by interval checks. -/
public theorem middle_k156_profile_ceiling
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
    let κ := (middleK156Norm : ℝ)
    let B := middleK156Profile.map (Rat.castHom ℝ)
    let M := (middleMomentPoly middleK156Profile (59 / 20) 0).map (Rat.castHom ℝ)
    let P := middleLowerEndpointPoly B M (a - 1 / 2)
    let E := middleEulerDecay B P κ a b (middleK156Scale : ℝ)
    gaussianMidResidual ((721603265 / 10 ^ 9) - 3 / 8 / gaussianDirectScale) 0 (61 / 1000)
        (middleResidualRates a) (middleResidualProfiles a b κ B E) x ≤
      if 29 ≤ x then -(901 / 20) else -(4407 / 100) := by
  intro x a b κ B M P E
  rw [middle_residual_profiles_eq]
  exact middle_k156_residual_ceiling hGRH hn ho hu hprod hp hq hrOdd hL hpass

end PseudoPrime.PrimeTestBounds.MillerRabin
