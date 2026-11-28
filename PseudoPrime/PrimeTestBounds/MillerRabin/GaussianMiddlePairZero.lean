/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddlePairExplicit
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleGammaBudget

/-! # Lower bounds for the middle pair zero contributions -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- If all prime bases up to the cutoff pass, the K141 pair zero contribution
has the lower bound obtained from the Euler estimate and the uniform Gamma cap.
The low-pole terms retain their signs. -/
public theorem middle_k141_pair_zero_lower
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n p q r : ℕ} [NeZero p]
    [NeZero q] [NeZero r] [NeZero n] [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)]
    [Fact (2 < q)] [Fact (2 < r)] (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hprod : n = p * q * r) (hp : Odd p) (hq : Odd q) (hr : Odd r) {x : ℝ} (hl : 20 ≤ x)
    (hh : x ≤ 25)
    (hpass :
      ∀ l : ℕ, l.Prime → (l : ℝ) ≤ Real.exp x → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    let χ₁ := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    let χ₂ := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
    let χ₃ := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
    let a : ℝ := 2
    let b : ℝ := 7 / 2
    let z := x + b
    let κ := (middleK141Norm : ℝ)
    let B := middleK141Profile.map (Rat.castHom ℝ)
    let M := (middleMomentPoly middleK141Profile (5 / 2) 0).map (Rat.castHom ℝ)
    let P := middleLowerEndpointPoly B M (a - 1 / 2)
    let E := middleEulerDecay B P κ a b (middleK141Scale : ℝ)
    let K := fun i : ℕ ↦
      LLS.PaperStatements.shiftedPoleKernel (max 1 i) a b (le_max_left _ _) (by norm_num only [a])
    let Z := fun {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) ↦
      -((κ : ℂ) *
            (∑' γ : ℂ,
              ∑ i ∈ Finset.Ico 3 32,
                ((middleK141Kernel ^ 2).coeff (31 - i) : ℂ) *
                  (K i).oscillatingZeroTerm χ (Real.exp x) γ)).re
    let G :=
      23 / 100 -
          κ *
            (Real.exp (-(1 / 2) * z) * (middleK141Kernel.eval₂ (Rat.castHom ℝ) (a - 1 / 2)) ^ 2 /
              (a - 1 / 2) ^ 32) -
          κ *
            (Real.exp (-(5 / 2) * z) * (middleK141Kernel.eval₂ (Rat.castHom ℝ) (-(1 / 2))) ^ 2 /
              (-(1 / 2) : ℝ) ^ 32) +
        1 / 10 ^ 6
    Real.exp (x / 2) * (7215924929 / 10 ^ 10) - (61 / 1000) * (x / 2) ^ 2 - 76739 / 10 ^ 6 +
          Real.exp (-a * x) * E.eval x -
        (2 * Real.log n) * (κ * Real.exp (-a * z)) * B.eval z -
        3 * G ≤
      Z χ₁ + Z χ₂ + Z χ₃ := by
  intro χ₁ χ₂ χ₃ a b z κ B M P E K Z G
  let τ := fun j : ℕ ↦ (χ₁ j).re + (χ₂ j).re + (χ₃ j).re
  obtain ⟨hτ, hτabs, hτknown⟩ := middle_pair_trace_bounds hn ho hu hprod hp hq hr hpass
  have he := middle_k141_euler_reflected hGRH.riemann hl hh τ τ hτ hτabs hτknown
  have hdeg : 2 * middleK141Kernel.natDegree + 3 ≤ 31 :=
    Nat.add_le_add_right (Nat.mul_le_mul_left 2 middle_k141_kernel_degree) 3
  have hx : 0 ≤ x := by linarith only [hl]
  have hf :=
    middle_pair_explicit middleK141Kernel hdeg (a := (2 : ℝ)) (b := 7 / 2) (by norm_num only)
      (by norm_num only) hx (middleK141Norm : ℝ) hGRH hn ho hu hprod hp hq hr hpass
  rw [← middle_k141_profile_eq_pole] at hf
  have hg := middle_k141_gamma_contour_cap hl hh
  have hnabs := neg_abs_le (middleReflectedSum B τ κ a b x)
  dsimp only [χ₁, χ₂, χ₃, τ, a, b, z, κ, B, M, P, E, K, Z, G] at he hf hg hnabs ⊢
  rw [show (-(9 / 16) : ℝ) = -9 / 16 by norm_num only, add_comm (7 / 2 : ℝ) x] at hg
  linarith only [he, hf, hg, hnabs]

/-- If all prime bases up to the cutoff pass, the K156 pair zero contribution
has the lower bound obtained from the Euler estimate and the uniform Gamma cap.
The low-pole terms retain their signs. -/
public theorem middle_k156_pair_zero_lower
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n p q r : ℕ} [NeZero p]
    [NeZero q] [NeZero r] [NeZero n] [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)]
    [Fact (2 < q)] [Fact (2 < r)] (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hprod : n = p * q * r) (hp : Odd p) (hq : Odd q) (hr : Odd r) {x : ℝ} (hl : 24 ≤ x)
    (hh : x ≤ 121 / 4)
    (hpass :
      ∀ l : ℕ, l.Prime → (l : ℝ) ≤ Real.exp x → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    let χ₁ := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    let χ₂ := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
    let χ₃ := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
    let a : ℝ := 49 / 20
    let b : ℝ := 7 / 2
    let z := x + b
    let κ := (middleK156Norm : ℝ)
    let B := middleK156Profile.map (Rat.castHom ℝ)
    let M := (middleMomentPoly middleK156Profile (59 / 20) 0).map (Rat.castHom ℝ)
    let P := middleLowerEndpointPoly B M (a - 1 / 2)
    let E := middleEulerDecay B P κ a b (middleK156Scale : ℝ)
    let K := fun i : ℕ ↦
      LLS.PaperStatements.shiftedPoleKernel (max 1 i) a b (le_max_left _ _) (by norm_num only [a])
    let Z := fun {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) ↦
      -((κ : ℂ) *
            (∑' γ : ℂ,
              ∑ i ∈ Finset.Ico 3 52,
                ((middleK156Kernel ^ 2).coeff (51 - i) : ℂ) *
                  (K i).oscillatingZeroTerm χ (Real.exp x) γ)).re
    let G :=
      1 / 1000 -
          κ *
            (Real.exp (-(1 / 2) * z) * (middleK156Kernel.eval₂ (Rat.castHom ℝ) (a - 1 / 2)) ^ 2 /
              (a - 1 / 2) ^ 52) +
        2 / 10 ^ 6
    Real.exp (x / 2) * (721603265 / 10 ^ 9) - (61 / 1000) * (x / 2) ^ 2 - 94703 / 10 ^ 6 +
          Real.exp (-a * x) * E.eval x -
        (2 * Real.log n) * (κ * Real.exp (-a * z)) * B.eval z -
        3 * G ≤
      Z χ₁ + Z χ₂ + Z χ₃ := by
  intro χ₁ χ₂ χ₃ a b z κ B M P E K Z G
  let τ := fun j : ℕ ↦ (χ₁ j).re + (χ₂ j).re + (χ₃ j).re
  obtain ⟨hτ, hτabs, hτknown⟩ := middle_pair_trace_bounds hn ho hu hprod hp hq hr hpass
  have he := middle_k156_euler_reflected hGRH.riemann hl hh τ τ hτ hτabs hτknown
  have hdeg : 2 * middleK156Kernel.natDegree + 3 ≤ 51 :=
    Nat.add_le_add_right (Nat.mul_le_mul_left 2 middle_k156_kernel_degree) 3
  have hx : 0 ≤ x := by linarith only [hl]
  have hf :=
    middle_pair_explicit middleK156Kernel hdeg (a := (49 / 20 : ℝ)) (b := 7 / 2) (by norm_num only)
      (by norm_num only) hx (middleK156Norm : ℝ) hGRH hn ho hu hprod hp hq hr hpass
  rw [← middle_k156_profile_eq_pole] at hf
  have hg := middle_k156_gamma_contour_cap hl hh
  have hnabs := neg_abs_le (middleReflectedSum B τ κ a b x)
  dsimp only [χ₁, χ₂, χ₃, τ, a, b, z, κ, B, M, P, E, K, Z, G] at he hf hg hnabs ⊢
  rw [show (-(9 / 16) : ℝ) = -9 / 16 by norm_num only, add_comm (7 / 2 : ℝ) x] at hg
  linarith only [he, hf, hg, hnabs]

end PseudoPrime.PrimeTestBounds.MillerRabin
