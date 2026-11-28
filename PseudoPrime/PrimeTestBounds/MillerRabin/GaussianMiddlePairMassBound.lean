/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleThreeMass
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleTailBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddlePairZero

/-! # Normalized upper bounds for the three middle zero contributions -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under passage by the prime bases through the cutoff, the three K141 signed
zero terms are bounded by the conductor, principal mass, pole and Euler budgets. -/
public theorem middle_k141_pair_zero_upper
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n p q r : ℕ} [NeZero p]
    [NeZero q] [NeZero r] [NeZero n] [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)]
    [Fact (2 < q)] [Fact (2 < r)] (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hprod : n = p * q * r) (hp : Odd p) (hq : Odd q) (hr : Odd r) {x : ℝ} (hl : 20 ≤ x)
    (hpass :
      ∀ l : ℕ, l.Prime → (l : ℝ) ≤ Real.exp x → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    let χ₁ := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    let χ₂ := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
    let χ₃ := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
    let κ := (middleK141Norm : ℝ)
    let K := fun j : ℕ ↦
      LLS.PaperStatements.shiftedPoleKernel (max 1 j) 2 (7 / 2) (le_max_left _ _) (by norm_num only)
    let Z := fun {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) ↦
      -((κ : ℂ) *
            (∑' γ : ℂ,
              ∑ j ∈ Finset.Ico 3 32,
                ((middleK141Kernel ^ 2).coeff (31 - j) : ℂ) *
                  (K j).oscillatingZeroTerm χ (Real.exp x) γ)).re
    Z χ₁ + Z χ₂ + Z χ₃ ≤
      3 / 8 * Real.log n + 3 * (30 / 10 ^ 6) -
          6 * κ * (middleMassExtension middleK141Kernel 2 16 ((1 / 2 : ℝ) : ℂ)).re +
        1 / 10 := by
  intro χ₁ χ₂ χ₃ κ K Z
  let α := fun j : ℕ ↦ 3 - ((χ₁ j).re + (χ₂ j).re + (χ₃ j).re)
  have hτ := (middle_pair_trace_bounds hn ho hu hprod hp hq hr hpass).1
  have hα (j : ℕ) : α j ∈ Set.Icc 0 4 := by
    exact ⟨sub_nonneg.mpr (hτ j).2, (sub_le_iff_le_add).mpr (by linarith only [(hτ j).1])⟩
  have hk : 0 ≤ κ := Rat.cast_nonneg.mpr (by decide +kernel)
  have hupper :=
    middle_pair_zero_mass_upper middleK141Kernel 2 (d := 14)
      (by norm_num only [Rat.cast_div, Rat.cast_ofNat]) (by decide) middle_k141_kernel_degree hGRH
      hn ho hu hprod hp hq hr (7 / 2) (Real.exp_pos x) hk hpass
  have hc := congrArg (fun v : ℝ ↦ v * (2 * Real.log n)) middle_k141_mass_center
  have hxi := middle_k141_xi_mass_le hGRH.riemann
  have ht :=
    middle_k141_tail_normalized hGRH.riemann (Real.exp_pos x)
      (by simpa only [Real.log_exp] using hl) α hα
  dsimp only [κ, α] at ht
  dsimp only at hupper
  simp only [Rat.cast_ofNat] at hupper
  change Z χ₁ + Z χ₂ + Z χ₃ ≤ _ at hupper
  dsimp only [κ] at ⊢
  nlinarith only [hupper, hc, hxi, ht]

/-- Under passage by the prime bases through the cutoff, the three K156 signed
zero terms are bounded by the conductor, principal mass, pole and Euler budgets. -/
public theorem middle_k156_pair_zero_upper
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n p q r : ℕ} [NeZero p]
    [NeZero q] [NeZero r] [NeZero n] [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)]
    [Fact (2 < q)] [Fact (2 < r)] (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hprod : n = p * q * r) (hp : Odd p) (hq : Odd q) (hr : Odd r) {x : ℝ} (hl : 24 ≤ x)
    (hpass :
      ∀ l : ℕ, l.Prime → (l : ℝ) ≤ Real.exp x → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    let χ₁ := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    let χ₂ := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
    let χ₃ := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
    let κ := (middleK156Norm : ℝ)
    let K := fun j : ℕ ↦
      LLS.PaperStatements.shiftedPoleKernel (max 1 j) (49 / 20) (7 / 2) (le_max_left _ _)
        (by norm_num only)
    let Z := fun {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) ↦
      -((κ : ℂ) *
            (∑' γ : ℂ,
              ∑ j ∈ Finset.Ico 3 52,
                ((middleK156Kernel ^ 2).coeff (51 - j) : ℂ) *
                  (K j).oscillatingZeroTerm χ (Real.exp x) γ)).re
    Z χ₁ + Z χ₂ + Z χ₃ ≤
      3 / 8 * Real.log n + 3 * (45 / 10 ^ 6) -
          6 * κ * (middleMassExtension middleK156Kernel (49 / 20) 26 ((1 / 2 : ℝ) : ℂ)).re +
        (if 29 ≤ x then 1 / 60 else 1) := by
  intro χ₁ χ₂ χ₃ κ K Z
  let α := fun j : ℕ ↦ 3 - ((χ₁ j).re + (χ₂ j).re + (χ₃ j).re)
  have hτ := (middle_pair_trace_bounds hn ho hu hprod hp hq hr hpass).1
  have hα (j : ℕ) : α j ∈ Set.Icc 0 4 := by
    exact ⟨sub_nonneg.mpr (hτ j).2, (sub_le_iff_le_add).mpr (by linarith only [(hτ j).1])⟩
  have hk : 0 ≤ κ := Rat.cast_nonneg.mpr (by decide +kernel)
  have hupper :=
    middle_pair_zero_mass_upper middleK156Kernel (49 / 20) (d := 24)
      (by norm_num only [Rat.cast_div, Rat.cast_ofNat]) (by decide) middle_k156_kernel_degree hGRH
      hn ho hu hprod hp hq hr (7 / 2) (Real.exp_pos x) hk hpass
  have hc := congrArg (fun v : ℝ ↦ v * (2 * Real.log n)) middle_k156_mass_center
  have hxi := middle_k156_xi_mass_le hGRH.riemann
  have ht :=
    middle_k156_tail_normalized hGRH.riemann (Real.exp_pos x)
      (by simpa only [Real.log_exp] using hl) α hα
  dsimp only [κ, α] at ht
  rw [Real.log_exp] at ht
  dsimp only at hupper
  simp only [Rat.cast_div, Rat.cast_ofNat] at hupper
  change Z χ₁ + Z χ₂ + Z χ₃ ≤ _ at hupper
  dsimp only [κ] at ⊢
  nlinarith only [hupper, hc, hxi, ht]

/-- If all tested prime bases pass, the K141 explicit formula forces this
scalar inequality between the lower and upper zero bounds. -/
public theorem middle_k141_scalar_of_pass
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n p q r : ℕ} [NeZero p]
    [NeZero q] [NeZero r] [NeZero n] [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)]
    [Fact (2 < q)] [Fact (2 < r)] (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hprod : n = p * q * r) (hp : Odd p) (hq : Odd q) (hr : Odd r) {x : ℝ} (hl : 20 ≤ x)
    (hh : x ≤ 25)
    (hpass :
      ∀ l : ℕ, l.Prime → (l : ℝ) ≤ Real.exp x → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    let a : ℝ := 2
    let b : ℝ := 7 / 2
    let z := x + b
    let κ := (middleK141Norm : ℝ)
    let B := middleK141Profile.map (Rat.castHom ℝ)
    let M := (middleMomentPoly middleK141Profile (5 / 2) 0).map (Rat.castHom ℝ)
    let P := middleLowerEndpointPoly B M (a - 1 / 2)
    let E := middleEulerDecay B P κ a b (middleK141Scale : ℝ)
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
      3 / 8 * Real.log n + 3 * (30 / 10 ^ 6) -
          6 * κ * (middleMassExtension middleK141Kernel 2 16 ((1 / 2 : ℝ) : ℂ)).re +
        1 / 10 := by
  exact
    (middle_k141_pair_zero_lower hGRH hn ho hu hprod hp hq hr hl hh hpass).trans
      (middle_k141_pair_zero_upper hGRH hn ho hu hprod hp hq hr hl hpass)

/-- If all tested prime bases pass, the K156 explicit formula forces this
scalar inequality between the lower and upper zero bounds. -/
public theorem middle_k156_scalar_of_pass
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n p q r : ℕ} [NeZero p]
    [NeZero q] [NeZero r] [NeZero n] [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)]
    [Fact (2 < q)] [Fact (2 < r)] (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hprod : n = p * q * r) (hp : Odd p) (hq : Odd q) (hr : Odd r) {x : ℝ} (hl : 24 ≤ x)
    (hh : x ≤ 121 / 4)
    (hpass :
      ∀ l : ℕ, l.Prime → (l : ℝ) ≤ Real.exp x → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    let a : ℝ := 49 / 20
    let b : ℝ := 7 / 2
    let z := x + b
    let κ := (middleK156Norm : ℝ)
    let B := middleK156Profile.map (Rat.castHom ℝ)
    let M := (middleMomentPoly middleK156Profile (59 / 20) 0).map (Rat.castHom ℝ)
    let P := middleLowerEndpointPoly B M (a - 1 / 2)
    let E := middleEulerDecay B P κ a b (middleK156Scale : ℝ)
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
      3 / 8 * Real.log n + 3 * (45 / 10 ^ 6) -
          6 * κ * (middleMassExtension middleK156Kernel (49 / 20) 26 ((1 / 2 : ℝ) : ℂ)).re +
        (if 29 ≤ x then 1 / 60 else 1) := by
  exact
    (middle_k156_pair_zero_lower hGRH hn ho hu hprod hp hq hr hl hh hpass).trans
      (middle_k156_pair_zero_upper hGRH hn ho hu hprod hp hq hr hl hpass)

end PseudoPrime.PrimeTestBounds.MillerRabin
