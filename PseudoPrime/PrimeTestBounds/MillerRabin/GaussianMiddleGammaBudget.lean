/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleGammaPoly
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleGammaUniform

/-! # Constant Gamma budgets for the direct middle contours -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The K141 Gamma contour is bounded by its uniform polynomial budget,
the explicit low-pole terms, and the certified approximation allowance. -/
public theorem middle_k141_gamma_contour_cap {x : ℝ} (hx : 20 ≤ x) (hx' : x ≤ 25) :
    let a : ℝ := 2
    let b : ℝ := 7 / 2
    let ha : 1 / 2 < a := by norm_num only [a]
    let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
    let l := fun t : ℝ ↦ ((-(9 / 16) : ℝ) : ℂ) + Complex.I * t
    let F := fun s ↦
      ∑ i ∈ Finset.Ico 3 32,
        ((middleK141Kernel ^ 2).coeff (31 - i) : ℂ) *
          (LLS.PaperStatements.shiftedPoleKernel (max 1 i) a b (le_max_left _ _) ha).function s
    let W := fun s : ℂ ↦ F s * Complex.exp (s * (x : ℂ))
    let z := b + x
    let D := ((1 / (2 * Real.pi) : ℝ) : ℂ)
    let κ := (middleK141Norm : ℝ)
    κ *
        ((D * (∫ t : ℝ, logDeriv Complex.Gammaℝ (r t + 1 / 2) * W (r t))).re +
          (D * (∫ t : ℝ, logDeriv Complex.Gammaℝ (1 / 2 - l t) * W (l t))).re) ≤
      23 / 100 -
          κ *
            (Real.exp (-(1 / 2) * z) * (middleK141Kernel.eval₂ (Rat.castHom ℝ) (a - 1 / 2)) ^ 2 /
              (a - 1 / 2) ^ 32) -
          κ *
            (Real.exp (-(5 / 2) * z) * (middleK141Kernel.eval₂ (Rat.castHom ℝ) (-(1 / 2))) ^ 2 /
              (-(1 / 2) : ℝ) ^ 32) +
        1 / 10 ^ 6 := by
  intro a b ha r l F W z D κ
  have hz : z ∈ Set.Icc (47 / 2) (57 / 2) := by
    dsimp only [z, b]
    exact ⟨by linarith only [hx], by linarith only [hx']⟩
  have h := middle_k141_gamma_upper_le hx hx'
  have hcap := middle_k141_gamma_uniform_le hz
  dsimp only [r, l, F, W, z, D, κ, a, b] at h hcap ⊢
  linarith only [h, hcap]

/-- The K156 Gamma contour is bounded by its uniform polynomial budget,
the explicit low-pole terms, and the certified approximation allowance. -/
public theorem middle_k156_gamma_contour_cap {x : ℝ} (hx : 24 ≤ x) (hx' : x ≤ 121 / 4) :
    let a : ℝ := 49 / 20
    let b : ℝ := 7 / 2
    let ha : 1 / 2 < a := by norm_num only [a]
    let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
    let l := fun t : ℝ ↦ ((-(9 / 16) : ℝ) : ℂ) + Complex.I * t
    let F := fun s ↦
      ∑ i ∈ Finset.Ico 3 52,
        ((middleK156Kernel ^ 2).coeff (51 - i) : ℂ) *
          (LLS.PaperStatements.shiftedPoleKernel (max 1 i) a b (le_max_left _ _) ha).function s
    let W := fun s : ℂ ↦ F s * Complex.exp (s * (x : ℂ))
    let z := b + x
    let D := ((1 / (2 * Real.pi) : ℝ) : ℂ)
    let κ := (middleK156Norm : ℝ)
    κ *
        ((D * (∫ t : ℝ, logDeriv Complex.Gammaℝ (r t + 1 / 2) * W (r t))).re +
          (D * (∫ t : ℝ, logDeriv Complex.Gammaℝ (1 / 2 - l t) * W (l t))).re) ≤
      1 / 1000 -
          κ *
            (Real.exp (-(1 / 2) * z) * (middleK156Kernel.eval₂ (Rat.castHom ℝ) (a - 1 / 2)) ^ 2 /
              (a - 1 / 2) ^ 52) +
        2 / 10 ^ 6 := by
  intro a b ha r l F W z D κ
  have hz : z ∈ Set.Icc (55 / 2) (135 / 4) := by
    dsimp only [z, b]
    exact ⟨by linarith only [hx], by linarith only [hx']⟩
  have h := middle_k156_gamma_upper_le hx hx'
  have hcap := middle_k156_gamma_uniform_le hz
  dsimp only [r, l, F, W, z, D, κ, a, b] at h hcap ⊢
  linarith only [h, hcap]

/-- The three pair conductors charge the physical K141 profile at log cutoff.
This evaluation uses the same left contour and normalization as the Gamma budget. -/
public theorem middle_k141_pair_conductor {x : ℝ} (hx : 0 ≤ x) {n p q r : ℕ} [NeZero p] [NeZero q]
    [NeZero r] (hn : n = p * q * r) :
    let a : ℝ := 2
    let b : ℝ := 7 / 2
    let ha : 1 / 2 < a := by norm_num only [a]
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let F := fun s ↦
      ∑ i ∈ Finset.Ico 3 32,
        ((middleK141Kernel ^ 2).coeff (31 - i) : ℂ) *
          (LLS.PaperStatements.shiftedPoleKernel (max 1 i) a b (le_max_left _ _) ha).function s
    let L := Real.log (p * q : ℕ) + Real.log (p * r : ℕ) + Real.log (q * r : ℕ)
    let κ := (middleK141Norm : ℝ)
    ((κ : ℂ) *
          (((1 / (2 * Real.pi) : ℝ) : ℂ) *
            (∫ t : ℝ, (L : ℂ) * (F (l t) * (Real.exp x : ℂ) ^ l t)))).re =
      (2 * Real.log n) * (κ * Real.exp (-a * (x + b))) *
        (middleK141Profile.map (Rat.castHom ℝ)).eval (x + b) := by
  have hd : 2 * middleK141Kernel.natDegree + 3 ≤ 31 :=
    Nat.add_le_add_right (Nat.mul_le_mul_left 2 middle_k141_kernel_degree) 3
  have h :=
    middle_pair_conductor middleK141Kernel hd (a := (2 : ℝ)) (b := 7 / 2) (by norm_num only)
      (by norm_num only) hx (middleK141Norm : ℝ) hn
  rw [← middle_k141_profile_eq_pole] at h
  simpa only [Polynomial.eval₂_eq_eval_map] using h

/-- The three pair conductors charge the physical K156 profile at log cutoff.
This evaluation uses the same left contour and normalization as the Gamma budget. -/
public theorem middle_k156_pair_conductor {x : ℝ} (hx : 0 ≤ x) {n p q r : ℕ} [NeZero p] [NeZero q]
    [NeZero r] (hn : n = p * q * r) :
    let a : ℝ := 49 / 20
    let b : ℝ := 7 / 2
    let ha : 1 / 2 < a := by norm_num only [a]
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let F := fun s ↦
      ∑ i ∈ Finset.Ico 3 52,
        ((middleK156Kernel ^ 2).coeff (51 - i) : ℂ) *
          (LLS.PaperStatements.shiftedPoleKernel (max 1 i) a b (le_max_left _ _) ha).function s
    let L := Real.log (p * q : ℕ) + Real.log (p * r : ℕ) + Real.log (q * r : ℕ)
    let κ := (middleK156Norm : ℝ)
    ((κ : ℂ) *
          (((1 / (2 * Real.pi) : ℝ) : ℂ) *
            (∫ t : ℝ, (L : ℂ) * (F (l t) * (Real.exp x : ℂ) ^ l t)))).re =
      (2 * Real.log n) * (κ * Real.exp (-a * (x + b))) *
        (middleK156Profile.map (Rat.castHom ℝ)).eval (x + b) := by
  have hd : 2 * middleK156Kernel.natDegree + 3 ≤ 51 :=
    Nat.add_le_add_right (Nat.mul_le_mul_left 2 middle_k156_kernel_degree) 3
  have h :=
    middle_pair_conductor middleK156Kernel hd (a := (49 / 20 : ℝ)) (b := 7 / 2) (by norm_num only)
      (by norm_num only) hx (middleK156Norm : ℝ) hn
  rw [← middle_k156_profile_eq_pole] at h
  simpa only [Polynomial.eval₂_eq_eval_map] using h

end PseudoPrime.PrimeTestBounds.MillerRabin
