/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianCenteredSeries
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighCompressedMoment
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighWitness

/-! # Principal and reflected error for high Gaussian kernels -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH and above the profile cutoff, bound the centered principal
error together with all three reflected character integrals. The signed
moments share one H30 correction, and the finite H27 terms remain explicit. -/
theorem high_principal_reflected_error_le (K : HighGaussianKernel) (hRH : RiemannHypothesis)
    {q₁ q₂ q₃ : ℕ} [NeZero q₁] [NeZero q₂] [NeZero q₃] (a : DirichletCharacter ℂ q₁)
    (b : DirichletCharacter ℂ q₂) (c : DirichletCharacter ℂ q₃) {X : ℝ} (hX : 1 ≤ X)
    (hz : (profileCorrectionStart K : ℝ) ≤ 5 + Real.log X) :
    let p := (K.pole : ℝ)
    let d := p - 1 / 2
    let σ := p + 1 / 2
    let B := K.realProfile
    let D :=
      Polynomial.C (d ^ 2) * B - Polynomial.C (2 * d) * B.derivative + B.derivative.derivative
    let W := fun u : ℝ ↦ u ^ d * B.eval (5 - Real.log u)
    let F := fun u : ℝ ↦ u * deriv W u
    let ℓ := Real.log X
    let z := 5 + ℓ
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let r := fun t : ℝ ↦ ((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)
    let J := fun L : ℂ → ℂ ↦
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ, -logDeriv L (r t) * (highGaussianSquare K (l t) * (X : ℂ) ^ l t))
    let M := fun j ↦ highSignedMoment K j z
    |Real.exp (-(5 * p)) *
            (principalErrorFunctional (deriv F) gaussianLogZetaError (F 1) X (Real.exp 5) /
              Real.sqrt X)| +
        |(J a.LFunction + J b.LFunction + J c.LFunction).re| ≤
      97 / 4000 +
        Real.exp (-(5 * p)) *
          (5 / 4 * Real.exp (-(5 / 2 : ℝ) * ℓ) * Real.exp ((d - 2) * 5) *
              (∫ t in (0 : ℝ)..z, Real.exp (-(d - 2) * t) * |D.eval t|) +
            5 / 3 * |F 1| * Real.exp (-(5 / 2 : ℝ) * ℓ)) +
        Real.exp (-p * z) * (51 / 10 * (d ^ 2 * M 0 + 2 * d * M 1 + M 2) + 6 * (σ * M 0 + M 1)) +
        Real.exp (-z / 2) * highH30Charge K := by
  intro p d σ B D W F ℓ z l r J M
  have hP := high_principal_error_le_moments K hRH hX
  rw [high_remainder_rat_poly_map] at hP
  have hR := high_principal_reflected_charge_le K a b c hX hz
  have hdecay : Real.exp (-(5 * p)) * Real.exp (-(d + 1 / 2) * ℓ) = Real.exp (-p * z) := by
    rw [← Real.exp_add]
    congr 1
    dsimp only [d, z]
    ring
  have hscale (I A B : ℝ) :
    Real.exp (-(5 * p)) * (51 / 10 * Real.exp (-(d + 1 / 2) * ℓ) * I + A + B) =
      51 / 10 * Real.exp (-p * z) * I + Real.exp (-(5 * p)) * (A + B) := by
    rw [← hdecay]
    ring
  dsimp only at hP hR
  rw [hscale] at hP
  dsimp only [p, d, σ, B, D, W, F, ℓ, z, l, r, J, M] at hP hR ⊢
  linarith only [hP, hR]

/-- The three verified compressed partitions feed rational numerical bounds
directly into the common H30 coefficient. -/
theorem high_h30_le_compressed (K : HighGaussianKernel)
    (hs : ∀ j : Fin 3, highCompressedSignCheck K j = true) (m : Fin 3 → ℚ)
    (hm : ∀ j, highCompressedMomentCharge K j ≤ m j) :
    let d := (K.pole : ℝ) - 1 / 2
    let σ := (K.pole : ℝ) + 1 / 2
    highH30Charge K ≤
      51 / 5 * (d ^ 2 * (m 0 : ℝ) + 2 * d * (m 1 : ℝ) + (m 2 : ℝ)) +
        12 * (σ * (m 0 : ℝ) + (m 1 : ℝ)) := by
  have hj (j : Fin 3) : highNegativeMoment K j ≤ (m j : ℝ) :=
    (high_compressed_moment_le K j (hs j)).trans (Rat.cast_le.mpr (hm j))
  exact high_h30_charge_le K (hj 0) (hj 1) (hj 2)

/-- Validated signs and caps for the compressed partitions imply the
concrete H30 coefficient used by the high-kernel bounds. -/
theorem high_h30_le_compressed_cap (K : HighGaussianKernel)
    (hs : ∀ j : Fin 3, highCompressedSignCheck K j = true)
    (hm : ∀ j : Fin 3, highCompressedMomentCharge K j ≤ highCompressedMomentCap K j) :
    highH30Charge K ≤
      (match K with
      | .k186 => (78548 : ℝ)
      | .k196 => 7510585) := by
  refine (high_h30_le_compressed K hs (highCompressedMomentCap K) hm).trans ?_
  cases K
  · rw [show highCompressedMomentCap .k186 (2 : Fin 3) = 1577 by decide]
    norm_num only [highCompressedMomentCap, HighGaussianKernel.pole, Rat.cast_div, Rat.cast_ofNat,
      Fin.val_zero, Fin.val_one]
  · rw [show highCompressedMomentCap .k196 (2 : Fin 3) = 149870 by decide]
    norm_num only [highCompressedMomentCap, HighGaussianKernel.pole, Rat.cast_div, Rat.cast_ofNat,
      Fin.val_zero, Fin.val_one]

end PseudoPrime.PrimeTestBounds.MillerRabin
