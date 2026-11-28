/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.ShiftedPoleArithmetic
public import PseudoPrime.LLS.PaperStatements.MellinKernelSignedFormula
import all PseudoPrime.LLS.PaperStatements.ShiftedPoleKernel

/-! # Explicit formula for the logarithmic polynomial of shifted poles -/

namespace PseudoPrime.LLS.PaperStatements

/-- Shifted poles with the same location have the same admissible strip width,
regardless of their order and modulation. -/
public theorem shiftedPoleKernel_delta (n : ℕ) (ρ b : ℝ) (hn : 1 ≤ n) (hρ : 1 / 2 < ρ) :
    (shiftedPoleKernel n ρ b hn hρ).delta = min ((ρ - 1 / 2) / 4) (1 / 8) := by rfl

/-- The shift kernel is regular at minus one half, so its regularized
value and the corresponding weighted residue both vanish. -/
public theorem shiftedPole_weightedResidue_zero (n : ℕ) (ρ b : ℝ) (hn : 1 ≤ n) (hρ : 1 / 2 < ρ)
    (F : ℂ → ℂ) (x : ℝ) : (shiftedPoleKernel n ρ b hn hρ).weightedResidue F x (-1 / 2) = 0 := by
  simp only [MellinKernel.weightedResidue, ite_true, shiftedPoleKernel, neg_div, neg_add_cancel,
    zero_mul, mul_zero]

/-- Apply the signed contour formula directly to the finite Mangoldt sum of the
shifted logarithmic polynomial. Choose a common contour strictly inside the
admissible strip of every component. -/
public theorem shiftedPole_polynomial_contours {ι : Type*} (s : Finset ι) (k : ι → ℕ) (c : ι → ℂ)
    (hk : ∀ i, 1 ≤ k i) {ρ b x : ℝ} (hρ : 1 / 2 < ρ) (hx : 1 ≤ x) {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    let K := fun i ↦ shiftedPoleKernel (k i) ρ b (hk i) hρ
    let d := min ((ρ - 1 / 2) / 4) (1 / 8)
    let a := -1 / 2 - d / 2
    let t := 1 / 2 + d / 2
    let W := fun i (z : ℂ) ↦ (K i).function z * (x : ℂ) ^ z
    (∑ n ∈ Finset.Ioc 0 ⌊x * Real.exp b⌋₊,
        ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * χ n *
          ((((n : ℝ) / x * Real.exp (-b)) ^ ρ : ℝ) : ℂ) *
          shiftedPolePolynomial s k c (b - Real.log ((n : ℝ) / x))) =
      (∑ i ∈ s,
            c i *
              MellinKernel.weightedResidue (K i) (fun z : ℂ ↦ χ.completedLFunction (z + 1 / 2)) x
                (-1 / 2)) -
          (∑' γ : ℂ, ∑ i ∈ s, c i * (K i).oscillatingZeroTerm χ x γ) +
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ v : ℝ,
            ∑ i ∈ s,
              c i *
                (-logDeriv χ.completedLFunction (((a : ℂ) + Complex.I * v) + 1 / 2) *
                  W i ((a : ℂ) + Complex.I * v))) +
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ v : ℝ,
            ∑ i ∈ s,
              c i *
                (logDeriv χ.gammaFactor (((t : ℂ) + Complex.I * v) + 1 / 2) *
                  W i ((t : ℂ) + Complex.I * v))) := by
  intro K d a t W
  have hd : 0 < d := lt_min (by linarith only [hρ]) (by norm_num only)
  have hupper : d ≤ 1 / 8 := min_le_right _ _
  have hwidth (i : ι) : (K i).delta = d := shiftedPoleKernel_delta _ _ _ _ _
  rw [← shiftedPole_summand_tsum s k c hk hρ (zero_lt_one.trans_le hx) χ]
  exact
    MellinKernel.tsum_signed_kernel_contours s K c hq hGRH hp hne hinv
      (by
        dsimp only [a, t]; linarith only [hd])
      (fun i _ ↦ by
        rw [hwidth]; dsimp only [a]; linarith only [hd])
      (fun i _ ↦ by
        rw [hwidth]; dsimp only [t]; linarith only [hd])
      (by
        dsimp only [a]; linarith only [hupper])
      (by
        dsimp only [t]; linarith only [hupper])
      hx
      (by
        dsimp only [a]; linarith only [hd])
      (by
        dsimp only [t]; linarith only [hd])

end PseudoPrime.LLS.PaperStatements
