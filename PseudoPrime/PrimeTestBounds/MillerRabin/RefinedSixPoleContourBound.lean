/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPolePhaseBound
public import PseudoPrime.LLS.PaperStatements.MellinKernelExplicitFormula

/-! Contour formula and three-character arithmetic bound for the refined kernel. -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The pole residue and the two contour integrals on the fixed lines ±9/16. -/
noncomputable def refinedContourRemainder {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) :
    ℂ :=
  let W := fun s : ℂ ↦ refinedSixPoleKernel.function s * (x : ℂ) ^ s
  LLS.PaperStatements.MellinKernel.weightedResidue refinedSixPoleKernel
      (fun z : ℂ ↦ χ.completedLFunction (z + 1 / 2)) x (-1 / 2) +
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ,
        -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
          W (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) +
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ,
        logDeriv χ.gammaFactor ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
          W (((9 / 16 : ℝ) : ℂ) + Complex.I * t))

/-- Under GRH, the refined arithmetic sum equals the contour remainder minus its zero sum. -/
theorem refined_contour_formula {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    (∑' n : ℕ, refinedSixPoleKernel.summand χ x n) =
      refinedContourRemainder χ x - ∑' ρ : ℂ, refinedSixPoleKernel.oscillatingZeroTerm χ x ρ := by
  have hd : refinedSixPoleKernel.delta = (1 / 8 : ℝ) := by
    norm_num only [refinedSixPoleKernel, LLS.PaperStatements.rationalPoleMellinKernel]
    apply min_eq_right
    norm_num only
  have h :=
    LLS.PaperStatements.MellinKernel.tsum_summand_eq_completed_residue_formula refinedSixPoleKernel
      hq hGRH hp hne hinv (a := (-9 / 16 : ℝ)) (b := 9 / 16) (by norm_num only)
      (by
        rw [hd]; norm_num only)
      (by
        rw [hd]; norm_num only)
      (by norm_num only) (by norm_num only) hx (by norm_num only) (by norm_num only)
  dsimp only [refinedContourRemainder] at *
  linear_combination h

/-- Under GRH, bound three arithmetic sums using their actual contour remainders
and certified mass. -/
theorem refined_three_summand_upper {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hpA : a.IsPrimitive) (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1)
    (hnC : c ≠ 1) (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) (heA : a.Even) (heB : b.Even)
    (heC : c.Even) {X : ℝ} (hX : 1000 ≤ X) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) {x : ℝ} (hx : 1 ≤ x) :
    (∑' n : ℕ, refinedSixPoleKernel.summand a x n).re +
        (∑' n : ℕ, refinedSixPoleKernel.summand b x n).re +
        (∑' n : ℕ, refinedSixPoleKernel.summand c x n).re <
      (refinedContourRemainder a x).re + (refinedContourRemainder b x).re +
          (refinedContourRemainder c x).re +
          (3 / 16 : ℝ) * (Real.log p + Real.log q + Real.log r) -
        (6366 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 5 := by
  have hz :=
    refined_three_phase_upper hGRH a b c hP hQ hR hpA hpB hpC hnA hnB hnC hiA hiB hiC heA heB heC hX
      ht hA hB hC (zero_lt_one.trans_le hx)
  have ha := congrArg Complex.re (refined_contour_formula hP hGRH hpA hnA hiA hx)
  have hb := congrArg Complex.re (refined_contour_formula hQ hGRH hpB hnB hiB hx)
  have hc := congrArg Complex.re (refined_contour_formula hR hGRH hpC hnC hiC hx)
  simp only [Complex.sub_re] at ha hb hc
  linarith only [hz, ha, hb, hc]

end PseudoPrime.PrimeTestBounds.MillerRabin
