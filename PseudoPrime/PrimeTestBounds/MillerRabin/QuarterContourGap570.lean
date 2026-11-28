/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrimeContour570
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterRadiusGap570
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSquareGain570

/-! # Gamma integral required by the section 31 counterexample hypotheses -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- If three primitive even characters have trace at least minus one and are all one on
the primes up to the square cutoff, their common Gamma integral exceeds 0.002. Compare
the contour bound with the strengthened finite square gain throughout the radius interval. -/
theorem even_gamma_positive_570 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s) (hP : 2 ≤ p) (hQ : 2 ≤ q) (hS : 2 ≤ s)
    (pa : a.IsPrimitive) (pb : b.IsPrimitive) (pc : c.IsPrimitive) (na : a ≠ 1) (nb : b ≠ 1)
    (nc : c ≠ 1) (ia : a⁻¹ ≠ 1) (ib : b⁻¹ ≠ 1) (ic : c⁻¹ ≠ 1) {r : ℝ} (hl : 278 ≤ r) (hu : r ≤ 285)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1)
    (hlog : Real.log p + Real.log q + Real.log s ≤ 4 * r) (ea : a.Even) (eb : b.Even)
    (ec : c.Even) : 2 / 1000 < (reflectedArch570 a⁻¹ (r ^ 2) + rightGamma570 a (r ^ 2)).re := by
  have hlo := quarter_square_gain_strong_570 a b c hl hu hG.riemann ht hA hB hC
  have hhi :=
    triple_explicit_upper_570 hG a b c hP hQ hS pa pb pc na nb nc ia ib ic hl hu ht hA hB hC hlog ea
      eb ec
  have ht' := radius_tail_numeric hl hu
  have hc := conductor_radius_upper_570 hl
  have hr : 0 < r := by linarith only [hl]
  rw [quarterKernel570,
    LLS.PaperStatements.rationalPole_transform _ _ _ _ (one_div_pos.mpr (sq_pos_of_pos hr)),
    Complex.ofReal_re, one_div] at hc
  dsimp only at hhi
  linarith only [hlo, hhi, ht', hc, hu]

end PseudoPrime.PrimeTestBounds.MillerRabin
