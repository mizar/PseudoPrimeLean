/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformMassSharp
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerTailMoments

/-! Three-character zero mass with an explicit Euler tail envelope. -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The refined Euler tail envelope at cutoff `X`, formed from the first three power-log
moment bounds. It is used in the three-character zero-mass inequality. -/
noncomputable def quarterEulerTailCap (X : ℝ) : ℝ :=
  (3 / 8 : ℝ) * quarterMomentTailCap 0 X + (81 / 200 : ℝ) * quarterMomentTailCap 1 X +
    (729 / 5000 : ℝ) * quarterMomentTailCap 2 X

/-- Under RH and prime-level triviality, the three-character zero mass is bounded by its
conductor term, the sharp Euler constant and the explicit moment-tail envelope. -/
theorem quarter_uniform_mass_tail_cap {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hRH : RiemannHypothesis) (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q)
    (c : DirichletCharacter ℂ r) (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hRA : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis a)
    (hRB : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis b)
    (hRC : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis c) (hpA : a.IsPrimitive)
    (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1) (hnC : c ≠ 1)
    (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) (heA : a.Even) (heB : b.Even) (heC : c.Even)
    {X : ℝ} (hX : 625 ≤ X) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) :
    sixMass a + sixMass b + sixMass c <
      (3 / 16 : ℝ) * (Real.log p + Real.log q + Real.log r) +
        -(3117 / 400 : ℝ) * (27 / 25 : ℝ) ^ 5 +
        4 * quarterEulerTailCap X := by
  have hm :=
    quarter_uniform_mass_sharp hRH a b c hP hQ hR hRA hRB hRC hpA hpB hpC hnA hnB hnC hiA hiB hiC
      heA heB heC (by linarith only [hX]) ht hA hB hC
  have ht' := quarter_euler_tail_moment_upper hRH hX
  dsimp only [quarterEulerTailCap]
  linarith only [hm, ht']

/-- The psi-free Euler-tail envelope is the positive linear combination of the three clean
moment-tail bounds. Its integrals admit explicit logarithmic power formulas. -/
noncomputable def quarterEulerCleanTailCap (X : ℝ) : ℝ :=
  (3 / 8 : ℝ) * quarterMomentCleanTail 0 X + (81 / 200 : ℝ) * quarterMomentCleanTail 1 X +
    (729 / 5000 : ℝ) * quarterMomentCleanTail 2 X

/-- Under RH and prime-level triviality, the three-character zero mass is bounded by the sharp
Euler constant and a psi-free tail envelope at every real cutoff at least 625. -/
theorem quarter_uniform_mass_tail_clean {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hRH : RiemannHypothesis) (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q)
    (c : DirichletCharacter ℂ r) (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hRA : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis a)
    (hRB : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis b)
    (hRC : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis c) (hpA : a.IsPrimitive)
    (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1) (hnC : c ≠ 1)
    (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) (heA : a.Even) (heB : b.Even) (heC : c.Even)
    {X : ℝ} (hX : 625 ≤ X) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) :
    sixMass a + sixMass b + sixMass c <
      (3 / 16 : ℝ) * (Real.log p + Real.log q + Real.log r) +
        -(3117 / 400 : ℝ) * (27 / 25 : ℝ) ^ 5 +
        4 * quarterEulerCleanTailCap X := by
  have hm :=
    quarter_uniform_mass_sharp hRH a b c hP hQ hR hRA hRB hRC hpA hpB hpC hnA hnB hnC hiA hiB hiC
      heA heB heC (by linarith only [hX]) ht hA hB hC
  have ht' := quarter_euler_tail_clean_upper hRH hX
  dsimp only [quarterEulerCleanTailCap]
  linarith only [hm, ht']

end PseudoPrime.PrimeTestBounds.MillerRabin
