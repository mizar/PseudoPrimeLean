/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianThreeEulerMass
public import PseudoPrime.LLS.GaussianPrefixSurplus

/-! Certified Gaussian three-character mass at cutoff 50000. -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH and the prefix hypotheses, insert the certified 50000-term Euler gain. -/
theorem gaussian_three_mass_50000 {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hpA : a.IsPrimitive) (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1)
    (hnC : c ≠ 1) (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) (heA : a.Even) (heB : b.Even)
    (heC : c.Even) {X : ℝ} (hX : 50000 ≤ X) (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) :
    gaussianActualZeroMass a + gaussianActualZeroMass b + gaussianActualZeroMass c <
      (20115621 / 50000000 : ℝ) * (Real.log p + Real.log q + Real.log r) + 683 / 50 - 108 / 25 -
        4 * (1129059 / 200000 : ℝ) := by
  let s := Finset.Ioc 0 50000
  have hpref :
    ∀ n ∈ s,
      Analysis.gaussianResolventMangoldtWeight n ≠ 0 → (a n).re + (b n).re + (c n).re = 3 := by
    intro n hn hw
    have hΛ : ArithmeticFunction.vonMangoldt n ≠ 0 := by
      intro hz
      apply hw
      simp only [Analysis.gaussianResolventMangoldtWeight, hz, zero_mul]
    have hn' : (n : ℝ) ≤ X := by
      have hn50000 : n ≤ 50000 := (Finset.mem_Ioc.mp hn).2
      exact (show (n : ℝ) ≤ 50000 by exact_mod_cast hn50000).trans hX
    have ha :=
      AnalyticNumberTheory.Arithmetic.character_eq_one_of_ambient_mangoldt (N := 1) a
        (fun l hl hlX _ ↦ hA l hl hlX) hn' (Nat.coprime_one_right n) hΛ
    have hb :=
      AnalyticNumberTheory.Arithmetic.character_eq_one_of_ambient_mangoldt (N := 1) b
        (fun l hl hlX _ ↦ hB l hl hlX) hn' (Nat.coprime_one_right n) hΛ
    have hc :=
      AnalyticNumberTheory.Arithmetic.character_eq_one_of_ambient_mangoldt (N := 1) c
        (fun l hl hlX _ ↦ hC l hl hlX) hn' (Nat.coprime_one_right n) hΛ
    rw [ha, hb, hc, Complex.one_re]
    norm_num only
  have hm :=
    gaussian_three_mass_even hGRH a b c hP hQ hR hpA hpB hpC hnA hnB hnC hiA hiB hiC heA heB heC s
      ht hpref
  have hl := LLS.gaussian_prefix50000_surplus hGRH.riemann (le_refl (50000 : ℝ))
  norm_num only [Nat.floor_ofNat] at hl
  dsimp only [s] at hm
  linarith only [hm, hl]

end PseudoPrime.PrimeTestBounds.MillerRabin
