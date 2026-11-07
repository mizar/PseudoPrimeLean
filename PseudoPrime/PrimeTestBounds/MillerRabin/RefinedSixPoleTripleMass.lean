/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleZeroEuler
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleEulerTriple

/-! # Three-character refined zero-mass bound -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For three characters satisfying the sign and prefix hypotheses, the
fourfold finite Euler prefix is bounded by the universal series and the three
separate signed series. Absolute convergence allows the combined sum to be
split. This form connects the prefix comparison to three zero-mass formulas. -/
theorem refined_three_euler_separate {p q r : ℕ} (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (s : Finset ℕ)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (hp : ∀ n ∈ s, ArithmeticFunction.vonMangoldt n ≠ 0 → (a n).re + (b n).re + (c n).re = 3) :
    4 * (∑ n ∈ s, ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n) ≤
      (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n) +
        (∑' n : ℕ, (a n).re * (ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n)) +
        (∑' n : ℕ, (b n).re * (ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n)) +
        (∑' n : ℕ, (c n).re * (ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n)) := by
  have h := refined_six_euler_three_prefix a b c s ht hp
  have hA := refined_six_euler_signed_summable a
  have hB := refined_six_euler_signed_summable b
  have hC := refined_six_euler_signed_summable c
  rw [Summable.tsum_add refined_six_euler_weight_summable ((hA.add hB).add hC),
    Summable.tsum_add (hA.add hB) hC, Summable.tsum_add hA hB] at h
  linarith only [h]

/-- The normalized sixth-pole mass of the zeros of the completed L-function
of a character. Multiplicities are included via the divisor, and the kernel
norm supplies the weight. This is the zero-side quantity used in the
three-character bound under the corresponding RH assumptions. -/
noncomputable def sixMass {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℝ :=
  ∑' ρ : ℂ,
    (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
      ‖refinedSixPoleKernel.function (Complex.I * ρ.im)‖

/-- The sixth-pole differential operator applied to the real Gamma
logarithmic derivative at distance `27/25`. It is the unscaled Gamma term in
the exact zero-mass formula and in the three-character comparison. -/
noncomputable def sixGamma {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℝ :=
  let G : ℝ → ℝ := fun u ↦ (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + u : ℝ) : ℂ)).re
  3 * G (27 / 25) - (81 / 25 : ℝ) * deriv G (27 / 25) + (729 / 625 : ℝ) * deriv (deriv G) (27 / 25)

/-- Under individual RH for three primitive nonprincipal characters, their
sixth-pole zero masses satisfy an upper bound retaining a fourfold Euler
prefix. The pointwise sign and prefix hypotheses permit the signed Euler
series to be combined before applying the three exact zero formulas. This is
the zero-mass estimate needed for the refined witness inequality. -/
theorem refined_three_mass {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r] (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hRA : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis a)
    (hRB : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis b)
    (hRC : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis c) (hpA : a.IsPrimitive)
    (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1) (hnC : c ≠ 1)
    (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) (s : Finset ℕ)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (hs : ∀ n ∈ s, ArithmeticFunction.vonMangoldt n ≠ 0 → (a n).re + (b n).re + (c n).re = 3) :
    8 * (sixMass a + sixMass b + sixMass c) ≤
      (3 / 2 : ℝ) * (Real.log p + Real.log q + Real.log r) +
          (sixGamma a + sixGamma b + sixGamma c) +
          8 * (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n) -
        32 * (∑ n ∈ s, ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n) := by
  have hA := refined_six_pole_formula_euler hP hRA hpA hnA hiA
  have hB := refined_six_pole_formula_euler hQ hRB hpB hnB hiB
  have hC := refined_six_pole_formula_euler hR hRC hpC hnC hiC
  have he := refined_three_euler_separate a b c s ht hs
  dsimp only [sixMass, sixGamma] at *
  linarith only [hA, hB, hC, he]

/-- If the three characters equal one on all primes through the cutoff,
the refined zero-mass bound retains every finite prefix below that cutoff.
Nonzero von Mangoldt support reduces each prefix index to a prime power, so
the prime hypotheses imply the required character values. This is the form
used when no smaller rejecting prime exists. -/
theorem refined_three_mass_of_prime_one {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r)
    (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hRA : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis a)
    (hRB : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis b)
    (hRC : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis c) (hpA : a.IsPrimitive)
    (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1) (hnC : c ≠ 1)
    (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) {X : ℝ} (s : Finset ℕ)
    (hS : ∀ k ∈ s, (k : ℝ) ≤ X) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) :
    8 * (sixMass a + sixMass b + sixMass c) ≤
      (3 / 2 : ℝ) * (Real.log p + Real.log q + Real.log r) +
          (sixGamma a + sixGamma b + sixGamma c) +
          8 * (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n) -
        32 * (∑ n ∈ s, ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n) := by
  apply refined_three_mass a b c hP hQ hR hRA hRB hRC hpA hpB hpC hnA hnB hnC hiA hiB hiC s ht
  intro k hk hΛ
  have h1 :=
    AnalyticNumberTheory.Arithmetic.character_eq_one_of_ambient_mangoldt (N := 1) a
      (fun l hl hlX _ ↦ hA l hl hlX) (hS k hk) (Nat.coprime_one_right k) hΛ
  have h2 :=
    AnalyticNumberTheory.Arithmetic.character_eq_one_of_ambient_mangoldt (N := 1) b
      (fun l hl hlX _ ↦ hB l hl hlX) (hS k hk) (Nat.coprime_one_right k) hΛ
  have h3 :=
    AnalyticNumberTheory.Arithmetic.character_eq_one_of_ambient_mangoldt (N := 1) c
      (fun l hl hlX _ ↦ hC l hl hlX) (hS k hk) (Nat.coprime_one_right k) hΛ
  rw [h1, h2, h3, Complex.one_re]
  norm_num only

/-- Given explicit Gamma, universal Euler and finite-prefix bounds, the
three-character zero-mass estimate has the numerical correction `6.366`
after accounting for the kernel normalization. The hypotheses isolate the
remaining numerical certificates needed for the high-range witness bound. -/
theorem refined_three_mass_numeric {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r)
    (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hRA : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis a)
    (hRB : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis b)
    (hRC : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis c) (hpA : a.IsPrimitive)
    (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1) (hnC : c ≠ 1)
    (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) {X : ℝ} (s : Finset ℕ)
    (hS : ∀ k ∈ s, (k : ℝ) ≤ X) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1)
    (hΓ : sixGamma a + sixGamma b + sixGamma c ≤ -(54 / 5 : ℝ) * (27 / 25 : ℝ) ^ 5)
    (hE :
      (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n) <
        (53 / 25 : ℝ) * (27 / 25 : ℝ) ^ 5)
    (hprefix :
      (223 / 125 : ℝ) * (27 / 25 : ℝ) ^ 5 <
        ∑ n ∈ s, ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n) :
    sixMass a + sixMass b + sixMass c <
      (3 / 16 : ℝ) * (Real.log p + Real.log q + Real.log r) -
        (6366 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 5 := by
  have h :=
    refined_three_mass_of_prime_one a b c hP hQ hR hRA hRB hRC hpA hpB hpC hnA hnB hnC hiA hiB hiC s
      hS ht hA hB hC
  linarith only [h, hΓ, hE, hprefix]

end PseudoPrime.PrimeTestBounds.MillerRabin
