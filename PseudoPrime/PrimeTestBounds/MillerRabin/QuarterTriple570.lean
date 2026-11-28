/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEuler570
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerBoundary570
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticTripleMain

/-! # Three-character zero-mass bound for section 31 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For three characters whose real values sum to at least minus one at every
index and to three on the nonzero Mangoldt support of a finite prefix, four
times that prefix is bounded by the total refined Euler mass plus the three
signed Euler series. Nonnegative complementary terms and absolute convergence
justify retaining the full signed prefix. -/
theorem quarter_euler_prefix_570 {p q r : ℕ} (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (s : Finset ℕ)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (hp : ∀ n ∈ s, ArithmeticFunction.vonMangoldt n ≠ 0 → (a n).re + (b n).re + (c n).re = 3) :
    4 * (∑ n ∈ s, ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n) ≤
      ∑' n : ℕ,
        (ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n +
          ((a n).re * (ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n) +
            (b n).re * (ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n) +
            (c n).re * (ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n))) := by
  have hsA := quarter_signed_euler_summable_570 a
  have hsB := quarter_signed_euler_summable_570 b
  have hsC := quarter_signed_euler_summable_570 c
  have h :=
    (quarter_euler_weight_summable_570.add ((hsA.add hsB).add hsC)).sum_le_tsum s
      (fun n _ ↦ by
        have hw : 0 ≤ ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n :=
          mul_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n))
            (quarter_euler_weight_nonneg_570_all n)
        have hsign := mul_le_mul_of_nonneg_right (ht n) hw
        nlinarith only [hsign])
  have he :
    (∑ n ∈ s,
        (ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n +
          ((a n).re * (ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n) +
            (b n).re * (ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n) +
            (c n).re * (ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n)))) =
      4 * (∑ n ∈ s, ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hz : ArithmeticFunction.vonMangoldt n = 0
    · simp only [hz, zero_mul, add_zero, mul_zero]
    · have hsign :=
        congrArg (fun z : ℝ ↦ z * (ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n))
          (hp n hn hz)
      nlinarith only [hsign]
  rw [he] at h
  exact h

/-- For three characters satisfying the sign and prefix hypotheses, the
fourfold finite Euler prefix is bounded by the universal series and the three
separate signed series. Absolute convergence allows the combined sum to be
split. This form connects the prefix comparison to three zero-mass formulas. -/
theorem quarter_separate_euler_570 {p q r : ℕ} (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (s : Finset ℕ)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (hp : ∀ n ∈ s, ArithmeticFunction.vonMangoldt n ≠ 0 → (a n).re + (b n).re + (c n).re = 3) :
    4 * (∑ n ∈ s, ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n) ≤
      (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n) +
        (∑' n : ℕ, (a n).re * (ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n)) +
        (∑' n : ℕ, (b n).re * (ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n)) +
        (∑' n : ℕ, (c n).re * (ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n)) := by
  have h := quarter_euler_prefix_570 a b c s ht hp
  have hA := quarter_signed_euler_summable_570 a
  have hB := quarter_signed_euler_summable_570 b
  have hC := quarter_signed_euler_summable_570 c
  rw [Summable.tsum_add quarter_euler_weight_summable_570 ((hA.add hB).add hC),
    Summable.tsum_add (hA.add hB) hC, Summable.tsum_add hA hB] at h
  linarith only [h]

/-- The normalized sixth-pole mass of the zeros of the completed L-function
of a character. Multiplicities are included via the divisor, and the kernel
norm supplies the weight. This is the zero-side quantity used in the
three-character bound under the corresponding RH assumptions. -/
noncomputable def quarterMass570 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℝ :=
  ∑' ρ : ℂ,
    (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
      ‖quarterKernel570.function (Complex.I * ρ.im)‖

/-- The sixth-pole differential operator applied to the real Gamma
logarithmic derivative at distance `51/50`. It is the unscaled Gamma term in
the exact zero-mass formula and in the three-character comparison. -/
noncomputable def quarterGamma570 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℝ :=
  let G : ℝ → ℝ := fun u ↦ (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + u : ℝ) : ℂ)).re
  3 * G (51 / 50) - (153 / 50 : ℝ) * deriv G (51 / 50) +
    (2601 / 2500 : ℝ) * deriv (deriv G) (51 / 50)

/-- Under individual RH for three primitive nonprincipal characters, their
sixth-pole zero masses satisfy an upper bound retaining a fourfold Euler
prefix. The pointwise sign and prefix hypotheses permit the signed Euler
series to be combined before applying the three exact zero formulas. This is
the zero-mass estimate needed for the refined witness inequality. -/
theorem quarter_three_mass_570 {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r)
    (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hRA : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis a)
    (hRB : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis b)
    (hRC : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis c) (hpA : a.IsPrimitive)
    (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1) (hnC : c ≠ 1)
    (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) (s : Finset ℕ)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (hs : ∀ n ∈ s, ArithmeticFunction.vonMangoldt n ≠ 0 → (a n).re + (b n).re + (c n).re = 3) :
    8 * (quarterMass570 a + quarterMass570 b + quarterMass570 c) ≤
      (3 / 2 : ℝ) * (Real.log p + Real.log q + Real.log r) +
          (quarterGamma570 a + quarterGamma570 b + quarterGamma570 c) +
          8 * (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n) -
        32 * (∑ n ∈ s, ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n) := by
  have hA := quarter_zero_euler_570 hP hRA hpA hnA hiA
  have hB := quarter_zero_euler_570 hQ hRB hpB hnB hiB
  have hC := quarter_zero_euler_570 hR hRC hpC hnC hiC
  have he := quarter_separate_euler_570 a b c s ht hs
  dsimp only [quarterMass570, quarterGamma570] at *
  linarith only [hA, hB, hC, he]

/-- If the three characters equal one on all primes through the cutoff,
the refined zero-mass bound retains every finite prefix below that cutoff.
Nonzero von Mangoldt support reduces each prefix index to a prime power, so
the prime hypotheses imply the required character values. This is the form
used when no smaller rejecting prime exists. -/
theorem quarter_mass_of_prime_one_570 {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
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
    8 * (quarterMass570 a + quarterMass570 b + quarterMass570 c) ≤
      (3 / 2 : ℝ) * (Real.log p + Real.log q + Real.log r) +
          (quarterGamma570 a + quarterGamma570 b + quarterGamma570 c) +
          8 * (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n) -
        32 * (∑ n ∈ s, ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n) := by
  apply quarter_three_mass_570 a b c hP hQ hR hRA hRB hRC hpA hpB hpC hnA hnB hnC hiA hiB hiC s ht
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

/-- For a prime prefix, a total Euler lower bound of 3.7275 and an average
normalized Gamma upper bound of -0.7345 yield the section 31 saving of 13.386.
The remaining Euler tail has coefficient four. -/
theorem quarter_mass_tail_570 {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r)
    (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hRA : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis a)
    (hRB : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis b)
    (hRC : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis c) (hpA : a.IsPrimitive)
    (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1) (hnC : c ≠ 1)
    (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) {X : ℝ} (s : Finset ℕ)
    (hS : ∀ k ∈ s, (k : ℝ) ≤ X) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) {R T : ℝ}
    (hlog : Real.log p + Real.log q + Real.log r ≤ 4 * R)
    (hg : quarterGamma570 a + quarterGamma570 b + quarterGamma570 c ≤ -24 * (7345 / 10000))
    (hw : 37275 / 10000 ≤ ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n)
    (htail :
      (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n) -
          (∑ n ∈ s, ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n) ≤
        T) :
    quarterMass570 a + quarterMass570 b + quarterMass570 c ≤ 3 / 4 * R - 13386 / 1000 + 4 * T := by
  have hm :=
    quarter_mass_of_prime_one_570 a b c hP hQ hR hRA hRB hRC hpA hpB hpC hnA hnB hnC hiA hiB hiC s
      hS ht hA hB hC
  linarith only [hm, hlog, hg, hw, htail]

/-- Under RH the Euler lower bound needed for the three-character mass gap follows from
the certified finite interval. The gamma bound and complementary tail estimate then give
the section 31 mass upper bound under the stated character and conductor hypotheses. -/
theorem quarter_mass_gap_570 {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r)
    (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hRA : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis a)
    (hRB : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis b)
    (hRC : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis c) (hpA : a.IsPrimitive)
    (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1) (hnC : c ≠ 1)
    (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) {X : ℝ} (s : Finset ℕ)
    (hS : ∀ k ∈ s, (k : ℝ) ≤ X) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) {R T : ℝ}
    (hlog : Real.log p + Real.log q + Real.log r ≤ 4 * R) (hRH : RiemannHypothesis)
    (hg : quarterGamma570 a + quarterGamma570 b + quarterGamma570 c ≤ -24 * (7345 / 10000))
    (htail :
      (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n) -
          (∑ n ∈ s, ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n) ≤
        T) :
    quarterMass570 a + quarterMass570 b + quarterMass570 c ≤ 3 / 4 * R - 13386 / 1000 + 4 * T := by
  exact
    quarter_mass_tail_570 a b c hP hQ hR hRA hRB hRC hpA hpB hpC hnA hnB hnC hiA hiB hiC s hS ht hA
      hB hC hlog hg (euler570_total_lower hRH) htail

end PseudoPrime.PrimeTestBounds.MillerRabin
