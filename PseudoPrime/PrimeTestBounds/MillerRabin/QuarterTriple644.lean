/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEuler644
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticTripleMain

/-! # Three-character zero-mass bound for section 122 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For three characters whose real values sum to at least minus one at every
index and to three on the nonzero Mangoldt support of a finite prefix, four
times that prefix is bounded by the total refined Euler mass plus the three
signed Euler series. Nonnegative complementary terms and absolute convergence
justify retaining the full signed prefix. -/
theorem quarter_euler_prefix_644 {p q r : ℕ} (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (s : Finset ℕ)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (hp : ∀ n ∈ s, ArithmeticFunction.vonMangoldt n ≠ 0 → (a n).re + (b n).re + (c n).re = 3) :
    4 * (∑ n ∈ s, ArithmeticFunction.vonMangoldt n * quarterEulerWeight644 n) ≤
      ∑' n : ℕ,
        (ArithmeticFunction.vonMangoldt n * quarterEulerWeight644 n +
          ((a n).re * (ArithmeticFunction.vonMangoldt n * quarterEulerWeight644 n) +
            (b n).re * (ArithmeticFunction.vonMangoldt n * quarterEulerWeight644 n) +
            (c n).re * (ArithmeticFunction.vonMangoldt n * quarterEulerWeight644 n))) := by
  have hsA := quarter_signed_euler_summable_644 a
  have hsB := quarter_signed_euler_summable_644 b
  have hsC := quarter_signed_euler_summable_644 c
  have h :=
    (quarter_euler_weight_summable_644.add ((hsA.add hsB).add hsC)).sum_le_tsum s
      (fun n _ ↦ by
        have hw : 0 ≤ ArithmeticFunction.vonMangoldt n * quarterEulerWeight644 n :=
          mul_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n))
            (quarter_euler_weight_nonneg_644_all n)
        have hsign := mul_le_mul_of_nonneg_right (ht n) hw
        nlinarith only [hsign])
  have he :
    (∑ n ∈ s,
        (ArithmeticFunction.vonMangoldt n * quarterEulerWeight644 n +
          ((a n).re * (ArithmeticFunction.vonMangoldt n * quarterEulerWeight644 n) +
            (b n).re * (ArithmeticFunction.vonMangoldt n * quarterEulerWeight644 n) +
            (c n).re * (ArithmeticFunction.vonMangoldt n * quarterEulerWeight644 n)))) =
      4 * (∑ n ∈ s, ArithmeticFunction.vonMangoldt n * quarterEulerWeight644 n) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hz : ArithmeticFunction.vonMangoldt n = 0
    · simp only [hz, zero_mul, add_zero, mul_zero]
    · have hsign :=
        congrArg (fun z : ℝ ↦ z * (ArithmeticFunction.vonMangoldt n * quarterEulerWeight644 n))
          (hp n hn hz)
      nlinarith only [hsign]
  rw [he] at h
  exact h

/-- For three characters satisfying the sign and prefix hypotheses, the
fourfold finite Euler prefix is bounded by the universal series and the three
separate signed series. Absolute convergence allows the combined sum to be
split. This form connects the prefix comparison to three zero-mass formulas. -/
theorem quarter_separate_euler_644 {p q r : ℕ} (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (s : Finset ℕ)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (hp : ∀ n ∈ s, ArithmeticFunction.vonMangoldt n ≠ 0 → (a n).re + (b n).re + (c n).re = 3) :
    4 * (∑ n ∈ s, ArithmeticFunction.vonMangoldt n * quarterEulerWeight644 n) ≤
      (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * quarterEulerWeight644 n) +
        (∑' n : ℕ, (a n).re * (ArithmeticFunction.vonMangoldt n * quarterEulerWeight644 n)) +
        (∑' n : ℕ, (b n).re * (ArithmeticFunction.vonMangoldt n * quarterEulerWeight644 n)) +
        (∑' n : ℕ, (c n).re * (ArithmeticFunction.vonMangoldt n * quarterEulerWeight644 n)) := by
  have h := quarter_euler_prefix_644 a b c s ht hp
  have hA := quarter_signed_euler_summable_644 a
  have hB := quarter_signed_euler_summable_644 b
  have hC := quarter_signed_euler_summable_644 c
  rw [Summable.tsum_add quarter_euler_weight_summable_644 ((hA.add hB).add hC),
    Summable.tsum_add (hA.add hB) hC, Summable.tsum_add hA hB] at h
  linarith only [h]

/-- The normalized sixth-pole mass of the zeros of the completed L-function
of a character. Multiplicities are included via the divisor, and the kernel
norm supplies the weight. This is the zero-side quantity used in the
three-character bound under the corresponding RH assumptions. -/
noncomputable def quarterMass644 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℝ :=
  ∑' ρ : ℂ,
    (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
      ‖quarterKernel644.function (Complex.I * ρ.im)‖

/-- The sixth-pole differential operator applied to the real Gamma
logarithmic derivative at distance `107/100`. It is the unscaled Gamma term in
the exact zero-mass formula and in the three-character comparison. -/
noncomputable def quarterGamma644 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℝ :=
  let G : ℝ → ℝ := fun u ↦ (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + u : ℝ) : ℂ)).re
  3 * G (107 / 100) - (321 / 100 : ℝ) * deriv G (107 / 100) +
    (11449 / 10000 : ℝ) * deriv (deriv G) (107 / 100)

/-- Under individual RH for three primitive nonprincipal characters, their
sixth-pole zero masses satisfy an upper bound retaining a fourfold Euler
prefix. The pointwise sign and prefix hypotheses permit the signed Euler
series to be combined before applying the three exact zero formulas. This is
the zero-mass estimate needed for the refined witness inequality. -/
theorem quarter_three_mass_644 {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r)
    (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hRA : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis a)
    (hRB : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis b)
    (hRC : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis c) (hpA : a.IsPrimitive)
    (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1) (hnC : c ≠ 1)
    (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) (s : Finset ℕ)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (hs : ∀ n ∈ s, ArithmeticFunction.vonMangoldt n ≠ 0 → (a n).re + (b n).re + (c n).re = 3) :
    8 * (quarterMass644 a + quarterMass644 b + quarterMass644 c) ≤
      (3 / 2 : ℝ) * (Real.log p + Real.log q + Real.log r) +
          (quarterGamma644 a + quarterGamma644 b + quarterGamma644 c) +
          8 * (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * quarterEulerWeight644 n) -
        32 * (∑ n ∈ s, ArithmeticFunction.vonMangoldt n * quarterEulerWeight644 n) := by
  have hA := quarter_zero_euler_644 hP hRA hpA hnA hiA
  have hB := quarter_zero_euler_644 hQ hRB hpB hnB hiB
  have hC := quarter_zero_euler_644 hR hRC hpC hnC hiC
  have he := quarter_separate_euler_644 a b c s ht hs
  dsimp only [quarterMass644, quarterGamma644] at *
  linarith only [hA, hB, hC, he]

/-- If the three characters equal one on all primes through the cutoff,
the refined zero-mass bound retains every finite prefix below that cutoff.
Nonzero von Mangoldt support reduces each prefix index to a prime power, so
the prime hypotheses imply the required character values. This is the form
used when no smaller rejecting prime exists. -/
theorem quarter_mass_of_prime_one_644 {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
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
    8 * (quarterMass644 a + quarterMass644 b + quarterMass644 c) ≤
      (3 / 2 : ℝ) * (Real.log p + Real.log q + Real.log r) +
          (quarterGamma644 a + quarterGamma644 b + quarterGamma644 c) +
          8 * (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * quarterEulerWeight644 n) -
        32 * (∑ n ∈ s, ArithmeticFunction.vonMangoldt n * quarterEulerWeight644 n) := by
  apply quarter_three_mass_644 a b c hP hQ hR hRA hRB hRC hpA hpB hpC hnA hnB hnC hiA hiB hiC s ht
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

/-- The three signed Euler contributions equal three copies of the universal
Euler mass less a single sum weighted by the real trace deficit. -/
theorem quarter_trace_mass_644 {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r)
    (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hpA : a.IsPrimitive)
    (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1) (hnC : c ≠ 1) :
    let W := fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * quarterEulerWeight644 n
    quarterMass644 a + quarterMass644 b + quarterMass644 c =
      3 / 16 * (Real.log p + Real.log q + Real.log r) +
            (quarterGamma644 a + quarterGamma644 b + quarterGamma644 c) / 8 -
          3 * (∑' n, W n) +
        ∑' n : ℕ, (3 - ((a n).re + (b n).re + (c n).re)) * W n := by
  intro W
  have ha := quarter_zero_euler_644 hP (hG _ a hpA) hpA hnA (inv_ne_one.mpr hnA)
  have hb := quarter_zero_euler_644 hQ (hG _ b hpB) hpB hnB (inv_ne_one.mpr hnB)
  have hc := quarter_zero_euler_644 hR (hG _ c hpC) hpC hnC (inv_ne_one.mpr hnC)
  have hW : Summable W := quarter_euler_weight_summable_644
  have hA := quarter_signed_euler_summable_644 a
  have hB := quarter_signed_euler_summable_644 b
  have hC := quarter_signed_euler_summable_644 c
  have he :
    ∀ n : ℕ,
      (3 - ((a n).re + (b n).re + (c n).re)) * W n =
        3 * W n - (((a n).re * W n + (b n).re * W n) + (c n).re * W n) := by
    intro n
    ring
  simp_rw [he]
  rw [Summable.tsum_sub (hW.mul_left 3) ((hA.add hB).add hC), Summable.tsum_add (hA.add hB) hC,
    Summable.tsum_add hA hB, tsum_mul_left]
  dsimp only [W, quarterMass644, quarterGamma644] at ha hb hc ⊢
  linarith only [ha, hb, hc]

end PseudoPrime.PrimeTestBounds.MillerRabin
