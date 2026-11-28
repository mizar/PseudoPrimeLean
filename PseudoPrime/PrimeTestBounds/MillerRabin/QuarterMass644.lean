/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTriple644
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterXiEuler644
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerTail644
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterZetaMass644

/-! # The section 122 mass identity and uniform zeta saving -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem quarter_even_gamma_eq {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (he : χ.Even) :
    quarterGamma644 χ = quarterXiOperator (logDeriv (1 : DirichletCharacter ℂ 1).gammaFactor) := by
  have hg : χ.gammaFactor = (1 : DirichletCharacter ℂ 1).gammaFactor := by
    funext z
    rw [he.gammaFactor_def,
      AnalyticNumberTheory.DirichletLFunction.principal_modulus_one_even.gammaFactor_def]
  unfold quarterGamma644 quarterXiOperator
  rw [hg]

/-- For three even primitive nonprincipal characters under GRH, their total
section 122 zero mass is the conductor contribution, two pole corrections
per character, three xi masses, and a single Euler trace-deficit series.
This is the analytic identity used in the signed comparison. -/
theorem quarter_even_mass_644 {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r)
    (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hRH : RiemannHypothesis)
    (hpA : a.IsPrimitive) (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1)
    (hnC : c ≠ 1) (heA : a.Even) (heB : b.Even) (heC : c.Even) :
    quarterMass644 a + quarterMass644 b + quarterMass644 c =
      3 / 16 * (Real.log p + Real.log q + Real.log r) -
          6 * (107 / 100 : ℝ) ^ 5 / ((107 / 100 : ℝ) ^ 2 - 1 / 4) ^ 3 +
        3 * (∑' ρ, ‖quarterKernel644.zetaKernelZeroTerm ρ‖) +
        ∑' n : ℕ,
          (3 - ((a n).re + (b n).re + (c n).re)) *
            (ArithmeticFunction.vonMangoldt n * quarterEulerWeight644 n) := by
  have h := quarter_trace_mass_644 a b c hP hQ hR hG hpA hpB hpC hnA hnB hnC
  dsimp only at h
  rw [quarter_even_gamma_eq heA, quarter_even_gamma_eq heB, quarter_even_gamma_eq heC] at h
  linarith only [h, quarter_xi_gamma_644 hRH]

/-- With conductor logarithms bounded by four times the radius, the
section 122 mass identity gives the uniform saving 11.7421197 after paying
for the three zeta masses. The trace-deficit series remains explicit. -/
theorem quarter_even_mass_upper_644 {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r)
    (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hRH : RiemannHypothesis)
    (hpA : a.IsPrimitive) (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1)
    (hnC : c ≠ 1) (heA : a.Even) (heB : b.Even) (heC : c.Even) {R : ℝ}
    (hlog : Real.log p + Real.log q + Real.log r ≤ 4 * R) :
    quarterMass644 a + quarterMass644 b + quarterMass644 c ≤
      3 / 4 * R - 11.7421197 +
        ∑' n : ℕ,
          (3 - ((a n).re + (b n).re + (c n).re)) *
            (ArithmeticFunction.vonMangoldt n * quarterEulerWeight644 n) := by
  have h := quarter_even_mass_644 a b c hP hQ hR hG hRH hpA hpB hpC hnA hnB hnC heA heB heC
  linarith only [h, hlog, quarter_zeta_mass_644 hRH, quarter_mass_constant_644]

/-- When every prime up to the cutoff has value one in the three even
characters and the real trace is at least minus one, the section 122 mass
is bounded by the conductor term, the fixed saving, and four times the
Euler mass outside the chosen finite prefix. -/
theorem quarter_even_prefix_mass_644 {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r)
    (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hRH : RiemannHypothesis)
    (hpA : a.IsPrimitive) (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1)
    (hnC : c ≠ 1) (heA : a.Even) (heB : b.Even) (heC : c.Even) {R X : ℝ}
    (hlog : Real.log p + Real.log q + Real.log r ≤ 4 * R) (s : Finset ℕ) (hS : ∀ k ∈ s, (k : ℝ) ≤ X)
    (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) :
    let W := fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * quarterEulerWeight644 n
    quarterMass644 a + quarterMass644 b + quarterMass644 c ≤
      3 / 4 * R - 11.7421197 + 4 * ((∑' n, W n) - ∑ n ∈ s, W n) := by
  intro W
  have h :=
    quarter_mass_of_prime_one_644 a b c hP hQ hR (hG _ a hpA) (hG _ b hpB) (hG _ c hpC) hpA hpB hpC
      hnA hnB hnC (inv_ne_one.mpr hnA) (inv_ne_one.mpr hnB) (inv_ne_one.mpr hnC) s hS ht hA hB hC
  rw [quarter_even_gamma_eq heA, quarter_even_gamma_eq heB, quarter_even_gamma_eq heC] at h
  change _ ≤ _ + _ + 8 * (∑' n, W n) - 32 * (∑ n ∈ s, W n) at h
  linarith only [h, hlog, quarter_xi_gamma_644 hRH, quarter_zeta_mass_644 hRH,
    quarter_mass_constant_644]

/-- For three even primitive nonprincipal characters satisfying the trace
and prime hypotheses at the cutoff, the section 122 mass is bounded by
the conductor, the fixed saving and the explicit centered Abel tail. -/
theorem quarter_even_cutoff_mass_644 {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r)
    (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hRH : RiemannHypothesis)
    (hpA : a.IsPrimitive) (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1)
    (hnC : c ≠ 1) (heA : a.Even) (heB : b.Even) (heC : c.Even) {R X : ℝ}
    (hlog : Real.log p + Real.log q + Real.log r ≤ 4 * R) (hlo : 2701 ≤ X) (hhi : X ≤ 1000000)
    (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) :
    quarterMass644 a + quarterMass644 b + quarterMass644 c ≤
      3 / 4 * R - 11.7421197 + 4 * positiveTail644 X := by
  have hX : 0 ≤ X := by linarith only [hlo]
  have h :=
    quarter_even_prefix_mass_644 a b c hP hQ hR hG hRH hpA hpB hpC hnA hnB hnC heA heB heC hlog
      (Finset.Ioc 0 ⌊X⌋₊) (fun _ hk ↦ (Nat.le_floor_iff hX).mp (Finset.mem_Ioc.mp hk).2) ht hA hB hC
  dsimp only at h
  linarith only [h, positive_tail_upper_644 hRH hlo hhi]

/-- Additional primes beyond the cutoff with trace three reduce the
section 122 mass bound by four times their Euler contribution. The two
finite sums are disjoint because the extra primes exceed the cutoff. -/
theorem quarter_even_extra_mass_644 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ s}
    (hp : 2 ≤ p) (hq : 2 ≤ q) (hs : 2 ≤ s)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c.Even) {R X : ℝ}
    (hlog : Real.log p + Real.log q + Real.log s ≤ 4 * R) (hlo : 2701 ≤ X) (hhi : X ≤ 1000000)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) (T : Finset ℕ)
    (hT : ∀ n ∈ T, n.Prime ∧ X < n ∧ (a n).re + (b n).re + (c n).re = 3) :
    quarterMass644 a + quarterMass644 b + quarterMass644 c ≤
      3 / 4 * R - 11.7421197 + 4 * positiveTail644 X -
        4 * ∑ n ∈ T, Real.log n * quarterEulerWeight644 n := by
  let P := Finset.Ioc 0 ⌊X⌋₊
  let W := fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * quarterEulerWeight644 n
  have hX : 0 ≤ X := by linarith only [hlo]
  have hbase {d : ℕ} (χ : DirichletCharacter ℂ d) (hχ : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → χ l = 1)
    (n : ℕ) (hn : n ∈ P) (hΛ : ArithmeticFunction.vonMangoldt n ≠ 0) : χ n = 1 :=
    AnalyticNumberTheory.Arithmetic.character_eq_one_of_ambient_mangoldt (N := 1) χ
      (fun l hl h _ ↦ hχ l hl h) ((Nat.le_floor_iff hX).mp (Finset.mem_Ioc.mp hn).2)
      (Nat.coprime_one_right n) hΛ
  have he :=
    quarter_separate_euler_644 a b c (P ∪ T) ht
      (by
        intro n hn hΛ
        rcases Finset.mem_union.mp hn with hn | hn
        · rw [hbase a hA n hn hΛ, hbase b hB n hn hΛ, hbase c hC n hn hΛ, Complex.one_re]
          norm_num only
        · exact (hT n hn).2.2)
  have hd : Disjoint P T :=
    Finset.disjoint_left.mpr
      (fun n hn hTn ↦
        (not_lt_of_ge ((Nat.le_floor_iff hX).mp (Finset.mem_Ioc.mp hn).2)) (hT n hTn).2.1)
  rw [Finset.sum_union hd] at he
  have hT' : (∑ n ∈ T, W n) = ∑ n ∈ T, Real.log n * quarterEulerWeight644 n := by
    apply Finset.sum_congr rfl
    intro n hn
    dsimp only [W]
    rw [ArithmeticFunction.vonMangoldt_apply_prime (hT n hn).1]
  have hM :=
    quarter_even_mass_upper_644 a b c hp hq hs hG hG.riemann ha.1 hb.1 hc.1 ha.2.1 hb.2.1 hc.2.1
      ha.2.2 hb.2.2 hc.2.2 hlog
  have hsA := quarter_signed_euler_summable_644 a
  have hsB := quarter_signed_euler_summable_644 b
  have hsC := quarter_signed_euler_summable_644 c
  have heq (n : ℕ) :
    (3 - ((a n).re + (b n).re + (c n).re)) * W n =
      3 * W n - ((a n).re * W n + (b n).re * W n + (c n).re * W n) := by
    ring
  change _ ≤ _ + (∑' n : ℕ, (3 - ((a n).re + (b n).re + (c n).re)) * W n) at hM
  simp_rw [heq] at hM
  rw [Summable.tsum_sub (quarter_euler_weight_summable_644.mul_left 3) ((hsA.add hsB).add hsC),
    Summable.tsum_add (hsA.add hsB) hsC, Summable.tsum_add hsA hsB, tsum_mul_left] at hM
  have htail := positive_tail_upper_644 hG.riemann hlo hhi
  dsimp only [W, P] at he hM hT'
  linarith only [he, hM, hT', htail]

end PseudoPrime.PrimeTestBounds.MillerRabin
