/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.GammaQuadraticArithmetic
public import Mathlib.Tactic.Linarith
public import PseudoPrime.LLS.PaperStatements.MellinKernelBounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.CharacterFullTriviality

/-! # Simultaneous quadratic Gamma main summands -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At positive scale, the three actual quadratic Gamma summands have a
common normalized nonnegative exponential Mangoldt weight. Sum the existing
individual identities and factor the three real character values. This is
the arithmetic bridge to the simultaneous main-sum lower bound. -/
theorem gamma_three_summand_identity {p q r : ℕ} (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (ha : a.IsQuadratic)
    (hb : b.IsQuadratic) (hc : c.IsQuadratic) {x : ℝ} (hx : 0 < x) (n : ℕ) :
    (LLS.PaperStatements.gammaMellinKernel.summand a x n).re +
        (LLS.PaperStatements.gammaMellinKernel.summand b x n).re +
        (LLS.PaperStatements.gammaMellinKernel.summand c x n).re =
      ((a n).re + (b n).re + (c n).re) *
        (Real.exp (-(n : ℝ) / x) * ArithmeticFunction.vonMangoldt n / Real.sqrt x) := by
  rw [LLS.PaperStatements.gamma_quadratic_summand_re_eq_exponential_all a ha hx,
    LLS.PaperStatements.gamma_quadratic_summand_re_eq_exponential_all b hb hx,
    LLS.PaperStatements.gamma_quadratic_summand_re_eq_exponential_all c hc hx]
  ring

/-- At positive scale, a simultaneous real-part sum at least minus one
makes the exponential principal weight plus the three actual quadratic Gamma
summands nonnegative. Factor the common weight and use its nonnegativity.
This justifies discarding terms outside a finite prefix in the main comparison. -/
theorem gamma_three_main_nonneg {p q r : ℕ} (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (ha : a.IsQuadratic)
    (hb : b.IsQuadratic) (hc : c.IsQuadratic) {x : ℝ} (hx : 0 < x) (n : ℕ)
    (hs : -1 ≤ (a n).re + (b n).re + (c n).re) :
    0 ≤
      Real.exp (-(n : ℝ) / x) * ArithmeticFunction.vonMangoldt n / Real.sqrt x +
        ((LLS.PaperStatements.gammaMellinKernel.summand a x n).re +
          (LLS.PaperStatements.gammaMellinKernel.summand b x n).re +
          (LLS.PaperStatements.gammaMellinKernel.summand c x n).re) := by
  rw [gamma_three_summand_identity a b c ha hb hc hx n]
  have hw : 0 ≤ Real.exp (-(n : ℝ) / x) * ArithmeticFunction.vonMangoldt n / Real.sqrt x :=
    div_nonneg (mul_nonneg (Real.exp_pos _).le ArithmeticFunction.vonMangoldt_nonneg)
      (Real.sqrt_nonneg x)
  have ht := mul_le_mul_of_nonneg_right hs hw
  linarith only [ht]

/-- At any positive scale, the normalized exponential Mangoldt weights are
summable. Identify them with the actual level-one Gamma summands and use the
real continuous-linear map on the convergent kernel series. This supplies
convergence for the principal term of the simultaneous main-sum inequality. -/
theorem summable_gamma_principal_weight {x : ℝ} (hx : 0 < x) :
    Summable
      (fun n : ℕ ↦ Real.exp (-(n : ℝ) / x) * ArithmeticFunction.vonMangoldt n / Real.sqrt x) := by
  have h1 : (1 : DirichletCharacter ℂ 1).IsQuadratic := fun z ↦
    Or.inr (Or.inl (MulChar.one_apply (isUnit_of_subsingleton z)))
  have hs :=
    Complex.reCLM.summable
      (LLS.PaperStatements.MellinKernel.summable_summand LLS.PaperStatements.gammaMellinKernel
        (1 : DirichletCharacter ℂ 1) hx)
  have he (n : ℕ) :
    (LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re =
      Real.exp (-(n : ℝ) / x) * ArithmeticFunction.vonMangoldt n / Real.sqrt x := by
    rw [LLS.PaperStatements.gamma_quadratic_summand_re_eq_exponential_all _ h1 hx,
      MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1)), Complex.one_re, one_mul]
  exact hs.congr he

/-- At positive scale, three actual quadratic Gamma series with a
simultaneous sign lower bound dominate four times the exponential Mangoldt
prefix wherever the prefix real-part sum is three. Use convergence of each
actual kernel series and the principal weight, then discard the nonnegative
complement. This supplies the infinite main-sum form of the coupled comparison. -/
theorem gamma_three_main_prefix_le {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r)
    (ha : a.IsQuadratic) (hb : b.IsQuadratic) (hc : c.IsQuadratic) {x : ℝ} (hx : 0 < x)
    (s : Finset ℕ) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hp : ∀ k ∈ s, (a k).re + (b k).re + (c k).re = 3) :
    4 * (∑ k ∈ s, Real.exp (-(k : ℝ) / x) * ArithmeticFunction.vonMangoldt k / Real.sqrt x) ≤
      ∑' k : ℕ,
        (Real.exp (-(k : ℝ) / x) * ArithmeticFunction.vonMangoldt k / Real.sqrt x +
          ((LLS.PaperStatements.gammaMellinKernel.summand a x k).re +
            (LLS.PaperStatements.gammaMellinKernel.summand b x k).re +
            (LLS.PaperStatements.gammaMellinKernel.summand c x k).re)) := by
  have hsA :=
    Complex.reCLM.summable
      (LLS.PaperStatements.MellinKernel.summable_summand LLS.PaperStatements.gammaMellinKernel a hx)
  have hsB :=
    Complex.reCLM.summable
      (LLS.PaperStatements.MellinKernel.summable_summand LLS.PaperStatements.gammaMellinKernel b hx)
  have hsC :=
    Complex.reCLM.summable
      (LLS.PaperStatements.MellinKernel.summable_summand LLS.PaperStatements.gammaMellinKernel c hx)
  have h :=
    ((summable_gamma_principal_weight hx).add ((hsA.add hsB).add hsC)).sum_le_tsum s
      (fun k _ ↦ gamma_three_main_nonneg a b c ha hb hc hx k (ht k))
  have he :
    (∑ k ∈ s,
        (Real.exp (-(k : ℝ) / x) * ArithmeticFunction.vonMangoldt k / Real.sqrt x +
          ((LLS.PaperStatements.gammaMellinKernel.summand a x k).re +
            (LLS.PaperStatements.gammaMellinKernel.summand b x k).re +
            (LLS.PaperStatements.gammaMellinKernel.summand c x k).re))) =
      4 * (∑ k ∈ s, Real.exp (-(k : ℝ) / x) * ArithmeticFunction.vonMangoldt k / Real.sqrt x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [gamma_three_summand_identity a b c ha hb hc hx k, hp k hk]
    ring
  rw [he] at h
  exact h

/-- The actual three-character main comparison only needs prefix sign
equality on nonzero Mangoldt support. Terms of weight zero vanish. This
allows small-prime triviality to supply the prefix without conditions on
other integers, while retaining convergence and nonnegativity of the tail. -/
theorem gamma_three_main_prefix_support_le {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r)
    (ha : a.IsQuadratic) (hb : b.IsQuadratic) (hc : c.IsQuadratic) {x : ℝ} (hx : 0 < x)
    (s : Finset ℕ) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hp : ∀ k ∈ s, ArithmeticFunction.vonMangoldt k ≠ 0 → (a k).re + (b k).re + (c k).re = 3) :
    4 * (∑ k ∈ s, Real.exp (-(k : ℝ) / x) * ArithmeticFunction.vonMangoldt k / Real.sqrt x) ≤
      ∑' k : ℕ,
        (Real.exp (-(k : ℝ) / x) * ArithmeticFunction.vonMangoldt k / Real.sqrt x +
          ((LLS.PaperStatements.gammaMellinKernel.summand a x k).re +
            (LLS.PaperStatements.gammaMellinKernel.summand b x k).re +
            (LLS.PaperStatements.gammaMellinKernel.summand c x k).re)) := by
  have hsA :=
    Complex.reCLM.summable
      (LLS.PaperStatements.MellinKernel.summable_summand LLS.PaperStatements.gammaMellinKernel a hx)
  have hsB :=
    Complex.reCLM.summable
      (LLS.PaperStatements.MellinKernel.summable_summand LLS.PaperStatements.gammaMellinKernel b hx)
  have hsC :=
    Complex.reCLM.summable
      (LLS.PaperStatements.MellinKernel.summable_summand LLS.PaperStatements.gammaMellinKernel c hx)
  have h :=
    ((summable_gamma_principal_weight hx).add ((hsA.add hsB).add hsC)).sum_le_tsum s
      (fun k _ ↦ gamma_three_main_nonneg a b c ha hb hc hx k (ht k))
  have he :
    (∑ k ∈ s,
        (Real.exp (-(k : ℝ) / x) * ArithmeticFunction.vonMangoldt k / Real.sqrt x +
          ((LLS.PaperStatements.gammaMellinKernel.summand a x k).re +
            (LLS.PaperStatements.gammaMellinKernel.summand b x k).re +
            (LLS.PaperStatements.gammaMellinKernel.summand c x k).re))) =
      4 * (∑ k ∈ s, Real.exp (-(k : ℝ) / x) * ArithmeticFunction.vonMangoldt k / Real.sqrt x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [gamma_three_summand_identity a b c ha hb hc hx k]
    by_cases hz : ArithmeticFunction.vonMangoldt k = 0
    · simp only [hz, mul_zero, zero_div, add_zero]
    · rw [hp k hk hz]
      ring
  rw [he] at h
  exact h

/-- If three quadratic characters are one at every prime through a cutoff,
their Gamma main sums dominate four times any prefix below that cutoff,
provided the simultaneous sign bound holds. Prime-power reduction determines
the nonzero Mangoldt terms internally. This is the main comparison ready for
the pair-character triviality produced by strong MR passage. -/
theorem gamma_three_main_of_prime_one {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r)
    (ha : a.IsQuadratic) (hb : b.IsQuadratic) (hc : c.IsQuadratic) {x : ℝ} (hx : 0 < x) {X : ℝ}
    (s : Finset ℕ) (hS : ∀ k ∈ s, (k : ℝ) ≤ X) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) :
    4 * (∑ k ∈ s, Real.exp (-(k : ℝ) / x) * ArithmeticFunction.vonMangoldt k / Real.sqrt x) ≤
      ∑' k : ℕ,
        (Real.exp (-(k : ℝ) / x) * ArithmeticFunction.vonMangoldt k / Real.sqrt x +
          ((LLS.PaperStatements.gammaMellinKernel.summand a x k).re +
            (LLS.PaperStatements.gammaMellinKernel.summand b x k).re +
            (LLS.PaperStatements.gammaMellinKernel.summand c x k).re)) := by
  apply gamma_three_main_prefix_support_le a b c ha hb hc hx s ht
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

/-- The prime-trivial main comparison can be written with the real parts
of the three actual complex series separately. Absolute convergence allows
splitting the combined series and commuting the real continuous-linear map
with each sum. This matches the form of the analytic character upper bounds. -/
theorem gamma_three_main_split_le {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r)
    (ha : a.IsQuadratic) (hb : b.IsQuadratic) (hc : c.IsQuadratic) {x : ℝ} (hx : 0 < x) {X : ℝ}
    (s : Finset ℕ) (hS : ∀ k ∈ s, (k : ℝ) ≤ X) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) :
    4 * (∑ k ∈ s, Real.exp (-(k : ℝ) / x) * ArithmeticFunction.vonMangoldt k / Real.sqrt x) ≤
      (∑' k : ℕ, Real.exp (-(k : ℝ) / x) * ArithmeticFunction.vonMangoldt k / Real.sqrt x) +
        (∑' k : ℕ, LLS.PaperStatements.gammaMellinKernel.summand a x k).re +
        (∑' k : ℕ, LLS.PaperStatements.gammaMellinKernel.summand b x k).re +
        (∑' k : ℕ, LLS.PaperStatements.gammaMellinKernel.summand c x k).re := by
  have h := gamma_three_main_of_prime_one a b c ha hb hc hx s hS ht hA hB hC
  have hsA :=
    LLS.PaperStatements.MellinKernel.summable_summand LLS.PaperStatements.gammaMellinKernel a hx
  have hsB :=
    LLS.PaperStatements.MellinKernel.summable_summand LLS.PaperStatements.gammaMellinKernel b hx
  have hsC :=
    LLS.PaperStatements.MellinKernel.summable_summand LLS.PaperStatements.gammaMellinKernel c hx
  have hrA : Summable (fun k ↦ (LLS.PaperStatements.gammaMellinKernel.summand a x k).re) :=
    Complex.reCLM.summable hsA
  have heA := Complex.reCLM.map_tsum hsA
  have hrB : Summable (fun k ↦ (LLS.PaperStatements.gammaMellinKernel.summand b x k).re) :=
    Complex.reCLM.summable hsB
  have heB := Complex.reCLM.map_tsum hsB
  have hrC : Summable (fun k ↦ (LLS.PaperStatements.gammaMellinKernel.summand c x k).re) :=
    Complex.reCLM.summable hsC
  have heC := Complex.reCLM.map_tsum hsC
  rw [(summable_gamma_principal_weight hx).tsum_add ((hrA.add hrB).add hrC),
    (hrA.add hrB).tsum_add hrC, hrA.tsum_add hrB] at h
  change
    (∑' k : ℕ, LLS.PaperStatements.gammaMellinKernel.summand a x k).re =
      ∑' k : ℕ, (LLS.PaperStatements.gammaMellinKernel.summand a x k).re at heA
  change
    (∑' k : ℕ, LLS.PaperStatements.gammaMellinKernel.summand b x k).re =
      ∑' k : ℕ, (LLS.PaperStatements.gammaMellinKernel.summand b x k).re at heB
  change
    (∑' k : ℕ, LLS.PaperStatements.gammaMellinKernel.summand c x k).re =
      ∑' k : ℕ, (LLS.PaperStatements.gammaMellinKernel.summand c x k).re at heC
  rw [← heA, ← heB, ← heC] at h
  linarith only [h]

end PseudoPrime.PrimeTestBounds.MillerRabin
