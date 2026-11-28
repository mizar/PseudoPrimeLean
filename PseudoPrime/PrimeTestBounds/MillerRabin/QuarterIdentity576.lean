/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterGamma570

/-! # Identity-prime savings in the section 86 zero mass -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Each prime beyond the cutoff where all three even characters equal one
saves four times its weighted logarithm in the sixth-pole mass bound. The
disjoint union with the known prefix avoids counting any contribution twice. -/
theorem mass_identity_primes_of_recovery {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r)
    (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hRA : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis a)
    (hRB : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis b)
    (hRC : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis c) (hpA : a.IsPrimitive)
    (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1) (hnC : c ≠ 1)
    (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) {X : ℝ} (s : Finset ℕ)
    (hS : ∀ k ∈ s, (k : ℝ) ≤ X) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) (w : Finset ℕ)
    (hw : ∀ l ∈ w, X < (l : ℝ) ∧ l.Prime ∧ a l = 1 ∧ b l = 1 ∧ c l = 1) {R T : ℝ}
    (hlog : Real.log p + Real.log q + Real.log r ≤ 4 * R) {C : ℝ}
    (hrec :
      C ≤
        3 * (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n) -
          (quarterGamma570 a + quarterGamma570 b + quarterGamma570 c) / 8)
    (htail :
      (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n) -
          (∑ n ∈ s, ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n) ≤
        T) :
    quarterMass570 a + quarterMass570 b + quarterMass570 c ≤
      3 / 4 * R - C + 4 * T - 4 * ∑ l ∈ w, Real.log l * quarterEulerWeight570 l := by
  have hd : Disjoint s w :=
    Finset.disjoint_left.mpr (fun _ hk hw' ↦ (not_lt_of_ge (hS _ hk)) (hw _ hw').1)
  have ht' (k : ℕ) (hk : k ∈ s ∪ w) (hv : ArithmeticFunction.vonMangoldt k ≠ 0) :
    (a k).re + (b k).re + (c k).re = 3 := by
    rcases Finset.mem_union.mp hk with hs | hs
    · have oneAt {d : ℕ} (χ : DirichletCharacter ℂ d)
        (hχ : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → χ l = 1) :=
        AnalyticNumberTheory.Arithmetic.character_eq_one_of_ambient_mangoldt (N := 1) χ
          (fun l hl hlX _ ↦ hχ l hl hlX) (hS k hs) (Nat.coprime_one_right k) hv
      rw [oneAt a hA, oneAt b hB, oneAt c hC, Complex.one_re]
      norm_num only
    · obtain ⟨_, _, ha, hb, hc⟩ := hw k hs
      rw [ha, hb, hc, Complex.one_re]
      norm_num only
  have hm :=
    quarter_three_mass_570 a b c hP hQ hR hRA hRB hRC hpA hpB hpC hnA hnB hnC hiA hiB hiC (s ∪ w) ht
      ht'
  rw [Finset.sum_union hd] at hm
  have he :=
    Finset.sum_congr (s₁ := w) rfl
      (fun l hl ↦
        congrArg (fun v : ℝ ↦ v * quarterEulerWeight570 l)
          (ArithmeticFunction.vonMangoldt_apply_prime (hw l hl).2.1))
  linarith only [hm, he, hlog, htail, hrec]

/-- Specialize finite identity-prime recovery to the section 86 constants. -/
theorem mass_identity_primes_576 {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r)
    (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hRA : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis a)
    (hRB : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis b)
    (hRC : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis c) (hpA : a.IsPrimitive)
    (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1) (hnC : c ≠ 1)
    (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) {X : ℝ} (s : Finset ℕ)
    (hS : ∀ k ∈ s, (k : ℝ) ≤ X) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) (w : Finset ℕ)
    (hw : ∀ l ∈ w, X < (l : ℝ) ∧ l.Prime ∧ a l = 1 ∧ b l = 1 ∧ c l = 1) {R T : ℝ}
    (hlog : Real.log p + Real.log q + Real.log r ≤ 4 * R) (hRH : RiemannHypothesis) (heA : a.Even)
    (heB : b.Even) (heC : c.Even)
    (htail :
      (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n) -
          (∑ n ∈ s, ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n) ≤
        T) :
    quarterMass570 a + quarterMass570 b + quarterMass570 c ≤
      3 / 4 * R - 13386 / 1000 + 4 * T - 4 * ∑ l ∈ w, Real.log l * quarterEulerWeight570 l := by
  apply
    mass_identity_primes_of_recovery a b c hP hQ hR hRA hRB hRC hpA hpB hpC hnA hnB hnC hiA hiB hiC
      s hS ht hA hB hC w hw hlog _ htail
  linarith only [euler570_total_lower hRH, quarter_gamma_even_570 heA, quarter_gamma_even_570 heB,
    quarter_gamma_even_570 heC]

/-- Euler mass at a prime above X where all three characters equal one, and zero elsewhere. -/
noncomputable def identityWeight576 {p q r : ℕ} (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (X : ℝ) (l : ℕ) : ℝ := by
  classical
    exact
    if X < l ∧ l.Prime ∧ a l = 1 ∧ b l = 1 ∧ c l = 1 then
      ArithmeticFunction.vonMangoldt l * quarterEulerWeight570 l
    else 0

/-- The full series of identity primes gives the same fourfold saving as its
finite subsums. Nonnegativity and domination by the universal Euler series
justify passage to the limit over finite sets. -/
theorem mass_identity_series_of_recovery {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
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
    (hlog : Real.log p + Real.log q + Real.log r ≤ 4 * R) {C : ℝ}
    (hrec :
      C ≤
        3 * (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n) -
          (quarterGamma570 a + quarterGamma570 b + quarterGamma570 c) / 8)
    (htail :
      (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n) -
          (∑ n ∈ s, ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n) ≤
        T) :
    quarterMass570 a + quarterMass570 b + quarterMass570 c ≤
      3 / 4 * R - C + 4 * T - 4 * ∑' l : ℕ, identityWeight576 a b c X l := by
  classical
  let P := fun l : ℕ ↦ X < (l : ℝ) ∧ l.Prime ∧ a l = 1 ∧ b l = 1 ∧ c l = 1
  have hsum : Summable (identityWeight576 a b c X) := by
    apply quarter_euler_weight_summable_570.of_nonneg_of_le
    · intro l
      unfold identityWeight576
      split_ifs
      · exact
          mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (quarter_euler_weight_nonneg_570_all l)
      · exact le_rfl
    · intro l
      unfold identityWeight576
      split_ifs
      · exact le_rfl
      · exact
          mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (quarter_euler_weight_nonneg_570_all l)
  have hf (t : Finset ℕ) :=
    mass_identity_primes_of_recovery a b c hP hQ hR hRA hRB hRC hpA hpB hpC hnA hnB hnC hiA hiB hiC
      s hS ht hA hB hC (t.filter P) (fun _ h ↦ (Finset.mem_filter.mp h).2) hlog hrec htail
  have he (t : Finset ℕ) :
    (∑ l ∈ t.filter P, Real.log l * quarterEulerWeight570 l) =
      ∑ l ∈ t, identityWeight576 a b c X l := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro l _
    unfold identityWeight576
    change (if P l then _ else _) = (if P l then _ else _)
    split_ifs with h
    · rw [ArithmeticFunction.vonMangoldt_apply_prime h.2.1]
    · rfl
  apply ge_of_tendsto (tendsto_const_nhds.sub (tendsto_const_nhds.mul hsum.hasSum))
  exact Filter.Eventually.of_forall (fun t ↦ (he t) ▸ hf t)

/-- Specialize identity-prime recovery to the section 86 Gamma and Euler constants. -/
theorem mass_identity_series_576 {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
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
    (hlog : Real.log p + Real.log q + Real.log r ≤ 4 * R) (hRH : RiemannHypothesis) (heA : a.Even)
    (heB : b.Even) (heC : c.Even)
    (htail :
      (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n) -
          (∑ n ∈ s, ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n) ≤
        T) :
    quarterMass570 a + quarterMass570 b + quarterMass570 c ≤
      3 / 4 * R - 13386 / 1000 + 4 * T - 4 * ∑' l : ℕ, identityWeight576 a b c X l := by
  apply
    mass_identity_series_of_recovery a b c hP hQ hR hRA hRB hRC hpA hpB hpC hnA hnB hnC hiA hiB hiC
      s hS ht hA hB hC hlog _ htail
  linarith only [euler570_total_lower hRH, quarter_gamma_even_570 heA, quarter_gamma_even_570 heB,
    quarter_gamma_even_570 heC]

end PseudoPrime.PrimeTestBounds.MillerRabin
