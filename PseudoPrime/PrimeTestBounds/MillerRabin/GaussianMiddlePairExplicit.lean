/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleExplicit
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPairCharacterData
import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticTripleConductors
import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticTripleCharacters

/-! # Middle explicit formula for the three pair characters -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under passage of the prime bases, sum the middle explicit formulas for the
three primitive pair characters. Their conductors contribute twice the log of
the product, and the common Gamma integral is counted three times. -/
public theorem middle_pair_explicit (Q : Polynomial ℚ) {N : ℕ} (hQ : 2 * Q.natDegree + 3 ≤ N)
    {a b x : ℝ} (ha : 1 ≤ a) (hb : 0 ≤ b) (hx : 0 ≤ x) (κ : ℝ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n p q r : ℕ} [NeZero p]
    [NeZero q] [NeZero r] [NeZero n] [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)]
    [Fact (2 < q)] [Fact (2 < r)] (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hprod : n = p * q * r) (hp : Odd p) (hq : Odd q) (hr : Odd r)
    (hpass :
      ∀ l : ℕ, l.Prime → (l : ℝ) ≤ Real.exp x → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    let χ₁ := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    let χ₂ := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
    let χ₃ := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
    let τ := fun j : ℕ ↦ (χ₁ j).re + (χ₂ j).re + (χ₃ j).re
    let ha' : 1 / 2 < a := (by norm_num only : (1 / 2 : ℝ) < 1).trans_le ha
    let K := fun i : ℕ ↦ LLS.PaperStatements.shiftedPoleKernel (max 1 i) a b (le_max_left _ _) ha'
    let S := Finset.Ico 3 (N + 1)
    let c := fun i ↦ ((Q ^ 2).coeff (N - i) : ℂ)
    let W := fun s : ℂ ↦ (∑ i ∈ S, c i * (K i).function s) * Complex.exp (s * (x : ℂ))
    let B := (middlePoleProfile N Q).map (Rat.castHom ℝ)
    let w := middlePrincipalWeight B (κ * Real.exp (-a * (x + b))) (x + b) (a - 1 / 2)
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let u := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
    let D := ((1 / (2 * Real.pi) : ℝ) : ℂ)
    let Z := fun {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) ↦
      -((κ : ℂ) * (∑' γ : ℂ, ∑ i ∈ S, c i * (K i).oscillatingZeroTerm χ (Real.exp x) γ)).re
    let G :=
      κ *
        ((D * (∫ v : ℝ, logDeriv Complex.Gammaℝ (u v + 1 / 2) * W (u v))).re +
          (D * (∫ v : ℝ, logDeriv Complex.Gammaℝ (1 / 2 - l v) * W (l v))).re)
    (∑ j ∈ Finset.Ioc 0 ⌊Real.exp (x + b)⌋₊, ArithmeticFunction.vonMangoldt j * (τ j * w j)) +
        middleReflectedSum B τ κ a b x =
      Z χ₁ + Z χ₂ + Z χ₃ + (2 * Real.log n) * (κ * Real.exp (-a * (x + b))) * B.eval (x + b) +
        3 * G := by
  intro χ₁ χ₂ χ₃ τ ha' K S c W B w l u D Z G
  obtain ⟨h₁, h₂, h₃, hχ₁, hχ₂, hχ₃, _⟩ :=
    pair_data_of_uniform_pass hn ho hu hprod hp hq hr (Real.exp x) hpass
  have e₁ := middle_explicit_euler_real Q hQ ha hb hx κ h₁ hGRH hχ₁.1 hχ₁.2.1 hχ₁.2.2.1 hχ₁.2.2.2
  have e₂ := middle_explicit_euler_real Q hQ ha hb hx κ h₂ hGRH hχ₂.1 hχ₂.2.1 hχ₂.2.2.1 hχ₂.2.2.2
  have e₃ := middle_explicit_euler_real Q hQ ha hb hx κ h₃ hGRH hχ₃.1 hχ₃.2.1 hχ₃.2.2.1 hχ₃.2.2.2
  have hbound {m : ℕ} (χ : DirichletCharacter ℂ m) (j : ℕ) : |(χ j).re| ≤ 3 :=
    (Complex.abs_re_le_norm _).trans ((χ.norm_le_one j).trans (by norm_num only))
  have hR :=
    middle_reflected_add_three B (fun j ↦ (χ₁ j).re) (fun j ↦ (χ₂ j).re) (fun j ↦ (χ₃ j).re)
      (hbound χ₁) (hbound χ₂) (hbound χ₃) (κ := κ) (b := b) (x := x) ha'
  change middleReflectedSum B τ κ a b x = _ at hR
  rw [hR]
  have hF :
    (∑ j ∈ Finset.Ioc 0 ⌊Real.exp (x + b)⌋₊, ArithmeticFunction.vonMangoldt j * (τ j * w j)) =
      (∑ j ∈ Finset.Ioc 0 ⌊Real.exp (x + b)⌋₊,
          ArithmeticFunction.vonMangoldt j * ((χ₁ j).re * w j)) +
        (∑ j ∈ Finset.Ioc 0 ⌊Real.exp (x + b)⌋₊,
          ArithmeticFunction.vonMangoldt j * ((χ₂ j).re * w j)) +
        (∑ j ∈ Finset.Ioc 0 ⌊Real.exp (x + b)⌋₊,
          ArithmeticFunction.vonMangoldt j * ((χ₃ j).re * w j)) := by
    simp only [τ, add_mul, mul_add, Finset.sum_add_distrib]
  rw [hF]
  have hlog := pair_level_log_sum hprod
  linear_combination e₁ + e₂ + e₃ + ((κ * Real.exp (-a * (x + b))) * B.eval (x + b)) * hlog

/-- Supply the bounds on the pair trace required by the middle Euler estimates.
When the small prime bases pass, the trace is three on their prime powers. -/
public theorem middle_pair_trace_bounds {n p q r : ℕ} [NeZero p] [NeZero q] [NeZero r] [NeZero n]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n) (hprod : n = p * q * r) (hp : Odd p)
    (hq : Odd q) (hr : Odd r) {x : ℝ}
    (hpass :
      ∀ l : ℕ, l.Prime → (l : ℝ) ≤ Real.exp x → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    let χ₁ := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    let χ₂ := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
    let χ₃ := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
    let τ := fun j : ℕ ↦ (χ₁ j).re + (χ₂ j).re + (χ₃ j).re
    (∀ m, -1 ≤ τ m ∧ τ m ≤ 3) ∧
      (∀ m, |τ m| ≤ 3) ∧ (∀ m ≤ ⌊Real.exp x⌋₊, ArithmeticFunction.vonMangoldt m ≠ 0 → τ m = 3) := by
  intro χ₁ χ₂ χ₃ τ
  obtain ⟨_, _, _, _, _, _, hsmall⟩ :=
    pair_data_of_uniform_pass hn ho hu hprod hp hq hr (Real.exp x) hpass
  have hτ (m : ℕ) : -1 ≤ τ m ∧ τ m ≤ 3 := by
    constructor
    · simpa only [τ, χ₁, χ₂, χ₃, Int.cast_natCast] using
        pair_character_sum_ge_neg_one (m : ℤ) p q r (hp.mul hq) (hp.mul hr) (hq.mul hr)
    · dsimp only [τ]
      linarith only [(Complex.re_le_norm (χ₁ m)).trans (χ₁.norm_le_one _),
        (Complex.re_le_norm (χ₂ m)).trans (χ₂.norm_le_one _),
        (Complex.re_le_norm (χ₃ m)).trans (χ₃.norm_le_one _)]
  refine ⟨hτ, fun m ↦ abs_le.mpr ⟨(by norm_num only : (-3 : ℝ) ≤ -1).trans (hτ m).1, (hτ m).2⟩, ?_⟩
  intro m hm hΛ
  have hm' := (Nat.le_floor_iff (Real.exp_nonneg x)).mp hm
  obtain ⟨l, k, hl, hk, rfl⟩ :=
    (isPrimePow_nat_iff m).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ)
  have hlx := (Nat.cast_le.mpr (Nat.le_self_pow hk.ne' l)).trans hm'
  obtain ⟨h₁, h₂, h₃⟩ := hsmall l hl hlx
  change χ₁ l = 1 at h₁
  change χ₂ l = 1 at h₂
  change χ₃ l = 1 at h₃
  norm_num only [τ, Nat.cast_pow, map_pow, h₁, h₂, h₃, one_pow, Complex.one_re]

end PseudoPrime.PrimeTestBounds.MillerRabin
