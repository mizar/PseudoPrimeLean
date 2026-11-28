/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighMassEvenDifference
import PseudoPrime.AnalyticNumberTheory.Arithmetic.CharacterPrimeTriviality
import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticTripleConductors
import Mathlib.Tactic.LinearCombination

/-! # Three-character zero mass and the signed Euler tail -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At unit scale, the Euler deficit is supported strictly above the tested cutoff. -/
private theorem high_mass_deficit_tail (K : HighGaussianKernel) {q : ℕ} (χ : DirichletCharacter ℂ q)
    {X : ℝ} (hX : 0 ≤ X) (hp : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ X → χ p = 1) :
    let W := fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n / Real.sqrt n * K.massProfile n
    (∑' n : ℕ, (1 - (χ n).re) * W n) =
      ∑' n : { n : ℕ // ⌊X⌋₊ < n }, (1 - (χ n.val).re) * W n.val := by
  intro W
  symm
  apply
    tsum_subtype_eq_of_support_subset (f := fun n : ℕ ↦ (1 - (χ n).re) * W n) (s :=
      {n : ℕ | ⌊X⌋₊ < n})
  intro n hn
  by_contra hno
  have hcut := (Nat.le_floor_iff hX).mp (le_of_not_gt hno)
  apply hn
  by_cases hm : ArithmeticFunction.vonMangoldt n = 0
  · simp only [W, hm, zero_div, zero_mul, mul_zero]
  simp only [AnalyticNumberTheory.Arithmetic.character_apply_one_of_mangoldt_ne_zero χ hp hcut hm,
    Complex.one_re, sub_self, zero_mul]

/-- The three signed deficits combine into the coefficient three minus the pair trace. -/
private theorem high_mass_trace_sum (K : HighGaussianKernel) {p q r : ℕ} [NeZero p] [NeZero q]
    [NeZero r] (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q)
    (c : DirichletCharacter ℂ r) (X : ℝ) :
    let W := fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n / Real.sqrt n * K.massProfile n
    let E := fun {m : ℕ} (χ : DirichletCharacter ℂ m) ↦
      ∑' n : { n : ℕ // ⌊X⌋₊ < n }, (1 - (χ n.val).re) * W n.val
    E a + E b + E c =
      ∑' n : { n : ℕ // ⌊X⌋₊ < n },
        (3 - ((a n.val).re + (b n.val).re + (c n.val).re)) * W n.val := by
  intro W E
  have hs {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) : Summable (fun n : ℕ ↦ (χ n).re * W n) :=
    (high_gaussian_mass_series_re K χ).summable
  have hW : Summable W := by
    apply (hs (1 : DirichletCharacter ℂ 1)).congr
    intro n
    simp only [MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1)), Complex.one_re, one_mul]
  have hE {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) :
    Summable (fun n : { n : ℕ // ⌊X⌋₊ < n } ↦ (1 - (χ n.val).re) * W n.val) := by
    apply ((hW.sub (hs χ)).subtype _).congr
    intro n
    change W n.val - (χ n.val).re * W n.val = _
    rw [sub_mul, one_mul]
  symm
  apply HasSum.tsum_eq
  apply (((hE a).hasSum.add (hE b).hasSum).add (hE c).hasSum).congr_fun
  intro n
  ring

/-- The central half in the Mellin profile cancels the two equal Euler tails. -/
private theorem twice_mass_weight (K : HighGaussianKernel) {m : ℕ} (hm : m ≠ 0) :
    2 * (ArithmeticFunction.vonMangoldt m / Real.sqrt m * K.massProfile m) =
      ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-(K.pole : ℝ) - 1 / 2) *
        (highGaussianMassPolynomial K).eval₂ (Rat.castHom ℝ) (Real.log m) := by
  have h := high_gaussian_mass_mangoldt_log K (1 : DirichletCharacter ℂ 1) hm
  simp only [MulChar.one_apply (isUnit_of_subsingleton (m : ZMod 1)), mul_one,
    ← Complex.ofReal_mul] at h
  linear_combination 2 * Complex.ofReal_injective h

/-- The signed tail in the three-character mass identity has the explicit
Fourier polynomial and the power weight of (H17). -/
public theorem high_gaussian_mass_tail_polynomial (K : HighGaussianKernel) {X : ℝ} (f : ℕ → ℝ) :
    (2 : ℝ) *
        ∑' m : { m : ℕ // ⌊X⌋₊ < m },
          f m.val * (ArithmeticFunction.vonMangoldt m.val / Real.sqrt m.val * K.massProfile m.val) =
      ∑' m : { m : ℕ // ⌊X⌋₊ < m },
        ArithmeticFunction.vonMangoldt m.val * f m.val * (m.val : ℝ) ^ (-(K.pole : ℝ) - 1 / 2) *
          (highGaussianMassPolynomial K).eval₂ (Rat.castHom ℝ) (Real.log m.val) := by
  rw [← tsum_mul_left]
  apply tsum_congr
  intro m
  have hm : m.val ≠ 0 := (Nat.zero_le _ |>.trans_lt m.property).ne'
  rw [mul_left_comm (2 : ℝ), twice_mass_weight K hm]
  ring

/-- The three pair conductors and their signed Euler tails give the high
Gaussian mass identity at every positive tested cutoff. -/
public theorem high_gaussian_three_mass (K : HighGaussianKernel) {n p q r : ℕ} [NeZero p] [NeZero q]
    [NeZero r] (hn : n = p * q * r) (a : DirichletCharacter ℂ (p * q))
    (b : DirichletCharacter ℂ (p * r)) (c : DirichletCharacter ℂ (q * r)) (hpq : 2 ≤ p * q)
    (hpr : 2 ≤ p * r) (hqr : 2 ≤ q * r) (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even)
    (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even) (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even)
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hRH : RiemannHypothesis) {X : ℝ}
    (hX : 0 < X) (hsmall : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1 ∧ b l = 1 ∧ c l = 1) :
    (∑' ρ : ℂ, ‖K.zeroTerm a X ρ‖) + (∑' ρ : ℂ, ‖K.zeroTerm b X ρ‖) +
        (∑' ρ : ℂ, ‖K.zeroTerm c X ρ‖) =
      3 / 8 * Real.log n - 6 * (K.massPole : ℝ) + 3 * K.xiMass.re +
        ∑' m : { m : ℕ // ⌊X⌋₊ < m },
          ArithmeticFunction.vonMangoldt m.val *
            (3 - ((a m.val).re + (b m.val).re + (c m.val).re)) *
            (m.val : ℝ) ^ (-(K.pole : ℝ) - 1 / 2) *
            (highGaussianMassPolynomial K).eval₂ (Rat.castHom ℝ) (Real.log m.val) := by
  rw [← high_gaussian_mass_tail_polynomial K (fun m ↦ 3 - ((a m).re + (b m).re + (c m).re))]
  have h₁ := high_gaussian_mass_even_real K hpq hg hRH ha.1 ha.2.1 ha.2.2.1 ha.2.2.2 hX
  have h₂ := high_gaussian_mass_even_real K hpr hg hRH hb.1 hb.2.1 hb.2.2.1 hb.2.2.2 hX
  have h₃ := high_gaussian_mass_even_real K hqr hg hRH hc.1 hc.2.1 hc.2.2.1 hc.2.2.2 hX
  dsimp only at h₁ h₂ h₃
  rw [high_mass_deficit_tail K a hX.le (fun l hl h ↦ (hsmall l hl h).1)] at h₁
  rw [high_mass_deficit_tail K b hX.le (fun l hl h ↦ (hsmall l hl h).2.1)] at h₂
  rw [high_mass_deficit_tail K c hX.le (fun l hl h ↦ (hsmall l hl h).2.2)] at h₃
  have htrace := high_mass_trace_sum K a b c X
  dsimp only at htrace
  rw [← htrace]
  dsimp only at h₁ h₂ h₃
  linear_combination h₁ + h₂ + h₃ + (3 / 16 : ℝ) * pair_level_log_sum hn

end PseudoPrime.PrimeTestBounds.MillerRabin
