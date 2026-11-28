/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterArithmetic632
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterGamma632
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterReflected632
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseGap107
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterContour600
import PseudoPrime.Analysis.NumericalLogBounds

/-! # Signed zero comparison on the radius interval [313, 316] -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Retain the radius-dependent Gamma recovery and use the sharper logarithmic
boundary cap at radius 313 in the signed zero comparison. -/
theorem signed_zero_upper_radius_632 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s) (hp : 2 ≤ p) (hq : 2 ≤ q) (hs : 2 ≤ s)
    (pa : a.IsPrimitive) (pb : b.IsPrimitive) (pc : c.IsPrimitive) (na : a ≠ 1) (nb : b ≠ 1)
    (nc : c ≠ 1) (ea : a.Even) (eb : b.Even) (ec : c.Even) {r : ℝ} (hr : r ∈ Set.Icc 313 316)
    (hlog : Real.log p + Real.log q + Real.log s ≤ 4 * r)
    (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) :
    let X := r ^ 2
    0.717289 * r + quarterArithmeticTerm632 r + 0.1448 * 1.53 * ((r - 313) / 316) +
        (3 * (0.035 * (1 - (r - 313) / 313)) + (if r ≤ 6289 / 20 then 0.01980648 else 0.01963648)) +
        ((∑' ρ : ℂ, quarterKernel570.oscillatingZeroTerm a X ρ).re +
          (∑' ρ : ℂ, quarterKernel570.oscillatingZeroTerm b X ρ).re +
          (∑' ρ : ℂ, quarterKernel570.oscillatingZeroTerm c X ρ).re) <
      section99Conductor r := by
  dsimp only
  have hx := one_le_pow₀ (show 1 ≤ r by linarith only [hr.1]) (n := 2)
  have ia := inv_ne_one.mpr na
  have ib := inv_ne_one.mpr nb
  have ic := inv_ne_one.mpr nc
  have h := quarter_arithmetic_growth_632 hG.riemann a b c hr ht hA hB hC
  dsimp only at h
  rw [section99_prime_sum_eq hp hG pa na ia hx, section99_prime_sum_eq hq hG pb nb ib hx,
    section99_prime_sum_eq hs hG pc nc ic hx] at h
  have ha := triple_contour_upper_from_313 a b c ia ib ic ea eb ec hr hlog
  have hz := reflected_integrals_632 hG.riemann hr.1 hr.2 a b c ht hA hB hC
  have hw : 0 ≤ quarterWeight570 (r ^ 2) 1 := by
    rw [section99_weight_eq_density (by linarith only [hr.1])]
    unfold gammaDensity570
    split_ifs
    · positivity
    · exact le_rfl
  have hb :=
    mul_le_mul_of_nonneg_right
      (show 3 * Real.log (2 * Real.pi) ≤ 5.517 by linarith only [Analysis.log_two_mul_pi_lt]) hw
  have hb' :=
    mul_le_mul_of_nonneg_left (quarter_weight_cap_313 hr.1) (by norm_num only : (0 : ℝ) ≤ 1.517)
  split_ifs with hcut
  · have hf := reflected_integrals_314_45 hG.riemann hr.1 hcut a b c ht hA hB hC
    linarith only [h, ha, hf, hb, hb']
  · linarith only [h, ha, hz, hb, hb']

/-- On the radius interval [313, 316], the signed oscillating sum is
controlled by the arithmetic lower bound, reflected recovery and Gamma terms. -/
theorem signed_zero_upper_632 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s) (hp : 2 ≤ p) (hq : 2 ≤ q) (hs : 2 ≤ s)
    (pa : a.IsPrimitive) (pb : b.IsPrimitive) (pc : c.IsPrimitive) (na : a ≠ 1) (nb : b ≠ 1)
    (nc : c ≠ 1) (ea : a.Even) (eb : b.Even) (ec : c.Even) {r : ℝ} (hr : r ∈ Set.Icc 313 316)
    (hlog : Real.log p + Real.log q + Real.log s ≤ 4 * r)
    (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) :
    let X := r ^ 2
    0.717289 * r + quarterArithmeticTerm632 r + 0.12337 +
        ((∑' ρ : ℂ, quarterKernel570.oscillatingZeroTerm a X ρ).re +
          (∑' ρ : ℂ, quarterKernel570.oscillatingZeroTerm b X ρ).re +
          (∑' ρ : ℂ, quarterKernel570.oscillatingZeroTerm c X ρ).re) <
      section99Conductor r := by
  have h :=
    signed_zero_upper_radius_632 hG a b c hp hq hs pa pb pc na nb nc ea eb ec hr hlog ht hA hB hC
  dsimp only at h ⊢
  split_ifs at h <;> linarith only [h, hr.1, hr.2]

/-- The two-frequency radius interval uses the sharper Gamma and reflection recovery
of its two arithmetic rows to bound the signed oscillating zero sum. -/
theorem signed_zero_upper_628 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s) (hp : 2 ≤ p) (hq : 2 ≤ q) (hs : 2 ≤ s)
    (pa : a.IsPrimitive) (pb : b.IsPrimitive) (pc : c.IsPrimitive) (na : a ≠ 1) (nb : b ≠ 1)
    (nc : c ≠ 1) (ea : a.Even) (eb : b.Even) (ec : c.Even) {r : ℝ} (hr : r ∈ Set.Icc 313 314)
    (hlog : Real.log p + Real.log q + Real.log s ≤ 4 * r)
    (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) :
    let X := r ^ 2
    0.717289 * r + quarterArithmeticTerm632 r + (if r ≤ 1568 / 5 then 0.12468 else 0.12450) +
        ((∑' ρ : ℂ, quarterKernel570.oscillatingZeroTerm a X ρ).re +
          (∑' ρ : ℂ, quarterKernel570.oscillatingZeroTerm b X ρ).re +
          (∑' ρ : ℂ, quarterKernel570.oscillatingZeroTerm c X ρ).re) <
      section99Conductor r := by
  dsimp only
  have hx := one_le_pow₀ (show 1 ≤ r by linarith only [hr.1]) (n := 2)
  have ia := inv_ne_one.mpr na
  have ib := inv_ne_one.mpr nb
  have ic := inv_ne_one.mpr nc
  have harith :=
    quarter_arithmetic_lower_632 hG.riemann a b c ⟨hr.1, hr.2.trans (by norm_num only)⟩ ht hA hB hC
  dsimp only at harith
  rw [section99_prime_sum_eq hp hG pa na ia hx, section99_prime_sum_eq hq hG pb nb ib hx,
    section99_prime_sum_eq hs hG pc nc ic hx] at harith
  have ha :=
    triple_contour_upper_from_313 a b c ia ib ic ea eb ec ⟨hr.1, hr.2.trans (by norm_num only)⟩ hlog
  have hz := reflected_integrals_628 hG.riemann hr.1 hr.2 a b c ht hA hB hC
  have hw : 0 ≤ quarterWeight570 (r ^ 2) 1 := by
    rw [section99_weight_eq_density (by linarith only [hr.1])]
    unfold gammaDensity570
    split_ifs
    · positivity
    · exact le_rfl
  have hb :=
    mul_le_mul_of_nonneg_right
      (show 3 * Real.log (2 * Real.pi) ≤ 5.517 by linarith only [Analysis.log_two_mul_pi_lt]) hw
  have hb' :=
    mul_le_mul_of_nonneg_left (quarter_weight_cap_313 hr.1) (by norm_num only : (0 : ℝ) ≤ 1.517)
  by_cases h : r ≤ 1568 / 5
  · rw [ite_eq_left h] at hz ⊢
    linarith only [h, ha, hz, hb, hb', harith]
  · rw [ite_eq_right h] at hz ⊢
    linarith only [hr.2, ha, hz, hb, hb', harith]

/-- The two certified rows make the mass, phase and signed zero estimates incompatible
at radii from 313 through 314. -/
theorem zero_bounds_contradict_628 {r M Z : ℝ} (hr : r ∈ Set.Icc 313 314)
    (hM : M ≤ 3 / 4 * r - 13.4154 + 4 * positiveTail570 (r ^ 2) - 0.02085)
    (hP : 0.0011365 * r + phaseClosed107 r ≤ M + Z)
    (hZ :
      0.717289 * r + quarterArithmeticTerm632 r + (if r ≤ 1568 / 5 then 0.12468 else 0.12450) + Z <
        section99Conductor r) :
    False := by
  by_cases h : r ≤ 1568 / 5
  · have he :=
      quarter_euler_row (by norm_num only : (292 : ℝ) ≤ 313) ⟨hr.1, h⟩
        (by norm_num only : (0 : ℝ) ≤ 3.78087) section107_euler_313 quarter_euler_at_313_6
    have hp := phase_remainder_lower_628 hr
    unfold quarterArithmeticTerm632 at hZ
    rw [ite_eq_left h, ite_eq_left h] at hZ
    linarith only [hM, hP, hZ, he, hp, h]
  · have hl := le_of_not_ge h
    have he :=
      quarter_euler_row (by norm_num only : (292 : ℝ) ≤ 1568 / 5) ⟨hl, hr.2⟩
        (by norm_num only : (0 : ℝ) ≤ 3.77798) quarter_euler_at_313_6 section107_euler_314
    have hp := phase_remainder_lower_628_right ⟨hl, hr.2⟩
    unfold quarterArithmeticTerm632 at hZ
    rw [ite_eq_right h, ite_eq_left hr.2, ite_eq_right h] at hZ
    linarith only [hM, hP, hZ, he, hp, hr.2]

end PseudoPrime.PrimeTestBounds.MillerRabin
