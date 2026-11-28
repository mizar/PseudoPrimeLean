/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTriangleGammaPair
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTrianglePairMass

/-! # Translated arithmetic sums for uniform Korselt triples -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At radius at least 287 the normalized real arithmetic sum is bounded
in absolute value by the normalized zero mass plus the translated gamma error. -/
theorem triangle_shifted_real_bound {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hi : χ⁻¹ = χ) (hev : χ.Even) {r : ℝ} (hr : 287 ≤ r) :
    let x := Real.exp (2 * Real.log r + 5 / 2)
    let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 5 / 4)
    (2 / 5) * |(∑' n : ℕ, K.summand χ x n).re| <
      (2 / 5) * (∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖) + 1 / 250 := by
  intro x K
  have hl := Real.log_nonneg (show 1 ≤ r by linarith only [hr])
  have hx : 1 ≤ x := Real.one_le_exp (by linarith only [hl])
  have hxlog : 5 / 2 ≤ Real.log x := by
    rw [Real.log_exp]; linarith only [hl]
  have ha := triangle_shifted_arithmetic_bound hq hGRH hp hne hi hx hxlog
  have hg := triangle_gamma_pair_bound hev hr
  dsimp only at ha hg
  have hadd (a g : ℂ) : |a.re| ≤ ‖a - g‖ + |g.re| := by
    have h := abs_add_le (a - g).re g.re
    rw [Complex.sub_re, sub_add_cancel] at h
    exact h.trans (add_le_add (Complex.abs_re_le_norm (a - g)) le_rfl)
  have ht := (hadd _ _).trans (add_le_add ha le_rfl)
  linarith only [ht, hg]

/-- Each pair character of a uniform Korselt product has normalized shifted
arithmetic mass below its log conductor minus the origin saving plus the gamma error. -/
theorem triangle_pair_arithmetic {n p q : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero (p * q)]
    [Fact p.Prime] [Fact q.Prime] [Fact (2 < p)] [Fact (2 < q)] (hn : 1 < n) (ho : Odd n)
    (hs : Squarefree n) (hp : Odd p) (hq : Odd q) (hd : p * q ∣ n) (hk : p - 1 ∣ n - 1)
    (hj : q - 1 ∣ n - 1) (hv : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {R : ℝ} (hR : 287 ≤ R)
    (hb :
      ∀ b : ℕ, b.Prime → b ≤ ⌊Real.exp (5 / 2)⌋₊ → PrimeTest.StrongMillerRabinPass n (b : ZMod n)) :
    let x := Real.exp (2 * Real.log R + 5 / 2)
    let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 5 / 4)
    let χ := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    (2 / 5) * |(∑' b : ℕ, K.summand χ x b).re| < Real.log (p * q : ℕ) - 28 / 5 + 1 / 250 := by
  have hprod :=
    (Fact.out : p.Prime).one_lt.trans_le (Nat.le_mul_of_pos_right p (Fact.out : q.Prime).pos)
  have ha :=
    triangle_shifted_real_bound hprod hGRH (pair_character_primitive hs hd (hp.mul hq))
      (pair_character_ne_one hs hd (hp.mul hq) hprod)
      (NumberTheory.complexJacobiNumeratorCharacter_isQuadratic _ _).inv
      (pair_character_even_of_korselt hn ho hp hq hk hj hv) hR
  exact ha.trans (add_lt_add_left (triangle_pair_zero_mass hn ho hs hp hq hd hk hj hv hGRH hb) _)

/-- The three normalized absolute real arithmetic sums in the translated window
have total cost below twice log n minus the three origin savings plus three gamma errors. -/
theorem triangle_triple_arithmetic {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hn : 1 < n) (ho : Odd n) (hs : Squarefree n) (he : n = p * q * r) (hp : Odd p) (hq : Odd q)
    (hr : Odd r) (hk : p - 1 ∣ n - 1) (hj : q - 1 ∣ n - 1) (hm : r - 1 ∣ n - 1)
    (hv : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hw : padicValNat 2 (r - 1) = padicValNat 2 (p - 1))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {R : ℝ} (hR : 287 ≤ R)
    (hb :
      ∀ b : ℕ, b.Prime → b ≤ ⌊Real.exp (5 / 2)⌋₊ → PrimeTest.StrongMillerRabinPass n (b : ZMod n)) :
    let x := Real.exp (2 * Real.log R + 5 / 2)
    let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 5 / 4)
    let mass {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k) :=
      (2 / 5 : ℝ) * |(∑' b : ℕ, K.summand χ x b).re|
    mass (NumberTheory.complexJacobiNumeratorCharacter _ (hp.mul hq)) +
        mass (NumberTheory.complexJacobiNumeratorCharacter _ (hp.mul hr)) +
        mass (NumberTheory.complexJacobiNumeratorCharacter _ (hq.mul hr)) <
      2 * Real.log n - 84 / 5 + 3 / 250 := by
  have ha : p * q ∣ n := he ▸ dvd_mul_right _ _
  have hB : p * r ∣ n := by
    rw [he, mul_right_comm]; exact dvd_mul_right _ _
  have hc : q * r ∣ n := by
    rw [he, Nat.mul_assoc]; exact dvd_mul_left _ _
  have hab := triangle_pair_arithmetic hn ho hs hp hq ha hk hj hv hGRH hR hb
  have hac := triangle_pair_arithmetic hn ho hs hp hr hB hk hm hw hGRH hR hb
  have hbc := triangle_pair_arithmetic hn ho hs hq hr hc hj hm (hw.trans hv.symm) hGRH hR hb
  dsimp only at hab hac hbc ⊢
  linarith only [hab, hac, hbc, pair_level_log_sum he]

end PseudoPrime.PrimeTestBounds.MillerRabin
