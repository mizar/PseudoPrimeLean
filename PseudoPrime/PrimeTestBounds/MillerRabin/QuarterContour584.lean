/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterArithmetic584
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterGammaSigned570
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterRadiusGap570

/-! # Necessary zero-mass bound on the section 94 interval -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For an even character the two Gamma terms contribute at most -0.033
on radii 288 through 292 by the first convolution estimate. -/
private theorem evenContourUpper {q : ℕ} [NeZero q] (a : DirichletCharacter ℂ q) (ia : a⁻¹ ≠ 1)
    (ea : a.Even) {r : ℝ} (hl : 288 ≤ r) (hu : r ≤ 292) :
    contourNonEuler570 a (r ^ 2) ≤
      Real.log q * Analysis.rationalPoleProfile 3 (25 / 51) (7 / 5) (r ^ 2)⁻¹ - 33 / 1000 := by
  have hx := sq_pos_of_pos (show 0 < r by linarith only [hl])
  have hx1 := one_le_pow₀ (show 1 ≤ r by linarith only [hl]) (n := 2)
  have hlo :=
    (Analysis.rationalLogIntervalCheck_sound (N := 288) (j := 8) (n := 24) (lo := 566 / 100) (hi :=
        6) (by decide +kernel)).1
  have hhi :=
    (Analysis.rationalLogIntervalCheck_sound (N := 292) (j := 8) (n := 24) (lo := 5) (hi :=
        568 / 100) (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlo hhi
  have hz : 1412 / 100 ≤ Real.log (r ^ 2) + 14 / 5 := by
    rw [Real.log_pow, Nat.cast_ofNat]
    linarith only [hlo, Real.log_le_log (by norm_num only) hl]
  have hz' : Real.log (r ^ 2) + 14 / 5 ≤ 1416 / 100 := by
    rw [Real.log_pow, Nat.cast_ofNat]
    linarith only [hhi, Real.log_le_log (by linarith only [hl]) hu]
  have hc := first_convolution_lower_584 hz hz'
  have hd : 0 ≤ gammaDensity570 (Real.log (r ^ 2) + 14 / 5) := by
    rw [gammaDensity570, ite_eq_left (by linarith only [hz])]
    positivity
  have hn := central_gamma_convolution_upper a ea hx (by linarith only [hz])
  rw [← central_gamma_pair_eq_570 a ea hx, ← right_gamma_eq_central_570 a hx, ←
    reflected_arch_eq_central_570 _ ia hx1, Complex.add_re] at hn
  unfold contourNonEuler570
  simp only [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg _),
    ← Complex.ofReal_mul, Complex.ofReal_re]
  linarith only [hn, hc, hd]

/-- A passing triple on the section 94 interval forces its zero masses less its
reflected Euler integrals to exceed the arithmetic lower bound less 3.197. -/
theorem mass_sub_reflected_lower_584 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s) (hP : 2 ≤ p) (hQ : 2 ≤ q) (hS : 2 ≤ s)
    (pa : a.IsPrimitive) (pb : b.IsPrimitive) (pc : c.IsPrimitive) (na : a ≠ 1) (nb : b ≠ 1)
    (nc : c ≠ 1) (ia : a⁻¹ ≠ 1) (ib : b⁻¹ ≠ 1) (ic : c⁻¹ ≠ 1) {r : ℝ} (hl : 288 ≤ r) (hu : r ≤ 292)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1)
    (hlog : Real.log p + Real.log q + Real.log s ≤ 4 * r) (ea : a.Even) (eb : b.Even)
    (ec : c.Even) :
    let x := r ^ 2
    717289 / 1000000 * r - 322103 / 100000 <
      quarterMass570 a + quarterMass570 b + quarterMass570 c -
        (reflectedIntegral570 a x + reflectedIntegral570 b x + reflectedIntegral570 c x) := by
  intro x
  have hr : 0 < r := by linarith only [hl]
  have hx : 1 ≤ x := one_le_pow₀ (show 1 ≤ r by linarith only [hl])
  have ha := contour_prime_upper_570 hP hG pa na ia hx
  have hb := contour_prime_upper_570 hQ hG pb nb ib hx
  have hc := contour_prime_upper_570 hS hG pc nc ic hx
  simp only [reflected_inv_570 _ (zero_lt_one.trans_le hx)] at ha hb hc
  have hw := (quarter_reflected_weight_584 (by linarith only [hl] : 278 ≤ r) hu).1
  have hd := conductor_radius_upper_of_288 hl
  rw [quarterKernel570,
    LLS.PaperStatements.rationalPole_transform _ _ _ _ (one_div_pos.mpr (sq_pos_of_pos hr)),
    Complex.ofReal_re, one_div] at hw hd
  have hlogs :=
    mul_le_mul_of_nonneg_right hlog
      (show 0 ≤ Analysis.rationalPoleProfile 3 (25 / 51) (7 / 5) x⁻¹ by linarith only [hw])
  have hlow := triple_arithmetic_lower_584 a b c hl hu hG.riemann ht hA hB hC
  dsimp only at hlow
  dsimp only [x] at *
  linarith only [hlow, ha, hb, hc, evenContourUpper a ia ea hl hu, evenContourUpper b ib eb hl hu,
    evenContourUpper c ic ec hl hu, hlogs, hd]

/-- Under GRH and the passing-triple hypotheses, the reflected integrals on the
section 94 interval must lie below the linear bound obtained by freezing the
positive Euler tail at radius 288 and subtracting the contour lower bound. -/
theorem reflected_sum_upper_584 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s) (hP : 2 ≤ p) (hQ : 2 ≤ q) (hS : 2 ≤ s)
    (pa : a.IsPrimitive) (pb : b.IsPrimitive) (pc : c.IsPrimitive) (na : a ≠ 1) (nb : b ≠ 1)
    (nc : c ≠ 1) (ia : a⁻¹ ≠ 1) (ib : b⁻¹ ≠ 1) (ic : c⁻¹ ≠ 1) {r : ℝ} (hl : 288 ≤ r) (hu : r ≤ 292)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1)
    (hlog : Real.log p + Real.log q + Real.log s ≤ 4 * r) (ea : a.Even) (eb : b.Even)
    (ec : c.Even) :
    reflectedIntegral570 a (r ^ 2) + reflectedIntegral570 b (r ^ 2) +
        reflectedIntegral570 c (r ^ 2) <
      32711 / 1000000 * r - 954657 / 100000 := by
  let X := (288 : ℝ) ^ 2
  have hx : X ≤ r ^ 2 := pow_le_pow_left₀ (by norm_num only) hl 2
  have htail :=
    positive_tail_upper_570 hG.riemann (show 2701 ≤ X by norm_num only [X])
      (show X ≤ 1000000 by norm_num only [X])
  have hm :=
    quarter_mass_even_570 a b c hP hQ hS (hG p a pa) (hG q b pb) (hG s c pc) pa pb pc na nb nc ia ib
      ic (Finset.Ioc 0 ⌊X⌋₊)
      (fun k hk ↦ ((Nat.le_floor_iff (sq_nonneg (288 : ℝ))).mp (Finset.mem_Ioc.mp hk).2).trans hx)
      ht hA hB hC hlog hG.riemann ea eb ec htail
  have he := radius_tail_numeric_576 (by norm_num only : (287 : ℝ) ≤ 288) (le_refl 288)
  have hc :=
    mass_sub_reflected_lower_584 hG a b c hP hQ hS pa pb pc na nb nc ia ib ic hl hu ht hA hB hC hlog
      ea eb ec
  dsimp only [X] at hm
  dsimp only at hc
  linarith only [hm, he, hc]

end PseudoPrime.PrimeTestBounds.MillerRabin
