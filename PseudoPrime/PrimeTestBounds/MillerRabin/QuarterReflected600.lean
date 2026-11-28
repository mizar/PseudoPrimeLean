/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterReflectedBound570
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterLeftContour570
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterReflectedTriple570
import PseudoPrime.AnalyticNumberTheory.Arithmetic.CharacterAmbientTriviality
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterReflectedBound570
import PseudoPrime.Analysis.LogTaylorBounds

/-! # Reflected Euler bound for section 99 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The signed reflected polynomial is bounded using the right endpoint
for its five negative terms and the left endpoint for the constant term. -/
private theorem reflected_endpoint_99 {z l u L U : ℝ} (hl : 14 ≤ l) (hlz : l ≤ z) (hzu : z ≤ u)
    (hL : L ≤ Real.exp (-(51 / 50 : ℝ) * u)) (hU : Real.exp (-(51 / 50 : ℝ) * l) ≤ U) :
    (51 / 50 : ℝ) ^ 5 / 120 *
        (∑ j ∈ Finset.range 6, (Nat.choose 5 j : ℝ) * scaled (5 - j) z * reflectedCoeff570 j) ≤
      (51 / 50 : ℝ) ^ 5 / 120 *
        (-4.1629 * (L * u ^ 5) - 47.062 * (L * u ^ 4) - 297.408 * (L * u ^ 3) -
            1095.15 * (L * u ^ 2) -
            1597.35 * (L * u) +
          1756.6 * U) := by
  have hz := hl.trans hlz
  have hu := hz.trans hzu
  have hh (k : ℕ) (hk : k ≤ 5) : L * u ^ k ≤ scaled k z :=
    (mul_le_mul_of_nonneg_right hL (pow_nonneg (by linarith only [hu]) k)).trans
      (scaled_anti k hk hz hu hzu)
  have h₅ := hh 5 (by decide)
  have h₄ := hh 4 (by decide)
  have h₃ := hh 3 (by decide)
  have h₂ := hh 2 (by decide)
  have h₁ := hh 1 (by decide)
  have h₀ : scaled 0 z ≤ U :=
    (scaled_anti 0 (by decide) hl hz hlz).trans (by simpa only [scaled, pow_zero, mul_one] using hU)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, Nat.reduceSub,
    Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, reflectedCoeff570, pow_one] at *
  linarith only [h₅, h₄, h₃, h₂, h₁, h₀]

/-- Certified endpoint logs for the two section 99 radius ranges. -/
private theorem reflected_log_endpoints_99 :
    14.15350 ≤ 14 / 5 + 2 * Real.log 292 ∧
      14.20088 ≤ 14 / 5 + 2 * Real.log 299 ∧
      14 / 5 + 2 * Real.log 299 ≤ 14.20090 ∧ 14 / 5 + 2 * Real.log 300 ≤ 14.20758 := by
  have h₁ :=
    (Analysis.rationalLogIntervalCheck_sound (N := 292) (j := 8) (n := 32) (lo := 567675 / 100000)
        (hi := 6) (by decide +kernel)).1
  have h₂ :=
    (Analysis.rationalLogIntervalCheck_sound (N := 299) (j := 8) (n := 32) (lo := 570044 / 100000)
      (hi := 570045 / 100000) (by decide +kernel))
  have h₃ :=
    (Analysis.rationalLogIntervalCheck_sound (N := 300) (j := 8) (n := 32) (lo := 5) (hi :=
        570379 / 100000) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h₁ h₂ h₃
  exact
    ⟨by linarith only [h₁], by linarith only [h₂.1], by linarith only [h₂.2], by linarith only [h₃]⟩

/-- Certified exponential values at the outer endpoints for the signed polynomial. -/
private theorem reflected_exp_endpoints_99 :
    Real.exp (-(51 / 50 : ℝ) * 14.15350) ≤ 53738 / 100000000000 ∧
      51201 / 100000000000 ≤ Real.exp (-(51 / 50 : ℝ) * 14.20090) ∧
      Real.exp (-(51 / 50 : ℝ) * 14.20088) ≤ 51203 / 100000000000 ∧
      50853 / 100000000000 ≤ Real.exp (-(51 / 50 : ℝ) * 14.20758) := by
  have h₁ :=
    (Analysis.rationalLogIntervalCheck_sound (N := 100000000000 / 53738) (j := 21) (n := 32) (lo :=
        14) (hi := 51 / 50 * 14.15350) (by decide +kernel)).2
  have h₂ :=
    (Analysis.rationalLogIntervalCheck_sound (N := 100000000000 / 51201) (j := 21) (n := 32) (lo :=
        51 / 50 * 14.20090) (hi := 15) (by decide +kernel)).1
  have h₃ :=
    (Analysis.rationalLogIntervalCheck_sound (N := 100000000000 / 51203) (j := 21) (n := 32) (lo :=
        14) (hi := 51 / 50 * 14.20088) (by decide +kernel)).2
  have h₄ :=
    (Analysis.rationalLogIntervalCheck_sound (N := 100000000000 / 50853) (j := 21) (n := 32) (lo :=
        51 / 50 * 14.20758) (hi := 15) (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_mul, Rat.cast_ofScientific] at h₁ h₂ h₃ h₄
  have upper {x N : ℝ} (hN : 0 < N) (h : Real.log N ≤ x) : Real.exp (-x) ≤ N⁻¹ := by
    rw [Real.exp_neg]
    exact (inv_le_inv₀ (Real.exp_pos _) hN).2 ((Real.log_le_iff_le_exp hN).1 h)
  have lower {x N : ℝ} (hN : 0 < N) (h : x ≤ Real.log N) : N⁻¹ ≤ Real.exp (-x) := by
    rw [Real.exp_neg]
    exact (inv_le_inv₀ hN (Real.exp_pos _)).2 ((Real.le_log_iff_exp_le hN).1 h)
  simp only [neg_mul]
  constructor
  · have h :=
      upper (x := (51 / 50) * 14.15350) (N := 100000000000 / 53738) (by norm_num only)
        (by linarith only [h₁])
    exact h.trans_eq (by norm_num only)
  constructor
  · have h :=
      lower (x := (51 / 50) * 14.20090) (N := 100000000000 / 51201) (by norm_num only)
        (by linarith only [h₂])
    exact (by norm_num only : (51201 / 100000000000 : ℝ) = (100000000000 / 51201)⁻¹).trans_le h
  constructor
  · have h :=
      upper (x := (51 / 50) * 14.20088) (N := 100000000000 / 51203) (by norm_num only)
        (by linarith only [h₃])
    exact h.trans_eq (by norm_num only)
  · have h :=
      lower (x := (51 / 50) * 14.20758) (N := 100000000000 / 50853) (by norm_num only)
        (by linarith only [h₄])
    exact (by norm_num only : (50853 / 100000000000 : ℝ) = (100000000000 / 50853)⁻¹).trans_le h

/-- Bound the reflected sum with the scaled signed polynomial at the
logarithmic endpoints. The known prime-power prefix supplies its coefficients. -/
theorem reflected_shifted_box {z l u L U C : ℝ} (hl : 14 ≤ l) (hlz : l ≤ z) (hzu : z ≤ u)
    (hL : L ≤ Real.exp (-(51 / 50) * u)) (hU : Real.exp (-(51 / 50) * l) ≤ U)
    (hcap :
      (51 / 50 : ℝ) ^ 5 / 120 *
          (-4.1629 * (L * u ^ 5) - 47.062 * (L * u ^ 4) - 297.408 * (L * u ^ 3) -
              1095.15 * (L * u ^ 2) -
              1597.35 * (L * u) +
            1756.6 * U) <
        C)
    (hRH : RiemannHypothesis) (τ : ℕ → ℝ) (ht : ∀ n, -1 ≤ τ n ∧ τ n ≤ 3)
    (hp : ∀ n ∈ Finset.Ioc 0 2701, ArithmeticFunction.vonMangoldt n ≠ 0 → τ n = 3) :
    (51 / 50 : ℝ) ^ 5 / 120 * Real.exp (-(51 / 50) * z) *
        (-(∑' n : ℕ, τ n * reflectedWeight570 z n)) <
      C := by
  have hz : 0 ≤ z := by linarith only [hl, hlz]
  have h := reflected_polynomial_570 hRH hz τ ht hp
  have hc :=
    Finset.sum_le_sum (s := Finset.range 6)
      (fun j hj ↦
        mul_le_mul_of_nonneg_left
          (reflected_coeff_le_570 j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
          (mul_nonneg (Nat.cast_nonneg (Nat.choose 5 j)) (pow_nonneg hz (5 - j))))
  apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left (h.trans hc) (by positivity))
  rw [mul_assoc, Finset.mul_sum]
  have hd (j : ℕ) :
    Real.exp (-(51 / 50 : ℝ) * z) * ((Nat.choose 5 j : ℝ) * z ^ (5 - j) * reflectedCoeff570 j) =
      (Nat.choose 5 j : ℝ) * scaled (5 - j) z * reflectedCoeff570 j := by
    unfold scaled
    ring
  simp only [hd]
  exact (reflected_endpoint_99 hl hlz hzu hL hU).trans_lt hcap

/-- On the full section 107 interval, the reflected sum with its
negative sign is strictly below minus 0.02385. -/
theorem section107_reflected_shifted {r : ℝ} (hr : r ∈ Set.Icc 300 313) (hRH : RiemannHypothesis)
    (τ : ℕ → ℝ) (ht : ∀ n, -1 ≤ τ n ∧ τ n ≤ 3)
    (hp : ∀ n ∈ Finset.Ioc 0 2701, ArithmeticFunction.vonMangoldt n ≠ 0 → τ n = 3) :
    let z := 14 / 5 + 2 * Real.log r
    (51 / 50 : ℝ) ^ 5 / 120 * Real.exp (-(51 / 50) * z) *
        (-(∑' n : ℕ, τ n * reflectedWeight570 z n)) <
      -0.02385 := by
  intro z
  have hr₀ : 0 < r := by linarith only [hr.1]
  have ha :=
    (Analysis.rationalLogIntervalCheck_sound (N := 300) (j := 8) (n := 32) (lo := 570378 / 100000)
        (hi := 6) (by decide +kernel)).1
  have hb :=
    (Analysis.rationalLogIntervalCheck_sound (N := 313) (j := 8) (n := 32) (lo := 5) (hi :=
        57462032 / 10000000) (by decide +kernel)).2
  have hc :=
    (Analysis.rationalLogIntervalCheck_sound (N := 10 ^ 13 / 4663848) (j := 21) (n := 32) (lo :=
        51 / 50 * 14.2924064) (hi := 15) (by decide +kernel)).1
  have hd :=
    (Analysis.rationalLogIntervalCheck_sound (N := 10 ^ 12 / 508546) (j := 21) (n := 32) (lo := 14)
        (hi := 51 / 50 * 14.20756) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow, Rat.cast_mul,
    Rat.cast_ofScientific] at ha hb hc hd
  have hlz : 14.20756 ≤ z := by
    dsimp only [z]
    linarith only [ha, Real.log_le_log (by norm_num only) hr.1]
  have hzu : z ≤ 14.2924064 := by
    dsimp only [z]
    linarith only [hb, Real.log_le_log hr₀ hr.2]
  have hL : (4663848 / 10 ^ 13 : ℝ) ≤ Real.exp (-(51 / 50) * 14.2924064) := by
    rw [neg_mul, Real.exp_neg,
      show (4663848 / 10 ^ 13 : ℝ) = (10 ^ 13 / 4663848)⁻¹ by norm_num only]
    exact
      (inv_le_inv₀ (by norm_num only) (Real.exp_pos _)).2
        ((Real.le_log_iff_exp_le (by norm_num only)).1 (by linarith only [hc]))
  have hU : Real.exp (-(51 / 50 : ℝ) * 14.20756) ≤ 508546 / 10 ^ 12 := by
    rw [neg_mul, Real.exp_neg, show (508546 / 10 ^ 12 : ℝ) = (10 ^ 12 / 508546)⁻¹ by norm_num only]
    exact
      (inv_le_inv₀ (Real.exp_pos _) (by norm_num only)).2
        ((Real.log_le_iff_le_exp (by norm_num only)).1 (by linarith only [hd]))
  exact reflected_shifted_box (by norm_num only) hlz hzu hL hU (by norm_num only) hRH τ ht hp

/-- Section 99's two signed reflected bounds hold throughout their
radius ranges by applying the certified endpoint comparison to all six terms. -/
theorem section99_reflected_shifted {r : ℝ} (hl : 292 ≤ r) (hu : r ≤ 300) (hRH : RiemannHypothesis)
    (τ : ℕ → ℝ) (ht : ∀ n, -1 ≤ τ n ∧ τ n ≤ 3)
    (hp : ∀ n ∈ Finset.Ioc 0 2701, ArithmeticFunction.vonMangoldt n ≠ 0 → τ n = 3) :
    let z := 14 / 5 + 2 * Real.log r
    (51 / 50 : ℝ) ^ 5 / 120 * Real.exp (-(51 / 50) * z) *
        (-(∑' n : ℕ, τ n * reflectedWeight570 z n)) <
      -(if r ≤ 299 then 0.02549 else 0.02537) := by
  intro z
  have hr : 0 < r := by linarith only [hl]
  obtain ⟨hl₂, hl₉, hu₉, hu₀⟩ := reflected_log_endpoints_99
  obtain ⟨hU₂, hL₉, hU₉, hL₀⟩ := reflected_exp_endpoints_99
  have ha : 14.15350 ≤ z := by
    dsimp only [z]
    linarith only [hl₂, Real.log_le_log (by norm_num only) hl]
  have hz : 0 ≤ z := by linarith only [ha]
  have h := reflected_polynomial_570 hRH hz τ ht hp
  have hc :=
    Finset.sum_le_sum (s := Finset.range 6)
      (fun j hj ↦
        mul_le_mul_of_nonneg_left
          (reflected_coeff_le_570 j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
          (mul_nonneg (Nat.cast_nonneg (Nat.choose 5 j)) (pow_nonneg hz (5 - j))))
  apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left (h.trans hc) (by positivity))
  rw [mul_assoc, Finset.mul_sum]
  have hd (j : ℕ) :
    Real.exp (-(51 / 50 : ℝ) * z) * ((Nat.choose 5 j : ℝ) * z ^ (5 - j) * reflectedCoeff570 j) =
      (Nat.choose 5 j : ℝ) * scaled (5 - j) z * reflectedCoeff570 j := by
    unfold scaled
    ring
  simp only [hd]
  split_ifs with h299
  · have hb : z ≤ 14.20090 := by
      dsimp only [z]
      linarith only [hu₉, Real.log_le_log hr h299]
    exact (reflected_endpoint_99 (by norm_num only) ha hb hL₉ hU₂).trans_lt (by norm_num only)
  · have ha' : 14.20088 ≤ z := by
      dsimp only [z]
      linarith only [hl₉, Real.log_le_log (by norm_num only) (le_of_lt (lt_of_not_ge h299))]
    have hb : z ≤ 14.20758 := by
      dsimp only [z]
      linarith only [hu₀, Real.log_le_log hr hu]
    exact (reflected_endpoint_99 (by norm_num only) ha' hb hL₀ hU₉).trans_lt (by norm_num only)

/-- Under RH, if three characters are one at primes through the squared radius and their
real sum is at least minus one, their signed reflected kernel series satisfies the
section 99 bounds for radii from 292 through 300. Prime-power support gives the prefix sign. -/
theorem section99_reflected_triple_kernel (hRH : RiemannHypothesis) {p q s : ℕ} {r : ℝ}
    (hl : 292 ≤ r) (hu : r ≤ 300) (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q)
    (c : DirichletCharacter ℂ s) (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) :
    -(∑' n : ℕ,
          ((a n).re + (b n).re + (c n).re) *
            (ArithmeticFunction.vonMangoldt n / Real.sqrt n *
              (quarterKernel570.transform (((n : ℝ) * r ^ 2)⁻¹)).re)) <
      -(if r ≤ 299 then 0.02549 else 0.02537) := by
  let τ := fun n : ℕ ↦ (a n).re + (b n).re + (c n).re
  have hsign (n : ℕ) : -1 ≤ τ n ∧ τ n ≤ 3 := by
    refine ⟨ht n, ?_⟩
    dsimp only [τ]
    linarith only [(Complex.re_le_norm _).trans (a.norm_le_one n),
      (Complex.re_le_norm _).trans (b.norm_le_one n),
      (Complex.re_le_norm _).trans (c.norm_le_one n)]
  have hone {m : ℕ} (χ : DirichletCharacter ℂ m) (hχ : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → χ l = 1)
    {n : ℕ} (hn : n ∈ Finset.Ioc 0 2701) (hv : ArithmeticFunction.vonMangoldt n ≠ 0) : χ n = 1 := by
    have hn' : (n : ℝ) ≤ 2701 := by exact_mod_cast (Finset.mem_Ioc.mp hn).2
    have hx := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 292) hl 2
    exact
      AnalyticNumberTheory.Arithmetic.character_eq_one_of_ambient_mangoldt (N := 1) χ
        (fun l hl hlX _ ↦ hχ l hl hlX) (by linarith only [hx, hn']) (Nat.coprime_one_right n) hv
  have hprefix (n : ℕ) (hn : n ∈ Finset.Ioc 0 2701) (hv : ArithmeticFunction.vonMangoldt n ≠ 0) :
    τ n = 3 := by
    dsimp only [τ]
    rw [hone a hA hn hv, hone b hB hn hv, hone c hC hn hv, Complex.one_re]
    norm_num only
  have h := section99_reflected_shifted hl hu hRH τ hsign hprefix
  dsimp only at h
  let C := ((51 / 50 : ℝ) ^ 5 / 120 * Real.exp (-(51 / 50) * (14 / 5))) * r ^ (-(2 * (51 / 50 : ℝ)))
  change -(∑' n : ℕ, τ n * _) < _
  simp_rw [reflected_kernel_term_570 (show 1 ≤ r by linarith only [hl])]
  change -(∑' n : ℕ, τ n * (C * reflectedWeight570 _ n)) < _
  simp_rw [mul_left_comm (τ _) C, tsum_mul_left, ← mul_neg]
  dsimp only [C]
  rw [Real.rpow_def_of_pos (by linarith only [hl] : 0 < r), mul_assoc _ (Real.exp _) (Real.exp _), ←
    Real.exp_add]
  convert h using 4
  ring

/-- For three characters satisfying the prime-prefix and sign conditions, the negative
sum of their reflected integrals at a square cutoff satisfies the section 99 bounds throughout
the radius interval. Add the three absolutely convergent kernel series. -/
theorem section99_reflected_integrals (hRH : RiemannHypothesis) {p q s : ℕ} [NeZero p] [NeZero q]
    [NeZero s] {r : ℝ} (hl : 292 ≤ r) (hu : r ≤ 300) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) :
    -(reflectedIntegral570 a (r ^ 2) + reflectedIntegral570 b (r ^ 2) +
          reflectedIntegral570 c (r ^ 2)) <
      -(if r ≤ 299 then 0.02549 else 0.02537) := by
  have hx := sq_pos_of_pos (show 0 < r by linarith only [hl])
  have h :=
    ((reflected_hasSum_570 a hx).add (reflected_hasSum_570 b hx)).add (reflected_hasSum_570 c hx)
  have he := h.tsum_eq
  simp only [← add_mul] at he
  rw [← he]
  exact section99_reflected_triple_kernel hRH hl hu a b c ht hA hB hC

/-- Under RH, if three characters are one at primes through the squared radius and their
real sum is at least minus one, their signed reflected kernel series satisfies the
section 99 bounds for radii from 292 through 300. Prime-power support gives the prefix sign. -/
theorem section107_reflected_triple_kernel (hRH : RiemannHypothesis) {p q s : ℕ} {r : ℝ}
    (hr : r ∈ Set.Icc 300 313) (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q)
    (c : DirichletCharacter ℂ s) (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) :
    -(∑' n : ℕ,
          ((a n).re + (b n).re + (c n).re) *
            (ArithmeticFunction.vonMangoldt n / Real.sqrt n *
              (quarterKernel570.transform (((n : ℝ) * r ^ 2)⁻¹)).re)) <
      -0.02385 := by
  let τ := fun n : ℕ ↦ (a n).re + (b n).re + (c n).re
  have hsign (n : ℕ) : -1 ≤ τ n ∧ τ n ≤ 3 := by
    refine ⟨ht n, ?_⟩
    dsimp only [τ]
    linarith only [(Complex.re_le_norm _).trans (a.norm_le_one n),
      (Complex.re_le_norm _).trans (b.norm_le_one n),
      (Complex.re_le_norm _).trans (c.norm_le_one n)]
  have hone {m : ℕ} (χ : DirichletCharacter ℂ m) (hχ : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → χ l = 1)
    {n : ℕ} (hn : n ∈ Finset.Ioc 0 2701) (hv : ArithmeticFunction.vonMangoldt n ≠ 0) : χ n = 1 := by
    have hn' : (n : ℝ) ≤ 2701 := by exact_mod_cast (Finset.mem_Ioc.mp hn).2
    have hx := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 300) hr.1 2
    exact
      AnalyticNumberTheory.Arithmetic.character_eq_one_of_ambient_mangoldt (N := 1) χ
        (fun l hl hlX _ ↦ hχ l hl hlX) (by linarith only [hx, hn']) (Nat.coprime_one_right n) hv
  have hprefix (n : ℕ) (hn : n ∈ Finset.Ioc 0 2701) (hv : ArithmeticFunction.vonMangoldt n ≠ 0) :
    τ n = 3 := by
    dsimp only [τ]
    rw [hone a hA hn hv, hone b hB hn hv, hone c hC hn hv, Complex.one_re]
    norm_num only
  have h := section107_reflected_shifted hr hRH τ hsign hprefix
  dsimp only at h
  let C := ((51 / 50 : ℝ) ^ 5 / 120 * Real.exp (-(51 / 50) * (14 / 5))) * r ^ (-(2 * (51 / 50 : ℝ)))
  change -(∑' n : ℕ, τ n * _) < _
  simp_rw [reflected_kernel_term_570 (show 1 ≤ r by linarith only [hr.1])]
  change -(∑' n : ℕ, τ n * (C * reflectedWeight570 _ n)) < _
  simp_rw [mul_left_comm (τ _) C, tsum_mul_left, ← mul_neg]
  dsimp only [C]
  rw [Real.rpow_def_of_pos (by linarith only [hr.1] : 0 < r), mul_assoc _ (Real.exp _) (Real.exp _),
    ← Real.exp_add]
  convert h using 4
  ring

/-- For three characters satisfying the prime-prefix and sign conditions, the negative
sum of their reflected integrals at a square cutoff satisfies the section 107 bound throughout
the radius interval. Add the three absolutely convergent kernel series. -/
theorem section107_reflected_integrals (hRH : RiemannHypothesis) {p q s : ℕ} [NeZero p] [NeZero q]
    [NeZero s] {r : ℝ} (hr : r ∈ Set.Icc 300 313) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) :
    -(reflectedIntegral570 a (r ^ 2) + reflectedIntegral570 b (r ^ 2) +
          reflectedIntegral570 c (r ^ 2)) <
      -0.02385 := by
  have hx := sq_pos_of_pos (show 0 < r by linarith only [hr.1])
  have h :=
    ((reflected_hasSum_570 a hx).add (reflected_hasSum_570 b hx)).add (reflected_hasSum_570 c hx)
  have he := h.tsum_eq
  simp only [← add_mul] at he
  rw [← he]
  exact section107_reflected_triple_kernel hRH hr a b c ht hA hB hC

end PseudoPrime.PrimeTestBounds.MillerRabin
