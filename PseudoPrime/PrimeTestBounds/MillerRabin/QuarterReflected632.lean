/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterReflected600
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterReflected600
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterReflectedBound570
import all PseudoPrime.Analysis.LogTaylorBounds
import PseudoPrime.AnalyticNumberTheory.Arithmetic.CharacterAmbientTriviality
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseBoxes117

/-! # Signed reflected Euler bound for section 107 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A right-endpoint cap for the reflected polynomial bounds the signed Euler sum. -/
theorem reflected_shifted_of_cap {r u L C : ℝ} (hl : 313 ≤ r) (hb : 14 / 5 + 2 * Real.log r ≤ u)
    (hL : L ≤ Real.exp (-(51 / 50) * u))
    (hcap :
      (51 / 50 : ℝ) ^ 5 / 120 *
          (-4.1629 * (L * u ^ 5) - 47.062 * (L * u ^ 4) - 297.408 * (L * u ^ 3) -
              1095.15 * (L * u ^ 2) -
              1597.35 * (L * u) +
            1756.6 / 2144100) <
        C)
    (hRH : RiemannHypothesis) (τ : ℕ → ℝ) (ht : ∀ n, -1 ≤ τ n ∧ τ n ≤ 3)
    (hp : ∀ n ∈ Finset.Ioc 0 2701, ArithmeticFunction.vonMangoldt n ≠ 0 → τ n = 3) :
    let z := 14 / 5 + 2 * Real.log r
    (51 / 50 : ℝ) ^ 5 / 120 * Real.exp (-(51 / 50) * z) *
        (-(∑' n : ℕ, τ n * reflectedWeight570 z n)) <
      C := by
  intro z
  have hr : 0 < r := by linarith only [hl]
  have hl₀ :=
    (Analysis.rationalLogIntervalCheck_sound (N := 313) (j := 8) (n := 32) (lo :=
        574620318 / 100000000) (hi := 6) (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hl₀
  have ha : 14.29240636 ≤ z := by
    dsimp only [z]
    linarith only [hl₀, Real.log_le_log (by norm_num only) hl]
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
  have hlogU :=
    (Analysis.rationalLogIntervalCheck_sound (N := 2144100) (j := 21) (n := 24) (lo := 14) (hi :=
        14578240 / 1000000) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlogU
  have hU : Real.exp (-(51 / 50) * 14.29240636) ≤ (1 / 2144100 : ℝ) := by
    rw [neg_mul, Real.exp_neg, one_div]
    exact
      inv_le_inv₀ (Real.exp_pos _) (by norm_num only) |>.2
        ((Real.log_le_iff_le_exp (by norm_num only)).1 (by linarith only [hlogU]))
  apply (reflected_endpoint_99 (by norm_num only) ha hb hL hU).trans_lt
  simpa only [mul_one_div] using hcap

/-- The signed reflected sum is below -0.02352 across the radius interval from 313 to 316.
The five negative terms use the right endpoint and the positive term the left. -/
theorem reflected_shifted_632 {r : ℝ} (hl : 313 ≤ r) (hu : r ≤ 316) (hRH : RiemannHypothesis)
    (τ : ℕ → ℝ) (ht : ∀ n, -1 ≤ τ n ∧ τ n ≤ 3)
    (hp : ∀ n ∈ Finset.Ioc 0 2701, ArithmeticFunction.vonMangoldt n ≠ 0 → τ n = 3) :
    let z := 14 / 5 + 2 * Real.log r
    (51 / 50 : ℝ) ^ 5 / 120 * Real.exp (-(51 / 50) * z) *
        (-(∑' n : ℕ, τ n * reflectedWeight570 z n)) <
      -0.02352 := by
  have hr : 0 < r := by linarith only [hl]
  have hu₀ :=
    (Analysis.rationalLogIntervalCheck_sound (N := 316) (j := 8) (n := 32) (lo := 5) (hi :=
        575574222 / 100000000) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hu₀
  have hb : 14 / 5 + 2 * Real.log r ≤ 14.31148444 := by linarith only [hu₀, Real.log_le_log hr hu]
  have hlogL :=
    (Analysis.rationalLogIntervalCheck_sound (N := 2186300) (j := 21) (n := 24) (lo :=
        14597720 / 1000000) (hi := 15) (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlogL
  have hL : (1 / 2186300 : ℝ) ≤ Real.exp (-(51 / 50) * 14.31148444) := by
    rw [neg_mul, Real.exp_neg, one_div]
    exact
      inv_le_inv₀ (by norm_num only) (Real.exp_pos _) |>.2
        ((Real.le_log_iff_exp_le (by norm_num only)).1 (by linarith only [hlogL]))
  exact reflected_shifted_of_cap hl hb hL (by norm_num only) hRH τ ht hp

/-- The reflected polynomial cap transfers to the three passing character terms. -/
theorem reflected_triple_kernel_of_cap (hRH : RiemannHypothesis) {p q s : ℕ} {r u L C : ℝ}
    (hl : 313 ≤ r) (hu : 14 / 5 + 2 * Real.log r ≤ u) (hL : L ≤ Real.exp (-(51 / 50) * u))
    (hcap :
      (51 / 50 : ℝ) ^ 5 / 120 *
          (-4.1629 * (L * u ^ 5) - 47.062 * (L * u ^ 4) - 297.408 * (L * u ^ 3) -
              1095.15 * (L * u ^ 2) -
              1597.35 * (L * u) +
            1756.6 / 2144100) <
        C)
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) :
    -(∑' n : ℕ,
          ((a n).re + (b n).re + (c n).re) *
            (ArithmeticFunction.vonMangoldt n / Real.sqrt n *
              (quarterKernel570.transform (((n : ℝ) * r ^ 2)⁻¹)).re)) <
      C := by
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
    have hx := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 313) hl 2
    exact
      AnalyticNumberTheory.Arithmetic.character_eq_one_of_ambient_mangoldt (N := 1) χ
        (fun l hl hlX _ ↦ hχ l hl hlX) (by linarith only [hx, hn']) (Nat.coprime_one_right n) hv
  have hprefix (n : ℕ) (hn : n ∈ Finset.Ioc 0 2701) (hv : ArithmeticFunction.vonMangoldt n ≠ 0) :
    τ n = 3 := by
    dsimp only [τ]
    rw [hone a hA hn hv, hone b hB hn hv, hone c hC hn hv, Complex.one_re]
    norm_num only
  have h := reflected_shifted_of_cap hl hu hL hcap hRH τ hsign hprefix
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

/-- Under RH, if three characters are one at primes through the squared radius and their
real sum is at least minus one, their signed reflected kernel series satisfies the
radius 316 bound for radii from 313 through 316. Prime-power support gives the prefix sign. -/
theorem reflected_triple_kernel_632 (hRH : RiemannHypothesis) {p q s : ℕ} {r : ℝ} (hl : 313 ≤ r)
    (hu : r ≤ 316) (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q)
    (c : DirichletCharacter ℂ s) (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) :
    -(∑' n : ℕ,
          ((a n).re + (b n).re + (c n).re) *
            (ArithmeticFunction.vonMangoldt n / Real.sqrt n *
              (quarterKernel570.transform (((n : ℝ) * r ^ 2)⁻¹)).re)) <
      -0.02352 := by
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
    have hx := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 313) hl 2
    exact
      AnalyticNumberTheory.Arithmetic.character_eq_one_of_ambient_mangoldt (N := 1) χ
        (fun l hl hlX _ ↦ hχ l hl hlX) (by linarith only [hx, hn']) (Nat.coprime_one_right n) hv
  have hprefix (n : ℕ) (hn : n ∈ Finset.Ioc 0 2701) (hv : ArithmeticFunction.vonMangoldt n ≠ 0) :
    τ n = 3 := by
    dsimp only [τ]
    rw [hone a hA hn hv, hone b hB hn hv, hone c hC hn hv, Complex.one_re]
    norm_num only
  have h := reflected_shifted_632 hl hu hRH τ hsign hprefix
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

/-- The reflected polynomial cap transfers to the three passing character terms. -/
theorem reflected_integrals_of_cap (hRH : RiemannHypothesis) {p q s : ℕ} [NeZero p] [NeZero q]
    [NeZero s] {r u L C : ℝ} (hl : 313 ≤ r) (hu : 14 / 5 + 2 * Real.log r ≤ u)
    (hL : L ≤ Real.exp (-(51 / 50) * u))
    (hcap :
      (51 / 50 : ℝ) ^ 5 / 120 *
          (-4.1629 * (L * u ^ 5) - 47.062 * (L * u ^ 4) - 297.408 * (L * u ^ 3) -
              1095.15 * (L * u ^ 2) -
              1597.35 * (L * u) +
            1756.6 / 2144100) <
        C)
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) :
    -(reflectedIntegral570 a (r ^ 2) + reflectedIntegral570 b (r ^ 2) +
          reflectedIntegral570 c (r ^ 2)) <
      C := by
  have hx := sq_pos_of_pos (show 0 < r by linarith only [hl])
  have h :=
    ((reflected_hasSum_570 a hx).add (reflected_hasSum_570 b hx)).add (reflected_hasSum_570 c hx)
  have he := h.tsum_eq
  simp only [← add_mul] at he
  rw [← he]
  exact reflected_triple_kernel_of_cap hRH hl hu hL hcap a b c ht hA hB hC

/-- For three characters satisfying the prime-prefix and sign conditions, the negative
sum of their reflected integrals at a square cutoff satisfies the radius 316 bound throughout
the radius interval. Add the three absolutely convergent kernel series. -/
theorem reflected_integrals_632 (hRH : RiemannHypothesis) {p q s : ℕ} [NeZero p] [NeZero q]
    [NeZero s] {r : ℝ} (hl : 313 ≤ r) (hu : r ≤ 316) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) :
    -(reflectedIntegral570 a (r ^ 2) + reflectedIntegral570 b (r ^ 2) +
          reflectedIntegral570 c (r ^ 2)) <
      -0.02352 := by
  have hx := sq_pos_of_pos (show 0 < r by linarith only [hl])
  have h :=
    ((reflected_hasSum_570 a hx).add (reflected_hasSum_570 b hx)).add (reflected_hasSum_570 c hx)
  have he := h.tsum_eq
  simp only [← add_mul] at he
  rw [← he]
  exact reflected_triple_kernel_632 hRH hl hu a b c ht hA hB hC

private theorem reflected_cap_628_1 : (1 / 2152576 : ℝ) ≤ Real.exp (-(51 / 50) * 14.29623712) := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound (N := 2152576) (j := 21) (n := 24) (lo :=
        1458217581 / 10 ^ 8) (hi := 15) (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow] at h
  rw [neg_mul, Real.exp_neg, one_div]
  exact
    (inv_le_inv₀ (by norm_num only) (Real.exp_pos _)).2
      ((Real.le_log_iff_exp_le (by norm_num only)).1 (by linarith only [h]))

private theorem reflected_cap_628_2 : (1 / 2158180 : ℝ) ≤ Real.exp (-(51 / 50) * 14.298786) := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound (N := 2158180) (j := 21) (n := 24) (lo :=
        1458477582 / 10 ^ 8) (hi := 15) (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow] at h
  rw [neg_mul, Real.exp_neg, one_div]
  exact
    (inv_le_inv₀ (by norm_num only) (Real.exp_pos _)).2
      ((Real.le_log_iff_exp_le (by norm_num only)).1 (by linarith only [h]))

/-- Reflected Euler recovery on the two radius intervals in the two-frequency comparison. -/
theorem reflected_integrals_628 (hRH : RiemannHypothesis) {p q s : ℕ} [NeZero p] [NeZero q]
    [NeZero s] {r : ℝ} (hl : 313 ≤ r) (hu : r ≤ 314) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) :
    -(reflectedIntegral570 a (r ^ 2) + reflectedIntegral570 b (r ^ 2) +
          reflectedIntegral570 c (r ^ 2)) <
      if r ≤ 1568 / 5 then -0.02378 else -0.02374 := by
  have hr : 0 < r := by linarith only [hl]
  by_cases h : r ≤ 1568 / 5
  · rw [ite_eq_left h]
    have hb :=
      (Analysis.rationalLogIntervalCheck_sound (N := 98345) (j := 16) (n := 48) (lo := 11) (hi :=
          114962371 / 10000000) (by decide +kernel)).2
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at hb
    have hx :=
      Real.log_le_log (sq_pos_of_pos hr)
        ((pow_le_pow_left₀ hr.le h 2).trans (by norm_num only : ((1568 / 5 : ℝ) ^ 2) ≤ 98345))
    rw [Real.log_pow, Nat.cast_ofNat] at hx
    have hz : 14 / 5 + 2 * Real.log r ≤ 14.29623712 := by linarith only [hx, hb]
    exact
      reflected_integrals_of_cap hRH hl hz reflected_cap_628_1 (by norm_num only) a b c ht hA hB hC
  · rw [ite_eq_right h]
    have hb :=
      (Analysis.rationalLogIntervalCheck_sound (N := 314) (j := 8) (n := 32) (lo := 5) (hi :=
          574939299 / 100000000) (by decide +kernel)).2
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at hb
    have hz : 14 / 5 + 2 * Real.log r ≤ 14.298786 := by linarith only [Real.log_le_log hr hu, hb]
    exact
      reflected_integrals_of_cap hRH hl hz reflected_cap_628_2 (by norm_num only) a b c ht hA hB hC

private theorem reflected_factor_314_45 :
    (1 / 2164489 : ℝ) ≤ Real.exp (-(51 / 50) * 14.30165018) := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound (N := 2164489) (j := 21) (n := 24) (lo :=
        1458769485 / 10 ^ 8) (hi := 15) (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow] at h
  rw [neg_mul, Real.exp_neg, one_div]
  exact
    (inv_le_inv₀ (by norm_num only) (Real.exp_pos _)).2
      ((Real.le_log_iff_exp_le (by norm_num only)).1 (by linarith only [h]))

/-- The first section 117 row retains a reflected recovery of 0.02369. -/
theorem reflected_integrals_314_45 (hRH : RiemannHypothesis) {p q s : ℕ} [NeZero p] [NeZero q]
    [NeZero s] {r : ℝ} (hl : 313 ≤ r) (hu : r ≤ 6289 / 20) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) :
    -(reflectedIntegral570 a (r ^ 2) + reflectedIntegral570 b (r ^ 2) +
          reflectedIntegral570 c (r ^ 2)) <
      -0.02369 := by
  have hr : 0 < r := by linarith only [hl]
  have hz : 14 / 5 + 2 * Real.log r ≤ 14.30165018 := by
    linarith only [Real.log_le_log hr hu, section117_log_box_314_45.2]
  exact
    reflected_integrals_of_cap hRH hl hz reflected_factor_314_45 (by norm_num only) a b c ht hA hB
      hC

end PseudoPrime.PrimeTestBounds.MillerRabin
