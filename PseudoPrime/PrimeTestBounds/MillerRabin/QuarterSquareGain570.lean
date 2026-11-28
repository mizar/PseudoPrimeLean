/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterOdd574

/-! # Uniform finite lower bound for the section 31 square contribution -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem log_trapezoid {y : ℝ} (hy : 1 ≤ y) : 2 * Real.log y ≤ y - y⁻¹ := by
  let f := fun t : ℝ ↦ t - t⁻¹ - 2 * Real.log t
  have hd {t : ℝ} (ht : 0 < t) : HasDerivAt f (1 - -(t ^ 2)⁻¹ - 2 * t⁻¹) t := by
    convert
      (((hasDerivAt_id t).sub (hasDerivAt_inv ht.ne')).sub
        ((Real.hasDerivAt_log ht.ne').const_mul 2)) using
      1
    funext u
    rfl
  have hm : MonotoneOn f (Set.Ici 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _)
    · exact fun t ht ↦ (hd (zero_lt_one.trans_le ht)).continuousAt.continuousWithinAt
    · intro t ht
      exact (hd (zero_lt_one.trans_le (interior_subset ht))).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hd (zero_lt_one.trans_le (interior_subset ht))).deriv, ← inv_pow]
      nlinarith only [sq_nonneg (1 - t⁻¹)]
  have h := hm (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hy) hy
  simp only [f, inv_one, Real.log_one, mul_zero, sub_self] at h
  linarith only [h]

/-- A rational upper bound for the decrease in the square weight's log coordinate.
The endpoint radius 278 gives the largest ratio in the section 31 interval. -/
private def dropBound (k : ℕ) : ℚ :=
  51 / 50 * ((k : ℚ) / 278 - 278 / k)

/-- Four times a rational lower estimate for a prime square's principal weight.
The cubic Taylor polynomial bounds the exponential factor from below. -/
private def squareCredit (k : ℕ) : ℚ :=
  let z := dropBound k
  4 * (565 / 100) / k * (357 / 125 - z) ^ 5 * (1 + z + z ^ 2 / 2 + z ^ 3 / 6) / (174 / 10) / 120

private def squarePrimes :=
  (Finset.Ioc 285 600).filter Nat.Prime

private theorem credit_sum : 982 / 10000 < ∑ k ∈ squarePrimes, squareCredit k := by decide +kernel

private theorem drop_bounds (k : ℕ) (hk : k ∈ squarePrimes) :
    0 ≤ dropBound k ∧ dropBound k ≤ 357 / 125 := by
  exact
    (show ∀ j ∈ squarePrimes, 0 ≤ dropBound j ∧ dropBound j ≤ 357 / 125 from by decide +kernel) k hk

private theorem log_square_upper {r : ℝ} (hl : 278 ≤ r) {k : ℕ} (hk : k ∈ squarePrimes) :
    51 / 50 * Real.log ((k : ℝ) ^ 2 / r ^ 2) ≤ (dropBound k : ℝ) := by
  have hn := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hk).1).1
  have hkr : (278 : ℝ) ≤ k := by exact_mod_cast (le_trans (by decide : 278 ≤ 285) hn.le)
  have hr : 0 < r := by linarith only [hl]
  have h1 := log_trapezoid ((one_le_div (by norm_num only : (0 : ℝ) < 278)).mpr hkr)
  have h2 :=
    Real.log_le_log (div_pos (by linarith only [hkr]) hr)
      (div_le_div_of_nonneg_left (by linarith only [hkr]) (by norm_num only) hl)
  rw [← div_pow, Real.log_pow]
  simp only [dropBound, Rat.cast_mul, Rat.cast_sub, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    inv_div] at *
  norm_num only [Nat.cast_ofNat] at *
  linarith only [h1, h2]

private theorem fifth_increasing :
    MonotoneOn (fun t : ℝ ↦ t ^ 5 * Real.exp (-t)) (Set.Icc 0 5) := by
  have hd (t : ℝ) :=
    ((hasDerivAt_pow 5 t).mul (Real.hasDerivAt_exp _ |>.comp t (hasDerivAt_id t).neg))
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · exact fun t _ ↦ (hd t).continuousAt.continuousWithinAt
  · exact fun t _ ↦ (hd t).differentiableAt.differentiableWithinAt
  · intro t ht
    change 0 ≤ deriv ((fun x : ℝ ↦ x ^ 5) * Real.exp ∘ (-id)) t
    rw [(hd t).deriv]
    change 0 ≤ 5 * t ^ 4 * Real.exp (-t) + t ^ 5 * (Real.exp (-t) * -1)
    have hu : t ≤ 5 := (interior_subset ht : t ∈ Set.Icc 0 5).2
    have h :=
      mul_nonneg (sub_nonneg.mpr hu) (mul_nonneg (by positivity : 0 ≤ t ^ 4) (Real.exp_pos (-t)).le)
    linarith only [h]

private theorem profile_lower {z v : ℝ} (hz : 0 ≤ z) (hz' : z ≤ 357 / 125) (hv : 357 / 125 - z ≤ v)
    (hv' : v ≤ 5) :
    (357 / 125 - z) ^ 5 * (1 + z + z ^ 2 / 2 + z ^ 3 / 6) / (174 / 10) ≤ v ^ 5 * Real.exp (-v) := by
  have he :=
    Analysis.exp_le_taylor_add_two_next (x := (357 / 125 : ℝ)) (n := 12) (by norm_num only)
      (by norm_num only)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at he
  have hi :=
    one_div_le_one_div_of_le (Real.exp_pos _) (he.trans (by norm_num only : _ ≤ (174 / 10 : ℝ)))
  rw [one_div (Real.exp _), ← Real.exp_neg] at hi
  have ht := Real.sum_le_exp_of_nonneg hz 4
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one, pow_zero, pow_one, div_one, zero_add] at ht
  have hprod :=
    mul_le_mul (show 1 + z + z ^ 2 / 2 + z ^ 3 / 6 ≤ Real.exp z by linarith only [ht]) hi
      (by norm_num only) (Real.exp_pos _).le
  rw [← Real.exp_add] at hprod
  have hpow := mul_le_mul_of_nonneg_left hprod (pow_nonneg (sub_nonneg.mpr hz') 5)
  have hm :=
    fifth_increasing
      (show 357 / 125 - z ∈ Set.Icc (0 : ℝ) 5 from ⟨sub_nonneg.mpr hz', by linarith only [hz]⟩)
      (show v ∈ Set.Icc (0 : ℝ) 5 from ⟨le_trans (sub_nonneg.mpr hz') hv, hv'⟩) hv
  change _ ≤ v ^ 5 * Real.exp (-v) at hm
  rw [show z + -(357 / 125 : ℝ) = -(357 / 125 - z) by ring] at hpow
  linarith only [hpow, hm]

private theorem credit_le_term {r : ℝ} (hl : 278 ≤ r) {k : ℕ} (hk : k ∈ squarePrimes)
    (hkr : r < k) :
    (squareCredit k : ℝ) ≤
      4 * (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) (k ^ 2)).re := by
  obtain ⟨hkI, hp⟩ := Finset.mem_filter.mp hk
  have hnk := (Finset.mem_Ioc.mp hkI).1
  have h285 : (285 : ℝ) < k := by exact_mod_cast hnk
  have hr : 0 < r := by linarith only [hl]
  have hk0 := hr.trans hkr
  let u := Real.log ((k : ℝ) ^ 2 / r ^ 2)
  have hu0 : 0 ≤ u :=
    Real.log_nonneg ((one_le_div (sq_pos_of_pos hr)).mpr (pow_le_pow_left₀ hr.le hkr.le 2))
  obtain ⟨hz, hz'⟩ := drop_bounds k hk
  have hz0 : (0 : ℝ) ≤ dropBound k := by exact_mod_cast hz
  have hz1 : (dropBound k : ℝ) ≤ 357 / 125 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hz'
    simpa only [Rat.cast_div, Rat.cast_ofNat] using h
  have hlog : 51 / 50 * u ≤ (dropBound k : ℝ) := log_square_upper hl hk
  let v := (2 * (7 / 5) - u) / (2 * (25 / 51))
  have ve : v = 357 / 125 - 51 / 50 * u := by
    dsimp only [v]; ring
  have hprof :=
    profile_lower hz0 hz1 (v := v)
      (by
        rw [ve]; linarith only [hlog])
      (by
        rw [ve]; linarith only [hu0])
  have hs : u ≤ 14 / 5 := by linarith only [hlog, hz1]
  have ht :=
    quarter_summand_570 (sq_pos_of_pos hr) (pow_pos (Nat.cast_pos.mp hk0) 2)
      (by simpa only [Nat.cast_pow] using hs)
  rw [ht, ArithmeticFunction.vonMangoldt_apply_pow (by decide : 2 ≠ 0),
    ArithmeticFunction.vonMangoldt_apply_prime hp, quarterWeight570, Nat.cast_pow,
    Real.sqrt_sq hk0.le]
  have h285log :=
    (Analysis.rationalLogIntervalCheck_sound (N := 285) (j := 8) (n := 32) (lo := 565 / 100) (hi :=
        6) (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h285log
  have hkl := h285log.trans (Real.log_le_log (by norm_num only) h285.le)
  change (squareCredit k : ℝ) ≤ 4 * (1 / (k : ℝ) * (v ^ 5 * Real.exp (-v) / 120) * Real.log k)
  simp only [squareCredit, Rat.cast_div, Rat.cast_mul, Rat.cast_sub, Rat.cast_add, Rat.cast_pow,
    Rat.cast_ofNat, Rat.cast_one, Rat.cast_natCast]
  have hv : 0 ≤ v := by
    rw [ve]; linarith only [hs]
  have hmul :=
    mul_le_mul hprof hkl (by norm_num only) (mul_nonneg (pow_nonneg hv 5) (Real.exp_pos _).le)
  have hscl := mul_le_mul_of_nonneg_left hmul (show 0 ≤ 4 / (k : ℝ) / 120 by positivity)
  convert hscl using 1 <;> ring

attribute [local irreducible] squarePrimes in
/-- For radii from 278 to 285, prime squares with roots between 285 and 600
raise the section 31 principal lower bound by more than 0.0982. The proof sums
rational lower estimates that hold uniformly throughout the radius interval. -/
theorem quarter_square_gain_strong_570 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s) {r : ℝ}
    (hl : 278 ≤ r) (hu : r ≤ 285) (hRH : RiemannHypothesis)
    (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) :
    717289 / 1000000 * r - 21 / 100 + 982 / 10000 <
      (∑' k : ℕ, quarterKernel570.summand a (r ^ 2) k).re +
        (∑' k : ℕ, quarterKernel570.summand b (r ^ 2) k).re +
        (∑' k : ℕ, quarterKernel570.summand c (r ^ 2) k).re := by
  have hr : 0 ≤ r := by linarith only [hl]
  have hs (k : ℕ) (hk : k ∈ squarePrimes) : (k : ℝ) ≤ r ^ 2 ∧ r ^ 2 < (k : ℝ) ^ 2 := by
    unfold squarePrimes at hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_Ioc.mp (Finset.mem_filter.mp hk).1
    exact
      ⟨(show (k : ℝ) ≤ 600 by exact_mod_cast hk2).trans
          ((by norm_num only : (600 : ℝ) ≤ 278 ^ 2).trans
            (pow_le_pow_left₀ (by norm_num only) hl 2)),
        pow_lt_pow_left₀ (hu.trans_lt (by exact_mod_cast hk1)) hr (by decide)⟩
  have h := quarter_square_lower_570 a b c hl hu hRH squarePrimes (fun k hk ↦ hs k hk) ht hA hB hC
  have hc := (Rat.cast_lt (K := ℝ)).mpr credit_sum
  simp only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_sum] at hc
  have hw :=
    Finset.sum_le_sum
      (fun k hk ↦
        credit_le_term hl hk
          (hu.trans_lt
            (by
              unfold squarePrimes at hk
              exact_mod_cast (Finset.mem_Ioc.mp (Finset.mem_filter.mp hk).1).1)))
  rw [← Finset.mul_sum] at hw
  dsimp only at h
  linarith only [hc, hw, h]

attribute [local irreducible] squarePrimes in
/-- For radii from 278 to 285, prime squares with roots between 285 and 600
raise the section 31 principal lower bound by more than 0.0916. The proof sums
rational lower estimates that hold uniformly throughout the radius interval. -/
theorem quarter_square_gain_570 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s) {r : ℝ}
    (hl : 278 ≤ r) (hu : r ≤ 285) (hRH : RiemannHypothesis)
    (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) :
    717289 / 1000000 * r - 21 / 100 + 916 / 10000 <
      (∑' k : ℕ, quarterKernel570.summand a (r ^ 2) k).re +
        (∑' k : ℕ, quarterKernel570.summand b (r ^ 2) k).re +
        (∑' k : ℕ, quarterKernel570.summand c (r ^ 2) k).re := by
  have h := quarter_square_gain_strong_570 a b c hl hu hRH ht hA hB hC
  linarith only [h]

private theorem square_prime_above_292 : ∀ k ∈ squarePrimes, 292 < k := by decide +kernel

attribute [local irreducible] squarePrimes in
/-- On the radius interval from 285 to 292 the square and odd-power terms together improve the
principal prefix comparison by more than 0.10897. The square roots used in the
earlier certificate are all prime and strictly greater than 292. -/
theorem power_gain_584 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s] (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s) {r : ℝ} (hl : 285 ≤ r) (hu : r ≤ 292)
    (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) :
    let X := r ^ 2
    let f := fun k : ℕ ↦ (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) X k).re
    4 * (∑ k ∈ Finset.Ioc 0 ⌊X⌋₊, f k) -
          (∑' k : ℕ, quarterKernel570.summand (1 : DirichletCharacter ℂ 1) X k).re +
        10897 / 100000 <
      (∑' k : ℕ, quarterKernel570.summand a X k).re +
        (∑' k : ℕ, quarterKernel570.summand b X k).re +
        (∑' k : ℕ, quarterKernel570.summand c X k).re := by
  have hr : 0 ≤ r := by linarith only [hl]
  have above (k : ℕ) (hk : k ∈ squarePrimes) : r < k :=
    hu.trans_lt (by exact_mod_cast square_prime_above_292 k hk)
  have hs (k : ℕ) (hk : k ∈ squarePrimes) : (k : ℝ) ≤ r ^ 2 ∧ r ^ 2 < (k : ℝ) ^ 2 := by
    have habove := above k hk
    unfold squarePrimes at hk
    have h600 := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hk).1).2
    exact
      ⟨(show (k : ℝ) ≤ 600 by exact_mod_cast h600).trans
          ((by norm_num only : (600 : ℝ) ≤ 285 ^ 2).trans
            (pow_le_pow_left₀ (by norm_num only) hl 2)),
        pow_lt_pow_left₀ habove hr (by decide)⟩
  have h := square_odd_lower_584 a b c hl hu squarePrimes hs ht hA hB hC
  have hc := (Rat.cast_lt (K := ℝ)).mpr credit_sum
  simp only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_sum] at hc
  have hw :=
    Finset.sum_le_sum (fun k hk ↦ credit_le_term (by linarith only [hl] : 278 ≤ r) hk (above k hk))
  rw [← Finset.mul_sum] at hw
  dsimp only at h ⊢
  linarith only [h, hc, hw, odd_gain_lower_584 hl hu]

/-- On the section 62 interval the square and odd-power terms together improve the
principal prefix comparison by more than 0.10897. The square roots used in the
earlier certificate are all prime and strictly greater than 287. -/
theorem power_gain_574 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s] (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s) {r : ℝ} (hl : 285 ≤ r) (hu : r ≤ 287)
    (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) :
    let X := r ^ 2
    let f := fun k : ℕ ↦ (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) X k).re
    4 * (∑ k ∈ Finset.Ioc 0 ⌊X⌋₊, f k) -
          (∑' k : ℕ, quarterKernel570.summand (1 : DirichletCharacter ℂ 1) X k).re +
        10897 / 100000 <
      (∑' k : ℕ, quarterKernel570.summand a X k).re +
        (∑' k : ℕ, quarterKernel570.summand b X k).re +
        (∑' k : ℕ, quarterKernel570.summand c X k).re := by
  exact power_gain_584 a b c hl (hu.trans (by norm_num only)) ht hA hB hC

/-- On the radius interval from 285 to 288 the square and odd-power terms together improve the
principal prefix comparison by more than 0.10897. The square roots used in the
earlier certificate are all prime and strictly greater than 288. -/
theorem power_gain_576 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s] (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s) {r : ℝ} (hl : 285 ≤ r) (hu : r ≤ 288)
    (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) :
    let X := r ^ 2
    let f := fun k : ℕ ↦ (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) X k).re
    4 * (∑ k ∈ Finset.Ioc 0 ⌊X⌋₊, f k) -
          (∑' k : ℕ, quarterKernel570.summand (1 : DirichletCharacter ℂ 1) X k).re +
        10897 / 100000 <
      (∑' k : ℕ, quarterKernel570.summand a X k).re +
        (∑' k : ℕ, quarterKernel570.summand b X k).re +
        (∑' k : ℕ, quarterKernel570.summand c X k).re := by
  exact power_gain_584 a b c hl (hu.trans (by norm_num only)) ht hA hB hC

end PseudoPrime.PrimeTestBounds.MillerRabin
