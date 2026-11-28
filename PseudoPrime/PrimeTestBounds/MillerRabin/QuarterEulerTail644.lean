/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerAbel644
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerMoments570
import PseudoPrime.AnalyticNumberTheory.Arithmetic.NaturalTailLimit
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterInterval600

/-! # Section 122 Euler tail estimates -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Evaluate the main Euler integral on an interval above one at decay exponent 13/25. -/
theorem euler644_main_interval {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ t : ℝ in a..b, eulerDensity644 t) =
      ∑ j : Fin 3,
        ![(3 / 8 : ℝ), 321 / 800, 11449 / 80000] j *
          (eulerMomentValue570 (57 / 100) j.val a - eulerMomentValue570 (57 / 100) j.val b) := by
  apply euler570_polynomial_interval (k := 0) (by norm_num only) ha hab
  intro t ht
  rw [Fin.sum_univ_three]
  change
    _ =
      3 / 8 * eulerMoment570 _ 0 t + 321 / 800 * eulerMoment570 _ 1 t +
        11449 / 80000 * eulerMoment570 _ 2 t
  unfold eulerMoment570 eulerDensity644
  rw [show -(57 / 100 : ℝ) - 1 = -(157 / 100 : ℝ) by norm_num only]
  ring

/-- Evaluate the four-fifths square-root error integral via moments of degrees zero to two. -/
theorem euler644_low_interval {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ t : ℝ in a..b, (4 / 5 : ℝ) * Real.sqrt t * -eulerSlope644 t) =
      ∑ j : Fin 3,
        ![(4 / 5 : ℝ) * (3 / 16), (4 / 5 : ℝ) * (27499 / 80000), (4 / 5 : ℝ) * (1797493 / 8000000)]
            j *
          (eulerMomentValue570 (107 / 100) (0 + j.val) a -
            eulerMomentValue570 (107 / 100) (0 + j.val) b) := by
  apply euler570_polynomial_interval (by norm_num only) ha hab
  intro t ht
  have hp : 0 < t := zero_lt_one.trans_le (ha.trans ht.1)
  have he : Real.sqrt t * t ^ (-(257 / 100 : ℝ)) = t ^ (-(107 / 100 : ℝ) - 1) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hp]
    norm_num only
  rw [Fin.sum_univ_three]
  change
    _ =
      (4 / 5 : ℝ) * (3 / 16) * eulerMoment570 _ 0 t +
        (4 / 5 : ℝ) * (27499 / 80000) * eulerMoment570 _ 1 t +
        (4 / 5 : ℝ) * (1797493 / 8000000) * eulerMoment570 _ 2 t
  unfold eulerSlope644 eulerMoment570
  rw [← he]
  ring

/-- Evaluate the RH log-square error integral via moments of degrees two to four. -/
theorem euler644_high_interval {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ t : ℝ in a..b, Real.sqrt t * (Real.log t ^ 2 / 24) * -eulerSlope644 t) =
      ∑ j : Fin 3,
        ![(1 / 24 : ℝ) * (3 / 16), (1 / 24 : ℝ) * (27499 / 80000),
              (1 / 24 : ℝ) * (1797493 / 8000000)]
            j *
          (eulerMomentValue570 (107 / 100) (2 + j.val) a -
            eulerMomentValue570 (107 / 100) (2 + j.val) b) := by
  apply euler570_polynomial_interval (by norm_num only) ha hab
  intro t ht
  have hp : 0 < t := zero_lt_one.trans_le (ha.trans ht.1)
  have he : Real.sqrt t * t ^ (-(257 / 100 : ℝ)) = t ^ (-(107 / 100 : ℝ) - 1) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hp]
    norm_num only
  rw [Fin.sum_univ_three]
  change
    _ =
      (1 / 24 : ℝ) * (3 / 16) * eulerMoment570 _ 2 t +
        (1 / 24 : ℝ) * (27499 / 80000) * eulerMoment570 _ 3 t +
        (1 / 24 : ℝ) * (1797493 / 8000000) * eulerMoment570 _ 4 t
  unfold eulerSlope644 eulerMoment570
  rw [← he]
  ring

/-- The endpoint expression for the main integral, formed from its three logarithmic moments. -/
noncomputable def eulerMainTail644 (x : ℝ) : ℝ :=
  3 / 8 * eulerMomentValue570 (57 / 100) 0 x + 321 / 800 * eulerMomentValue570 (57 / 100) 1 x +
    11449 / 80000 * eulerMomentValue570 (57 / 100) 2 x

/-- Subtract the two main endpoint expressions to obtain the exact main integral. -/
private theorem mainDiff {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ t : ℝ in a..b, eulerDensity644 t) = eulerMainTail644 a - eulerMainTail644 b := by
  rw [euler644_main_interval ha hab, Fin.sum_univ_three]
  unfold eulerMainTail644
  change
    (3 / 8 : ℝ) * (eulerMomentValue570 (57 / 100) 0 a - eulerMomentValue570 (57 / 100) 0 b) +
        (321 / 800 : ℝ) *
          (eulerMomentValue570 (57 / 100) 1 a - eulerMomentValue570 (57 / 100) 1 b) +
        (11449 / 80000 : ℝ) *
          (eulerMomentValue570 (57 / 100) 2 a - eulerMomentValue570 (57 / 100) 2 b) =
      _
  ring

/-- The endpoint expression for the finite square-root error envelope. -/
noncomputable def eulerLowError644 (x : ℝ) : ℝ :=
  3 / 20 * eulerMomentValue570 (107 / 100) 0 x +
    27499 / 100000 * eulerMomentValue570 (107 / 100) 1 x +
    1797493 / 10000000 * eulerMomentValue570 (107 / 100) 2 x

/-- Subtract the finite-error endpoint expressions to evaluate the low error integral. -/
private theorem lowDiff {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ t : ℝ in a..b, (4 / 5 : ℝ) * Real.sqrt t * -eulerSlope644 t) =
      eulerLowError644 a - eulerLowError644 b := by
  rw [euler644_low_interval ha hab, Fin.sum_univ_three]
  unfold eulerLowError644
  change
    ((4 / 5 : ℝ) * (3 / 16)) *
          (eulerMomentValue570 (107 / 100) 0 a - eulerMomentValue570 (107 / 100) 0 b) +
        ((4 / 5 : ℝ) * (27499 / 80000)) *
          (eulerMomentValue570 (107 / 100) 1 a - eulerMomentValue570 (107 / 100) 1 b) +
        ((4 / 5 : ℝ) * (1797493 / 8000000)) *
          (eulerMomentValue570 (107 / 100) 2 a - eulerMomentValue570 (107 / 100) 2 b) =
      _
  ring

/-- The endpoint expression for the RH logarithmic error envelope. -/
noncomputable def eulerHighError644 (x : ℝ) : ℝ :=
  1 / 128 * eulerMomentValue570 (107 / 100) 2 x +
    27499 / 1920000 * eulerMomentValue570 (107 / 100) 3 x +
    1797493 / 192000000 * eulerMomentValue570 (107 / 100) 4 x

/-- Subtract the RH-error endpoint expressions to evaluate the high error integral. -/
private theorem highDiff {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ t : ℝ in a..b, Real.sqrt t * (Real.log t ^ 2 / 24) * -eulerSlope644 t) =
      eulerHighError644 a - eulerHighError644 b := by
  rw [euler644_high_interval ha hab, Fin.sum_univ_three]
  unfold eulerHighError644
  change
    ((1 / 24 : ℝ) * (3 / 16)) *
          (eulerMomentValue570 (107 / 100) 2 a - eulerMomentValue570 (107 / 100) 2 b) +
        ((1 / 24 : ℝ) * (27499 / 80000)) *
          (eulerMomentValue570 (107 / 100) 3 a - eulerMomentValue570 (107 / 100) 3 b) +
        ((1 / 24 : ℝ) * (1797493 / 8000000)) *
          (eulerMomentValue570 (107 / 100) 4 a - eulerMomentValue570 (107 / 100) 4 b) =
      _
  ring

/-- Endpoint moments are nonnegative above one by positivity of the tail polynomial. -/
private theorem moment_nonneg {d x : ℝ} (hd : 0 < d) (hx : 1 ≤ x) (k : ℕ) :
    0 ≤ eulerMomentValue570 d k x := by
  exact
    mul_nonneg (Real.rpow_nonneg (zero_le_one.trans hx) _)
      (Analysis.log_power_tail_poly_nonneg hd (Real.log_nonneg hx) k)

/-- The explicit Euler tail majorant consists of the main moment, the lower boundary
and the two error terms from the psi envelopes. -/
noncomputable def positiveTail644 (x : ℝ) : ℝ :=
  eulerMainTail644 x + (4 / 5) * Real.sqrt x * eulerDensity644 x + eulerLowError644 x +
    eulerHighError644 1000000

/-- The Euler tail envelope retaining the exact lower Abel boundary.
The remaining moments bound the main integral and the two error integrals. -/
noncomputable def signedTail644 (x : ℝ) : ℝ :=
  eulerMainTail644 x - (Chebyshev.psi x - x) * eulerDensity644 x + eulerLowError644 x +
    eulerHighError644 1000000

/-- Centered Abel summation on both sides of one million gives a finite upper bound
with the upper psi boundary retained for the infinite limit. -/
private theorem finite_tail_upper (hRH : RiemannHypothesis) {a b : ℝ} (ha : 2701 ≤ a)
    (hav : a ≤ 1000000) (hb : 1000000 ≤ b) :
    let w := fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * quarterEulerWeight644 n
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, w n) ≤
      signedTail644 a + (Chebyshev.psi b - b) * eulerDensity644 b := by
  intro w
  have ha1 : 1 ≤ a := by linarith only [ha]
  have lo := euler644_abel (zero_lt_one.trans_le ha1) hav
  have hi := euler644_abel (by norm_num only) hb
  have el := (abs_le.mp (euler644_error_million (by linarith only [ha]) hav (le_refl 1000000))).1
  have eh := (abs_le.mp (euler644_error_high hRH (le_refl 1000000) hb)).1
  rw [mainDiff ha1 hav] at lo
  rw [mainDiff (by norm_num only) hb] at hi
  rw [lowDiff ha1 hav] at el
  rw [highDiff (by norm_num only) hb] at eh
  have hbm (k : ℕ) :=
    moment_nonneg (by norm_num only : (0 : ℝ) < 57 / 100) (show 1 ≤ b by linarith only [hb]) k
  have hbe (k : ℕ) :=
    moment_nonneg (by norm_num only : (0 : ℝ) < 107 / 100) (show 1 ≤ b by linarith only [hb]) k
  have hve (k : ℕ) :=
    moment_nonneg (by norm_num only : (0 : ℝ) < 107 / 100) (by norm_num only : (1 : ℝ) ≤ 1000000) k
  have hmb : 0 ≤ eulerMainTail644 b := by
    unfold eulerMainTail644
    linarith only [hbm 0, hbm 1, hbm 2]
  have heb : 0 ≤ eulerHighError644 b := by
    unfold eulerHighError644
    linarith only [hbe 2, hbe 3, hbe 4]
  have hev : 0 ≤ eulerLowError644 1000000 := by
    unfold eulerLowError644
    linarith only [hve 0, hve 1, hve 2]
  unfold signedTail644
  rw [← Finset.Ioc_union_Ioc_eq_Ioc (Nat.floor_mono hav) (Nat.floor_mono hb),
    Finset.sum_union (Finset.Ioc_disjoint_Ioc_of_le le_rfl)]
  dsimp only [w]
  linear_combination lo + hi + el + eh + hmb + heb + hev

/-- The RH log-square bound and power decay force the upper Euler boundary to vanish. -/
private theorem upper_boundary_zero (hRH : RiemannHypothesis) :
    Filter.Tendsto (fun t ↦ (Chebyshev.psi t - t) * eulerDensity644 t) Filter.atTop (nhds 0) := by
  apply
    squeeze_zero_norm' _
      (Analysis.log_pow_mul_neg_rpow_tendsto (by norm_num only : (0 : ℝ) < 107 / 100) 4)
  filter_upwards [Filter.eventually_ge_atTop (1000000 : ℝ)] with t ht
  have hp : 0 < t := by linarith only [ht]
  have hl : 1 ≤ Real.log t :=
    (Real.le_log_iff_exp_le hp).mpr (Real.exp_one_lt_d9.le.trans (by linarith only [ht]))
  have hlog := zero_le_one.trans hl
  have hd : 0 ≤ eulerDensity644 t := by
    unfold eulerDensity644
    positivity
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hd]
  apply (mul_le_mul_of_nonneg_right (euler570_psi_high hRH ht) hd).trans
  have hz :
    3 / 8 + 321 / 800 * Real.log t + 11449 / 80000 * Real.log t ^ 2 ≤ 24 * Real.log t ^ 2 := by
    nlinarith only [hl, sq_nonneg (Real.log t - 1)]
  have he : Real.sqrt t * t ^ (-(157 / 100 : ℝ)) = t ^ (-(107 / 100 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hp]
    norm_num only
  unfold eulerDensity644
  have hw : 0 ≤ Real.sqrt t * t ^ (-(157 / 100 : ℝ)) * (Real.log t ^ 2 / 24) := by positivity
  linear_combination mul_le_mul_of_nonneg_left hz hw + Real.log t ^ 4 * he

/-- Under RH the positive Euler tail above a real cutoff between 2701 and one million
is bounded by the explicit section 122 expression. Pass the finite upper bound to infinity
using summability and decay of the centered upper boundary. -/
theorem signed_tail_upper_644 (hRH : RiemannHypothesis) {a : ℝ} (ha : 2701 ≤ a)
    (hav : a ≤ 1000000) :
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * quarterEulerWeight644 n) -
        (∑ n ∈ Finset.Ioc 0 ⌊a⌋₊, ArithmeticFunction.vonMangoldt n * quarterEulerWeight644 n) ≤
      signedTail644 a := by
  have ht :=
    AnalyticNumberTheory.Arithmetic.tendsto_tail_prefix _
      (by simp only [ArithmeticFunction.map_zero, zero_mul]) quarter_euler_weight_summable_644 a
  have hb :=
    (upper_boundary_zero hRH).comp
      (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ)) Filter.atTop Filter.atTop)
  have hr := hb.const_add (signedTail644 a)
  rw [add_zero] at hr
  apply le_of_tendsto_of_tendsto ht hr
  filter_upwards [Filter.eventually_ge_atTop (1000000 : ℕ)] with n hn
  have h := finite_tail_upper hRH ha hav (b := (n : ℝ)) (by exact_mod_cast hn)
  simpa only [Nat.floor_natCast, Function.comp_apply] using h

/-- The Euler tail above a cutoff from 2701 through one million satisfies
the original unsigned bound by the finite psi envelope at the cutoff. -/
theorem positive_tail_upper_644 (hRH : RiemannHypothesis) {a : ℝ} (ha : 2701 ≤ a)
    (hav : a ≤ 1000000) :
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * quarterEulerWeight644 n) -
        (∑ n ∈ Finset.Ioc 0 ⌊a⌋₊, ArithmeticFunction.vonMangoldt n * quarterEulerWeight644 n) ≤
      positiveTail644 a := by
  have ha₁ : 1 ≤ a := by linarith only [ha]
  have hfa : 0 ≤ eulerDensity644 a := by
    have hlog := Real.log_nonneg ha₁
    have ha₀ := zero_le_one.trans ha₁
    unfold eulerDensity644
    positivity
  have he :=
    mul_le_mul_of_nonneg_right
      (abs_le.mp
          (AnalyticNumberTheory.Arithmetic.psi_four_fifths_1423_million (by linarith only [ha])
            hav)).1
      hfa
  refine (signed_tail_upper_644 hRH ha hav).trans ?_
  unfold signedTail644 positiveTail644
  linarith only [he]

/-- Between cutoffs from 2701 through one million, the signed envelope
decreases by at least the Euler sum removed from the tail. The finite
Abel error is bounded by the difference of the low error moments. -/
theorem signed_tail_drop_644 {a b : ℝ} (ha : 2701 ≤ a) (hab : a ≤ b) (hb : b ≤ 1000000) :
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, ArithmeticFunction.vonMangoldt n * quarterEulerWeight644 n) ≤
      signedTail644 a - signedTail644 b := by
  have ha₁ : 1 ≤ a := by linarith only [ha]
  have h := euler644_abel (zero_lt_one.trans_le ha₁) hab
  have he := (abs_le.mp (euler644_error_million (by linarith only [ha]) hab hb)).1
  rw [mainDiff ha₁ hab] at h
  rw [lowDiff ha₁ hab] at he
  unfold signedTail644
  linarith only [h, he]

/-- The signed Euler tail envelope is antitone even at the jumps of psi
throughout the finite Abel range. Each removed Euler summand is nonnegative. -/
theorem signed_tail_antitone_644 : AntitoneOn signedTail644 (Set.Icc 2701 1000000) := by
  intro a ha b hb hab
  have h₀ :
    0 ≤ ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, ArithmeticFunction.vonMangoldt n * quarterEulerWeight644 n := by
    apply Finset.sum_nonneg
    intro n hn
    exact
      mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (quarter_euler_weight_nonneg_644
          (Nat.succ_le_of_lt (Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hn).1)))
  exact sub_nonneg.mp (h₀.trans (signed_tail_drop_644 ha.1 hab hb.2))

/-- For positive x the square-root boundary is a positive combination of moments of
degrees one and two. The constant coefficient cancels after expanding the tail polynomials. -/
theorem euler644_boundary_moments {x : ℝ} (hx : 0 < x) :
    Real.sqrt x * eulerDensity644 x =
      11449 / 80000 * eulerMomentValue570 (107 / 100) 1 x +
        1225043 / 8000000 * eulerMomentValue570 (107 / 100) 2 x := by
  unfold eulerDensity644 eulerMomentValue570
  rw [Real.sqrt_eq_rpow, ← mul_assoc, ← Real.rpow_add hx]
  norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero,
    Nat.reduceAdd, show (1 / 2 : ℝ) + -(157 / 100) = -(107 / 100) by norm_num only]
  ring

/-- For radius at least one, the explicit Euler tail at the square cutoff
is differentiable, decreasing, and has logarithmic slope at least −2.14. -/
theorem euler644_tail_slope {r : ℝ} (hr : 1 ≤ r) :
    ∃ v : ℝ,
      HasDerivAt (fun x : ℝ ↦ positiveTail644 (x ^ 2)) v r ∧
        -(2.14 * positiveTail644 (r ^ 2)) ≤ r * v ∧ v ≤ 0 := by
  have hp := zero_lt_one.trans_le hr
  have hm {d : ℝ} (hd : 0 < d) (k : ℕ) : 0 ≤ eulerMomentValue570 d k (r ^ 2) :=
    mul_nonneg (Real.rpow_nonneg (sq_nonneg _) _)
      (Analysis.log_power_tail_poly_nonneg hd (Real.log_nonneg (one_le_pow₀ hr)) k)
  have hh : 0 ≤ eulerHighError644 1000000 := by
    have h (k : ℕ) : 0 ≤ eulerMomentValue570 (107 / 100) k 1000000 :=
      mul_nonneg (Real.rpow_nonneg (by norm_num only) _)
        (Analysis.log_power_tail_poly_nonneg (by norm_num only) (Real.log_nonneg (by norm_num only))
          k)
    unfold eulerHighError644
    linarith only [h 2, h 3, h 4]
  obtain ⟨a0, ha0, la0, ua0⟩ := section99_moment_slope (by norm_num only : (0 : ℝ) < 57 / 100) hr 0
  obtain ⟨a1, ha1, la1, ua1⟩ := section99_moment_slope (by norm_num only : (0 : ℝ) < 57 / 100) hr 1
  obtain ⟨a2, ha2, la2, ua2⟩ := section99_moment_slope (by norm_num only : (0 : ℝ) < 57 / 100) hr 2
  obtain ⟨b0, hb0, lb0, ub0⟩ := section99_moment_slope (by norm_num only : (0 : ℝ) < 107 / 100) hr 0
  obtain ⟨b1, hb1, lb1, ub1⟩ := section99_moment_slope (by norm_num only : (0 : ℝ) < 107 / 100) hr 1
  obtain ⟨b2, hb2, lb2, ub2⟩ := section99_moment_slope (by norm_num only : (0 : ℝ) < 107 / 100) hr 2
  have hmain :=
    (((ha0.const_mul (3 / 8)).add (ha1.const_mul (321 / 800))).add (ha2.const_mul (11449 / 80000)))
  have hlow :=
    (((hb0.const_mul (3 / 20)).add (hb1.const_mul (27499 / 100000))).add
      (hb2.const_mul (1797493 / 10000000)))
  have hbd :=
    ((hb1.const_mul (11449 / 80000)).add (hb2.const_mul (1225043 / 8000000))) |>.const_mul (4 / 5)
  have hsum := (((hmain.add hbd).add hlow).add_const (eulerHighError644 1000000))
  refine ⟨_, hsum.congr_of_eventuallyEq ?_, ?_, ?_⟩
  · filter_upwards [lt_mem_nhds hp] with x hx
    unfold positiveTail644 eulerMainTail644 eulerLowError644
    rw [mul_assoc, euler644_boundary_moments (sq_pos_of_pos hx)]
    rfl
  · unfold positiveTail644 eulerMainTail644 eulerLowError644
    rw [mul_assoc (4 / 5), euler644_boundary_moments (sq_pos_of_pos hp)]
    linarith only [la0, la1, la2, lb0, lb1, lb2, hh, hm (by norm_num only : (0 : ℝ) < 57 / 100) 0,
      hm (by norm_num only : (0 : ℝ) < 57 / 100) 1, hm (by norm_num only : (0 : ℝ) < 57 / 100) 2]
  · linarith only [ua0, ua1, ua2, ub0, ub1, ub2]

end PseudoPrime.PrimeTestBounds.MillerRabin
