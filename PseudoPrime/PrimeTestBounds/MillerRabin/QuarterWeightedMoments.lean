/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWeightedEuler
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWeightedEuler
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTwoShiftEuler

/-! # Closed logarithmic moments for the section 107 Euler tail -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private noncomputable def mainCoeff : Fin 3 → ℝ :=
  ![c0 - 5 * c1 + 25 * c2, c1 - 10 * c2, c2]

/-- Closed main tail at a lower endpoint, using the three logarithmic moments
with decay exponent 13/25. -/
noncomputable def weightedEulerMain (a : ℝ) : ℝ :=
  ∑ j : Fin 3, mainCoeff j * eulerMomentValue570 (13 / 25) j.val a

/-- The integral between endpoints at least one equals the difference of their
closed main tails. Expand the weight and integrate its three monomials. -/
theorem weightedEuler_main_interval {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ t : ℝ in a..b, weightedEulerDensity t) = weightedEulerMain a - weightedEulerMain b := by
  unfold weightedEulerMain
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  apply euler570_polynomial_interval (k := 0) (by norm_num only) ha hab
  intro t ht
  have ht0 := zero_lt_one.trans_le (ha.trans ht.1)
  rw [Fin.sum_univ_three]
  simp only [mainCoeff, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  unfold eulerMoment570 weightedEulerDensity
  rw [poly101_expand]
  rw [show -(13 / 25 : ℝ) - 1 = -(38 / 25 : ℝ) by norm_num only, Real.rpow_def_of_pos ht0,
    mul_comm (Real.log t) (-(38 / 25 : ℝ))]
  norm_num only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
  ring

/-- The main integral tends to the closed tail at its lower endpoint. Each
upper endpoint moment vanishes since the decay exponent is positive. -/
theorem weightedEuler_main_limit {a : ℝ} (ha : 1 ≤ a) :
    Filter.Tendsto (fun b : ℝ ↦ ∫ t : ℝ in a..b, weightedEulerDensity t) Filter.atTop
      (nhds (weightedEulerMain a)) := by
  have h (k : ℕ) : Filter.Tendsto (eulerMomentValue570 (13 / 25) k) Filter.atTop (nhds 0) := by
    change
      Filter.Tendsto
        (fun t : ℝ ↦ t ^ (-(13 / 25 : ℝ)) * Analysis.logPowerTailPoly (13 / 25) k (Real.log t)) _ _
    simpa only [eulerMomentValue570, neg_mul, neg_neg, neg_zero] using
      (Analysis.log_power_tail_primitive_tendsto (by norm_num only : (0 : ℝ) < 13 / 25) k).neg
  have hz :=
    (((h 0).const_mul (mainCoeff 0)).add ((h 1).const_mul (mainCoeff 1))).add
      ((h 2).const_mul (mainCoeff 2))
  simp only [mul_zero, add_zero] at hz
  have hz' : Filter.Tendsto weightedEulerMain Filter.atTop (nhds 0) := by
    change Filter.Tendsto (fun t ↦ weightedEulerMain t) _ _
    simp only [weightedEulerMain, Fin.sum_univ_three]
    exact hz
  have hh := hz'.const_sub (weightedEulerMain a)
  rw [sub_zero] at hh
  apply hh.congr'
  filter_upwards [Filter.eventually_ge_atTop a] with b hb
  exact (weightedEuler_main_interval ha hb).symm

private noncomputable def errorCoeff : Fin 3 → ℝ :=
  ![(38 / 25 * mainCoeff 0 - mainCoeff 1) / 24, (38 / 25 * mainCoeff 1 - 2 * mainCoeff 2) / 24,
    (38 / 25 * mainCoeff 2) / 24]

/-- Closed tail for the square-root log-square error majorant. -/
noncomputable def weightedEulerError (a : ℝ) : ℝ :=
  ∑ j : Fin 3, errorCoeff j * eulerMomentValue570 (51 / 50) (2 + j.val) a

/-- The RH error envelope integrates exactly to the difference of three
endpoint moments of degrees two, three and four. -/
theorem weightedEuler_error_interval {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ t : ℝ in a..b, Real.sqrt t * (Real.log t ^ 2 / 24) * -deriv weightedEulerDensity t) =
      weightedEulerError a - weightedEulerError b := by
  unfold weightedEulerError
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  apply euler570_polynomial_interval (by norm_num only) ha hab
  intro t ht
  have hp := zero_lt_one.trans_le (ha.trans ht.1)
  let C := mainCoeff 0
  let L := mainCoeff 1
  let Q := mainCoeff 2
  rw [weighted_euler_density_deriv hp, (poly101_deriv _).deriv, poly101_expand, Fin.sum_univ_three]
  rw [mul_comm (-(38 / 25 : ℝ)), ← Real.rpow_def_of_pos hp]
  change
    _ =
      ((38 / 25 * C - L) / 24) * eulerMoment570 _ 2 t +
        ((38 / 25 * L - 2 * Q) / 24) * eulerMoment570 _ 3 t +
        ((38 / 25 * Q) / 24) * eulerMoment570 _ 4 t
  have hpow : t ^ (-(38 / 25 : ℝ)) * t⁻¹ = t ^ (-(38 / 25 : ℝ) - 1) := by
    rw [Real.rpow_sub hp, Real.rpow_one, div_eq_mul_inv (t ^ _) t]
  have hs : Real.sqrt t * t ^ (-(38 / 25 : ℝ) - 1) = t ^ (-(51 / 50 : ℝ) - 1) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hp]
    norm_num only
  unfold eulerMoment570
  rw [← hs, ← hpow]
  unfold C L Q mainCoeff
  norm_num only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  ring

/-- Under RH, the common Euler tail above a cutoff at least 101 is bounded
by its main tail, its lower boundary error, and three explicit error moments. -/
theorem weightedEuler_tail_closed {a : ℝ} (hRH : RiemannHypothesis) (ha : 101 ≤ a)
    (hl : 5 ≤ Real.log a) :
    let f := fun n : ℕ ↦
      ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (38 / 25 : ℝ) *
        weightedEulerPoly (11 / 25) (91 / 200) (Real.log n)
    (∑' n, f n) - ∑ n ∈ Finset.Ioc 0 ⌊a⌋₊, f n ≤
      weightedEulerMain a + Real.sqrt a * (Real.log a ^ 2 / 24) * weightedEulerDensity a +
        weightedEulerError a := by
  have ha1 : 1 ≤ a := by linarith only [ha]
  have hm (k : ℕ) : Filter.Tendsto (eulerMomentValue570 (51 / 50) k) Filter.atTop (nhds 0) := by
    change
      Filter.Tendsto
        (fun t : ℝ ↦ t ^ (-(51 / 50 : ℝ)) * Analysis.logPowerTailPoly (51 / 50) k (Real.log t)) _ _
    simpa only [neg_mul, neg_neg, neg_zero] using
      (Analysis.log_power_tail_primitive_tendsto (by norm_num only : (0 : ℝ) < 51 / 50) k).neg
  have hz :=
    (((hm 2).const_mul (errorCoeff 0)).add ((hm 3).const_mul (errorCoeff 1))).add
      ((hm 4).const_mul (errorCoeff 2))
  simp only [mul_zero, add_zero] at hz
  have he : Filter.Tendsto weightedEulerError Filter.atTop (nhds 0) := by
    change Filter.Tendsto (fun t ↦ weightedEulerError t) _ _
    simp only [weightedEulerError, Fin.sum_univ_three]
    exact hz
  intro f
  apply le_of_forall_pos_le_add
  intro ε hε
  have hh :=
    weighted_euler_tail_RH (D := weightedEulerError a + ε) hRH ha hl (weightedEuler_main_limit ha1)
      (by
        filter_upwards [he.eventually (lt_mem_nhds (neg_lt_zero.mpr hε)),
          Filter.eventually_ge_atTop a] with b hb hab
        rw [weightedEuler_error_interval ha1 hab]
        linarith only [hb])
  dsimp only at hh
  dsimp only [f]
  linarith only [hh]

/-- Under RH and the three-character trace floor, the cosine Euler contribution
for the section 107 coefficients is at least minus four times the explicit cap. -/
theorem weighted_cosine_tail_lower {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) {X : ℝ}
    (hX : 85264 ≤ X) (hl : 5 ≤ Real.log X) (hRH : RiemannHypothesis)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re) :
    let S := twoShiftCosineTail a b c X
    let u : ℝ := 11 / 25
    let v : ℝ := 91 / 200
    (-4 : ℝ) *
        (weightedEulerMain X + Real.sqrt X * (Real.log X ^ 2 / 24) * weightedEulerDensity X +
          weightedEulerError X) ≤
      u * S (14 / 5) - v * S 3 - ((u ^ 2 + v ^ 2) / 2) * S 0 + (u * v) * S (1 / 5) := by
  intro S u v
  dsimp only [S, u, v]
  rw [twoShift_weighted_euler_eq a b c hX]
  let f := fun n : ℕ ↦
    ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (38 / 25 : ℝ) *
      weightedEulerPoly (11 / 25) (91 / 200) (Real.log n)
  let D := fun n : ℕ ↦ 3 - ((a n).re + (b n).re + (c n).re)
  have hs : Summable f := weighted_euler_summable
  have hp := hs.sum_add_tsum_compl (s := Finset.Icc 0 ⌊X⌋₊)
  change
    (∑ n ∈ Finset.Icc 0 ⌊X⌋₊, f n) + (∑' n : { n : ℕ // n ∉ Finset.Icc 0 ⌊X⌋₊ }, f n.val) =
      ∑' n, f n at hp
  have hpred : (fun n : ℕ ↦ n ∉ Finset.Icc 0 ⌊X⌋₊) = (fun n : ℕ ↦ ⌊X⌋₊ < n) := by
    funext n
    simp only [Finset.mem_Icc, Nat.zero_le, true_and, not_le]
  rw [hpred, ← Finset.sum_Ioc_add_eq_sum_Icc (Nat.zero_le _)] at hp
  have hf0 : f 0 = 0 := by
    dsimp only [f]; rw [ArithmeticFunction.map_zero, zero_div, zero_mul]
  rw [hf0, add_zero] at hp
  have hcap := weightedEuler_tail_closed hRH (by linarith only [hX]) hl
  dsimp only at hcap
  change (∑' n, f n) - ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, f n ≤ _ at hcap
  have hsub := (hs.subtype (fun n ↦ ⌊X⌋₊ < n)).mul_left (4 : ℝ)
  have hb (n : { n : ℕ // ⌊X⌋₊ < n }) :
    0 ≤ D n.val * f n.val ∧ D n.val * f n.val ≤ 4 * f n.val := by
    have hn := Nat.lt_of_floor_lt n.property
    have hlog := hl.trans (Real.log_le_log (by linarith only [hX]) hn.le)
    have hf : 0 ≤ f n.val :=
      mul_nonneg
        (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        (weighted_euler_pos hlog).le
    have hD : 0 ≤ D n.val := by
      dsimp only [D]
      linarith only [(Complex.re_le_norm _).trans (a.norm_le_one n.val),
        (Complex.re_le_norm _).trans (b.norm_le_one n.val),
        (Complex.re_le_norm _).trans (c.norm_le_one n.val)]
    have hu : D n.val ≤ 4 := by
      dsimp only [D]; linarith only [ht n.val]
    exact ⟨mul_nonneg hD hf, mul_le_mul_of_nonneg_right hu hf⟩
  have hD :=
    hsub.of_norm_bounded
      (fun n ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (hb n).1]
        exact (hb n).2)
  have hsum := hD.tsum_le_tsum (fun n ↦ (hb n).2) hsub
  rw [tsum_mul_left] at hsum
  change _ ≤ -(∑' n : { n : ℕ // ⌊X⌋₊ < n }, D n.val * f n.val)
  linarith only [hp, hcap, hsum]

/-- The forward main polynomial in the log-cutoff coordinate. -/
noncomputable def phaseEulerMainPoly107 (x : ℝ) : ℝ :=
  ∑ k : Fin 3, mainCoeff k * Analysis.logPowerTailPoly (13 / 25) k.val x

/-- The forward error polynomial includes the lower boundary and the
integrated slope of the regular Euler weight. -/
noncomputable def phaseEulerErrorPoly107 (x : ℝ) : ℝ :=
  x ^ 2 / 24 * weightedEulerPoly (11 / 25) (91 / 200) x +
    ∑ k : Fin 3, errorCoeff k * Analysis.logPowerTailPoly (51 / 50) (2 + k.val) x

/-- At positive t the power in the integrated moment is an exponential of log t. -/
theorem forward_moment_scale {d t : ℝ} (ht : 0 < t) (k : ℕ) :
    eulerMomentValue570 d k t =
      Real.exp (-d * Real.log t) * Analysis.logPowerTailPoly d k (Real.log t) := by
  rw [eulerMomentValue570, Real.rpow_def_of_pos ht, mul_comm (Real.log t)]

/-- The square-root factor changes the decay exponent at a positive endpoint. -/
theorem forward_boundary_scale {t : ℝ} (ht : 0 < t) :
    Real.sqrt t * Real.exp (-(38 / 25 : ℝ) * Real.log t) =
      Real.exp (-(51 / 50 : ℝ) * Real.log t) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos ht, ← Real.exp_add]
  congr 1
  ring

/-- At a positive cutoff, both forward Euler contributions split into
a fixed log-polynomial times the corresponding exponential decay. -/
theorem phase_euler_log107 {t : ℝ} (ht : 0 < t) :
    weightedEulerMain t + Real.sqrt t * (Real.log t ^ 2 / 24) * weightedEulerDensity t +
        weightedEulerError t =
      Real.exp (-(13 / 25) * Real.log t) * phaseEulerMainPoly107 (Real.log t) +
        Real.exp (-(51 / 50) * Real.log t) * phaseEulerErrorPoly107 (Real.log t) := by
  unfold weightedEulerMain weightedEulerDensity weightedEulerError phaseEulerMainPoly107
    phaseEulerErrorPoly107
  simp_rw [forward_moment_scale ht, Finset.mul_sum]
  rw [show
      Real.sqrt t * (Real.log t ^ 2 / 24) *
          (Real.exp (-(38 / 25 : ℝ) * Real.log t) *
            weightedEulerPoly (11 / 25) (91 / 200) (Real.log t)) =
        (Real.sqrt t * Real.exp (-(38 / 25 : ℝ) * Real.log t)) *
          (Real.log t ^ 2 / 24 * weightedEulerPoly (11 / 25) (91 / 200) (Real.log t))
      by ring,
    forward_boundary_scale ht]
  simp only [mul_add, Fin.sum_univ_three]
  ring

private theorem moment_mul_upper {d l x h a A : ℝ} (hd : 0 < d) (hl : 0 ≤ l) (hx : x ∈ Set.Icc l h)
    (ha : a ≤ A) (k : ℕ) :
    a * Analysis.logPowerTailPoly d k x ≤
      A * Analysis.logPowerTailPoly d k (if 0 ≤ A then h else l) := by
  have h0 := Analysis.log_power_tail_poly_nonneg hd (hl.trans hx.1) k
  apply (mul_le_mul_of_nonneg_right ha h0).trans
  split_ifs with hA
  · exact mul_le_mul_of_nonneg_left (Analysis.log_power_tail_poly_mono hd (hl.trans hx.1) hx.2 k) hA
  · exact
      mul_le_mul_of_nonpos_left (Analysis.log_power_tail_poly_mono hd hl hx.1 k) (le_of_not_ge hA)

/-- Bound the main Euler polynomial using the signs of its three coefficients
and rational endpoints of the logarithmic argument. -/
theorem phase_euler_main_box107 {l x h : ℝ} (hl : 0 ≤ l) (hx : x ∈ Set.Icc l h) :
    phaseEulerMainPoly107 x ≤
      0.690829 * Analysis.logPowerTailPoly (13 / 25) 0 h -
          0.608173 * Analysis.logPowerTailPoly (13 / 25) 1 l +
        0.132621 * Analysis.logPowerTailPoly (13 / 25) 2 h := by
  obtain ⟨hc, he, hq⟩ := poly101_coeff
  have h0 : mainCoeff 0 ≤ 0.690829 := by
    change c0 - 5 * c1 + 25 * c2 ≤ _
    linarith only [hc.2, he.1, hq.2]
  have h1 : mainCoeff 1 ≤ -0.608173 := by
    change c1 - 10 * c2 ≤ _
    linarith only [he.2, hq.1]
  have h2 : mainCoeff 2 ≤ 0.132621 := by
    change c2 ≤ _
    linarith only [hq.2]
  have H0 := moment_mul_upper (by norm_num only : 0 < (13 / 25 : ℝ)) hl hx h0 0
  have H1 := moment_mul_upper (by norm_num only : 0 < (13 / 25 : ℝ)) hl hx h1 1
  have H2 := moment_mul_upper (by norm_num only : 0 < (13 / 25 : ℝ)) hl hx h2 2
  unfold phaseEulerMainPoly107
  norm_num only [Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, ite_eq_left,
    ite_eq_right, show (0 : ℝ) ≤ 0.690829 by norm_num only,
    show ¬(0 : ℝ) ≤ -0.608173 by norm_num only,
    show (0 : ℝ) ≤ 0.132621 by norm_num only] at H0 H1 H2 ⊢
  linarith only [H0, H1, H2]

/-- Bound the forward error polynomial by evaluating its boundary factor and
the three signed moments at the appropriate rational endpoints. -/
theorem phase_euler_error_box107 {l x h : ℝ} (hl : 5 ≤ l) (hx : x ∈ Set.Icc l h) :
    phaseEulerErrorPoly107 x ≤
      h ^ 2 / 24 * (0.96548098 + 0.71803515 * (h - 5) + 0.13262092 * (h - 5) ^ 2) +
            0.0690931 * Analysis.logPowerTailPoly (51 / 50) 2 h -
          0.0495693 * Analysis.logPowerTailPoly (51 / 50) 3 l +
        0.0083994 * Analysis.logPowerTailPoly (51 / 50) 4 h := by
  obtain ⟨hc, he, hq⟩ := poly101_coeff
  have h0 : errorCoeff 0 ≤ 0.0690931 := by
    change (38 / 25 * (c0 - 5 * c1 + 25 * c2) - (c1 - 10 * c2)) / 24 ≤ _
    linarith only [hc.2, he.1, hq.2]
  have h1 : errorCoeff 1 ≤ -0.0495693 := by
    change (38 / 25 * (c1 - 10 * c2) - 2 * c2) / 24 ≤ _
    linarith only [he.2, hq.1]
  have h2 : errorCoeff 2 ≤ 0.0083994 := by
    change (38 / 25 * c2) / 24 ≤ _
    linarith only [hq.2]
  have hl0 : 0 ≤ l := by linarith only [hl]
  have hx0 := hl0.trans hx.1
  have hxh : 0 ≤ x - 5 := sub_nonneg.mpr (hl.trans hx.1)
  have hshift : x - 5 ≤ h - 5 := sub_le_sub_right hx.2 _
  have hP :
    weightedEulerPoly (11 / 25) (91 / 200) x ≤
      0.96548098 + 0.71803515 * (h - 5) + 0.13262092 * (h - 5) ^ 2 := by
    rw [poly101_expand]
    have h₁ := mul_le_mul he.2 hshift hxh (by norm_num only)
    have h₂ := mul_le_mul hq.2 (pow_le_pow_left₀ hxh hshift 2) (sq_nonneg _) (by norm_num only)
    linarith only [hc.2, h₁, h₂]
  have hboundary :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx0 hx.2 2) (weighted_euler_pos (hl.trans hx.1)).le
  have hboundary' := mul_le_mul_of_nonneg_left hP (sq_nonneg h)
  have H0 := moment_mul_upper (by norm_num only : 0 < (51 / 50 : ℝ)) hl0 hx h0 2
  have H1 := moment_mul_upper (by norm_num only : 0 < (51 / 50 : ℝ)) hl0 hx h1 3
  have H2 := moment_mul_upper (by norm_num only : 0 < (51 / 50 : ℝ)) hl0 hx h2 4
  unfold phaseEulerErrorPoly107
  norm_num only [Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.reduceAdd,
    ite_eq_left, ite_eq_right, show (0 : ℝ) ≤ 0.0690931 by norm_num only,
    show ¬(0 : ℝ) ≤ -0.0495693 by norm_num only,
    show (0 : ℝ) ≤ 0.0083994 by norm_num only] at H0 H1 H2 ⊢
  linarith only [H0, H1, H2, hboundary, hboundary']

/-- In logarithmic coordinates the scaled Euler main tail has derivative
minus the weighted Euler density without the Jacobian factor. -/
theorem phase_euler_main_deriv107 (x : ℝ) :
    HasDerivAt (fun y ↦ Real.exp (-(13 / 25) * y) * phaseEulerMainPoly107 y)
      (-(Real.exp (-(13 / 25) * x) * weightedEulerPoly (11 / 25) (91 / 200) x)) x := by
  have h (k : Fin 3) :=
    (Analysis.log_power_tail_poly_deriv (by norm_num only : (0 : ℝ) < 13 / 25) k.val x).const_mul
      (mainCoeff k)
  have H := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ ↦ h k)
  have hExp := ((hasDerivAt_id x).const_mul (-(13 / 25 : ℝ))).exp
  have hd := hExp.mul H
  unfold phaseEulerMainPoly107
  apply hd.congr_deriv
  simp only [id, Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
  rw [poly101_expand]
  unfold mainCoeff
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  ring

/-- The section 107 Euler polynomial exceeds eight when its logarithmic
argument is at least eleven, using the positive shifted coefficients. -/
theorem weighted_euler_gt_eight107 {x : ℝ} (hx : 11 ≤ x) :
    8 < weightedEulerPoly (11 / 25) (91 / 200) x := by
  obtain ⟨h0, h1, h2⟩ := poly101_coeff
  have hx' : 6 ≤ x - 5 := by linarith only [hx]
  have h1' := mul_le_mul h1.1 hx' (by norm_num only) (by linarith only [h1.1])
  have h2' :=
    mul_le_mul h2.1 (pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 6) hx' 2) (by norm_num only)
      (by linarith only [h2.1])
  rw [poly101_expand]
  linarith only [h0.1, h1', h2']

/-- In log coordinates the derivative of the forward error cap includes
both the endpoint derivative and the negative lower-integrand contribution. -/
theorem phase_euler_error_deriv107 (x : ℝ) :
    let P := weightedEulerPoly (11 / 25) (91 / 200)
    HasDerivAt (fun y ↦ Real.exp (-(51 / 50) * y) * phaseEulerErrorPoly107 y)
      (Real.exp (-(51 / 50) * x) / 24 *
        (2 * x ^ 2 * deriv P x + (2 * x - (127 / 50) * x ^ 2) * P x))
      x := by
  intro P
  have h (k : Fin 3) :=
    (Analysis.log_power_tail_poly_deriv (by norm_num only : (0 : ℝ) < 51 / 50) (2 + k.val)
          x).const_mul
      (errorCoeff k)
  have H := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ ↦ h k)
  have hB := (((hasDerivAt_id x).pow 2).div_const 24).mul (poly101_deriv x)
  have hExp := ((hasDerivAt_id x).const_mul (-(51 / 50 : ℝ))).exp
  have hd := hExp.mul (hB.add H)
  unfold phaseEulerErrorPoly107
  apply hd.congr_deriv
  dsimp only [P]
  rw [(poly101_deriv x).deriv]
  simp only [Pi.mul_apply, Pi.add_apply, Pi.pow_apply, id]
  simp only [poly101_expand]
  norm_num only [Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.reduceAdd,
    Nat.cast_ofNat, errorCoeff, mainCoeff, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

private theorem weighted_euler_deriv_le_third {x : ℝ} (hx : 11 ≤ x) :
    3 * deriv (weightedEulerPoly (11 / 25) (91 / 200)) x ≤
      weightedEulerPoly (11 / 25) (91 / 200) x := by
  obtain ⟨h0, h1, h2⟩ := poly101_coeff
  have hA : 0 ≤ c1 * (x - 8) := mul_nonneg (by linarith only [h1.1]) (by linarith only [hx])
  have hB : 0 ≤ c2 * (x - 5) * (x - 11) :=
    mul_nonneg (mul_nonneg (by linarith only [h2.1]) (by linarith only [hx])) (sub_nonneg.mpr hx)
  rw [(poly101_deriv x).deriv, poly101_expand]
  nlinarith only [h0.1, hA, hB]

/-- Above log cutoff eleven, the forward Abel error cap decreases. The
logarithmic derivative of the weighted quadratic is at most one third. -/
theorem phase_euler_error_deriv_nonpos107 {x : ℝ} (hx : 11 ≤ x) :
    deriv (fun y ↦ Real.exp (-(51 / 50) * y) * phaseEulerErrorPoly107 y) x ≤ 0 := by
  rw [(phase_euler_error_deriv107 x).deriv]
  apply mul_nonpos_of_nonneg_of_nonpos (div_nonneg (Real.exp_pos _).le (by norm_num only))
  have h := mul_le_mul_of_nonneg_left (weighted_euler_deriv_le_third hx) (sq_nonneg x)
  have hx0 : 0 ≤ x := by linarith only [hx]
  have hx2 := mul_le_mul_of_nonneg_right (show 10 ≤ x by linarith only [hx]) hx0
  have hp := (weighted_euler_pos (show 5 ≤ x by linarith only [hx])).le
  have hh := mul_le_mul_of_nonneg_right (show 2 * x ≤ x ^ 2 / 5 by nlinarith only [hx2]) hp
  have hp' := mul_nonneg (sq_nonneg x) hp
  linarith only [h, hh, hp']

end PseudoPrime.PrimeTestBounds.MillerRabin
