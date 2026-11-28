/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterShift663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerTail663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalWeights656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentIntegral656
import PseudoPrime.AnalyticNumberTheory.Arithmetic.WeightedAbelInterval
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMass656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterThetaPoly656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterProfile663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalTrivial656
import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleMonotonicity

/-! # Signed Abel formula for the principal forward tail -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At an endpoint the principal tail above any integer cutoff is a finite
Mangoldt sum, restricted by the upper support of the forward weight. -/
theorem quarter_endpoint_tail_finite_663 {u : ℝ} (hu : 0 < u) (N : ℕ) :
    let W := fun n ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) u n).re
    (∑' n : ℕ, W n) - (∑ n ∈ Finset.Ioc 0 N, W n) =
      ∑ n ∈ Finset.Ioc N ⌊u * Real.exp (21 / 8)⌋₊,
        ArithmeticFunction.vonMangoldt n * quarterWeight656 u n := by
  intro W
  classical
  have hW : Summable W :=
    (Complex.hasSum_re
        (LLS.PaperStatements.MellinKernel.summable_summand quarterKernel656
            (1 : DirichletCharacter ℂ 1) hu).hasSum).summable
  rw [←
    tsum_above_eq hW
      (by simp only [W, principal_summand_eq hu, ArithmeticFunction.map_zero, zero_mul])]
  let y := u * Real.exp (21 / 8)
  let F := fun n : ℕ ↦ if N < n then W n else 0
  have ht := tsum_subtype {n : ℕ | N < n} W
  change (∑' n : { n : ℕ // N < n }, W n.val) = _ at ht
  have ht' : (∑' n : { n : ℕ // N < n }, W n.val) = ∑' n : ℕ, F n := by
    simpa only [F, Set.indicator, Set.mem_ofPred] using ht
  rw [ht']
  have hy : 0 < y := mul_pos hu (Real.exp_pos _)
  refine (tsum_eq_sum ?_).trans (Finset.sum_congr rfl ?_)
  · intro n hn
    by_cases h : N < n
    · have hny := Nat.lt_of_floor_lt (lt_of_not_ge (fun h' ↦ hn (Finset.mem_Ioc.mpr ⟨h, h'⟩)))
      have hn₀ := hy.trans hny
      have hs : ¬Real.log ((n : ℝ) / u) ≤ 21 / 8 := by
        intro h'
        exact
          hny.not_ge
            ((div_le_iff₀ hu).mp ((Real.log_le_iff_le_exp (div_pos hn₀ hu)).mp h') |>.trans_eq
              (mul_comm _ _))
      simp only [F, W, ite_eq_left h, principal_summand_eq hu, ite_eq_right hs, mul_zero]
    · exact ite_eq_right h
  · intro n hn
    have hn₁ := (Finset.mem_Ioc.mp hn).1
    have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.zero_le N |>.trans_lt hn₁)
    have hn₂ := (Nat.le_floor_iff hy.le).mp (Finset.mem_Ioc.mp hn).2
    have hs :=
      (Real.log_le_iff_le_exp (div_pos hn₀ hu)).mpr
        ((div_le_iff₀ hu).mpr (hn₂.trans_eq (mul_comm _ _)))
    simp only [F, W, ite_eq_left hn₁, principal_summand_eq hu, ite_eq_left hs]

/-- The principal tail above a positive squared radius is its continuous
mass minus the signed cutoff and derivative terms. The upper boundary vanishes. -/
theorem quarter_principal_abel_663 {x : ℝ} (hx : 0 < x) :
    let W := fun n ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) x n).re
    let y := x * Real.exp (21 / 8)
    (∑' n : ℕ, W n) - (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, W n) =
      (∫ t in x..y, quarterWeight656 x t) - (Chebyshev.psi x - x) * quarterWeight656 x x -
        ∫ t in x..y, (Chebyshev.psi t - t) * deriv (quarterWeight656 x) t := by
  intro W y
  have hy : x ≤ y := le_mul_of_one_le_right hx.le (Real.one_le_exp (by norm_num only))
  rw [quarter_endpoint_tail_finite_663 hx]
  have hd := weight_smooth_656 hx
  have hs : Set.Icc x y ⊆ Set.Ioi 0 := fun _ h ↦ hx.trans_le h.1
  have hcont : ContinuousOn (deriv (quarterWeight656 x)) (Set.Icc x y) :=
    (hd.continuousOn_deriv_of_isOpen isOpen_Ioi (by decide)).mono hs
  have ha :=
    AnalyticNumberTheory.Arithmetic.mangoldt_centered_abel_interval hx.le hy
      (fun t ht ↦
        (hd.differentiableOn (by decide) t (hs ht)).differentiableAt (isOpen_Ioi.mem_nhds (hs ht)))
      hcont.integrableOn_Icc
  have hb : quarterWeight656 x y = 0 := by
    unfold quarterWeight656
    dsimp only [y]
    rw [mul_div_cancel_left₀ _ hx.ne', Real.log_exp]
    norm_num only [zero_mul, zero_div, mul_zero]
  rw [hb, mul_zero, zero_sub] at ha
  linarith only [ha]

/-- The normalized continuous mass above the tested cutoff. Multiplying
by the radius gives the continuous forward tail at the squared scale. -/
@[expose]
noncomputable def quarterTailMass663 : ℝ :=
  ∫ u in (1 : ℝ)..Real.exp (21 / 8), (quarterKernel656.transform u).re / Real.sqrt u

private theorem tail_mass_split :
    (∫ u in (0 : ℝ)..1, (quarterKernel656.transform u).re / Real.sqrt u) + quarterTailMass663 =
      (quarterKernel656.function (1 / 2)).re := by
  let f := fun u ↦ (quarterKernel656.transform u).re / Real.sqrt u
  let b := Real.exp (21 / 8 : ℝ)
  have hb : 1 ≤ b := Real.one_le_exp (by norm_num only)
  have hi := LLS.PaperStatements.MellinKernel.integrableOn_weight_Ioi quarterKernel656
  have hcut : (∫ u in Set.Ioi b, f u) = 0 := by
    refine
      (MeasureTheory.setIntegral_congr_fun (g := fun _ ↦ 0) measurableSet_Ioi ?_).trans
        (by simp only [MeasureTheory.integral_zero])
    intro u hu
    have hu' : b < u := hu
    have hu₀ := (Real.exp_pos (21 / 8 : ℝ)).trans hu'
    have hz :=
      Analysis.rationalPoleProfile_eq_zero 3 (5 / 11) (21 / 16)
        (by
          rw [show 2 * (21 / 16 : ℝ) = 21 / 8 by norm_num only]
          exact hu')
    dsimp only [f]
    rw [quarterKernel656, LLS.PaperStatements.rationalPole_transform _ _ _ _ hu₀, hz]
    simp only [Complex.ofReal_zero, Complex.zero_re, zero_div]
  have hfull := LLS.PaperStatements.MellinKernel.integral_weight_Ioi_eq quarterKernel656
  change (∫ u in Set.Ioi (0 : ℝ), f u) = _ at hfull
  rw [← Set.Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num only),
    MeasureTheory.setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hi.mono_set fun _ ht ↦ ht.1) (hi.mono_set fun _ ht ↦ zero_lt_one.trans ht),
    ← Set.Ioc_union_Ioi_eq_Ioi hb,
    MeasureTheory.setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hi.mono_set fun _ ht ↦ zero_lt_one.trans ht.1)
      (hi.mono_set fun _ ht ↦ (zero_lt_one.trans_le hb).trans ht),
    hcut, add_zero] at hfull
  unfold quarterTailMass663
  rw [intervalIntegral.integral_of_le (by norm_num only : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_of_le hb]
  exact hfull

/-- A rational lower bound for the normalized principal tail mass,
obtained from the exact cutoff moment and two exponential Taylor bounds. -/
theorem quarter_tail_mass_lower_663 : (0.088044185448 : ℝ) ≤ quarterTailMass663 := by
  have hp := profile_exp_error (21 / 16 : ℚ) (by norm_num only)
  have hn := profile_exp_error (-(231 / 80 : ℚ)) (by norm_num only)
  have hpQ : (3.71545073794110 : ℚ) ≤ profileExpTaylor (21 / 16) - 1 / 10 ^ 16 := by decide +kernel
  have hnQ : profileExpTaylor (-(231 / 80)) + 1 / 10 ^ 16 ≤ (0.05571532696350 : ℚ) := by
    decide +kernel
  have hpR := (Rat.cast_le (K := ℝ)).mpr hpQ
  have hnR := (Rat.cast_le (K := ℝ)).mpr hnQ
  norm_num only [Rat.cast_ofScientific, Rat.cast_add, Rat.cast_sub, Rat.cast_neg, Rat.cast_div,
    Rat.cast_pow, Rat.cast_ofNat] at hp hn hpR hnR
  have h := tail_mass_split
  rw [quarterKernel656, LLS.PaperStatements.rationalPole_half_value,
    LLS.PaperStatements.rationalPole_cutoff_moment _ _ _ _ (by norm_num only)] at h
  norm_num only [Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd, Finset.sum_range_succ,
    Finset.sum_range_zero, Nat.choose_zero_right, Nat.choose_self, Nat.choose_one_right, Nat.choose,
    Nat.factorial, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
  linarith only [h, hpR, hnR, (abs_le.mp hp).1, (abs_le.mp hn).2]

/-- The normalized forward mass is at most 0.089. The normalized total
mass and the same Taylor certificates give the opposite side of the enclosure. -/
theorem quarter_tail_mass_upper_663 : quarterTailMass663 ≤ (0.089 : ℝ) := by
  have hp := profile_exp_error (21 / 16 : ℚ) (by norm_num only)
  have hn := profile_exp_error (-(231 / 80 : ℚ)) (by norm_num only)
  have hpQ : profileExpTaylor (21 / 16) + 1 / 10 ^ 16 ≤ (3.71545073794111 : ℚ) := by decide +kernel
  have hnQ : (0.05571532696349 : ℚ) ≤ profileExpTaylor (-(231 / 80)) - 1 / 10 ^ 16 := by
    decide +kernel
  have hpR := (Rat.cast_le (K := ℝ)).mpr hpQ
  have hnR := (Rat.cast_le (K := ℝ)).mpr hnQ
  norm_num only [Rat.cast_ofScientific, Rat.cast_add, Rat.cast_sub, Rat.cast_neg, Rat.cast_div,
    Rat.cast_pow, Rat.cast_ofNat] at hp hn hpR hnR
  have h := tail_mass_split
  rw [quarterKernel656, LLS.PaperStatements.rationalPole_half_value,
    LLS.PaperStatements.rationalPole_cutoff_moment _ _ _ _ (by norm_num only)] at h
  norm_num only [Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd, Finset.sum_range_succ,
    Finset.sum_range_zero, Nat.choose_zero_right, Nat.choose_self, Nat.choose_one_right, Nat.choose,
    Nat.factorial, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
  linarith only [h, hpR, hnR, (abs_le.mp hp).2, (abs_le.mp hn).1]

/-- The principal integral cancels the positive half-point residue and
the linear principal coefficient, leaving only the signed Abel errors. -/
theorem quarter_principal_integral_cancel_663 {r : ℝ} (hr : 0 < r) :
    let x := r ^ 2
    4 * (∫ t in x..x * Real.exp (21 / 8), quarterWeight656 x t) -
          3 * ((11 / 10 : ℝ) ^ 5 / (8 / 5) ^ 6 * Real.exp (21 / 16)) * r +
        0.71780481 * r <
      0 := by
  intro x
  let b := Real.exp (21 / 8 : ℝ)
  have hb : 1 ≤ b := Real.one_le_exp (by norm_num only)
  have hx : 0 < x := sq_pos_of_pos hr
  have hs := quarter_scale_integral_656 hx hx (le_mul_of_one_le_right hx.le hb) le_rfl
  rw [div_self hx.ne', mul_div_cancel_left₀ _ hx.ne', Real.sqrt_sq hr.le] at hs
  change _ = r * quarterTailMass663 at hs
  have hδ := mul_lt_mul_of_pos_right quarter_principal_delta_656 hr
  have hhalf :
    (quarterKernel656.function (1 / 2)).re * r =
      ((11 / 10 : ℝ) ^ 5 / (8 / 5) ^ 6 * Real.exp (21 / 16)) * r := by
    rw [quarterKernel656, LLS.PaperStatements.rationalPole_half_value]
    norm_num only [Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd]
    ring
  dsimp only [x] at hs ⊢
  nlinarith only [hs, hδ, hhalf, congrArg (fun z : ℝ ↦ r * z) tail_mass_split]

/-- The final arithmetic comparison retains the signed cutoff and
derivative terms, the inverse-scale conductor and the negative pole. -/
theorem quarter_signed_comparison_663 {p q k : ℕ} [NeZero p] [NeZero q] [NeZero k]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ k}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hk : 2 ≤ k)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r : ℝ}
    (hr : r ∈ Set.Icc 328 (663 / 2)) (hL : Real.log p + Real.log q + Real.log k = 4 * r)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hpa : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → a n = 1)
    (hpb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → b n = 1)
    (hpc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → c n = 1) (K : Finset ℕ)
    (hK : ∀ n ∈ K, r ^ 2 < (n : ℝ)) (hU : ∀ n ∈ K, Real.log ((n : ℝ) / r ^ 2) ≤ 21 / 8)
    (hpow : ∀ n ∈ K, ∃ p k : ℕ, p.Prime ∧ 2 ≤ k ∧ n = p ^ k) :
    let x := r ^ 2
    let z := (11 / 10 : ℝ) * (21 / 8 + 2 * Real.log r)
    (∑ n ∈ K, 4 * (ArithmeticFunction.vonMangoldt n * quarterWeight656 x n)) <
      -4 * (Chebyshev.psi x - x) * quarterWeight656 x x -
            4 *
              (∫ t in x..x * Real.exp (21 / 8),
                (Chebyshev.psi t - t) * deriv (quarterWeight656 x) t) +
          4 * r * (z ^ 5 * Real.exp (-z) / 120) -
        3 * (((11 / 10 : ℝ) ^ 5 / (3 / 5) ^ 6) * Real.exp (-(21 / 16)) / r) -
        1.49369637 -
        0.0219746789 * (663 / 2 - r) := by
  intro x z
  have hr₀ : 0 < r := by linarith only [hr.1]
  have hr₁ : 1 ≤ r := by linarith only [hr.1]
  have hs := quarter_scalar_comparison_663 ha hb hc hp hq hk hG hr hL ht hpa hpb hpc K hK hU hpow
  have hA := quarter_principal_abel_663 (sq_pos_of_pos hr₀)
  have hI := quarter_principal_integral_cancel_663 hr₀
  have hP := main_poles_656 hr₀
  have hC := main_conductor_656 hr₁
  dsimp only at hs hA hI hP hC
  rw [hA, hC, hP.1, hP.2] at hs
  dsimp only [x, z]
  linarith only [hs, hI]

private theorem main_conductor_antitone :
    AntitoneOn (fun r : ℝ ↦ 4 * r * (quarterKernel656.transform (r ^ 2)⁻¹).re) (Set.Ici 328) := by
  intro a ha r hr har
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound (N := 328) (j := 9) (n := 27) (lo := 5.793) (hi := 6)
        (by decide +kernel)).1
  norm_num only [Rat.cast_ofScientific, Rat.cast_ofNat] at hlog
  have hm :=
    refined_log_fifth_antitone (b := 21 / 8) (p := 6 / 5) (E := 328) (by norm_num only)
      (by norm_num only) (by linarith only [hlog])
  have he (t : ℝ) (ht : 1 ≤ t) :
    4 * t * (quarterKernel656.transform (t ^ 2)⁻¹).re =
      ((11 / 10 : ℝ) ^ 5 / 30 * Real.exp ((11 / 10) * -(21 / 8))) *
        ((21 / 8 + 2 * Real.log t) ^ 5 * t ^ (-(6 / 5) : ℝ)) := by
    rw [main_conductor_factor_656 ht]
    ring
  have h₁ : 328 ≤ a := ha
  have h₂ : 328 ≤ r := hr
  change
    4 * r * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤
      4 * a * (quarterKernel656.transform (a ^ 2)⁻¹).re
  rw [he r (by linarith only [h₂]), he a (by linarith only [h₁])]
  exact mul_le_mul_of_nonneg_left (hm ha hr har) (by positivity)

private theorem main_conductor_midpoint :
    4 * (1319 / 4 : ℝ) * (quarterKernel656.transform ((1319 / 4 : ℝ) ^ 2)⁻¹).re ≤ 1.654812 := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1319 / 4) (j := 9) (n := 27) (lo := 5) (hi :=
        11.59667 / 2) (by decide +kernel)).2
  have h :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 108735) (p := 3) (d :=
        5) (lo := 0) (hi := 0.000950996) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, neg_div] at hl h
  have hp : (1319 / 4 : ℝ) ^ (-(6 / 5) : ℝ) ≤ 0.000950996 := by
    rw [show (-(6 / 5 : ℝ)) = ((2 : ℕ) : ℝ) * (-(3 / 5)) by norm_num only,
      Real.rpow_natCast_mul (by norm_num only : (0 : ℝ) ≤ 1319 / 4)]
    refine
      (Real.rpow_le_rpow_of_nonpos (by norm_num only : (0 : ℝ) < 108735) (by norm_num only)
            (by norm_num only)).trans
        ?_
    norm_num only at h ⊢
    exact h
  have hb :=
    main_conductor_box (r := 1319 / 4) (u := 1319 / 4) (z := 11.59667) (C := 1.654812)
      (by norm_num only) le_rfl (by linarith only [hl]) hp (by norm_num only) (by norm_num only)
  simpa only [sub_self, mul_zero, add_zero] using hb

/-- The left endpoint and the midpoint at 329.75 give two upper bounds
for the decreasing inverse-scale conductor. -/
theorem quarter_main_conductor_box_663 {r : ℝ} (hr : 328 ≤ r) :
    4 * r * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤
      1.659189 - (if 1319 / 4 ≤ r then 0.004377 else 0) := by
  by_cases h : 1319 / 4 ≤ r
  · rw [ite_eq_left h]
    exact
      (main_conductor_antitone (by norm_num only [Set.mem_Ici] : (1319 / 4 : ℝ) ∈ Set.Ici 328) hr
            h).trans
        (main_conductor_midpoint.trans (by norm_num only))
  · rw [ite_eq_right h, sub_zero]
    have hb := main_conductor_328_656 (by norm_num only : (322 : ℝ) ≤ 328) le_rfl
    rw [sub_self, mul_zero, add_zero] at hb
    exact (main_conductor_antitone (le_refl 328) hr hr).trans hb

private theorem negative_pole_lower :
    (9.29061 : ℝ) ≤ (11 / 10) ^ 5 / (3 / 5) ^ 6 * Real.exp (-(21 / 16)) := by
  have h := profile_exp_error (-(21 / 16 : ℚ)) (by norm_num only)
  have hq : (26914634 : ℚ) / 10 ^ 8 ≤ profileExpTaylor (-(21 / 16)) - 1 / 10 ^ 16 := by
    decide +kernel
  have hc := (Rat.cast_le (K := ℝ)).mpr hq
  norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_sub, Rat.cast_pow, Rat.cast_ofNat] at h hc
  linarith only [(abs_le.mp h).1, hc]

/-- On all section 137 radii, the conductor, negative half-point pole
and constant term together cost at most 0.081415. -/
theorem quarter_main_scalar_box_663 {r : ℝ} (hr : r ∈ Set.Icc 328 (663 / 2)) :
    let z := (11 / 10 : ℝ) * (21 / 8 + 2 * Real.log r)
    4 * r * (z ^ 5 * Real.exp (-z) / 120) -
        3 * (((11 / 10 : ℝ) ^ 5 / (3 / 5) ^ 6) * Real.exp (-(21 / 16)) / r) -
        1.49369637 ≤
      0.081415 - (if 1319 / 4 ≤ r then 0.004377 else 0) := by
  intro z
  have hr₀ : 0 < r := by linarith only [hr.1]
  have hp :=
    (div_le_div_of_nonneg_left (by norm_num only : (0 : ℝ) ≤ 9.29061) hr₀ hr.2).trans
      (div_le_div_of_nonneg_right negative_pole_lower hr₀.le)
  have hc := quarter_main_conductor_box_663 hr.1
  rw [main_conductor_656 (by linarith only [hr.1] : 1 ≤ r)] at hc
  dsimp only [z]
  linarith only [hc, hp]

/-- The main kernel constants are absorbed into a uniform scalar cost.
Only the signed Abel contribution remains to be compared with the recovered powers. -/
theorem quarter_numeric_comparison_663 {p q k : ℕ} [NeZero p] [NeZero q] [NeZero k]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ k}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hk : 2 ≤ k)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r : ℝ}
    (hr : r ∈ Set.Icc 328 (663 / 2)) (hL : Real.log p + Real.log q + Real.log k = 4 * r)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hpa : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → a n = 1)
    (hpb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → b n = 1)
    (hpc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → c n = 1) (K : Finset ℕ)
    (hK : ∀ n ∈ K, r ^ 2 < (n : ℝ)) (hU : ∀ n ∈ K, Real.log ((n : ℝ) / r ^ 2) ≤ 21 / 8)
    (hpow : ∀ n ∈ K, ∃ p k : ℕ, p.Prime ∧ 2 ≤ k ∧ n = p ^ k) :
    let x := r ^ 2
    (∑ n ∈ K, 4 * (ArithmeticFunction.vonMangoldt n * quarterWeight656 x n)) <
      -4 * (Chebyshev.psi x - x) * quarterWeight656 x x -
            4 *
              (∫ t in x..x * Real.exp (21 / 8),
                (Chebyshev.psi t - t) * deriv (quarterWeight656 x) t) +
          0.081415 -
        0.0219746789 * (663 / 2 - r) -
        (if 1319 / 4 ≤ r then 0.004377 else 0) := by
  intro x
  have h := quarter_signed_comparison_663 ha hb hc hp hq hk hG hr hL ht hpa hpb hpc K hK hU hpow
  have hB := quarter_main_scalar_box_663 hr
  dsimp only [x] at h hB ⊢
  linarith only [h, hB]

/-- On the forward tail the shifted coordinate is at most 231/80.
The fifth-power term therefore cannot outweigh the negative fourth-power term. -/
theorem quarter_tail_weight_deriv_nonpos_663 {x t : ℝ} (hx : 0 < x)
    (ht : t ∈ Set.Icc x (x * Real.exp (21 / 8))) : deriv (quarterWeight656 x) t ≤ 0 := by
  have ht₀ := hx.trans_le ht.1
  have h₀ := Real.log_nonneg ((le_div_iff₀ hx).mpr (by simpa only [one_mul] using ht.1))
  have h₁ :=
    (Real.log_le_iff_le_exp (div_pos ht₀ hx)).mpr
      ((div_le_iff₀ hx).mpr (ht.2.trans_eq (mul_comm _ _)))
  have hv : shiftedCoord x t ∈ Set.Icc 0 (231 / 80) := by
    unfold shiftedCoord
    exact ⟨by linarith only [h₁], by linarith only [h₀]⟩
  have hpoly : (3 / 5 : ℝ) * shiftedCoord x t - 5 * (11 / 10) ≤ 0 := by linarith only [hv.2]
  have hf : 0 ≤ weightFactor x t := by
    unfold weightFactor; positivity
  have hd := log_deriv hx ht₀
  dsimp only at hd
  have hh : t * deriv (quarterWeight656 x) t ≤ 0 := by
    rw [hd]
    have h := mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hv.1 4) hpoly
    nlinarith only [mul_nonpos_of_nonneg_of_nonpos hf h]
  exact nonpos_of_mul_nonpos_right hh ht₀

/-- The signed derivative contribution is bounded by the integral of a
majorant for the Chebyshev error, weighted by the negative kernel derivative. -/
theorem quarter_tail_error_majorant_663 {x : ℝ} (hx : 0 < x) {E : ℝ → ℝ}
    (hE : ∀ t ∈ Set.Icc x (x * Real.exp (21 / 8)), Chebyshev.psi t - t ≤ E t)
    (hi :
      IntervalIntegrable (fun t ↦ (Chebyshev.psi t - t) * deriv (quarterWeight656 x) t)
        MeasureTheory.volume x (x * Real.exp (21 / 8)))
    (hI :
      IntervalIntegrable (fun t ↦ E t * deriv (quarterWeight656 x) t) MeasureTheory.volume x
        (x * Real.exp (21 / 8))) :
    -(∫ t in x..x * Real.exp (21 / 8), (Chebyshev.psi t - t) * deriv (quarterWeight656 x) t) ≤
      -(∫ t in x..x * Real.exp (21 / 8), E t * deriv (quarterWeight656 x) t) := by
  have hy := le_mul_of_one_le_right hx.le (Real.one_le_exp (by norm_num only : (0 : ℝ) ≤ 21 / 8))
  apply neg_le_neg
  exact
    intervalIntegral.integral_mono_on hy hI hi fun t ht ↦
      mul_le_mul_of_nonpos_right (hE t ht) (quarter_tail_weight_deriv_nonpos_663 hx ht)

/-- A constant signed Chebyshev bound on a subinterval costs that constant
times the drop in the kernel weight. This applies to each certified interval. -/
theorem quarter_tail_error_cell_663 {x a b C : ℝ} (hx : 0 < x) (ha : x ≤ a) (hab : a ≤ b)
    (hb : b ≤ x * Real.exp (21 / 8)) (hψ : ∀ t ∈ Set.Icc a b, Chebyshev.psi t - t ≤ C) :
    -(∫ t in a..b, (Chebyshev.psi t - t) * deriv (quarterWeight656 x) t) ≤
      C * (quarterWeight656 x a - quarterWeight656 x b) := by
  have hsub : Set.Icc a b ⊆ Set.Ioi 0 := fun _ h ↦ hx.trans_le (ha.trans h.1)
  have hs := weight_smooth_656 hx
  have hc : ContinuousOn (deriv (quarterWeight656 x)) (Set.Icc a b) :=
    (hs.continuousOn_deriv_of_isOpen isOpen_Ioi (by decide)).mono hsub
  have hψI : IntervalIntegrable Chebyshev.psi MeasureTheory.volume a b :=
    Chebyshev.psi_mono.intervalIntegrable
  have hi := hψI.sub (continuous_id.intervalIntegrable a b)
  have hI := hi.mul_continuousOn (by simpa only [Set.uIcc_of_le hab] using hc)
  have hD : IntervalIntegrable (deriv (quarterWeight656 x)) MeasureTheory.volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 hc.integrableOn_Icc
  have hC := hD.const_mul C
  have hm :=
    intervalIntegral.integral_mono_on hab hC hI fun t ht ↦
      mul_le_mul_of_nonpos_right (hψ t ht)
        (quarter_tail_weight_deriv_nonpos_663 hx ⟨ha.trans ht.1, ht.2.trans hb⟩)
  have hd :
    (∫ t in a..b, deriv (quarterWeight656 x) t) = quarterWeight656 x b - quarterWeight656 x a := by
    apply intervalIntegral.integral_deriv_eq_sub
    · intro t ht
      have ht' := hsub ((Set.uIcc_of_le hab) ▸ ht)
      exact (hs.differentiableOn (by decide) t ht').differentiableAt (isOpen_Ioi.mem_nhds ht')
    · exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 hc.integrableOn_Icc
  rw [intervalIntegral.integral_const_mul, hd] at hm
  simp only [id_eq] at hm
  linarith only [hm]

private theorem main_conductor_k197_endpoint :
    4 * (6643 / 20 : ℝ) * (quarterKernel656.transform ((6643 / 20 : ℝ) ^ 2)⁻¹).re ≤ 1.64886 := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 6643 / 20) (j := 9) (n := 27) (lo := 5) (hi :=
        11.61118 / 2) (by decide +kernel)).2
  have h :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 6643 / 20) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000942756) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, neg_div] at hl h
  have hp : (6643 / 20 : ℝ) ^ (-(6 / 5) : ℝ) ≤ 0.000942756 := by
    norm_num only at h ⊢
    exact h
  have hb :=
    main_conductor_box (r := 6643 / 20) (u := 6643 / 20) (z := 11.61118) (C := 1.64886)
      (by norm_num only) le_rfl (by linarith only [hl]) hp (by norm_num only) (by norm_num only)
  simpa only [sub_self, mul_zero, add_zero] using hb

/-- The inverse-scale conductor after 332.15 is bounded by its
certified left endpoint value. -/
theorem quarter_main_conductor_k197 {r : ℝ} (hr : 332.15 ≤ r) :
    4 * r * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.64886 := by
  have hl : (6643 / 20 : ℝ) ∈ Set.Ici 328 := by norm_num only [Set.mem_Ici]
  have h : (6643 / 20 : ℝ) ≤ r := by linarith only [hr]
  exact (main_conductor_antitone hl (hl.trans h) h).trans main_conductor_k197_endpoint

end PseudoPrime.PrimeTestBounds.MillerRabin
