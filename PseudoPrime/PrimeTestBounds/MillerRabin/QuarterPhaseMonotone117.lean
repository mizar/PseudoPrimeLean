/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhase117
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseReflectedMonotone117

/-! # Monotonicity of the section 117 main phase terms -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The decaying fifth power associated to the shifted conductor in §117. -/
noncomputable def phaseConductorMonomial117 (h x : ℝ) : ℝ :=
  Real.exp (-(13 / 25) * x) * (x - h) ^ 5

private theorem phase_conductor_deriv117 (h x : ℝ) :
    HasDerivAt (phaseConductorMonomial117 h)
      (-(Real.exp (-(13 / 25) * x) * ((x - h) ^ 4 * (13 / 25 * (x - h) - 5)))) x := by
  have he := ((hasDerivAt_id x).const_mul (-(13 / 25 : ℝ))).exp
  have hp := ((hasDerivAt_id x).sub_const h).pow 5
  apply (he.mul hp).congr_deriv
  norm_num only [id_eq, Nat.cast_ofNat, Pi.pow_apply]
  ring

/-- The far shifted positive monomial decreases above log cutoff 11.48. -/
theorem phase_far_conductor_antitone117 :
    AntitoneOn (phaseConductorMonomial117 (11 / 10)) (Set.Ici 11.48) := by
  let h := phase_conductor_deriv117 (11 / 10)
  apply
    antitoneOn_of_deriv_nonpos (convex_Ici _) (fun x _ ↦ (h x).continuousAt.continuousWithinAt)
      (fun x _ ↦ (h x).differentiableAt.differentiableWithinAt)
  intro x hx
  have hb : 11.48 ≤ x := interior_subset hx
  rw [(h x).deriv]
  exact
    neg_nonpos.mpr
      (mul_nonneg (Real.exp_pos _).le
        (mul_nonneg (pow_nonneg (by linarith only [hb]) 4) (by linarith only [hb])))

private theorem phase_near_slope_sign117 {x : ℝ} (hx : 11.48 ≤ x) :
    x ^ 4 * (13 / 25 * x - 5) ≤
      Real.exp ((51 / 50) * (1 / 50)) * ((x - 1 / 50) ^ 4 * (13 / 25 * (x - 1 / 50) - 5)) := by
  have hx0 : 0 ≤ x := by linarith only [hx]
  have hk : 0 ≤ (13 / 25 : ℝ) * x - 5 := by linarith only [hx]
  have ha : 0.9982 * x ≤ x - 1 / 50 := by linarith only [hx]
  have hb : 0.9892 * ((13 / 25 : ℝ) * x - 5) ≤ 13 / 25 * (x - 1 / 50) - 5 := by linarith only [hx]
  have h :=
    mul_le_mul (pow_le_pow_left₀ (mul_nonneg (by norm_num only) hx0) ha 4) hb
      (mul_nonneg (by norm_num only) hk) (pow_nonneg (by linarith only [hx]) 4)
  have hE : (1.0204 : ℝ) ≤ Real.exp ((51 / 50) * (1 / 50)) := by
    linarith only [Real.add_one_le_exp ((51 / 50 : ℝ) * (1 / 50))]
  have hp := mul_nonneg (pow_nonneg hx0 4) hk
  have h' :=
    mul_le_mul hE h
      (mul_nonneg (pow_nonneg (mul_nonneg (by norm_num only) hx0) 4)
        (mul_nonneg (by norm_num only) hk))
      (Real.exp_pos _).le
  have hc :=
    mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 1.0204 * 0.9982 ^ 4 * 0.9892 by norm_num only) hp
  linear_combination h' + hc

/-- The difference of the base and near shifted conductor monomials increases
on the full log-cutoff half-line starting at 11.48. -/
theorem phase_near_conductor_mono117 :
    MonotoneOn
      (fun x : ℝ ↦
        phaseConductorMonomial117 0 x -
          Real.exp ((51 / 50) * (1 / 50)) * phaseConductorMonomial117 (1 / 50) x)
      (Set.Ici 11.48) := by
  have h (x : ℝ) :=
    (phase_conductor_deriv117 0 x).sub
      ((phase_conductor_deriv117 (1 / 50) x).const_mul (Real.exp ((51 / 50) * (1 / 50))))
  apply
    monotoneOn_of_deriv_nonneg (convex_Ici _) (fun x _ ↦ (h x).continuousAt.continuousWithinAt)
      (fun x _ ↦ (h x).differentiableAt.differentiableWithinAt)
  intro x hx
  rw [(h x).deriv, sub_zero]
  have hb : 11.48 ≤ x := interior_subset hx
  have he :=
    mul_le_mul_of_nonneg_left (phase_near_slope_sign117 hb) (Real.exp_pos (-(13 / 25) * x)).le
  linear_combination he

/-- The reciprocal pole coefficient in the section 117 remainder. -/
noncomputable def phaseRecip117 : ℝ :=
  -(3 * (51 / 50 : ℝ) ^ 5 / (13 / 25) ^ 6) *
    (3.143 - 3.124 * Real.exp (1 / 100) - 0.0374 * Real.exp (11 / 20))

private theorem phase_recip_upper117 : phaseRecip117 ≤ 14 := by
  have h₁ :=
    Analysis.exp_le_taylor_add_two_next (x := (1 / 100 : ℝ)) (n := 16) (by norm_num only)
      (by norm_num only)
  have h₂ :=
    Analysis.exp_le_taylor_add_two_next (x := (11 / 20 : ℝ)) (n := 16) (by norm_num only)
      (by norm_num only)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at h₁ h₂
  unfold phaseRecip117
  linarith only [h₁, h₂]

private theorem phase_near_exp_upper117 : Real.exp ((51 / 50 : ℝ) * (1 / 50)) ≤ 1.021 := by
  have h :=
    Analysis.exp_le_taylor_add_two_next (x := (51 / 50 : ℝ) * (1 / 50)) (n := 16) (by norm_num only)
      (by norm_num only)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at h
  linarith only [h]

private theorem phase_exp_window117 {x : ℝ} (hx : x ∈ Set.Icc 11.48 12) :
    (1 / 550 : ℝ) ≤ Real.exp (-(13 / 25) * x) ∧
      Real.exp (-(13 / 25) * x) ≤ 1 / 375 ∧ Real.exp (-x / 2) ≤ 1 / 250 := by
  have hl := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 5.9696 by norm_num only) 24
  have hq := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 5.74 by norm_num only) 24
  have hu :=
    Analysis.exp_le_taylor_add_two_next (x := (6.24 : ℝ)) (n := 24) (by norm_num only)
      (by norm_num only)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at hl hq hu
  have h1 : (375 : ℝ) ≤ Real.exp 5.9696 := by linarith only [hl]
  have h2 : (250 : ℝ) ≤ Real.exp 5.74 := by linarith only [hq]
  have h3 : Real.exp 6.24 ≤ 550 := by linarith only [hu]
  rw [neg_mul, Real.exp_neg, neg_div, Real.exp_neg, ← one_div, ← one_div]
  exact
    ⟨one_div_le_one_div_of_le (Real.exp_pos _)
        (le_trans (Real.exp_le_exp.mpr (by linarith only [hx.2])) h3),
      one_div_le_one_div_of_le (by norm_num only)
        (h1.trans (Real.exp_le_exp.mpr (by linarith only [hx.1]))),
      one_div_le_one_div_of_le (by norm_num only)
        (h2.trans (Real.exp_le_exp.mpr (by linarith only [hx.1])))⟩

private theorem phase_main_deriv117 (x : ℝ) :
    HasDerivAt (fun t ↦ -4 * threeShiftEulerMain (Real.exp t))
      (4 * Real.exp (-(13 / 25) * x) * threeShiftEulerPoly x) x := by
  have h := (three_shift_main_log_deriv (x / 2)).comp x ((hasDerivAt_id x).div_const 2)
  have h' := h.const_mul (-4)
  have he (t : ℝ) : 2 * (t / 2) = t := by ring
  simpa only [Function.comp_apply, id_eq, he, mul_one] using
    (h'.congr_deriv
      (by
        rw [he]; ring))

/-- The increase of the main Euler tail recovery pays for the decrease of the
small positive conductor term and the reciprocal pole on the log window. -/
theorem phase_main_conductor_mono117 :
    MonotoneOn
      (fun x : ℝ ↦
        -4 * threeShiftEulerMain (Real.exp x) +
          ((51 / 50 : ℝ) ^ 5 / 30 * 0.019 * Real.exp ((51 / 50) * (1 / 50))) *
            phaseConductorMonomial117 (1 / 50) x +
          phaseRecip117 * Real.exp (-x / 2))
      (Set.Icc 11.48 12) := by
  let C := (51 / 50 : ℝ) ^ 5 / 30 * 0.019 * Real.exp ((51 / 50) * (1 / 50))
  have hd (x : ℝ) :=
    ((phase_main_deriv117 x).add ((phase_conductor_deriv117 (1 / 50) x).const_mul C)).add
      ((((hasDerivAt_id x).neg).div_const 2).exp.const_mul phaseRecip117)
  apply
    monotoneOn_of_deriv_nonneg (convex_Icc _ _) (fun x _ ↦ (hd x).continuousAt.continuousWithinAt)
      (fun x _ ↦ (hd x).differentiableAt.differentiableWithinAt)
  intro x hx
  have hx' := interior_subset hx
  have ⟨hle, hhi, hrec⟩ := phase_exp_window117 hx'
  rw [(hd x).deriv]
  simp only [Pi.neg_apply, id_eq]
  have hp := three_shift_euler_poly_gt14 (show 11.4 ≤ x by linarith only [hx'.1])
  have hplus := mul_le_mul hle hp.le (by norm_num only) (Real.exp_pos _).le
  have hC : C ≤ (51 / 50 : ℝ) ^ 5 / 30 * 0.019 * 1.021 :=
    mul_le_mul_of_nonneg_left phase_near_exp_upper117 (by norm_num only)
  have hx0 : 0 ≤ x - 1 / 50 := by linarith only [hx'.1]
  have ha := pow_le_pow_left₀ hx0 (show x - 1 / 50 ≤ 12 by linarith only [hx'.2]) 4
  have hb : 13 / 25 * (x - 1 / 50) - 5 ≤ (13 / 25 : ℝ) * 12 - 5 := by linarith only [hx'.2]
  have hh := mul_le_mul ha hb (by linarith only [hx'.1]) (by norm_num only)
  have hP : 0 ≤ (x - 1 / 50) ^ 4 * (13 / 25 * (x - 1 / 50) - 5) :=
    mul_nonneg (pow_nonneg hx0 _) (by linarith only [hx'.1])
  have hc := mul_le_mul hhi hh hP (by norm_num only)
  have hcost := mul_le_mul hC hc (mul_nonneg (Real.exp_pos _).le hP) (by norm_num only)
  have hrep := mul_le_mul phase_recip_upper117 hrec (Real.exp_pos _).le (by norm_num only)
  linarith only [hplus, hcost, hrep]

/-- The sum of the main Euler recovery, the complete shifted conductor, and
the reciprocal pole is nondecreasing on the section 117 logarithmic window. -/
theorem phase_main_core_mono117 :
    MonotoneOn
      (fun x : ℝ ↦
        -4 * threeShiftEulerMain (Real.exp x) +
          ((51 / 50 : ℝ) ^ 5 / 30) *
            (3.143 * phaseConductorMonomial117 0 x -
              3.124 * Real.exp ((51 / 50) * (1 / 50)) * phaseConductorMonomial117 (1 / 50) x -
              0.0374 * Real.exp ((51 / 50) * (11 / 10)) * phaseConductorMonomial117 (11 / 10) x) +
          phaseRecip117 * Real.exp (-x / 2))
      (Set.Icc 11.48 12) := by
  intro x hx y hy hxy
  have h₁ := phase_main_conductor_mono117 hx hy hxy
  have h₂ := phase_near_conductor_mono117 hx.1 hy.1 hxy
  have h₃ := phase_far_conductor_antitone117 hx.1 hy.1 hxy
  have hg :=
    mul_le_mul_of_nonneg_left h₃
      (show 0 ≤ (51 / 50 : ℝ) ^ 5 / 30 * 0.0374 * Real.exp ((51 / 50) * (11 / 10)) by positivity)
  linear_combination h₁ + ((51 / 50 : ℝ) ^ 5 / 30 * 3.143) * h₂ + hg

/-- The integrated RH slope envelope decreases as the logarithmic cutoff
increases. Its difference is the integral of a nonnegative function. -/
theorem phase_euler_error_antitone117 :
    AntitoneOn (fun x : ℝ ↦ threeShiftEulerError (Real.exp x)) (Set.Ici 11.48) := by
  intro x hx y hy hxy
  have he := Real.exp_le_exp.mpr hxy
  have ha : 1 ≤ Real.exp x := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith only [Set.mem_Ici.mp hx])
  have h := three_shift_error_interval ha he
  have hi :
    0 ≤
      ∫ t : ℝ in Real.exp x..Real.exp y,
        Real.sqrt t * (Real.log t ^ 2 / 24) * -deriv threeShiftEulerDensity t := by
    apply intervalIntegral.integral_nonneg he
    intro t ht
    have hp := (Real.exp_pos x).trans_le ht.1
    have hl := Real.log_le_log (Real.exp_pos x) ht.1
    rw [Real.log_exp] at hl
    exact
      mul_nonneg (by positivity)
        (neg_nonneg.mpr
          (three_shift_density_deriv_neg hp (by linarith only [hl, Set.mem_Ici.mp hx])).le)
  linarith only [h, hi]

/-- The radius-dependent forward part of the §117 remainder, expressed at
logarithmic cutoff x. -/
noncomputable def threeShiftForward117 (x : ℝ) : ℝ :=
  -4 * threeShiftEulerMain (Real.exp x) +
      ((51 / 50 : ℝ) ^ 5 / 30) *
        (3.143 * phaseConductorMonomial117 0 x -
          3.124 * Real.exp ((51 / 50) * (1 / 50)) * phaseConductorMonomial117 (1 / 50) x -
          0.0374 * Real.exp ((51 / 50) * (11 / 10)) * phaseConductorMonomial117 (11 / 10) x) +
      phaseRecip117 * Real.exp (-x / 2) -
    4 *
      (Real.sqrt (Real.exp x) * (Real.log (Real.exp x) ^ 2 / 24) *
          threeShiftEulerDensity (Real.exp x) +
        threeShiftEulerError (Real.exp x))

/-- The complete forward contribution is nondecreasing on the section 117 window. -/
theorem phase_forward_mono117 : MonotoneOn threeShiftForward117 (Set.Icc 11.48 12) := by
  intro x hx y hy hxy
  have hmain := phase_main_core_mono117 hx hy hxy
  have herror := phase_euler_error_antitone117 hx.1 hy.1 hxy
  have hx' : x ∈ Set.Ici (10 : ℝ) := (by norm_num only : (10 : ℝ) ≤ 11.48).trans hx.1
  have hy' : y ∈ Set.Ici (10 : ℝ) := (by norm_num only : (10 : ℝ) ≤ 11.48).trans hy.1
  have hboundary := three_shift_boundary_antitone hx' hy' hxy
  unfold threeShiftForward117
  linarith only [hmain, herror, hboundary]

/-- The constant part of the phase remainder consists of the symmetric poles
at all seven frequencies and the common zeta cost. -/
noncomputable def threeShiftPhasePole117 : ℝ :=
  let B := fun s : ℝ ↦ -6 * ((51 / 50 : ℝ) ^ 5 / ((51 / 50) ^ 2 - 1 / 4) ^ 3) * Real.cosh (s / 2)
  3.143 * B (14 / 5) + (-3.124) * B (141 / 50) + (-0.0374) * B (39 / 10) +
      (-((3.143 ^ 2 + 3.124 ^ 2 + 0.0374 ^ 2) / 2)) * B 0 +
      (3.143 * 3.124) * B (1 / 50) +
      (3.143 * 0.0374) * B (11 / 10) +
      (-(3.124 * 0.0374)) * B (27 / 25) -
    0.00003249

/-- At positive radius the phase remainder is its constant and forward parts
less the two terms that bound the reflected Euler costs. -/
theorem three_shift_remainder_forward_eq {r : ℝ} (hr : 0 < r) :
    threeShiftRemainder117 r =
      threeShiftPhasePole117 + threeShiftForward117 (2 * Real.log r) -
        4 * (3.124 - 3.143 * Real.exp (-(51 / 50) * (1 / 50))) *
          threeShiftReflectedCap (r ^ 2) (1 / 50) -
        4 * 0.0374 * threeShiftReflectedCap (r ^ 2) (11 / 10) := by
  have he : Real.exp (2 * Real.log r) = r ^ 2 := by rw [two_mul, Real.exp_add, Real.exp_log hr, sq]
  have hi : Real.exp (-(2 * Real.log r) / 2) = r⁻¹ := by
    rw [show -(2 * Real.log r) / 2 = -Real.log r by ring, Real.exp_neg, Real.exp_log hr]
  unfold threeShiftRemainder117 threeShiftPhasePole117 threeShiftForward117
  dsimp only
  rw [he, hi]
  unfold phaseConductorMonomial117 phaseRecip117
  ring

private theorem section117_log_mem {r : ℝ} (hr : r ∈ Set.Icc 314 316) :
    2 * Real.log r ∈ Set.Icc 11.48 12 := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 314) (j := 8) (n := 24) (lo := 574 / 100) (hi :=
        6) (by decide +kernel)).1
  have hu :=
    (Analysis.rationalLogIntervalCheck_sound (N := 316) (j := 8) (n := 24) (lo := 5) (hi := 6)
        (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hl hu
  exact
    ⟨by linarith only [hl, Real.log_le_log (by norm_num only) hr.1], by
      linarith only [hu, Real.log_le_log (show 0 < r by linarith only [hr.1]) hr.2]⟩

/-- The full section 117 phase remainder is nondecreasing on radii 314 to 316. -/
theorem section117_remainder_mono : MonotoneOn threeShiftRemainder117 (Set.Icc 314 316) := by
  intro r hr s hs hrs
  have hr0 : 0 < r := by linarith only [hr.1]
  have hs0 : 0 < s := by linarith only [hs.1]
  have hx := section117_log_mem hr
  have hy := section117_log_mem hs
  have hxy := mul_le_mul_of_nonneg_left (Real.log_le_log hr0 hrs) (by norm_num only : (0 : ℝ) ≤ 2)
  have hforward := phase_forward_mono117 hx hy hxy
  have hx' : 2 * Real.log r ∈ Set.Ici (11 : ℝ) := (by norm_num only : (11 : ℝ) ≤ 11.48).trans hx.1
  have hy' : 2 * Real.log s ∈ Set.Ici (11 : ℝ) := (by norm_num only : (11 : ℝ) ≤ 11.48).trans hy.1
  have he (t : ℝ) (ht : 0 < t) : Real.exp (2 * Real.log t) = t ^ 2 := by
    rw [two_mul, Real.exp_add, Real.exp_log ht, sq]
  have hnear := ref_cap_antitone117 (Or.inl rfl : (1 / 50 : ℝ) = 1 / 50 ∨ _) hx' hy' hxy
  have hfar := ref_cap_antitone117 (Or.inr rfl : (11 / 10 : ℝ) = 1 / 50 ∨ _) hx' hy' hxy
  dsimp only at hnear hfar
  rw [he r hr0, he s hs0] at hnear hfar
  have ht := Real.add_one_le_exp ((51 / 50 : ℝ) * (1 / 50))
  have hu : Real.exp (-(51 / 50 : ℝ) * (1 / 50)) ≤ (1.0204 : ℝ)⁻¹ := by
    rw [neg_mul, Real.exp_neg]
    exact (inv_le_inv₀ (Real.exp_pos _) (by norm_num only)).2 (by linarith only [ht])
  have hv : (0 : ℝ) ≤ 4 * (3.124 - 3.143 * Real.exp (-(51 / 50) * (1 / 50))) := by
    linarith only [hu]
  rw [three_shift_remainder_forward_eq hr0, three_shift_remainder_forward_eq hs0]
  linarith only [hforward, mul_le_mul_of_nonneg_left hnear hv, hfar]

private theorem phase_pole_cosh_box {x l u : ℝ} (hx : 0 ≤ x) (hs : x / 25 ≤ 1 / 2)
    (hl : l ≤ ∑ k ∈ Finset.range 24, x ^ k / (k.factorial : ℝ))
    (hu :
      (∑ k ∈ Finset.range 24, x ^ k / (k.factorial : ℝ)) + (x ^ 24 / ((24 : ℕ).factorial : ℝ)) * 2 ≤
        u)
    (hp : 0 < l) : (l + 1 / u) / 2 ≤ Real.cosh x ∧ Real.cosh x ≤ (u + 1 / l) / 2 := by
  have h₁ := hl.trans (Real.sum_le_exp_of_nonneg hx 24)
  have h₂ := (Analysis.exp_le_taylor_add_two_next (x := x) (n := 24) hx hs).trans hu
  have h₃ := one_div_le_one_div_of_le (Real.exp_pos x) h₂
  have h₄ := one_div_le_one_div_of_le hp h₁
  rw [Real.cosh_eq, Real.exp_neg, ← one_div]
  constructor <;> linarith only [h₁, h₂, h₃, h₄]

/-- The constant pole contribution after the common zeta cost exceeds 2.03856241. -/
theorem phase_pole_lower117 : 2.03856241 < threeShiftPhasePole117 := by
  have h0 :=
    phase_pole_cosh_box (x := 7 / 5) (l := 4055199966843 / 10 ^ 12) (u := 4055199966846 / 10 ^ 12)
      (by norm_num only) (by norm_num only)
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
      (by norm_num only)
  have h1 :=
    phase_pole_cosh_box (x := 141 / 100) (l := 4095955404070 / 10 ^ 12) (u :=
      4095955404073 / 10 ^ 12) (by norm_num only) (by norm_num only)
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
      (by norm_num only)
  have h2 :=
    phase_pole_cosh_box (x := 39 / 20) (l := 7028687580588 / 10 ^ 12) (u := 7028687580591 / 10 ^ 12)
      (by norm_num only) (by norm_num only)
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
      (by norm_num only)
  have h3 :=
    phase_pole_cosh_box (x := 1 / 100) (l := 1010050167083 / 10 ^ 12) (u := 1010050167086 / 10 ^ 12)
      (by norm_num only) (by norm_num only)
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
      (by norm_num only)
  have h4 :=
    phase_pole_cosh_box (x := 11 / 20) (l := 1733253017866 / 10 ^ 12) (u := 1733253017869 / 10 ^ 12)
      (by norm_num only) (by norm_num only)
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
      (by norm_num only)
  have h5 :=
    phase_pole_cosh_box (x := 27 / 50) (l := 1716006862183 / 10 ^ 12) (u := 1716006862186 / 10 ^ 12)
      (by norm_num only) (by norm_num only)
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
      (by norm_num only)
  unfold threeShiftPhasePole117
  norm_num only [zero_div, Real.cosh_zero]
  linarith only [h0.2, h1.1, h2.1, h3.2, h4.2, h5.1]

/-- The reciprocal pole has coefficient at least 12.93701296.
Lower Taylor polynomials suffice because both exponential coefficients are positive. -/
theorem phase_recip_lower117 : 12.93701296 ≤ phaseRecip117 := by
  have ha := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 1 / 100 by norm_num only) 16
  have hb := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 11 / 20 by norm_num only) 16
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_one, Nat.cast_zero] at ha hb
  unfold phaseRecip117
  linarith only [ha, hb]

/-- At log cutoff twice the logarithm of a positive radius, the reciprocal pole
contributes at least its certified coefficient divided by the radius. -/
theorem phase_recip_at_radius117 {r : ℝ} (hr : 0 < r) :
    12.93701296 / r ≤ phaseRecip117 * Real.exp (-(2 * Real.log r) / 2) := by
  rw [show -(2 * Real.log r) / 2 = -Real.log r by ring, Real.exp_neg, Real.exp_log hr, ←
    div_eq_mul_inv]
  exact div_le_div_of_nonneg_right phase_recip_lower117 hr.le

end PseudoPrime.PrimeTestBounds.MillerRabin
