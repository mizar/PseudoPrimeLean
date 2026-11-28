/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalPhase
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterDensity570
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalPhase
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipal600
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAbel570
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEndpoint570
import PseudoPrime.Analysis.LogTaylorBounds
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.TrivialZeroIntegralBound
import PseudoPrime.LLS.RiemannExplicitFormula

/-! # Trivial-zero estimate for the section 99 principal term -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- On positive inputs the exponential prefactor divided by the input is
its endpoint value times the power with exponent minus twelve twenty-fifths. -/
private theorem section99_factor_div {X t : ℝ} (hx : 0 < X) (ht : 0 < t) :
    quarterFactor570 X t / t = quarterFactor570 X 1 * t ^ (-(12 / 25 : ℝ)) := by
  unfold quarterFactor570 quarterCoord570
  rw [Real.sqrt_one, one_div_one, one_mul, Real.log_div ht.ne' hx.ne',
    show (1 / X : ℝ) = X⁻¹ from one_div X, Real.log_inv, sub_neg_eq_add, Real.sqrt_eq_rpow,
    Real.rpow_def_of_pos ht, Real.rpow_def_of_pos ht]
  have he :
    -((2 * (7 / 5) - (Real.log t - Real.log X)) / (2 * (25 / 51))) =
      -((2 * (7 / 5) + Real.log X) / (2 * (25 / 51))) + Real.log t * (1 / 2) + Real.log t +
        Real.log t * -(12 / 25) := by
    ring
  rw [he, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log ht]
  field_simp [ht.ne', Real.exp_ne_zero]

/-- On the inner support the second Abel density is at most 0.28 times
the physical weight at one. The shifted coordinate controls the sign
of the lower-degree terms. -/
theorem section99_inner_density_upper {X t : ℝ} (hx : 1 ≤ X) (hb : 14 ≤ quarterCoord570 X 1)
    (ht : 1 ≤ t) (hcut : t ≤ X) :
    deriv (fun u ↦ u * deriv (quarterWeight570 X) u) t ≤ 0.28 * quarterWeight570 X 1 := by
  let v := quarterCoord570 X t
  let b := quarterCoord570 X 1
  let F := quarterFactor570 X 1
  have hx0 := zero_lt_one.trans_le hx
  have ht0 := zero_lt_one.trans_le ht
  have hv0 : 0 ≤ v := by
    have hlog := Real.log_nonpos (div_nonneg ht0.le hx0.le) ((div_le_one hx0).2 hcut)
    dsimp only [v, quarterCoord570]
    norm_num only
    linarith only [hlog]
  have hvb : v ≤ b := by
    have hlog := Real.log_le_log (one_div_pos.mpr hx0) (div_le_div_of_nonneg_right ht hx0.le)
    dsimp only [v, b, quarterCoord570]
    norm_num only
    linarith only [hlog]
  have hb0 := hv0.trans hvb
  have hv5 := pow_le_pow_left₀ hv0 hvb 5
  have hpoly :
    v ^ 3 * ((13 / 25) ^ 2 * v ^ 2 - 10 * (51 / 50) * (13 / 25) * v + 20 * (51 / 50) ^ 2) ≤
      0.28 * b ^ 5 := by
    have h := pow_nonneg hv0 3
    rcases le_or_gt v 4 with hv | hv
    · have hv3 := pow_le_pow_left₀ hv0 hv 3
      have hb5 := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 14) hb 5
      nlinarith only [hv5, hv3, hb5, mul_nonneg h hv0]
    · have hn : -10 * (51 / 50 : ℝ) * (13 / 25) * v + 20 * (51 / 50) ^ 2 ≤ 0 := by
        linarith only [hv]
      nlinarith only [hv5, pow_nonneg hb0 5, mul_nonpos_of_nonneg_of_nonpos h hn]
  have hp : t ^ (-(12 / 25 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht (by norm_num only)
  have hF : 0 ≤ F := by
    dsimp only [F, quarterFactor570]; positivity
  have hw : quarterWeight570 X 1 = F * b ^ 5 := by
    unfold F b quarterWeight570 quarterFactor570 quarterCoord570
    ring
  rw [quarter_second_density_570 hx0 ht0, section99_factor_div hx0 ht0, hw]
  change F * t ^ (-(12 / 25 : ℝ)) * v ^ 3 * _ ≤ _
  rw [mul_assoc (F * _)]
  calc
    _ ≤ (F * t ^ (-(12 / 25 : ℝ))) * (0.28 * b ^ 5) :=
      mul_le_mul_of_nonneg_left hpoly (mul_nonneg hF (Real.rpow_nonneg ht0.le _))
    _ ≤ _ := by
      have h :=
        mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hF hp)
          (show 0 ≤ 0.28 * b ^ 5 by positivity)
      linarith only [h]

/-- The logarithmic trivial-zero series is nonnegative and bounded by
five twelfths of the inverse square on the closed physical support. -/
private theorem section99_trivial_envelope {t : ℝ} (ht : 1 ≤ t) :
    let T := AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries t
    0 ≤ T ∧ T ≤ (5 / 12 : ℝ) * t⁻¹ ^ 2 := by
  intro T
  have hπ : Real.pi ^ 2 / 24 ≤ (5 / 12 : ℝ) := by
    nlinarith only [sq_nonneg Real.pi, Real.pi_lt_d4, Real.pi_pos,
      mul_nonneg (sub_nonneg.mpr Real.pi_lt_d4.le)
        (add_nonneg Real.pi_pos.le (by norm_num only : (0 : ℝ) ≤ 3.1416))]
  rcases ht.eq_or_lt with he | hlt
  · subst t
    have hT : T = Real.pi ^ 2 / 24 := by
      dsimp only [T, AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries]
      simp only [inv_one, one_pow,
        show
            (fun k : ℕ ↦ (1 : ℝ) / (4 * ((k : ℝ) + 1) ^ 2)) =
              (fun k : ℕ ↦ (1 / 4 : ℝ) * (1 / ((k : ℝ) + 1) ^ 2))
            by
            funext k
            simp only [one_div, mul_inv_rev, mul_comm],
        tsum_mul_left, LLS.tsum_shifted_basel_eq]
      ring
    rw [hT, inv_one, one_pow, mul_one]
    exact ⟨by positivity, hπ⟩
  · exact
      ⟨AnalyticNumberTheory.RiemannZeta.triv_nonneg hlt,
        (AnalyticNumberTheory.RiemannZeta.triv_decay hlt).trans
          ((mul_le_mul_of_nonneg_left hπ (sq_nonneg _)).trans_eq (mul_comm _ _))⟩

/-- At the section 99 radii the shifted coordinate at one lies between
fourteen and fifteen. The rational logarithm checks certify both endpoints. -/
private theorem section99_coord_one {r : ℝ} (hl : 292 ≤ r) (hu : r ≤ 300) :
    14 ≤ quarterCoord570 (r ^ 2) 1 ∧ quarterCoord570 (r ^ 2) 1 ≤ 15 := by
  have hr : 0 < r := by linarith only [hl]
  have hlo :=
    (Analysis.rationalLogIntervalCheck_sound (N := 292) (j := 8) (n := 20) (lo := 227 / 40) (hi :=
        6) (by decide +kernel)).1
  have hhi :=
    (Analysis.rationalLogIntervalCheck_sound (N := 300) (j := 8) (n := 20) (lo := 5) (hi := 29 / 5)
        (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlo hhi
  unfold quarterCoord570
  rw [one_div, Real.log_inv, sub_neg_eq_add, Real.log_pow, Nat.cast_ofNat]
  norm_num only
  constructor
  · linarith only [hlo, Real.log_le_log (by norm_num only) hl]
  · linarith only [hhi, Real.log_le_log hr hu]

/-- The logarithmic derivative at one costs at most one fifth of the
endpoint weight when the shifted coordinate lies between fourteen and fifteen. -/
private theorem section99_deriv_one_le {X : ℝ} (hx : 0 < X) (hb : 14 ≤ quarterCoord570 X 1)
    (hu : quarterCoord570 X 1 ≤ 15) :
    deriv (quarterWeight570 X) 1 ≤ (1 / 5) * quarterWeight570 X 1 := by
  let v := quarterCoord570 X 1
  let F := quarterFactor570 X 1
  have hv : 0 ≤ v := by linarith only [hb]
  have hF : 0 ≤ F := by
    dsimp only [F, quarterFactor570]; positivity
  have h := quarter_log_deriv_570 hx (zero_lt_one : (0 : ℝ) < 1)
  rw [one_mul] at h
  have hw : quarterWeight570 X 1 = F * v ^ 5 := by
    unfold F v quarterWeight570 quarterFactor570 quarterCoord570
    ring
  rw [h, hw]
  have hp : (13 / 25) * v ^ 5 - 5 * (51 / 50) * v ^ 4 ≤ (1 / 5) * v ^ 5 := by
    have he := mul_le_mul_of_nonneg_right hu (pow_nonneg hv 4)
    dsimp only [v]
    nlinarith only [he, pow_nonneg hv 4]
  linarith only [mul_le_mul_of_nonneg_left hp hF]

/-- The inverse-square majorant has integral at most one on the inner support. -/
private theorem section99_inv_sq_integral {X : ℝ} (hX : 1 ≤ X) :
    (∫ t in (1 : ℝ)..X, t⁻¹ ^ 2) ≤ 1 := by
  have hp (t : ℝ) (ht : t ∈ Set.uIcc (1 : ℝ) X) : 0 < t := by
    rw [Set.uIcc_of_le hX] at ht
    exact zero_lt_one.trans_le ht.1
  have hc : ContinuousOn (fun t : ℝ ↦ t⁻¹ ^ 2) (Set.uIcc 1 X) := fun t ht ↦
    ((continuousAt_id.inv₀ (hp t ht).ne').pow 2).continuousWithinAt
  have hi := hc.intervalIntegrable (μ := MeasureTheory.volume)
  have hd (t : ℝ) (ht : t ∈ Set.uIcc (1 : ℝ) X) : HasDerivAt (fun x : ℝ ↦ -x⁻¹) (t⁻¹ ^ 2) t := by
    convert (hasDerivAt_inv (hp t ht).ne').neg using 1
    simp only [neg_neg, ← inv_pow]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi, inv_one]
  linarith only [inv_nonneg.mpr (zero_le_one.trans hX)]

/-- Using its explicit value at the arithmetic cutoff, the weight there
is nonnegative and at most two whenever the cutoff is at least one. -/
private theorem section99_cutoff_weight_bound {X : ℝ} (hX : 1 ≤ X) :
    0 ≤ quarterWeight570 X X ∧ quarterWeight570 X X ≤ 2 := by
  have hx := zero_lt_one.trans_le hX
  have hs : 1 ≤ Real.sqrt X := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hX
  have hsi := inv_le_one_of_one_le₀ hs
  have he := Real.exp_le_one_iff.mpr (by norm_num only : -(357 / 125 : ℝ) ≤ 0)
  have hf : (357 / 125 : ℝ) ^ 5 * Real.exp (-(357 / 125)) / 120 ≤ 2 := by
    have h := mul_le_mul_of_nonneg_left he (by norm_num only : (0 : ℝ) ≤ (357 / 125) ^ 5)
    linarith only [h]
  have hp : 0 ≤ (357 / 125 : ℝ) ^ 5 * Real.exp (-(357 / 125)) / 120 := by positivity
  unfold quarterWeight570
  rw [div_self hx.ne', Real.log_one, sub_zero]
  dsimp only
  rw [show (2 * (7 / 5) / (2 * (25 / 51)) : ℝ) = 357 / 125 by norm_num only]
  change
    0 ≤ (1 / Real.sqrt X) * ((357 / 125) ^ 5 * Real.exp (-(357 / 125)) / 120) ∧
      (1 / Real.sqrt X) * ((357 / 125) ^ 5 * Real.exp (-(357 / 125)) / 120) ≤ 2
  rw [one_div]
  exact
    ⟨mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg X)) hp, (mul_le_of_le_one_left hp hsi).trans hf⟩

/-- Bound the trivial-zero Abel action in terms of the actual weight at one. -/
theorem quarter_trivial_upper_weight {r : ℝ} (hl : 292 ≤ r) (hb : 14 ≤ quarterCoord570 (r ^ 2) 1)
    (hbu : quarterCoord570 (r ^ 2) 1 ≤ 15) :
    section99AbelAction (r ^ 2) AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries ≤
      (3 / 5) * quarterWeight570 (r ^ 2) 1 + 0.000012 := by
  let X := r ^ 2
  let B := X * Real.exp (14 / 5)
  let W := quarterWeight570 X
  let P := fun t ↦ t * deriv W t
  let T := AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries
  have hx1000 : 1000 ≤ X := by
    dsimp only [X]; nlinarith only [hl, sq_nonneg (r - 292)]
  have hx1 : 1 ≤ X := (by norm_num only : (1 : ℝ) ≤ 1000).trans hx1000
  have hx := zero_lt_one.trans_le hx1
  have hXB : X ≤ B := le_mul_of_one_le_right hx.le (Real.one_le_exp (by norm_num only))
  have hQ : ContinuousOn (deriv P) (Set.Icc 1 B) :=
    (((quarter_weight_smooth hx).2.continuousOn_deriv_of_isOpen isOpen_Ioi (by decide)).mono
      (fun _ ht ↦ zero_lt_one.trans_le ht.1))
  have hT : ContinuousOn T (Set.Icc 1 B) :=
    AnalyticNumberTheory.RiemannZeta.trivial_cont_closed le_rfl
  have hI := hT.mul hQ
  have hI₁ :=
    (hI.mono (Set.Icc_subset_Icc_right hXB)).intervalIntegrable_of_Icc (μ := MeasureTheory.volume)
      hx1
  have hI₂ :=
    (hI.mono (Set.Icc_subset_Icc_left hx1)).intervalIntegrable_of_Icc (μ := MeasureTheory.volume)
      hXB
  have hw : 0 ≤ W 1 := by
    change 0 ≤ quarterWeight570 X 1
    rw [section99_weight_one_power hx]
    have hlog := Real.log_nonneg hx1
    positivity
  have hD (t : ℝ) (ht : 1 ≤ t) : 0 ≤ T t ∧ T t ≤ (5 / 12 : ℝ) * t⁻¹ ^ 2 :=
    section99_trivial_envelope ht
  have hmajor : ContinuousOn (fun t : ℝ ↦ (0.28 * W 1 * (5 / 12)) * t⁻¹ ^ 2) (Set.Icc 1 X) := by
    intro t ht
    exact
      (continuousAt_const.mul
          ((continuousAt_id.inv₀ (zero_lt_one.trans_le ht.1).ne').pow 2)).continuousWithinAt
  have hi :=
    intervalIntegral.integral_mono_on hx1 hI₁ (hmajor.intervalIntegrable_of_Icc hx1)
      (fun t ht ↦ by
        have h₁ :=
          mul_le_mul_of_nonneg_left (section99_inner_density_upper hx1 hb ht.1 ht.2) (hD t ht.1).1
        have h₂ := mul_le_mul_of_nonneg_right (hD t ht.1).2 (show 0 ≤ 0.28 * W 1 by positivity)
        change T t * deriv P t ≤ _
        change T t * deriv P t ≤ T t * (0.28 * W 1) at h₁
        linarith only [h₁, h₂])
  rw [intervalIntegral.integral_const_mul] at hi
  have hin := hi.trans (mul_le_of_le_one_right (by positivity) (section99_inv_sq_integral hx1))
  have hout : 0 ≤ ∫ t in X..B, T t * deriv P t := by
    apply intervalIntegral.integral_nonneg hXB
    intro t ht
    exact mul_nonneg (hD t (hx1.trans ht.1)).1 (quarter_outer_density_nonneg hx ht.1 ht.2)
  have h₁ : P 1 * T 1 ≤ (1 / 5) * W 1 * (5 / 12) := by
    have h := mul_le_mul_of_nonneg_right (section99_deriv_one_le hx hb hbu) (hD 1 le_rfl).1
    have hj := (hD 1 le_rfl).2
    rw [inv_one, one_pow, mul_one] at hj
    exact
      (by simpa only [P, one_mul] using h : P 1 * T 1 ≤ (1 / 5) * W 1 * T 1).trans
        (mul_le_mul_of_nonneg_left hj (by positivity))
  have hTX : T X ≤ (1 / 1000000 : ℝ) := by
    have h := (inv_le_inv₀ hx (by norm_num only : (0 : ℝ) < 1000)).2 hx1000
    have hh := pow_le_pow_left₀ (inv_nonneg.mpr hx.le) h 2
    linarith only [(hD X hx1).2, hh]
  have hpX : -P X * T X ≤ 3 / 1000000 := by
    have hW₂ := section99_cutoff_weight_bound hx1
    dsimp only [P, W]
    rw [quarter_cutoff_deriv_570 hx]
    have hh := mul_le_mul hW₂.2 hTX (hD X hx1).1 (by norm_num only : (0 : ℝ) ≤ 2)
    linarith only [hh]
  change 0 ≤ ∫ t in X..B, (T * deriv P) t at hout
  change
    4 * (∫ t in (1 : ℝ)..X, (T * deriv P) t) - (∫ t in (1 : ℝ)..B, (T * deriv P) t) -
          4 * P X * T X +
        3 * P 1 * T 1 ≤
      _
  rw [← intervalIntegral.integral_add_adjacent_intervals hI₁ hI₂]
  change _ ≤ (3 / 5) * W 1 + 0.000012
  linarith only [hin, hout, h₁, hpX]

/-- The trivial-zero contribution to the physical Abel action is at
most 0.002 on the full section 99 radius interval. -/
theorem quarter_trivial_upper_coord {r : ℝ} (hl : 292 ≤ r) (hb : 14 ≤ quarterCoord570 (r ^ 2) 1)
    (hbu : quarterCoord570 (r ^ 2) 1 ≤ 15) :
    section99AbelAction (r ^ 2) AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries ≤
      0.002 := by
  have h := quarter_trivial_upper_weight hl hb hbu
  linarith only [h, section99_weight_one_le hl]

/-- The section 99 radius window satisfies the coordinate conditions for
the trivial-zero contribution to the centered Abel action. -/
theorem section99_trivial_upper {r : ℝ} (hl : 292 ≤ r) (hu : r ≤ 300) :
    section99AbelAction (r ^ 2) AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries ≤
      0.002 := by
  obtain ⟨hb, hbu⟩ := section99_coord_one hl hu
  exact quarter_trivial_upper_coord hl hb hbu

/-- On the section 99 radius interval RH gives the required lower bound
for the principal error, including both types of zeros and the endpoint. -/
theorem section99_principal_error_lower (hRH : RiemannHypothesis) {r : ℝ} (hl : 292 ≤ r)
    (hu : r ≤ 300) : -0.0273 ≤ section99PrincipalError r := by
  apply section99_error_of_abel hl
  have hx : 1 ≤ r ^ 2 := one_le_pow₀ (by linarith only [hl]) (n := 2)
  rw [section99_abel_zero_split hx]
  linarith only [section99_nontrivial_lower hRH hl, section99_trivial_upper hl hu]

/-- Under RH the section 99 principal prime-power comparison holds on
the full radius interval. Insert the proved error bound into the exact
principal comparison with its two cutoff corrections. -/
theorem section99_principal_lower_RH (hRH : RiemannHypothesis) {r : ℝ} (hl : 292 ≤ r)
    (hu : r ≤ 300) :
    let X := r ^ 2
    let S := fun n : ℕ ↦ (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) X n).re
    0.717289 * r - 0.29136 - 0.0273 + (if r ≤ 299 then 0.002237 else 0.002229) -
        3 * Real.log (2 * Real.pi) * quarterWeight570 X 1 <
      4 * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, S n) - (∑' n : ℕ, S n) := by
  exact section99_principal_budget hl hu (section99_principal_error_lower hRH hl hu)

end PseudoPrime.PrimeTestBounds.MillerRabin
