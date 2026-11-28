/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMain570
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAbel570
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.IntegratedLogSplit
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAbel570
import PseudoPrime.LLS.RiemannWeightedErrorBounds
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt1423toMillion
import PseudoPrime.Analysis.NumericalLogBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Principal cutoff comparison for section 99 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The principal cutoff boundary retains the positive logarithmic constant
after applying the finite four-fifths Chebyshev bound on the section 99 interval. -/
theorem section99_principal_boundary {r : ℝ} (hl : 292 ≤ r) (hu : r ≤ 300) :
    -0.29136 + (if r ≤ 299 then 0.002237 else 0.002229) ≤
      4 * quarterWeight570 (r ^ 2) (r ^ 2) *
        (Chebyshev.psi (r ^ 2) - r ^ 2 + Real.log (2 * Real.pi)) := by
  have hr : 0 < r := by linarith only [hl]
  have hx : 1423 ≤ r ^ 2 := by nlinarith only [hl, sq_nonneg (r - 292)]
  have hx' : r ^ 2 ≤ 1000000 := (pow_le_pow_left₀ hr.le hu 2).trans (by norm_num only)
  have hψ := (abs_le.mp (AnalyticNumberTheory.Arithmetic.psi_four_fifths_1423_million hx hx')).1
  rw [Real.sqrt_sq hr.le] at hψ
  let w := (quarterKernel570.transform 1).re
  have hw : (0.09104 : ℝ) ≤ w := by linarith only [quarter_unit_weight_570.1]
  have hw' : w ≤ (0.09105 : ℝ) := by linarith only [quarter_unit_weight_570.2]
  have hw₀ : 0 ≤ w := le_trans (by norm_num only) hw
  have he := mul_le_mul_of_nonneg_left hψ hw₀
  have hm := mul_le_mul_of_nonneg_right hw' (show 0 ≤ (4 / 5 : ℝ) * r by positivity)
  have hlog : (1.837 : ℝ) ≤ Real.log (2 * Real.pi) := by linarith only [Analysis.log_two_mul_pi_gt]
  have hp := mul_le_mul hw hlog (by norm_num only) hw₀
  rw [quarter_cutoff_weight_570 (sq_pos_of_pos hr), Real.sqrt_sq hr.le]
  change _ ≤ 4 * (w / r) * _
  rw [show
      4 * (w / r) * (Chebyshev.psi (r ^ 2) - r ^ 2 + Real.log (2 * Real.pi)) =
        (4 * w * (Chebyshev.psi (r ^ 2) - r ^ 2 + Real.log (2 * Real.pi))) / r
      by ring]
  apply (le_div_iff₀ hr).2
  split_ifs with h
  · linarith only [he, hm, hp, h]
  · linarith only [he, hm, hp, hu]

/-- The missing principal integral costs less than 0.003 from radius 292 onward. -/
theorem quarter_missing_mass_lt_600 {r : ℝ} (hl : 292 ≤ r) :
    r * (∫ u in (0 : ℝ)..1 / r ^ 2, (quarterKernel570.transform u).re / Real.sqrt u) <
      3 / 1000 := by
  have hr : 0 < r := by linarith only [hl]
  have hx : (77284 : ℝ) ≤ r ^ 2 :=
    (by norm_num only : (77284 : ℝ) = 278 ^ 2) ▸
      pow_le_pow_left₀ (by norm_num only) ((by norm_num only : (278 : ℝ) ≤ 292).trans hl) 2
  have hm := quarter_missing_mass_570 hx
  rw [Real.sqrt_sq hr.le] at hm
  apply hm.trans_lt
  have h := reflected_weight_upper_of_288 ((by norm_num only : (288 : ℝ) ≤ 292).trans hl)
  have hx0 := sq_pos_of_pos hr
  have hlog := Real.log_nonneg (one_le_pow₀ (show 1 ≤ r by linarith only [hl]) (n := 2))
  have hw : quarterWeight570 (r ^ 2) 1 = (quarterKernel570.transform (1 / r ^ 2)).re := by
    rw [quarterKernel570, LLS.PaperStatements.rationalPole_transform _ _ _ _ (one_div_pos.mpr hx0),
      Complex.ofReal_re, Analysis.rationalPoleProfile,
      ite_eq_left
        ⟨one_div_pos.mpr hx0, by
          rw [one_div, Real.log_inv]; linarith only [hlog]⟩]
    norm_num only [quarterWeight570, Real.sqrt_one, div_one, Nat.reduceMul, Nat.reduceSub,
      Nat.factorial, Nat.cast_ofNat, one_mul]
  rw [hw]
  linarith only [h]

/-- Retain the lower cutoff integral exactly in the principal comparison. -/
private theorem integral_difference_exact {r : ℝ} (hl : 292 ≤ r) :
    let X := r ^ 2
    717289 / 1000000 * r -
        4 * r * (∫ u in (0 : ℝ)..1 / X, (quarterKernel570.transform u).re / Real.sqrt u) <
      4 * (∫ t in (1 : ℝ)..X, quarterWeight570 X t) -
        ∫ t in (1 : ℝ)..X * Real.exp (14 / 5), quarterWeight570 X t := by
  intro X
  have hr : 0 < r := by linarith only [hl]
  have hx : 1 ≤ X := by
    dsimp only [X]; nlinarith only [hl, sq_nonneg (r - 1)]
  have hx0 := zero_lt_one.trans_le hx
  have hb : X ≤ X * Real.exp (14 / 5) := by
    exact le_mul_of_one_le_right hx0.le (Real.one_le_exp (by norm_num only))
  let K := fun u ↦ (quarterKernel570.transform u).re / Real.sqrt u
  have hi {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : IntervalIntegrable K MeasureTheory.volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
      ((LLS.PaperStatements.MellinKernel.integrableOn_weight_Ioi quarterKernel570).mono_set
        (fun _ h ↦ ha.trans_lt h.1))
  have hq := (one_div_pos.mpr hx0).le
  have hsplit :=
    intervalIntegral.integral_add_adjacent_intervals (hi le_rfl hq)
      (hi hq ((div_le_one hx0).mpr hx))
  have hshort := quarter_scale_integral_570 hx0 zero_lt_one hx hb
  have hfull := quarter_integral_le_mass_570 hx0 zero_lt_one (hx.trans hb) le_rfl
  have hs : Real.sqrt X = r := Real.sqrt_sq hr.le
  rw [hs, div_self hx0.ne'] at hshort
  rw [hs] at hfull
  have hd := mul_lt_mul_of_pos_right quarter_principal_delta_570 hr
  change _ = ∫ u in (0 : ℝ)..1, K u at hsplit
  change _ = r * ∫ u in 1 / X..1, K u at hshort
  change _ < (4 * (∫ u in (0 : ℝ)..1, K u) - _) * r at hd
  nlinarith only [hshort, hfull, hd, congrArg (fun z : ℝ ↦ r * z) hsplit]

/-- The principal integral difference exceeds 0.717289r minus 0.012 from radius 292 onward. -/
theorem quarter_integral_difference_600 {r : ℝ} (hl : 292 ≤ r) :
    let X := r ^ 2
    717289 / 1000000 * r - 12 / 1000 <
      4 * (∫ t in (1 : ℝ)..X, quarterWeight570 X t) -
        ∫ t in (1 : ℝ)..X * Real.exp (14 / 5), quarterWeight570 X t := by
  have hi := integral_difference_exact hl
  have hm := quarter_missing_mass_lt_600 hl
  dsimp only at hi ⊢
  linarith only [hi, hm]

/-- The supported integrals and certified cutoff boundary give the main
part of the section 99 principal lower bound. -/
theorem section99_integral_boundary {r : ℝ} (hl : 292 ≤ r) (hu : r ≤ 300) :
    let X := r ^ 2
    0.717289 * r - 0.012 - 0.29136 + (if r ≤ 299 then 0.002237 else 0.002229) <
      4 * (∫ t in (1 : ℝ)..X, quarterWeight570 X t) -
          (∫ t in (1 : ℝ)..X * Real.exp (14 / 5), quarterWeight570 X t) +
        4 * quarterWeight570 X X * (Chebyshev.psi X - X + Real.log (2 * Real.pi)) := by
  dsimp only
  have hi := quarter_integral_difference_600 hl
  dsimp only at hi
  linarith only [hi, section99_principal_boundary hl hu]

/-- The centered Abel remainder including the lower-end terms. The missing
integral from zero to one is accounted for separately by the main integral bound. -/
noncomputable def section99PrincipalRemainder (X : ℝ) : ℝ :=
  let W := quarterWeight570 X
  let P := fun t ↦ t * deriv W t
  let c := Real.log (2 * Real.pi)
  let E := fun t ↦ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t - (t - c * Real.log t)
  4 * (∫ t in (1 : ℝ)..X, E t * deriv P t) -
      (∫ t in (1 : ℝ)..X * Real.exp (14 / 5), E t * deriv P t) -
      4 * P X * E X -
      3 * P 1 +
    3 * (1 - c) * W 1

/-- The Abel identity and the certified boundary reduce the section 99
principal sum to its centered remainder on the physical support. -/
theorem section99_principal_of_remainder {r : ℝ} (hl : 292 ≤ r) (hu : r ≤ 300) :
    let X := r ^ 2
    let S := fun n : ℕ ↦ (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) X n).re
    0.717289 * r - 0.012 - 0.29136 + (if r ≤ 299 then 0.002237 else 0.002229) +
        section99PrincipalRemainder X <
      4 * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, S n) - (∑' n : ℕ, S n) := by
  dsimp only
  have hx : 1 ≤ r ^ 2 := by nlinarith only [hl, sq_nonneg (r - 292)]
  have h := quarter_centered_difference_570 hx
  have hg := section99_integral_boundary hl hu
  dsimp only at h hg
  unfold section99PrincipalRemainder
  linarith only [h, hg]

/-- The principal error at radius r includes the exact missing integral and
normalizes the lower boundary by the logarithmic term in the paper comparison. -/
noncomputable def section99PrincipalError (r : ℝ) : ℝ :=
  let X := r ^ 2
  section99PrincipalRemainder X + 3 * Real.log (2 * Real.pi) * quarterWeight570 X 1 -
    4 * r * (∫ u in (0 : ℝ)..1 / X, (quarterKernel570.transform u).re / Real.sqrt u)

/-- Given the centered principal error budget, the section 99 arithmetic
comparison has exactly the paper's boundary and conductor terms. -/
theorem section99_principal_budget {r : ℝ} (hl : 292 ≤ r) (hu : r ≤ 300)
    (hE : -0.0273 ≤ section99PrincipalError r) :
    let X := r ^ 2
    let S := fun n : ℕ ↦ (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) X n).re
    0.717289 * r - 0.29136 - 0.0273 + (if r ≤ 299 then 0.002237 else 0.002229) -
        3 * Real.log (2 * Real.pi) * quarterWeight570 X 1 <
      4 * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, S n) - (∑' n : ℕ, S n) := by
  dsimp only
  have hx : 1 ≤ r ^ 2 := by nlinarith only [hl, sq_nonneg (r - 292)]
  have h := quarter_centered_difference_570 hx
  have hi := integral_difference_exact hl
  dsimp only at h hi
  unfold section99PrincipalError section99PrincipalRemainder at hE
  linarith only [h, hi, hE, section99_principal_boundary hl hu]

/-- For radii at least 292, the principal comparison retains both the signed
Chebyshev boundary and the logarithmic boundary with the exact weight.
Only the centered principal error remains as an analytic input. -/
theorem quarter_principal_signed {r : ℝ} (hl : 292 ≤ r) {err : ℝ}
    (hE : err ≤ section99PrincipalError r) :
    let X := r ^ 2
    let S := fun n : ℕ ↦ (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) X n).re
    0.717289 * r + err + 4 * quarterWeight570 X X * (Chebyshev.psi X - X + Real.log (2 * Real.pi)) -
        3 * Real.log (2 * Real.pi) * quarterWeight570 X 1 <
      4 * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, S n) - (∑' n : ℕ, S n) := by
  dsimp only
  have hx : 1 ≤ r ^ 2 := by nlinarith only [hl, sq_nonneg (r - 1)]
  have h := quarter_centered_difference_570 hx
  have hi := integral_difference_exact hl
  dsimp only at h hi
  unfold section99PrincipalError section99PrincipalRemainder at hE
  linarith only [h, hi, hE]

/-- The centered Abel operator on the physical support with its lower boundary
term retained. It annihilates constants, permitting a centered zero expansion. -/
noncomputable def section99AbelAction (X : ℝ) (F : ℝ → ℝ) : ℝ :=
  let P := fun t ↦ t * deriv (quarterWeight570 X) t
  4 * (∫ t in (1 : ℝ)..X, F t * deriv P t) -
      (∫ t in (1 : ℝ)..X * Real.exp (14 / 5), F t * deriv P t) -
      4 * P X * F X +
    3 * P 1 * F 1

/-- An additive constant in the centered explicit formula cancels exactly. -/
theorem section99_abel_const {X : ℝ} (hX : 1 ≤ X) (c : ℝ) :
    section99AbelAction X (fun _ ↦ c) = 0 := by
  let B := X * Real.exp (14 / 5)
  let P := fun t ↦ t * deriv (quarterWeight570 X) t
  have hx := zero_lt_one.trans_le hX
  have hb : 1 ≤ B := hX.trans (le_mul_of_one_le_right hx.le (Real.one_le_exp (by norm_num only)))
  have hP : ContDiffOn ℝ 1 P (Set.Ioi 0) := (quarter_weight_smooth hx).2
  have hI {b : ℝ} (h : 1 ≤ b) : (∫ t in (1 : ℝ)..b, deriv P t) = P b - P 1 := by
    have hsub : Set.Icc (1 : ℝ) b ⊆ Set.Ioi 0 := fun _ ht ↦ zero_lt_one.trans_le ht.1
    apply intervalIntegral.integral_deriv_eq_sub
    · intro t ht
      have ht' := hsub ((Set.uIcc_of_le h) ▸ ht)
      exact ((hP.differentiableOn (by decide)) t ht').differentiableAt (isOpen_Ioi.mem_nhds ht')
    · apply (intervalIntegrable_iff_integrableOn_Icc_of_le h).2
      exact ((hP.continuousOn_deriv_of_isOpen isOpen_Ioi (by decide)).mono hsub).integrableOn_Icc
  have hB : P B = 0 := by
    dsimp only [P, B]
    rw [(quarter_support_jet_570 hx).2, mul_zero]
  change
    4 * (∫ t in (1 : ℝ)..X, c * deriv P t) - (∫ t in (1 : ℝ)..B, c * deriv P t) - 4 * P X * c +
        3 * P 1 * c =
      0
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hI hX, hI hb, hB]
  ring

/-- The centered Mangoldt remainder is the Abel action plus the explicit
weight at the lower endpoint. The input takes value minus one at that endpoint. -/
theorem section99_remainder_eq_action (X : ℝ) :
    section99PrincipalRemainder X =
      section99AbelAction X
          (fun t ↦
            AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t -
              (t - Real.log (2 * Real.pi) * Real.log t)) +
        3 * (1 - Real.log (2 * Real.pi)) * quarterWeight570 X 1 := by
  dsimp only [section99PrincipalRemainder, section99AbelAction]
  rw [LLS.logWeightedMangoldtSum_eq_zero_of_le_one (le_refl (1 : ℝ)), Real.log_one, mul_zero,
    sub_zero, zero_sub]
  ring

/-- The Abel action distributes over a sum when both weighted inputs are
integrable on the two support intervals. -/
theorem section99_abel_add {X : ℝ} (F G : ℝ → ℝ) :
    let P := fun t ↦ t * deriv (quarterWeight570 X) t
    let B := X * Real.exp (14 / 5)
    IntervalIntegrable (fun t ↦ F t * deriv P t) MeasureTheory.volume 1 X →
      IntervalIntegrable (fun t ↦ G t * deriv P t) MeasureTheory.volume 1 X →
      IntervalIntegrable (fun t ↦ F t * deriv P t) MeasureTheory.volume 1 B →
      IntervalIntegrable (fun t ↦ G t * deriv P t) MeasureTheory.volume 1 B →
      section99AbelAction X (fun t ↦ F t + G t) =
        section99AbelAction X F + section99AbelAction X G := by
  intro P B hF hG hF' hG'
  unfold section99AbelAction
  dsimp only [P, B] at hF hG hF' hG'
  simp only [add_mul, intervalIntegral.integral_add hF hG, intervalIntegral.integral_add hF' hG']
  ring

/-- After normalizing the lower boundary, the centered error consists of the
Abel action, the weight at one and the exact omitted support integral. -/
theorem section99_error_eq_action (r : ℝ) :
    let X := r ^ 2
    section99PrincipalError r =
      section99AbelAction X
            (fun t ↦
              AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t -
                (t - Real.log (2 * Real.pi) * Real.log t)) +
          3 * quarterWeight570 X 1 -
        4 * r * (∫ u in (0 : ℝ)..1 / X, (quarterKernel570.transform u).re / Real.sqrt u) := by
  dsimp only [section99PrincipalError]
  rw [section99_remainder_eq_action]
  ring

/-- For radii at least 292, the lower endpoint and the omitted support integral
together cost less than 0.002861 in the centered principal error. -/
theorem section99_endpoint_lower {r : ℝ} (hl : 292 ≤ r) :
    -(0.002861 : ℝ) <
      3 * quarterWeight570 (r ^ 2) 1 -
        4 * r * (∫ u in (0 : ℝ)..1 / r ^ 2, (quarterKernel570.transform u).re / Real.sqrt u) := by
  have hr : 0 < r := by linarith only [hl]
  have hx : (77284 : ℝ) ≤ r ^ 2 :=
    (by norm_num only : (77284 : ℝ) = 278 ^ 2) ▸
      pow_le_pow_left₀ (by norm_num only) ((by norm_num only : (278 : ℝ) ≤ 292).trans hl) 2
  have hm := quarter_missing_mass_570 hx
  rw [Real.sqrt_sq hr.le] at hm
  have h := reflected_weight_upper_of_288 ((by norm_num only : (288 : ℝ) ≤ 292).trans hl)
  have hx0 := sq_pos_of_pos hr
  have hlog := Real.log_nonneg (one_le_pow₀ (show 1 ≤ r by linarith only [hl]) (n := 2))
  have hw : quarterWeight570 (r ^ 2) 1 = (quarterKernel570.transform (1 / r ^ 2)).re := by
    rw [quarterKernel570, LLS.PaperStatements.rationalPole_transform _ _ _ _ (one_div_pos.mpr hx0),
      Complex.ofReal_re, Analysis.rationalPoleProfile,
      ite_eq_left
        ⟨one_div_pos.mpr hx0, by
          rw [one_div, Real.log_inv]; linarith only [hlog]⟩]
    norm_num only [quarterWeight570, Real.sqrt_one, div_one, Nat.reduceMul, Nat.reduceSub,
      Nat.factorial, Nat.cast_ofNat, one_mul]
  rw [← hw] at h
  linarith only [h, hm]

/-- A lower bound of minus 0.024439 for the centered Abel action suffices
for the section 99 principal error budget at radii at least 292. -/
theorem section99_error_of_abel {r : ℝ} (hl : 292 ≤ r)
    (h :
      -(0.024439 : ℝ) ≤
        section99AbelAction (r ^ 2)
          (fun t ↦
            AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t -
              (t - Real.log (2 * Real.pi) * Real.log t))) :
    -0.0273 ≤ section99PrincipalError r := by
  have he := section99_error_eq_action r
  dsimp only at he
  linarith only [he, h, section99_endpoint_lower hl]

/-- At and above one, the centered Mangoldt error is the real nontrivial-zero series
minus the trivial-zero series and the constant pole residue. This gives the
input for the section 99 Abel action on the interior of its support. -/
theorem section99_centered_zero_eq {t : ℝ} (ht : 1 ≤ t) :
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t -
        (t - Real.log (2 * Real.pi) * Real.log t) =
      (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re -
        AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries t -
        AnalyticNumberTheory.RiemannXi.qMinusOneRiemannZetaSecondLogDerivAtZero.re := by
  rcases ht.eq_or_lt with he | hlt
  · subst t
    rw [AnalyticNumberTheory.RiemannZeta.log_weighted_exact_one]
    ring
  · rw [AnalyticNumberTheory.RiemannZeta.log_weighted_exact hlt]
    ring

/-- The Abel action depends only on the input on its physical support. -/
theorem section99_abel_congr {X : ℝ} (hX : 1 ≤ X) {F G : ℝ → ℝ}
    (h : Set.EqOn F G (Set.Icc 1 (X * Real.exp (14 / 5)))) :
    section99AbelAction X F = section99AbelAction X G := by
  have hXB :=
    le_mul_of_one_le_right (zero_le_one.trans hX)
      (Real.one_le_exp (by norm_num only : (0 : ℝ) ≤ 14 / 5))
  have hB := hX.trans hXB
  dsimp only [section99AbelAction]
  rw [h ⟨hX, hXB⟩, h ⟨le_rfl, hB⟩]
  have inner :=
    intervalIntegral.integral_congr (μ := MeasureTheory.volume) (f := fun t ↦
      F t * deriv (fun u ↦ u * deriv (quarterWeight570 X) u) t) (g := fun t ↦
      G t * deriv (fun u ↦ u * deriv (quarterWeight570 X) u) t) (a := 1) (b := X)
      (fun t ht ↦ by
        rw [Set.uIcc_of_le hX] at ht
        exact
          congrArg (fun y ↦ y * deriv (fun u ↦ u * deriv (quarterWeight570 X) u) t)
            (h ⟨ht.1, ht.2.trans hXB⟩))
  have outer :=
    intervalIntegral.integral_congr (μ := MeasureTheory.volume) (f := fun t ↦
      F t * deriv (fun u ↦ u * deriv (quarterWeight570 X) u) t) (g := fun t ↦
      G t * deriv (fun u ↦ u * deriv (quarterWeight570 X) u) t) (a := 1) (b :=
      X * Real.exp (14 / 5))
      (fun t ht ↦ by
        rw [Set.uIcc_of_le hB] at ht
        exact congrArg (fun y ↦ y * deriv (fun u ↦ u * deriv (quarterWeight570 X) u) t) (h ht))
  rw [inner, outer]

/-- The section 99 Abel action can use the exact zero expansion on its
entire physical support, including the lower endpoint. -/
theorem section99_abel_zero_expansion {X : ℝ} (hX : 1 ≤ X) :
    section99AbelAction X
        (fun t ↦
          AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t -
            (t - Real.log (2 * Real.pi) * Real.log t)) =
      section99AbelAction X
        (fun t ↦
          (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re -
            AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries t -
            AnalyticNumberTheory.RiemannXi.qMinusOneRiemannZetaSecondLogDerivAtZero.re) := by
  exact section99_abel_congr hX (fun _ ht ↦ section99_centered_zero_eq ht.1)

/-- Continuous inputs on the physical support satisfy the integrability
conditions for subtracting their Abel actions. -/
theorem section99_abel_sub {X : ℝ} (hX : 1 ≤ X) {F G : ℝ → ℝ}
    (hF : ContinuousOn F (Set.Icc 1 (X * Real.exp (14 / 5))))
    (hG : ContinuousOn G (Set.Icc 1 (X * Real.exp (14 / 5)))) :
    section99AbelAction X (fun t ↦ F t - G t) =
      section99AbelAction X F - section99AbelAction X G := by
  let B := X * Real.exp (14 / 5)
  let P := fun t ↦ t * deriv (quarterWeight570 X) t
  have hx := zero_lt_one.trans_le hX
  have hXB : X ≤ B := le_mul_of_one_le_right hx.le (Real.one_le_exp (by norm_num only))
  have hQ : ContinuousOn (deriv P) (Set.Icc 1 B) :=
    (((quarter_weight_smooth hx).2.continuousOn_deriv_of_isOpen isOpen_Ioi (by decide)).mono
      (fun _ ht ↦ zero_lt_one.trans_le ht.1))
  have hI {H : ℝ → ℝ} (hH : ContinuousOn H (Set.Icc 1 B)) {b : ℝ} (hb : 1 ≤ b) (hbB : b ≤ B) :
    IntervalIntegrable (fun t ↦ H t * deriv P t) MeasureTheory.volume 1 b := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hb).2
    exact ((hH.mul hQ).mono (Set.Icc_subset_Icc_right hbB)).integrableOn_Icc
  have hf₁ := hI hF hX hXB
  have hg₁ := hI hG hX hXB
  have hf₂ := hI hF (hX.trans hXB) le_rfl
  have hg₂ := hI hG (hX.trans hXB) le_rfl
  dsimp (config := { failIfUnchanged := false }) only [P, B] at hf₁ hg₁ hf₂ hg₂
  dsimp only [section99AbelAction]
  simp only [sub_mul, intervalIntegral.integral_sub hf₁ hg₁, intervalIntegral.integral_sub hf₂ hg₂]
  ring

/-- On the entire physical support, split the centered Mangoldt Abel action
into nontrivial and trivial zero contributions. The constant pole residue
cancels exactly. -/
theorem section99_abel_zero_split {X : ℝ} (hX : 1 ≤ X) :
    section99AbelAction X
        (fun t ↦
          AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t -
            (t - Real.log (2 * Real.pi) * Real.log t)) =
      section99AbelAction X
          (fun t ↦ (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re) -
        section99AbelAction X AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries := by
  let Z := fun t : ℝ ↦ (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re
  let T := AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries
  let c := AnalyticNumberTheory.RiemannXi.qMinusOneRiemannZetaSecondLogDerivAtZero.re
  have hz : ContinuousOn Z (Set.Icc 1 (X * Real.exp (14 / 5))) :=
    Complex.continuous_re.comp_continuousOn
      (AnalyticNumberTheory.RiemannZeta.zero_sum_continuous (b := X * Real.exp (14 / 5))
        (le_refl (1 : ℝ)))
  have ht : ContinuousOn T (Set.Icc 1 (X * Real.exp (14 / 5))) :=
    AnalyticNumberTheory.RiemannZeta.trivial_cont_closed (le_refl (1 : ℝ))
  rw [section99_abel_zero_expansion hX]
  change section99AbelAction X (fun t ↦ (Z - T) t - c) = _
  rw [section99_abel_sub hX (hz.sub ht) (continuousOn_const (c := c)), section99_abel_const hX,
    sub_zero]
  exact section99_abel_sub hX hz ht

/-- The section 99 Abel actions of the real rectangular zero ledgers converge
to the action of the full nontrivial-zero series on the physical support. -/
theorem section99_zero_action_limit {X : ℝ} (hX : 1 ≤ X) :
    Filter.Tendsto
      (fun m : ℕ ↦
        section99AbelAction X
          (fun t ↦
            (∑
                ρ ∈
                  (AnalyticNumberTheory.RiemannZeta.riemannZetaZerosInAnyRectangle
                        (AnalyticNumberTheory.RiemannZeta.unifiedRectangleLower m)
                        (AnalyticNumberTheory.RiemannZeta.unifiedTauRectangleUpper 2 m)).filter
                    (fun ρ ↦ ¬ρ.re < 0),
                AnalyticNumberTheory.RiemannZeta.riemannZetaLogZeroContribution t ρ).re))
      Filter.atTop
      (nhds
        (section99AbelAction X
          (fun t ↦
            (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re))) := by
  let B := X * Real.exp (14 / 5)
  let P := fun t ↦ t * deriv (quarterWeight570 X) t
  have hx := zero_lt_one.trans_le hX
  have hXB : X ≤ B := le_mul_of_one_le_right hx.le (Real.one_le_exp (by norm_num only))
  have hQ {b : ℝ} : ContinuousOn (deriv P) (Set.Icc 1 b) :=
    (((quarter_weight_smooth hx).2.continuousOn_deriv_of_isOpen isOpen_Ioi (by decide)).mono
      (fun _ ht ↦ zero_lt_one.trans_le ht.1))
  have hi := AnalyticNumberTheory.RiemannZeta.weighted_zero_integral_limit (le_refl (1 : ℝ)) hX hQ
  have ho :=
    AnalyticNumberTheory.RiemannZeta.weighted_zero_integral_limit (le_refl (1 : ℝ)) (hX.trans hXB)
      hQ
  have hcut :=
    (Complex.continuous_re.tendsto _).comp
      (AnalyticNumberTheory.RiemannZeta.log_zero_tsum_limit_closed hX)
  have hone :=
    (Complex.continuous_re.tendsto _).comp
      (AnalyticNumberTheory.RiemannZeta.log_zero_tsum_limit_closed (le_refl (1 : ℝ)))
  exact (((hi.const_mul 4).sub ho).sub (hcut.const_mul (4 * P X))).add (hone.const_mul (3 * P 1))

/-- On the physical support, a finite sum of continuous inputs can be
evaluated by summing their individual Abel actions. -/
theorem section99_abel_finset_sum {ι : Type*} {X : ℝ} (hX : 1 ≤ X) (S : Finset ι) (F : ι → ℝ → ℝ)
    (hF : ∀ i ∈ S, ContinuousOn (F i) (Set.Icc 1 (X * Real.exp (14 / 5)))) :
    section99AbelAction X (fun t ↦ ∑ i ∈ S, F i t) = ∑ i ∈ S, section99AbelAction X (F i) := by
  let B := X * Real.exp (14 / 5)
  let P := fun t ↦ t * deriv (quarterWeight570 X) t
  have hx := zero_lt_one.trans_le hX
  have hXB : X ≤ B := le_mul_of_one_le_right hx.le (Real.one_le_exp (by norm_num only))
  have hQ : ContinuousOn (deriv P) (Set.Icc 1 B) :=
    (((quarter_weight_smooth hx).2.continuousOn_deriv_of_isOpen isOpen_Ioi (by decide)).mono
      (fun _ ht ↦ zero_lt_one.trans_le ht.1))
  have hI {b : ℝ} (hb : 1 ≤ b) (hbB : b ≤ B) :
    (∫ t in (1 : ℝ)..b, ∑ i ∈ S, F i t * deriv P t) =
      ∑ i ∈ S, ∫ t in (1 : ℝ)..b, F i t * deriv P t := by
    apply intervalIntegral.integral_finsetSum
    intro i hi
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hb).2
    exact (((hF i hi).mul hQ).mono (Set.Icc_subset_Icc_right hbB)).integrableOn_Icc
  change
    4 * (∫ t in (1 : ℝ)..X, (∑ i ∈ S, F i t) * deriv P t) -
          (∫ t in (1 : ℝ)..B, (∑ i ∈ S, F i t) * deriv P t) -
          4 * P X * (∑ i ∈ S, F i X) +
        3 * P 1 * (∑ i ∈ S, F i 1) =
      ∑ i ∈ S,
        (4 * (∫ t in (1 : ℝ)..X, F i t * deriv P t) - (∫ t in (1 : ℝ)..B, F i t * deriv P t) -
            4 * P X * F i X +
          3 * P 1 * F i 1)
  simp only [Finset.sum_mul, hI hX hXB, hI (hX.trans hXB) le_rfl, Finset.mul_sum,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]

/-- Summing the individual physical Abel contributions over successively
larger zero rectangles converges to the full nontrivial-zero contribution. -/
theorem section99_sum_action_limit {X : ℝ} (hX : 1 ≤ X) :
    Filter.Tendsto
      (fun m : ℕ ↦
        ∑
          ρ ∈
            (AnalyticNumberTheory.RiemannZeta.riemannZetaZerosInAnyRectangle
                  (AnalyticNumberTheory.RiemannZeta.unifiedRectangleLower m)
                  (AnalyticNumberTheory.RiemannZeta.unifiedTauRectangleUpper 2 m)).filter
              (fun ρ ↦ ¬ρ.re < 0),
          section99AbelAction X
            (fun t ↦ (AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re))
      Filter.atTop
      (nhds
        (section99AbelAction X
          (fun t ↦
            (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re))) := by
  apply (section99_zero_action_limit hX).congr'
  filter_upwards with m
  let S :=
    (AnalyticNumberTheory.RiemannZeta.riemannZetaZerosInAnyRectangle
          (AnalyticNumberTheory.RiemannZeta.unifiedRectangleLower m)
          (AnalyticNumberTheory.RiemannZeta.unifiedTauRectangleUpper 2 m)).filter
      (fun ρ ↦ ¬ρ.re < 0)
  let F := fun (ρ : ℂ) (t : ℝ) ↦ (AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re
  change
    section99AbelAction X
        (fun t ↦
          (∑ ρ ∈ S, AnalyticNumberTheory.RiemannZeta.riemannZetaLogZeroContribution t ρ).re) =
      ∑ ρ ∈ S, section99AbelAction X (F ρ)
  rw [←
    section99_abel_finset_sum hX S F
      (fun ρ _ ↦
        Complex.continuous_re.comp_continuousOn
          (AnalyticNumberTheory.RiemannZeta.zero_term_continuous zero_lt_one ρ))]
  apply section99_abel_congr hX
  intro t _
  dsimp only [F]
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro ρ hρ
  have hm := Finset.mem_filter.mp hρ
  have hz := (AnalyticNumberTheory.RiemannZeta.mem_riemannZetaZerosInAnyRectangle_iff.mp hm.1).2
  simp only [AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm, hz, true_and, not_lt.mp hm.2,
    ↓reduceIte]

/-- Two integrations by parts move the Abel action onto the derivative of
the logarithmic derivative of its input, retaining both cutoff values. -/
theorem section99_abel_parts {X : ℝ} (hX : 1 ≤ X) {F D H : ℝ → ℝ}
    (hF : ∀ t > 0, HasDerivAt F (D t) t) (hG : ∀ t > 0, HasDerivAt (fun u ↦ u * D u) (H t) t)
    (hD : ContinuousOn D (Set.Ioi 0)) (hH : ContinuousOn H (Set.Ioi 0)) :
    let B := X * Real.exp (14 / 5)
    let W := quarterWeight570 X
    section99AbelAction X F =
      4 * (∫ t in (1 : ℝ)..X, H t * W t) - (∫ t in (1 : ℝ)..B, H t * W t) - 4 * (X * D X) * W X +
        3 * D 1 * W 1 := by
  intro B W
  let P := fun t ↦ t * deriv W t
  let G := fun t ↦ t * D t
  have hx := zero_lt_one.trans_le hX
  have hb : 1 ≤ B := hX.trans (le_mul_of_one_le_right hx.le (Real.one_le_exp (by norm_num only)))
  obtain ⟨hW, hP⟩ := quarter_weight_smooth hx
  have hw (t : ℝ) (ht : 0 < t) : HasDerivAt W (deriv W t) t :=
    (((hW.differentiableOn (by decide)) t ht).differentiableAt (isOpen_Ioi.mem_nhds ht)).hasDerivAt
  have hp (t : ℝ) (ht : 0 < t) : HasDerivAt P (deriv P t) t :=
    (((hP.differentiableOn (by decide)) t ht).differentiableAt (isOpen_Ioi.mem_nhds ht)).hasDerivAt
  have hi {b : ℝ} (h : 1 ≤ b) :
    (∫ t in (1 : ℝ)..b, F t * deriv P t) =
      F b * P b - F 1 * P 1 - (G b * W b - G 1 * W 1) + ∫ t in (1 : ℝ)..b, H t * W t := by
    have hsub : Set.uIcc (1 : ℝ) b ⊆ Set.Ioi 0 := by
      rw [Set.uIcc_of_le h]
      exact fun _ ht ↦ zero_lt_one.trans_le ht.1
    have h₁ :=
      intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun t ht ↦ hF t (hsub ht))
        (fun t ht ↦ hp t (hsub ht)) (hD.mono hsub).intervalIntegrable
        ((hP.continuousOn_deriv_of_isOpen isOpen_Ioi (by decide)).mono hsub).intervalIntegrable
    have h₂ :=
      intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun t ht ↦ hG t (hsub ht))
        (fun t ht ↦ hw t (hsub ht)) (hH.mono hsub).intervalIntegrable
        ((hW.continuousOn_deriv_of_isOpen isOpen_Ioi (by decide)).mono hsub).intervalIntegrable
    have he : (∫ t in (1 : ℝ)..b, D t * P t) = ∫ t in (1 : ℝ)..b, G t * deriv W t := by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only [P, G]
      ring
    rw [h₁, he, h₂]
    ring
  obtain ⟨hwB, hpB⟩ := quarter_support_jet_570 hx
  change W B = 0 at hwB
  have hPB : P B = 0 := by
    dsimp only [P, W, B]
    rw [hpB, mul_zero]
  change
    4 * (∫ t in (1 : ℝ)..X, F t * deriv P t) - (∫ t in (1 : ℝ)..B, F t * deriv P t) -
          4 * P X * F X +
        3 * P 1 * F 1 =
      _
  rw [hi hX, hi hb, hPB, hwB]
  dsimp only [G]
  ring

/-- Multiplying the first derivative of a complex power by its real
argument restores the original exponent. This is the derivative input to
the two integrations by parts for a zero contribution. -/
private theorem quarter_cpow_log_deriv {t : ℝ} (ht : 0 < t) (c ρ : ℂ) :
    t * (c * ρ * (t : ℂ) ^ (ρ - 1)).re = (c * ρ * (t : ℂ) ^ ρ).re := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hre (z : ℂ) : ((t : ℂ) * z).re = t * z.re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [← hre]
  apply congrArg Complex.re
  calc
    (t : ℂ) * (c * ρ * (t : ℂ) ^ (ρ - 1)) = c * ρ * ((t : ℂ) ^ (ρ - 1) * (t : ℂ) ^ (1 : ℂ)) := by
      rw [Complex.cpow_one]
      ring
    _ = c * ρ * (t : ℂ) ^ ρ := by rw [← Complex.cpow_add _ _ ht', sub_add_cancel]

/-- The physical Abel action of a complex power times a constant is a
weighted Mellin integral with explicit endpoint terms. Zero contributions
use the constant minus the multiplicity divided by the square of the zero. -/
theorem section99_abel_cpow {X : ℝ} (hX : 1 ≤ X) {ρ : ℂ} (hρ : ρ ≠ 0) (c : ℂ) :
    let B := X * Real.exp (14 / 5)
    let W := quarterWeight570 X
    let H := fun t : ℝ ↦ (c * ρ * ρ * (t : ℂ) ^ (ρ - 1)).re
    section99AbelAction X (fun t ↦ (c * (t : ℂ) ^ ρ).re) =
      4 * (∫ t in (1 : ℝ)..X, H t * W t) - (∫ t in (1 : ℝ)..B, H t * W t) -
          4 * (c * ρ * (X : ℂ) ^ ρ).re * W X +
        3 * (c * ρ).re * W 1 := by
  intro B W H
  let D := fun t : ℝ ↦ (c * ρ * (t : ℂ) ^ (ρ - 1)).re
  have hpow (a : ℂ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u : ℝ ↦ (a * (u : ℂ) ^ ρ).re) (a * ρ * (t : ℂ) ^ (ρ - 1)).re t := by
    have hd := (hasDerivAt_ofReal_cpow_const ht.ne' hρ).const_mul a
    simpa only [zero_apply, zero_add, Complex.reCLM_apply, mul_assoc] using
      (hasDerivAt_const t Complex.reCLM).clm_apply hd
  have hg (t : ℝ) (ht : 0 < t) : HasDerivAt (fun u ↦ u * D u) (H t) t := by
    apply (hpow (c * ρ) ht).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioi.mem_nhds ht] with u hu
    exact quarter_cpow_log_deriv hu c ρ
  have hc (a : ℂ) : ContinuousOn (fun t : ℝ ↦ (a * (t : ℂ) ^ (ρ - 1)).re) (Set.Ioi 0) := by
    intro t ht
    have hp := Complex.continuousAt_ofReal_cpow_const t (ρ - 1) (Or.inr (ne_of_gt ht))
    exact (Complex.continuous_re.continuousAt.comp (continuousAt_const.mul hp)).continuousWithinAt
  have h := section99_abel_parts hX (fun _ ht ↦ hpow c ht) hg (hc (c * ρ)) (hc (c * ρ * ρ))
  dsimp only at h
  change _ = _ - 4 * (c * ρ * (X : ℂ) ^ ρ).re * W X + 3 * (c * ρ).re * W 1
  rw [h, quarter_cpow_log_deriv (zero_lt_one.trans_le hX), Complex.ofReal_one, Complex.one_cpow,
    mul_one]

/-- The contribution of a nontrivial zero to the physical Abel action is
its signed power integral with two explicit boundary values. The zero's
multiplicity multiplies every term. -/
theorem section99_abel_zero_term {X : ℝ} (hX : 1 ≤ X) {ρ : ℂ} (hz : riemannZeta ρ = 0)
    (hre : 0 ≤ ρ.re) (hρ : ρ ≠ 0) :
    let B := X * Real.exp (14 / 5)
    let W := quarterWeight570 X
    let m := (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ)
    let H := fun t : ℝ ↦ (-m * (t : ℂ) ^ (ρ - 1)).re
    section99AbelAction X
        (fun t ↦ (AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re) =
      4 * (∫ t in (1 : ℝ)..X, H t * W t) - (∫ t in (1 : ℝ)..B, H t * W t) -
          4 * (-m / ρ * (X : ℂ) ^ ρ).re * W X +
        3 * (-m / ρ).re * W 1 := by
  intro B W m H
  let c := -m / ρ ^ 2
  have h₁ : c * ρ = -m / ρ := by
    dsimp only [c]
    rw [pow_two, ← div_div, div_mul_cancel₀ _ hρ]
  have h₂ : c * ρ * ρ = -m := by rw [h₁, div_mul_cancel₀ _ hρ]
  have he :
    (fun t ↦ (AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re) =
      (fun t : ℝ ↦ (c * (t : ℂ) ^ ρ).re) := by
    funext t
    simp only [AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm, hz, hre, and_self,
      ↓reduceIte, AnalyticNumberTheory.RiemannZeta.riemannZetaLogZeroContribution, c]
    rw [div_mul_eq_mul_div]
  rw [he]
  have h := section99_abel_cpow hX hρ c
  dsimp only at h
  simp only [h₂] at h
  simp only [h₁] at h
  exact h

/-- The physical Mellin integral and boundary contributions from one
nontrivial zero at cutoff X, including its multiplicity. -/
noncomputable def section99ZeroIntegral (X : ℝ) (ρ : ℂ) : ℝ :=
  let W := quarterWeight570 X
  let m := (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ)
  let H := fun t : ℝ ↦ (-m * (t : ℂ) ^ (ρ - 1)).re
  4 * (∫ t in (1 : ℝ)..X, H t * W t) - (∫ t in (1 : ℝ)..X * Real.exp (14 / 5), H t * W t) -
      4 * (-m / ρ * (X : ℂ) ^ ρ).re * W X +
    3 * (-m / ρ).re * W 1

/-- The sum of the explicit Mellin and endpoint contributions converges to
the nontrivial-zero part of the section 99 principal Abel action. -/
theorem section99_zero_integral_limit {X : ℝ} (hX : 1 ≤ X) :
    Filter.Tendsto
      (fun m : ℕ ↦
        ∑
          ρ ∈
            (AnalyticNumberTheory.RiemannZeta.riemannZetaZerosInAnyRectangle
                  (AnalyticNumberTheory.RiemannZeta.unifiedRectangleLower m)
                  (AnalyticNumberTheory.RiemannZeta.unifiedTauRectangleUpper 2 m)).filter
              (fun ρ ↦ ¬ρ.re < 0),
          section99ZeroIntegral X ρ)
      Filter.atTop
      (nhds
        (section99AbelAction X
          (fun t ↦
            (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re))) := by
  apply (section99_sum_action_limit hX).congr'
  filter_upwards with m
  apply Finset.sum_congr rfl
  intro ρ hρ
  have hm := Finset.mem_filter.mp hρ
  have hz := (AnalyticNumberTheory.RiemannZeta.mem_riemannZetaZerosInAnyRectangle_iff.mp hm.1).2
  have hn : ρ ≠ 0 := by
    intro he
    rw [he, riemannZeta_zero] at hz
    norm_num only at hz
  exact section99_abel_zero_term hX hz (not_lt.mp hm.2) hn

/-- At positive arguments the physical weight at cutoff X is the unit
weight evaluated at the rescaled argument, divided by the square root of X. -/
private theorem quarter_weight_rescale {X u : ℝ} (hX : 0 < X) (hu : 0 < u) :
    quarterWeight570 X (u * X) = (Real.sqrt X)⁻¹ * quarterWeight570 1 u := by
  simp only [quarterWeight570, mul_div_cancel_right₀ _ hX.ne', div_one, Real.sqrt_mul hu.le,
    one_div, mul_inv_rev]
  ring

/-- Rescale each signed power integral in the physical zero contribution
to a unit-cutoff integral. Its lower limit is exactly the physical endpoint
one divided by the cutoff. -/
theorem section99_power_integral_scale {X b : ℝ} (hX : 0 < X) (hb : 1 ≤ b) (c ρ : ℂ) :
    (∫ t in (1 : ℝ)..b, (c * (t : ℂ) ^ (ρ - 1)).re * quarterWeight570 X t) =
      Real.sqrt X *
        ∫ u in (1 / X : ℝ)..b / X,
          (c * (X : ℂ) ^ (ρ - 1) * (u : ℂ) ^ (ρ - 1)).re * quarterWeight570 1 u := by
  let f := fun t : ℝ ↦ (c * (t : ℂ) ^ (ρ - 1)).re * quarterWeight570 X t
  have h := intervalIntegral.integral_comp_mul_right f (a := 1 / X) (b := b / X) hX.ne'
  rw [div_mul_cancel₀ _ hX.ne', div_mul_cancel₀ _ hX.ne', smul_eq_mul] at h
  have he :
    (∫ u in (1 / X : ℝ)..b / X, f (u * X)) =
      ∫ u in (1 / X : ℝ)..b / X,
        (Real.sqrt X)⁻¹ *
          ((c * (X : ℂ) ^ (ρ - 1) * (u : ℂ) ^ (ρ - 1)).re * quarterWeight570 1 u) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le (div_le_div_of_nonneg_right hb hX.le)] at hu
    have hu0 := (one_div_pos.mpr hX).trans_le hu.1
    dsimp only [f]
    rw [quarter_weight_rescale hX hu0, Complex.ofReal_mul, Complex.ofReal_mul_cpow hu0.le X,
      show c * ((u : ℂ) ^ (ρ - 1) * (X : ℂ) ^ (ρ - 1)) = c * (X : ℂ) ^ (ρ - 1) * (u : ℂ) ^ (ρ - 1)
        by ring]
    ring
  rw [he, intervalIntegral.integral_const_mul] at h
  have hh := congrArg (fun y : ℝ ↦ X * y) h
  rw [mul_inv_cancel_left₀ hX.ne'] at hh
  have hs : X * (Real.sqrt X)⁻¹ = Real.sqrt X := by
    rw [← div_eq_mul_inv]
    apply (div_eq_iff (Real.sqrt_pos.mpr hX).ne').mpr
    rw [← sq, Real.sq_sqrt hX.le]
  rw [← mul_assoc, hs] at hh
  exact hh.symm

/-- In the zero coefficient both integrals use the same unit-cutoff
integrand, with upper limits one and the exponential support endpoint. -/
theorem section99_zero_integral_scale {X : ℝ} (hX : 1 ≤ X) (ρ : ℂ) :
    let m := (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ)
    let F := fun u : ℝ ↦ (-m * (X : ℂ) ^ (ρ - 1) * (u : ℂ) ^ (ρ - 1)).re * quarterWeight570 1 u
    section99ZeroIntegral X ρ =
      4 * (Real.sqrt X * ∫ u in (1 / X : ℝ)..1, F u) -
          (Real.sqrt X * ∫ u in (1 / X : ℝ)..Real.exp (14 / 5), F u) -
          4 * (-m / ρ * (X : ℂ) ^ ρ).re * quarterWeight570 X X +
        3 * (-m / ρ).re * quarterWeight570 X 1 := by
  dsimp only [section99ZeroIntegral]
  have hx := zero_lt_one.trans_le hX
  have hb :=
    hX.trans (le_mul_of_one_le_right hx.le (Real.one_le_exp (by norm_num only : (0 : ℝ) ≤ 14 / 5)))
  rw [section99_power_integral_scale hx hX, section99_power_integral_scale hx hb, div_self hx.ne',
    mul_div_cancel_left₀ _ hx.ne']

/-- The unit physical weight on positive arguments is a logarithmic
polynomial times a power, in the normalization used by the Mellin moments. -/
theorem quarter_unit_weight_power {u : ℝ} (hu : 0 < u) :
    quarterWeight570 1 u =
      (Real.exp (-(14 / 5 * (51 / 50))) / ((50 / 51) ^ 5 * 120)) *
        (u ^ ((13 / 25 : ℝ)) * (14 / 5 - Real.log u) ^ 5) := by
  rw [quarterWeight570, div_one, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hu,
    Real.rpow_def_of_pos hu, div_pow]
  have he :
    Real.exp (-((2 * (7 / 5) - Real.log u) / (2 * (25 / 51)))) =
      Real.exp (-(14 / 5 * (51 / 50))) *
        (Real.exp (Real.log u * (13 / 25)) * Real.exp (Real.log u * (1 / 2))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  dsimp only
  rw [he]
  norm_num only [show (2 * (7 / 5) : ℝ) = 14 / 5 by norm_num only,
    show (2 * (25 / 51) : ℝ) = 50 / 51 by norm_num only]
  field_simp [Real.exp_ne_zero]
  ring

/-- A complex power times the unit weight is integrable down to zero
whenever the effective Mellin exponent has positive real part. -/
theorem section99_power_integrable_zero {ρ : ℂ} (hρ : 0 < ρ.re + 13 / 25) (c : ℂ) :
    IntervalIntegrable (fun u : ℝ ↦ (c * (u : ℂ) ^ (ρ - 1)).re * quarterWeight570 1 u)
      MeasureTheory.volume 0 1 := by
  let C := Real.exp (-(14 / 5 * (51 / 50))) / ((50 / 51) ^ 5 * 120)
  have hC : 0 ≤ C := by
    dsimp only [C]; positivity
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2
  have hi := ((Analysis.shifted_log_moment 5 (14 / 5) hρ).1.const_mul (‖c‖ * C))
  apply hi.mono'
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioc
    intro u hu
    have hp := Complex.continuousAt_ofReal_cpow_const u (ρ - 1) (Or.inr hu.1.ne')
    have hW : ContinuousOn (quarterWeight570 1) (Set.Ioi 0) :=
      (quarter_weight_smooth (X := 1) zero_lt_one).1.continuousOn
    have hw := (hW u hu.1).continuousAt (isOpen_Ioi.mem_nhds hu.1)
    exact
      ((Complex.continuous_re.continuousAt.comp (continuousAt_const.mul hp)).mul
          hw).continuousWithinAt
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
    have hl : 0 ≤ 14 / 5 - Real.log u := by linarith only [Real.log_nonpos hu.1.le hu.2]
    have hw : 0 ≤ quarterWeight570 1 u := by
      rw [quarter_unit_weight_power hu.1]
      exact mul_nonneg hC (mul_nonneg (Real.rpow_nonneg hu.1.le _) (pow_nonneg hl _))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw]
    calc
      _ ≤ ‖c * (u : ℂ) ^ (ρ - 1)‖ * quarterWeight570 1 u :=
        mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm _) hw
      _ = _ := by
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu.1, Complex.sub_re, Complex.one_re,
          quarter_unit_weight_power hu.1]
        rw [show ρ.re + 13 / 25 - 1 = (ρ.re - 1) + 13 / 25 by ring, Real.rpow_add hu.1]
        ring

/-- Extending both scaled zero integrals to zero subtracts exactly three
times the omitted lower integral, since both use the same integrand. -/
theorem section99_extend_integrals {X : ℝ} (hX : 1 ≤ X) {ρ : ℂ} (hρ : 0 < ρ.re + 13 / 25) (c : ℂ) :
    let F := fun u : ℝ ↦ (c * (u : ℂ) ^ (ρ - 1)).re * quarterWeight570 1 u
    4 * (∫ u in (1 / X : ℝ)..1, F u) - (∫ u in (1 / X : ℝ)..Real.exp (14 / 5), F u) =
      4 * (∫ u in (0 : ℝ)..1, F u) - (∫ u in (0 : ℝ)..Real.exp (14 / 5), F u) -
        3 * (∫ u in (0 : ℝ)..1 / X, F u) := by
  intro F
  have hx := zero_lt_one.trans_le hX
  have ha : 0 < 1 / X := one_div_pos.mpr hx
  have ha1 : 1 / X ≤ 1 := by
    rw [one_div]; exact inv_le_one_of_one_le₀ hX
  have h0 : IntervalIntegrable F MeasureTheory.volume 0 (1 / X) :=
    (section99_power_integrable_zero hρ c).mono_set
      (by
        rw [Set.uIcc_of_le ha.le, Set.uIcc_of_le zero_le_one]
        exact Set.Icc_subset_Icc_right ha1)
  have hi {b : ℝ} (hb : 1 ≤ b) : IntervalIntegrable F MeasureTheory.volume (1 / X) b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (ha1.trans hb)]
    intro u hu
    have hu0 := ha.trans_le hu.1
    have hp := Complex.continuousAt_ofReal_cpow_const u (ρ - 1) (Or.inr hu0.ne')
    have hw : ContinuousOn (quarterWeight570 1) (Set.Ioi 0) :=
      (quarter_weight_smooth (X := 1) zero_lt_one).1.continuousOn
    exact
      ((Complex.continuous_re.continuousAt.comp (continuousAt_const.mul hp)).mul
          ((hw u hu0).continuousAt (isOpen_Ioi.mem_nhds hu0))).continuousWithinAt
  rw [← intervalIntegral.integral_add_adjacent_intervals h0 (hi le_rfl), ←
    intervalIntegral.integral_add_adjacent_intervals h0 (hi (Real.one_le_exp (by norm_num only)))]
  ring

/-- The zero contribution is the difference of two moments starting at
zero, the common omitted integral, and its explicit boundary terms. -/
theorem section99_zero_integral_extended {X : ℝ} (hX : 1 ≤ X) {ρ : ℂ} (hρ : 0 < ρ.re + 13 / 25) :
    let m := (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ)
    let F := fun u : ℝ ↦ (-m * (X : ℂ) ^ (ρ - 1) * (u : ℂ) ^ (ρ - 1)).re * quarterWeight570 1 u
    section99ZeroIntegral X ρ =
      Real.sqrt X *
            (4 * (∫ u in (0 : ℝ)..1, F u) - (∫ u in (0 : ℝ)..Real.exp (14 / 5), F u) -
              3 * (∫ u in (0 : ℝ)..1 / X, F u)) -
          4 * (-m / ρ * (X : ℂ) ^ ρ).re * quarterWeight570 X X +
        3 * (-m / ρ).re * quarterWeight570 X 1 := by
  intro m F
  have hs := section99_zero_integral_scale hX ρ
  have he := section99_extend_integrals hX hρ (-m * (X : ℂ) ^ (ρ - 1))
  dsimp only at hs he
  rw [hs]
  have hm := congrArg (fun y : ℝ ↦ Real.sqrt X * y) he
  change Real.sqrt X * _ = Real.sqrt X * _ at hm
  dsimp only [F, m] at *
  linarith only [hm]

/-- The logarithmic substitution at the unit cutoff turns the power
weight and its Jacobian into an exponential times a degree-five polynomial. -/
theorem section99_log_moment_integrand (v : ℝ) (c ρ : ℂ) :
    Real.exp (-v) * ((c * (Real.exp (-v) : ℂ) ^ (ρ - 1)).re * quarterWeight570 1 (Real.exp (-v))) =
      (Real.exp (-(14 / 5 * (51 / 50))) / ((50 / 51) ^ 5 * 120)) *
        ((14 / 5 + v) ^ 5 * (c * Complex.exp (-(ρ + (13 / 25 : ℂ)) * (v : ℂ))).re) := by
  have hp := Real.exp_pos (-v)
  rw [quarter_unit_weight_power hp, Real.rpow_def_of_pos hp, Real.log_exp, sub_neg_eq_add]
  have hpow : (Real.exp (-v) : ℂ) ^ (ρ - 1) = Complex.exp ((-(v : ℂ)) * (ρ - 1)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'), ← Complex.ofReal_log hp.le,
      Real.log_exp, Complex.ofReal_neg]
  rw [hpow]
  have he :
    Complex.exp (-(ρ + (13 / 25 : ℂ)) * (v : ℂ)) =
      (Real.exp (-v) : ℂ) *
        ((Real.exp (-v * (13 / 25)) : ℂ) * Complex.exp (-(v : ℂ) * (ρ - 1))) := by
    rw [Complex.ofReal_exp, Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg, ←
      Complex.exp_add, ← Complex.exp_add]
    push_cast
    congr 1
    ring
  rw [he]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, add_zero]
  ring

/-- The zero moment up to a positive cutoff is a six-term rational function of the
effective Mellin exponent, multiplied by the fixed kernel normalization. -/
theorem section99_mellin_moment {ρ : ℂ} (hρ : 0 < ρ.re + 13 / 25) (c : ℂ) {y : ℝ} (hy : 0 < y) :
    let s := ρ + (13 / 25 : ℂ)
    (∫ u in (0 : ℝ)..y, (c * (u : ℂ) ^ (ρ - 1)).re * quarterWeight570 1 u) =
      (Real.exp (-(14 / 5 * (51 / 50))) / ((50 / 51) ^ 5 * 120)) *
        (c *
            ((y : ℂ) ^ s *
              (∑ j ∈ Finset.range 6,
                (((5 : ℕ).choose j : ℂ) * ((14 / 5 - Real.log y : ℝ) : ℂ) ^ (5 - j)) *
                  ((j.factorial : ℂ) / s ^ (j + 1))))).re := by
  intro s
  have hs : 0 < s.re := by
    dsimp only [s]
    norm_num only [Complex.add_re, Complex.div_ofNat_re]
    exact hρ
  let f := fun u : ℝ ↦ (u : ℂ) ^ (s - 1) * ((14 / 5 - Real.log u : ℝ) : ℂ) ^ 5
  have hm := Analysis.complex_log_moment_cutoff 5 (14 / 5) hs hy
  rw [intervalIntegral.integral_of_le hy.le] at hm
  have hi : MeasureTheory.IntegrableOn f (Set.Ioc 0 y) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hy.le).1
      (Analysis.complex_log_moment_integrable 5 (14 / 5) hs hy)
  let C := Real.exp (-(14 / 5 * (51 / 50))) / ((50 / 51) ^ 5 * 120)
  rw [intervalIntegral.integral_of_le hy.le]
  have hw :
    (∫ u in Set.Ioc (0 : ℝ) y, (c * (u : ℂ) ^ (ρ - 1)).re * quarterWeight570 1 u) =
      ∫ u in Set.Ioc (0 : ℝ) y, C * (c * f u).re := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro u hu
    have hpow : (u : ℂ) ^ (s - 1) = (u : ℂ) ^ (ρ - 1) * ((u ^ (13 / 25 : ℝ) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hu.1.le, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hu.1.ne')]
      congr 1
      dsimp only [s]
      push_cast
      ring
    dsimp only [f]
    rw [quarter_unit_weight_power hu.1, hpow, ← Complex.ofReal_pow]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero]
    dsimp only [C]
    ring
  rw [hw, MeasureTheory.integral_const_mul]
  have hr := integral_re (hi.const_mul c)
  simp only [RCLike.re_eq_complex_re] at hr
  rw [hr, MeasureTheory.integral_const_mul]
  change C * (c * ∫ u in Set.Ioc (0 : ℝ) y, f u).re = _
  rw [show (∫ u in Set.Ioc (0 : ℝ) y, f u) = _ from hm]

/-- The unit-cutoff zero moment is a six-term rational function of the
effective Mellin exponent, multiplied by the fixed kernel normalization. -/
theorem section99_unit_mellin_moment {ρ : ℂ} (hρ : 0 < ρ.re + 13 / 25) (c : ℂ) :
    let s := ρ + (13 / 25 : ℂ)
    (∫ u in (0 : ℝ)..1, (c * (u : ℂ) ^ (ρ - 1)).re * quarterWeight570 1 u) =
      (Real.exp (-(14 / 5 * (51 / 50))) / ((50 / 51) ^ 5 * 120)) *
        (c *
            (∑ j ∈ Finset.range 6,
              (((5 : ℕ).choose j : ℂ) * (14 / 5 : ℂ) ^ (5 - j)) *
                ((j.factorial : ℂ) / s ^ (j + 1)))).re := by
  simpa only [Complex.ofReal_one, Complex.one_cpow, one_mul, Real.log_one, sub_zero,
    Complex.ofReal_div, Complex.ofReal_ofNat] using
    section99_mellin_moment hρ c (y := 1) zero_lt_one

/-- The six logarithmic moments at a positive endpoint y form the
polynomial in inverse powers of the effective exponent s. -/
noncomputable def section99Moment (s : ℂ) (y : ℝ) : ℂ :=
  (y : ℂ) ^ s *
    ∑ j ∈ Finset.range 6,
      (((5 : ℕ).choose j : ℂ) * ((14 / 5 - Real.log y : ℝ) : ℂ) ^ (5 - j)) *
        ((j.factorial : ℂ) / s ^ (j + 1))

/-- Evaluate the physical zero coefficient by finite moments at the unit
cutoff, support endpoint and omitted lower endpoint. -/
theorem section99_zero_integral_formula {X : ℝ} (hX : 1 ≤ X) {ρ : ℂ} (hρ : 0 < ρ.re + 13 / 25) :
    let m := (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ)
    let c := -m * (X : ℂ) ^ (ρ - 1)
    let s := ρ + (13 / 25 : ℂ)
    let C := Real.exp (-(14 / 5 * (51 / 50))) / ((50 / 51) ^ 5 * 120)
    section99ZeroIntegral X ρ =
      Real.sqrt X * C *
            (c *
                (4 * section99Moment s 1 - section99Moment s (Real.exp (14 / 5)) -
                  3 * section99Moment s (1 / X))).re -
          4 * (-m / ρ * (X : ℂ) ^ ρ).re * quarterWeight570 X X +
        3 * (-m / ρ).re * quarterWeight570 X 1 := by
  intro m c s C
  have h := section99_zero_integral_extended hX hρ
  have hM {y : ℝ} (hy : 0 < y) :
    (∫ u in (0 : ℝ)..y, (c * (u : ℂ) ^ (ρ - 1)).re * quarterWeight570 1 u) =
      C * (c * section99Moment s y).re :=
    section99_mellin_moment hρ c hy
  change section99ZeroIntegral X ρ = _ at h
  rw [h, hM zero_lt_one, hM (Real.exp_pos _), hM (one_div_pos.mpr (zero_lt_one.trans_le hX))]
  have hscale (a : ℝ) (z : ℂ) : (c * ((a : ℂ) * z)).re = a * (c * z).re := by
    rw [← mul_assoc, mul_comm c, mul_assoc]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hlinear (A B D : ℂ) :
    (c * (4 * A - B - 3 * D)).re = 4 * (c * A).re - (c * B).re - 3 * (c * D).re := by
    simp only [mul_sub, Complex.sub_re]
    exact congrArg₂ (· - ·) (congrArg (· - (c * B).re) (hscale 4 A)) (hscale 3 D)
  rw [hlinear]
  ring

/-- At the exponential endpoint the logarithmic shift vanishes and only
the highest inverse power contributes to the full-support Mellin moment. -/
theorem section99_moment_support (s : ℂ) :
    section99Moment s (Real.exp (14 / 5)) = (Real.exp (14 / 5) : ℂ) ^ s * (120 / s ^ 6) := by
  unfold section99Moment
  norm_num only [Real.log_exp, sub_self, Complex.ofReal_zero, Finset.sum_range_succ,
    Finset.sum_range_zero, Nat.reduceSub, Nat.reduceAdd, zero_pow, pow_zero, Nat.factorial,
    Nat.choose_self, Nat.cast_one, Nat.cast_ofNat, zero_mul, mul_zero, one_mul, zero_add,
    Nat.reduceMul]

/-- Normalize the cutoff power so its modulus is one on the critical line. -/
theorem section99_cutoff_phase_mul {X : ℝ} (hX : 0 < X) (ρ : ℂ) :
    (Real.sqrt X : ℂ) * (X : ℂ) ^ (ρ - 1) = (X : ℂ) ^ ρ / (Real.sqrt X : ℂ) := by
  apply (eq_div_iff (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hX).ne')).mpr
  calc
    _ = ((Real.sqrt X : ℂ) * (Real.sqrt X : ℂ)) * (X : ℂ) ^ (ρ - 1) := by ring
    _ = (X : ℂ) ^ (1 : ℂ) * (X : ℂ) ^ (ρ - 1) := by
      rw [Complex.cpow_one, ← Complex.ofReal_mul, ← sq, Real.sq_sqrt hX.le]
    _ = (X : ℂ) ^ ρ := by
      rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hX.ne')]
      congr 1
      ring

/-- On the critical line the normalized cutoff power has norm one, so
the magnitude of a coefficient can be bounded independently of its phase. -/
theorem section99_cutoff_phase_norm {X : ℝ} (hX : 0 < X) {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    ‖(X : ℂ) ^ ρ / (Real.sqrt X : ℂ)‖ = 1 := by
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hX, hρ, ← Real.sqrt_eq_rpow, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg X), div_self (Real.sqrt_pos.mpr hX).ne']

/-- The radius-independent coefficient multiplying the critical-line
cutoff phase. The two full moments and the upper boundary enter together. -/
noncomputable def section99PhaseKernel (ρ : ℂ) : ℂ :=
  let s := ρ + (13 / 25 : ℂ)
  let C := (Real.exp (-(14 / 5 * (51 / 50))) / ((50 / 51) ^ 5 * 120) : ℝ)
  4 * (quarterWeight570 1 1 : ℂ) / ρ -
    (C : ℂ) * (4 * section99Moment s 1 - section99Moment s (Real.exp (14 / 5)))

/-- Split a zero coefficient into its normalized phase times a fixed kernel
and two corrections from the physical lower cutoff. -/
theorem section99_zero_phase_split {X : ℝ} (hX : 1 ≤ X) {ρ : ℂ} (hρ : 0 < ρ.re + 13 / 25) :
    let m := (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ)
    let p := (X : ℂ) ^ ρ / (Real.sqrt X : ℂ)
    let C := (Real.exp (-(14 / 5 * (51 / 50))) / ((50 / 51) ^ 5 * 120) : ℝ)
    section99ZeroIntegral X ρ =
      (m * p * section99PhaseKernel ρ).re +
        3 * C * (m * p * section99Moment (ρ + 13 / 25) (1 / X)).re +
        3 * (-m / ρ).re * quarterWeight570 X 1 := by
  intro m p C
  have hx := zero_lt_one.trans_le hX
  have hp := section99_cutoff_phase_mul hx ρ
  have hw := quarter_weight_rescale hx (u := 1) zero_lt_one
  rw [one_mul] at hw
  have h := section99_zero_integral_formula hX hρ
  dsimp only at h
  rw [h, hw]
  let A := 4 * section99Moment (ρ + 13 / 25) 1 - section99Moment (ρ + 13 / 25) (Real.exp (14 / 5))
  let D := section99Moment (ρ + 13 / 25) (1 / X)
  let w := quarterWeight570 1 1
  change
    Real.sqrt X * C * (-m * (X : ℂ) ^ (ρ - 1) * (A - 3 * D)).re -
          4 * (-m / ρ * (X : ℂ) ^ ρ).re * ((Real.sqrt X)⁻¹ * w) +
        3 * (-m / ρ).re * quarterWeight570 X 1 =
      (m * p * (4 * (w : ℂ) / ρ - (C : ℂ) * A)).re + 3 * C * (m * p * D).re +
        3 * (-m / ρ).re * quarterWeight570 X 1
  have hre (a : ℝ) (z : ℂ) : ((a : ℂ) * z).re = a * z.re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have h₁ :
    ((Real.sqrt X : ℂ) * (-m * (X : ℂ) ^ (ρ - 1) * (A - 3 * D))) = -m * p * (A - 3 * D) := by
    dsimp only [p]
    rw [← hp]
    ring
  have h₂ : (((Real.sqrt X)⁻¹ : ℝ) : ℂ) * (-m / ρ * (X : ℂ) ^ ρ) = -m / ρ * p := by
    dsimp only [p]
    rw [Complex.ofReal_inv]
    ring
  have hr₁ := congrArg Complex.re h₁
  have hr₂ := congrArg Complex.re h₂
  rw [hre] at hr₁ hr₂
  have he :
    (m * p * (4 * (w : ℂ) / ρ - (C : ℂ) * A)).re =
      -4 * w * (-m / ρ * p).re - C * (m * p * A).re := by
    rw [mul_sub, Complex.sub_re]
    congr 1
    · rw [← hre (-4 * w)]
      congr 1
      push_cast
      ring
    · rw [← hre C]
      congr 1
      ring
  have hf : (-m * p * (A - 3 * D)).re = -(m * p * A).re + 3 * (m * p * D).re := by
    rw [← hre (3 : ℝ), ← Complex.neg_re, ← Complex.add_re]
    congr 1
    push_cast
    ring
  rw [he]
  rw [hf] at hr₁
  calc
    _ =
        C * ((Real.sqrt X) * (-m * (X : ℂ) ^ (ρ - 1) * (A - 3 * D)).re) -
            4 * w * ((Real.sqrt X)⁻¹ * (-m / ρ * (X : ℂ) ^ ρ).re) +
          3 * (-m / ρ).re * quarterWeight570 X 1 :=
      by ring
    _ = _ := by
      rw [hr₁, hr₂]; ring

/-- On the critical line, the modulus of the phase term is bounded by
the multiplicity times the norm of the radius-independent kernel. -/
theorem section99_phase_kernel_bound {X : ℝ} (hX : 0 < X) {ρ : ℂ} (hρ : ρ.re = 1 / 2) (m : ℕ) :
    |((m : ℂ) * ((X : ℂ) ^ ρ / (Real.sqrt X : ℂ)) * section99PhaseKernel ρ).re| ≤
      (m : ℝ) * ‖section99PhaseKernel ρ‖ := by
  apply (Complex.abs_re_le_norm _).trans
  rw [norm_mul, norm_mul, section99_cutoff_phase_norm hX hρ, mul_one, ← Complex.ofReal_natCast,
    Complex.norm_real, Real.norm_of_nonneg (Nat.cast_nonneg m)]

/-- Isolate the inverse-square leading term of the phase kernel. The
unit moment's first reciprocal combines with the boundary reciprocal. -/
theorem section99_phase_kernel_expand {ρ : ℂ} (hρ : ρ ≠ 0) (hs : ρ + (13 / 25 : ℂ) ≠ 0) :
    let s := ρ + (13 / 25 : ℂ)
    let C := (Real.exp (-(14 / 5 * (51 / 50))) / ((50 / 51) ^ 5 * 120) : ℝ)
    section99PhaseKernel ρ =
      (C : ℂ) *
        (4 * (14 / 5 : ℂ) ^ 5 * (13 / 25) / (ρ * s) -
            4 *
              (∑ j ∈ Finset.range 5,
                (((5 : ℕ).choose (j + 1) : ℂ) * (14 / 5 : ℂ) ^ (5 - (j + 1))) *
                  (((j + 1).factorial : ℂ) / s ^ ((j + 1) + 1))) +
          (Real.exp (14 / 5) : ℂ) ^ s * (120 / s ^ 6)) := by
  intro s C
  have hw : (quarterWeight570 1 1 : ℂ) = (C : ℂ) * (14 / 5 : ℂ) ^ 5 := by
    rw [quarter_unit_weight_power zero_lt_one]
    dsimp only [C]
    simp only [Real.one_rpow, Real.log_one, sub_zero, one_mul, Complex.ofReal_mul,
      Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_ofNat]
  have hunit :
    section99Moment s 1 =
      (14 / 5 : ℂ) ^ 5 / s +
        ∑ j ∈ Finset.range 5,
          (((5 : ℕ).choose (j + 1) : ℂ) * (14 / 5 : ℂ) ^ (5 - (j + 1))) *
            (((j + 1).factorial : ℂ) / s ^ ((j + 1) + 1)) := by
    unfold section99Moment
    rw [Finset.sum_range_succ']
    simp only [Complex.ofReal_one, Complex.one_cpow, one_mul, Real.log_one, sub_zero,
      Complex.ofReal_div, Complex.ofReal_ofNat, Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero,
      Nat.factorial_zero, Nat.zero_add, pow_one, mul_one_div]
    rw [add_comm]
  dsimp only [section99PhaseKernel]
  change
    4 * (quarterWeight570 1 1 : ℂ) / ρ -
        (C : ℂ) * (4 * section99Moment s 1 - section99Moment s (Real.exp (14 / 5))) =
      _
  rw [hw, hunit, section99_moment_support]
  have he : (1 : ℂ) / ρ - 1 / s = (13 / 25) / (ρ * s) := by
    have hs' : s ≠ 0 := hs
    field_simp [hρ, hs']
    dsimp only [s]
    ring
  calc
    _ =
        (C : ℂ) *
          (4 * (14 / 5 : ℂ) ^ 5 * (1 / ρ - 1 / s) -
              4 *
                (∑ j ∈ Finset.range 5,
                  (((5 : ℕ).choose (j + 1) : ℂ) * (14 / 5 : ℂ) ^ (5 - (j + 1))) *
                    (((j + 1).factorial : ℂ) / s ^ ((j + 1) + 1))) +
            (Real.exp (14 / 5) : ℂ) ^ s * (120 / s ^ 6)) :=
      by ring
    _ = _ := by
      rw [he]; ring

/-- Bound the fixed phase kernel by a sum of reciprocal powers, exposing
the inverse-square decay needed for the high-zero tail. -/
theorem section99_phase_kernel_tail {ρ : ℂ} (hρ : ρ ≠ 0) (hs : ρ + (13 / 25 : ℂ) ≠ 0) :
    let s := ρ + (13 / 25 : ℂ)
    let C := (Real.exp (-(14 / 5 * (51 / 50))) / ((50 / 51) ^ 5 * 120) : ℝ)
    ‖section99PhaseKernel ρ‖ ≤
      C *
        ((4 * (14 / 5) ^ 5 * (13 / 25)) / (‖ρ‖ * ‖s‖) +
          4 *
            (∑ j ∈ Finset.range 5,
              (((5 : ℕ).choose (j + 1) : ℝ) * (14 / 5 : ℝ) ^ (5 - (j + 1))) *
                (((j + 1).factorial : ℝ) / ‖s‖ ^ ((j + 1) + 1))) +
          Real.exp ((14 / 5) * s.re) * (120 / ‖s‖ ^ 6)) := by
  intro s C
  let A := 4 * (14 / 5 : ℂ) ^ 5 * (13 / 25) / (ρ * s)
  let F := fun j : ℕ ↦
    (((5 : ℕ).choose (j + 1) : ℂ) * (14 / 5 : ℂ) ^ (5 - (j + 1))) *
      (((j + 1).factorial : ℂ) / s ^ ((j + 1) + 1))
  let D := (Real.exp (14 / 5) : ℂ) ^ s * (120 / s ^ 6)
  have he : section99PhaseKernel ρ = (C : ℂ) * (A - 4 * (∑ j ∈ Finset.range 5, F j) + D) :=
    section99_phase_kernel_expand hρ hs
  rw [he, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg
      (by
        dsimp only [C]; positivity)]
  apply
    mul_le_mul_of_nonneg_left _
      (by
        dsimp only [C]; positivity)
  have hfour : ‖(4 : ℂ)‖ = (4 : ℝ) := Complex.norm_ofNat _
  have h :
    ‖A - 4 * (∑ j ∈ Finset.range 5, F j) + D‖ ≤ ‖A‖ + 4 * (∑ j ∈ Finset.range 5, ‖F j‖) + ‖D‖ := by
    calc
      _ ≤ ‖A - 4 * (∑ j ∈ Finset.range 5, F j)‖ + ‖D‖ := norm_add_le _ _
      _ ≤ (‖A‖ + ‖(4 : ℂ) * (∑ j ∈ Finset.range 5, F j)‖) + ‖D‖ :=
        add_le_add_left (norm_sub_le _ _) _
      _ ≤ _ := by
        rw [norm_mul, hfour]
        exact
          add_le_add_left
            (add_le_add_right
              (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by norm_num only : (0 : ℝ) ≤ 4)) _)
            _
  apply h.trans
  have hD : ‖D‖ = Real.exp ((14 / 5) * s.re) * (120 / ‖s‖ ^ 6) := by
    dsimp only [D]
    rw [norm_mul, norm_div, norm_pow, Complex.norm_ofNat,
      Complex.norm_cpow_eq_rpow_re_of_pos (Real.exp_pos _), Real.rpow_def_of_pos (Real.exp_pos _),
      Real.log_exp]
  rw [hD]
  apply add_le_add_left
  have heA : ‖A‖ = (4 * (14 / 5 : ℝ) ^ 5 * (13 / 25)) / (‖ρ‖ * ‖s‖) := by
    simp only [A, norm_div, norm_mul, norm_pow, Complex.norm_ofNat]
  rw [heA]
  apply add_le_add_right
  apply le_of_eq
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp only [F, norm_mul, norm_div, norm_pow, Complex.norm_ofNat, Complex.norm_natCast]

/-- Numerator of the rational part of the phase kernel in Section 104.
Its argument is the effective Mellin exponent. -/
noncomputable def section104Numerator (s : ℂ) : ℂ :=
  -(17018288 / 78125) * s ^ 5 - (872592 / 3125) * s ^ 4 - (151312 / 625) * s ^ 3 -
      (11424 / 125) * s ^ 2 +
    (1368 / 25) * s +
    312 / 5

/-- The rational part of the phase kernel has the common denominator
from Section 104. Combining the terms preserves their cancellations. -/
theorem section99_phase_kernel_rational {ρ : ℂ} (hρ : ρ ≠ 0) (hs : ρ + (13 / 25 : ℂ) ≠ 0) :
    let s := ρ + (13 / 25 : ℂ)
    let C := (Real.exp (-(14 / 5 * (51 / 50))) / ((50 / 51) ^ 5 * 120) : ℝ)
    section99PhaseKernel ρ =
      (C : ℂ) *
        (4 * section104Numerator s / (ρ * s ^ 6) +
          (Real.exp (14 / 5) : ℂ) ^ s * (120 / s ^ 6)) := by
  intro s C
  rw [section99_phase_kernel_expand hρ hs]
  change (C : ℂ) * (_ - _ + _) = (C : ℂ) * (_ + _)
  congr 2
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, Nat.reduceSub,
    Nat.choose, Nat.factorial, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, zero_add,
    add_zero, pow_zero, pow_one, mul_one, one_mul, section104Numerator]
  dsimp only [s]
  field_simp [hρ, hs]
  apply congrArg (fun z : ℂ ↦ z / (ρ * 25 + 13) ^ 6)
  ring

/-- The squared modulus polynomial from Section 104, evaluated at the
squared ordinate of a zero. -/
noncomputable def section104NormPolynomial (z : ℝ) : ℝ :=
  (289622126450944 / 6103515625) * z ^ 5 + (262010390307638336 / 762939453125) * z ^ 4 +
    (541127807836464711968 / 476837158203125) * z ^ 3 +
    (691311736370338386621192 / 298023223876953125) * z ^ 2 +
    (555633899038052789188973049 / 186264514923095703125) * z +
    1404005148524444584781450458449 / 2328306436538696289062500

/-- Squaring the numerator norm on the effective critical line yields
the degree-five polynomial in the squared ordinate from Section 104. -/
theorem section104_numerator_normSq (t : ℝ) :
    Complex.normSq (section104Numerator (51 / 50 + (t : ℂ) * Complex.I)) =
      section104NormPolynomial (t ^ 2) := by
  unfold section104Numerator section104NormPolynomial
  rw [Complex.normSq_apply]
  simp only [← Complex.ofReal_ofNat, ← Complex.ofReal_div]
  set z : ℂ := ↑(51 / 50 : ℝ) + (t : ℂ) * Complex.I
  have hz : z.re = 51 / 50 ∧ z.im = t := by
    constructor <;>
      simp only [z, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero,
        add_zero, zero_add, sub_zero]
  simp only [pow_succ z 4, pow_succ z 3, pow_succ z 2, pow_succ z 1, pow_one, Complex.mul_re,
    Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.neg_re,
    Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, hz.1, hz.2, add_zero, neg_zero]
  ring

/-- The rational factor has squared modulus equal to the polynomial
divided by the exact critical-line denominator. -/
theorem section104_rational_norm_sq (t : ℝ) :
    let ρ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I
    let s := (51 / 50 : ℂ) + (t : ℂ) * Complex.I
    ‖section104Numerator s / (ρ * s ^ 6)‖ ^ 2 =
      section104NormPolynomial (t ^ 2) / ((t ^ 2 + 1 / 4) * (t ^ 2 + (51 / 50) ^ 2) ^ 6) := by
  intro ρ s
  have hn (a : ℝ) : Complex.normSq ((a : ℂ) + (t : ℂ) * Complex.I) = t ^ 2 + a ^ 2 := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero,
      zero_add, sub_zero]
    ring
  have hρ : Complex.normSq ρ = t ^ 2 + 1 / 4 := by
    dsimp only [ρ]
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_one, ← Complex.ofReal_div, hn]
    ring
  have hs : Complex.normSq s = t ^ 2 + (51 / 50) ^ 2 := by
    dsimp only [s]
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_ofNat, ← Complex.ofReal_div, hn]
  rw [norm_div, div_pow, norm_mul, mul_pow, norm_pow, show (‖s‖ ^ 6) ^ 2 = (‖s‖ ^ 2) ^ 6 by ring,
    Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, hρ, hs]
  exact congrArg (fun x : ℝ ↦ x / _) (section104_numerator_normSq t)

/-- On the critical line, bound the fixed kernel by the square-root
envelope of Section 104 and the norm of the sixth-power term. -/
theorem section104_phase_kernel_le (t : ℝ) :
    let ρ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I
    let C := (Real.exp (-(14 / 5 * (51 / 50))) / ((50 / 51) ^ 5 * 120) : ℝ)
    ‖section99PhaseKernel ρ‖ ≤
      C *
        (4 *
            Real.sqrt
              (section104NormPolynomial (t ^ 2) / ((t ^ 2 + 1 / 4) * (t ^ 2 + (51 / 50) ^ 2) ^ 6)) +
          Real.exp ((14 / 5) * (51 / 50)) * (120 / (t ^ 2 + (51 / 50) ^ 2) ^ 3)) := by
  intro ρ C
  let s := (51 / 50 : ℂ) + (t : ℂ) * Complex.I
  have he : ρ + (13 / 25 : ℂ) = s := by
    dsimp only [ρ, s]; ring
  have hre (a : ℝ) : ((a : ℂ) + (t : ℂ) * Complex.I).re = a := by
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hr : ρ.re = 1 / 2 := by
    dsimp only [ρ]
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_one, ← Complex.ofReal_div, hre]
  have hsr : s.re = 51 / 50 := by
    dsimp only [s]
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_ofNat, ← Complex.ofReal_div, hre]
  have hn (z : ℂ) (hz : 0 < z.re) : z ≠ 0 := by
    intro hz0
    rw [hz0, Complex.zero_re] at hz
    exact (lt_irrefl _ hz)
  have h :=
    section99_phase_kernel_rational (hn ρ (hr ▸ (by norm_num only : 0 < (1 / 2 : ℝ))))
      (by
        rw [he]; exact hn s (hsr ▸ (by norm_num only : 0 < (51 / 50 : ℝ))))
  dsimp only at h
  rw [he] at h
  change section99PhaseKernel ρ = (C : ℂ) * _ at h
  rw [h, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg
      (by
        dsimp only [C]; positivity)]
  apply
    mul_le_mul_of_nonneg_left _
      (by
        dsimp only [C]; positivity)
  rw [show (4 : ℂ) * section104Numerator s / (ρ * s ^ 6) = 4 * (section104Numerator s / (ρ * s ^ 6))
      by ring]
  refine (norm_add_le _ _).trans_eq ?_
  rw [norm_mul, Complex.norm_ofNat]
  have hnum := section104_rational_norm_sq t
  dsimp only at hnum
  change ‖section104Numerator s / (ρ * s ^ 6)‖ ^ 2 = _ at hnum
  rw [← hnum, Real.sqrt_sq (norm_nonneg _)]
  have hs : ‖s‖ ^ 2 = t ^ 2 + (51 / 50) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hsr]
    have hi : s.im = t := by
      dsimp only [s]
      rw [← Complex.ofReal_ofNat, ← Complex.ofReal_ofNat, ← Complex.ofReal_div]
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, mul_one, mul_zero, add_zero, zero_add]
    rw [hi]
    ring
  have ht : ‖(120 : ℂ) / s ^ 6‖ = 120 / (t ^ 2 + (51 / 50) ^ 2) ^ 3 := by
    rw [norm_div, norm_pow, Complex.norm_ofNat, show (‖s‖ ^ 6) = (‖s‖ ^ 2) ^ 3 by ring, hs]
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (Real.exp_pos _),
    Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, hsr, ht]

/-- The exponential normalization cancels the exponential in the
full-support norm bound, leaving the rational coefficient of Section 104. -/
theorem section104_phase_kernel_envelope (t : ℝ) :
    let ρ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I
    let C := (Real.exp (-(14 / 5 * (51 / 50))) / ((50 / 51) ^ 5 * 120) : ℝ)
    ‖section99PhaseKernel ρ‖ ≤
      4 * C *
          Real.sqrt
            (section104NormPolynomial (t ^ 2) / ((t ^ 2 + 1 / 4) * (t ^ 2 + (51 / 50) ^ 2) ^ 6)) +
        (51 / 50) ^ 5 / (t ^ 2 + (51 / 50) ^ 2) ^ 3 := by
  intro ρ C
  have h := section104_phase_kernel_le t
  dsimp only at h
  have hC : C * Real.exp ((14 / 5) * (51 / 50)) = (51 / 50) ^ 5 / 120 := by
    dsimp only [C]
    rw [Real.exp_neg, div_mul_eq_mul_div, inv_mul_cancel₀ (Real.exp_pos _).ne']
    norm_num only
  change ‖section99PhaseKernel ρ‖ ≤ _
  refine h.trans_eq ?_
  change C * (_ + _ * _) = _
  rw [mul_add, ← mul_assoc C (Real.exp ((14 / 5) * (51 / 50))), hC]
  ring

/-- The largest monomial divided by the critical-line denominator is
decreasing for squared ordinates at least 196. -/
private theorem section104_top_ratio_antitone :
    AntitoneOn (fun z : ℝ ↦ z ^ 5 / ((z + 1 / 4) * (z + (51 / 50) ^ 2) ^ 6)) (Set.Ici 196) := by
  let a : ℝ := (51 / 50) ^ 2
  let d := fun z : ℝ ↦ (z + 1 / 4) * (z + a) ^ 6
  have hd (z : ℝ) (hz : 196 ≤ z) : 0 < d z :=
    mul_pos (by linarith only [hz])
      (pow_pos
        (by
          dsimp only [a]; linarith only [hz])
        _)
  have hder (z : ℝ) (hz : 196 ≤ z) :
    HasDerivAt (fun u ↦ u ^ 5 / d u)
      ((z ^ 4 * (z + a) ^ 5 * (-2 * z ^ 2 + (4 * a - 1 / 4) * z + 5 / 4 * a)) / (d z) ^ 2) z := by
    have h :=
      ((hasDerivAt_id z).pow 5).div
        (((hasDerivAt_id z).add_const (1 / 4 : ℝ)).mul (((hasDerivAt_id z).add_const a).pow 6))
        (hd z hz).ne'
    convert h using 1
    · rfl
    · simp only [Pi.pow_apply, Pi.mul_apply, id_eq, d]
      apply congrArg (fun u : ℝ ↦ u / ((z + 1 / 4) * (z + a) ^ 6) ^ 2)
      norm_num only [Nat.cast_ofNat, Nat.reduceSub, mul_one]
      ring
  change AntitoneOn (fun z ↦ z ^ 5 / d z) _
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · exact fun z hz ↦ (hder z hz).continuousAt.continuousWithinAt
  · exact fun z hz ↦ (hder z (interior_subset hz)).differentiableAt.differentiableWithinAt
  · intro z hz
    have hz' : (196 : ℝ) ≤ z := interior_subset hz
    rw [(hder z hz').deriv]
    apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
    apply
      mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (pow_nonneg (by linarith only [hz']) _)
          (pow_nonneg
            (by
              dsimp only [a]; linarith only [hz'])
            _))
    have hz2 := mul_nonneg (sub_nonneg.mpr hz') (show 0 ≤ z by linarith only [hz'])
    dsimp only [a]
    nlinarith only [hz', hz2]

/-- The squared envelope is decreasing on the entire ordinate range of
the certified low zeros. Each monomial reduces to the top ratio divided
by a nondecreasing positive power. -/
theorem section104_ratio_antitone :
    AntitoneOn (fun z : ℝ ↦ section104NormPolynomial z / ((z + 1 / 4) * (z + (51 / 50) ^ 2) ^ 6))
      (Set.Ici 196) := by
  intro x hx y hy hxy
  let d := fun z : ℝ ↦ (z + 1 / 4) * (z + (51 / 50) ^ 2) ^ 6
  have hx0 : 0 < x := by linarith only [show 196 ≤ x from hx]
  have hy0 := hx0.trans_le hxy
  have he (z : ℝ) (hz : 0 < z) (j : ℕ) (hj : j ≤ 5) :
    z ^ j / d z = (z ^ 5 / d z) / z ^ (5 - j) := by
    have hp : z ^ 5 = z ^ j * z ^ (5 - j) := by rw [← pow_add, Nat.add_sub_of_le hj]
    rw [hp, mul_div_right_comm, mul_div_cancel_right₀ _ (pow_pos hz _).ne']
  have h₅ : x ^ 5 / d x ≥ y ^ 5 / d y := section104_top_ratio_antitone hx hy hxy
  have hk (j : ℕ) (hj : j ≤ 5) : y ^ j / d y ≤ x ^ j / d x := by
    rw [he x hx0 j hj, he y hy0 j hj]
    have hp : 0 ≤ x ^ 5 / d x := by
      dsimp only [d]; positivity
    exact div_le_div₀ hp h₅ (pow_pos hx0 _) (pow_le_pow_left₀ hx0.le hxy _)
  change section104NormPolynomial y / d y ≤ section104NormPolynomial x / d x
  unfold section104NormPolynomial
  have h₄ := hk 4 (by decide)
  have h₃ := hk 3 (by decide)
  have h₂ := hk 2 (by decide)
  have h₁ := hk 1 (by decide)
  have h₀ := hk 0 (by decide)
  simp only [pow_one, pow_zero] at h₁ h₀
  simp only [add_div, mul_div_assoc]
  have hc (z : ℝ) :
    (1404005148524444584781450458449 / 2328306436538696289062500) / d z =
      (1404005148524444584781450458449 / 2328306436538696289062500) * (1 / d z) := by
    ring
  rw [hc x, hc y]
  linarith only [h₅, h₄, h₃, h₂, h₁, h₀]

/-- A certified lower endpoint at least fourteen gives a uniform bound on
the fixed kernel when the absolute ordinate is at least that endpoint. -/
theorem section104_kernel_le_abs_endpoint {l t : ℝ} (hl : 14 ≤ l) (hlt : l ≤ |t|) :
    let C := (Real.exp (-(14 / 5 * (51 / 50))) / ((50 / 51) ^ 5 * 120) : ℝ)
    ‖section99PhaseKernel ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      4 * C *
          Real.sqrt
            (section104NormPolynomial (l ^ 2) / ((l ^ 2 + 1 / 4) * (l ^ 2 + (51 / 50) ^ 2) ^ 6)) +
        (51 / 50) ^ 5 / (l ^ 2 + (51 / 50) ^ 2) ^ 3 := by
  intro C
  have hl0 : 0 ≤ l := by linarith only [hl]
  have hll : (196 : ℝ) ≤ l ^ 2 := by
    exact (by norm_num only : (196 : ℝ) = 14 ^ 2) ▸ pow_le_pow_left₀ (by norm_num only) hl 2
  have hlt2 : l ^ 2 ≤ t ^ 2 := by
    rw [← sq_abs t]
    exact pow_le_pow_left₀ hl0 hlt 2
  apply (section104_phase_kernel_envelope t).trans
  apply add_le_add
  · exact
      mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (section104_ratio_antitone hll (hll.trans hlt2) hlt2)) (by positivity)
  · apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact pow_le_pow_left₀ (by positivity) (add_le_add_left hlt2 _) _

/-- A certified lower endpoint at least fourteen gives a uniform bound on
the fixed kernel at every greater ordinate. -/
theorem section104_kernel_le_endpoint {l t : ℝ} (hl : 14 ≤ l) (hlt : l ≤ t) :
    let C := (Real.exp (-(14 / 5 * (51 / 50))) / ((50 / 51) ^ 5 * 120) : ℝ)
    ‖section99PhaseKernel ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      4 * C *
          Real.sqrt
            (section104NormPolynomial (l ^ 2) / ((l ^ 2 + 1 / 4) * (l ^ 2 + (51 / 50) ^ 2) ^ 6)) +
        (51 / 50) ^ 5 / (l ^ 2 + (51 / 50) ^ 2) ^ 3 := by
  exact section104_kernel_le_abs_endpoint hl (hlt.trans (le_abs_self t))

/-- Above height one hundred, the numerator polynomial is bounded by
220 squared times the fifth power of the squared ordinate. -/
theorem section104_poly_tail {z : ℝ} (hz : 10000 ≤ z) :
    section104NormPolynomial z ≤ (220 : ℝ) ^ 2 * z ^ 5 := by
  have hz0 : 0 ≤ z := by linarith only [hz]
  have hp (j : ℕ) (hj : j ≤ 5) : z ^ j * (10000 : ℝ) ^ (5 - j) ≤ z ^ 5 := by
    rw [show z ^ 5 = z ^ j * z ^ (5 - j) by rw [← pow_add, Nat.add_sub_of_le hj]]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num only) hz _) (pow_nonneg hz0 _)
  have h₀ := hp 0 (by decide)
  have h₁ := hp 1 (by decide)
  have h₂ := hp 2 (by decide)
  have h₃ := hp 3 (by decide)
  have h₄ := hp 4 (by decide)
  norm_num only [pow_zero, pow_one, Nat.reduceSub, one_mul] at h₀ h₁ h₂ h₃ h₄
  unfold section104NormPolynomial
  linarith only [h₀, h₁, h₂, h₃, h₄, pow_nonneg hz0 5]

/-- Above height one hundred, the rational envelope is bounded by
220 divided by the squared ordinate. -/
theorem section104_sqrt_tail {z : ℝ} (hz : 10000 ≤ z) :
    Real.sqrt (section104NormPolynomial z / ((z + 1 / 4) * (z + (51 / 50) ^ 2) ^ 6)) ≤ 220 / z := by
  have hz0 : 0 < z := by linarith only [hz]
  have hd : z ^ 7 ≤ (z + 1 / 4) * (z + (51 / 50) ^ 2) ^ 6 := by
    rw [show z ^ 7 = z * z ^ 6 by ring]
    exact
      mul_le_mul (le_add_of_nonneg_right (by norm_num only))
        (pow_le_pow_left₀ hz0.le (le_add_of_nonneg_right (sq_nonneg _)) _) (pow_nonneg hz0.le _)
        (by positivity)
  have hp : 0 ≤ (220 : ℝ) ^ 2 * z ^ 5 := by positivity
  have h := div_le_div₀ hp (section104_poly_tail hz) (pow_pos hz0 7) hd
  have he : (220 : ℝ) ^ 2 * z ^ 5 / z ^ 7 = (220 / z) ^ 2 := by field_simp [hz0.ne']
  rw [he] at h
  exact (Real.sqrt_le_sqrt h).trans_eq (Real.sqrt_sq (div_nonneg (by norm_num only) hz0.le))

/-- A rational upper bound for the normalization in the Section 104 kernel.
A finite exponential series at the positive argument certifies the bound. -/
theorem section104_norm_constant_le :
    Real.exp (-(14 / 5 * (51 / 50))) / ((50 / 51) ^ 5 * 120) ≤ (53 / 100000 : ℝ) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 14 / 5 * (51 / 50)) 11
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_one,
    Nat.cast_ofNat, Nat.reduceMul, Nat.reduceSub] at h
  have he : (17388 / 1000 : ℝ) ≤ Real.exp (14 / 5 * (51 / 50)) := by linarith only [h]
  rw [Real.exp_neg, inv_eq_one_div]
  apply (div_le_iff₀ (by norm_num only : (0 : ℝ) < (50 / 51) ^ 5 * 120)).2
  exact (div_le_div_of_nonneg_left zero_le_one (by norm_num only) he).trans (by norm_num only)

/-- For either sign of the ordinate, the fixed phase kernel above height
one hundred is bounded by 0.467 divided by the squared ordinate. -/
theorem section104_kernel_high {t : ℝ} (ht : 100 ≤ |t|) :
    ‖section99PhaseKernel ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 0.467 / t ^ 2 := by
  let z := t ^ 2
  have hz : 10000 ≤ z := by
    dsimp only [z]
    rw [← sq_abs]
    exact (by norm_num only : (10000 : ℝ) = 100 ^ 2) ▸ pow_le_pow_left₀ (by norm_num only) ht 2
  have hz0 : 0 < z := by linarith only [hz]
  have hb := section104_phase_kernel_envelope t
  dsimp only at hb
  apply hb.trans
  change
    _ * Real.sqrt (section104NormPolynomial z / ((z + 1 / 4) * (z + (51 / 50) ^ 2) ^ 6)) +
        (51 / 50) ^ 5 / (z + (51 / 50) ^ 2) ^ 3 ≤
      _
  have h₁ :=
    mul_le_mul (mul_le_mul_of_nonneg_left section104_norm_constant_le (by norm_num only))
      (section104_sqrt_tail hz) (Real.sqrt_nonneg _)
      (by norm_num only : (0 : ℝ) ≤ 4 * (53 / 100000))
  have h₂ : (51 / 50) ^ 5 / (z + (51 / 50) ^ 2) ^ 3 ≤ 0.0006 / z := by
    apply
      (div_le_div_of_nonneg_left (by norm_num only) (pow_pos hz0 3)
          (pow_le_pow_left₀ hz0.le (le_add_of_nonneg_right (sq_nonneg _)) 3)).trans
    apply (div_le_div_iff₀ (pow_pos hz0 3) hz0).2
    have hsq := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 10000) hz 2
    have hc : (51 / 50 : ℝ) ^ 5 ≤ 0.0006 * z ^ 2 := by linarith only [hsq]
    have h := mul_le_mul_of_nonneg_right hc hz0.le
    linarith only [show (51 / 50 : ℝ) ^ 5 * z ≤ 0.0006 * z ^ 3 by
        simpa only [mul_assoc, ← pow_succ] using h]
  change _ ≤ 0.467 / z
  exact (add_le_add h₁ h₂).trans_eq (by ring)

end PseudoPrime.PrimeTestBounds.MillerRabin
