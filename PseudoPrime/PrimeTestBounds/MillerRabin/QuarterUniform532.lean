/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.SquarePrincipalLower
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformFiniteBudget
import PseudoPrime.PrimeTestBounds.MillerRabin.SquareRecoveryGap
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformClosedNegative
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFiniteCell
import PseudoPrime.Analysis.LogTaylorBounds
import PseudoPrime.AnalyticNumberTheory.Arithmetic.TruncatedEulerCertificates3
import PseudoPrime.Analysis.NumericalLogBounds

/-! # Uniform witnesses from the certified principal lower bound -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- On a cell of the recovery extension, rational upper bounds for the
conductor, reflected moment and Euler tail imply a rejecting prime when the
endpoint budget is nonnegative. The finite psi lower bound supplies the
principal side without a spectral certificate. -/
theorem square_recovery_cell {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r b R H J : ℝ}
    (hr : 465 / 2 ≤ r) (hb : r ≤ b) (hb' : b ≤ 278) (hlog : Real.log n = 2 * r)
    (hR : quarterReflectedScale r ≤ R) (hH : quarterMomentScale r ≤ H)
    (hJ : quarterEulerClosedTailCap (r ^ 2) ≤ J)
    (hc :
      (3181 / 100000) * b + (4 * b + 3 * (1839 / 1000)) * R + H + 4 * J + -(21 / 250) +
              4 * (89611 / 1000000) * (4 / 5) -
            236 / 100000 +
          283 / 10000 ≤
        (3117 / 400) * (27 / 25) ^ 5) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hr0 : 0 < r := (by norm_num only : (0 : ℝ) < 465 / 2).trans_le hr
  have hx : 625 ≤ r ^ 2 :=
    (by norm_num only : (625 : ℝ) ≤ (465 / 2) ^ 2).trans (pow_le_pow_left₀ (by norm_num only) hr 2)
  have href :=
    quarter_reflected_of_moments (by linarith only [hx] : 1 ≤ r ^ 2)
      (quarter_moment_bounds_of_integrals hGRH.riemann quarter_moment_integral_bounds)
  have hl := square_principal_of_psi70 hr (hb.trans hb') hGRH.riemann
  dsimp only at hl
  rw [mul_div_assoc, quarter_reflected_scale_eq hr0] at hl
  have hscale : 0 ≤ quarterReflectedScale r := by
    unfold quarterReflectedScale
    have hz := Real.log_nonneg (by linarith only [hx] : 1 ≤ r ^ 2)
    positivity
  have hprod :=
    mul_le_mul
      (show 4 * r + 3 * Real.log (2 * Real.pi) ≤ 4 * b + 3 * (1839 / 1000) by
        linarith only [hb, Analysis.log_two_mul_pi_lt])
      hR hscale (by linarith only [hr, hb])
  have hg :=
    quarter_gamma_first_nonneg (z := Real.log (r ^ 2) + 21 / 8)
      (by linarith only [Real.log_nonneg (by linarith only [hx] : 1 ≤ r ^ 2)])
  have hy := quarter_shift_log_ge_twelve (by linarith only [hr] : 180 ≤ r)
  have hz : 0 ≤ Real.log (r ^ 2) + 21 / 8 := by linarith only [hy]
  have hd : 0 ≤ quarterGammaDensity (Real.log (r ^ 2) + 21 / 8) := by
    rw [quarterGammaDensity, ite_eq_left hz]
    positivity
  obtain ⟨p, hp, hw, hf⟩ :=
    square_uniform_witness hn ho hu hGRH hr (hb.trans hb') rfl hx hy (href.trans hH) ∅
      (fun k hk ↦ False.elim (Finset.notMem_empty k hk))
      (by
        simp only [Finset.sum_empty, mul_zero, sub_zero]
        rw [hlog]
        unfold quarterReflectedScale at hprod hl
        linarith only [hl, hc, hprod, hb, hJ, hg, hd])
  exact
    ⟨p, hp,
      hw.trans
        (by
          rw [hlog]; ring_nf; exact le_rfl),
      hf⟩

private theorem checked_radius {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r a b L P Q V : ℝ}
    (hlo : 465 / 2 ≤ r) (ha : 1 ≤ a) (har : a ≤ r) (hrb : r ≤ b) (hb : b ≤ 278)
    (hlog : Real.log n = 2 * r) (hl : Real.log (b ^ 2) ≤ L) (hP : (a ^ 2) ^ (-(27 / 25 : ℝ)) ≤ P)
    (hQ : (a ^ 2) ^ (-(29 / 50 : ℝ)) ≤ Q) (hV : (a ^ 2) ^ (-(83 / 100 : ℝ)) ≤ V)
    (hc :
      let c := (27 / 25 : ℝ) ^ 5 / 120 * (58721 / 1000000) * P
          let z := 21 / 8 + L
          3181 / 100000 * b + (4 * b + 3 * (1839 / 1000)) * (c * z ^ 5) +
              c * quarterMomentPolynomial z +
              4 * quarterEulerClosedUpper L Q V +
              -(21 / 250) +
              4 * (89611 / 1000000) * (4 / 5) -
            236 / 100000 +
          283 / 10000 ≤
        (3117 / 400 : ℝ) * (27 / 25) ^ 5) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have ha0 : 0 < a := by linarith only [ha]
  have hr : 1 ≤ r := ha.trans har
  have hmin : a ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (by linarith only [ha]) har 2
  have hmax : r ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ (by linarith only [hr]) hrb 2
  have hlogr := (Real.log_le_log (sq_pos_of_pos (by linarith only [hr])) hmax).trans hl
  have hp :=
    (Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos ha0) hmin
          (by norm_num only : (-(27 / 25 : ℝ)) ≤ 0)).trans
      hP
  have hq :=
    (Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos ha0) hmin
          (by norm_num only : (-(29 / 50 : ℝ)) ≤ 0)).trans
      hQ
  have hv :=
    (Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos ha0) hmin
          (by norm_num only : (-(83 / 100 : ℝ)) ≤ 0)).trans
      hV
  have hq0 : 0 ≤ Q := (Real.rpow_nonneg (sq_nonneg r) _).trans hq
  have hv0 : 0 ≤ V := (Real.rpow_nonneg (sq_nonneg r) _).trans hv
  have hru := quarter_finite_reflected_upper hr hlogr hp
  have hju :=
    quarter_euler_closed_upper (show (1 : ℝ) ≤ r ^ 2 by nlinarith only [hr]) hlogr hq0 hv0 hq hv
  exact square_recovery_cell hn ho hu hGRH hlo hrb hb hlog hru.1 hru.2 hju hc

/-- Square recovery supplies a rejecting prime at radii between 266 and 268. -/
theorem square_radius_266_268 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r : ℝ} (hl : 266 ≤ r)
    (hh : r ≤ 268) (he : Real.log n = 2 * r) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    checked_radius hn ho hu hGRH (L := (1118199 / 100000)) (P := (57845 / 10000000000)) (Q :=
      (15386412 / 10000000000)) (V := (943403 / 10000000000)) (by linarith only [hl])
      (by norm_num only) hl hh (by norm_num only) he
  · have h :=
      (Analysis.rationalLogIntervalCheck_sound (N := 71824) (j := 16) (n := 32) (lo := 0) (hi :=
          (1118199 / 100000)) (by decide +kernel)).2
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at h ⊢
    exact h
  · have h :=
      (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 70756) (p := 27) (d :=
          25) (lo := 0) (hi := (57845 / 10000000000)) (by decide +kernel)).2
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at h ⊢
    exact h
  · have h :=
      (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 70756) (p := 29) (d :=
          50) (lo := 0) (hi := (15386412 / 10000000000)) (by decide +kernel)).2
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at h ⊢
    exact h
  · have h :=
      (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 70756) (p := 83) (d :=
          100) (lo := 0) (hi := (943403 / 10000000000)) (by decide +kernel)).2
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at h ⊢
    exact h
  · norm_num only [quarterMomentPolynomial, quarterEulerClosedUpper, quarterMomentClosedUpper,
      Analysis.logPowerTailPoly]

/-- Square recovery supplies a rejecting prime at radii between 268 and 270. -/
theorem square_radius_268_270 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r : ℝ} (hl : 268 ≤ r)
    (hh : r ≤ 270) (he : Real.log n = 2 * r) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    checked_radius hn ho hu hGRH (L := (1119686 / 100000)) (P := (56917 / 10000000000)) (Q :=
      (15253295 / 10000000000)) (V := (931745 / 10000000000)) (by linarith only [hl])
      (by norm_num only) hl hh (by norm_num only) he
  · have h :=
      (Analysis.rationalLogIntervalCheck_sound (N := 72900) (j := 16) (n := 32) (lo := 0) (hi :=
          (1119686 / 100000)) (by decide +kernel)).2
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at h ⊢
    exact h
  · have h :=
      (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 71824) (p := 27) (d :=
          25) (lo := 0) (hi := (56917 / 10000000000)) (by decide +kernel)).2
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at h ⊢
    exact h
  · have h :=
      (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 71824) (p := 29) (d :=
          50) (lo := 0) (hi := (15253295 / 10000000000)) (by decide +kernel)).2
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at h ⊢
    exact h
  · have h :=
      (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 71824) (p := 83) (d :=
          100) (lo := 0) (hi := (931745 / 10000000000)) (by decide +kernel)).2
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at h ⊢
    exact h
  · norm_num only [quarterMomentPolynomial, quarterEulerClosedUpper, quarterMomentClosedUpper,
      Analysis.logPowerTailPoly]

/-- Square recovery extends the uniform quarter-square rejecting bound from log 532 to 540. -/
theorem quarter_uniform_532_540 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (ha : 532 ≤ Real.log n)
    (hb : Real.log n ≤ 540) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let r := Real.log n / 2
  have he : Real.log n = 2 * r := by
    dsimp only [r]; ring
  by_cases hm : r ≤ 268
  · exact square_radius_266_268 hn ho hu hGRH (by linarith only [ha, he]) hm he
  exact square_radius_268_270 hn ho hu hGRH (le_of_not_ge hm) (by linarith only [he, hb]) he

end PseudoPrime.PrimeTestBounds.MillerRabin
