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
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterGammaFirstNumerics
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFiniteCell
import PseudoPrime.Analysis.LogTaylorBounds
import PseudoPrime.AnalyticNumberTheory.Arithmetic.TruncatedEulerCertificates3
import PseudoPrime.Analysis.NumericalLogBounds

/-! # Uniform witnesses from the certified principal lower bound -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem upper_cell {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r b R H J : ℝ} (hr : 268 ≤ r)
    (hb : r ≤ b) (hb' : b ≤ 278) (hlog : Real.log n = 2 * r) (hR : quarterReflectedScale r ≤ R)
    (hH : quarterMomentScale r ≤ H) (hJ : quarterEulerClosedTailCap (r ^ 2) ≤ J)
    (hc :
      (3181 / 100000) * b + (4 * b + 3 * (1839 / 1000)) * R + H + 4 * J + -(21 / 250) +
                4 * (89611 / 1000000) * (1 / 3) -
              236 / 100000 +
            62 / 1000 -
          3 * (26 / 1000) ≤
        (3117 / 400) * (27 / 25) ^ 5) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hr0 : 0 < r := (by norm_num only : (0 : ℝ) < 268).trans_le hr
  have hx : 625 ≤ r ^ 2 :=
    (by norm_num only : (625 : ℝ) ≤ (268) ^ 2).trans (pow_le_pow_left₀ (by norm_num only) hr 2)
  have href :=
    quarter_reflected_of_moments (by linarith only [hx] : 1 ≤ r ^ 2)
      (quarter_moment_bounds_of_integrals hGRH.riemann quarter_moment_integral_bounds)
  have hl := square_principal_268_278 hr (hb.trans hb') hGRH.riemann
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
  have hlow :=
    (Analysis.rationalLogIntervalCheck_sound (N := 71824) (j := 16) (n := 32) (lo := 11) (hi := 12)
        (by decide +kernel)).1
  have hhigh :=
    (Analysis.rationalLogIntervalCheck_sound (N := 77284) (j := 16) (n := 32) (lo := 11) (hi :=
        113 / 10) (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlow hhigh
  have hlo :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 71824)
      (show (71824 : ℝ) ≤ r ^ 2 by nlinarith only [hr])
  have hhi :=
    Real.log_le_log (sq_pos_of_pos hr0)
      (show r ^ 2 ≤ (77284 : ℝ) by nlinarith only [pow_le_pow_left₀ hr0.le (hb.trans hb') 2])
  have hg :=
    quarter_first_correction_13_14 (z := Real.log (r ^ 2) + 21 / 8) (by linarith only [hlow, hlo])
      (by linarith only [hhigh, hhi])
  have hy := quarter_shift_log_ge_twelve (by linarith only [hr] : 180 ≤ r)
  have hz : 0 ≤ Real.log (r ^ 2) + 21 / 8 := by linarith only [hy]
  have hd : 0 ≤ quarterGammaDensity (Real.log (r ^ 2) + 21 / 8) := by
    rw [quarterGammaDensity, ite_eq_left hz]
    positivity
  obtain ⟨p, hp, hw, hf⟩ :=
    square_uniform_witness hn ho hu hGRH (by linarith only [hr]) (hb.trans hb') rfl hx hy
      (href.trans hH) ∅ (fun k hk ↦ False.elim (Finset.notMem_empty k hk))
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
    (hlo : 268 ≤ r) (ha : 1 ≤ a) (har : a ≤ r) (hrb : r ≤ b) (hb : b ≤ 278)
    (hlog : Real.log n = 2 * r) (hl : Real.log (b ^ 2) ≤ L) (hP : (a ^ 2) ^ (-(27 / 25 : ℝ)) ≤ P)
    (hQ : (a ^ 2) ^ (-(29 / 50 : ℝ)) ≤ Q) (hV : (a ^ 2) ^ (-(83 / 100 : ℝ)) ≤ V)
    (hc :
      let c := (27 / 25 : ℝ) ^ 5 / 120 * (58721 / 1000000) * P
          let z := 21 / 8 + L
          3181 / 100000 * b + (4 * b + 3 * (1839 / 1000)) * (c * z ^ 5) +
                c * quarterMomentPolynomial z +
                4 * quarterEulerClosedUpper L Q V +
                -(21 / 250) +
                4 * (89611 / 1000000) * (1 / 3) -
              236 / 100000 +
            62 / 1000 -
          3 * (26 / 1000) ≤
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
  exact upper_cell hn ho hu hGRH hlo hrb hb hlog hru.1 hru.2 hju hc

/-- Square recovery supplies a rejecting prime at radii between 270 and 274. -/
theorem square_radius_270_274 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r : ℝ} (hl : 270 ≤ r)
    (hh : r ≤ 274) (he : Real.log n = 2 * r) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    checked_radius hn ho hu hGRH (L := (1122627 / 100000)) (P := (56010 / 10000000000)) (Q :=
      (15122308 / 10000000000)) (V := (920316 / 10000000000)) (by linarith only [hl])
      (by norm_num only) hl hh (by norm_num only) he
  · have h :=
      (Analysis.rationalLogIntervalCheck_sound (N := 75076) (j := 16) (n := 32) (lo := 0) (hi :=
          (1122627 / 100000)) (by decide +kernel)).2
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at h ⊢
    exact h
  · have h :=
      (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 72900) (p := 27) (d :=
          25) (lo := 0) (hi := (56010 / 10000000000)) (by decide +kernel)).2
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at h ⊢
    exact h
  · have h :=
      (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 72900) (p := 29) (d :=
          50) (lo := 0) (hi := (15122308 / 10000000000)) (by decide +kernel)).2
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at h ⊢
    exact h
  · have h :=
      (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 72900) (p := 83) (d :=
          100) (lo := 0) (hi := (920316 / 10000000000)) (by decide +kernel)).2
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at h ⊢
    exact h
  · norm_num only [quarterMomentPolynomial, quarterEulerClosedUpper, quarterMomentClosedUpper,
      Analysis.logPowerTailPoly]

/-- Square recovery supplies a rejecting prime at radii between 274 and 276. -/
theorem square_radius_274_276 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r : ℝ} (hl : 274 ≤ r)
    (hh : r ≤ 276) (he : Real.log n = 2 * r) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    checked_radius hn ho hu hGRH (L := (1124082 / 100000)) (P := (54259 / 10000000000)) (Q :=
      (14866522 / 10000000000)) (V := (898121 / 10000000000)) (by linarith only [hl])
      (by norm_num only) hl hh (by norm_num only) he
  · have h :=
      (Analysis.rationalLogIntervalCheck_sound (N := 76176) (j := 16) (n := 32) (lo := 0) (hi :=
          (1124082 / 100000)) (by decide +kernel)).2
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at h ⊢
    exact h
  · have h :=
      (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 75076) (p := 27) (d :=
          25) (lo := 0) (hi := (54259 / 10000000000)) (by decide +kernel)).2
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at h ⊢
    exact h
  · have h :=
      (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 75076) (p := 29) (d :=
          50) (lo := 0) (hi := (14866522 / 10000000000)) (by decide +kernel)).2
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at h ⊢
    exact h
  · have h :=
      (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 75076) (p := 83) (d :=
          100) (lo := 0) (hi := (898121 / 10000000000)) (by decide +kernel)).2
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at h ⊢
    exact h
  · norm_num only [quarterMomentPolynomial, quarterEulerClosedUpper, quarterMomentClosedUpper,
      Analysis.logPowerTailPoly]

/-- Square recovery supplies a rejecting prime at radii between 276 and 277. -/
theorem square_radius_276_277 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r : ℝ} (hl : 276 ≤ r)
    (hh : r ≤ 277) (he : Real.log n = 2 * r) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    checked_radius hn ho hu hGRH (L := (1124805 / 100000)) (P := (53413 / 10000000000)) (Q :=
      (14741630 / 10000000000)) (V := (887343 / 10000000000)) (by linarith only [hl])
      (by norm_num only) hl hh (by norm_num only) he
  · have h :=
      (Analysis.rationalLogIntervalCheck_sound (N := 76729) (j := 16) (n := 32) (lo := 0) (hi :=
          (1124805 / 100000)) (by decide +kernel)).2
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at h ⊢
    exact h
  · have h :=
      (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 76176) (p := 27) (d :=
          25) (lo := 0) (hi := (53413 / 10000000000)) (by decide +kernel)).2
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at h ⊢
    exact h
  · have h :=
      (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 76176) (p := 29) (d :=
          50) (lo := 0) (hi := (14741630 / 10000000000)) (by decide +kernel)).2
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at h ⊢
    exact h
  · have h :=
      (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 76176) (p := 83) (d :=
          100) (lo := 0) (hi := (887343 / 10000000000)) (by decide +kernel)).2
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at h ⊢
    exact h
  · norm_num only [quarterMomentPolynomial, quarterEulerClosedUpper, quarterMomentClosedUpper,
      Analysis.logPowerTailPoly]

/-- Square recovery supplies a rejecting prime at radii between 277 and 278. -/
theorem square_radius_277_278 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r : ℝ} (hl : 277 ≤ r)
    (hh : r ≤ 278) (he : Real.log n = 2 * r) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    checked_radius hn ho hu hGRH (L := (1125526 / 100000)) (P := (52998 / 10000000000)) (Q :=
      (14679914 / 10000000000)) (V := (882032 / 10000000000)) (by linarith only [hl])
      (by norm_num only) hl hh (by norm_num only) he
  · have h :=
      (Analysis.rationalLogIntervalCheck_sound (N := 77284) (j := 16) (n := 32) (lo := 0) (hi :=
          (1125526 / 100000)) (by decide +kernel)).2
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at h ⊢
    exact h
  · have h :=
      (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 76729) (p := 27) (d :=
          25) (lo := 0) (hi := (52998 / 10000000000)) (by decide +kernel)).2
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at h ⊢
    exact h
  · have h :=
      (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 76729) (p := 29) (d :=
          50) (lo := 0) (hi := (14679914 / 10000000000)) (by decide +kernel)).2
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at h ⊢
    exact h
  · have h :=
      (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 76729) (p := 83) (d :=
          100) (lo := 0) (hi := (882032 / 10000000000)) (by decide +kernel)).2
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at h ⊢
    exact h
  · norm_num only [quarterMomentPolynomial, quarterEulerClosedUpper, quarterMomentClosedUpper,
      Analysis.logPowerTailPoly]

/-- Square recovery extends the uniform quarter-square rejecting bound from log 540 to 556. -/
theorem quarter_uniform_540_556 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (ha : 540 ≤ Real.log n)
    (hb : Real.log n ≤ 556) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let r := Real.log n / 2
  have he : Real.log n = 2 * r := by
    dsimp only [r]; ring
  by_cases h1 : r ≤ 274
  · exact square_radius_270_274 hn ho hu hGRH (by linarith only [ha, he]) h1 he
  by_cases h2 : r ≤ 276
  · exact square_radius_274_276 hn ho hu hGRH (le_of_not_ge h1) h2 he
  by_cases h3 : r ≤ 277
  · exact square_radius_276_277 hn ho hu hGRH (le_of_not_ge h2) h3 he
  exact square_radius_277_278 hn ho hu hGRH (le_of_not_ge h3) (by linarith only [he, hb]) he

end PseudoPrime.PrimeTestBounds.MillerRabin
