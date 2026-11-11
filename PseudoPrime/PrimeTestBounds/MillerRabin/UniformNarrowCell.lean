/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.UniformNarrowScalar
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFiniteMajorant
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerTailInterval

/-! # Endpoint-certified uniform witnesses with coefficient three elevenths -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, endpoint logarithm, power and scalar certificates on a scale
interval starting at 465 give a uniform witness with coefficient `3 / 11`. -/
theorem uniform_narrow_cell {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {a b L P Q V R H J s t : ℝ}
    (ha : 465 ≤ a) (haL : a ≤ Real.log n) (hLb : Real.log n ≤ b)
    (hlog : Real.log (((52223 / 100000 : ℝ) * b) ^ 2) ≤ L)
    (hP : (((52223 / 100000 : ℝ) * a) ^ 2) ^ (-(27 / 25 : ℝ)) ≤ P)
    (hQ : (((52223 / 100000 : ℝ) * a) ^ 2) ^ (-(29 / 50 : ℝ)) ≤ Q)
    (hV : (((52223 / 100000 : ℝ) * a) ^ 2) ^ (-(83 / 100 : ℝ)) ≤ V) (hs : 0 < s)
    (hsqrt : s ^ 2 ≤ (52223 / 100000 : ℝ) * a) (ht0 : 0 ≤ t)
    (htsqrt : (52223 / 100000 : ℝ) * b ≤ t ^ 2)
    (hR : ((27 / 25 : ℝ) ^ 5 / 120) * (58721 / 1000000) * P * ((21 / 8 : ℝ) + L) ^ 5 ≤ R)
    (hH :
      ((27 / 25 : ℝ) ^ 5 / 120) * (58721 / 1000000) * P *
          quarterMomentPolynomial ((21 / 8 : ℝ) + L) ≤
        H)
    (hJ : quarterEulerClosedUpper L Q V ≤ J)
    (hcert :
      (2645975208579 / 48828125000000000 : ℝ) * a +
            (27 / 25 : ℝ) ^ 5 *
              ((3117 / 400 : ℝ) - 7 / 200 - (351 / 200 : ℝ) / ((52223 / 100000 : ℝ) * a) -
                (529 / 5000 : ℝ) * t -
                (526064 / 10000000 : ℝ) / s) -
          (2 * b + 3 * (1839 / 1000 : ℝ)) * R -
          H -
          4 * J -
          (39 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 ≥
        0) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (3 / 11 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let r : ℝ := (52223 / 100000 : ℝ) * Real.log n
  have har : (52223 / 100000 : ℝ) * a ≤ r := by
    dsimp only [r]; nlinarith only [haL]
  have hrb : r ≤ (52223 / 100000 : ℝ) * b := by
    dsimp only [r]; nlinarith only [hLb]
  have ha0 : (0 : ℝ) < (52223 / 100000 : ℝ) * a := by nlinarith only [ha]
  have hr : 180 ≤ r := by nlinarith only [ha, har]
  have hmin : ((52223 / 100000 : ℝ) * a) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ ha0.le har 2
  have hmax : r ^ 2 ≤ ((52223 / 100000 : ℝ) * b) ^ 2 :=
    pow_le_pow_left₀ (by linarith only [hr]) hrb 2
  have hlogr := (Real.log_le_log (sq_pos_of_pos (by linarith only [hr])) hmax).trans hlog
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
  have hru := quarter_finite_reflected_upper (by linarith only [hr]) hlogr hp
  have hju :=
    quarter_euler_closed_upper (show (1 : ℝ) ≤ r ^ 2 by nlinarith only [hr]) hlogr hq0 hv0 hq hv
  have hR0 : 0 ≤ quarterReflectedScale r := by
    dsimp only [quarterReflectedScale]
    have hz : 0 ≤ (21 / 8 : ℝ) + Real.log (r ^ 2) := by
      have h := Real.log_nonneg (show (1 : ℝ) ≤ r ^ 2 by nlinarith only [hr])
      linarith only [h]
    positivity
  have hlow : s ≤ Real.sqrt r := Real.le_sqrt_of_sq_le (hsqrt.trans har)
  have hhigh : Real.sqrt r ≤ t := Real.sqrt_le_iff.mpr ⟨ht0, hrb.trans htsqrt⟩
  have hbudget :=
    uniform_narrow_scalar ha haL hLb rfl hs hlow hhigh hR0 (hru.1.trans hR) (hru.2.trans hH)
      (hju.trans hJ) hcert
  obtain ⟨p, hp', hpbound, hfail⟩ := uniform_narrow_witness hn ho hu hGRH hr hbudget
  have hcut : r ^ 2 ≤ (3 / 11 : ℝ) * Real.log n ^ 2 := by
    dsimp only [r]
    have hsq := sq_nonneg (Real.log n)
    nlinarith only [hsq]
  exact ⟨p, hp', hpbound.trans hcut, hfail⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
