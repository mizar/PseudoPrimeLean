/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalCostPart2Bounds
public import PseudoPrime.LLS.Extensions.RetainedEvenReciprocalBounds
public import PseudoPrime.LLS.Extensions.QNeOneSharpCharacterBounds

/-! # Reciprocal-loss transfer to the odd-prime quadratic branches -/

@[expose] public section

namespace PseudoPrime.LLS.Extensions

/-- The even logarithmic upper envelope with root y, conductor bound f,
Riemann reciprocal loss r and dyadic defect d. The exact even main error
is retained. This separates the analytic estimate from numerical branching. -/
noncomputable def qNeOneReciprocalUpper (y f r d : ℝ) : ℝ :=
  (2 * y + 2 + 2 * Real.log y) *
      (((1 / 2) * (1 - 1 / y ^ 2) * f - 4 / 5 - (2 * Real.log y - r - d)) / (1 - 1 / y) ^ 2) +
    f * Real.log y +
    Analysis.primitiveLogEvenMainError (y ^ 2)

/-- For an even primitive nonprincipal character under GRH and root at least eight,
an arbitrary certified even reciprocal error e shifts the effective loss by e+4/5.
Combine the parity-conditional reciprocal bound with the exact logarithmic
estimate. This retains stronger even errors without changing the envelope. -/
theorem evenLogWeighted_le_reciprocalUpper_of_mainError {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    (ψ : DirichletCharacter ℂ N) (hp : ψ.IsPrimitive) (hne : ψ ≠ 1) (heven : ψ.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y f r d e : ℝ} (hy : 8 ≤ y)
    (hE : Analysis.primitiveReciprocalEvenMainError (y ^ 2) ≤ e)
    (hF : Real.log N - Real.log Real.pi ≤ f)
    (hR :
      Real.log (y ^ 2) - r ≤ AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum (y ^ 2))
    (hd : weightedReciprocalDefect ψ (y ^ 2) ≤ d) :
    (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2) ψ).re ≤
      qNeOneReciprocalUpper y f (r + e + 4 / 5) d := by
  have hy0 : 0 < y := by linarith only [hy]
  have hx := Analysis.sq_ge_64_of_ge_8 hy
  have hx1 : (1 : ℝ) < y ^ 2 := by linarith only [hx]
  have hr :=
    primitiveReciprocalRaw_even_le_of_mainError hN2 hGRH hp hne (inv_ne_one.mpr hne) heven hx1 hE
  have hl := re_characterReciprocalWeightedSum_ge_of_pointwise_lower ψ hR hd
  have hu :=
    AnalyticNumberTheory.DirichletLFunction.primitiveLogWeightedUpper_of_grh_even_exact hN2 hGRH hp
      hne (inv_ne_one.mpr hne) heven hx
  rw [Real.sqrt_sq hy0.le] at hr hu
  rw [Real.log_pow] at hl hu
  norm_num only [Nat.cast_ofNat] at hl hu
  have hz : 0 ≤ Real.log y := Real.log_nonneg (by linarith only [hy])
  have hden : 0 < (1 - 1 / y) ^ 2 := by
    exact sq_pos_of_pos (sub_pos.mpr ((div_lt_one hy0).mpr (by linarith only [hy])))
  have hFmul :=
    mul_le_mul_of_nonneg_left hF
      (show 0 ≤ (1 / 2 : ℝ) * (1 - 1 / y ^ 2)
        by
        have hv : 1 / y ^ 2 ≤ (1 : ℝ) :=
          (div_le_one (sq_pos_of_pos hy0)).mpr (by nlinarith only [hy])
        linarith only [hv])
  have hb :
    |AnalyticNumberTheory.DirichletLFunction.primitiveBRe ψ| ≤
      ((1 / 2) * (1 - 1 / y ^ 2) * f - 4 / 5 - (2 * Real.log y - (r + e + 4 / 5) - d)) /
        (1 - 1 / y) ^ 2 := by
    apply (le_div_iff₀ hden).mpr
    nlinarith only [hr, hl, hFmul]
  have hm :=
    mul_le_mul_of_nonneg_left hb (show 0 ≤ 2 * y + 2 + 2 * Real.log y by linarith only [hy, hz])
  have hf := mul_le_mul_of_nonneg_right hF hz
  unfold qNeOneReciprocalUpper
  nlinarith only [hu, hm, hf]

/-- For an even primitive nonprincipal character under GRH and y at least eight,
a pointwise reciprocal lower bound and a dyadic defect bound control the log sum.
Combine the stronger even reciprocal remainder with the exact even log estimate.
This supplies all three values at two without requiring prime triviality at two. -/
theorem evenLogWeighted_le_reciprocalUpper {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    (ψ : DirichletCharacter ℂ N) (hp : ψ.IsPrimitive) (hne : ψ ≠ 1) (heven : ψ.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y f r d : ℝ} (hy : 8 ≤ y)
    (hF : Real.log N - Real.log Real.pi ≤ f)
    (hR :
      Real.log (y ^ 2) - r ≤ AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum (y ^ 2))
    (hd : weightedReciprocalDefect ψ (y ^ 2) ≤ d) :
    (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2) ψ).re ≤
      qNeOneReciprocalUpper y f r d := by
  have hE : Analysis.primitiveReciprocalEvenMainError (y ^ 2) ≤ -(4 / 5 : ℝ) := by
    have h := llsPrimitiveReciprocalEvenMainError_lt_neg_four_fifths (Analysis.sq_ge_64_of_ge_8 hy)
    exact h.le
  have he : r + -(4 / 5 : ℝ) + 4 / 5 = r := by ring
  simpa only [he] using
    evenLogWeighted_le_reciprocalUpper_of_mainError hN2 ψ hp hne heven hGRH hy hE hF hR hd

/-- For y at least eight, increasing the conductor, reciprocal loss and
dyadic defect bounds increases the upper envelope. All multiplying coefficients
are nonnegative. This permits compatible relaxations of the three costs. -/
theorem qNeOneReciprocalUpper_mono {y f g r s d e : ℝ} (hy : 8 ≤ y) (hf : f ≤ g) (hr : r ≤ s)
    (hd : d ≤ e) : qNeOneReciprocalUpper y f r d ≤ qNeOneReciprocalUpper y g s e := by
  have hy0 : 0 < y := by linarith only [hy]
  have hz : 0 ≤ Real.log y := Real.log_nonneg (by linarith only [hy])
  have hden : 0 ≤ (1 - 1 / y) ^ 2 := sq_nonneg _
  have hcoef : 0 ≤ (1 / 2 : ℝ) * (1 - 1 / y ^ 2) := by
    have hv : 1 / y ^ 2 ≤ (1 : ℝ) := (div_le_one (sq_pos_of_pos hy0)).mpr (by nlinarith only [hy])
    linarith only [hv]
  have hF := mul_le_mul_of_nonneg_left hf hcoef
  have hn :
    (1 / 2 : ℝ) * (1 - 1 / y ^ 2) * f - 4 / 5 - (2 * Real.log y - r - d) ≤
      (1 / 2 : ℝ) * (1 - 1 / y ^ 2) * g - 4 / 5 - (2 * Real.log y - s - e) := by
    linarith only [hF, hr, hd]
  have hB := div_le_div_of_nonneg_right hn hden
  have hM :=
    mul_le_mul_of_nonneg_left hB (show 0 ≤ 2 * y + 2 + 2 * Real.log y by linarith only [hy, hz])
  have hFz := mul_le_mul_of_nonneg_right hf hz
  unfold qNeOneReciprocalUpper
  linarith only [hM, hFz]

/-- The earlier zero-branch upper envelope is the reciprocal-loss envelope
with loss 8/5 and dyadic defect log 2. Expand the definitions and normalize.
This connects existing large-scale separation to the new parameterized family. -/
theorem qNeOneReciprocalUpper_eq_zeroStar (y : ℝ) :
    qNeOneReciprocalUpper y (y + Real.log 4 - Real.log Real.pi) (8 / 5) (Real.log 2) =
      qNeOneUpperBoundZeroStar y := by
  unfold qNeOneReciprocalUpper qNeOneUpperBoundZeroStar qNeOneBUpperBoundZeroStar
  ring

/-- For y at least eight, the corrected negative-one envelope is dominated
by the zero envelope at every reciprocal loss r. The conductor saving cancels
the extra dyadic correction. An exact identity proves this independently of r. -/
theorem qNeOneReciprocalUpper_neg_one_corrected_le_zero {y r L : ℝ} (hy : 8 ≤ y) :
    qNeOneReciprocalUpper y (L - Real.log Real.pi) r ((4 / 3) * Real.log 2) +
        Analysis.logTwoSquareCorrection y ≤
      qNeOneReciprocalUpper y (L + Real.log 4 - Real.log Real.pi) r (Real.log 2) := by
  have hy0 : 0 < y := by linarith only [hy]
  have hd : 0 < (1 - 1 / y) ^ 2 := by
    exact sq_pos_of_pos (sub_pos.mpr ((div_lt_one hy0).mpr (by linarith only [hy])))
  have hc : 0 ≤ 2 / 3 - 1 / y ^ 2 := by
    have ht : 1 / y ^ 2 ≤ (1 / 64 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num only) (by norm_num only) (Analysis.sq_ge_64_of_ge_8 hy)
    linarith only [ht]
  have hz : 0 ≤ Real.log y := Real.log_nonneg (by linarith only [hy])
  have he :
    qNeOneReciprocalUpper y (L + Real.log 4 - Real.log Real.pi) r (Real.log 2) -
        (qNeOneReciprocalUpper y (L - Real.log Real.pi) r ((4 / 3) * Real.log 2) +
          Analysis.logTwoSquareCorrection y) =
      (2 * y + 2 + 2 * Real.log y) * (Real.log 2 * (2 / 3 - 1 / y ^ 2) / (1 - 1 / y) ^ 2) +
        (Real.log 2) ^ 2 := by
    unfold qNeOneReciprocalUpper Analysis.logTwoSquareCorrection
    rw [Real.log_four_eq]
    field_simp [hy0.ne', (ne_of_gt hd)]
    ring
  have hp :=
    add_nonneg
      (mul_nonneg (by linarith only [hy, hz] : 0 ≤ 2 * y + 2 + 2 * Real.log y)
        (div_nonneg (mul_nonneg (Real.log_pos (by norm_num only : (1 : ℝ) < 2)).le hc) hd.le))
      (sq_nonneg (Real.log 2))
  linarith only [he, hp]

/-- The Riemann lower envelope after the half-square dyadic defect.
Retain zero mass 233/10000 and the logarithmic constant 1839/1000.
The same expression applies to all three corrected character sums. -/
noncomputable def qNeOneReciprocalLower (y : ℝ) : ℝ :=
  y ^ 2 - (233 / 5000 : ℝ) * (y + 1) - (1839 / 500 : ℝ) * Real.log y - 1 - 2 * (Real.log y) ^ 2

/-- For roots y at least eight, the precise lower envelope lies below the
actual Riemann logarithmic lower expression minus its half-square defect.
Use the certified zero mass and logarithmic constant. No character is required. -/
theorem qNeOneReciprocalLower_le_riemann {y : ℝ} (hy : 8 ≤ y) :
    qNeOneReciprocalLower y ≤ riemannLogLowerAt (y ^ 2) - (Real.log (y ^ 2)) ^ 2 / 2 := by
  have hm :=
    mul_le_mul_of_nonneg_right AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_233_div_10000
      (show 0 ≤ y + 1 by linarith only [hy])
  have hl :=
    mul_le_mul_of_nonneg_right Analysis.log_two_mul_pi_lt.le
      (Real.log_nonneg (show 1 ≤ y by linarith only [hy]))
  rw [qNeOneReciprocalLower, riemannLogLowerAt, Real.sqrt_sq (show 0 ≤ y by linarith only [hy]),
    Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  nlinarith only [hm, hl]

/-- A logarithmic defect at most half the squared log plus c transfers
the Riemann lower estimate to the character sum corrected by c.
This common interface supplies the zero, one and negative-one branches. -/
theorem qNeOneReciprocalLower_le_corrected_sum {f : ℕ} [NeZero f] (ψ : DirichletCharacter ℂ f)
    (hRH : LLSRiemannWeightedLowerBound) {y c : ℝ} (hy : 8 ≤ y)
    (hd : weightedLogDefect ψ (y ^ 2) ≤ (Real.log (y ^ 2)) ^ 2 / 2 + c) :
    qNeOneReciprocalLower y ≤
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2) ψ).re + c := by
  have hx := Analysis.sq_ge_64_of_ge_8 hy
  have h :=
    re_characterLogWeightedSum_ge_of_defect_le hRH ψ
      (lt_of_lt_of_le (by norm_num only : (1 : ℝ) < 64) hx) hd
  have hl := qNeOneReciprocalLower_le_riemann hy
  linarith only [h, hl]

/-- Under GRH and the conductor conditions, any certified even reciprocal error
can be used in the three dyadic branches. The effective envelope loss is
r+e+4/5. Preserve the conductor saving in the negative-one branch and compare
with the common Riemann lower envelope. This avoids fixing a numerical error. -/
theorem not_oddPrimeTrivial_of_reciprocal_loss_and_mainError {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hne : χ ≠ 1)
    (heven : χ.primitiveCharacter.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y L r e : ℝ} (hy : 8 ≤ y)
    (hE : Analysis.primitiveReciprocalEvenMainError (y ^ 2) ≤ e)
    (hlog4 : Real.log χ.conductor ≤ L + Real.log 4)
    (hlogOdd : χ.primitiveCharacter 2 ≠ 0 → Real.log χ.conductor ≤ L)
    (hcases : χ.primitiveCharacter 2 = 0 ∨ χ.primitiveCharacter 2 = 1 ∨ χ.primitiveCharacter 2 = -1)
    (hR :
      Real.log (y ^ 2) - r ≤ AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum (y ^ 2))
    (hsep :
      qNeOneReciprocalUpper y (L + Real.log 4 - Real.log Real.pi) (r + e + 4 / 5) (Real.log 2) <
        qNeOneReciprocalLower y) :
    ¬OddPrimeTrivial χ (y ^ 2) := by
  intro hodd
  have hp := DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hprim := AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hne
  have hf : 2 ≤ χ.conductor := by
    have h0 := NeZero.pos χ.conductor
    have h1 :=
      AnalyticNumberTheory.DirichletLFunction.dirichletCharacter_level_ne_one_of_ne_one hprim
    exact Nat.succ_le_iff.mpr (Nat.lt_of_le_of_ne h0 (Ne.symm h1))
  have hx := Analysis.sq_ge_64_of_ge_8 hy
  have hx2 : (2 : ℝ) ≤ y ^ 2 := le_trans (by norm_num only) hx
  have hRH := llsRiemannWeightedLowerBound_of_riemannHypothesis hGRH.riemann
  have hF := sub_le_sub_right hlog4 (Real.log Real.pi)
  rcases hcases with h2 | h2 | h2
  · have hdS := weightedLogDefect_le_of_apply_two_eq_zero (y ^ 2) χ hx2 hodd h2
    have hdR := weightedReciprocalDefect_le_of_apply_two_eq_zero (y ^ 2) χ hx2 hodd h2
    have hl :=
      qNeOneReciprocalLower_le_corrected_sum χ.primitiveCharacter hRH hy (c := 0)
        (by simpa only [add_zero] using hdS)
    have hu :=
      evenLogWeighted_le_reciprocalUpper_of_mainError hf χ.primitiveCharacter hp hprim heven hGRH hy
        hE hF hR hdR
    simp only [add_zero] at hl
    exact (not_lt_of_ge (hl.trans hu)) hsep
  · have hdS := weightedLogDefect_le_of_apply_two_eq_one (y ^ 2) χ hx2 hodd h2
    have hdR : weightedReciprocalDefect χ.primitiveCharacter (y ^ 2) ≤ Real.log 2 := by
      rw [weightedReciprocalDefect_eq_zero_of_apply_two_eq_one (y ^ 2) χ hx2 hodd h2]
      exact (Real.log_pos (by norm_num only : (1 : ℝ) < 2)).le
    have hl :=
      qNeOneReciprocalLower_le_corrected_sum χ.primitiveCharacter hRH hy (c := 0)
        (by simpa only [add_zero] using hdS)
    have hu :=
      evenLogWeighted_le_reciprocalUpper_of_mainError hf χ.primitiveCharacter hp hprim heven hGRH hy
        hE hF hR hdR
    simp only [add_zero] at hl
    exact (not_lt_of_ge (hl.trans hu)) hsep
  · have hdS :=
      weightedLogDefect_le_of_apply_two_eq_neg_one (y ^ 2) χ (le_trans (by norm_num only) hx) hodd
        h2
    have hdR := weightedReciprocalDefect_le_of_apply_two_eq_neg_one (y ^ 2) χ hx2 hodd h2
    have hd :
      weightedLogDefect χ.primitiveCharacter (y ^ 2) ≤
        (Real.log (y ^ 2)) ^ 2 / 2 + Analysis.logTwoSquareCorrection y := by
      simpa only [Analysis.logTwoSquareCorrection, Real.log_pow, Nat.cast_ofNat] using hdS
    have hl := qNeOneReciprocalLower_le_corrected_sum χ.primitiveCharacter hRH hy hd
    have hFo :=
      sub_le_sub_right
        (hlogOdd
          (by
            rw [h2]; norm_num only))
        (Real.log Real.pi)
    have hu :=
      evenLogWeighted_le_reciprocalUpper_of_mainError hf χ.primitiveCharacter hp hprim heven hGRH hy
        hE hFo hR hdR
    have hc := qNeOneReciprocalUpper_neg_one_corrected_le_zero (r := r + e + 4 / 5) (L := L) hy
    have hu' := (add_le_add hu (le_refl (Analysis.logTwoSquareCorrection y))).trans hc
    exact (not_lt_of_ge (hl.trans hu')) hsep

/-- Under GRH and the stated conductor conditions, a separating reciprocal-loss
envelope rules out odd-prime triviality. Treat the primitive value at two as
zero, one or negative one and retain its exact dyadic correction.
The separation and reciprocal lower bound remain arbitrary analytic inputs. -/
theorem not_oddPrimeTrivial_of_reciprocal_loss {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] (hne : χ ≠ 1) (heven : χ.primitiveCharacter.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y L r : ℝ} (hy : 8 ≤ y)
    (hlog4 : Real.log χ.conductor ≤ L + Real.log 4)
    (hlogOdd : χ.primitiveCharacter 2 ≠ 0 → Real.log χ.conductor ≤ L)
    (hcases : χ.primitiveCharacter 2 = 0 ∨ χ.primitiveCharacter 2 = 1 ∨ χ.primitiveCharacter 2 = -1)
    (hR :
      Real.log (y ^ 2) - r ≤ AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum (y ^ 2))
    (hsep :
      qNeOneReciprocalUpper y (L + Real.log 4 - Real.log Real.pi) r (Real.log 2) <
        qNeOneReciprocalLower y) :
    ¬OddPrimeTrivial χ (y ^ 2) := by
  have hE : Analysis.primitiveReciprocalEvenMainError (y ^ 2) ≤ -(4 / 5 : ℝ) :=
    (llsPrimitiveReciprocalEvenMainError_lt_neg_four_fifths (Analysis.sq_ge_64_of_ge_8 hy)).le
  have he : r + -(4 / 5 : ℝ) + 4 / 5 = r := by ring
  apply
    not_oddPrimeTrivial_of_reciprocal_loss_and_mainError χ hne heven hGRH hy hE hlog4 hlogOdd hcases
      hR
  simpa only [he] using hsep

end PseudoPrime.LLS.Extensions
