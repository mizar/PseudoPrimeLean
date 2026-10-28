/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaFixedStencil
public import PseudoPrime.LLS.GammaPrefixRecovered
public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaReflectedEnvelope

/-! # Recovered Gamma prefix and fixed-stencil all-input witness bounds -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH, the variation of the corrected ramp error is bounded by the
compact envelope and the clipped endpoint increment. The support-only continuity
is handled by the clamped extension. -/
theorem gammaFixedError_variation_bound (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    |PseudoPrime.AnalyticNumberTheory.Arithmetic.exponentialRampVariationFunctional
          (PseudoPrime.LLS.clippedShiftError x)| ≤
      (3 / 2) * ((63 / 800 : ℝ) * Real.sqrt x + 21 / 20) +
        42 * (PseudoPrime.LLS.fixedStencilIncrement x + 1 / 200) := by
  have hbound :
    ∀ u ∈ Set.Icc 0 (99 / 40 : ℝ),
      |gammaClippedErrorExtension x u| ≤ (63 / 800 : ℝ) * Real.sqrt x + 21 / 20 := by
    intro u hu
    rw [gammaClippedErrorExtension_eqOn hu]
    exact PseudoPrime.LLS.clippedShiftError_compact_le hRH hx hu.1 hu.2
  have hx0 : 0 < x := by linarith only [hx]
  have hleft :
    gammaClippedErrorExtension x (99 / 40) = PseudoPrime.LLS.clippedShiftError x (99 / 40) :=
    gammaClippedErrorExtension_eqOn ⟨by norm_num only, le_rfl⟩
  have hright :
    gammaClippedErrorExtension x (247 / 100) = PseudoPrime.LLS.clippedShiftError x (247 / 100) :=
    gammaClippedErrorExtension_eqOn ⟨by norm_num only, by norm_num only⟩
  have hinc := PseudoPrime.LLS.fixedShiftError_increment hRH hx
  have hD :
    |gammaClippedErrorExtension x (99 / 40) - gammaClippedErrorExtension x (247 / 100)| ≤
      PseudoPrime.LLS.fixedStencilIncrement x + 1 / 200 := by
    rw [hleft, hright]
    exact hinc
  have hv :=
    AnalyticNumberTheory.Arithmetic.exponentialRampVariationFunctional_abs_le_of_increment
      (gammaClippedErrorExtension_continuous hx0) hbound hD
  rw [AnalyticNumberTheory.Arithmetic.exponentialRampVariationFunctional_congr
      gammaClippedErrorExtension_eqOn] at hv
  exact hv

/-- Under RH and r>=1, the width 2r^2/25 gives the displayed index-four main lower bound.
Combine two normalized ramp bounds with the principal comparison. Retain the exact
reciprocal coefficients before applying log(2 pi)<=1839/1000 and exp(-1/r^2)<=1.
This is the analytic main input for the sharper all-input Gamma witness theorem. -/
theorem gammaRecoveredFourT_lower (hRH : RiemannHypothesis) {r : ℝ} (hr : 1 ≤ r) :
    (86733 / 98800 : ℝ) * r - 8431597 / 11856000 - (5754559 / 494000) / r ≤
      (4 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum (r ^ 2) / r) -
          (∑' k : ℕ,
              LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) (r ^ 2)
                k).re) /
        3 := by
  have hr0 : 0 < r := by linarith only [hr]
  have hx : 1 ≤ r ^ 2 := by nlinarith only [hr]
  have hx0 : 0 < r ^ 2 := (sq_pos_of_pos hr0)
  have hs : Real.sqrt (r ^ 2) = r := Real.sqrt_sq hr0.le
  let V : ℝ :=
    (3 / 2) * ((63 / 800 : ℝ) * r + 21 / 20) + 42 * (LLS.fixedStencilIncrement (r ^ 2) + 1 / 200)
  let E : ℝ := LLS.fixedShiftPrincipalError (r ^ 2)
  let atom : ℝ := Real.log (2 * Real.pi) * Real.exp (-(1 / r ^ 2))
  let T : ℝ := AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum (r ^ 2) / r
  let P : ℝ :=
    (∑' k : ℕ,
        LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) k).re
  have hvar := (abs_le.mp (gammaFixedError_variation_bound hRH hx)).1
  rw [hs] at hvar
  have hraw := gammaClippedRawError_variation_eq hx
  have hnorm :=
    AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum_normalized_eq_main_add_error hx0
  rw [hs] at hnorm
  have hmass : (293 / 320 : ℝ) ≤ ∫ u in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight u := by
    linarith only [Analysis.gamma_ramp_mass_lower]
  have hm := mul_le_mul_of_nonneg_right hmass hr0.le
  have hT : (293 / 320 : ℝ) * r - (V + atom) / r ≤ T := by
    dsimp only [T]
    rw [hnorm]
    apply add_le_add hm
    rw [← neg_div]
    apply (div_le_div_iff_of_pos_right hr0).mpr
    rw [hraw]
    dsimp only [V, atom]
    linarith only [hvar]
  have hprincipal := LLS.fixedShiftPrincipal_ge_mass133 (r ^ 2)
  have hactual := LLS.fixedShiftPrincipal_le_actual hRH hx
  rw [hs] at hprincipal hactual
  have hP : (133 / 160 : ℝ) * r - (E + atom) / r ≤ 2 * T - P := hprincipal.trans hactual
  have hc0 : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by nlinarith only [Real.pi_gt_three] : (1 : ℝ) ≤ 2 * Real.pi)
  have hc : Real.log (2 * Real.pi) ≤ (1839 / 1000 : ℝ) := Analysis.log_two_mul_pi_lt.le
  have he : Real.exp (-(1 / r ^ 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (one_div_nonneg.mpr (sq_nonneg r)))
  have hatom : atom ≤ (1839 / 1000 : ℝ) := by
    exact (mul_le_mul_of_nonneg_left he hc0).trans (by simpa only [mul_one] using hc)
  have hcoeff :
    (2 * V + E) / 3 =
      (71 / 80 - 86733 / 98800 : ℝ) * r ^ 2 + (8431597 / 11856000 : ℝ) * r +
            (5754559 / 494000 : ℝ) -
          (1 + 56 / 494) * (1839 / 1000) +
        (56 / 494) * Real.log (2 * Real.pi) := by
    dsimp only [V, E, LLS.fixedShiftPrincipalError, LLS.fixedStencilIncrement,
      LLS.fixedStencilEnvelope]
    rw [hs]
    have hratio (z : ℝ) :
      2 * z * ((99 / 40 : ℝ) * r ^ 2 + (2 / 25) * r ^ 2) / ((2 / 25) * r ^ 2) =
        (511 / 8 : ℝ) * z := by
      rw [show 2 * z * ((99 / 40 : ℝ) * r ^ 2 + (2 / 25) * r ^ 2) = ((511 / 100 : ℝ) * z) * r ^ 2 by
          ring,
        mul_div_mul_right _ _ (pow_ne_zero 2 hr0.ne')]
      ring
    simp only [hratio]
    ring
  have hcost :
    (2 * V + E) / 3 + atom ≤
      (71 / 80 - 86733 / 98800 : ℝ) * r ^ 2 + (8431597 / 11856000 : ℝ) * r + 5754559 / 494000 := by
    linarith only [hcoeff, hc, hatom]
  have hTr := mul_le_mul_of_nonneg_right hT hr0.le
  have hPr := mul_le_mul_of_nonneg_right hP hr0.le
  rw [sub_mul, div_mul_cancel₀ _ hr0.ne'] at hTr hPr
  have hid :
    ((86733 / 98800 : ℝ) * r - 8431597 / 11856000 - (5754559 / 494000) / r) * r =
      (86733 / 98800 : ℝ) * r ^ 2 - (8431597 / 11856000 : ℝ) * r - 5754559 / 494000 := by
    simp only [sub_mul, div_mul_cancel₀ _ hr0.ne', pow_two]
    ring
  apply (mul_le_mul_iff_right₀ hr0).mp
  change r * _ ≤ r * ((4 * T - P) / 3)
  nlinarith only [hTr, hPr, hcost, hid]

/-- The signed-prefix gap with reflected reciprocal constant 58129633/2223000.
It uses actual prefix credit 106/25 and the tighter fixed-width stencil,
while retaining the rigorously connected reflected tail. Its positive root supplies the cutoff. -/
noncomputable def gammaRecoveredGap (L r : ℝ) : ℝ :=
  (86733 / 98800 : ℝ) * r - (11783423 / 25000000 : ℝ) * L - 36174637 / 11856000 -
    ((7 / 6 : ℝ) * L + 58129633 / 2223000) / r

/-- The positive quadratic root of the reflected signed-prefix gap. The
certified domain begins at L=101; the lower bound sixty is established
algebraically before the analytic tail is used. -/
noncomputable def gammaRecoveredRoot (L : ℝ) : ℝ :=
  ((11783423 / 25000000 : ℝ) * L + 36174637 / 11856000 +
      Real.sqrt
        (((11783423 / 25000000 : ℝ) * L + 36174637 / 11856000) ^ 2 +
          4 * (86733 / 98800 : ℝ) * ((7 / 6 : ℝ) * L + 58129633 / 2223000))) /
    (2 * (86733 / 98800 : ℝ))

/-- The witness cutoff (99/40) times the square of the reflected root.
For L>=101 its root exceeds sixty and includes the entire 1000 prefix.
The all-input witness theorem uses this single expression. -/
noncomputable def gammaRecoveredBound (L : ℝ) : ℝ :=
  (99 / 40 : ℝ) * gammaRecoveredRoot L ^ 2

/-- For L>=101, the reflected root is positive. Its positive linear
numerator and nonnegative discriminant have a positive denominator. -/
theorem gammaRecoveredRoot_pos {L : ℝ} (hL : 101 ≤ L) : 0 < gammaRecoveredRoot L := by
  have hD : (0 : ℝ) ≤ 36174637 / 11856000 := by norm_num only
  have hL0 : 0 < L := by linarith only [hL]
  have hB : 0 < (11783423 / 25000000 : ℝ) * L + (36174637 / 11856000) := by
    have hmul := mul_pos (by norm_num only : (0 : ℝ) < 11783423 / 25000000) hL0
    linarith only [hmul, hD]
  have hA : 0 < (7 / 6 : ℝ) * L + 58129633 / 2223000 := by
    apply add_pos
    · exact mul_pos (by norm_num only) hL0
    · norm_num only
  have hK : 0 < (86733 / 98800 : ℝ) := by norm_num only
  have hdisc :
    0 <
      ((11783423 / 25000000 : ℝ) * L + (36174637 / 11856000)) ^ 2 +
        4 * (86733 / 98800 : ℝ) * ((7 / 6 : ℝ) * L + 58129633 / 2223000) := by
    apply add_pos
    · exact sq_pos_of_pos hB
    · exact mul_pos (mul_pos (by norm_num only) hK) hA
  dsimp only [gammaRecoveredRoot]
  apply div_pos
  · exact add_pos hB (Real.sqrt_pos.mpr hdisc)
  · exact mul_pos (by norm_num only) hK

/-- For L>=101, the reflected root makes the scalar gap zero. Square
the discriminant identity and divide its exact quadratic equation by
the positive root. No analytic tail bound is used in this step. -/
theorem gammaRecoveredGap_root_eq_zero {L : ℝ} (hL : 101 ≤ L) :
    gammaRecoveredGap L (gammaRecoveredRoot L) = 0 := by
  have hD : (0 : ℝ) ≤ 36174637 / 11856000 := by norm_num only
  let b : ℝ := (11783423 / 25000000 : ℝ) * L + (36174637 / 11856000)
  let A : ℝ := (7 / 6 : ℝ) * L + 58129633 / 2223000
  let K : ℝ := 86733 / 98800
  let disc : ℝ := b ^ 2 + 4 * K * A
  let r : ℝ := (b + Real.sqrt disc) / (2 * K)
  have hB : 0 < b := by
    dsimp only [b]
    have hL0 : 0 < L := by linarith only [hL]
    have hmul := mul_pos (by norm_num only : (0 : ℝ) < 11783423 / 25000000) hL0
    linarith only [hmul, hD]
  have hA : 0 < A := by
    dsimp only [A]
    linarith only [hL]
  have hK : 0 < K := by norm_num only [K]
  have hdisc : 0 < disc := by
    dsimp only [disc]
    exact add_pos (sq_pos_of_pos hB) (mul_pos (mul_pos (by norm_num only) hK) hA)
  have hs : (Real.sqrt disc) ^ 2 = disc := Real.sq_sqrt hdisc.le
  have hr : 0 < r := by
    dsimp only [r]
    exact div_pos (add_pos hB (Real.sqrt_pos.mpr hdisc)) (mul_pos (by norm_num only) hK)
  have hrEq : gammaRecoveredRoot L = r := by dsimp only [gammaRecoveredRoot, r, disc, b, A, K]
  have hquad : K * r ^ 2 - b * r - A = 0 := by
    have hlin : r * (2 * K) = b + Real.sqrt disc := by
      dsimp only [r]
      exact div_mul_cancel₀ _ (mul_ne_zero (by norm_num only : (2 : ℝ) ≠ 0) hK.ne')
    have hsqrt : r * (2 * K) - b = Real.sqrt disc := by linarith only [hlin]
    have hsq : (r * (2 * K) - b) ^ 2 = disc := by rw [hsqrt, hs]
    have hdiscEq : disc = b ^ 2 + 4 * K * A := rfl
    norm_num only [K] at hdiscEq hsq ⊢
    nlinarith only [hdiscEq, hsq]
  have hmul : gammaRecoveredGap L r * r = 0 := by
    rw [gammaRecoveredGap]
    dsimp only [A, b, K] at hquad ⊢
    simp only [sub_mul, div_mul_cancel₀ _ hr.ne']
    nlinarith only [hquad]
  rw [hrEq]
  exact (mul_eq_zero.mp hmul).resolve_right hr.ne'

/-- For L>=101, every radius above the reflected root has nonnegative
gap. Factor the difference from its zero root into a nonnegative
radius increment and a positive slope. -/
theorem gammaRecoveredGap_nonneg_of_root_le {L r : ℝ} (hL : 101 ≤ L)
    (hr : gammaRecoveredRoot L ≤ r) : 0 ≤ gammaRecoveredGap L r := by
  let rho := gammaRecoveredRoot L
  have hrho : 0 < rho := gammaRecoveredRoot_pos hL
  have hr' : 0 < r := lt_of_lt_of_le hrho hr
  have hL0 : 0 < L := by linarith only [hL]
  have hA : 0 < (7 / 6 : ℝ) * L + 58129633 / 2223000 := by
    apply add_pos
    · exact mul_pos (by norm_num only) hL0
    · norm_num only
  have hK : 0 < (86733 / 98800 : ℝ) := by norm_num only
  have hid :
    gammaRecoveredGap L r - gammaRecoveredGap L rho =
      ((86733 / 98800 : ℝ) + ((7 / 6 : ℝ) * L + 58129633 / 2223000) / (r * rho)) * (r - rho) := by
    calc
      _ =
          (86733 / 98800 : ℝ) * (r - rho) +
            (((7 / 6 : ℝ) * L + 58129633 / 2223000) / rho -
              ((7 / 6 : ℝ) * L + 58129633 / 2223000) / r) :=
        by
        simp only [gammaRecoveredGap]
        ring
      _ = _ := by
        rw [div_sub_div _ _ hrho.ne' hr'.ne', mul_comm rho r]
        ring
  have hdiff :
    0 ≤ ((86733 / 98800 : ℝ) + ((7 / 6 : ℝ) * L + 58129633 / 2223000) / (r * rho)) * (r - rho) := by
    apply mul_nonneg
    · exact add_nonneg hK.le (div_nonneg hA.le (mul_nonneg hr'.le hrho.le))
    · exact sub_nonneg.mpr hr
  have hroot : gammaRecoveredGap L rho = 0 := by
    dsimp only [rho]
    exact gammaRecoveredGap_root_eq_zero hL
  rw [hroot] at hid
  linarith only [hid, hdiff]

/-- For L>=101 and a positive test radius, a nonnegative reflected
gap bounds the root above. A smaller test radius would give a strictly
positive root-to-test gap difference and a contradiction. -/
theorem gammaRecoveredRoot_le_of_gap_nonneg {L r : ℝ} (hL : 101 ≤ L) (hr : 0 < r)
    (hgap : 0 ≤ gammaRecoveredGap L r) : gammaRecoveredRoot L ≤ r := by
  by_contra hnot
  have hlt : r < gammaRecoveredRoot L := lt_of_not_ge hnot
  let rho := gammaRecoveredRoot L
  have hrho : 0 < rho := gammaRecoveredRoot_pos hL
  have hL0 : 0 < L := by linarith only [hL]
  have hA : 0 < (7 / 6 : ℝ) * L + 58129633 / 2223000 := by
    apply add_pos
    · exact mul_pos (by norm_num only) hL0
    · norm_num only
  have hK : 0 < (86733 / 98800 : ℝ) := by norm_num only
  have hid :
    gammaRecoveredGap L rho - gammaRecoveredGap L r =
      ((86733 / 98800 : ℝ) + ((7 / 6 : ℝ) * L + 58129633 / 2223000) / (r * rho)) * (rho - r) := by
    calc
      _ =
          (86733 / 98800 : ℝ) * (rho - r) +
            (((7 / 6 : ℝ) * L + 58129633 / 2223000) / r -
              ((7 / 6 : ℝ) * L + 58129633 / 2223000) / rho) :=
        by
        simp only [gammaRecoveredGap]
        ring
      _ = _ := by
        rw [div_sub_div _ _ hr.ne' hrho.ne']
        ring
  have hdiff :
    0 < ((86733 / 98800 : ℝ) + ((7 / 6 : ℝ) * L + 58129633 / 2223000) / (r * rho)) * (rho - r) := by
    apply mul_pos
    · exact add_pos hK (div_pos hA (mul_pos hr hrho))
    · exact sub_pos.mpr hlt
  have hroot : gammaRecoveredGap L rho = 0 := by
    dsimp only [rho]
    exact gammaRecoveredGap_root_eq_zero hL
  rw [hroot] at hid
  linarith only [hid, hdiff, hgap]

/-- For L>=101, the reflected root strictly exceeds sixty. The gap
at sixty is negative on the whole half-line, so root monotonicity
excludes a smaller root before any tail estimate is applied. -/
theorem gammaRecoveredRoot_gt_sixty {L : ℝ} (hL : 101 ≤ L) : (60 : ℝ) < gammaRecoveredRoot L := by
  by_contra h
  have hg := gammaRecoveredGap_nonneg_of_root_le hL (le_of_not_gt h)
  dsimp only [gammaRecoveredGap] at hg
  linarith only [hg, hL]

/-- Under GRH, every odd composite n>1 with log n>=101 has an actual
rejecting prime within the reflected Gamma cutoff. Use the unchanged
recovered prefix and fixed-stencil main term and the new reflected-budget consumer. Strict
common cost supplies the required strict gap at the scalar root. -/
theorem exists_prime_gammaRecovered {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 101 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ gammaRecoveredBound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  let r := gammaRecoveredRoot (Real.log n)
  have hr60 : (60 : ℝ) < r := gammaRecoveredRoot_gt_sixty hL
  have hr : (1 : ℝ) ≤ r := by linarith only [hr60]
  have hr0 : (0 : ℝ) < r := by linarith only [hr60]
  have hx : (2 : ℝ) ≤ r ^ 2 := by nlinarith only [hr60]
  have hs : Real.sqrt (r ^ 2) = r := Real.sqrt_sq hr0.le
  have hQ : 20000 ≤ n := by
    by_contra h
    have hN : (n : ℝ) ≤ 46000 := by
      exact_mod_cast ((lt_of_not_ge h).le.trans (by norm_num only : 20000 ≤ 46000))
    have hl := Real.log_le_log (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn)) hN
    linarith only [hl, Analysis.log_46000_lt_eleven, hL]
  have hn9 : n ≠ 9 := by
    intro h
    rw [h] at hQ
    norm_num only at hQ
  have htail0 :=
    LLS.PaperStatements.rpow_neg_nine_sixteenths_le_div_scale_sqrt (a := 5 / 3)
      (by norm_num only : (0 : ℝ) < 5 / 3)
      (by
        norm_num only; nlinarith only [hr60] : (5 / 3 : ℝ) ^ 16 ≤ r ^ 2)
  rw [hs] at htail0
  have hpow : (35 / 2 : ℝ) * (r ^ 2) ^ (-9 / 16 : ℝ) ≤ (21 / 2) / r := by
    calc
      _ ≤ (35 / 2) * (1 / ((5 / 3) * r)) := mul_le_mul_of_nonneg_left htail0 (by norm_num only)
      _ = _ := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        norm_num only
        ring
  have hsq : (3600 : ℝ) ≤ r ^ 2 := by nlinarith only [hr60]
  have hrecip :=
    div_le_div_of_nonneg_left (by norm_num only : (0 : ℝ) ≤ 1) (by norm_num only : (0 : ℝ) < 3600)
      hsq
  have hrecipDiv := div_le_div_of_nonneg_right hrecip hr0.le
  have hrec : 1 / (r ^ 2 * r) ≤ (1 / 3600 : ℝ) / r := by simpa only [div_div] using hrecipDiv
  have htail :
    (35 / 2 : ℝ) * (r ^ 2) ^ (-9 / 16 : ℝ) + 1 / (r ^ 2 * r) ≤ (21 / 2 + 1 / 3600 : ℝ) / r := by
    have hadd := add_le_add hpow hrec
    convert hadd using 1
    ring
  have hpref := LLS.gamma_prefix1000_recovered hGRH.riemann (le_refl (1000 : ℝ))
  have hg : 0 ≤ gammaRecoveredGap (Real.log n) r := by rw [gammaRecoveredGap_root_eq_zero hL]
  have hu := gammaReflectedBudget_lt_common hGRH.riemann n n (r ^ 2) 1000
  rw [hs] at hu
  have hid :
    ((7 / 6 : ℝ) * Real.log n + 58129633 / 2223000) / r =
      ((7 / 6 : ℝ) * Real.log n + 4) / r + (21 / 2 + 1 / 3600 : ℝ) / r +
        (5754559 / 494000) / r := by
    ring
  have hbudget :
    gammaReflectedMRBudget n n (r ^ 2) 1000 <
      (86733 / 98800 : ℝ) * r - 8431597 / 11856000 - (5754559 / 494000) / r := by
    dsimp only [gammaRecoveredGap] at hg
    linarith only [hu, hpref, htail, hg, hid]
  have hmain := gammaRecoveredFourT_lower hGRH.riemann hr
  have hactual :
    gammaReflectedMRBudget n n (r ^ 2) 1000 <
      (4 *
            (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum (r ^ 2) /
              Real.sqrt (r ^ 2)) -
          (∑' k : ℕ,
              LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) (r ^ 2)
                k).re) /
        3 := by
    rw [hs]
    exact hbudget.trans_le hmain
  exact
    exists_prime_reflected_gap_all hn ho hc hn9 hGRH hQ hx (by norm_num only)
      (by nlinarith only [hr60]) hactual

/-- Under the reflected Gamma assumptions, the least rejecting prime
satisfies the same cutoff. Extract it from the actual all-input witness
theorem with no squarefreeness, index or factor-count restriction. -/
theorem exists_least_gammaRecovered {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 101 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ gammaRecoveredBound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  exact
    exists_least_prime_reject_of_exists_prime_reject (exists_prime_gammaRecovered hn ho hc hGRH hL)

end PseudoPrime.PrimeTestBounds.MillerRabin
