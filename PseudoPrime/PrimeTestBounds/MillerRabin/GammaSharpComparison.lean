/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaClippedComparison
public import PseudoPrime.LLS.GammaCheckpoint1000Sharp
public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointEvenPolynomial
/-! # Sharper width and retained reciprocal coefficients -/
@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH and r>=1, the width 2r^2/25 gives the displayed index-four main lower bound.
Combine two normalized ramp bounds with the principal comparison. Retain the exact
reciprocal coefficients before applying log(2 pi)<=1839/1000 and exp(-1/r^2)<=1.
This is the analytic main input for the sharper all-input Gamma witness theorem. -/
theorem gammaSharpFourT_lower (hRH : RiemannHypothesis) {r : ℝ} (hr : 1 ≤ r) :
    (86733 / 98800 : ℝ) * r - 10148557 / 11856000 - (5754559 / 494000) / r ≤
      (4 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum (r ^ 2) / r) -
        (∑' k : ℕ, LLS.PaperStatements.gammaMellinKernel.summand
          (1 : DirichletCharacter ℂ 1) (r ^ 2) k).re) / 3 := by
  have hr0 : 0 < r := by linarith only [hr]
  have hx : 1 ≤ r ^ 2 := by nlinarith only [hr]
  have hx0 : 0 < r ^ 2 := (sq_pos_of_pos hr0)
  have hs : Real.sqrt (r ^ 2) = r := Real.sqrt_sq hr0.le
  have hh : 0 < (2 / 25 : ℝ) * r ^ 2 := mul_pos (by norm_num only) hx0
  have hhx : (2 / 25 : ℝ) * r ^ 2 ≤ r ^ 2 := by nlinarith only [sq_nonneg r]
  let V : ℝ := (3 / 2) * ((63 / 800 : ℝ) * r + 21 / 20) +
    42 * (LLS.logShiftRampIncrement (r ^ 2) ((2 / 25) * r ^ 2) + 1 / 200)
  let E : ℝ := LLS.clippedShiftPrincipalErrorNumerator (r ^ 2) ((2 / 25) * r ^ 2)
  let atom : ℝ := Real.log (2 * Real.pi) * Real.exp (-(1 / r ^ 2))
  let T : ℝ := AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum (r ^ 2) / r
  let P : ℝ := (∑' k : ℕ, LLS.PaperStatements.gammaMellinKernel.summand
    (1 : DirichletCharacter ℂ 1) (r ^ 2) k).re
  have hvar := (abs_le.mp (gammaClippedError_variation_bound hRH hx hh hhx)).1
  rw [hs] at hvar
  have hraw := gammaClippedRawError_variation_eq hx
  have hnorm :=
    AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum_normalized_eq_main_add_error hx0
  rw [hs] at hnorm
  have hmass : (293 / 320 : ℝ) ≤
      ∫ u in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight u := by
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
  have hprincipal := LLS.clippedShiftPrincipalLower_ge_mass133
    (r ^ 2) ((2 / 25) * r ^ 2)
  have hactual := LLS.clippedShiftPrincipalLower_le_actual hRH hx hh hhx
  rw [hs] at hprincipal hactual
  have hP : (133 / 160 : ℝ) * r - (E + atom) / r ≤ 2 * T - P :=
    hprincipal.trans hactual
  have hc0 : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by nlinarith only [Real.pi_gt_three] : (1 : ℝ) ≤ 2 * Real.pi)
  have hc : Real.log (2 * Real.pi) ≤ (1839 / 1000 : ℝ) :=
    Analysis.log_two_mul_pi_lt.le
  have he : Real.exp (-(1 / r ^ 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (one_div_nonneg.mpr (sq_nonneg r)))
  have hatom : atom ≤ (1839 / 1000 : ℝ) := by
    exact (mul_le_mul_of_nonneg_left he hc0).trans (by simpa only [mul_one] using hc)
  have hcoeff : (2 * V + E) / 3 =
      (71 / 80 - 86733 / 98800 : ℝ) * r ^ 2 + (10148557 / 11856000 : ℝ) * r +
      (5754559 / 494000 : ℝ) - (1 + 56 / 494) * (1839 / 1000) +
      (56 / 494) * Real.log (2 * Real.pi) := by
    dsimp only [V, E, LLS.clippedShiftPrincipalErrorNumerator,
      LLS.logShiftRampIncrement, LLS.logShiftRampEnvelope]
    rw [hs]
    field_simp [pow_ne_zero 2 hr0.ne']
    ring
  have hcost : (2 * V + E) / 3 + atom ≤
      (71 / 80 - 86733 / 98800 : ℝ) * r ^ 2 +
      (10148557 / 11856000 : ℝ) * r + 5754559 / 494000 := by
    linarith only [hcoeff, hc, hatom]
  have hTr := mul_le_mul_of_nonneg_right hT hr0.le
  have hPr := mul_le_mul_of_nonneg_right hP hr0.le
  rw [sub_mul, div_mul_cancel₀ _ hr0.ne'] at hTr hPr
  have hid : ((86733 / 98800 : ℝ) * r - 10148557 / 11856000 -
      (5754559 / 494000) / r) * r =
      (86733 / 98800 : ℝ) * r ^ 2 - (10148557 / 11856000 : ℝ) * r - 5754559 / 494000 := by
    field_simp [hr0.ne']
  apply (mul_le_mul_iff_right₀ hr0).mp
  change r * _ ≤ r * ((4 * T - P) / 3)
  nlinarith only [hTr, hPr, hcost, hid]

/-- The sharper Gamma scalar gap K1*r-mu*L-D1-(7L/6+T1)/r.
It retains prefix credit 423/100 and the unrounded reciprocal main coefficients.
A nonnegative gap controls the actual signed budget with strictness preserved. -/
noncomputable def gammaSharpGap (L r : ℝ) : ℝ :=
  (86733 / 98800 : ℝ) * r - (11783423 / 25000000 : ℝ) * L - 38128717 / 11856000 -
    ((7 / 6 : ℝ) * L + 20475759 / 494000) / r

/-- The positive quadratic root of the sharper gap at logarithmic scale L.
Its certified domain begins at L=100. The root bound is proved algebraically
before any tail estimate is used, avoiding a circular size assumption. -/
noncomputable def gammaSharpRoot (L : ℝ) : ℝ :=
  ((11783423 / 25000000 : ℝ) * L + 38128717 / 11856000 +
    Real.sqrt (((11783423 / 25000000 : ℝ) * L + 38128717 / 11856000) ^ 2 +
      4 * (86733 / 98800 : ℝ) * ((7 / 6 : ℝ) * L + 20475759 / 494000))) /
    (2 * (86733 / 98800 : ℝ))

/-- The witness cutoff (99/40)*gammaSharpRoot(L)^2.
For L>=100 its root exceeds 60, making the prefix floor inactive.
The all-input witness theorem uses this single expression. -/
noncomputable def gammaSharpBound (L : ℝ) : ℝ := (99 / 40 : ℝ) * gammaSharpRoot L ^ 2

/-- For L>=100, the sharper root is positive.
Its numerator has positive linear part and positive discriminant.
The denominator is positive. -/
theorem gammaSharpRoot_pos {L : ℝ} (hL : 100 ≤ L)
    : 0 < gammaSharpRoot L := by
  have hD : (0 : ℝ) ≤ 38128717 / 11856000 := by norm_num only
  have hL0 : 0 < L := by linarith only [hL]
  have hB : 0 < (11783423 / 25000000 : ℝ) * L + (38128717 / 11856000) := by
    have hmul := mul_pos (by norm_num only : (0 : ℝ) < 11783423 / 25000000) hL0
    linarith only [hmul, hD]
  have hA : 0 < (7 / 6 : ℝ) * L + 20475759 / 494000 := by
    apply add_pos
    · exact mul_pos (by norm_num only) hL0
    · norm_num only
  have hK : 0 < (86733 / 98800 : ℝ) := by norm_num only
  have hdisc :
    0 <
      ((11783423 / 25000000 : ℝ) * L + (38128717 / 11856000)) ^ 2 +
        4 * (86733 / 98800 : ℝ) * ((7 / 6 : ℝ) * L + 20475759 / 494000) := by
    apply add_pos
    · exact sq_pos_of_pos hB
    · exact mul_pos (mul_pos (by norm_num only) hK) hA
  dsimp only [gammaSharpRoot]
  apply div_pos
  · exact add_pos hB (Real.sqrt_pos.mpr hdisc)
  · exact mul_pos (by norm_num only) hK


/-- For L>=100, the sharper root makes the scalar gap vanish.
Square the discriminant identity, obtain the quadratic equation, and divide by the positive root. -/
theorem gammaSharpGap_root_eq_zero {L : ℝ} (hL : 100 ≤ L)
    :
    gammaSharpGap L (gammaSharpRoot L) = 0 := by
  have hD : (0 : ℝ) ≤ 38128717 / 11856000 := by norm_num only
  let b : ℝ := (11783423 / 25000000 : ℝ) * L + (38128717 / 11856000)
  let A : ℝ := (7 / 6 : ℝ) * L + 20475759 / 494000
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
  have hrEq : gammaSharpRoot L = r := by
    dsimp only [gammaSharpRoot, r, disc, b, A, K]
  have hquad : K * r ^ 2 - b * r - A = 0 := by
    dsimp only [r]
    have hK0 : K ≠ 0 := ne_of_gt hK
    field_simp [hK0]
    dsimp only [disc] at hs
    nlinarith only [hs]
  have hmul : gammaSharpGap L r * r = 0 := by
    rw [gammaSharpGap]
    dsimp only [A, b, K] at hquad ⊢
    field_simp [hr.ne']
    nlinarith only [hquad]
  rw [hrEq]
  exact (mul_eq_zero.mp hmul).resolve_right hr.ne'


/-- For L>=100, any radius at least the sharper root has nonnegative gap.
Factor the gap difference into nonnegative radius distance and positive slope. -/
theorem gammaSharpGap_nonneg_of_root_le {L r : ℝ} (hL : 100 ≤ L)
    (hr : gammaSharpRoot L ≤ r) :
    0 ≤ gammaSharpGap L r := by
  let rho := gammaSharpRoot L
  have hrho : 0 < rho := gammaSharpRoot_pos hL
  have hr' : 0 < r := lt_of_lt_of_le hrho hr
  have hL0 : 0 < L := by linarith only [hL]
  have hA : 0 < (7 / 6 : ℝ) * L + 20475759 / 494000 := by
    apply add_pos
    · exact mul_pos (by norm_num only) hL0
    · norm_num only
  have hK : 0 < (86733 / 98800 : ℝ) := by norm_num only
  have hid :
    gammaSharpGap L r - gammaSharpGap L rho =
      ((86733 / 98800 : ℝ) + ((7 / 6 : ℝ) * L + 20475759 / 494000) / (r * rho)) * (r - rho) := by
    simp only [gammaSharpGap]
    field_simp [hr'.ne', hrho.ne']
    ring_nf
  have hdiff : 0 ≤
      ((86733 / 98800 : ℝ) + ((7 / 6 : ℝ) * L + 20475759 / 494000) / (r * rho)) *
      (r - rho) := by
    apply mul_nonneg
    · exact add_nonneg hK.le (div_nonneg hA.le (mul_nonneg hr'.le hrho.le))
    · exact sub_nonneg.mpr hr
  have hroot : gammaSharpGap L rho = 0 := by
    dsimp only [rho]
    exact gammaSharpGap_root_eq_zero hL
  rw [hroot] at hid
  linarith only [hid, hdiff]


/-- For L>=100 and positive test radius, a nonnegative gap bounds the sharper root above.
A radius below the root would give a strictly positive root-to-test gap difference. -/
theorem gammaSharpRoot_le_of_gap_nonneg {L r : ℝ} (hL : 100 ≤ L)
    (hr : 0 < r) (hgap : 0 ≤ gammaSharpGap L r) :
    gammaSharpRoot L ≤ r := by
  by_contra hnot
  have hlt : r < gammaSharpRoot L := lt_of_not_ge hnot
  let rho := gammaSharpRoot L
  have hrho : 0 < rho := gammaSharpRoot_pos hL
  have hL0 : 0 < L := by linarith only [hL]
  have hA : 0 < (7 / 6 : ℝ) * L + 20475759 / 494000 := by
    apply add_pos
    · exact mul_pos (by norm_num only) hL0
    · norm_num only
  have hK : 0 < (86733 / 98800 : ℝ) := by norm_num only
  have hid :
    gammaSharpGap L rho - gammaSharpGap L r =
      ((86733 / 98800 : ℝ) + ((7 / 6 : ℝ) * L + 20475759 / 494000) / (r * rho)) * (rho - r) := by
    simp only [gammaSharpGap]
    field_simp [hr.ne', hrho.ne']
    ring_nf
  have hdiff : 0 <
      ((86733 / 98800 : ℝ) + ((7 / 6 : ℝ) * L + 20475759 / 494000) / (r * rho)) *
      (rho - r) := by
    apply mul_pos
    · exact add_pos hK (div_pos hA (mul_pos hr hrho))
    · exact sub_pos.mpr hlt
  have hroot : gammaSharpGap L rho = 0 := by
    dsimp only [rho]
    exact gammaSharpGap_root_eq_zero hL
  rw [hroot] at hid
  linarith only [hid, hdiff, hgap]


/-- For L>=100, the sharper root is strictly greater than 60.
Its gap at 60 is negative throughout the half-line, contradicting root<=60.
This purely algebraic size estimate precedes the analytic tail estimate. -/
theorem gammaSharpRoot_gt_sixty {L : ℝ} (hL : 100 ≤ L) : (60 : ℝ) < gammaSharpRoot L := by
  by_contra h
  have hg := gammaSharpGap_nonneg_of_root_le hL (le_of_not_gt h)
  dsimp only [gammaSharpGap] at hg
  linarith only [hg, hL]

/-- Under GRH, every odd composite n>1 with log n>=100 has a prime rejecting strong MR
within gammaSharpBound(log n). Use prefix 423/100, the width-2/25 main estimate,
and the root>60 tail bound in the generic all-input signed-prefix consumer.
The actual common-cost bound remains strict even though the scalar root gap is zero. -/
theorem exists_prime_gammaSharp {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 100 ≤ Real.log n) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ gammaSharpBound (Real.log n) ∧
      ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  let r := gammaSharpRoot (Real.log n)
  have hr60 : (60 : ℝ) < r := gammaSharpRoot_gt_sixty hL
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
  have htail0 := LLS.PaperStatements.rpow_neg_nine_sixteenths_le_div_scale_sqrt
    (a := 5 / 3) (by norm_num only : (0 : ℝ) < 5 / 3)
    (by norm_num only; nlinarith only [hr60] : (5 / 3 : ℝ) ^ 16 ≤ r ^ 2)
  rw [hs] at htail0
  have htail : 43 * (r ^ 2) ^ (-9 / 16 : ℝ) ≤ (129 / 5) / r := by
    calc
      _ ≤ 43 * (1 / ((5 / 3) * r)) :=
        mul_le_mul_of_nonneg_left htail0 (by norm_num only)
      _ = _ := by
        field_simp [hr0.ne']
        norm_num only
  have hpref := LLS.gamma_prefix1000_sharp hGRH.riemann (le_refl (1000 : ℝ))
  have hg : 0 ≤ gammaSharpGap (Real.log n) r := by
    rw [gammaSharpGap_root_eq_zero hL]
  have hu := gammaSignedPrefixMRBudget_lt_precise_common_cost hGRH.riemann n n (r ^ 2) 1000
  rw [hs] at hu
  have hid : ((7 / 6 : ℝ) * Real.log n + 20475759 / 494000) / r =
      ((7 / 6 : ℝ) * Real.log n + 4) / r + (129 / 5) / r + (5754559 / 494000) / r := by
    ring
  have hbudget : gammaSignedPrefixMRBudget n n (r ^ 2) 1000 <
      (86733 / 98800 : ℝ) * r - 10148557 / 11856000 - (5754559 / 494000) / r := by
    dsimp only [gammaSharpGap] at hg
    linarith only [hu, hpref, htail, hg, hid]
  have hmain := gammaSharpFourT_lower hGRH.riemann hr
  have hactual : gammaSignedPrefixMRBudget n n (r ^ 2) 1000 <
      (4 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum (r ^ 2) /
        Real.sqrt (r ^ 2)) -
        (∑' k : ℕ, LLS.PaperStatements.gammaMellinKernel.summand
          (1 : DirichletCharacter ℂ 1) (r ^ 2) k).re) / 3 := by
    rw [hs]
    exact hbudget.trans_le hmain
  exact exists_prime_witness_of_signed_prefix_gap_all_inputs hn ho hc hn9 hGRH hQ hx
    (by norm_num only) (by nlinarith only [hr60]) hactual

/-- Under the sharper Gamma assumptions, the least rejecting prime is within gammaSharpBound.
Apply least-prime extraction to the actual rejecting-prime theorem.
No squarefreeness, subgroup index, Korselt or prime-factor count assumption is exposed. -/
theorem exists_least_gammaSharp {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 100 ≤ Real.log n) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ gammaSharpBound (Real.log n) ∧
      ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
      ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  exact exists_least_prime_reject_of_exists_prime_reject
    (exists_prime_gammaSharp hn ho hc hGRH hL)

end PseudoPrime.PrimeTestBounds.MillerRabin
