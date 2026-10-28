/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaReflectedPrefixBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaSharpComparison

/-! # The reflected signed-prefix Gamma root and actual witnesses -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The signed-prefix gap with reflected reciprocal constant 58129633/2223000.
It retains prefix 423/100, width 2/25 and all main coefficients, changing only
the rigorously connected reflected tail. Its positive root supplies the cutoff. -/
noncomputable def gammaReflectedGap (L r : ℝ) : ℝ :=
  (86733 / 98800 : ℝ) * r - (11783423 / 25000000 : ℝ) * L - 38128717 / 11856000 -
    ((7 / 6 : ℝ) * L + 58129633 / 2223000) / r

/-- The positive quadratic root of the reflected signed-prefix gap. The
certified domain begins at L=100; the lower bound sixty is established
algebraically before the analytic tail is used. -/
noncomputable def gammaReflectedRoot (L : ℝ) : ℝ :=
  ((11783423 / 25000000 : ℝ) * L + 38128717 / 11856000 +
      Real.sqrt
        (((11783423 / 25000000 : ℝ) * L + 38128717 / 11856000) ^ 2 +
          4 * (86733 / 98800 : ℝ) * ((7 / 6 : ℝ) * L + 58129633 / 2223000))) /
    (2 * (86733 / 98800 : ℝ))

/-- The witness cutoff (99/40) times the square of the reflected root.
For L>=100 its root exceeds sixty and includes the entire 1000 prefix.
The all-input witness theorem uses this single expression. -/
noncomputable def gammaReflectedBound (L : ℝ) : ℝ :=
  (99 / 40 : ℝ) * gammaReflectedRoot L ^ 2

/-- For L>=100, the reflected root is positive. Its positive linear
numerator and nonnegative discriminant have a positive denominator. -/
theorem gammaReflectedRoot_pos {L : ℝ} (hL : 100 ≤ L) : 0 < gammaReflectedRoot L := by
  have hD : (0 : ℝ) ≤ 38128717 / 11856000 := by norm_num only
  have hL0 : 0 < L := by linarith only [hL]
  have hB : 0 < (11783423 / 25000000 : ℝ) * L + (38128717 / 11856000) := by
    have hmul := mul_pos (by norm_num only : (0 : ℝ) < 11783423 / 25000000) hL0
    linarith only [hmul, hD]
  have hA : 0 < (7 / 6 : ℝ) * L + 58129633 / 2223000 := by
    apply add_pos
    · exact mul_pos (by norm_num only) hL0
    · norm_num only
  have hK : 0 < (86733 / 98800 : ℝ) := by norm_num only
  have hdisc :
    0 <
      ((11783423 / 25000000 : ℝ) * L + (38128717 / 11856000)) ^ 2 +
        4 * (86733 / 98800 : ℝ) * ((7 / 6 : ℝ) * L + 58129633 / 2223000) := by
    apply add_pos
    · exact sq_pos_of_pos hB
    · exact mul_pos (mul_pos (by norm_num only) hK) hA
  dsimp only [gammaReflectedRoot]
  apply div_pos
  · exact add_pos hB (Real.sqrt_pos.mpr hdisc)
  · exact mul_pos (by norm_num only) hK

/-- For L>=100, the reflected root makes the scalar gap zero. Square
the discriminant identity and divide its exact quadratic equation by
the positive root. No analytic tail bound is used in this step. -/
theorem gammaReflectedGap_root_eq_zero {L : ℝ} (hL : 100 ≤ L) :
    gammaReflectedGap L (gammaReflectedRoot L) = 0 := by
  have hD : (0 : ℝ) ≤ 38128717 / 11856000 := by norm_num only
  let b : ℝ := (11783423 / 25000000 : ℝ) * L + (38128717 / 11856000)
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
  have hrEq : gammaReflectedRoot L = r := by dsimp only [gammaReflectedRoot, r, disc, b, A, K]
  have hquad : K * r ^ 2 - b * r - A = 0 := by
    dsimp only [r]
    have hK0 : K ≠ 0 := ne_of_gt hK
    field_simp [hK0]
    dsimp only [disc] at hs
    nlinarith only [hs]
  have hmul : gammaReflectedGap L r * r = 0 := by
    rw [gammaReflectedGap]
    dsimp only [A, b, K] at hquad ⊢
    field_simp [hr.ne']
    nlinarith only [hquad]
  rw [hrEq]
  exact (mul_eq_zero.mp hmul).resolve_right hr.ne'

/-- For L>=100, every radius above the reflected root has nonnegative
gap. Factor the difference from its zero root into a nonnegative
radius increment and a positive slope. -/
theorem gammaReflectedGap_nonneg_of_root_le {L r : ℝ} (hL : 100 ≤ L)
    (hr : gammaReflectedRoot L ≤ r) : 0 ≤ gammaReflectedGap L r := by
  let rho := gammaReflectedRoot L
  have hrho : 0 < rho := gammaReflectedRoot_pos hL
  have hr' : 0 < r := lt_of_lt_of_le hrho hr
  have hL0 : 0 < L := by linarith only [hL]
  have hA : 0 < (7 / 6 : ℝ) * L + 58129633 / 2223000 := by
    apply add_pos
    · exact mul_pos (by norm_num only) hL0
    · norm_num only
  have hK : 0 < (86733 / 98800 : ℝ) := by norm_num only
  have hid :
    gammaReflectedGap L r - gammaReflectedGap L rho =
      ((86733 / 98800 : ℝ) + ((7 / 6 : ℝ) * L + 58129633 / 2223000) / (r * rho)) * (r - rho) := by
    simp only [gammaReflectedGap]
    field_simp [hr'.ne', hrho.ne']
    ring_nf
  have hdiff :
    0 ≤ ((86733 / 98800 : ℝ) + ((7 / 6 : ℝ) * L + 58129633 / 2223000) / (r * rho)) * (r - rho) := by
    apply mul_nonneg
    · exact add_nonneg hK.le (div_nonneg hA.le (mul_nonneg hr'.le hrho.le))
    · exact sub_nonneg.mpr hr
  have hroot : gammaReflectedGap L rho = 0 := by
    dsimp only [rho]
    exact gammaReflectedGap_root_eq_zero hL
  rw [hroot] at hid
  linarith only [hid, hdiff]

/-- For L>=100 and a positive test radius, a nonnegative reflected
gap bounds the root above. A smaller test radius would give a strictly
positive root-to-test gap difference and a contradiction. -/
theorem gammaReflectedRoot_le_of_gap_nonneg {L r : ℝ} (hL : 100 ≤ L) (hr : 0 < r)
    (hgap : 0 ≤ gammaReflectedGap L r) : gammaReflectedRoot L ≤ r := by
  by_contra hnot
  have hlt : r < gammaReflectedRoot L := lt_of_not_ge hnot
  let rho := gammaReflectedRoot L
  have hrho : 0 < rho := gammaReflectedRoot_pos hL
  have hL0 : 0 < L := by linarith only [hL]
  have hA : 0 < (7 / 6 : ℝ) * L + 58129633 / 2223000 := by
    apply add_pos
    · exact mul_pos (by norm_num only) hL0
    · norm_num only
  have hK : 0 < (86733 / 98800 : ℝ) := by norm_num only
  have hid :
    gammaReflectedGap L rho - gammaReflectedGap L r =
      ((86733 / 98800 : ℝ) + ((7 / 6 : ℝ) * L + 58129633 / 2223000) / (r * rho)) * (rho - r) := by
    simp only [gammaReflectedGap]
    field_simp [hr.ne', hrho.ne']
    ring_nf
  have hdiff :
    0 < ((86733 / 98800 : ℝ) + ((7 / 6 : ℝ) * L + 58129633 / 2223000) / (r * rho)) * (rho - r) := by
    apply mul_pos
    · exact add_pos hK (div_pos hA (mul_pos hr hrho))
    · exact sub_pos.mpr hlt
  have hroot : gammaReflectedGap L rho = 0 := by
    dsimp only [rho]
    exact gammaReflectedGap_root_eq_zero hL
  rw [hroot] at hid
  linarith only [hid, hdiff, hgap]

/-- For L>=100, the reflected root strictly exceeds sixty. The gap
at sixty is negative on the whole half-line, so root monotonicity
excludes a smaller root before any tail estimate is applied. -/
theorem gammaReflectedRoot_gt_sixty {L : ℝ} (hL : 100 ≤ L) : (60 : ℝ) < gammaReflectedRoot L := by
  by_contra h
  have hg := gammaReflectedGap_nonneg_of_root_le hL (le_of_not_gt h)
  dsimp only [gammaReflectedGap] at hg
  linarith only [hg, hL]

/-- Under GRH, every odd composite n>1 with log n>=100 has an actual
rejecting prime within the reflected Gamma cutoff. Use the unchanged
sharp prefix main term and the new reflected-budget consumer. Strict
common cost supplies the required strict gap at the scalar root. -/
theorem exists_prime_gammaReflected {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 100 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ gammaReflectedBound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  let r := gammaReflectedRoot (Real.log n)
  have hr60 : (60 : ℝ) < r := gammaReflectedRoot_gt_sixty hL
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
        field_simp [hr0.ne']
        norm_num only
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
  have hpref := LLS.gamma_prefix1000_sharp hGRH.riemann (le_refl (1000 : ℝ))
  have hg : 0 ≤ gammaReflectedGap (Real.log n) r := by rw [gammaReflectedGap_root_eq_zero hL]
  have hu := gammaReflectedBudget_lt_common hGRH.riemann n n (r ^ 2) 1000
  rw [hs] at hu
  have hid :
    ((7 / 6 : ℝ) * Real.log n + 58129633 / 2223000) / r =
      ((7 / 6 : ℝ) * Real.log n + 4) / r + (21 / 2 + 1 / 3600 : ℝ) / r +
        (5754559 / 494000) / r := by
    ring
  have hbudget :
    gammaReflectedMRBudget n n (r ^ 2) 1000 <
      (86733 / 98800 : ℝ) * r - 10148557 / 11856000 - (5754559 / 494000) / r := by
    dsimp only [gammaReflectedGap] at hg
    linarith only [hu, hpref, htail, hg, hid]
  have hmain := gammaSharpFourT_lower hGRH.riemann hr
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
theorem exists_least_gammaReflected {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 100 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ gammaReflectedBound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  exact
    exists_least_prime_reject_of_exists_prime_reject (exists_prime_gammaReflected hn ho hc hGRH hL)

end PseudoPrime.PrimeTestBounds.MillerRabin
