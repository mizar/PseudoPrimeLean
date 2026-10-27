/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TwoPolePrimeTrivialNumerics
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeFactorCountBounds

/-! # Negative prime witnesses with the conductor and level-prime costs combined -/

@[expose] public section

namespace PseudoPrime.LLS

/-- At scale at least four, the empty-prefix quadratic upper budget is bounded by
its level-only version plus the prime-count ramp cost. Absorb the conductor gap
with coefficient 1/2+(3/2)x^(-9/16). No RH or triviality assumption is needed. -/
theorem generalTwoPoleUpper_empty_le_prime_count {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hquad : χ.IsQuadratic) {x : ℝ} (hx : 4 ≤ x) :
    generalTwoPoleGammaUpper χ ∅ x ≤
      twoPolePrimeTrivialUpper q ∅ x +
        (q.primeFactors.card : ℝ) * Real.log ((99 / 40 : ℝ) * x) / Real.sqrt x := by
  have hx0 : 0 < x := by linarith only [hx]
  have hs : 2 ≤ Real.sqrt x := by nlinarith only [Real.sq_sqrt hx0.le, Real.sqrt_nonneg x, hx]
  have hp := Real.rpow_nonneg hx0.le (-9 / 16 : ℝ)
  have hm : 1 ≤ (1 / 2 + (3 / 2 : ℝ) * x ^ (-9 / 16 : ℝ)) * Real.sqrt x := by
    nlinarith only [hs, mul_nonneg hp (Real.sqrt_nonneg x)]
  have hc : 1 ≤ (99 / 40 : ℝ) * x := by linarith only [hx]
  have h := gammaQuadraticLocalCorrection_absorb_conductor χ hquad hx0 hc hm
  dsimp only [generalTwoPoleGammaUpper, twoPolePrimeTrivialUpper,
    AnalyticNumberTheory.Arithmetic.excludedCharacterDefect]
  simp only [Finset.sum_empty, Finset.filter_empty, mul_zero, sub_zero, add_zero]
  nlinarith only [h]

/-- For a level q at most A and scale at least four, retain the original level's
prime count and enlarge the remaining budget to A. Logarithmic monotonicity in
nonnegative factors gives a common bound even for small primitive conductors. -/
theorem generalTwoPoleUpper_empty_le_ambient_prime_count {q A : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hqA : q ≤ A) {x : ℝ} (hx : 4 ≤ x) :
    generalTwoPoleGammaUpper χ ∅ x ≤
      twoPolePrimeTrivialUpper A ∅ x +
        (q.primeFactors.card : ℝ) * Real.log ((99 / 40 : ℝ) * x) / Real.sqrt x := by
  have h0 := generalTwoPoleUpper_empty_le_prime_count χ hquad hx
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hl := Real.log_le_log (Nat.cast_pos.mpr hqpos) (Nat.cast_le.mpr hqA)
  have hm :=
    Real.log_le_log (Nat.cast_pos.mpr (lt_of_lt_of_le hqpos (le_max_right 20000 q)))
      (Nat.cast_le.mpr (max_le_max (le_refl 20000) hqA))
  have hp := Real.rpow_nonneg (by linarith only [hx] : 0 ≤ x) (-9 / 16 : ℝ)
  have hd :=
    div_le_div_of_nonneg_right
      (show
        (7 / 6 : ℝ) * Real.log (max 20000 q : ℕ) + 4 ≤ (7 / 6 : ℝ) * Real.log (max 20000 A : ℕ) + 4
        by linarith only [hm])
      (Real.sqrt_nonneg x)
  have hr := mul_le_mul_of_nonneg_left hl hp
  have hu : twoPolePrimeTrivialUpper q ∅ x ≤ twoPolePrimeTrivialUpper A ∅ x := by
    dsimp only [twoPolePrimeTrivialUpper]
    linarith only [hl, hd, hr]
  exact h0.trans (add_le_add hu (le_refl _))

/-- For real L at least 3000 and root 5L/8+20, the scale is at least four and both
endpoint logarithms are at most L/160. Use the tangent at 10000 and rational root
bounds. These data control the principal errors and prime-count ramp cost. -/
theorem twoPole_negative_root_data {L : ℝ} (hL : 3000 ≤ L) :
    let r := (5 / 8 : ℝ) * L + 20;
    4 ≤ r ^ 2 ∧
      (3 / 5 : ℝ) * L + 18 ≤ r ∧
      Real.log ((99 / 40 : ℝ) * r ^ 2) ≤ L / 160 ∧ Real.log ((101 / 40 : ℝ) * r ^ 2) ≤ L / 160 := by
  let r := (5 / 8 : ℝ) * L + 20
  have hr : 0 < r := by
    dsimp only [r]; linarith only [hL]
  have hlow : (3 / 5 : ℝ) * L + 18 ≤ r := by
    dsimp only [r]; linarith only [hL]
  have hhi : r ≤ (79 / 125 : ℝ) * L := by
    dsimp only [r]; linarith only [hL]
  have hs := mul_self_le_mul_self hr.le hhi
  have hx : 4 ≤ r ^ 2 := by nlinarith only [hlow, hL, sq_nonneg (r - 2)]
  have hLp : 0 < L := by linarith only [hL]
  have ht := Real.log_le_sub_one_of_pos (div_pos hLp (by norm_num only : (0 : ℝ) < 10000))
  rw [Real.log_div hLp.ne' (by norm_num only : (10000 : ℝ) ≠ 0)] at ht
  have h10000 : Real.log (10000 : ℝ) ≤ 19 / 2 := by
    rw [show (10000 : ℝ) = 100 ^ 2 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [twoPole_log_hundred_le_nineteen_fourths]
  have hlog : 2 * Real.log L + 1 / 100 ≤ L / 160 := by linarith only [ht, h10000, hL]
  have haux : Real.log ((101 / 40 : ℝ) * r ^ 2) ≤ 2 * Real.log L + 1 / 100 := by
    have h :=
      Real.log_le_log
        (mul_pos (by norm_num only : (0 : ℝ) < 101 / 40)
          (zero_lt_one.trans_le (by linarith only [hx] : 1 ≤ r ^ 2)))
        (show (101 / 40 : ℝ) * r ^ 2 ≤ (101 / 100 : ℝ) * L ^ 2 by nlinarith only [hs])
    rw [Real.log_mul (by norm_num only : (101 / 100 : ℝ) ≠ 0) (pow_ne_zero 2 hLp.ne'),
      Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    have hc := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 101 / 100)
    linarith only [h, hc]
  have hsmall : Real.log ((99 / 40 : ℝ) * r ^ 2) ≤ Real.log ((101 / 40 : ℝ) * r ^ 2) :=
    Real.log_le_log (by nlinarith only [hx]) (by nlinarith only [hx])
  exact ⟨hx, hlow, hsmall.trans (haux.trans hlog), haux.trans hlog⟩

/-- For positive q at most A with log A at least 3000, bound the number of level
primes by two thirds of log A. Use the large-level estimate or bound small levels
through log 20000. This lets one ambient scale include every input below B. -/
theorem primeFactors_card_le_two_thirds_ambient_log {q A : ℕ} (hq : 0 < q) (hqA : q ≤ A)
    (hL : 3000 ≤ Real.log A) : (q.primeFactors.card : ℝ) ≤ (2 / 3 : ℝ) * Real.log A := by
  have hlog := Real.log_le_log (Nat.cast_pos.mpr hq) (Nat.cast_le.mpr hqA)
  by_cases hlarge : 20000 ≤ q
  · have hc := AnalyticNumberTheory.Arithmetic.card_primeFactors_le_two_thirds_log hlarge
    linarith only [hc, hlog]
  · have hqsmall : (q : ℝ) ≤ 100 ^ 3 := by
      exact_mod_cast ((le_of_not_ge hlarge).trans (by norm_num only : (20000 : ℕ) ≤ 100 ^ 3))
    have h := Real.log_le_log (Nat.cast_pos.mpr hq) hqsmall
    rw [Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    have hlq : Real.log q ≤ 15 := by linarith only [h, twoPole_log_hundred_le_nineteen_fourths]
    have hc := AnalyticNumberTheory.DirichletLFunction.card_primeFactors_le_log_div_log_two hq
    have h2 : 1 / 2 ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
    have hh := (le_div_iff₀ (by linarith only [h2] : 0 < Real.log 2)).mp hc
    have hn : 0 ≤ (q.primeFactors.card : ℝ) := Nat.cast_nonneg _
    nlinarith only [hh, h2, hn, hlq, hL]

/-- For a quadratic character of positive level at most A with log A at least 3000,
the general empty-prefix two-pole separation is positive at root 5log(A)/8+20.
Combine the quantitative level-only margin with a local cost at most log(A)/144.
This numerical result needs no GRH and feeds the negative-prime witness theorem. -/
theorem generalTwoPoleSeparation_negative_affine_pos {q A : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hqA : q ≤ A) (hL : 3000 ≤ Real.log A) :
    0 < generalTwoPoleGammaSeparation χ ∅ (((5 / 8 : ℝ) * Real.log A + 20) ^ 2) := by
  let L := Real.log A
  let r := (5 / 8 : ℝ) * L + 20
  have hd := twoPole_negative_root_data hL
  have hr : 0 < r := by
    dsimp only [r, L]; linarith only [hL]
  have hL0 : 0 ≤ L := by
    dsimp only [L]; linarith only [hL]
  have hx : 4 ≤ r ^ 2 := hd.1
  have hroot : (3 / 5 : ℝ) * L + 18 ≤ r := hd.2.1
  have hlog : Real.log ((99 / 40 : ℝ) * r ^ 2) ≤ L / 160 := hd.2.2.1
  have hcard :=
    primeFactors_card_le_two_thirds_ambient_log (Nat.pos_of_ne_zero (NeZero.ne q)) hqA hL
  have hlog0 : 0 ≤ Real.log ((99 / 40 : ℝ) * r ^ 2) := Real.log_nonneg (by nlinarith only [hx])
  have hprod := mul_le_mul hcard hlog hlog0 (show 0 ≤ (2 / 3 : ℝ) * L by linarith only [hL0])
  have hcost :
    (q.primeFactors.card : ℝ) * Real.log ((99 / 40 : ℝ) * r ^ 2) / Real.sqrt (r ^ 2) ≤ L / 144 := by
    rw [Real.sqrt_sq hr.le]
    apply (div_le_iff₀ hr).mpr
    have ht := mul_le_mul_of_nonneg_right hroot hL0
    nlinarith only [hprod, ht, hL0]
  have hu := generalTwoPoleUpper_empty_le_ambient_prime_count χ hquad hqA hx
  have hbase :=
    twoPolePrimeTrivialSeparation_lower (by linarith only [hL] : 1500 ≤ Real.log A) hroot
      (show Real.log ((99 / 40 : ℝ) * r ^ 2) ≤ Real.log A / 40 by linarith only [hlog, hL0])
      (show Real.log ((101 / 40 : ℝ) * r ^ 2) ≤ Real.log A / 40 by linarith only [hd.2.2.2, hL0])
  have hsep :
    twoPolePrimeTrivialSeparation A ∅ (r ^ 2) - L / 144 ≤
      generalTwoPoleGammaSeparation χ ∅ (r ^ 2) := by
    dsimp only [twoPolePrimeTrivialSeparation, generalTwoPoleGammaSeparation]
    linarith only [hu, hcost]
  change 0 < generalTwoPoleGammaSeparation χ ∅ (r ^ 2)
  dsimp only [r, L] at hbase
  dsimp only [L] at hsep
  linarith only [hbase, hsep, hL]

/-- Under GRH, a nonprincipal quadratic character of level q at most A with log A
at least 3000 has a prime not dividing q, below the affine cutoff, with value minus
one. Apply the general ramp contradiction and exclude values zero and one.
The common ambient scale also covers small original levels. -/
theorem exists_prime_neg_one_le_twoPole_ambient {q A : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (hqA : q ≤ A)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 3000 ≤ Real.log A) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬p ∣ q ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * ((5 / 8 : ℝ) * Real.log A + 20) ^ 2 ∧ χ p = -1 := by
  have hd := twoPole_negative_root_data hL
  obtain ⟨p, hp, hn, hb, hv⟩ :=
    exists_prime_not_one_of_generalTwoPole χ hne hGRH
      (by linarith only [hd.1] : 1 ≤ ((5 / 8 : ℝ) * Real.log A + 20) ^ 2) ∅
      (fun k hk ↦ False.elim (Finset.notMem_empty k hk))
      (generalTwoPoleSeparation_negative_affine_pos χ hquad hqA hL)
  have hz : χ p ≠ 0 :=
    MulChar.apply_ne_zero_iff.mpr
      ((ZMod.isUnit_iff_coprime p q).mpr (hp.coprime_iff_not_dvd.mpr hn))
  refine ⟨p, hp, hn, hb, ?_⟩
  rcases hquad (p : ZMod q) with h0 | h1 | hm
  · exact False.elim (hz h0)
  · exact False.elim (hv h1)
  · exact hm

end PseudoPrime.LLS
