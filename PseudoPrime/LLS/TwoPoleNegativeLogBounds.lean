/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TwoPoleNegativeBounds

/-! # Variable-radius negative comparison with logarithmic prime-factor cost -/

@[expose] public section

namespace PseudoPrime.LLS

/-- For every positive real L, log L is at most L/2500+69/10. Bound log 2500
by 79/10 with a thirteen-term positive Taylor sum, then apply the logarithmic
tangent. This controls nonlinear radii on a continuous half-line. -/
theorem twoPole_log_tangent {L : ℝ} (hL : 0 < L) : Real.log L ≤ L / 2500 + 69 / 10 := by
  have hLp : 0 < L := by linarith only [hL]
  have h2500 : Real.log (2500 : ℝ) ≤ 79 / 10 := by
    apply (Real.log_le_iff_le_exp (by norm_num only : (0 : ℝ) < 2500)).mpr
    have ht : (2500 : ℝ) ≤ ∑ k ∈ Finset.range 13, (79 / 10 : ℝ) ^ k / (k.factorial : ℝ) := by
      norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    exact ht.trans (Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 79 / 10) 13)
  have h := Real.log_le_sub_one_of_pos (div_pos hLp (by norm_num only : (0 : ℝ) < 2500))
  rw [Real.log_div hLp.ne' (by norm_num only : (2500 : ℝ) ≠ 0)] at h
  linarith only [h, h2500]

/-- The negative-witness root (500/821)L+(11/4)log L+30. The logarithmic
correction pays for the prime-count local cost while preserving the two-pole
leading coefficient. Later apply this root at the common ambient logarithm. -/
noncomputable def twoPoleNegativeLogRoot (L : ℝ) : ℝ :=
  (500 / 821 : ℝ) * L + (11 / 4 : ℝ) * Real.log L + 30

/-- On positive real inputs, the negative logarithmic root is monotone.
Use monotonicity of log and the positive rational coefficients. This transfers a
common ambient logarithm to an elementary upper radius. -/
theorem twoPoleNegativeLogRoot_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    twoPoleNegativeLogRoot x ≤ twoPoleNegativeLogRoot y := by
  have h := Real.log_le_log hx hxy
  dsimp only [twoPoleNegativeLogRoot]
  linarith only [h, hxy]

/-- For L at least 2250, the negative logarithmic root is at most 79L/125.
Use the global tangent to bound the logarithmic correction. This controls both
endpoint logs and comparison with the logarithmic square. -/
theorem twoPoleNegativeLogRoot_le_linear {L : ℝ} (hL : 2250 ≤ L) :
    twoPoleNegativeLogRoot L ≤ (79 / 125 : ℝ) * L := by
  have h := twoPole_log_tangent (by linarith only [hL] : 0 < L)
  dsimp only [twoPoleNegativeLogRoot]
  linarith only [h, hL]

/-- For real L at least 2250, the logarithmic root gives scale at least four,
lower root 3L/5+18, cutoff log at most 2log L and the second endpoint log at most
L/40. Rational root enclosures and the global tangent control the full half-line. -/
theorem twoPoleNegativeLogRoot_data {L : ℝ} (hL : 2250 ≤ L) :
    4 ≤ (twoPoleNegativeLogRoot L) ^ 2 ∧
      (3 / 5 : ℝ) * L + 18 ≤ twoPoleNegativeLogRoot L ∧
      Real.log ((99 / 40 : ℝ) * (twoPoleNegativeLogRoot L) ^ 2) ≤ 2 * Real.log L ∧
      Real.log ((101 / 40 : ℝ) * (twoPoleNegativeLogRoot L) ^ 2) ≤ L / 40 := by
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith only [hL])
  have ht := twoPole_log_tangent (L := L) (by linarith only [hL])
  have hlo : (3 / 5 : ℝ) * L + 18 ≤ twoPoleNegativeLogRoot L := by
    dsimp only [twoPoleNegativeLogRoot]
    linarith only [hL, hlog0]
  have hhi := twoPoleNegativeLogRoot_le_linear hL
  have hr : 0 ≤ twoPoleNegativeLogRoot L := by linarith only [hlo, hL]
  have hx : 4 ≤ (twoPoleNegativeLogRoot L) ^ 2 := by
    nlinarith only [hlo, hL, sq_nonneg (twoPoleNegativeLogRoot L - 2)]
  have hs := mul_self_le_mul_self hr hhi
  have hLp : 0 < L := by linarith only [hL]
  have ha : Real.log ((99 / 40 : ℝ) * (twoPoleNegativeLogRoot L) ^ 2) ≤ 2 * Real.log L := by
    have h :=
      Real.log_le_log (by nlinarith only [hx] : 0 < (99 / 40 : ℝ) * (twoPoleNegativeLogRoot L) ^ 2)
        (show (99 / 40 : ℝ) * (twoPoleNegativeLogRoot L) ^ 2 ≤ L ^ 2 by nlinarith only [hs])
    rw [Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    exact h
  have hb : Real.log ((101 / 40 : ℝ) * (twoPoleNegativeLogRoot L) ^ 2) ≤ L / 40 := by
    have h :=
      Real.log_le_log (by nlinarith only [hx] : 0 < (101 / 40 : ℝ) * (twoPoleNegativeLogRoot L) ^ 2)
        (show (101 / 40 : ℝ) * (twoPoleNegativeLogRoot L) ^ 2 ≤ (101 / 100 : ℝ) * L ^ 2 by
          nlinarith only [hs])
    rw [Real.log_mul (by norm_num only : (101 / 100 : ℝ) ≠ 0) (pow_ne_zero 2 hLp.ne'),
      Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    have hc := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 101 / 100)
    linarith only [h, hc, ht, hL]
  exact ⟨hx, hlo, ha, hb⟩

/-- For a quadratic character of level q at most A with log A at least 1500,
any root in the stated range and with controlled endpoint logs has an explicit
separation lower bound retaining the actual prime count. Absorb the conductor
first, then combine with the quantitative level-only comparison. No RH is needed. -/
theorem generalTwoPoleSeparation_lower_prime_count {q A : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hquad : χ.IsQuadratic) (hqA : q ≤ A) (hL : 1500 ≤ Real.log A) {r : ℝ}
    (hr : (3 / 5 : ℝ) * Real.log A + 18 ≤ r)
    (hA : Real.log ((99 / 40 : ℝ) * r ^ 2) ≤ Real.log A / 40)
    (hB : Real.log ((101 / 40 : ℝ) * r ^ 2) ≤ Real.log A / 40) :
    (821 / 1000 : ℝ) * r - Real.log A / 2 - 11021 / 450 -
        (q.primeFactors.card : ℝ) * Real.log ((99 / 40 : ℝ) * r ^ 2) / r ≤
      generalTwoPoleGammaSeparation χ ∅ (r ^ 2) := by
  have hx : 4 ≤ r ^ 2 := by nlinarith only [hr, hL, sq_nonneg (r - 2)]
  have hr0 : 0 ≤ r := by linarith only [hr, hL]
  have hu := generalTwoPoleUpper_empty_le_ambient_prime_count χ hquad hqA hx
  rw [Real.sqrt_sq hr0] at hu
  have hl := twoPolePrimeTrivialSeparation_lower hL hr hA hB
  dsimp only [twoPolePrimeTrivialSeparation, generalTwoPoleGammaSeparation] at *
  linarith only [hu, hl]

/-- For positive q at most A with log A at least forty-five, bound the original
level prime count by two thirds of log A. Use the large-level estimate or the
logarithmic small-level bound. This includes every smaller input in one ambient scale. -/
theorem twoPole_prime_count_ambient {q A : ℕ} (hq : 0 < q) (hqA : q ≤ A) (hL : 45 ≤ Real.log A) :
    (q.primeFactors.card : ℝ) ≤ (2 / 3 : ℝ) * Real.log A := by
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

/-- For a quadratic character of positive level at most A with log A at least
2250, the general empty-prefix separation is positive at the logarithmic root.
Retain local cost at most (20/9)log log A instead of rounding it to a linear term.
This numerical theorem is unconditional and feeds negative-prime extraction. -/
theorem generalTwoPoleSeparation_negative_log_pos {q A : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hquad : χ.IsQuadratic) (hqA : q ≤ A) (hL : 2250 ≤ Real.log A) :
    0 < generalTwoPoleGammaSeparation χ ∅ (twoPoleNegativeLogRoot (Real.log A) ^ 2) := by
  let L := Real.log A
  let r := twoPoleNegativeLogRoot L
  have hd := twoPoleNegativeLogRoot_data hL
  have hL0 : 0 ≤ L := by
    dsimp only [L]; linarith only [hL]
  have hl0 : 0 ≤ Real.log L :=
    Real.log_nonneg
      (by
        dsimp only [L]; linarith only [hL])
  have hr : 0 < r := by
    have hroot : (3 / 5 : ℝ) * L + 18 ≤ r := hd.2.1
    linarith only [hroot, hL0]
  have hcard :=
    twoPole_prime_count_ambient (Nat.pos_of_ne_zero (NeZero.ne q)) hqA
      (by linarith only [hL] : 45 ≤ Real.log A)
  have hlog : Real.log ((99 / 40 : ℝ) * r ^ 2) ≤ 2 * Real.log L := hd.2.2.1
  have hlog0 : 0 ≤ Real.log ((99 / 40 : ℝ) * r ^ 2) := Real.log_nonneg (by nlinarith only [hd.1])
  have hprod := mul_le_mul hcard hlog hlog0 (show 0 ≤ (2 / 3 : ℝ) * L by linarith only [hL0])
  have hcost :
    (q.primeFactors.card : ℝ) * Real.log ((99 / 40 : ℝ) * r ^ 2) / r ≤
      (20 / 9 : ℝ) * Real.log L := by
    apply (div_le_iff₀ hr).mpr
    have hroot : (3 / 5 : ℝ) * L + 18 ≤ r := hd.2.1
    have ht := mul_le_mul_of_nonneg_right hroot hl0
    nlinarith only [hprod, ht, hl0]
  have ht := twoPole_log_tangent (L := L) (by linarith only [hL])
  have hlow :=
    generalTwoPoleSeparation_lower_prime_count χ hquad hqA
      (by linarith only [hL] : 1500 ≤ Real.log A) hd.2.1
      (show Real.log ((99 / 40 : ℝ) * r ^ 2) ≤ Real.log A / 40 by linarith only [hlog, ht, hL])
      hd.2.2.2
  have he : (821 / 1000 : ℝ) * r - L / 2 = (9031 / 4000 : ℝ) * Real.log L + 2463 / 100 := by
    dsimp only [r, twoPoleNegativeLogRoot]
    ring
  change 0 < generalTwoPoleGammaSeparation χ ∅ (r ^ 2)
  linarith only [hlow, hcost, he, hl0]

/-- For L at least 2250, the logarithmic negative root is smaller than 5L/8+20.
Apply the global tangent to its log term. This proves the new radius dominates
the previous affine result throughout that result's domain. -/
theorem twoPoleNegativeLogRoot_lt_affine {L : ℝ} (hL : 2250 ≤ L) :
    twoPoleNegativeLogRoot L < (5 / 8 : ℝ) * L + 20 := by
  have ht := twoPole_log_tangent (L := L) (by linarith only [hL])
  dsimp only [twoPoleNegativeLogRoot]
  linarith only [ht, hL]

/-- Under GRH, a nonprincipal quadratic character of level q at most A with
log A at least 2250 has a prime not dividing q below the logarithmic two-pole
cutoff with value minus one. Apply the general separation and exclude zero and
one. The common ambient scale permits small original levels. -/
theorem exists_prime_neg_one_le_twoPole_log_ambient {q A : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (hqA : q ≤ A)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 2250 ≤ Real.log A) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬p ∣ q ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * twoPoleNegativeLogRoot (Real.log A) ^ 2 ∧ χ p = -1 := by
  have hd := twoPoleNegativeLogRoot_data hL
  obtain ⟨p, hp, hn, hb, hv⟩ :=
    exists_prime_not_one_of_generalTwoPole χ hne hGRH
      (by linarith only [hd.1] : 1 ≤ twoPoleNegativeLogRoot (Real.log A) ^ 2) ∅
      (fun k hk ↦ False.elim (Finset.notMem_empty k hk))
      (generalTwoPoleSeparation_negative_log_pos χ hquad hqA hL)
  have hz : χ p ≠ 0 :=
    MulChar.apply_ne_zero_iff.mpr
      ((ZMod.isUnit_iff_coprime p q).mpr (hp.coprime_iff_not_dvd.mpr hn))
  refine ⟨p, hp, hn, hb, ?_⟩
  rcases hquad (p : ZMod q) with h0 | h1 | hm
  · exact False.elim (hz h0)
  · exact False.elim (hv h1)
  · exact hm

end PseudoPrime.LLS
