/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TwoPolePrimePowerPrefixSavings
public import PseudoPrime.LLS.JointRampPrincipalWitnessBounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeFactorLogDeficitBounds

/-! # An explicit negative-prime root from conductor-cancelled Euler prefixes -/

@[expose] public section

namespace PseudoPrime.LLS

/-- For positive L, log L is at most L/800+57/10. Bound log 800 by a positive
exponential Taylor prefix and apply the logarithmic tangent. This controls the shifted root at
the analytic entrance without a table of input-dependent certificates. -/
theorem conductorPrefix_log_tangent {L : ℝ} (hL : 0 < L) : Real.log L ≤ L / 800 + 57 / 10 := by
  have hn : Real.log (800 : ℝ) ≤ 67 / 10 := by
    apply (Real.log_le_iff_le_exp (by norm_num only : (0 : ℝ) < 800)).mpr
    have h : (800 : ℝ) ≤ ∑ k ∈ Finset.range 18, (67 / 10 : ℝ) ^ k / (k.factorial : ℝ) := by
      norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    exact h.trans (Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 67 / 10) 18)
  have ht := Real.log_le_sub_one_of_pos (div_pos hL (by norm_num only : (0 : ℝ) < 800))
  rw [Real.log_div hL.ne' (by norm_num only : (800 : ℝ) ≠ 0)] at ht
  linarith only [ht, hn]

/-- The negative-witness root (500/821)L+(33/20) log L+9. Its additive constant uses the
conductor-cancelled Euler saving. The function is evaluated at a common ambient logarithm to
bound all nonsquare odd inputs in a finite maximum. -/
noncomputable def conductorPrefixNegativeLogRoot (L : ℝ) : ℝ :=
  (500 / 821 : ℝ) * L + (33 / 20 : ℝ) * Real.log L + 9

/-- For L at least 500, log L is at least six. Compare with 432 and use the certified
logarithms of two and three. This gives the lower corner for the numerator comparison. -/
theorem conductorPrefix_log_lower {L : ℝ} (hL : 500 ≤ L) : 6 ≤ Real.log L := by
  have h :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 432) (show (432 : ℝ) ≤ L by linarith only [hL])
  rw [show (432 : ℝ) = 2 ^ 4 * 3 ^ 3 by norm_num only,
    Real.log_mul (by norm_num only : (2 : ℝ) ^ 4 ≠ 0) (by norm_num only : (3 : ℝ) ^ 3 ≠ 0),
    Real.log_pow, Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith only [h, Real.log_two_gt_d9, Real.log_three_gt_d9]

/-- For L at least 500, the conductor-prefix root is at least five and the two endpoint
logarithms obey the displayed caps. Use the logarithmic tangent to bound the root by 13L/20.
These estimates supply the minimum scale and cutoff bounds for the saved numerator. -/
theorem conductorPrefixNegativeLogRoot_data {L : ℝ} (hL : 500 ≤ L) :
    5 ≤ conductorPrefixNegativeLogRoot L ∧
      Real.log ((99 / 40 : ℝ) * conductorPrefixNegativeLogRoot L ^ 2) ≤ 2 * Real.log L + 1 / 20 ∧
      Real.log ((101 / 40 : ℝ) * conductorPrefixNegativeLogRoot L ^ 2) ≤
        2 * Real.log L + 3 / 40 := by
  let r := conductorPrefixNegativeLogRoot L
  have hl := conductorPrefix_log_lower hL
  have hp : 0 < L := by linarith only [hL]
  have ht := twoPoleRetained_log_tangent hp
  have hr : 5 ≤ r := by
    dsimp only [r, conductorPrefixNegativeLogRoot]; linarith only [hL, hl]
  have hu : r ≤ (13 / 20 : ℝ) * L := by
    dsimp only [r, conductorPrefixNegativeLogRoot]
    linarith only [ht, hL]
  have hs := mul_self_le_mul_self (by linarith only [hr] : 0 ≤ r) hu
  have ha :=
    Real.log_le_log (by nlinarith only [hr, sq_nonneg (r - 5)] : 0 < (99 / 40 : ℝ) * r ^ 2)
      (show (99 / 40 : ℝ) * r ^ 2 ≤ (21 / 20 : ℝ) * L ^ 2 by nlinarith only [hs])
  rw [Real.log_mul (by norm_num only : (21 / 20 : ℝ) ≠ 0) (pow_ne_zero 2 hp.ne'),
    Real.log_pow] at ha
  norm_num only [Nat.cast_ofNat] at ha
  have hca := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 21 / 20)
  have hb :=
    Real.log_le_log (by nlinarith only [hr, sq_nonneg (r - 5)] : 0 < (101 / 40 : ℝ) * r ^ 2)
      (show (101 / 40 : ℝ) * r ^ 2 ≤ (43 / 40 : ℝ) * L ^ 2 by nlinarith only [hs])
  rw [Real.log_mul (by norm_num only : (43 / 40 : ℝ) ≠ 0) (pow_ne_zero 2 hp.ne'),
    Real.log_pow] at hb
  norm_num only [Nat.cast_ofNat] at hb
  have hcb := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 43 / 40)
  exact ⟨hr, by linarith only [ha, hca], by linarith only [hb, hcb]⟩

/-- For L at least 500 and u at least six, the numerator plus joint saving exceeds the product
of the affine factor-count bound and cutoff logarithm cap. Use shifted polynomial positivity.
This keeps the logarithmic deficits of small primes through the witness comparison. -/
theorem conductorPrefixNegative_deficit_margin {L u : ℝ} (hL : 500 ≤ L) (hu : 6 ≤ u) :
    (5 / 2 + (3 / 8 : ℝ) * L) * (2 * u + 1 / 20) <
      twoPoleRetainedNumerator L (87 / 25) ((500 / 821 : ℝ) * L + (33 / 20 : ℝ) * u + 9)
          (2 * u + 3 / 40) +
        (1 / 5 : ℝ) * ((500 / 821 : ℝ) * L + (33 / 20 : ℝ) * u + 9) := by
  dsimp only [twoPoleRetainedNumerator]
  nlinarith only [hL, hu, sq_nonneg (L - 500), sq_nonneg (u - 15 / 2),
    mul_nonneg (sub_nonneg.mpr hL) (sub_nonneg.mpr hu)]

/-- For a positive level at most A with log A at least 500, the numerator plus joint saving at
the improved root exceeds the level-prime ramp numerator. Keep the affine factor-count bound
5/2+(3/8) log A and the endpoint logarithm cap. This supplies the strict saved-gap inequality. -/
theorem conductorPrefixNegative_numerator_dominates_cost {q A : ℕ} (hq : 0 < q) (hqA : q ≤ A)
    (hL : 500 ≤ Real.log A) :
    (q.primeFactors.card : ℝ) *
        Real.log ((99 / 40 : ℝ) * conductorPrefixNegativeLogRoot (Real.log A) ^ 2) <
      twoPoleRetainedNumerator (Real.log A) (87 / 25) (conductorPrefixNegativeLogRoot (Real.log A))
          (2 * Real.log (Real.log A) + 3 / 40) +
        (1 / 5 : ℝ) * conductorPrefixNegativeLogRoot (Real.log A) := by
  have hd := conductorPrefixNegativeLogRoot_data hL
  have hcard :=
    AnalyticNumberTheory.Arithmetic.primeFactors_card_le_five_halves_add_three_eighths_log hq hqA
  have hr := hd.1
  have hs := sq_nonneg (conductorPrefixNegativeLogRoot (Real.log A) - 5)
  have hlog0 : 0 ≤ Real.log ((99 / 40 : ℝ) * conductorPrefixNegativeLogRoot (Real.log A) ^ 2) :=
    Real.log_nonneg (by nlinarith only [hr, hs])
  have hp :=
    mul_le_mul hcard hd.2.1 hlog0 (show 0 ≤ 5 / 2 + (3 / 8 : ℝ) * Real.log A by linarith only [hL])
  have hn := conductorPrefixNegative_deficit_margin hL (conductorPrefix_log_lower hL)
  dsimp only [conductorPrefixNegativeLogRoot] at hp ⊢
  exact hp.trans_lt hn

/-- Under GRH, an even nonprincipal quadratic character of level at most A, with log A at
least 500, has a unit-prime witness of value minus one below 99/40 times the improved root
squared. Use the full Euler prefix through thirteen, its saving one, and the joint
numerator margin. This is an explicit negative-witness bound without an input-dependent prefix
budget assumption or finite input enumeration. -/
theorem exists_prime_neg_one_le_conductorPrefix_log_ambient {q A : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (heven : χ.Even) (hne : χ ≠ 1)
    (hqA : q ≤ A) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 500 ≤ Real.log A) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬p ∣ q ∧
        (p : ℝ) ≤ (99 / 40 : ℝ) * conductorPrefixNegativeLogRoot (Real.log A) ^ 2 ∧ χ p = -1 := by
  let r := conductorPrefixNegativeLogRoot (Real.log A)
  have hd := conductorPrefixNegativeLogRoot_data hL
  have hx : 25 ≤ r ^ 2 := by nlinarith only [hd.1, sq_nonneg (r - 5)]
  have hc :=
    AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant_le_signed_of_even
      χ.primitiveCharacter ((NumberTheory.primitiveCharacter_even_iff χ).mpr heven)
  have hn :=
    conductorPrefixNegative_numerator_dominates_cost (Nat.pos_of_ne_zero (NeZero.ne q)) hqA hL
  have hg :=
    twoPoleConstantGap_mul_root_lower (A := A) (C := 87 / 25) (by linarith only [hd.1] : 1 ≤ r)
      hd.2.2
  have hgs :=
    twoPoleSignedVariationGap_gt_constant (A := A) (C := 87 / 25)
      (show 1 ≤ r ^ 2 by linarith only [hx])
  have hgj :=
    jointRampPrincipalGap_gt_signed (A := A) (C := 87 / 25) (show 1 ≤ r ^ 2 by linarith only [hx])
  have hm :=
    mul_le_mul_of_nonneg_right
      (show
        twoPoleConstantGap A (87 / 25) (r ^ 2) + 1 / 5 ≤ jointRampPrincipalGap A (87 / 25) (r ^ 2)
        by linarith only [hgs, hgj])
      (show 0 ≤ r by linarith only [hd.1])
  have hupper :
    twoPoleRetainedNumerator (Real.log A) (87 / 25) r (2 * Real.log (Real.log A) + 3 / 40) +
        (1 / 5 : ℝ) * r ≤
      jointRampPrincipalGap A (87 / 25) (r ^ 2) * r := by
    nlinarith only [hg, hm]
  have hgap :
    (q.primeFactors.card : ℝ) * Real.log ((99 / 40 : ℝ) * r ^ 2) / Real.sqrt (r ^ 2) <
      jointRampPrincipalGap A (112 / 25 - 1) (r ^ 2) := by
    rw [Real.sqrt_sq (by linarith only [hd.1] : 0 ≤ r)]
    apply (div_lt_iff₀ (by linarith only [hd.1] : 0 < r)).mpr
    norm_num only at *
    exact hn.trans_le hupper
  apply
    exists_prime_neg_one_of_jointRampPrincipal_conductor_prefix χ hquad hne hqA hGRH
      (by linarith only [hx] : 2 ≤ r ^ 2) (Y := 13) (by norm_num only) (a := 3 / 10) (d :=
      (1 / 5 : ℝ) * Real.log 2) (by norm_num only)
      (mul_nonneg (by norm_num only) (Real.log_natCast_nonneg 2))
      (by
        rw [Real.sqrt_sq (show 0 ≤ r by linarith only [hd.1])]; linarith only [hd.1])
      (fun p hp ↦
        AnalyticNumberTheory.Arithmetic.pairedEulerPrefixWeight_prime_upper_three_tenths hp)
      _ hc (g := 1) _ hgap
  · intro n hn
    have hn13 : n ≤ 13 := by
      norm_num only [Nat.floor_ofNat] at hn
      exact (Finset.mem_Ioc.mp hn).2
    exact (Nat.cast_le.mpr hn13).trans (by nlinarith only [hx])
  · norm_num only [Nat.floor_ofNat]
    exact twoPoleEulerPrefixMass_thirteen_saving_one

end PseudoPrime.LLS
