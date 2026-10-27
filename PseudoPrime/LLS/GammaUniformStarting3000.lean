/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaUniformSmallScaleBounds
public import PseudoPrime.LLS.GammaUniformRationalProfileBounds
public import PseudoPrime.LLS.RefinedTheorem11S1Subgroup

/-! # Rational coefficient-0.796 witnesses from modulus 3000 -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH, q ≥ 20000, log q ≤ 34971 and H proper, a coprime outside
prime exists through (199/250)(log q+216)². Use T=sqrt(199/200)(log q+216),
the smaller-scale comparison and factor-support allowance 160/9.
This closes the middle logarithmic range without a finite modulus table. -/
theorem gamma_profile_199_div_250_plus_216_middle {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (hH : H ≠ ⊤) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hq : 20000 ≤ q)
    (hupper : Real.log q ≤ 34971) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬p ∣ q ∧ ¬residueInSubgroup q H p ∧ (p : ℝ) ≤ (199 / 250 : ℝ) * (Real.log q + 216) ^ 2 := by
  let L := Real.log q
  let T := Real.sqrt (199 / 200 : ℝ) * (L + 216)
  let x := (32 / 99 : ℝ) * T ^ 2
  have hlog20 :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 20000) (by exact_mod_cast hq : (20000 : ℝ) ≤ q)
  rw [show (20000 : ℝ) = 2 * 10 ^ 4 by norm_num only,
    Real.log_mul (by norm_num only : (2 : ℝ) ≠ 0) (pow_ne_zero 4 (by norm_num only : (10 : ℝ) ≠ 0)),
    Real.log_pow] at hlog20
  norm_num only [Nat.cast_ofNat] at hlog20
  have hL : (49 / 5 : ℝ) ≤ L := by
    linarith only [hlog20, Real.log_two_gt_d9, Analysis.log_ten_gt_230258]
  have hL0 : 0 < L := by linarith only [hL]
  have hsqrt : (124687 / 125000 : ℝ) ≤ Real.sqrt (199 / 200 : ℝ) := by
    apply (Real.le_sqrt (by norm_num only) (by norm_num only)).mpr
    norm_num only
  have hTlower : (124687 / 125000 : ℝ) * (L + 216) ≤ T :=
    mul_le_mul_of_nonneg_right hsqrt (show 0 ≤ L + 216 by linarith only [hL0])
  have hT : 224 ≤ T := by linarith only [hTlower, hL]
  have hambient : L ≤ T := by linarith only [hTlower, hupper]
  have hxlarge := (Analysis.gamma_small_scale_bounds hT).1
  have hx : 1 ≤ x := (by norm_num only : (1 : ℝ) ≤ (9 / 5) ^ 16).trans hxlarge
  have hT0 : 0 < T := by linarith only [hT]
  have hcut : 1 ≤ (4 / 5 : ℝ) * T ^ 2 := by nlinarith only [hT, sq_nonneg (T - 224)]
  have hcutlog :=
    Real.log_le_log (zero_lt_one.trans_le hcut)
      (show (4 / 5 : ℝ) * T ^ 2 ≤ T ^ 2 by nlinarith only [sq_nonneg T])
  rw [Real.log_pow] at hcutlog
  norm_num only [Nat.cast_ofNat] at hcutlog
  have hlocal :=
    Analysis.gamma_commonFactor_budget_of_ambient_scale (by norm_num only : (0 : ℝ) < 9 / 16)
      (show 1 < T by linarith only [hT]) hambient (zero_lt_one.trans_le hx) hcut hcutlog
      (Analysis.ramp_scale_sqrt_lower hT0.le) (Analysis.gamma_small_scale_cuberoot_ratio hT)
  norm_num only at hlocal
  have hbudget :
    (11783423 / 25000000 : ℝ) * Real.log q + 75169 / 900 +
        2 *
          (AnalyticNumberTheory.Arithmetic.commonFactorExponentialSum x ((4 / 5 : ℝ) * T ^ 2) q /
            Real.sqrt x) <
      (11783423 / 25000000 + 1 / 795 : ℝ) * T := by
    linarith only [hlocal, hTlower, hL]
  obtain ⟨p, hp, hd, hout, hb⟩ :=
    exists_prime_outside_le_gamma_four_fifths_small_scale hq H hH hGRH hT hambient hbudget
  have he : (4 / 5 : ℝ) * T ^ 2 = (199 / 250 : ℝ) * (L + 216) ^ 2 := by
    dsimp only [T]
    rw [mul_pow, Real.sq_sqrt (by norm_num only : (0 : ℝ) ≤ 199 / 200)]
    ring
  exact ⟨p, hp, hd, hout, he ▸ hb⟩

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS

/-- For 3000 ≤ q < 20000, the refined Part 1 radius root is at most seventy.
Bound log q by ten, its logarithm by three, and the distinct prime count by twenty-two.
Discard the nonnegative reciprocal saving to bound the correction by sixty.
This transfers the small modulus range without new exhaustive certificates. -/
theorem refinedRadiusRoot_le_seventy_of_lt_20000 {q : ℕ} [NeZero q] (hq : 3000 ≤ q)
    (hsmall : q < 20000) : refinedRadiusRoot q ≤ 70 := by
  let L := Real.log q
  let z := Real.log L
  have hL := Analysis.eight_lt_log_level hq
  have hqpos : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hlog20 := Real.log_le_log hqpos (by exact_mod_cast hsmall.le : (q : ℝ) ≤ 20000)
  rw [show (20000 : ℝ) = 2 * (2 * 5) ^ 4 by norm_num only,
    Real.log_mul (by norm_num only : (2 : ℝ) ≠ 0)
      (pow_ne_zero 4 (by norm_num only : (2 * 5 : ℝ) ≠ 0)),
    Real.log_pow,
    Real.log_mul (by norm_num only : (2 : ℝ) ≠ 0) (by norm_num only : (5 : ℝ) ≠ 0)] at hlog20
  norm_num only [Nat.cast_ofNat] at hlog20
  have hLupper : L ≤ 10 := by linarith only [hlog20, Real.log_two_lt_d9, Real.log_five_lt_d9]
  have hL0 : 0 < L := by linarith only [hL]
  have hz0 : 0 ≤ z := Real.log_nonneg (show 1 ≤ L by linarith only [hL])
  have hz := Real.log_le_sub_one_of_pos (div_pos hL0 (by norm_num only : (0 : ℝ) < 4))
  rw [Real.log_div hL0.ne' (by norm_num only : (4 : ℝ) ≠ 0), show (4 : ℝ) = 2 ^ 2 by norm_num only,
    Real.log_pow] at hz
  norm_num only [Nat.cast_ofNat] at hz
  have hzupper : z ≤ 3 := by
    dsimp only [z]
    linarith only [hz, hLupper, Real.log_two_lt_d9]
  have hcard :=
    AnalyticNumberTheory.Arithmetic.primeFactors_card_le_cutoff_add_log_div (NeZero.ne q)
      (by norm_num only : (1 : ℝ) < 2)
  have hdiv : L / Real.log 2 ≤ 2 * L := by
    apply (div_le_iff₀ (show (0 : ℝ) < Real.log 2 by linarith only [Real.log_two_gt_d9])).mpr
    have h := mul_le_mul_of_nonneg_left Real.log_two_gt_d9.le hL0.le
    nlinarith only [h, hL0]
  have hcard22 : (q.primeFactors.card : ℝ) ≤ 22 := by linarith only [hcard, hdiv, hLupper]
  have hzsq : z ^ 2 ≤ 9 := by nlinarith only [hz0, hzupper]
  have hnum := mul_le_mul_of_nonneg_right hcard22 (sq_nonneg z)
  have hw : 2 * (q.primeFactors.card : ℝ) * z ^ 2 / L ≤ 50 := by
    rw [div_le_iff₀ hL0]
    nlinarith only [hnum, hzsq, hL]
  have hA : 0 ≤ refinedAuxiliaryTerm q := le_max_left _ _
  have hB : refinedCorrectionTerm q ≤ 60 := by
    unfold refinedCorrectionTerm
    apply max_le (by norm_num only)
    change 2 * z + 2 + 2 * (q.primeFactors.card : ℝ) * z ^ 2 / L - 2 * refinedAuxiliaryTerm q ≤ 60
    linarith only [hzupper, hw, hA]
  dsimp only [refinedRadiusRoot]
  linarith only [hLupper, hB]

end PseudoPrime.LLS

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH, 3000 ≤ q < 20000 and H proper, a coprime outside prime
exists through (199/250)(log q+216)². Apply refined Part 1, bound its radius
by seventy and compare the squared cutoffs. This is the small modulus branch. -/
theorem gamma_profile_199_div_250_plus_216_small {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (hH : H ≠ ⊤) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hq : 3000 ≤ q)
    (hsmall : q < 20000) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬p ∣ q ∧ ¬residueInSubgroup q H p ∧ (p : ℝ) ≤ (199 / 250 : ℝ) * (Real.log q + 216) ^ 2 := by
  obtain ⟨p, hp, hb⟩ := LLS.exists_prime_outside_subgroup_le_refinedRadius hq H hH hGRH
  have hroot := LLS.refinedRadiusRoot_le_seventy_of_lt_20000 hq hsmall
  have hL := Analysis.eight_lt_log_level hq
  have hroot0 : 0 ≤ LLS.refinedRadiusRoot q := by
    unfold LLS.refinedRadiusRoot
    have hB : 0 ≤ LLS.refinedCorrectionTerm q := le_max_left _ _
    linarith only [hL, hB]
  have hbound : (LLS.refinedRadiusRoot q) ^ 2 ≤ (199 / 250 : ℝ) * (Real.log q + 216) ^ 2 := by
    nlinarith only [hroot, hroot0, hL, sq_nonneg (Real.log q - 8)]
  refine ⟨p, hp.1, hp.2.1, ?_, hb.trans hbound⟩
  rintro ⟨u, hu, he⟩
  obtain ⟨v, hv, hve⟩ := hp.2.2
  have heq : v = u := Units.ext (hve.trans he.symm)
  exact hv (heq ▸ hu)

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH, every q ≥ 3000 and proper unit subgroup H has a coprime
outside prime through (199/250)(log q+216)². Split at modulus 20000 and
logarithmic value 34971, using the small, middle and stronger large profiles.
This has rational coefficients (199/250,0,216) and no further arithmetic hypothesis. -/
theorem exists_prime_outside_le_gamma_199_div_250_plus_216_3000 {q : ℕ} (H : Subgroup (ZMod q)ˣ)
    (hH : H ≠ ⊤) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hq : 3000 ≤ q) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬p ∣ q ∧ ¬residueInSubgroup q H p ∧ (p : ℝ) ≤ (199 / 250 : ℝ) * (Real.log q + 216) ^ 2 := by
  have hq0 : q ≠ 0 := Nat.ne_zero_of_lt ((by decide : (0 : ℕ) < 3000).trans_le hq)
  let : NeZero q := ⟨hq0⟩
  by_cases hsmall : q < 20000
  · exact gamma_profile_199_div_250_plus_216_small H hH hGRH hq hsmall
  · by_cases hlarge : 34971 ≤ Real.log q
    · obtain ⟨p, hp, hd, hout, hb⟩ :=
        exists_prime_outside_le_gamma_199_div_250_plus_117_log H hH hGRH hlarge
      have hbound :
        (199 / 250 : ℝ) * (Real.log q + 117) ^ 2 ≤ (199 / 250 : ℝ) * (Real.log q + 216) ^ 2 := by
        nlinarith only [hlarge, sq_nonneg (Real.log q + 117)]
      exact ⟨p, hp, hd, hout, hb.trans hbound⟩
    · exact
        gamma_profile_199_div_250_plus_216_middle H hH hGRH (Nat.le_of_not_lt hsmall)
          (le_of_not_ge hlarge)

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS

/-- Under GRH, q ≥ 3000 and χ nonprincipal, a coprime prime with χ(p) ≠ 1
exists through (199/250)(log q+216)². Apply the uniform subgroup cutoff to its unit kernel.
This is the general-character interface for the starting value 3000. -/
theorem exists_prime_character_ne_one_le_gamma_199_div_250_plus_216_3000 {q : ℕ}
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hq : 3000 ≤ q) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ χ p ≠ 1 ∧ (p : ℝ) ≤ (199 / 250 : ℝ) * (Real.log q + 216) ^ 2 := by
  exact
    exists_prime_character_ne_one_of_uniform_subgroup_cutoff χ hne
      (fun H hH ↦
        PaperStatements.exists_prime_outside_le_gamma_199_div_250_plus_216_3000 H hH hGRH hq)

/-- Under GRH, q ≥ 3000 and H proper, the least coprime outside prime is
at most (199/250)(log q+216)². Minimize the bounded subgroup witness.
Minimality is among all eligible primes, with the same starting value and formula. -/
theorem exists_least_prime_outside_le_gamma_199_div_250_plus_216_3000 {q : ℕ}
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hq : 3000 ≤ q) :
    ∃ p : ℕ,
      PrimeOutsideSubgroup q H p ∧
        (p : ℝ) ≤ (199 / 250 : ℝ) * (Real.log q + 216) ^ 2 ∧
        ∀ r, PrimeOutsideSubgroup q H r → p ≤ r := by
  exact
    exists_least_prime_outside_of_subgroup_cutoff H
      (PaperStatements.exists_prime_outside_le_gamma_199_div_250_plus_216_3000 H hH hGRH hq)

end PseudoPrime.LLS
