/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.CoarseConductorLogBounds
public import PseudoPrime.LLS.LogShiftRampPrincipalBounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.BoundedPrimeExclusion
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.CompositeMangoldtSqrtBound

/-! # Conductor-square and linear prime-exclusion witness bounds -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under RH, y at least 131072 has logarithmic half-difference at least
y/2-4sqrt(y). Subtract the two corrected principal formulas so the logarithmic
shift leaves only log(2pi)log(2). This gives a bounded-weight principal main term. -/
theorem principal_log_half_difference_lower (hRH : RiemannHypothesis) {y : ℝ} (hy : 131072 ≤ y) :
    y / 2 - 4 * Real.sqrt y ≤
      AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum y -
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (y / 2) := by
  have hy0 : 0 < y := (by norm_num only : (0 : ℝ) < 131072).trans_le hy
  have hy1 : 1 < y := (by norm_num only : (1 : ℝ) < 131072).trans_le hy
  have hh : 1 < y / 2 := by linarith only [hy]
  have hA :=
    (abs_le.mp
        (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum_log_shift_error_le hRH hy1)).1
  have hB :=
    (abs_le.mp (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum_log_shift_error_le hRH hh)).2
  have hs := Real.sqrt_le_sqrt (show y / 2 ≤ y by linarith only [hy0])
  have hs2 : 2 ≤ Real.sqrt y :=
    (Real.le_sqrt (by norm_num only) hy0.le).mpr
      (by
        norm_num only; linarith only [hy])
  rw [Real.log_div hy0.ne' (by norm_num only : (2 : ℝ) ≠ 0)] at hB
  have hpi := Analysis.log_two_mul_pi_lt
  have hpi0 : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by linarith only [Real.pi_gt_three] : 1 ≤ 2 * Real.pi)
  have hcost := mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le hpi0
  have hprod : Real.log (2 * Real.pi) * Real.log 2 ≤ 2 := by nlinarith only [hcost, hpi]
  nlinarith only [hA, hB, hs, hs2, hprod]

/-- Under GRH for a primitive character of level at least three, absence
of nontrivial prime values outside a nonzero excluded modulus forces
y/2 at most (12 log(q)+112)sqrt(y) plus twice the excluded prime logarithm sum.
Combine bounded prime exclusion, higher-power removal, and primitive norm bounds. -/
theorem log_half_no_witness_conductor_comparison {q m : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hq : 3 ≤ q) (hp : χ.IsPrimitive) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hm : m ≠ 0) {y : ℝ} (hy : 131072 ≤ y)
    (hno : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ y → ¬p ∣ m → χ p = 1) :
    y / 2 ≤ (12 * Real.log q + 112) * Real.sqrt y + 2 * (∑ p ∈ m.primeFactors, Real.log p) := by
  have hy0 : 0 < y := (by norm_num only : (0 : ℝ) < 131072).trans_le hy
  have hh : 65536 ≤ y / 2 := by linarith only [hy]
  have hhalf : y / 2 ≤ y := by linarith only [hy0]
  have hb :=
    AnalyticNumberTheory.Arithmetic.log_difference_prime_exclusion χ hm
      (div_pos hy0 (by norm_num only : (0 : ℝ) < 2)) hhalf hno
  have hr : y / (y / 2) = 2 := by field_simp [hy0.ne']
  rw [hr] at hb
  have hP := principal_log_half_difference_lower hGRH.riemann hy
  have hR :=
    norm_characterLogWeightedSum_le_sqrt_conductor hq hp hGRH
      ((by norm_num only : (65536 : ℝ) ≤ 131072).trans hy)
  have hL := norm_characterLogWeightedSum_le_sqrt_conductor hq hp hGRH hh
  have hs := Real.sqrt_le_sqrt hhalf
  have hcoef : 0 ≤ 6 * (Real.log q + 6) := by linarith only [Real.log_natCast_nonneg q]
  have hLs := mul_le_mul_of_nonneg_left hs hcoef
  have hnorm :=
    (Complex.re_le_norm
          (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum y χ -
            AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y / 2) χ)).trans
      (norm_sub_le _ _)
  have hsharp :=
    AnalyticNumberTheory.Arithmetic.psi_sub_theta_le_six_sqrt
      ((by norm_num only : (1 : ℝ) ≤ 131072).trans hy)
  have ht : Chebyshev.psi y - Chebyshev.theta y ≤ 18 * Real.sqrt y := by
    nlinarith only [hsharp, Real.sqrt_nonneg y]
  have hsum : 0 ≤ ∑ p ∈ m.primeFactors, Real.log p :=
    Finset.sum_nonneg (fun p _ ↦ Real.log_natCast_nonneg p)
  have htail := Chebyshev.theta_le_psi y
  have hln2 : Real.log (2 : ℝ) ≤ 1 := by linarith only [Real.log_two_lt_d9]
  have hscale1 :=
    mul_le_mul_of_nonneg_right hln2
      (show 0 ≤ (∑ p ∈ m.primeFactors, Real.log p) + Chebyshev.psi y - Chebyshev.theta y by
        linarith only [hsum, htail])
  nlinarith only [hb, hP, hR, hL, hLs, hnorm, ht, hscale1]

/-- Under GRH, a primitive character of level q at least three has a prime
outside any nonzero excluded modulus m with nontrivial value and size at most
8(12log(q)+200)^2+16sum_{p|m}log(p). The conductor and exclusion costs are separate.
Choose a scale exceeding the comparison threshold and absorb the root term by
Young's inequality. No new finite input verification is required. -/
theorem exists_prime_ne_one_le_conductor_exclusion {q m : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hq : 3 ≤ q) (hp : χ.IsPrimitive) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hm : m ≠ 0) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ 8 * (12 * Real.log q + 200) ^ 2 + 16 * (∑ r ∈ m.primeFactors, Real.log r) ∧
        ¬p ∣ m ∧ χ p ≠ 1 := by
  classical
  let B := 12 * Real.log q + 200
  let E := ∑ r ∈ m.primeFactors, Real.log r
  let y := 8 * B ^ 2 + 16 * E
  have hB : 200 ≤ B := by
    dsimp only [B]; linarith only [Real.log_natCast_nonneg q]
  have hE : 0 ≤ E := Finset.sum_nonneg (fun p _ ↦ Real.log_natCast_nonneg p)
  have hy : 131072 ≤ y := by
    dsimp only [y]
    nlinarith only [hB, hE, sq_nonneg (B - 200)]
  by_contra hnone
  have hno (p : ℕ) (hp : p.Prime) (hb : (p : ℝ) ≤ y) (hd : ¬p ∣ m) : χ p = 1 := by
    by_contra hne
    exact hnone ⟨p, hp, hb, hd, hne⟩
  have hc := log_half_no_witness_conductor_comparison χ hq hp hGRH hm hy hno
  have hs := Real.sq_sqrt (show 0 ≤ y by linarith only [hy])
  have hlarge : (12 * Real.log q + 112) * Real.sqrt y ≤ B * Real.sqrt y := by
    have h := Real.sqrt_nonneg y
    dsimp only [B]
    nlinarith only [h]
  have hYoung := sq_nonneg (Real.sqrt y / 2 - B)
  change y / 2 ≤ (12 * Real.log q + 112) * Real.sqrt y + 2 * E at hc
  have hydef : y = 8 * B ^ 2 + 16 * E := rfl
  nlinarith only [hc, hs, hlarge, hYoung, hydef, hB, hE, sq_nonneg (B - 200)]

end PseudoPrime.LLS.PaperStatements
