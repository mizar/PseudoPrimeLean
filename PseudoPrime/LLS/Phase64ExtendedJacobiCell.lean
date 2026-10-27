/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Phase64TransportedNumericalBudget
public import PseudoPrime.LLS.Phase64CertifiedJacobiCell

/-! # A fixed-scale strict Jacobi witness bound on the wider phase64 cell -/

@[expose] public section

namespace PseudoPrime.LLS

/-- For upper bounds on log(n), log(4*n), log(q), the negative power and a
positive lower bound for sqrt(x), bound the actual numerical budget by the corresponding
scalar expression. Monotonicity of positive factors and division proves the result.
This generic comparison permits new ranges without changing arithmetic certificates. -/
theorem phase64_budget_le_of_scalar_caps {n q : ℕ} {x N Q S P : ℝ} (hn : Real.log n ≤ N)
    (h4 : Real.log (4 * (n : ℝ)) ≤ N + 7 / 5) (hq : Real.log q ≤ Q) (hS : 0 < S)
    (hs : S ≤ Real.sqrt x) (hQ : 0 ≤ (7 / 6 : ℝ) * Q + 4) (hp : x ^ (-9 / 16 : ℝ) ≤ P) :
    phase64NumericalJacobiBudget n q x ≤
      (90992831 / 200000000 : ℝ) * (N + 7 / 5) + 3 / 100 * N - 129 / 200 +
        ((7 / 6 : ℝ) * Q + 4) / S +
        43 * P := by
  have hlead := mul_le_mul_of_nonneg_left h4 (by norm_num only : (0 : ℝ) ≤ 90992831 / 200000000)
  have hlin := mul_le_mul_of_nonneg_left hn (by norm_num only : (0 : ℝ) ≤ 3 / 100)
  have hnum : (7 / 6 : ℝ) * Real.log q + 4 ≤ (7 / 6 : ℝ) * Q + 4 := by linarith only [hq]
  have hdiv := div_le_div_of_nonneg_left hQ hS hs
  have hquot := (div_le_div_of_nonneg_right hnum (Real.sqrt_nonneg x)).trans hdiv
  dsimp only [phase64NumericalJacobiBudget]
  linarith only [hlead, hlin, hquot, hp]

/-- At every scale at least 163840/99, bound the negative power by 7/430.
Certify the rational sixteenth-power inequality and apply negative-power monotonicity.
This supplies a uniform scalar input to the fixed-scale budget comparison. -/
theorem phase64_rpow_neg_le_of_scale_lower {x : ℝ} (hx : (163840 / 99 : ℝ) ≤ x) :
    x ^ (-9 / 16 : ℝ) ≤ 7 / 430 := by
  have hpcheck : (1 : ℚ) ≤ (7 / 430 : ℚ) ^ 16 * (163840 / 99 : ℚ) ^ 9 := by decide +kernel
  have hp :=
    (Analysis.rpow_neg_div_nat_interval (by norm_num only : (0 : ℝ) < 163840 / 99)
        (by norm_num only : (0 : ℝ) ≤ 0) (by norm_num only : (0 : ℝ) ≤ 7 / 430) 9 16
        (by norm_num only) (by norm_num only)
        (by
          have hc := (Rat.cast_le (K := ℝ)).mpr hpcheck
          simpa only [Rat.cast_one, Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using
            hc)).2
  exact
    (Real.rpow_le_rpow_of_nonpos (by norm_num only : (0 : ℝ) < 163840 / 99) hx
          (by norm_num only : (-9 / 16 : ℝ) ≤ 0)).trans
      hp

/-- For positive n with log(n)<=64.05 and log(q)<=65.45, the numerical
budget at scale 163840/99 is below 1373/(407/10). Combine the generic scalar caps
with the certified power bound and rational arithmetic. This extends the admissible
integer range while retaining the old endpoint certificates. -/
theorem phase64_fixed_budget_lt_margin {n q : ℕ} (hn : 0 < n) (hnL : Real.log n ≤ 1281 / 20)
    (hqL : Real.log q ≤ 1309 / 20) :
    phase64NumericalJacobiBudget n q (163840 / 99) < 1373 / (407 / 10) := by
  have h4 : Real.log (4 * (n : ℝ)) ≤ (1281 / 20 : ℝ) + 7 / 5 := by
    have hlog4 : Real.log (4 : ℝ) ≤ 7 / 5 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num only, Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      linarith only [Real.log_two_lt_d9]
    rw [Real.log_mul (by norm_num only : (4 : ℝ) ≠ 0) (Nat.cast_pos.mpr hn).ne']
    linarith only [hlog4, hnL]
  have hs : (2034 / 50 : ℝ) ≤ Real.sqrt (163840 / 99) :=
    (Real.le_sqrt (by norm_num only) (by norm_num only)).mpr (by norm_num only)
  have hp := phase64_rpow_neg_le_of_scale_lower (le_refl (163840 / 99 : ℝ))
  have hb :=
    phase64_budget_le_of_scalar_caps hnL h4 hqL (by norm_num only : (0 : ℝ) < 2034 / 50) hs
      (by norm_num only) hp
  norm_num only at hb ⊢
  linarith only [hb]

/-- Under GRH, odd nonsquare n and 64<=log(n)<=64.05, produce an odd
prime at most 4096 with Jacobi value -1. Choose the fixed anchor scale at level 64,
reuse the certified ramp and principal endpoints and compare the new scalar budget.
No additional numerical certificate is assumed; this remains a bounded-range theorem. -/
theorem exists_odd_prime_negative_phase64_fixed_cap
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hlo : (64 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ 1281 / 20) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ 4096 ∧ jacobiSym n p = -1 := by
  obtain ⟨bridge⟩ := NumberTheory.exists_jacobiCharacterArithmeticData hn.pos hn hns
  obtain ⟨hq, hm, hlog⟩ := phase64_ambient_four_mul_data hn hlo
  have hqlog : Real.log ((4 * n : ℕ) : ℝ) ≤ 1309 / 20 := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    linarith only [hlog, hhi]
  have hB := phase64_fixed_budget_lt_margin hn.pos hhi hqlog
  have htail :=
    principalExponentialTailBound_40000_le (by norm_num only : (0 : ℝ) < 4096128001 / 2475000)
      (by norm_num only : (4096128001 / 2475000 : ℝ) ≤ 1660)
  have hA :=
    phase64_principalRamp_lower_of_finite_bounds (by norm_num only : (64 : ℝ) ≤ 64)
      (by norm_num only : (64 : ℝ) ≤ 64001 / 1000) 40000
      Analysis.Phase64EndpointCertificates.phase64_ramp_endpoint_lower
      Analysis.Phase64EndpointCertificates.phase64_principal_endpoint_upper htail
      (by norm_num only : (1373 : ℝ) ≤ 2 * 1514 - 1654 - 1 / 100)
      (by norm_num only : (0 : ℝ) ≤ 1373)
  have hgap :
    phase64NumericalJacobiBudget n (4 * n) (64 ^ 2 / (99 / 40)) <
      principalRampDifference (64 ^ 2 / (99 / 40)) := by
    norm_num only at hA hB ⊢
    exact hB.trans_le hA
  have hw :=
    exists_odd_prime_negative_of_phase64_numerical_gap bridge hGRH hq hm
      (by norm_num only : (64 : ℝ) ≤ 64) (by norm_num only : (64 : ℝ) ≤ 64001 / 1000) hgap
  norm_num only at hw
  exact hw

/-- Under GRH, odd nonsquare n and 64<=log(n)<=64.05, produce a negative
odd-prime Jacobi witness strictly below log(n)^2. An odd witness through 4096 cannot
equal the even endpoint. This strengthens the certified bounded cell in width and
strictness without asserting a whole-half-line entrance. -/
theorem exists_odd_prime_negative_phase64_extended_cell
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hlo : (64 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ 1281 / 20) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) < (Real.log n) ^ 2 ∧ jacobiSym n p = -1 := by
  obtain ⟨p, hp, ho, hb, hv⟩ := exists_odd_prime_negative_phase64_fixed_cap hGRH hn hns hlo hhi
  have hbN : p ≤ 4096 := Nat.cast_le.mp (show (p : ℝ) ≤ ((4096 : ℕ) : ℝ) from hb)
  have hpne : p ≠ 4096 := fun he ↦ (by decide : ¬Odd (4096 : ℕ)) (he ▸ ho)
  have hlt : p < 4096 := lt_of_le_of_ne hbN hpne
  have hs : (4096 : ℝ) ≤ (Real.log n) ^ 2 := by nlinarith only [hlo]
  exact ⟨p, hp, ho, (Nat.cast_lt.mpr hlt).trans_le hs, hv⟩

/-- Under the same GRH and bounded odd-nonsquare hypotheses, produce a
non-one odd-prime Jacobi witness strictly below log(n)^2. The negative witness is
also non-one. This connects the wider cell to the second witness predicate. -/
theorem exists_odd_prime_not_one_phase64_extended_cell
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hlo : (64 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ 1281 / 20) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) < (Real.log n) ^ 2 ∧ jacobiSym n p ≠ 1 := by
  obtain ⟨p, hp, ho, hb, hv⟩ := exists_odd_prime_negative_phase64_extended_cell hGRH hn hns hlo hhi
  exact
    ⟨p, hp, ho, hb, by
      rw [hv]; norm_num only⟩

/-- Given GRH, the wider bounded cell and an explicit nonempty negative
witness set, bound its least odd-prime witness strictly by log(n)^2. Compare the
least witness with the proved pointwise witness. This exports the least-witness bound. -/
theorem primeNegOneWitness_lt_phase64_extended_cell
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hlo : (64 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ 1281 / 20)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) < (Real.log n) ^ 2 := by
  obtain ⟨p, hp, ho, hb, hv⟩ := exists_odd_prime_negative_phase64_extended_cell hGRH hn hns hlo hhi
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hv⟩)).trans_lt hb

/-- Given GRH, the wider bounded cell and an explicit nonempty non-one
witness set, bound its least odd-prime witness strictly by log(n)^2. Apply the
least-witness comparison to the new non-one witness. This exports the second bound. -/
theorem primeNeOneWitness_lt_phase64_extended_cell
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hlo : (64 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ 1281 / 20)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) < (Real.log n) ^ 2 := by
  obtain ⟨p, hp, ho, hb, hv⟩ := exists_odd_prime_not_one_phase64_extended_cell hGRH hn hns hlo hhi
  exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hv⟩)).trans_lt hb

end PseudoPrime.LLS
