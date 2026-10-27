/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Phase64ExtendedJacobiCell
public import PseudoPrime.Analysis.Phase64SharpAggregateBounds

/-! # Wider fixed-scale Jacobi bounds from sharp existing aggregates -/

@[expose] public section

namespace PseudoPrime.LLS

/-- For positive n with log(n)<=64.18 and log(q)<=65.58, the fixed-scale
numerical budget is below 1375/(20341/500). Apply the existing generic scalar caps.
This comparison uses sharper aggregate precision while keeping the same spectral anchor. -/
theorem phase64_sharp_fixed_budget_lt_margin {n q : ℕ} (hn : 0 < n) (hnL : Real.log n ≤ 3209 / 50)
    (hqL : Real.log q ≤ 3279 / 50) :
    phase64NumericalJacobiBudget n q (163840 / 99) < 1375 / (20341 / 500) := by
  have h4 : Real.log (4 * (n : ℝ)) ≤ (3209 / 50 : ℝ) + 7 / 5 := by
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

/-- At scale 163840/99, the actual principal-ramp difference is at least
1375/(20341/500). Reuse the exact certified aggregate caps, the old tail bound and
a sharper rational upper bound for the endpoint square root. No new atom data enter. -/
theorem phase64_principalRamp_sharp_lower :
    (1375 / (20341 / 500) : ℝ) ≤ principalRampDifference (163840 / 99) := by
  have ht :=
    principalExponentialTailBound_40000_le (by norm_num only : (0 : ℝ) < 4096128001 / 2475000)
      (by norm_num only : (4096128001 / 2475000 : ℝ) ≤ 1660)
  have hs : Real.sqrt (4096128001 / 2475000 : ℝ) ≤ 20341 / 500 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  exact
    principalRampDifference_lower_of_finite_endpoints (by norm_num only : (0 : ℝ) < 163840 / 99)
      (le_refl (163840 / 99 : ℝ)) (by norm_num only : (163840 / 99 : ℝ) ≤ 4096128001 / 2475000)
      40000 Analysis.Phase64EndpointCertificates.phase64_ramp_endpoint_lower_sharp
      Analysis.Phase64EndpointCertificates.phase64_principal_endpoint_upper_sharp ht
      (by norm_num only : (1375 : ℝ) ≤ 2 * (151409083 / 100000) - 16531667 / 10000 - 1 / 100)
      (by norm_num only : (0 : ℝ) ≤ 1375) hs

/-- Under GRH, odd nonsquare n and 64<=log(n)<=64.18, produce a negative
odd-prime Jacobi witness through 4096. Keep the fixed level-64 spectral anchor and
compare the sharper certified principal-ramp lower bound with the scalar budget. -/
theorem exists_odd_prime_negative_phase64_sharp_fixed_cap
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hlo : (64 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ 3209 / 50) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ 4096 ∧ jacobiSym n p = -1 := by
  obtain ⟨bridge⟩ := NumberTheory.exists_jacobiCharacterArithmeticData hn.pos hn hns
  obtain ⟨hq, hm, hlog⟩ := phase64_ambient_four_mul_data hn hlo
  have hqlog : Real.log ((4 * n : ℕ) : ℝ) ≤ 3279 / 50 := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    linarith only [hlog, hhi]
  have hB := phase64_sharp_fixed_budget_lt_margin hn.pos hhi hqlog
  have hA := phase64_principalRamp_sharp_lower
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

/-- Under the same bounded GRH and odd-nonsquare hypotheses, produce a
negative odd-prime Jacobi witness strictly below log(n)^2. The prime through 4096
cannot equal the even endpoint. This extends the certified strict cell without
claiming an unbounded analytic entrance. -/
theorem exists_odd_prime_negative_phase64_sharp_fixed_cell
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hlo : (64 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ 3209 / 50) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) < (Real.log n) ^ 2 ∧ jacobiSym n p = -1 := by
  obtain ⟨p, hp, ho, hb, hv⟩ :=
    exists_odd_prime_negative_phase64_sharp_fixed_cap hGRH hn hns hlo hhi
  have hbN : p ≤ 4096 := Nat.cast_le.mp (show (p : ℝ) ≤ ((4096 : ℕ) : ℝ) from hb)
  have hpne : p ≠ 4096 := fun he ↦ (by decide : ¬Odd (4096 : ℕ)) (he ▸ ho)
  have hlt : p < 4096 := lt_of_le_of_ne hbN hpne
  have hs : (4096 : ℝ) ≤ (Real.log n) ^ 2 := by nlinarith only [hlo]
  exact ⟨p, hp, ho, (Nat.cast_lt.mpr hlt).trans_le hs, hv⟩

/-- Under GRH, odd nonsquare n and 64<=log(n)<=64.18, obtain a non-one
odd-prime Jacobi witness strictly below log(n)^2. Use the negative witness and exclude
value one. This exports the same wider cell for the second witness predicate. -/
theorem exists_odd_prime_not_one_phase64_sharp_fixed_cell
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hlo : (64 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ 3209 / 50) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) < (Real.log n) ^ 2 ∧ jacobiSym n p ≠ 1 := by
  obtain ⟨p, hp, ho, hb, hv⟩ :=
    exists_odd_prime_negative_phase64_sharp_fixed_cell hGRH hn hns hlo hhi
  exact
    ⟨p, hp, ho, hb, by
      rw [hv]; norm_num only⟩

/-- Under the wider bounded cell and an explicit nonempty negative witness
set, its least odd-prime witness is strictly below log(n)^2. Compare the minimum
with the proved pointwise witness. No search-range bound is used in minimality. -/
theorem primeNegOneWitness_lt_phase64_sharp_fixed_cell
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hlo : (64 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ 3209 / 50)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) < (Real.log n) ^ 2 := by
  obtain ⟨p, hp, ho, hb, hv⟩ :=
    exists_odd_prime_negative_phase64_sharp_fixed_cell hGRH hn hns hlo hhi
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hv⟩)).trans_lt hb

/-- Under the wider bounded cell and an explicit nonempty non-one witness
set, its least odd-prime witness is strictly below log(n)^2. Apply the existing
least-witness comparison to the newly proved pointwise witness. -/
theorem primeNeOneWitness_lt_phase64_sharp_fixed_cell
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hlo : (64 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ 3209 / 50)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) < (Real.log n) ^ 2 := by
  obtain ⟨p, hp, ho, hb, hv⟩ :=
    exists_odd_prime_not_one_phase64_sharp_fixed_cell hGRH hn hns hlo hhi
  exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hv⟩)).trans_lt hb

end PseudoPrime.LLS
