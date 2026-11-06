/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030SquareLog10
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030EarlyCells

/-! # Extended weighted semiprime cells -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

set_option maxHeartbeats 4000000 in
-- The finite family is expanded during elaboration.
/-- Under GRH, the extended weighted table supplies a semiprime witness for
any budget through 58 when the logarithmic and local bounds hold. -/
theorem exists_prime_reject_supply58 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (budget : ℕ)
    (hbudget : budget ≤ 58) {D X : ℝ} (hD : D ≤ Real.log (target030SquareRow.getD budget 0 : ℝ))
    (hB : (19 : ℝ) ≤ X)
    (hlocal : localFullEnvelope (max ((budget : ℝ) / 10) (Real.log n - D)) ≤ X) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let S := target030FirstPrimes.toFinset
  let w := target030FirstWeight
  let F := weightedPrimeFamily S w budget
  have hprime : ∀ r ∈ S, r.Prime := fun r hr ↦
    (target030_first_prime_supply r (List.mem_toFinset.mp hr)).1
  have hbound : ∀ r ∈ S, r ≤ 19 := fun r hr ↦
    (target030_first_prime_supply r (List.mem_toFinset.mp hr)).2
  have hw : ∀ r ∈ S, Real.log r ≤ (w r : ℝ) / 10 := fun r hr ↦
    target030_first_weight_bounds r (List.mem_toFinset.mp hr)
  have hwpos : ∀ r ∈ S, 1 ≤ w r := fun r hr ↦ target030First_labels.2.2 r (List.mem_toFinset.mp hr)
  have hsub : ∀ T ∈ F, ∀ r ∈ T, r ∈ S := fun T hT ↦
    ((mem_weightedPrimeFamily S w budget hwpos T).mp hT).1
  have hcost : ∀ T ∈ F, (T.map w).sum ≤ budget := fun T hT ↦
    ((mem_weightedPrimeFamily S w budget hwpos T).mp hT).2
  have hc : F.card = target030SquareRow.getD budget 0 := target030Square_family_card budget hbudget
  exact
    exists_prime_reject_semiprime_weighted_cell hn ho hp hq hpq hprod S F 19 budget w 10
      (by norm_num only) hsub hprime hbound hw hcost le_rfl (hc ▸ hD) hB hlocal hGRH

/-- The budget-55 weighted count proves the 0.30 semiprime bound on `[10.059, 10.384]`. -/
theorem target030_semiprime_cell_7 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (10059 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 10384 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_supply58 hn ho hp hq hpq hprod hGRH 55 (by decide) (D := (4875 / 1000 : ℝ))
  · change (4875 / 1000 : ℝ) ≤ Real.log (131 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 131 8 32 (4875 / 1000) 5 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only at ⊢
    exact h
  · nlinarith only [hL]
  · apply
      local_envelope_le_03_interval (lo := (10059 / 1000 : ℝ)) (hi := (10384 / 1000 : ℝ)) (R :=
        (5509 / 1000 : ℝ)) (by norm_num only) hL hU
    all_goals norm_num only

/-- The budget-56 weighted count proves the 0.30 semiprime bound on `[10.384, 10.614]`. -/
theorem target030_semiprime_cell_8 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (10384 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 10614 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_supply58 hn ho hp hq hpq hprod hGRH 56 (by decide) (D := (4927 / 1000 : ℝ))
  · change (4927 / 1000 : ℝ) ≤ Real.log (138 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 138 8 32 (4927 / 1000) 5 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only at ⊢
    exact h
  · nlinarith only [hL]
  · apply
      local_envelope_le_03_interval (lo := (10384 / 1000 : ℝ)) (hi := (10614 / 1000 : ℝ)) (R :=
        (5687 / 1000 : ℝ)) (by norm_num only) hL hU
    all_goals norm_num only

/-- Under GRH, the eight weighted cells give a 0.30 rejecting prime for every
distinct odd semiprime with logarithm in `[8, 10.614]`. -/
theorem exists_prime_reject_03_semiprime_10614 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 10614 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases h1 : Real.log n ≤ 10059 / 1000
  · exact exists_prime_reject_03_semiprime_log10 hn ho hp hq hpq hprod hGRH hL h1
  · by_cases h2 : Real.log n ≤ 10384 / 1000
    · exact target030_semiprime_cell_7 hn ho hp hq hpq hprod hGRH (le_of_not_ge h1) h2
    · exact target030_semiprime_cell_8 hn ho hp hq hpq hprod hGRH (le_of_not_ge h2) hU

end PseudoPrime.PrimeTestBounds.MillerRabin
