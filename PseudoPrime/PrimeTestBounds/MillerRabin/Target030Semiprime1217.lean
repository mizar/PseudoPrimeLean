/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Count65
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Semiprime1119

/-! # Further semiprime coverage from the extended weighted count -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

set_option maxHeartbeats 4000000 in
-- The weighted multiset family needs extra elaboration steps.
/-- Under GRH, the checked eight-prime table supplies a semiprime witness for
any budget through 65 when the logarithmic and local-envelope bounds hold. -/
theorem exists_prime_reject_supply65 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (budget : ℕ)
    (hbudget : budget ≤ 65) {D X : ℝ} (hD : D ≤ Real.log (target030Row65.getD budget 0 : ℝ))
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
  have hc : F.card = target030Row65.getD budget 0 := target030_family_card65 budget hbudget
  exact
    exists_prime_reject_semiprime_weighted_cell hn ho hp hq hpq hprod S F 19 budget w 10
      (by norm_num only) hsub hprime hbound hw hcost le_rfl (hc ▸ hD) hB hlocal hGRH

/-- The local envelope is within the 0.30 target on a closed interval when
both arguments of its maximum are bounded by the same linear radius. -/
theorem target030_semiprime_envelope {n : ℕ} {A D lo hi : ℝ} (hA : 0 ≤ A) (hlo : lo ≤ Real.log n)
    (hhi : Real.log n ≤ hi) (hleft : A ≤ (5477 / 10000 : ℝ) * lo)
    (hright : (1 - 5477 / 10000 : ℝ) * hi ≤ D) :
    localFullEnvelope (max A (Real.log n - D)) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
  have hmax : max A (Real.log n - D) ≤ (5477 / 10000 : ℝ) * Real.log n := by
    apply max_le
    · linarith only [hlo, hleft]
    · linarith only [hhi, hright]
  have hnonneg : 0 ≤ max A (Real.log n - D) := hA.trans (le_max_left _ _)
  have hsq := mul_self_le_mul_self hnonneg hmax
  have hLsq := sq_nonneg (Real.log n)
  exact (min_le_left _ _).trans ((min_le_left _ _).trans (by nlinarith only [hsq, hLsq]))

/-- Under GRH, the weighted count gives a 0.30 semiprime witness on
`[11.19, 11.63]`. The logarithm and interval inequalities are certified. -/
theorem target030_semiprime65_cell1 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (1119 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 1163 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_supply65 hn ho hp hq hpq hprod hGRH 61 (by decide) (D := (5262 / 1000 : ℝ))
  · change (5262 / 1000 : ℝ) ≤ Real.log (193 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 193 8 32 (5262 / 1000) 6 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only at ⊢
    exact h
  · nlinarith only [hL]
  · apply
      target030_semiprime_envelope (lo := (1119 / 100 : ℝ)) (hi := (1163 / 100 : ℝ))
        (by norm_num only) hL hU
    all_goals norm_num only

/-- Under GRH, the weighted count gives a 0.30 semiprime witness on
`[11.63, 11.89]`. The logarithm and interval inequalities are certified. -/
theorem target030_semiprime65_cell2 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (1163 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 1189 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_supply65 hn ho hp hq hpq hprod hGRH 63 (by decide) (D := (5379 / 1000 : ℝ))
  · change (5379 / 1000 : ℝ) ≤ Real.log (217 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 217 8 32 (5379 / 1000) 6 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only at ⊢
    exact h
  · nlinarith only [hL]
  · apply
      target030_semiprime_envelope (lo := (1163 / 100 : ℝ)) (hi := (1189 / 100 : ℝ))
        (by norm_num only) hL hU
    all_goals norm_num only

/-- Under GRH, the weighted count gives a 0.30 semiprime witness on
`[11.89, 12.17]`. The logarithm and interval inequalities are certified. -/
theorem target030_semiprime65_cell3 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (1189 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 1217 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_supply65 hn ho hp hq hpq hprod hGRH 65 (by decide) (D := (5505 / 1000 : ℝ))
  · change (5505 / 1000 : ℝ) ≤ Real.log (246 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 246 8 32 (5505 / 1000) 6 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only at ⊢
    exact h
  · nlinarith only [hL]
  · apply
      target030_semiprime_envelope (lo := (1189 / 100 : ℝ)) (hi := (1217 / 100 : ℝ))
        (by norm_num only) hL hU
    all_goals norm_num only

/-- Under GRH, every distinct odd semiprime with logarithm in `[8, 12.17]`
has a 0.30 rejecting prime. Three continuous weighted-count intervals extend
the previous coverage through 11.19. -/
theorem exists_prime_reject_03_semiprime_1217 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 1217 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases h1 : Real.log n ≤ 1119 / 100
  · exact exists_prime_reject_03_semiprime_1119 hn ho hp hq hpq hprod hGRH hL h1
  · by_cases h2 : Real.log n ≤ 1163 / 100
    · exact target030_semiprime65_cell1 hn ho hp hq hpq hprod hGRH (le_of_not_ge h1) h2
    · by_cases h3 : Real.log n ≤ 1189 / 100
      · exact target030_semiprime65_cell2 hn ho hp hq hpq hprod hGRH (le_of_not_ge h2) h3
      · exact target030_semiprime65_cell3 hn ho hp hq hpq hprod hGRH (le_of_not_ge h3) hU

end PseudoPrime.PrimeTestBounds.MillerRabin
