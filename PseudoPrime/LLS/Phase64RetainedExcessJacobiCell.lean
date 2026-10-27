/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.Phase64RetainedExcessBounds
public import PseudoPrime.LLS.Phase64LowerStartJacobiCell

/-! # A wider fixed-scale witness cell retaining the ramified aggregate saving -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: actual Jacobi data, RH, scale in [1600,1700], prefix at least 500,
and any real excess cap e. Claim: the local budget is at most the existing
numerical budget plus e-13/5. Preserve the excess saving through every comparison.
Role: admit sharper rational local aggregates without defining a new budget. -/
theorem phase64_local_budget_le_numerical_of_excess_cap {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) (hRH : RiemannHypothesis) (q : ℕ)
    {x b e : ℝ} (hlo : 1600 ≤ x) (hhi : x ≤ 1700) (hb : 500 ≤ b)
    (he : Analysis.phase64RamifiedExcess x ≤ e) :
    phase64JacobiLocalBudget bridge q x b ≤ phase64NumericalJacobiBudget n q x + (e - 13 / 5) := by
  have h1 := phase64_jacobi_local_budget_le_ramified bridge q hlo b
  have h2 := phase64_ramified_budget_le_finite bridge q hlo hhi b
  have h3 :
    phase64FiniteJacobiBudget n q x b ≤ phase64ScalarJacobiBudget n q x b + (e - 13 / 5) := by
    dsimp only [phase64FiniteJacobiBudget, phase64ScalarJacobiBudget]
    linarith only [he]
  have h4 := phase64_scalar_budget_le_euler n q x b
  have h5 := phase64_euler_budget_le_total n q x hb
  have h6 := phase64_total_budget_le_numerical hRH n q x
  linarith only [h1, h2, h3, h4, h5, h6]

/-- Input: positive n, log(n) <= 64.36 and log(q) <= 65.76. Claim: the numerical
budget minus 97/1000 is below the certified fixed principal-ramp lower bound.
Apply scalar caps and rational arithmetic. Role: use the retained excess saving. -/
theorem phase64_retained_fixed_budget_lt_margin {n q : ℕ} (hn : 0 < n)
    (hnL : Real.log n ≤ 1609 / 25) (hqL : Real.log q ≤ 1644 / 25) :
    phase64NumericalJacobiBudget n q (163840 / 99) - 97 / 1000 < 1375 / (20341 / 500) := by
  have h4 : Real.log (4 * (n : ℝ)) ≤ (1609 / 25 : ℝ) + 7 / 5 := by
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

/-- Under GRH, odd nonsquare n and 10 <= log(n) <= 64.36, there is a negative
odd-prime Jacobi witness at most 4093. Contradict the no-witness local comparison
using the retained numerical saving and the existing fixed-scale lower bound.
Role: widen the bounded input cell without recomputing endpoint sums. -/
theorem exists_odd_prime_negative_phase64_retained_fixed_cap
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hlo : (10 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ 1609 / 25) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ p ≤ 4093 ∧ jacobiSym n p = -1 := by
  obtain ⟨bridge⟩ := NumberTheory.exists_jacobiCharacterArithmeticData hn.pos hn hns
  obtain ⟨hq, hm, hlog⟩ := phase64_ambient_four_mul_data_from_log_ten hn hlo
  have hqlog : Real.log ((4 * n : ℕ) : ℝ) ≤ 1644 / 25 := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    linarith only [hlog, hhi]
  have hB := phase64_retained_fixed_budget_lt_margin hn.pos hhi hqlog
  have hA := phase64_principalRamp_sharp_lower
  have he :=
    Analysis.phase64_ramified_excess_le_2503 (by norm_num only : (1600 : ℝ) ≤ 163840 / 99)
      (by norm_num only : (163840 / 99 : ℝ) ≤ 1660)
  have hb :=
    phase64_local_budget_le_numerical_of_excess_cap bridge hGRH.riemann (4 * n)
      (by norm_num only : (1600 : ℝ) ≤ 163840 / 99) (by norm_num only : (163840 / 99 : ℝ) ≤ 1700)
      (by norm_num only : (500 : ℝ) ≤ 4096) he
  apply Classical.byContradiction
  intro h
  have hno : ∀ p : ℕ, p.Prime → Odd p → (p : ℝ) ≤ (64 : ℝ) ^ 2 → jacobiSym n p ≠ -1 := by
    intro p hp ho hpb hv
    have hnB : p ≤ 4096 :=
      Nat.cast_le.mp
        (show (p : ℝ) ≤ ((4096 : ℕ) : ℝ) from by
          norm_num only at hpb
          exact hpb)
    exact h ⟨p, hp, ho, prime_le_4093_of_le_4096 hp hnB, hv⟩
  have hc :=
    phase64_jacobi_no_negative_local_comparison bridge hGRH hq hm (by norm_num only : (64 : ℝ) ≤ 64)
      (by norm_num only : (64 : ℝ) ≤ 64001 / 1000) hno
  norm_num only at hc hb
  dsimp only [principalRampDifference] at hA
  linarith only [hc, hb, hA, hB]

/-- Under GRH, odd nonsquare n and 63.977 <= log(n) <= 64.36, obtain a negative
odd-prime Jacobi witness strictly below log(n)^2. Compare the fixed cutoff 4093
with the lower endpoint squared. Role: export the wider bounded analytic cell. -/
theorem exists_odd_prime_negative_phase64_retained_cell
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hlo : (63977 / 1000 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ 1609 / 25) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) < (Real.log n) ^ 2 ∧ jacobiSym n p = -1 := by
  obtain ⟨p, hp, ho, hb, hv⟩ :=
    exists_odd_prime_negative_phase64_retained_fixed_cap hGRH hn hns
      ((by norm_num only : (10 : ℝ) ≤ 63977 / 1000).trans hlo) hhi
  have hs : (4093 : ℝ) < (Real.log n) ^ 2 := by nlinarith only [hlo]
  exact ⟨p, hp, ho, (Nat.cast_le.mpr hb).trans_lt hs, hv⟩

/-- Under the same GRH and odd-nonsquare interval hypotheses, obtain a non-one
odd-prime Jacobi witness strictly below log(n)^2. Use the negative witness.
Role: export the lowered bounded interval for the non-one predicate. -/
theorem exists_odd_prime_not_one_phase64_retained_cell
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hlo : (63977 / 1000 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ 1609 / 25) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) < (Real.log n) ^ 2 ∧ jacobiSym n p ≠ 1 := by
  obtain ⟨p, hp, ho, hb, hv⟩ := exists_odd_prime_negative_phase64_retained_cell hGRH hn hns hlo hhi
  exact
    ⟨p, hp, ho, hb, by
      rw [hv]; norm_num only⟩

/-- Under the wider bounded cell and an explicit nonempty negative witness
set, its least odd-prime witness is strictly below log(n)^2. Compare the minimum
with the proved pointwise witness. No search-range bound is used in minimality. -/
theorem primeNegOneWitness_lt_phase64_retained_cell
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hlo : (63977 / 1000 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ 1609 / 25)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) < (Real.log n) ^ 2 := by
  obtain ⟨p, hp, ho, hb, hv⟩ := exists_odd_prime_negative_phase64_retained_cell hGRH hn hns hlo hhi
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hv⟩)).trans_lt hb

/-- Under the wider bounded cell and an explicit nonempty non-one witness
set, its least odd-prime witness is strictly below log(n)^2. Apply the existing
least-witness comparison to the newly proved pointwise witness. -/
theorem primeNeOneWitness_lt_phase64_retained_cell
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hlo : (63977 / 1000 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ 1609 / 25)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) < (Real.log n) ^ 2 := by
  obtain ⟨p, hp, ho, hb, hv⟩ := exists_odd_prime_not_one_phase64_retained_cell hGRH hn hns hlo hhi
  exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hv⟩)).trans_lt hb

end PseudoPrime.LLS
