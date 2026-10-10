/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.CosetPrimeBounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimitiveComparison

/-! # Logarithmic Mangoldt sums in a subgroup coset

The absence of primes in the coset removes the prime terms. The remaining
nonnegative sum is bounded by the unrestricted contribution of composite prime powers.
This is the elementary reduction preceding the upper bounds in Section 4.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- A natural residue belongs to `aH` when it is represented by a unit whose quotient
by `a` lies in `H`. Prime membership adds primality to this predicate.
Unlike the prime set, this predicate also selects higher prime powers. -/
def residueInCoset (q : ℕ) (H : Subgroup (ZMod q)ˣ) (a : (ZMod q)ˣ) (n : ℕ) : Prop :=
  ∃ u : (ZMod q)ˣ, a⁻¹ * u ∈ H ∧ (u : ZMod q) = (n : ZMod q)

open Classical in
/-- The logarithmic Mangoldt sum on positive indices up to the cutoff in `aH`.
Composite prime powers remain even when this coset contains no primes below the cutoff.
This is the arithmetic quantity compared with character averages in Section 4. -/
noncomputable def cosetLogWeightedSum (q : ℕ) (H : Subgroup (ZMod q)ˣ) (a : (ZMod q)ˣ) (x : ℝ) :
    ℝ :=
  ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (residueInCoset q H a),
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm x n

/-- At a positive cutoff, the coset logarithmic sum is nonnegative.
Every selected index is positive and at most the cutoff, so both Mangoldt and
logarithmic weights are nonnegative. This permits upper comparisons termwise. -/
theorem cosetLogWeightedSum_nonneg {q : ℕ} (H : Subgroup (ZMod q)ˣ) (a : (ZMod q)ˣ) {x : ℝ}
    (hx : 0 < x) : 0 ≤ cosetLogWeightedSum q H a x := by
  classical
  apply Finset.sum_nonneg
  intro n hn
  obtain ⟨hn0, hnx⟩ := Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1
  exact AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm_nonneg hx hn0 hnx

/-- If there are no coset primes through a positive cutoff, its logarithmic sum is
bounded by the unrestricted sum on nonprime indices. Vanishing Mangoldt coefficients
remove indices that are not prime powers; the remaining indices are composite prime powers.
This is the first upper-bound reduction in the proof of Theorem 1.4. -/
theorem cosetLogWeightedSum_le_nonprime_sum {q : ℕ} (H : Subgroup (ZMod q)ˣ) (a : (ZMod q)ˣ) {x : ℝ}
    (hx : 0 < x) (hno : ∀ p : ℕ, p ∈ primesInCoset q H a → ¬(p : ℝ) ≤ x) :
    cosetLogWeightedSum q H a x ≤
      ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n ↦ ¬n.Prime),
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm x n := by
  classical
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    obtain ⟨hni, hcos⟩ := Finset.mem_filter.mp hn
    refine Finset.mem_filter.mpr ⟨hni, ?_⟩
    intro hp
    exact hno n ⟨hp, hcos⟩ ((Nat.cast_le.mpr (Finset.mem_Ioc.mp hni).2).trans (Nat.floor_le hx.le))
  · intro n hn _
    obtain ⟨hn0, hnx⟩ := Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1
    exact AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm_nonneg hx hn0 hnx

/-- At a positive cutoff, if the coset weighted sum exceeds the unrestricted
nonprime contribution, there is a coset prime through the cutoff. Contradict the
nonprime upper comparison. This turns the Section 4 weighted sandwich into a witness. -/
theorem exists_prime_in_coset_le_of_weighted_gap {q : ℕ} (H : Subgroup (ZMod q)ˣ) (a : (ZMod q)ˣ)
    {x : ℝ} (hx : 0 < x)
    (hgap :
      (∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n ↦ ¬n.Prime),
          AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm x n) <
        cosetLogWeightedSum q H a x) :
    ∃ p : ℕ, p ∈ primesInCoset q H a ∧ (p : ℝ) ≤ x := by
  classical
  by_contra h
  exact
    (not_le_of_gt hgap) (cosetLogWeightedSum_le_nonprime_sum H a hx (fun p hp hpx ↦ h ⟨p, hp, hpx⟩))

/-- For a nonzero modulus and positive cutoff, a strict weighted gap bounds the least
coset prime by the cutoff. Construct a bounded witness by the weighted comparison and
transfer its bound to the minimum. This connects the analytic sandwich to Theorem 1.4. -/
theorem exists_least_prime_in_coset_le_of_weighted_gap {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (a : (ZMod q)ˣ) {x : ℝ} (hx : 0 < x)
    (hgap :
      (∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n ↦ ¬n.Prime),
          AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm x n) <
        cosetLogWeightedSum q H a x) :
    ∃ p : ℕ, IsLeast (primesInCoset q H a) p ∧ (p : ℝ) ≤ x := by
  obtain ⟨p, hp, hpx⟩ := exists_prime_in_coset_le_of_weighted_gap H a hx hgap
  obtain ⟨r, hr, hb⟩ := exists_least_prime_in_coset_le_or H a (A := x) (B := x) ⟨p, hp, Or.inl hpx⟩
  exact ⟨r, hr, hb.elim id id⟩

/-- For the identity subgroup, coset membership is equality to the unit residue.
The quotient condition forces the representing unit to equal the coset representative.
This identifies subgroup-coset sums with arithmetic-progression sums. -/
theorem residueInCoset_bot_iff {q : ℕ} (a : (ZMod q)ˣ) (n : ℕ) :
    residueInCoset q ⊥ a n ↔ (n : ZMod q) = (a : ZMod q) := by
  constructor
  · rintro ⟨u, hu, hn⟩
    have he : a = u := inv_mul_eq_one.mp (Subgroup.mem_bot.mp hu)
    exact hn.symm.trans (congrArg Units.val he.symm)
  · intro hn
    exact ⟨a, Subgroup.mem_bot.mpr (inv_mul_cancel a), hn.symm⟩

open Classical in
/-- The logarithmic sum for the identity subgroup equals the sum in its residue class.
Identify coset membership with residue equality and rewrite the positive integer interval.
This connects the character-average bounds to the least-prime progression argument. -/
theorem cosetLogWeightedSum_bot_eq {q : ℕ} (a : (ZMod q)ˣ) (x : ℝ) :
    cosetLogWeightedSum q ⊥ a x =
      ∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n : ℕ ↦ (n : ZMod q) = (a : ZMod q)),
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm x n := by
  unfold cosetLogWeightedSum
  have he : Finset.Ioc 0 ⌊x⌋₊ = Finset.Icc 1 ⌊x⌋₊ := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc, Nat.succ_le_iff]
  simp only [he, residueInCoset_bot_iff]

end PseudoPrime.LLS.PaperStatements
