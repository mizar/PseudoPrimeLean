/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.TriangularTunedBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.FromLLS
/-! Whole-domain cumulative MR bounds with certified high-range history. -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin
/-- The least rejecting prime for an odd composite above one, and zero otherwise.
The infimum ranges over primes rejecting the canonical strong MR test.
Under GRH the set is nonempty and its infimum is an actual least witness.
Zero outside the target domain makes cumulative maxima total, including empty ranges. -/
noncomputable def compositeLeastPrime (n : ℕ) : ℕ := by
  classical
  exact if 1 < n ∧ Odd n ∧ ¬n.Prime then
    sInf {p : ℕ | p.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n)} else 0

/-- Under GRH an odd composite has its canonical least rejecting prime below log squared.
Transfer the existing actual prime witness by the natural infimum property.
This supplies a safe bound for all inputs preceding any high-profile entrance. -/
theorem compositeLeastPrime_le_log_sq (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime) :
    (compositeLeastPrime n : ℝ) ≤ Real.log n ^ 2 := by
  obtain ⟨p, hp, hb, hr⟩ := exists_prime_millerRabin_witness_le_log_sq hGRH hn ho hc
  have hfail : ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) :=
    PrimeTest.not_strongMillerRabinPass_iff.mpr hr
  simp only [compositeLeastPrime, ite_eq_left (show 1 < n ∧ Odd n ∧ ¬n.Prime from ⟨hn, ho, hc⟩)]
  have hm := Nat.sInf_le (s := {q : ℕ |
    q.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n)}) ⟨hp, hfail⟩
  exact (Nat.cast_le.mpr hm).trans hb

/-- The history-preserving bound for one triangular profile at logarithmic upper scale.
Take the maximum of the entrance squared and the current certified quadratic cutoff.
The entrance value covers all earlier inputs via the global log-square witness theorem.
The pointwise public envelope is unchanged. -/
noncomputable def profileCumulative (f : TriangularProfile) (L : ℝ) : ℝ :=
  max (f.T ^ 2) (f.C * L ^ 2)

/-- Every target input below the natural upper bound satisfies a profile's cumulative bound.
Before the real entrance use log squared; after it use the actual triangular witness.
Compare logarithms only for positive natural inputs. Non-target inputs contribute zero. -/
theorem compositeLeastPrime_le_profile (f : TriangularProfile)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {n N : ℕ} (hnN : n ≤ N) :
    (compositeLeastPrime n : ℝ) ≤ profileCumulative f (Real.log N) := by
  have hC : 0 ≤ f.C := (sq_nonneg f.a).trans f.square
  by_cases hn : 1 < n ∧ Odd n ∧ ¬n.Prime
  · have hl0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (Nat.one_le_cast.mpr hn.1.le)
    have hlog := Real.log_le_log (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn.1))
      (Nat.cast_le.mpr hnN)
    by_cases he : f.T ≤ Real.log n
    · obtain ⟨p, hp, hb, hr⟩ := exists_prime_triangularProfile f hn.1 hn.2.1 hn.2.2 hGRH he
      have hleast : compositeLeastPrime n ≤ p := by
        rw [compositeLeastPrime, ite_eq_left hn]
        exact Nat.sInf_le (s := {q : ℕ |
          q.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n)}) ⟨hp, hr⟩
      exact ((Nat.cast_le.mpr hleast).trans hb).trans
        ((mul_le_mul_of_nonneg_left ((sq_le_sq₀ hl0 (hl0.trans hlog)).mpr hlog) hC).trans
          (le_max_right _ _))
    · have hT : 0 ≤ f.T := (by norm_num only : (0 : ℝ) ≤ 30000000000).trans f.entry
      exact (compositeLeastPrime_le_log_sq hGRH hn.1 hn.2.1 hn.2.2).trans
        (((sq_le_sq₀ hl0 hT).mpr (le_of_not_ge he)).trans (le_max_left _ _))
  · rw [compositeLeastPrime, ite_eq_right hn, Nat.cast_zero]
    exact (sq_nonneg f.T).trans (le_max_left _ _)

/-- The explicit cumulative bound from the seven certified high-range profiles.
Intersect the global log-square bound with each profile's history-preserving maximum.
Only seven real expressions are used, with no enumeration of inputs or monotonicity
requirement on the pointwise selected envelope. -/
noncomputable def highCumulativeEnvelope (N : ℕ) : ℝ :=
  min (Real.log N ^ 2)
    (Finset.univ.inf' Finset.univ_nonempty
      (fun i : Fin 7 ↦ profileCumulative (triangularTunedProfile i) (Real.log N)))

/-- Under GRH every individual least-witness value below an arbitrary natural upper bound
is bounded by the high cumulative envelope. Intersect the global and seven profile bounds.
This covers all earlier inputs even when a pointwise guard lowers the current cutoff. -/
theorem compositeLeastPrime_le_cumulative
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {n N : ℕ} (hnN : n ≤ N) :
    (compositeLeastPrime n : ℝ) ≤ highCumulativeEnvelope N := by
  apply le_min ?_ (Finset.le_inf' _ _ (fun i _ ↦ compositeLeastPrime_le_profile _ hGRH hnN))
  by_cases hn : 1 < n ∧ Odd n ∧ ¬n.Prime
  · have hl0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (Nat.one_le_cast.mpr hn.1.le)
    have hlog := Real.log_le_log (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn.1))
      (Nat.cast_le.mpr hnN)
    exact (compositeLeastPrime_le_log_sq hGRH hn.1 hn.2.1 hn.2.2).trans
      ((sq_le_sq₀ hl0 (hl0.trans hlog)).mpr hlog)
  · rw [compositeLeastPrime, ite_eq_right hn, Nat.cast_zero]
    exact sq_nonneg _

/-- The maximum of least rejecting primes over odd composites at most the upper bound.
Use the finite natural supremum of the total individual function, whose non-target values
are zero. Thus an empty target range has value zero without an extra nonemptiness premise.
This definition is mathematical and requires no generated exhaustive certificate. -/
noncomputable def cumulativeLeastPrime (N : ℕ) : ℕ :=
  (Finset.range (N + 1)).sup compositeLeastPrime

/-- Under GRH the cumulative maximum is bounded by the explicit high-range formula
at every natural upper bound, including zero and ranges with no odd composite.
Bound each member by the real formula, pass through its natural floor, and take
the finite supremum. This is a whole-domain cumulative statement. -/
theorem cumulativeLeastPrime_le_high
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (N : ℕ) :
    (cumulativeLeastPrime N : ℝ) ≤ highCumulativeEnvelope N := by
  have h0 : 0 ≤ highCumulativeEnvelope N :=
    (Nat.cast_nonneg (compositeLeastPrime 0)).trans
      (compositeLeastPrime_le_cumulative hGRH (Nat.zero_le N))
  have hb : cumulativeLeastPrime N ≤ ⌊highCumulativeEnvelope N⌋₊ := by
    apply Finset.sup_le
    intro n hn
    exact (Nat.le_floor_iff h0).mpr
      (compositeLeastPrime_le_cumulative hGRH
        (Nat.le_of_lt_succ (Finset.mem_range.mp hn)))
  exact (Nat.cast_le.mpr hb).trans (Nat.floor_le h0)
/-- Under GRH the total individual value at an odd composite is an actual prime
rejecting strong MR and is least among all rejecting primes. Obtain nonemptiness
from the existing witness theorem and apply the natural infimum specification. -/
theorem compositeLeastPrime_spec (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime) :
    (compositeLeastPrime n).Prime ∧
      ¬PrimeTest.StrongMillerRabinPass n (compositeLeastPrime n : ZMod n) ∧
      ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) →
        compositeLeastPrime n ≤ q := by
  obtain ⟨p, hp, _, hr⟩ := exists_prime_millerRabin_witness_le_log_sq hGRH hn ho hc
  have hfail : ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) :=
    PrimeTest.not_strongMillerRabinPass_iff.mpr hr
  have hs : {q : ℕ | q.Prime ∧
      ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n)}.Nonempty := ⟨p, hp, hfail⟩
  rw [compositeLeastPrime, ite_eq_left (show 1 < n ∧ Odd n ∧ ¬n.Prime from ⟨hn, ho, hc⟩)]
  exact ⟨(Nat.sInf_mem hs).1, (Nat.sInf_mem hs).2,
    fun q hq hqr ↦ Nat.sInf_le (s := {q : ℕ |
      q.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n)}) ⟨hq, hqr⟩⟩

/-- Once the current quadratic value covers a profile's retained history,
the whole cumulative envelope is at most that value. This certifies recovery
of each improved high-range coefficient without discarding earlier inputs. -/
theorem highCumulative_le_recovered (N : ℕ) (i : Fin 7)
    (hr : (triangularTunedProfile i).T ^ 2 ≤
      (triangularTunedProfile i).C * Real.log N ^ 2) :
    highCumulativeEnvelope N ≤
      (triangularTunedProfile i).C * Real.log N ^ 2 := by
  apply (min_le_right _ _).trans
  have hi := Finset.inf'_le
    (fun i : Fin 7 ↦ profileCumulative (triangularTunedProfile i) (Real.log N))
    (Finset.mem_univ i)
  exact hi.trans_eq (max_eq_right hr)
end PseudoPrime.PrimeTestBounds.MillerRabin
