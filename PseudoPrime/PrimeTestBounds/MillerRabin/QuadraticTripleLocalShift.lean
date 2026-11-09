/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimePairLocalData
public import PseudoPrime.PrimeTestBounds.MillerRabin.LocalEvenWitness
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticTripleUniformSpacing

/-! # Local even shifts for ordered prime triples -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A two-prime divisor gives a rejecting prime at the even shifted radius
under GRH and a certified correction. The factor three is an immediate
witness; otherwise the existing local subgroup lies at a divisor no larger
than the pair. This supplies the witness interface for the low-range cells. -/
theorem exists_prime_reject_pair_shift {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p * q ∣ n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {b d s : ℝ} (hb : 8 ≤ b) (hd : d < LLS.PaperStatements.fullEndpointEvenGapCorrection b)
    (hs : Real.log ((p * q : ℕ) : ℝ) ≤ s) :
    ∃ a : ℕ,
      a.Prime ∧
        (a : ℝ) ≤ (max b (s - d)) ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (a : ZMod n) := by
  rcases prime_pair_local_data hn ho hp hq hpq with hthree | ⟨m, hm, hmn, hmpq, H, hH, hpass⟩
  · have hy : 8 ≤ max b (s - d) := hb.trans (le_max_left _ _)
    have hy2 : (3 : ℝ) ≤ (max b (s - d)) ^ 2 := by nlinarith only [hy, sq_nonneg (max b (s - d))]
    exact
      ⟨3, Nat.prime_three, hy2,
        PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn ho Nat.prime_three hthree⟩
  · let : NeZero m := ⟨Nat.ne_of_gt hm⟩
    have hms : Real.log m ≤ s :=
      (Real.log_le_log (Nat.cast_pos.mpr hm) (Nat.cast_le.mpr hmpq)).trans hs
    exact exists_prime_reject_of_local_shift hn ho hmn H hH hpass hGRH hb hd hms

/-- An ordered uniform Korselt triple with least factor at least five has a
rejecting prime under GRH at the even shifted radius with the explicit spacing
correction at `P`. The logarithmic input bound controls the least factor,
and the resulting pair-modulus bound feeds the local witness theorem. -/
theorem uniformKorselt_reject_shift {n p q r : ℕ} (hn : 1 < n) (ho : Odd n) (hnp : n = p * q * r)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hpO : Odd p) (hqO : Odd q) (hrO : Odd r)
    (hpq : p < q) (hqr : q < r) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (P : ℝ) (hp5 : 5 ≤ (p : ℝ))
    (hP : 0 < P) (hlog : Real.log n < 3 * Real.log P) {b d : ℝ} (hb : 8 ≤ b)
    (hd : d < LLS.PaperStatements.fullEndpointEvenGapCorrection b) :
    ∃ a : ℕ,
      a.Prime ∧
        (a : ℝ) ≤
          (max b
              ((2 / 3 : ℝ) * Real.log n -
                (1 / 3 : ℝ) * Real.log (1 + (4 * Real.sqrt (P - 1) - 2) / P) -
                d)) ^
            2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (a : ZMod n) := by
  have hshift :=
    uniformKorselt_log_shift_of_log_bound hnp hp hq hr hpO hqO hrO hpq hqr hu P hp5 hP hlog
  have hpqd : p * q ∣ n := hnp ▸ dvd_mul_right (p * q) r
  have hs :
    Real.log ((p * q : ℕ) : ℝ) ≤
      (2 / 3 : ℝ) * Real.log n - (1 / 3 : ℝ) * Real.log (1 + (4 * Real.sqrt (P - 1) - 2) / P) := by
    rw [Nat.cast_mul]
    linarith only [hshift]
  exact exists_prime_reject_pair_shift hn ho hp hq hpqd hGRH hb hd hs

end PseudoPrime.PrimeTestBounds.MillerRabin
