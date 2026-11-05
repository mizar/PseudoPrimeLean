/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.CountCandidateData

/-! # Coverage chains for odd prime squares -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Check a chain of candidate indices extending an initial logarithmic coverage cap.
Each candidate must have cutoff at most `B` and begin at or below the current cap; it
extends coverage to twice its strict multichoose endpoint. The final cap must reach `target`.
The separate soundness theorem combines these rational checks with checked candidate data. -/
def squareChainCheck (L : List CandidateLogData) (B : ℕ) (cap target : ℚ) : List ℕ → Bool
  | [] => decide (target ≤ cap)
  | i :: is =>
    match L[i]? with
    | none => false
    | some d =>
      decide (d.candidate.bound ≤ B ∧ d.candidate.upper ≤ cap) &&
        squareChainCheck L B (max cap (2 * d.candidate.lower)) target is

/-- A checked chain extends an initial square witness bound from `cap` through `target`.
Assume RH, an odd prime square, and checked candidate certificates. Induction on the chain
uses the initial witness below the current cap and the candidate count above it; matching
endpoints overlap because the product-size inequality is strict only above the cap. -/
theorem squareChainCheck_sound {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (L : List CandidateLogData)
    (hL : L.all CandidateLogData.certifiedCheck = true) (B : ℕ) (ids : List ℕ) (cap target : ℚ)
    (hcheck : squareChainCheck L B cap target ids = true)
    (hbase :
      Real.log n ≤ (cap : ℝ) →
        ∃ r : ℕ, r.Prime ∧ r ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n))
    (hlog : Real.log n ≤ (target : ℝ)) :
    ∃ r : ℕ, r.Prime ∧ r ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  induction ids generalizing cap with
  | nil =>
    have htc : target ≤ cap := of_decide_eq_true hcheck
    exact hbase (hlog.trans ((Rat.cast_le (K := ℝ)).mpr htc))
  | cons i is ih =>
    cases heq : L[i]? with
    | none => simp only [squareChainCheck, heq, Bool.false_eq_true] at hcheck
    | some
      d =>
      have hc :
        (decide (d.candidate.bound ≤ B ∧ d.candidate.upper ≤ cap) &&
            squareChainCheck L B (max cap (2 * d.candidate.lower)) target is) =
          true := by
        simpa only [squareChainCheck, heq] using hcheck
      have hparts := Bool.and_eq_true_iff.mp hc
      have hd : d.candidate.bound ≤ B ∧ d.candidate.upper ≤ cap := of_decide_eq_true hparts.1
      apply ih (max cap (2 * d.candidate.lower)) hparts.2
      intro hx
      by_cases hsmall : Real.log n ≤ (cap : ℝ)
      · exact hbase hsmall
      · have hlo : (d.candidate.upper : ℝ) < Real.log n :=
          ((Rat.cast_le (K := ℝ)).mpr hd.2).trans_lt (lt_of_not_ge hsmall)
        have hhi : Real.log n ≤ 2 * (d.candidate.lower : ℝ) := by
          simp only [Rat.cast_max, Rat.cast_mul, Rat.cast_ofNat] at hx
          exact (le_max_iff.mp hx).resolve_left hsmall
        obtain ⟨r, hr, hrB, hfail⟩ :=
          candidateList_square hn ho hp hp2 hpow hRH L hL d (List.mem_of_getElem? heq) hlo hhi
        exact ⟨r, hr, hrB.trans hd.1, hfail⟩

/-- An odd prime square below a logarithmic seed cap has a rejecting prime at most `B`
when the cap is strictly below `2 log (B + 1)`. Otherwise its prime factor would be at
least `B + 1`, contradicting logarithm monotonicity; the factor itself is a witness. -/
theorem exists_prime_reject_square_seed {n p B : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hpow : n = p ^ 2) (cap : ℚ) (hcap : (cap : ℝ) < 2 * Real.log (B + 1))
    (hlog : Real.log n ≤ (cap : ℝ)) :
    ∃ r : ℕ, r.Prime ∧ r ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hpB : p ≤ B := by
    by_contra hpB
    have hpge : (B : ℝ) + 1 ≤ p := by exact_mod_cast (Nat.succ_le_of_lt (lt_of_not_ge hpB))
    have hpos : (0 : ℝ) < (B : ℝ) + 1 :=
      add_pos_of_nonneg_of_pos (Nat.cast_nonneg B) (by norm_num only)
    have hpLog := Real.log_le_log hpos hpge
    have hnLog : Real.log n = 2 * Real.log p := by
      rw [hpow, Nat.cast_pow, Real.log_pow]
      norm_num only [Nat.cast_ofNat]
    linarith only [hcap, hlog, hpLog, hnLog]
  have hdiv : p ∣ n := by
    rw [hpow]
    exact dvd_pow_self p (by decide : 2 ≠ 0)
  exact ⟨p, hp, hpB, PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn ho hp hdiv⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
