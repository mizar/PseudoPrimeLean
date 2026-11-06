/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.SquareCoverageData

/-! # Transfer square-coverage certificates to square divisors -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- An odd input divisible by a prime square has a bounded rejecting prime
when a certified prime supply and multichoose count cover the logarithm of that
square. The local kernel is formed using the original input. -/
theorem squareDivisor_candidate {n p B M k : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hp2 : p ≠ 2) (hdiv : p ^ 2 ∣ n) (hB : 1 < B) (hpi : M ≤ B.primeCounting) {u v : ℝ}
    (hsize : (k : ℝ) * Real.log B ≤ u) (hlo : u < Real.log (p ^ 2 : ℕ))
    (hhi : Real.log (p ^ 2 : ℕ) ≤ 2 * v) (hcount : v < Real.log (Nat.choose (M + k) k : ℝ)) :
    ∃ r : ℕ, r.Prime ∧ r ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hsize' : (k : ℝ) * Real.log B < Real.log (p ^ 2 : ℕ) := hsize.trans_lt hlo
  have hcount' : Real.log (p ^ 2 : ℕ) < 2 * Real.log (Nat.choose (M + k) k : ℝ) := by
    linarith only [hhi, hcount]
  obtain ⟨hs, hc⟩ := square_choose_of_log_bounds hp rfl hB hsize' hcount'
  exact
    exists_prime_primePow_multichoose_count hn ho hp hp2 (by norm_num only : 0 < 2) hdiv B M k hB
      hpi hs hc

/-- A checked candidate from a certified list gives the square-divisor witness
on its logarithmic interval, using the original input's local kernel. -/
theorem squareDivisor_candidate_list {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hp2 : p ≠ 2) (hdiv : p ^ 2 ∣ n) (hRH : RiemannHypothesis) (L : List CandidateLogData)
    (hL : L.all CandidateLogData.certifiedCheck = true) (d : CandidateLogData) (hd : d ∈ L)
    (hlo : (d.candidate.upper : ℝ) < Real.log (p ^ 2 : ℕ))
    (hhi : Real.log (p ^ 2 : ℕ) ≤ 2 * d.candidate.lower) :
    ∃ r : ℕ, r.Prime ∧ r ≤ d.candidate.bound ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have h := d.certified_sound hRH (List.all_eq_true.mp hL d hd)
  exact
    squareDivisor_candidate hn ho hp hp2 hdiv h.2.1 h.2.2 (d.sound h.1).1 hlo hhi (d.sound h.1).2

/-- A checked coverage chain extends a witness bound for a prime-square divisor
from the seed to the target. The chain uses the divisor's logarithmic scale,
while every produced witness rejects the original odd input. -/
theorem squareDivisor_chain {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hdiv : p ^ 2 ∣ n) (hRH : RiemannHypothesis) (L : List CandidateLogData)
    (hL : L.all CandidateLogData.certifiedCheck = true) (B : ℕ) (ids : List ℕ) (cap target : ℚ)
    (hcheck : squareChainCheck L B cap target ids = true)
    (hbase :
      Real.log (p ^ 2 : ℕ) ≤ (cap : ℝ) →
        ∃ r : ℕ, r.Prime ∧ r ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n))
    (hlog : Real.log (p ^ 2 : ℕ) ≤ (target : ℝ)) :
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
      by_cases hsmall : Real.log (p ^ 2 : ℕ) ≤ (cap : ℝ)
      · exact hbase hsmall
      · have hlo : (d.candidate.upper : ℝ) < Real.log (p ^ 2 : ℕ) :=
          ((Rat.cast_le (K := ℝ)).mpr hd.2).trans_lt (lt_of_not_ge hsmall)
        have hhi : Real.log (p ^ 2 : ℕ) ≤ 2 * (d.candidate.lower : ℝ) := by
          simp only [Rat.cast_max, Rat.cast_mul, Rat.cast_ofNat] at hx
          exact (le_max_iff.mp hx).resolve_left hsmall
        obtain ⟨r, hr, hrB, hfail⟩ :=
          squareDivisor_candidate_list hn ho hp hp2 hdiv hRH L hL d (List.mem_of_getElem? heq) hlo
            hhi
        exact ⟨r, hr, hrB.trans hd.1, hfail⟩

/-- Below the seed cap, the prime divisor itself is a bounded rejecting
witness. Its square divides the original input and determines the logarithm. -/
theorem squareDivisor_seed {n p B : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hdiv : p ^ 2 ∣ n)
    (cap : ℚ) (hcap : (cap : ℝ) < 2 * Real.log (B + 1)) (hlog : Real.log (p ^ 2 : ℕ) ≤ (cap : ℝ)) :
    ∃ r : ℕ, r.Prime ∧ r ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hpB : p ≤ B := by
    by_contra hpB
    have hpge : (B : ℝ) + 1 ≤ p := by exact_mod_cast (Nat.succ_le_of_lt (lt_of_not_ge hpB))
    have hpos : (0 : ℝ) < (B : ℝ) + 1 :=
      add_pos_of_nonneg_of_pos (Nat.cast_nonneg B) (by norm_num only)
    have hpLog := Real.log_le_log hpos hpge
    have hnLog : Real.log (p ^ 2 : ℕ) = 2 * Real.log p := by
      rw [Nat.cast_pow, Real.log_pow]
      norm_num only [Nat.cast_ofNat]
    linarith only [hcap, hlog, hpLog, hnLog]
  have hpn : p ∣ n := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hdiv
  exact ⟨p, hp, hpB, PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn ho hp hpn⟩

/-- Under RH, a checked square-coverage row applies to any odd input divisible
by the prime square. The divisor logarithm is bounded by the input logarithm,
and the local kernel yields a rejecting prime for the original input. -/
theorem squareCoverage_sound_divisor {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hp2 : p ≠ 2) (hdiv : p ^ 2 ∣ n) (hRH : RiemannHypothesis) (d : SquareCoverageData)
    (hcheck : d.check = true) (hlog : Real.log n ≤ (d.target : ℝ)) :
    ∃ r : ℕ, r.Prime ∧ r ≤ d.bound ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hc :
    Analysis.fineLogCheck (d.bound + 1 : ℕ) d.logScale 64 (d.seed / 2 + 1 / 1000000000000000000)
          (d.seed / 2 + 1) =
        true ∧
      squareChainCheck allCountCandidates d.bound d.seed d.target d.chain = true :=
    of_decide_eq_true hcheck
  have hs := (Analysis.fineLogCheck_sound hc.1).1
  simp only [Rat.cast_add, Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_natCast,
    Nat.cast_add, Nat.cast_one] at hs
  have hseed : (d.seed : ℝ) < 2 * Real.log (d.bound + 1) := by linarith only [hs]
  have hpowle : p ^ 2 ≤ n := Nat.le_of_dvd (Nat.zero_lt_of_lt hn) hdiv
  have hlogpow : Real.log (p ^ 2 : ℕ) ≤ Real.log n :=
    Real.log_le_log (Nat.cast_pos.mpr (pow_pos hp.pos 2)) (Nat.cast_le.mpr hpowle)
  apply
    squareDivisor_chain hn ho hp hp2 hdiv hRH allCountCandidates allCountCandidates_checked d.bound
      d.chain d.seed d.target hc.2
  · exact squareDivisor_seed hn ho hp hdiv d.seed hseed
  · exact hlogpow.trans hlog

end PseudoPrime.PrimeTestBounds.MillerRabin
