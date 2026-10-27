/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.EndpointFixed67
public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointFourStep
public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointFixed61
/-! # Fixed endpoint prime witnesses at most 61 and 67 -/
@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A prime below 71 is at most 67. Kernel-check that 68,69 and 70 are composite.
This rounds prime witnesses without enumerating inputs n. -/
theorem prime_lt71_le67 {p : ℕ} (hp : p.Prime) (h : p < 71) : p ≤ 67 := by
  have hcheck : ∀ k ∈ Finset.Icc 68 70, ¬Nat.Prime k := by decide +kernel
  by_contra hn
  exact hcheck p (Finset.mem_Icc.mpr ⟨Nat.lt_of_not_ge hn, Nat.le_of_lt_succ h⟩) hp

/-- Under GRH, every odd composite n>1 with log n<=1147/100 has a rejecting prime<=61.
Use the positive gap at radius 1637/200, whose square is below 67, then round primes. -/
theorem exists_prime_endpoint61Sharp {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ≤ 1147 / 100) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ 61 ∧
      ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hb, hr⟩ := exists_prime_evenEndpoint hn ho hc hGRH
    (by norm_num only : (8 : ℝ) ≤ 1637 / 200) (LLS.PaperStatements.endpoint61Sharp_gap_pos hL)
  have hceil : (p : ℝ) < 67 := hb.trans_lt (by norm_num only)
  have hbound := prime_lt67_le61 hp (by exact_mod_cast hceil)
  exact ⟨p, hp, by exact_mod_cast hbound, hr⟩

/-- Under the sharpened fixed-61 assumptions, the least rejecting prime is at most 61.
Apply least-prime extraction to the actual witness theorem. -/
theorem exists_least_endpoint61Sharp {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ≤ 1147 / 100) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ 61 ∧
      ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
      ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  exact exists_least_prime_reject_of_exists_prime_reject
    (exists_prime_endpoint61Sharp hn ho hc hGRH hL)

/-- Under GRH, every odd composite n>1 with log n<=47/4 has a rejecting prime<=67.
Use the positive gap at radius 337/40, whose square is below 71, then round primes. -/
theorem exists_prime_endpoint67 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ≤ 47 / 4) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ 67 ∧
      ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hb, hr⟩ := exists_prime_evenEndpoint hn ho hc hGRH
    (by norm_num only : (8 : ℝ) ≤ 337 / 40) (LLS.PaperStatements.endpoint67_gap_pos hL)
  have hceil : (p : ℝ) < 71 := hb.trans_lt (by norm_num only)
  have hbound := prime_lt71_le67 hp (by exact_mod_cast hceil)
  exact ⟨p, hp, by exact_mod_cast hbound, hr⟩

/-- Under the fixed-67 assumptions, the least rejecting prime is at most 67.
Apply least-prime extraction to the actual witness theorem. -/
theorem exists_least_endpoint67 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ≤ 47 / 4) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ 67 ∧
      ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
      ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  exact exists_least_prime_reject_of_exists_prime_reject
    (exists_prime_endpoint67 hn ho hc hGRH hL)

end PseudoPrime.PrimeTestBounds.MillerRabin
