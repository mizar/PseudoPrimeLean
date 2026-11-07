/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticTripleRoundGap

/-! # Local pointwise witnesses and prime rounding -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, a proper local subgroup containing the images of every strong
pass gives a rejecting prime at the rounded radius when its logarithmic level
is bounded by `lowRoundLevel`. A quotient character is even because `-1`
belongs to the subgroup. -/
theorem exists_prime_reject_local_round {n q : ℕ} [NeZero q] (hn : 1 < n) (ho : Odd n) (hqn : q ∣ n)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hpass :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
          ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (a : ZMod q))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hq : Real.log q ≤ lowRoundLevel) :
    ∃ p : ℕ,
      p.Prime ∧ (p : ℝ) ≤ lowRoundRadius ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have : H.Normal := H.normal_of_isMulCommutative
  have : Nontrivial ((ZMod q)ˣ ⧸ H) := QuotientGroup.nontrivial_iff.mpr hH
  obtain ⟨x, hx⟩ := exists_ne (1 : (ZMod q)ˣ ⧸ H)
  obtain ⟨χ, hχ⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity ((ZMod q)ˣ ⧸ H) ℂ hx
  have he : (LLS.pullbackCharacter χ).Even := by
    change (LLS.pullbackCharacter χ) (-1) = 1
    simpa only [Units.val_neg, Units.val_one] using
      LLS.pullbackCharacter_eq_one_of_mem χ (neg_one_mem_of_local_pass hn ho hqn H hpass)
  obtain ⟨p, hp, hb, hv⟩ :=
    LLS.PaperStatements.exists_prime_ne_one_pointwise (LLS.pullbackCharacter χ)
      (LLS.pullbackCharacter_ne_one_of_ne_one χ hχ) he hGRH (by norm_num only [lowRoundRadius])
      (lowRound_pointwise_gap hq)
  refine ⟨p, hp, hb, ?_⟩
  intro hpassing
  obtain ⟨u, hu, heq⟩ := hpass p hpassing
  exact hv (heq ▸ LLS.pullbackCharacter_eq_one_of_mem χ hu)

/-- A two-prime divisor with bounded logarithm yields a rounded-radius rejecting
prime under GRH. If three divides the input it is a direct witness; otherwise
the pair supplies a proper local subgroup at a divisor of no greater size. -/
theorem exists_prime_reject_pair_round {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p * q ∣ n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hs : Real.log ((p * q : ℕ) : ℝ) ≤ lowRoundLevel) :
    ∃ a : ℕ,
      a.Prime ∧ (a : ℝ) ≤ lowRoundRadius ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (a : ZMod n) := by
  rcases prime_pair_local_data hn ho hp hq hpq with hthree | ⟨m, hm, hmn, hmpq, H, hH, hpass⟩
  · have hb : (3 : ℝ) ≤ lowRoundRadius ^ 2 := by norm_num only [lowRoundRadius]
    exact
      ⟨3, Nat.prime_three, hb,
        PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn ho Nat.prime_three hthree⟩
  · let : NeZero m := ⟨Nat.ne_of_gt hm⟩
    have hmlevel : Real.log m ≤ lowRoundLevel :=
      (Real.log_le_log (Nat.cast_pos.mpr hm) (Nat.cast_le.mpr hmpq)).trans hs
    exact exists_prime_reject_local_round hn ho hmn H hH hpass hGRH hmlevel

/-- A prime below 479 is at most 467: each intervening integer is composite.
The finite primality check enables rounding a strict radius bound down to 467. -/
theorem prime_le_467_of_lt_479 {a : ℕ} (ha : a.Prime) (h : a < 479) : a ≤ 467 := by
  by_contra hn
  have hlo : 468 ≤ a := Nat.succ_le_of_lt (Nat.lt_of_not_ge hn)
  have hhi : a ≤ 478 := Nat.le_pred_of_lt h
  interval_cases a <;> norm_num only [Nat.prime_def_lt] at ha

end PseudoPrime.PrimeTestBounds.MillerRabin
