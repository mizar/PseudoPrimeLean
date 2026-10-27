/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Anchor250Separation
public import PseudoPrime.PrimeTestBounds.MillerRabin.TwoPolePrefixBounds

/-! # MR prime witnesses from the certified anchor at logarithmic level 250 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For an odd composite input greater than one under GRH with logarithm at least
250, a prime failing the actual strong MR test lies through (392931/400000)log(n)^2.
Pull back a nonprincipal quotient character from the strong-liar subgroup and apply
the certified anchored half-line separation. This connects the analytic bound to MR. -/
theorem exists_prime_strong_witness_le_anchor250 {n : ℕ} [NeZero n] (hn : 1 < n) (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 250 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (392931 / 400000 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  classical
  by_contra h
  have hpass :
    ∀ p : ℕ,
      p.Prime →
        (p : ℝ) ≤ (392931 / 400000 : ℝ) * (Real.log n) ^ 2 →
        PrimeTest.StrongMillerRabinPass n (p : ZMod n) :=
    fun p hp hb ↦ Classical.byContradiction (fun hf ↦ h ⟨p, hp, hb, hf⟩)
  obtain ⟨H, hH, hHpass⟩ :=
    PrimeTest.exists_proper_subgroup_containing_strongMillerRabinPass hn hnOdd hnComposite
  have : H.Normal := H.normal_of_isMulCommutative
  have : Nontrivial ((ZMod n)ˣ ⧸ H) := QuotientGroup.nontrivial_iff.mpr hH
  obtain ⟨z, hz⟩ := exists_ne (1 : (ZMod n)ˣ ⧸ H)
  obtain ⟨χ', hχz⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity ((ZMod n)ˣ ⧸ H) ℂ hz
  apply
    LLS.prime_trivial_false_le_anchor250 (LLS.pullbackCharacter χ')
      (LLS.pullbackCharacter_ne_one_of_ne_one χ' hχz) (le_refl n) hGRH hL
  intro p hp hb
  obtain ⟨u, hu, he⟩ := hHpass p (hpass p hp hb)
  rw [← he]
  exact LLS.pullbackCharacter_eq_one_of_mem χ' hu

/-- For every odd composite input under GRH with logarithm at least 250, a prime
rejecting base obeys the new quadratic coefficient and lies strictly below log(n)^2.
Infer the input side conditions from its logarithm and use the coefficient below one.
This is the public pointwise finite-scale MR witness bound. -/
theorem exists_prime_witness_le_anchor250_log_250 {n : ℕ} (hnOdd : Odd n) (hnComposite : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 250 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (392931 / 400000 : ℝ) * (Real.log n) ^ 2 ∧
        (p : ℝ) < (Real.log n) ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨hnOdd.pos.ne'⟩
  have hl := Real.log_le_sub_one_of_pos (Nat.cast_pos.mpr hnOdd.pos)
  have hn : 1 < n := by
    have hreal : (1 : ℝ) < n := by linarith only [hl, hL]
    exact_mod_cast hreal
  obtain ⟨p, hp, hb, hf⟩ := exists_prime_strong_witness_le_anchor250 hn hnOdd hnComposite hGRH hL
  have hs := sq_pos_of_pos (show 0 < Real.log n by linarith only [hL])
  exact ⟨p, hp, hb, by nlinarith only [hb, hs], hf⟩

/-- Under the same odd-composite GRH hypotheses, the least prime rejecting base
obeys (392931/400000)log(n)^2. Minimize over all prime rejecting bases and compare
with the constructed witness. Leastness is unrestricted by the cutoff. -/
theorem exists_least_prime_witness_le_anchor250_log_250 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 250 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ (392931 / 400000 : ℝ) * (Real.log n) ^ 2 ∧
        ∀ r : ℕ, r.Prime → ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) → p ≤ r := by
  classical
  obtain ⟨p, hp, hb, _, hf⟩ := exists_prime_witness_le_anchor250_log_250 hnOdd hnComposite hGRH hL
  have hex : ∃ r : ℕ, r.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := ⟨p, hp, hf⟩
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      (Nat.cast_le.mpr (Nat.find_min' hex ⟨hp, hf⟩)).trans hb, fun r hr hf ↦
      Nat.find_min' hex ⟨hr, hf⟩⟩

/-- Under the same hypotheses, a prime through the new bound fails the initial
one equality and every negative-one equality in the canonical binary decomposition
of n-1. Apply the exact strong MR rejection equivalence. This exposes the actual
power conditions rather than a surrogate character condition. -/
theorem exists_prime_rejecting_powers_le_anchor250_log_250 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 250 ≤ Real.log n) :
    let (s, d) := Nat.maxPowDvdDiv 2 (n - 1)
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (392931 / 400000 : ℝ) * (Real.log n) ^ 2 ∧
        (p : ZMod n) ^ d ≠ 1 ∧ ∀ j : ℕ, j < s → (p : ZMod n) ^ (2 ^ j * d) ≠ -1 := by
  obtain ⟨p, hp, hb, _, hf⟩ := exists_prime_witness_le_anchor250_log_250 hnOdd hnComposite hGRH hL
  exact ⟨p, hp, hb, PrimeTest.not_strongMillerRabinPass_iff.mp hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
