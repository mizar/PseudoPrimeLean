/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TwoPoleConstantBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.TwoPoleSignedBounds

/-! # MR prime witnesses from the direct signed two-pole error bound -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For odd composite n greater than one under GRH, positive character-free two-pole
separation yields a prime failing the strong Miller-Rabin test through the cutoff.
Universal prime passage forces a nonprincipal quotient character to be trivial on
every small prime, contradicting the scalar criterion. No uniform character budget
is left as a hypothesis. -/
theorem exists_prime_strong_witness_of_twoPoleConstantGap {n : ℕ} [NeZero n] (hn : 1 < n)
    (hnOdd : Odd n) (hnComposite : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 2 ≤ x)
    (hgap : 0 < LLS.twoPoleConstantGap n (523 / 100) x) :
    ∃ p : ℕ,
      p.Prime ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  classical
  by_contra h
  have hpass :
    ∀ p : ℕ,
      p.Prime → (p : ℝ) ≤ (99 / 40 : ℝ) * x → PrimeTest.StrongMillerRabinPass n (p : ZMod n) :=
    fun p hp hb ↦ Classical.byContradiction (fun hf ↦ h ⟨p, hp, hb, hf⟩)
  obtain ⟨H, hH, hHpass⟩ :=
    PrimeTest.exists_proper_subgroup_containing_strongMillerRabinPass hn hnOdd hnComposite
  have : H.Normal := H.normal_of_isMulCommutative
  have : Nontrivial ((ZMod n)ˣ ⧸ H) := QuotientGroup.nontrivial_iff.mpr hH
  obtain ⟨z, hz⟩ := exists_ne (1 : (ZMod n)ˣ ⧸ H)
  obtain ⟨χ', hχz⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity ((ZMod n)ˣ ⧸ H) ℂ hz
  apply
    LLS.prime_trivial_false_of_twoPoleConstantGap (LLS.pullbackCharacter χ')
      (LLS.pullbackCharacter_ne_one_of_ne_one χ' hχz) (le_refl n) hGRH hx
      (AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant_le_signed _) hgap
  intro p hp hb
  obtain ⟨u, hu, he⟩ := hHpass p (hpass p hp hb)
  rw [← he]
  exact LLS.pullbackCharacter_eq_one_of_mem χ' hu

/-- For odd composite n greater than one under GRH with log n at least 800,
a prime rejecting base lies through (99/40)((500/821)log n+72/5) squared. Insert the
continuous affine separation into the character-free MR criterion.
No additional numerical or factorization hypothesis remains. -/
theorem exists_prime_strong_witness_le_signedGammaTwoPole {n : ℕ} [NeZero n] (hn : 1 < n)
    (hnOdd : Odd n) (hnComposite : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 800 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (99 / 40 : ℝ) * ((500 / 821 : ℝ) * Real.log n + 72 / 5) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hd := LLS.twoPoleConstant_root_data hL (c := 72 / 5) (by norm_num only) (by norm_num only)
  have hx4 : 4 ≤ ((500 / 821 : ℝ) * Real.log n + 72 / 5) ^ 2 := hd.1
  have hg :=
    LLS.twoPoleConstantGap_affine_margin hL (c := 72 / 5) (C := 523 / 100) (by norm_num only)
      (by norm_num only)
  exact
    exists_prime_strong_witness_of_twoPoleConstantGap hn hnOdd hnComposite hGRH
      (by linarith only [hx4] : 2 ≤ ((500 / 821 : ℝ) * Real.log n + 72 / 5) ^ 2)
      (by linarith only [hg])

/-- For every odd composite n under GRH with log n at least 800, a prime MR witness
obeys the affine two-pole bound, which is strictly below (log n) squared.
Derive n greater than one from its logarithm and bound the affine root by 6271log n/10000.
This is the public pointwise bound used in the best-interval comparison. -/
theorem exists_prime_witness_le_signedGammaTwoPole_log_800 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 800 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (99 / 40 : ℝ) * ((500 / 821 : ℝ) * Real.log n + 72 / 5) ^ 2 ∧
        (p : ℝ) < (Real.log n) ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨hnOdd.pos.ne'⟩
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hnOdd.pos
  have ht := Real.log_le_sub_one_of_pos hn0
  have hn : 1 < n := by exact_mod_cast (show (1 : ℝ) < n by linarith only [ht, hL])
  obtain ⟨p, hp, hb, hf⟩ :=
    exists_prime_strong_witness_le_signedGammaTwoPole hn hnOdd hnComposite hGRH hL
  have hr : 0 ≤ (500 / 821 : ℝ) * Real.log n + 72 / 5 := by linarith only [hL]
  have hu : (500 / 821 : ℝ) * Real.log n + 72 / 5 ≤ (6271 / 10000 : ℝ) * Real.log n := by
    linarith only [hL]
  have hs := mul_self_le_mul_self hr hu
  have hsq : 0 < (Real.log n) ^ 2 := sq_pos_of_pos (by linarith only [hL])
  exact ⟨p, hp, hb, by nlinarith only [hb, hs, hsq], hf⟩

/-- Under the same hypotheses, the least prime rejecting base obeys the affine
two-pole bound. Minimize the unbounded rejection predicate and compare with the
explicit witness. Leastness ranges over all prime rejecting bases. -/
theorem exists_least_prime_witness_le_signedGammaTwoPole_log_800 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 800 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ (99 / 40 : ℝ) * ((500 / 821 : ℝ) * Real.log n + 72 / 5) ^ 2 ∧
        ∀ r : ℕ, r.Prime → ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) → p ≤ r := by
  classical
  obtain ⟨p, hp, hb, _, hf⟩ :=
    exists_prime_witness_le_signedGammaTwoPole_log_800 hnOdd hnComposite hGRH hL
  have hex : ∃ r : ℕ, r.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := ⟨p, hp, hf⟩
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      (Nat.cast_le.mpr (Nat.find_min' hex ⟨hp, hf⟩)).trans hb, fun r hr hf ↦
      Nat.find_min' hex ⟨hr, hf⟩⟩

/-- Under the same hypotheses, a prime through the affine two-pole cutoff fails
the initial power equality and every negative-one equality in the canonical binary
decomposition of n-1. Apply the exact strong-test rejection equivalence.
This exposes the actual power conditions of the rejecting witness. -/
theorem exists_prime_rejecting_powers_le_signedGammaTwoPole_log_800 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 800 ≤ Real.log n) :
    let (s, d) := Nat.maxPowDvdDiv 2 (n - 1);
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (99 / 40 : ℝ) * ((500 / 821 : ℝ) * Real.log n + 72 / 5) ^ 2 ∧
        (p : ZMod n) ^ d ≠ 1 ∧ ∀ j : ℕ, j < s → (p : ZMod n) ^ (2 ^ j * d) ≠ -1 := by
  obtain ⟨p, hp, hb, _, hf⟩ :=
    exists_prime_witness_le_signedGammaTwoPole_log_800 hnOdd hnComposite hGRH hL
  exact ⟨p, hp, hb, PrimeTest.not_strongMillerRabinPass_iff.mp hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
