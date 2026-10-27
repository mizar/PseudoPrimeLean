/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TwoPolePrincipalPrefixBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.TwoPoleSignedGammaBounds

/-! # MR prime witnesses retaining nonnegative Euler prefixes -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, a positive signed-principal gap with a retained Euler prefix yields a prime
rejecting base for an odd composite input. Pull back a nonprincipal quotient character and use
the joint-error character comparison with the actual principal bound. This connects
the improved principal estimate to the actual strong Miller-Rabin rejection predicate. -/
theorem exists_prime_strong_witness_of_twoPolePrincipalPrefixGap {n : ℕ} [NeZero n] (hn : 1 < n)
    (hnOdd : Odd n) (hnComposite : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x g : ℝ} (hx : 2 ≤ x)
    (S : Finset ℕ) (hS : ∀ n ∈ S, (n : ℝ) ≤ (99 / 40 : ℝ) * x)
    (hg : g ≤ 2 * LLS.twoPoleEulerPrefixMass S)
    (hgap : 0 < LLS.jointRampPrincipalGap n (523 / 100 - g) x) :
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
    LLS.prime_trivial_false_of_jointRampPrincipal_prefix (LLS.pullbackCharacter χ')
      (LLS.pullbackCharacter_ne_one_of_ne_one χ' hχz) (le_refl n) hGRH hx
      (AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant_le_signed _) S hS hg hgap
  intro p hp hb
  obtain ⟨u, hu, he⟩ := hHpass p (hpass p hp hb)
  rw [← he]
  exact LLS.pullbackCharacter_eq_one_of_mem χ' hu

/-- For odd composite n greater than one under GRH, positive character-free two-pole
separation yields a prime failing the strong Miller-Rabin test through the cutoff.
Universal prime passage forces a nonprincipal quotient character to be trivial on
every small prime. Retain a principal finite-prefix saving before applying the scalar gap.
No separate character-dependent exclusion budget is needed. -/
theorem exists_prime_strong_witness_of_twoPolePrefixGap {n : ℕ} [NeZero n] (hn : 1 < n)
    (hnOdd : Odd n) (hnComposite : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x g : ℝ} (hx : 2 ≤ x)
    (S : Finset ℕ) (hS : ∀ n ∈ S, (n : ℝ) ≤ (99 / 40 : ℝ) * x)
    (hg : g ≤ 2 * LLS.twoPoleEulerPrefixMass S)
    (hgap : 0 < LLS.twoPoleConstantGap n (523 / 100 - g) x) :
    ∃ p : ℕ,
      p.Prime ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    exists_prime_strong_witness_of_twoPolePrincipalPrefixGap hn hnOdd hnComposite hGRH hx S hS hg
  have hnew :=
    LLS.twoPoleSignedVariationGap_gt_constant (A := n) (C := 523 / 100 - g)
      (show 1 ≤ x by linarith only [hx])
  have hj :=
    LLS.jointRampPrincipalGap_gt_signed (A := n) (C := 523 / 100 - g)
      (show 1 ≤ x by linarith only [hx])
  linarith only [hgap, hnew, hj]

/-- For odd composite n greater than one under GRH with log n at least 500,
a prime rejecting base lies through (99/40)((500/821)log n+213/20) squared. Insert the
continuous affine separation into the character-free MR criterion.
No additional numerical or factorization hypothesis remains. -/
theorem exists_prime_strong_witness_le_eulerPrefixTwoPole {n : ℕ} [NeZero n] (hn : 1 < n)
    (hnOdd : Odd n) (hnComposite : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 500 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (99 / 40 : ℝ) * ((500 / 821 : ℝ) * Real.log n + 213 / 20) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hd := LLS.twoPolePrincipalPrefix_root_data hL
  have hx4 : 4 ≤ ((500 / 821 : ℝ) * Real.log n + 213 / 20) ^ 2 := hd.2.1
  have hm := LLS.twoPolePrincipalPrefix_gap_positive hL (C := 523 / 100 - 8 / 5) (by norm_num only)
  apply
    exists_prime_strong_witness_of_twoPolePrincipalPrefixGap hn hnOdd hnComposite hGRH
      (by linarith only [hx4] : 2 ≤ ((500 / 821 : ℝ) * Real.log n + 213 / 20) ^ 2)
      ({2,3,5,7} : Finset ℕ)
  · intro k hk
    have hs : ∀ k ∈ ({2,3,5,7} : Finset ℕ), k ≤ 7 := by decide
    exact (Nat.cast_le.mpr (hs k hk)).trans (by linarith only [hx4])
  · exact AnalyticNumberTheory.Arithmetic.pairedEuler_prefix_2357_saving
  · linarith only [hm]

/-- For every odd composite n under GRH with log n at least 500, a prime MR witness
obeys the affine two-pole bound, which is strictly below (log n) squared.
Derive n greater than one from its logarithm and bound the affine root by 1271log n/2000.
This is the public pointwise bound used in the best-interval comparison. -/
theorem exists_prime_witness_le_eulerPrefixTwoPole_log_500 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 500 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (99 / 40 : ℝ) * ((500 / 821 : ℝ) * Real.log n + 213 / 20) ^ 2 ∧
        (p : ℝ) < (Real.log n) ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨hnOdd.pos.ne'⟩
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hnOdd.pos
  have ht := Real.log_le_sub_one_of_pos hn0
  have hn : 1 < n := by exact_mod_cast (show (1 : ℝ) < n by linarith only [ht, hL])
  obtain ⟨p, hp, hb, hf⟩ :=
    exists_prime_strong_witness_le_eulerPrefixTwoPole hn hnOdd hnComposite hGRH hL
  have hr : 0 ≤ (500 / 821 : ℝ) * Real.log n + 213 / 20 := by linarith only [hL]
  have hu : (500 / 821 : ℝ) * Real.log n + 213 / 20 ≤ (1271 / 2000 : ℝ) * Real.log n := by
    linarith only [hL]
  have hs := mul_self_le_mul_self hr hu
  have hsq : 0 < (Real.log n) ^ 2 := sq_pos_of_pos (by linarith only [hL])
  exact ⟨p, hp, hb, by nlinarith only [hb, hs, hsq], hf⟩

/-- Under the same hypotheses, the least prime rejecting base obeys the affine
two-pole bound. Minimize the unbounded rejection predicate and compare with the
explicit witness. Leastness ranges over all prime rejecting bases. -/
theorem exists_least_prime_witness_le_eulerPrefixTwoPole_log_500 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 500 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ (99 / 40 : ℝ) * ((500 / 821 : ℝ) * Real.log n + 213 / 20) ^ 2 ∧
        ∀ r : ℕ, r.Prime → ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) → p ≤ r := by
  classical
  obtain ⟨p, hp, hb, _, hf⟩ :=
    exists_prime_witness_le_eulerPrefixTwoPole_log_500 hnOdd hnComposite hGRH hL
  have hex : ∃ r : ℕ, r.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := ⟨p, hp, hf⟩
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      (Nat.cast_le.mpr (Nat.find_min' hex ⟨hp, hf⟩)).trans hb, fun r hr hf ↦
      Nat.find_min' hex ⟨hr, hf⟩⟩

/-- Under the same hypotheses, a prime through the affine two-pole cutoff fails
the initial power equality and every negative-one equality in the canonical binary
decomposition of n-1. Apply the exact strong-test rejection equivalence.
This exposes the actual power conditions of the rejecting witness. -/
theorem exists_prime_rejecting_powers_le_eulerPrefixTwoPole_log_500 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 500 ≤ Real.log n) :
    let (s, d) := Nat.maxPowDvdDiv 2 (n - 1);
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (99 / 40 : ℝ) * ((500 / 821 : ℝ) * Real.log n + 213 / 20) ^ 2 ∧
        (p : ZMod n) ^ d ≠ 1 ∧ ∀ j : ℕ, j < s → (p : ZMod n) ^ (2 ^ j * d) ≠ -1 := by
  obtain ⟨p, hp, hb, _, hf⟩ :=
    exists_prime_witness_le_eulerPrefixTwoPole_log_500 hnOdd hnComposite hGRH hL
  exact ⟨p, hp, hb, PrimeTest.not_strongMillerRabinPass_iff.mp hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
