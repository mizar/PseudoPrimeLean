/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ClippedAffineWitnessBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.TwoPolePrefixBounds

/-! # MR prime witnesses from the clipped-corrected affine radius -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For an odd composite input greater than one under GRH with logarithm at least
300, a prime failing the actual strong MR test lies through (99/40)((500/821)log n+3)^2.
Pull back a nonprincipal quotient character and apply the certified affine separation.
This connects the fully corrected principal comparison to actual MR rejection. -/
theorem exists_prime_strong_witness_le_clippedAffine {n : ℕ} [NeZero n] (hn : 1 < n) (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 300 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (99 / 40 : ℝ) * LLS.clippedAffineRoot (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  classical
  by_contra h
  have hpass :
    ∀ p : ℕ,
      p.Prime →
        (p : ℝ) ≤ (99 / 40 : ℝ) * LLS.clippedAffineRoot (Real.log n) ^ 2 →
        PrimeTest.StrongMillerRabinPass n (p : ZMod n) :=
    fun p hp hb ↦ Classical.byContradiction (fun hf ↦ h ⟨p, hp, hb, hf⟩)
  obtain ⟨H, hH, hHpass⟩ :=
    PrimeTest.exists_proper_subgroup_containing_strongMillerRabinPass hn hnOdd hnComposite
  have : H.Normal := H.normal_of_isMulCommutative
  have : Nontrivial ((ZMod n)ˣ ⧸ H) := QuotientGroup.nontrivial_iff.mpr hH
  obtain ⟨z, hz⟩ := exists_ne (1 : (ZMod n)ˣ ⧸ H)
  obtain ⟨χ', hχz⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity ((ZMod n)ˣ ⧸ H) ℂ hz
  apply
    LLS.prime_trivial_false_le_clippedAffine (LLS.pullbackCharacter χ')
      (LLS.pullbackCharacter_ne_one_of_ne_one χ' hχz) (le_refl n) hGRH hL
  intro p hp hb
  obtain ⟨u, hu, he⟩ := hHpass p (hpass p hp hb)
  rw [← he]
  exact LLS.pullbackCharacter_eq_one_of_mem χ' hu

/-- For every odd composite input under GRH with logarithm at least 300, a prime
rejecting base obeys the clipped affine bound and lies strictly below log(n)^2.
Infer the input side conditions and use the certified root data. This is the public
pointwise MR witness bound from the new principal comparison. -/
theorem exists_prime_witness_le_clippedAffine_log_300 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 300 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (99 / 40 : ℝ) * LLS.clippedAffineRoot (Real.log n) ^ 2 ∧
        (p : ℝ) < (Real.log n) ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨hnOdd.pos.ne'⟩
  have hl := Real.log_le_sub_one_of_pos (Nat.cast_pos.mpr hnOdd.pos)
  have hn : 1 < n := by
    have hreal : (1 : ℝ) < n := by linarith only [hl, hL]
    exact_mod_cast hreal
  obtain ⟨p, hp, hb, hf⟩ :=
    exists_prime_strong_witness_le_clippedAffine hn hnOdd hnComposite hGRH hL
  exact ⟨p, hp, hb, hb.trans_lt (LLS.clippedAffine_root_data hL).2.2, hf⟩

/-- Under the odd-composite GRH hypotheses with logarithm at least 300, the least
prime rejecting base is at most (99/40)((500/821)log n+3)^2. Minimize over all prime
rejecting bases and compare with the constructed witness. Leastness is unrestricted. -/
theorem exists_least_prime_witness_le_clippedAffine_log_300 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 300 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ (99 / 40 : ℝ) * LLS.clippedAffineRoot (Real.log n) ^ 2 ∧
        ∀ r : ℕ, r.Prime → ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) → p ≤ r := by
  classical
  obtain ⟨p, hp, hb, _, hf⟩ :=
    exists_prime_witness_le_clippedAffine_log_300 hnOdd hnComposite hGRH hL
  have hex : ∃ r : ℕ, r.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := ⟨p, hp, hf⟩
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      (Nat.cast_le.mpr (Nat.find_min' hex ⟨hp, hf⟩)).trans hb, fun r hr hf ↦
      Nat.find_min' hex ⟨hr, hf⟩⟩

/-- Under the odd-composite GRH hypotheses with logarithm at least 300, a prime
within the clipped affine cutoff fails every required strong-MR power equality.
Unfold rejection using the canonical two-adic decomposition of n-1. This exposes the
actual modular-power certificate behind the prime witness bound. -/
theorem exists_prime_rejecting_powers_le_clippedAffine_log_300 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 300 ≤ Real.log n) :
    let (s, d) := Nat.maxPowDvdDiv 2 (n - 1)
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (99 / 40 : ℝ) * LLS.clippedAffineRoot (Real.log n) ^ 2 ∧
        (p : ZMod n) ^ d ≠ 1 ∧ ∀ j : ℕ, j < s → (p : ZMod n) ^ (2 ^ j * d) ≠ -1 := by
  obtain ⟨p, hp, hb, _, hf⟩ :=
    exists_prime_witness_le_clippedAffine_log_300 hnOdd hnComposite hGRH hL
  exact ⟨p, hp, hb, PrimeTest.not_strongMillerRabinPass_iff.mp hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
