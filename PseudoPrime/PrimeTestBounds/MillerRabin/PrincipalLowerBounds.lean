/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PrincipalLowerWitnessBounds
public import PseudoPrime.LLS.ClippedLogShiftPrincipalBounds
public import PseudoPrime.LLS.TwoPoleSmallPrefixSavings
public import PseudoPrime.PrimeTestBounds.MillerRabin.TwoPoleSignedGammaBounds

/-! # MR rejecting prime bases from certified principal lower caps -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For an odd composite input greater than one under GRH, a certified principal
lower cap and positive gap with a retained Euler prefix give an actual rejecting prime.
Pull back a nonprincipal quotient character from the strong-liar subgroup and use the
generic principal consumer. This separates the kernel analysis from MR extraction. -/
theorem exists_prime_strong_witness_of_principalLowerGap {n : ℕ} [NeZero n] (hn : 1 < n)
    (hnOdd : Odd n) (hnComposite : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x g P : ℝ} (hx : 2 ≤ x)
    (hP :
      P ≤
        2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
          (∑' k : ℕ,
              LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re)
    (S : Finset ℕ) (hS : ∀ n ∈ S, (n : ℝ) ≤ (99 / 40 : ℝ) * x)
    (hg : g ≤ 2 * LLS.twoPoleEulerPrefixMass S)
    (hgap : 0 < LLS.principalLowerGap n (523 / 100 - g) x P) :
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
    LLS.prime_trivial_false_of_principalLower_prefix (LLS.pullbackCharacter χ')
      (LLS.pullbackCharacter_ne_one_of_ne_one χ' hχz) (le_refl n) hGRH hx hP
      (AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant_le_signed _) S hS hg hgap
  intro p hp hb
  obtain ⟨u, hu, he⟩ := hHpass p (hpass p hp hb)
  rw [← he]
  exact LLS.pullbackCharacter_eq_one_of_mem χ' hu

/-- For an odd composite input greater than one under GRH, a positive gap from the
fully clipped-corrected principal cap gives an actual rejecting prime through (99/40)x.
Assume x at least three and an admissible width. Insert the certified four-prime saving
and the proved principal lower cap; no abstract principal-bound premise remains. -/
theorem exists_prime_strong_witness_of_clippedShift_gap {n : ℕ} [NeZero n] (hn : 1 < n)
    (hnOdd : Odd n) (hnComposite : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x h : ℝ} (hx : 3 ≤ x)
    (hh : 0 < h) (hhx : h ≤ x)
    (hgap : 0 < LLS.principalLowerGap n (363 / 100) x (LLS.clippedShiftPrincipalLower x h)) :
    ∃ p : ℕ,
      p.Prime ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    exists_prime_strong_witness_of_principalLowerGap hn hnOdd hnComposite hGRH
      (by linarith only [hx])
      (LLS.clippedShiftPrincipalLower_le_actual hGRH.riemann (by linarith only [hx]) hh hhx)
      ({2,3,5,7} : Finset ℕ)
  · intro k hk
    have hs : k ≤ 7 := (by decide +kernel : ∀ j ∈ ({2,3,5,7} : Finset ℕ), j ≤ 7) k hk
    exact (Nat.cast_le.mpr hs).trans (by linarith only [hx])
  · exact AnalyticNumberTheory.Arithmetic.pairedEuler_prefix_2357_saving
  · norm_num only
    exact hgap

end PseudoPrime.PrimeTestBounds.MillerRabin
