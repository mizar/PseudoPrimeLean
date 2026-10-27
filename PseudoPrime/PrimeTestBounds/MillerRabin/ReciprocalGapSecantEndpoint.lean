/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalGapSecantEndpoint
public import PseudoPrime.PrimeTestBounds.MillerRabin.ReciprocalGapFullEndpoint
public import PseudoPrime.PrimeTestBounds.MillerRabin.ReciprocalGapAmbient

/-! # MR rejecting primes from secant endpoint separation -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For odd composite N>1 under GRH, h>0 and 64<=Y<=x, secant endpoint
separation at every nontrivial divisor yields a prime rejecting the canonical strong test
through x. Choose a character trivial on passing residues and use its primitive character.
Prime factors remain valid rejecting bases; no arithmetic exclusions are charged. -/
theorem exists_prime_reject_of_full_secant_divisor_separation {N : ℕ} [NeZero N] (hn : 1 < N)
    (ho : Odd N) (hc : ¬N.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {h x Y : ℝ} (hh : 0 < h) (hx : 1 < x) (hY : 64 ≤ Y) (hYx : Y ≤ x)
    (hgap :
      ∀ d : ℕ, 2 ≤ d → d ∣ N → LLS.PaperStatements.reciprocalGapFullSecantSeparation h d x Y < 0) :
    let (s, a) := Nat.maxPowDvdDiv 2 (N - 1)
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ x ∧ (p : ZMod N) ^ a ≠ 1 ∧ ∀ j : ℕ, j < s → (p : ZMod N) ^ (2 ^ j * a) ≠ -1 := by
  obtain ⟨χ, hχ, hpass⟩ := exists_character_trivial_on_pass hn ho hc
  let _ : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hψ : χ.primitiveCharacter ≠ 1 := by
    intro hv
    have he := DirichletCharacter.changeLevel_primitiveCharacter χ
    rw [hv, DirichletCharacter.changeLevel_one] at he
    exact hχ he.symm
  have hq : 2 ≤ χ.conductor :=
    (Nat.two_le_iff _).mpr
      ⟨χ.conductor_ne_zero, fun he ↦ hχ (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr he)⟩
  obtain ⟨p, hp, hpx, hv⟩ :=
    LLS.PaperStatements.exists_prime_not_one_of_reciprocalGap_full_secant hh hq hGRH
      χ.primitiveCharacter_isPrimitive hψ (fun hi ↦ hψ (inv_eq_one.mp hi)) hx hY hYx
      (hgap χ.conductor hq χ.conductor_dvd_level)
  refine ⟨p, hp, hpx, PrimeTest.not_strongMillerRabinPass_iff.mp ?_⟩
  intro ha
  have hcop := (ZMod.isUnit_iff_coprime p N).mp (PrimeTest.strongMillerRabinPass_isUnit hn ho ha)
  have he := DirichletCharacter.primitiveCharacter_apply_of_isCoprime χ hcop.isCoprime
  simp only [Int.cast_natCast] at he
  exact hv (he.trans (hpass p ha))

/-- For odd composite N>1 under GRH, h>0 and 64<=Y<=x, one strict secant
endpoint inequality at N gives a prime rejecting the canonical strong test through x.
Use level monotonicity to discharge the divisor conditions. This is the factorization-free
MR consumer of the improved variable-gap analytic principal lower bound. -/
theorem exists_prime_reject_of_full_secant_separation {N : ℕ} [NeZero N] (hn : 1 < N) (ho : Odd N)
    (hc : ¬N.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {h x Y : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hY : 64 ≤ Y) (hYx : Y ≤ x)
    (hgap : LLS.PaperStatements.reciprocalGapFullSecantSeparation h N x Y < 0) :
    let (s, a) := Nat.maxPowDvdDiv 2 (N - 1)
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ x ∧ (p : ZMod N) ^ a ≠ 1 ∧ ∀ j : ℕ, j < s → (p : ZMod N) ^ (2 ^ j * a) ≠ -1 := by
  apply exists_prime_reject_of_full_secant_divisor_separation hn ho hc hGRH hh hx hY hYx
  intro d hd hdN
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num only : (0 : ℕ) < 2) hd
  have hdle := Nat.le_of_dvd (NeZero.pos N) hdN
  exact
    (LLS.PaperStatements.reciprocalGapFullSecantSeparation_mono_level hh hx.le hY hd0 hdle).trans_lt
      hgap

end PseudoPrime.PrimeTestBounds.MillerRabin
