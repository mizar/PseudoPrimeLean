/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.ConcaveFittingLogBounds
public import PseudoPrime.PrimeTest.MillerRabin.Computation.Small

/-! # Unconditional finite witnesses through the concave MR fitting envelope -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Every odd composite natural number above one is at least nine.
Check the finitely many smaller odd inputs by the kernel and exclude their primality.
This establishes the lower domain guard for actual finite MR witnesses. -/
theorem mrRegion_odd_composite_ge_nine {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime) :
    9 ≤ n := by
  by_contra h9
  have hp : ∀ k : Fin 9, 1 < k.val → Odd k.val → k.val.Prime := by decide +kernel
  exact hc (hp ⟨n, Nat.lt_of_not_ge h9⟩ hn ho)

/-- For every odd composite 1 < n < 3000, a prime strong Miller--Rabin witness
lies below the proposed concave envelope at log n, without GRH.
The existing finite classification supplies base two except at 2047;
there either base two or three is absorbed by the second certified vertex.
This connects actual finite witnesses to the fitted expression. -/
theorem exists_prime_witness_le_mrRegion_of_lt_3000 {n : ℕ} (hn : 1 < n) (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hlt : n < 3000) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ mrSmallRegionEnvelope (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have h9 := mrRegion_odd_composite_ge_nine hn hnOdd hnComposite
  have hmax : n ≤ 100000 := (Nat.le_of_lt hlt).trans (by decide : 3000 ≤ 100000)
  by_cases he : n = 2047
  · subst n
    have hb := mrRegion_envelope_ge_three (le_refl 2047) (by decide : 2047 ≤ 100000)
    rcases PrimeTest.base_two_or_three_rejects_of_lt_3000 hn hnOdd hnComposite hlt with h2 | h3
    · exact
        ⟨2, by decide, (by norm_num only : (2 : ℝ) ≤ 3).trans hb,
          PrimeTest.strongMillerRabinWithBase_eq_false_iff_not_pass.mp h2⟩
    · exact ⟨3, by decide, hb, PrimeTest.strongMillerRabinWithBase_eq_false_iff_not_pass.mp h3⟩
  · exact
      ⟨2, by decide, mrRegion_envelope_ge_two h9 hmax,
        PrimeTest.strongMillerRabinWithBase_eq_false_iff_not_pass.mp
          (PrimeTest.base_two_rejects_of_lt_3000_of_ne_2047 hn hnOdd hnComposite hlt he)⟩

/-- For an odd composite 1 < n < 3000 and n ≤ B ≤ 100000, a prime witness
lies below the same fitted expression at log B, without GRH.
Transfer the pointwise witness by envelope monotonicity within its checked domain.
This is the finite-range interface with no weaker maximum formula. -/
theorem exists_prime_witness_le_mrRegion_envelope_of_lt_3000 {n B : ℕ} (hn : 1 < n) (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hlt : n < 3000) (hnB : n ≤ B) (hB : B ≤ 100000) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ mrSmallRegionEnvelope (Real.log B) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hb, hf⟩ := exists_prime_witness_le_mrRegion_of_lt_3000 hn hnOdd hnComposite hlt
  have hmono :=
    mrSmallRegionEnvelope_monotone
      (Real.log_le_log (Nat.cast_pos.mpr (zero_lt_one.trans hn)) (Nat.cast_le.mpr hnB))
      (mrRegion_log_upper ((zero_lt_one.trans hn).trans_le hnB) hB)
  exact ⟨p, hp, hb.trans hmono, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
