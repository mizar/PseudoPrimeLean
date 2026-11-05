/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.ReciprocalGapEvenAmbient
public import PseudoPrime.LLS.PaperStatements.FullEndpointEvenPolynomial

/-! # Even-character bounds for local Miller–Rabin witnesses -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- If every strong pass modulo odd `n > 1` maps into `H` at a divisor `q`, then
`-1` belongs to `H`. Use the passing base `n - 1` and reduce it modulo `q`.
This supplies evenness for local quotient characters. -/
theorem neg_one_mem_of_local_pass {n q : ℕ} [NeZero q] (hn : 1 < n) (ho : Odd n) (hqn : q ∣ n)
    (H : Subgroup (ZMod q)ˣ)
    (hpass :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
          ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (a : ZMod q)) :
    (-1 : (ZMod q)ˣ) ∈ H := by
  have hncast : ((n - 1 : ℕ) : ZMod n) = -1 := by
    rw [Nat.cast_sub (Nat.le_of_lt hn), ZMod.natCast_self, Nat.cast_one, zero_sub]
  have hqcast : ((n - 1 : ℕ) : ZMod q) = -1 := by
    rw [Nat.cast_sub (Nat.le_of_lt hn), (ZMod.natCast_eq_zero_iff n q).mpr hqn, Nat.cast_one,
      zero_sub]
  obtain ⟨u, hu, heq⟩ := hpass (n - 1) (hncast ▸ strongMillerRabinPass_neg_one hn ho)
  have : u = -1 := by
    apply Units.ext
    simpa only [Units.val_neg, Units.val_one] using heq.trans hqcast
  exact this ▸ hu

/-- Under GRH and a positive even endpoint gap, a proper subgroup containing
`-1` misses the residue of some prime at most `y²`. Pull a nontrivial quotient
character back to the original modulus; its evenness follows from membership of
`-1`. This is the analytic input to local Miller–Rabin witness bounds. -/
theorem exists_prime_outside_of_even_gap {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hneg : (-1 : (ZMod q)ˣ) ∈ H) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {y : ℝ} (hy : 8 ≤ y)
    (hgap :
      0 <
        LLS.PaperStatements.fullEndpointEvenExactComparisonGap (Real.log q) (2096 / 1831) y
          (Real.log y)) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ y ^ 2 ∧ ∀ u : (ZMod q)ˣ, u ∈ H → (u : ZMod q) ≠ (p : ZMod q) := by
  have : H.Normal := H.normal_of_isMulCommutative
  have : Nontrivial ((ZMod q)ˣ ⧸ H) := QuotientGroup.nontrivial_iff.mpr hH
  obtain ⟨x, hx⟩ := exists_ne (1 : (ZMod q)ˣ ⧸ H)
  obtain ⟨χ, hχ⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity ((ZMod q)ˣ ⧸ H) ℂ hx
  have he : (LLS.pullbackCharacter χ).Even := by
    change (LLS.pullbackCharacter χ) (-1) = 1
    simpa only [Units.val_neg, Units.val_one] using LLS.pullbackCharacter_eq_one_of_mem χ hneg
  obtain ⟨p, hp, hb, hv⟩ :=
    LLS.PaperStatements.exists_prime_ne_one_of_pos_evenExactGap (LLS.pullbackCharacter χ)
      (LLS.pullbackCharacter_ne_one_of_ne_one χ hχ) he hGRH hy hgap
  refine ⟨p, hp, hb, ?_⟩
  intro u hu heq
  exact hv (heq ▸ LLS.pullbackCharacter_eq_one_of_mem χ hu)

/-- Under GRH, a positive even endpoint gap for a divisor modulus `q` gives a
prime rejecting odd `n > 1` through `y²`, provided a proper subgroup contains
all local images of strong passes. The passing base `n - 1` forces evenness;
the prime outside the subgroup then rejects the original input. -/
theorem exists_prime_reject_of_local_even_gap {n q : ℕ} [NeZero q] (hn : 1 < n) (ho : Odd n)
    (hqn : q ∣ n) (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hpass :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
          ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (a : ZMod q))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 8 ≤ y)
    (hgap :
      0 <
        LLS.PaperStatements.fullEndpointEvenExactComparisonGap (Real.log q) (2096 / 1831) y
          (Real.log y)) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ y ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hb, hout⟩ :=
    exists_prime_outside_of_even_gap H hH (neg_one_mem_of_local_pass hn ho hqn H hpass) hGRH hy hgap
  refine ⟨p, hp, hb, ?_⟩
  intro hpasse
  obtain ⟨u, hu, heq⟩ := hpass p hpasse
  exact hout u hu heq

/-- A certified correction `d < h(b)` with `8 ≤ b` makes the even endpoint gap
positive at radius `max b (s - d)` for every level `t ≤ s`. Monotonicity of `h`
and the exact gap identity provide the continuous local-radius criterion. -/
theorem even_gap_pos_of_shift {b d s t : ℝ} (hb : 8 ≤ b)
    (hd : d < LLS.PaperStatements.fullEndpointEvenGapCorrection b) (hs : t ≤ s) :
    0 <
      LLS.PaperStatements.fullEndpointEvenExactComparisonGap t (2096 / 1831) (max b (s - d))
        (Real.log (max b (s - d))) := by
  let y := max b (s - d)
  have hby : b ≤ y := le_max_left _ _
  have hsy : s - d ≤ y := le_max_right _ _
  have hy : 8 ≤ y := hb.trans hby
  have hc :
    LLS.PaperStatements.fullEndpointEvenGapCorrection b ≤
      LLS.PaperStatements.fullEndpointEvenGapCorrection y :=
    LLS.PaperStatements.fullEndpointEvenGapCorrection_strictMonoOn.monotoneOn hb hy hby
  have hh : 0 < y + LLS.PaperStatements.fullEndpointEvenGapCorrection y - t := by
    linarith only [hd, hs, hsy, hc]
  rw [LLS.PaperStatements.fullEvenExactGap_eq_denominator_correction hy]
  exact mul_pos (LLS.PaperStatements.fullEndpointEvenGapDenominator_pos hy) hh

/-- Under GRH, an odd input and a proper local subgroup containing its passing
residues have a rejecting prime at most `max b (s - d)²`, when the local level
is at most `s` and `d` is below the even correction at `b ≥ 8`. Combine the
gap criterion with the local-to-original witness transfer; this is the common
consumer for the finite family of certified corrections. -/
theorem exists_prime_reject_of_local_shift {n q : ℕ} [NeZero q] (hn : 1 < n) (ho : Odd n)
    (hqn : q ∣ n) (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hpass :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
          ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (a : ZMod q))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {b d s : ℝ} (hb : 8 ≤ b)
    (hd : d < LLS.PaperStatements.fullEndpointEvenGapCorrection b) (hs : Real.log q ≤ s) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (max b (s - d)) ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  exact
    exists_prime_reject_of_local_even_gap hn ho hqn H hH hpass hGRH (hb.trans (le_max_left _ _))
      (even_gap_pos_of_shift hb hd hs)

end PseudoPrime.PrimeTestBounds.MillerRabin
