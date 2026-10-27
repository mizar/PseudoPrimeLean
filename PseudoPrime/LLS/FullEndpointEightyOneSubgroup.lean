/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.FullEndpointEightyOneRange
public import PseudoPrime.LLS.Theorem11S1Subgroup
public import PseudoPrime.Analysis.AdaptiveReciprocalRadius

/-! # Subgroup consumers and radius comparisons for the continuous endpoint bounds -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For every positive real L, (9/10)L is strictly below L-2log L+4.
Use the logarithmic tangent at twenty and log twenty below three.
This generic comparison explains dominance over the previous corrected radii. -/
theorem fullEndpoint_nineTenths_lt_log_corrected {L : ℝ} (hL : 0 < L) :
    (9 / 10 : ℝ) * L < L - 2 * Real.log L + 4 := by
  have h20 : Real.log (20 : ℝ) < 3 := by
    rw [show (20 : ℝ) = 2 ^ 2 * 5 by norm_num only,
      Real.log_mul (by norm_num only : (2 : ℝ) ^ 2 ≠ 0) (by norm_num only : (5 : ℝ) ≠ 0),
      Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_lt_d9, Real.log_five_lt_d9]
  have ht := Real.log_le_sub_one_of_pos (div_pos hL (by norm_num only : (0 : ℝ) < 20))
  rw [Real.log_div hL.ne' (by norm_num only : (20 : ℝ) ≠ 0)] at ht
  linarith only [ht, h20]

/-- For real L at least nine, (81/100)L squared is strictly below the adaptive
reciprocal squared radius. Use its proved reference-root lower bound and the generic
nine-tenths comparison. This certifies the new interval in the public best-bound table. -/
theorem fullEndpoint_eightyOne_lt_adaptive {L : ℝ} (hL : 9 ≤ L) :
    (81 / 100 : ℝ) * L ^ 2 < Analysis.adaptivePart2CutoffRoot L ^ 2 := by
  have ht :=
    Analysis.finerPart2Root_ge_thirty_six_fifths_of_639_div_100_le
      (by linarith only [hL] : (639 / 100 : ℝ) ≤ L)
  have hb :=
    Analysis.adaptivePart2Root_bounds
      (show 7 ≤ Analysis.finerPart2CutoffRoot L by linarith only [ht])
  have hc := fullEndpoint_nineTenths_lt_log_corrected (by linarith only [hL] : 0 < L)
  have hY : (9 / 10 : ℝ) * L < Analysis.adaptivePart2CutoffRoot L := by
    dsimp only [Analysis.finerPart2CutoffRoot] at hb
    linarith only [hb.1, hc]
  have hp :=
    mul_pos (sub_pos.mpr hY)
      (show 0 < Analysis.adaptivePart2CutoffRoot L + (9 / 10 : ℝ) * L by linarith only [hY, hL])
  nlinarith only [hp]

/-- Under GRH, a proper unit subgroup at 9<=log q<=26 has a prime outside its
image through (81/100)(log q)^2. Pull back a nonprincipal quotient character and use the
continuous endpoint certificate. Nonunit primes remain valid subgroup-image witnesses. -/
theorem exists_prime_outside_subgroup_le_eightyOne_log_sq {q : ℕ} [NeZero q]
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL9 : 9 ≤ Real.log q)
    (hL26 : Real.log q ≤ 26) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (81 / 100 : ℝ) * (Real.log q) ^ 2 ∧ ¬∃ u ∈ H, (u : ZMod q) = (p : ZMod q) := by
  have : H.Normal := H.normal_of_isMulCommutative
  have : Nontrivial ((ZMod q)ˣ ⧸ H) := QuotientGroup.nontrivial_iff.mpr hH
  obtain ⟨z, hz⟩ := exists_ne (1 : (ZMod q)ˣ ⧸ H)
  obtain ⟨χ', hχ⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity ((ZMod q)ˣ ⧸ H) ℂ hz
  obtain ⟨p, hp, hb, hv⟩ :=
    exists_prime_ne_one_le_eightyOne_log_sq (pullbackCharacter χ')
      (pullbackCharacter_ne_one_of_ne_one χ' hχ) hGRH hL9 hL26
  refine ⟨p, hp, hb, ?_⟩
  rintro ⟨u, hu, he⟩
  apply hv
  rw [← he]
  exact pullbackCharacter_eq_one_of_mem χ' hu

/-- Under GRH, a proper unit subgroup at log q<=9 has a prime at most sixty-one
outside its image. Pull back a nonprincipal quotient character and use the fixed endpoint
certificate. This is a uniform analytic bound without enumeration of input moduli. -/
theorem exists_prime_outside_subgroup_le_sixty_one {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (hH : H ≠ ⊤) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL9 : Real.log q ≤ 9) : ∃ p : ℕ, p.Prime ∧ p ≤ 61 ∧ ¬∃ u ∈ H, (u : ZMod q) = (p : ZMod q) := by
  have : H.Normal := H.normal_of_isMulCommutative
  have : Nontrivial ((ZMod q)ˣ ⧸ H) := QuotientGroup.nontrivial_iff.mpr hH
  obtain ⟨z, hz⟩ := exists_ne (1 : (ZMod q)ˣ ⧸ H)
  obtain ⟨χ', hχ⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity ((ZMod q)ˣ ⧸ H) ℂ hz
  obtain ⟨p, hp, hb, hv⟩ :=
    exists_prime_ne_one_le_sixty_one_of_log_le_nine (pullbackCharacter χ')
      (pullbackCharacter_ne_one_of_ne_one χ' hχ) hGRH hL9
  refine ⟨p, hp, hb, ?_⟩
  rintro ⟨u, hu, he⟩
  apply hv
  rw [← he]
  exact pullbackCharacter_eq_one_of_mem χ' hu

end PseudoPrime.LLS.PaperStatements
