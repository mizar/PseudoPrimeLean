/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaNonOneWitnessBounds
public import PseudoPrime.PseudoSquare.Bounds.PointwiseWitness
public import PseudoPrime.PseudoSquare.Bounds.QNeOneLogSq

/-! # Coefficient 0.8 non-one witnesses from 10^17400

The non-one comparison permits zero-valued prime witnesses.
Pointwise and finite-maximum bounds share the same coefficient and starting value.
-/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- For an odd nonsquare n with level 4n≥20000, under GRH and L≥40000 with log(n)≤L,
 there is an odd prime non-one Jacobi witness at most (4/5)L².
 Apply the non-one Gamma comparison to the complex quadratic character.
 On units use prime evaluation; on nonunits use the zero Jacobi value.
 This permits the same scale for pointwise bounds and finite maxima. -/
theorem exists_prime_ne_one_witness_le_gamma_at_endpoint {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hq : 20000 ≤ 4 * n) {L : ℝ} (hL : 40000 ≤ L) (hlogn : Real.log n ≤ L)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (4 / 5 : ℝ) * L ^ 2 ∧ jacobiSym n p ≠ 1 := by
  let : NeZero (4 * n) := ⟨Nat.mul_ne_zero (by norm_num only) (Odd.pos hn).ne'⟩
  have hlogq : Real.log (4 * n : ℕ) ≤ L + 2 := by
    rw [LLS.log_original_quadratic_level (Odd.pos hn)]
    linarith only [hlogn, LLS.log_four_le_two]
  obtain ⟨p, hp, hodd, hbound, hval⟩ :=
    LLS.exists_odd_prime_ne_one_of_gamma_log_40000 hq (NumberTheory.complexQuadraticCharacter n hn)
      (NumberTheory.complexQuadraticCharacter_isQuadratic n hn)
      (NumberTheory.complexQuadraticCharacter_ne_one_of_not_square n hn hns)
      (by exact ⟨2 * n, by ring⟩) hGRH hL hlogq
  refine ⟨p, hp, hodd, hbound, ?_⟩
  by_cases hc : Nat.Coprime p n
  · intro hv
    have he := NumberTheory.complexQuadraticCharacter_apply_odd_prime n hn hp hodd hc
    rw [hv, Int.cast_one] at he
    exact hval he
  · let : NeZero p := ⟨hp.ne_zero⟩
    have hg : (n : ℤ).gcd p ≠ 1 := by
      simpa only [Int.gcd_natCast_natCast, ← Nat.coprime_iff_gcd_eq_one, Nat.coprime_comm] using hc
    rw [NumberTheory.jacobi_eq_zero_iff_not_coprime.mpr hg]
    norm_num only

/-- For n≥10^17400, log(n)≥40000. Use logarithmic monotonicity and log(10)>23/10.
 Avoid expanding the natural power. This supplies the decimal public threshold. -/
theorem log_nat_ge_40000_of_decimal {n : ℕ} (hN : 10 ^ 17400 ≤ n) : (40000 : ℝ) ≤ Real.log n := by
  have hpos : 0 < (10 : ℝ) ^ (17400 : ℕ) := pow_pos (by norm_num only) _
  have hcast : (10 : ℝ) ^ (17400 : ℕ) ≤ (n : ℝ) := by exact_mod_cast hN
  have hl := Real.log_le_log hpos hcast
  rw [Real.log_pow] at hl
  norm_num only at hl
  linarith only [hl, Analysis.log_ten_gt_twenty_three_tenths]

/-- For decimal exponent d≥5, 10^d≥20000. Compare powers with the small exponent five.
 This avoids large numeral evaluation in the ambient-level gate. -/
private theorem nonOne_decimal_cutoff_ge (d : ℕ) (hd : 5 ≤ d) : 20000 ≤ 10 ^ d := by
  exact (by decide : 20000 ≤ 10 ^ 5).trans (Nat.pow_le_pow_right (by decide : 0 < 10) hd)

/-- Under GRH, every odd nonsquare n≥10^17400 has an odd prime p with Jacobi value
 different from one and p≤(4/5)log(n)². Apply the common-scale theorem at L=log(n).
 This improves the non-one starting value while retaining coefficient 0.8. -/
theorem exists_prime_ne_one_witness_le_gamma_17400
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hN : 10 ^ 17400 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log n) ^ 2 ∧ jacobiSym n p ≠ 1 := by
  have hnlarge : 20000 ≤ n := (nonOne_decimal_cutoff_ge 17400 (by decide : 5 ≤ 17400)).trans hN
  have hq : 20000 ≤ 4 * n :=
    (by norm_num only : 20000 ≤ 4 * 20000).trans (Nat.mul_le_mul_left 4 hnlarge)
  exact
    exists_prime_ne_one_witness_le_gamma_at_endpoint hn hns hq (log_nat_ge_40000_of_decimal hN)
      (le_refl _) hGRH

/-- Under GRH and n≥10^17400 for an odd nonsquare n, its least odd-prime non-one
 Jacobi witness is at most (4/5)log(n)². Minimize the bounded witness.
 This is the pointwise least-witness form of the improved non-one theorem. -/
theorem primeNeOneWitness_cast_le_gamma_17400
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hN : 10 ^ 17400 ≤ n)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤ (4 / 5 : ℝ) * (Real.log n) ^ 2 := by
  obtain ⟨p, hp, ho, hb, hv⟩ := exists_prime_ne_one_witness_le_gamma_17400 hGRH hn hns hN
  exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hb

/-- For every odd nonsquare n under GRH and L≥40000 with log(n)≤L,
 the least non-one witness is at most (4/5)L². Large levels use the common-scale Gamma
 theorem; smaller levels use the existing global non-one envelope bounded by 121.
 This covers all inputs, including those below the public decimal starting value. -/
theorem primeNeOneWitness_cast_le_gamma_endpoint
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) {L : ℝ} (hL : 40000 ≤ L) (hlogn : Real.log n ≤ L)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤ (4 / 5 : ℝ) * L ^ 2 := by
  by_cases hq : 20000 ≤ 4 * n
  · obtain ⟨p, hp, ho, hb, hv⟩ :=
      exists_prime_ne_one_witness_le_gamma_at_endpoint hn hns hq hL hlogn hGRH
    exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hb
  · have hnsmall : n ≤ 46000 := by
      have ht := lt_of_not_ge hq
      nlinarith only [ht]
    have hnR : (n : ℝ) ≤ 46000 := by exact_mod_cast hnsmall
    have hn0 : (0 : ℝ) < n := by exact_mod_cast Odd.pos hn
    have hl := (Real.log_le_log hn0 hnR).trans Analysis.log_46000_lt_eleven.le
    have hl0 : 0 ≤ Real.log n :=
      Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Odd.pos hn).ne')
    have hs : (Real.log n) ^ 2 ≤ (11 : ℝ) ^ 2 := (sq_le_sq₀ hl0 (by norm_num only)).mpr hl
    obtain ⟨p, hp, ho, hb, hv⟩ := exists_prime_ne_one_witness_of_grh hGRH (Odd.pos hn) hn hns
    have hmax : max (5 : ℝ) ((Real.log n) ^ 2) ≤ (11 : ℝ) ^ 2 := max_le (by norm_num only) hs
    have hbudget : (11 : ℝ) ^ 2 ≤ (4 / 5 : ℝ) * L ^ 2 := by
      nlinarith only [hL, sq_nonneg (L - 40000)]
    exact
      (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hv⟩)).trans
        (hb.trans (hmax.trans hbudget))

/-- Under GRH and B≥10^17400, the finite maximum of least odd-prime non-one witnesses
 is at most (4/5)log(B)². Cover every admissible n≤B at the common endpoint scale.
 The pointwise coefficient and starting value are retained without an extra maximum cutoff. -/
theorem QNeOne_le_gamma_17400 {B : ℕ} (hB : 10 ^ 17400 ≤ B)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (QNeOne B : ℝ) ≤ (4 / 5 : ℝ) * (Real.log B) ^ 2 := by
  apply QNeOne_cast_le_of_forall (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4 / 5) (sq_nonneg _))
  intro n hn
  have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Odd.pos ha.odd
  have hnB : (n : ℝ) ≤ B := by exact_mod_cast ha.le
  exact
    primeNeOneWitness_cast_le_gamma_endpoint hGRH ha.odd ha.not_isSquare
      (log_nat_ge_40000_of_decimal hB) (Real.log_le_log hn0 hnB)
      (NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
        (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare ha.odd ha.not_isSquare))

end PseudoPrime.PseudoSquare
