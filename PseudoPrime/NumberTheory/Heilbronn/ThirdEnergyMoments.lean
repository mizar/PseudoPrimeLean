/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.GlobalCorrelationTail
public import PseudoPrime.NumberTheory.Heilbronn.CorrelationEnergyMoments
public import PseudoPrime.Analysis.CubicTailThirdMoments

/-! # Third correlation moments for the Heilbronn subgroup -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- For odd prime p, the normalized third correlation moment is bounded by
786432 p² harmonic(p). Apply the generic layer estimate to the uniform cubic
tail. This is the finite third-moment input to energy amplification. -/
theorem normalized_third_moment_le_harmonic {p : ℕ} [Fact p.Prime] (hodd : Odd p) :
    (∑ τ : ZMod p, (normalizedCorrelation p τ : ℚ) ^ 3) ≤ 786432 * (p : ℚ) ^ 2 * harmonic p := by
  have hN : ∀ τ : ZMod p, normalizedCorrelation p τ ≤ p := fun τ ↦
    (card_cosetDifferenceAt_le 0 0 (principalShift p τ)).trans (Nat.sub_le p 1)
  have ht :=
    Analysis.sum_cubes_le_of_cubic_tail (normalizedCorrelation p) p (262144 * p ^ 2) hN
      (fun k _ ↦
        card_mul_cube_le_of_normalizedCorrelation_ge_all hodd
          (Finset.univ.filter (fun τ ↦ k + 1 ≤ normalizedCorrelation p τ))
          (fun τ hτ ↦ (Finset.mem_filter.mp hτ).2))
  norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at ht
  convert ht using 1
  ring

/-- For odd prime p, the normalized third moment is at most
786432 p²(1+ln p). Cast the harmonic estimate and apply its logarithmic bound.
This removes the finite harmonic sum from later real energy budgets. -/
theorem normalized_third_moment_le_log {p : ℕ} [Fact p.Prime] (hodd : Odd p) :
    (∑ τ : ZMod p, (normalizedCorrelation p τ : ℝ) ^ 3) ≤
      786432 * (p : ℝ) ^ 2 * (1 + Real.log p) := by
  have hq := normalized_third_moment_le_harmonic hodd
  have hr :
    (∑ τ : ZMod p, (normalizedCorrelation p τ : ℝ) ^ 3) ≤
      786432 * (p : ℝ) ^ 2 * (harmonic p : ℝ) := by
    exact_mod_cast hq
  exact
    hr.trans
      (mul_le_mul_of_nonneg_left (harmonic_le_one_add_log p)
        (mul_nonneg (by norm_num only) (sq_nonneg (p : ℝ))))

/-- Third additive energy: the sum of cubes of ordered difference counts
of the Heilbronn subgroup in ZMod(p²). This unnormalized natural number is
used in the mixed third-energy and amplification estimates. -/
noncomputable def heilbronnThirdEnergy (p : ℕ) [Fact p.Prime] : ℕ :=
  ∑ c : ZMod (p ^ 2), Nat.card (cosetDifferenceAt p 0 0 c) ^ 3

/-- Unit difference cubes sum to (p-1) times the normalized third moment.
Parametrize units by a principal shift and a nonzero residue and use
multiplicative invariance. This isolates the unit contribution to E₃. -/
theorem sum_unit_correlations_cube {p : ℕ} [Fact p.Prime] :
    (∑ c : { c : ZMod (p ^ 2) // IsUnit c }, Nat.card (cosetDifferenceAt p 0 0 c.val) ^ 3) =
      (p - 1) * ∑ τ : ZMod p, normalizedCorrelation p τ ^ 3 := by
  classical
  have he :=
    Fintype.sum_bijective (unitParameterMap (p := p)) unitParameterMap_bijective
      (fun z : ZMod p × { g : ZMod p // g ≠ 0 } ↦ normalizedCorrelation p z.1 ^ 3)
      (fun c : { c : ZMod (p ^ 2) // IsUnit c } ↦ Nat.card (cosetDifferenceAt p 0 0 c.val) ^ 3)
      (fun z ↦
        congrArg (fun n : ℕ ↦ n ^ 3)
          (card_cosetDifferenceAt_mul_teichLift 0 0 _ z.2.val z.2.property).symm)
  rw [← he, Fintype.sum_prod_type]
  have hc : Fintype.card { g : ZMod p // g ≠ 0 } = p - 1 := by
    rw [Fintype.card_subtype_compl (fun g : ZMod p ↦ g = 0), ZMod.card, Fintype.card_subtype_eq]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Nat.cast_id, hc]
  rw [Finset.mul_sum]

/-- The full third energy equals (p-1)³ plus (p-1) times the normalized
third moment. Separate zero, unit and nonzero nonunit differences and use
multiplicative invariance. This transfers the normalized bound to E₃. -/
theorem heilbronnThirdEnergy_eq_normalized_moment {p : ℕ} [Fact p.Prime] :
    heilbronnThirdEnergy p =
      (p - 1) ^ 3 + (p - 1) * ∑ τ : ZMod p, normalizedCorrelation p τ ^ 3 := by
  classical
  let : Nontrivial (ZMod (p ^ 2)) := (squareReduction p).domain_nontrivial
  have hz : ¬IsUnit (0 : ZMod (p ^ 2)) := not_isUnit_zero
  have hn :
    (∑ c : { c : ZMod (p ^ 2) // ¬IsUnit c }, Nat.card (cosetDifferenceAt p 0 0 c.val) ^ 3) =
      (p - 1) ^ 3 := by
    rw [Finset.sum_eq_single (⟨0, hz⟩ : { c : ZMod (p ^ 2) // ¬IsUnit c })]
    · rw [card_cosetDifferenceAt_zero]
    · intro c hc hne
      have hc0 : c.val ≠ 0 := fun he ↦ hne (Subtype.ext he)
      rw [cosetDifferenceAt_nonunit_empty 0 c.val hc0 c.property, Nat.card_of_isEmpty,
        zero_pow (by decide : 3 ≠ 0)]
    · intro hnot
      exact (hnot (Finset.mem_univ _)).elim
  have he :=
    Fintype.sum_subtype_add_sum_subtype (IsUnit : ZMod (p ^ 2) → Prop)
      (fun c ↦ Nat.card (cosetDifferenceAt p 0 0 c) ^ 3)
  rw [sum_unit_correlations_cube, hn] at he
  exact he.symm.trans (Nat.add_comm _ _)

/-- For odd prime p, the full third additive energy is at most
786433 p³(1+ln p). The normalized logarithmic third moment bounds unit
differences and the zero difference contributes at most p³.
This is the E₃ input required by the improved energy argument. -/
theorem heilbronnThirdEnergy_le_log {p : ℕ} [Fact p.Prime] (hodd : Odd p) :
    (heilbronnThirdEnergy p : ℝ) ≤ 786433 * (p : ℝ) ^ 3 * (1 + Real.log p) := by
  rw [heilbronnThirdEnergy_eq_normalized_moment, Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_sum]
  simp only [Nat.cast_pow]
  have hm := normalized_third_moment_le_log hodd
  have hpn : ((p - 1 : ℕ) : ℝ) ≤ p := Nat.cast_le.mpr (Nat.sub_le p 1)
  have hzero : (0 : ℝ) ≤ ((p - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  have hlog := Real.log_natCast_nonneg p
  have hcube := pow_le_pow_left₀ hzero hpn 3
  have hmass :=
    mul_le_mul hpn hm (Finset.sum_nonneg (fun _ _ ↦ pow_nonneg (Nat.cast_nonneg _) 3)) hp0
  have hunit :=
    mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 1 + Real.log p by linarith only [hlog])
      (pow_nonneg hp0 3)
  nlinarith only [hcube, hmass, hunit]

end PseudoPrime.NumberTheory.Heilbronn
