/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.CongruenceGrowthBudget
public import PseudoPrime.NumberTheory.Heilbronn.HeightLayerCutoffs

/-! # Transfer height-layer counts to the Heilbronn energy budget -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- Inputs: a natural-power count bound `N^a ≤ D^a H^a p^g`, a height bound
`H^a ≤ p^(2a-b)`, a scale bound `p^b ≤ k^a`, and enough exponent slack to absorb
the energy constant for large p. Claim: `p * heilbronnEnergy p * N < k^2`.
Proof: square the count bound, use the height estimate, and apply
`counting_budget_of_even_power`. Role: connect rational height-layer estimates to
the existing energy-to-witness argument. -/
theorem height_layer_count_energy_budget {p H k a b g D : ℕ} [Fact p.Prime] (hodd : Odd p)
    (ha : 0 < a) (hb : b ≤ 2 * a) (hslack : 11 * a + 2 * g < 6 * b) (hcut : p ^ b ≤ k ^ a)
    (hheight : H ^ a ≤ p ^ (2 * a - b))
    (hcount : boundedCongruenceCount p H ^ a ≤ D ^ a * H ^ a * p ^ g)
    (hlarge : 18874370 ^ a * D ^ (2 * a) < p ^ (6 * b - 11 * a - 2 * g)) :
    p * heilbronnEnergy p * boundedCongruenceCount p H < k ^ 2 := by
  have hpPos : 0 < p := (Fact.out : Nat.Prime p).pos
  have hN2 : boundedCongruenceCount p H ^ (2 * a) ≤ D ^ (2 * a) * H ^ (2 * a) * p ^ (2 * g) := by
    calc
      _ = (boundedCongruenceCount p H ^ a) ^ 2 := by
        rw [← pow_mul]
        congr 1
        omega
      _ ≤ (D ^ a * H ^ a * p ^ g) ^ 2 := Nat.pow_le_pow_left hcount 2
      _ = D ^ (2 * a) * H ^ (2 * a) * p ^ (2 * g) := by simp only [mul_pow, pow_mul, Nat.mul_comm]
  have hH2a : H ^ (2 * a) ≤ p ^ (2 * (2 * a - b)) := by
    calc
      _ = (H ^ a) ^ 2 := by
        rw [← pow_mul]
        congr 1
        omega
      _ ≤ (p ^ (2 * a - b)) ^ 2 := Nat.pow_le_pow_left hheight 2
      _ = p ^ (2 * (2 * a - b)) := by
        rw [← pow_mul]
        congr 1
        omega
  have hcoeff :
    18874370 ^ a * D ^ (2 * a) * p ^ (7 * a + 2 * (2 * a - b) + 2 * g) < p ^ (4 * b) := by
    have hexp : (6 * b - 11 * a - 2 * g) + (7 * a + 2 * (2 * a - b) + 2 * g) = 4 * b := by omega
    calc
      _ < p ^ (6 * b - 11 * a - 2 * g) * p ^ (7 * a + 2 * (2 * a - b) + 2 * g) :=
        Nat.mul_lt_mul_of_pos_right hlarge (Nat.pow_pos hpPos)
      _ = p ^ (4 * b) := by rw [← pow_add, hexp]
  have hH2a' : H ^ (2 * a) ≤ p ^ (2 * (2 * a - b)) := hH2a
  have hgap :
    (p ^ 2 * (18874370 * p ^ 5)) ^ a * (D ^ (2 * a) * H ^ (2 * a) * p ^ (2 * g)) < k ^ (4 * a) := by
    have hbase : (p ^ 2 * (18874370 * p ^ 5)) ^ a = 18874370 ^ a * p ^ (7 * a) := by
      rw [show p ^ 2 * (18874370 * p ^ 5) = 18874370 * p ^ 7 by ring, mul_pow, ← pow_mul]
    have hheight' :
      p ^ (7 * a) * H ^ (2 * a) * p ^ (2 * g) ≤
        p ^ (7 * a) * p ^ (2 * (2 * a - b)) * p ^ (2 * g) := by
      calc
        _ = p ^ (7 * a) * (H ^ (2 * a) * p ^ (2 * g)) := by ring
        _ ≤ p ^ (7 * a) * (p ^ (2 * (2 * a - b)) * p ^ (2 * g)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hH2a')
        _ = p ^ (7 * a) * p ^ (2 * (2 * a - b)) * p ^ (2 * g) := by ring
    have hbound :
      18874370 ^ a * D ^ (2 * a) * (p ^ (7 * a) * p ^ (2 * (2 * a - b)) * p ^ (2 * g)) <
        p ^ (4 * b) := by
      have hpow :
        p ^ (7 * a) * p ^ (2 * (2 * a - b)) * p ^ (2 * g) =
          p ^ (7 * a + 2 * (2 * a - b) + 2 * g) := by
        rw [← pow_add, ← pow_add]
      rw [hpow]
      exact hcoeff
    calc
      _ = 18874370 ^ a * D ^ (2 * a) * (p ^ (7 * a) * H ^ (2 * a) * p ^ (2 * g)) := by
        rw [hbase]; ring
      _ ≤ 18874370 ^ a * D ^ (2 * a) * (p ^ (7 * a) * p ^ (2 * (2 * a - b)) * p ^ (2 * g)) :=
        Nat.mul_le_mul_left _ hheight'
      _ < p ^ (4 * b) := hbound
      _ ≤ k ^ (4 * a) := by
        have h := Nat.pow_le_pow_left hcut 4
        simpa only [← pow_mul, Nat.mul_comm] using h
  apply counting_budget_of_even_power ha (heilbronnEnergy_square_le_uniform hodd) hN2
  exact hgap

/-- Inputs: fixed natural exponents with `11a+2g<6b`. Claim: beyond an explicit
threshold depending on `a,g,D`, the coefficient condition used by
`height_layer_count_energy_budget` holds. Choose `p` above the coefficient and use
`p ≤ p^s` for the positive integer slack `s=6b-11a-2g`. Role: isolate the final
large-prime absorption from the finite height-layer count. -/
theorem exists_height_layer_energy_threshold {a b g D : ℕ} (hslack : 11 * a + 2 * g < 6 * b) :
    ∃ P : ℕ, ∀ p : ℕ, P ≤ p → 18874370 ^ a * D ^ (2 * a) < p ^ (6 * b - 11 * a - 2 * g) := by
  have hs : 0 < 6 * b - 11 * a - 2 * g := by omega
  let M : ℕ := 18874370 ^ a * D ^ (2 * a)
  refine ⟨M + 1, ?_⟩
  intro p hp
  have hp0 : 0 < p := Nat.lt_of_lt_of_le (Nat.zero_lt_succ M) hp
  have hMp : M < p := Nat.lt_of_lt_of_le (Nat.lt_succ_self M) hp
  have hpow : p ≤ p ^ (6 * b - 11 * a - 2 * g) := by
    have h := Nat.pow_le_pow_right hp0 (Nat.succ_le_of_lt hs)
    simpa only [pow_one] using h
  change M < p ^ (6 * b - 11 * a - 2 * g)
  exact Nat.lt_of_lt_of_le hMp hpow

/-- A single constant controls the degree-42 small-height term for every p and H.
The divisor-power estimate is uniform in H; the cutoff inequalities then give the
same exponent `1/42+eta` uniformly in p. -/
theorem exists_global_shiftedHeightSmallTerm_rpow_bound {theta delta eta : ℝ} (hdelta : 0 < delta)
    (htheta0 : 0 < theta) (hbudget : theta + delta / 6 ≤ eta) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ p H : ℕ,
          1 < p →
            H ≤ shiftedHeightCutoff p theta 6 →
            ((shiftedHeightCutoff p theta 42 * H * maxDivisorCount H : ℕ) : ℝ) ≤
              C * H * (p : ℝ) ^ (1 / 42 + eta) := by
  obtain ⟨C, hC, hdiv⟩ := exists_uniform_maxDivisorCount_rpow_bound hdelta
  refine ⟨C, hC, ?_⟩
  intro p H hp htop
  by_cases hH : H = 0
  · subst H
    simp only [Nat.cast_zero, zero_mul, mul_zero]
    exact le_refl (0 : ℝ)
  · have hHpos : 0 < H := Nat.pos_of_ne_zero hH
    have hcut42 : (shiftedHeightCutoff p theta 42 : ℝ) ≤ (p : ℝ) ^ (1 / (42 : ℝ) - theta) :=
      shiftedHeightCutoff_cast_le
    have hHcut : (H : ℝ) ≤ (p : ℝ) ^ (1 / (6 : ℝ) - theta) := by
      exact (Nat.cast_le.mpr htop).trans shiftedHeightCutoff_cast_le
    have hpR : (1 : ℝ) ≤ (p : ℝ) := Nat.one_le_cast.mpr hp.le
    have hp0 : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr (Nat.lt_trans Nat.zero_lt_one hp)
    have hHcut' : (H : ℝ) ≤ (p : ℝ) ^ (1 / (6 : ℝ)) := by
      apply hHcut.trans
      exact Real.rpow_le_rpow_of_exponent_le hpR (by linarith only [htheta0.le])
    have hHdelta : (H : ℝ) ^ delta ≤ (p : ℝ) ^ (delta / 6) := by
      calc
        _ ≤ ((p : ℝ) ^ (1 / (6 : ℝ))) ^ delta :=
          Real.rpow_le_rpow (Nat.cast_nonneg H) hHcut' hdelta.le
        _ = (p : ℝ) ^ ((1 / (6 : ℝ)) * delta) := (Real.rpow_mul (Nat.cast_nonneg p) _ _).symm
        _ = (p : ℝ) ^ (delta / 6) := by
          congr 1
          ring
    have hExp : 1 / (42 : ℝ) - theta + delta / 6 ≤ 1 / 42 + eta := by
      linarith only [hbudget, htheta0.le]
    have hprod :
      ((shiftedHeightCutoff p theta 42 : ℝ) * H) * (maxDivisorCount H : ℝ) ≤
        ((shiftedHeightCutoff p theta 42 : ℝ) * H) * (C * (H : ℝ) ^ delta) :=
      mul_le_mul_of_nonneg_left (hdiv H) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    have hJP :
      (shiftedHeightCutoff p theta 42 : ℝ) * (H : ℝ) ^ delta ≤
        (p : ℝ) ^ (1 / (42 : ℝ) - theta + delta / 6) := by
      calc
        _ ≤ (p : ℝ) ^ (1 / (42 : ℝ) - theta) * (p : ℝ) ^ (delta / 6) :=
          mul_le_mul hcut42 hHdelta (Real.rpow_nonneg (Nat.cast_nonneg H) delta)
            (Real.rpow_nonneg (Nat.cast_nonneg p) _)
        _ = (p : ℝ) ^ (1 / (42 : ℝ) - theta + delta / 6) := by rw [← Real.rpow_add hp0]
    calc
      _ = ((shiftedHeightCutoff p theta 42 : ℝ) * H) * (maxDivisorCount H : ℝ) := by
        simp only [Nat.cast_mul]
      _ ≤ ((shiftedHeightCutoff p theta 42 : ℝ) * H) * (C * (H : ℝ) ^ delta) := hprod
      _ = C * H * ((shiftedHeightCutoff p theta 42 : ℝ) * (H : ℝ) ^ delta) := by ring
      _ ≤ C * H * (p : ℝ) ^ (1 / (42 : ℝ) - theta + delta / 6) :=
        mul_le_mul_of_nonneg_left hJP (mul_nonneg hC.le (Nat.cast_nonneg H))
      _ ≤ C * H * (p : ℝ) ^ (1 / 42 + eta) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hpR hExp)
          (mul_nonneg hC.le (Nat.cast_nonneg H))

/-- A single constant bounds the weighted sum over all 36 shifted height layers,
uniformly for every prime p and every `H<p`. Each degree-specific ratio estimate
has a uniform constant; sum those constants and use the exponent comparison
`1/j≤1/6` to obtain the common exponent `1/42+eta`. -/
theorem exists_global_shiftedHeightLayers_weighted_sum_bound {theta delta eta : ℝ}
    (hdelta : 0 < delta) (htheta0 : 0 < theta) (htheta : theta < 1 / 42)
    (hbudget : theta + delta / 6 ≤ eta) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ (p H : ℕ) [Fact p.Prime],
          1 < p →
            H < p →
            ∑ j ∈ Finset.Icc 6 41,
                ((heightRestrictedRatioSet p H (shiftedHeightCutoff p theta j)).card : ℝ) *
                  (H / (shiftedHeightCutoff p theta (j + 1) + 1) : ℕ) ≤
              C * H * (p : ℝ) ^ (1 / 42 + eta) := by
  have hUniform :
    ∀ (j : ℕ),
      j ∈ Finset.Icc 6 41 →
        ∃ Cj : ℝ,
          0 < Cj ∧
            ∀ (p' H' T : ℕ) [Fact p'.Prime],
              H' < p' →
                0 < T →
                T ^ (2 * j) < p' ^ 2 →
                ((heightRestrictedRatioSet p' H' T).card : ℝ) ≤
                  Cj * (T : ℝ) ^ delta * (p' : ℝ) ^ (1 / (j : ℝ)) := by
    intro j hj
    have hjpos : 0 < j := Nat.lt_of_lt_of_le (by decide : 0 < 6) (Finset.mem_Icc.mp hj).1
    exact exists_uniform_height_ratio_small_power_bound hjpos hdelta
  let layerConst : ℕ → ℝ := fun j =>
    if hj : j ∈ Finset.Icc 6 41 then Classical.choose (hUniform j hj) else 1
  have hspec :
    ∀ (p H : ℕ) [Fact p.Prime],
      1 < p →
        H < p →
        ∀ j : ℕ,
          j ∈ Finset.Icc 6 41 →
            0 < layerConst j ∧
              ((heightRestrictedRatioSet p H (shiftedHeightCutoff p theta j)).card : ℝ) ≤
                layerConst j * (shiftedHeightCutoff p theta j : ℝ) ^ delta *
                  (p : ℝ) ^ (1 / (j : ℝ)) := by
    intro p H hpPrime hp hHp j hj
    have hj' := Finset.mem_Icc.mp hj
    have hjpos : 0 < j := Nat.lt_of_lt_of_le (by decide : 0 < 6) hj'.1
    have hjCast : (j : ℝ) ≤ 41 := Nat.cast_le.mpr hj'.2
    have hinv : (1 : ℝ) / 41 ≤ 1 / (j : ℝ) :=
      one_div_le_one_div_of_le (Nat.cast_pos.mpr hjpos) hjCast
    have hsmall : (1 : ℝ) / 42 < 1 / 41 := by norm_num only
    have htheta_j : theta < 1 / (j : ℝ) := lt_trans htheta (hsmall.trans_le hinv)
    have hU := Classical.choose_spec (hUniform j hj)
    have hcutpos := shiftedHeightCutoff_pos hp htheta_j
    have hmod := shiftedHeightCutoff_modulus hp hjpos htheta0
    have hconst : layerConst j = Classical.choose (hUniform j hj) := by
      dsimp only [layerConst]
      exact dite_eq_left hj
    rw [hconst]
    exact ⟨hU.1, hU.2 p H (shiftedHeightCutoff p theta j) hHp hcutpos hmod⟩
  let K : ℝ := ∑ j ∈ Finset.Icc 6 41, layerConst j
  have hpositive : ∀ j, j ∈ Finset.Icc 6 41 → 0 < layerConst j := by
    intro j hj
    have hconst : layerConst j = Classical.choose (hUniform j hj) := by
      dsimp only [layerConst]
      exact dite_eq_left hj
    rw [hconst]
    exact (Classical.choose_spec (hUniform j hj)).1
  have hKnonneg : 0 ≤ K := Finset.sum_nonneg fun j hj ↦ (hpositive j hj).le
  have hKle : K ≤ K + 1 := le_add_of_nonneg_right (by norm_num only : (0 : ℝ) ≤ 1)
  have hBnonneg : ∀ (p H : ℕ), 0 ≤ (H : ℝ) * (p : ℝ) ^ (1 / 42 + eta) := by
    intro p H
    exact mul_nonneg (Nat.cast_nonneg H) (Real.rpow_nonneg (Nat.cast_nonneg p) _)
  refine ⟨K + 1, add_pos_of_nonneg_of_pos hKnonneg (by norm_num only : (0 : ℝ) < 1), ?_⟩
  intro p H hpPrime hp hHp
  have hspec' :
    ∀ j,
      j ∈ Finset.Icc 6 41 →
        0 < layerConst j ∧
          ((heightRestrictedRatioSet p H (shiftedHeightCutoff p theta j)).card : ℝ) ≤
            layerConst j * (shiftedHeightCutoff p theta j : ℝ) ^ delta * (p : ℝ) ^ (1 / (j : ℝ)) :=
    hspec p H hp hHp
  have hsum :=
    shiftedHeightLayers_weighted_sum_le hdelta.le htheta0 hbudget layerConst
      (fun j hj ↦ (hspec' j hj).1.le) (fun j hj ↦ (hspec' j hj).2)
  have hBnonneg' := hBnonneg p H
  calc
    _ ≤ K * H * (p : ℝ) ^ (1 / 42 + eta) := by simpa only [K] using hsum
    _ ≤ (K + 1) * H * (p : ℝ) ^ (1 / 42 + eta) := by
      calc
        _ = K * ((H : ℝ) * (p : ℝ) ^ (1 / 42 + eta)) := by ring
        _ ≤ (K + 1) * ((H : ℝ) * (p : ℝ) ^ (1 / 42 + eta)) :=
          mul_le_mul_of_nonneg_right hKle hBnonneg'
        _ = (K + 1) * H * (p : ℝ) ^ (1 / 42 + eta) := by ring

/-- The fixed exponents `a=4200`, `b=7734`, `g=101` satisfy the height-layer
counting and energy exponent constraints. Their scale ratio is strictly greater
than `116/63`, the real count exponent is `1/42+1/4200`, and
`theta=1/8400`, `delta=1/1400` meet the small-height loss budget. -/
theorem height_layer_parameters_4200 :
    (11 * 4200 + 2 * 101 < 6 * 7734) ∧
      7734 ≤ 2 * 4200 ∧
      (116 : ℝ) / 63 < 7734 / 4200 ∧
      (101 : ℝ) / 4200 = 1 / 42 + 1 / 4200 ∧
      (1 : ℝ) / 8400 + (1 / 1400) / 6 ≤ 1 / 4200 ∧ (1 : ℝ) / 8400 < 1 / 42 := by
  refine
    ⟨by norm_num only, by norm_num only, by norm_num only, by norm_num only, by norm_num only, by
      norm_num only⟩

/-- Inputs: the analytic hypotheses for the shifted height layers, a rational identity
`g/a = 1/42+eta`, and the scale/height inequalities. Claim: a natural coefficient `D`
exists such that the layer count gives the powered count bound, and whenever its explicit
large-prime inequality holds, the Heilbronn energy budget follows. Proof: obtain the real
uniform count estimate, rewrite its exponent as `g/a`, round its constant to a natural
coefficient, and invoke `height_layer_count_energy_budget`. Role: join the proved layer
estimate to the energy method without concealing the remaining coefficient absorption. -/
theorem exists_height_layer_count_energy_budget_of_rpow_bound {p H k a b g : ℕ} [Fact p.Prime]
    {theta delta eta : ℝ} (hodd : Odd p) (hHp : H < p) (htop : H ≤ shiftedHeightCutoff p theta 6)
    (hdelta : 0 < delta) (htheta0 : 0 < theta) (htheta : theta < 1 / 42)
    (hbudget : theta + delta / 6 ≤ eta) (ha : 0 < a) (hratio : (g : ℝ) / a = 1 / 42 + eta)
    (hb : b ≤ 2 * a) (hslack : 11 * a + 2 * g < 6 * b) (hcut : p ^ b ≤ k ^ a)
    (hheight : H ^ a ≤ p ^ (2 * a - b)) :
    ∃ D : ℕ,
      boundedCongruenceCount p H ^ a ≤ D ^ a * H ^ a * p ^ g ∧
        (18874370 ^ a * D ^ (2 * a) < p ^ (6 * b - 11 * a - 2 * g) →
          p * heilbronnEnergy p * boundedCongruenceCount p H < k ^ 2) := by
  obtain ⟨C, hC, hcount⟩ :=
    exists_uniform_boundedCongruenceCount_rpow_bound hodd hHp htop hdelta htheta0 htheta hbudget
  have hcount' : (boundedCongruenceCount p H : ℝ) ≤ C * H * (p : ℝ) ^ ((g : ℝ) / a) := by
    rw [hratio]
    exact hcount
  obtain ⟨D, hpowered⟩ := natural_count_power_le_rational_rpow_bound hcount' ha
  refine ⟨D, hpowered, ?_⟩
  intro hlarge
  exact height_layer_count_energy_budget hodd ha hb hslack hcut hheight hpowered hlarge

/-- For fixed positive layer parameters, one positive constant bounds the complete
signed congruence count for every odd prime and every admissible height. Combine
the global small-height bound with the global finite layer sum, retaining the
quantifier order needed by the eventual energy and witness estimates. -/
theorem exists_global_boundedCongruenceCount_rpow_bound {theta delta eta : ℝ} (hdelta : 0 < delta)
    (htheta0 : 0 < theta) (htheta : theta < 1 / 42) (hbudget : theta + delta / 6 ≤ eta) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ (p H : ℕ) [Fact p.Prime],
          Odd p →
            H < p →
            H ≤ shiftedHeightCutoff p theta 6 →
            (boundedCongruenceCount p H : ℝ) ≤ C * H * (p : ℝ) ^ (1 / 42 + eta) := by
  obtain ⟨Cs, hCs, hs⟩ := exists_global_shiftedHeightSmallTerm_rpow_bound hdelta htheta0 hbudget
  obtain ⟨Ct, hCt, ht⟩ :=
    exists_global_shiftedHeightLayers_weighted_sum_bound hdelta htheta0 htheta hbudget
  refine ⟨4 * (Cs + Ct), mul_pos (by norm_num only) (add_pos hCs hCt), ?_⟩
  intro p H hpPrime hodd hHp htop
  have hp := (Fact.out : Nat.Prime p).one_lt
  have hc := Nat.cast_le (α := ℝ).mpr (boundedCongruenceCount_le_shiftedHeightLayers hodd hHp htop)
  have hc' :
    (boundedCongruenceCount p H : ℝ) ≤
      4 *
        (((shiftedHeightCutoff p theta 42 * H * maxDivisorCount H : ℕ) : ℝ) +
          ∑ j ∈ Finset.Icc 6 41,
            ((heightRestrictedRatioSet p H (shiftedHeightCutoff p theta j)).card : ℝ) *
              (H / (shiftedHeightCutoff p theta (j + 1) + 1) : ℕ)) := by
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_sum] using hc
  have hadd := add_le_add (hs p H hp htop) (ht p H hp hHp)
  calc
    _ ≤ _ := hc'
    _ ≤ 4 * (Cs * H * (p : ℝ) ^ (1 / 42 + eta) + Ct * H * (p : ℝ) ^ (1 / 42 + eta)) :=
      mul_le_mul_of_nonneg_left hadd (by norm_num only)
    _ = 4 * (Cs + Ct) * H * (p : ℝ) ^ (1 / 42 + eta) := by ring

/-- Fixed layer parameters and a rational count exponent admit a single natural
coefficient for all admissible primes and heights. Round the global real constant
up once, then raise the estimate to the positive denominator power. This is the
uniform input required to absorb that coefficient into a large-prime threshold. -/
theorem exists_global_height_layer_count_power_bound {theta delta eta : ℝ} {a g : ℕ}
    (hdelta : 0 < delta) (htheta0 : 0 < theta) (htheta : theta < 1 / 42)
    (hbudget : theta + delta / 6 ≤ eta) (ha : 0 < a) (hratio : (g : ℝ) / a = 1 / 42 + eta) :
    ∃ D : ℕ,
      ∀ (p H : ℕ) [Fact p.Prime],
        Odd p →
          H < p →
          H ≤ shiftedHeightCutoff p theta 6 →
          boundedCongruenceCount p H ^ a ≤ D ^ a * H ^ a * p ^ g := by
  obtain ⟨C, hC, hc⟩ :=
    exists_global_boundedCongruenceCount_rpow_bound hdelta htheta0 htheta hbudget
  let D : ℕ := Nat.ceil C
  refine ⟨D, ?_⟩
  intro p H hp hodd hHp htop
  have hfactor : 0 ≤ (H : ℝ) * (p : ℝ) ^ ((g : ℝ) / a) :=
    mul_nonneg (Nat.cast_nonneg H) (Real.rpow_nonneg (Nat.cast_nonneg p) _)
  have hcount : (boundedCongruenceCount p H : ℝ) ≤ (D : ℝ) * H * (p : ℝ) ^ ((g : ℝ) / a) := by
    have hh := hc p H hodd hHp htop
    rw [← hratio] at hh
    have hCD : C ≤ (D : ℝ) := Nat.le_ceil C
    have hmul := mul_le_mul_of_nonneg_right hCD hfactor
    have hmul' : C * H * (p : ℝ) ^ ((g : ℝ) / a) ≤ (D : ℝ) * H * (p : ℝ) ^ ((g : ℝ) / a) := by
      simpa only [mul_assoc] using hmul
    exact hh.trans hmul'
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (boundedCongruenceCount p H)) hcount a
  have hpid : ((p : ℝ) ^ ((g : ℝ) / a)) ^ a = (p : ℝ) ^ g := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg p) ((g : ℝ) / a) a,
      div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (ne_of_gt ha)), Real.rpow_natCast]
  rw [mul_pow, mul_pow, hpid] at hpow
  apply Nat.cast_le (α := ℝ).mp
  simpa only [Nat.cast_mul, Nat.cast_pow] using hpow

/-- Fixed admissible exponents admit a threshold uniform in the prime, height,
and scale. Combine the globally uniform powered count bound with coefficient
absorption and the energy comparison. No new congruence-count hypothesis is used. -/
theorem exists_global_height_layer_energy_budget {theta delta eta : ℝ} {a b g : ℕ}
    (hdelta : 0 < delta) (htheta0 : 0 < theta) (htheta : theta < 1 / 42)
    (hbudget : theta + delta / 6 ≤ eta) (ha : 0 < a) (hratio : (g : ℝ) / a = 1 / 42 + eta)
    (hb : b ≤ 2 * a) (hslack : 11 * a + 2 * g < 6 * b) :
    ∃ P : ℕ,
      ∀ (p H k : ℕ) [Fact p.Prime],
        Odd p →
          P ≤ p →
          H < p →
          H ≤ shiftedHeightCutoff p theta 6 →
          p ^ b ≤ k ^ a →
          H ^ a ≤ p ^ (2 * a - b) → p * heilbronnEnergy p * boundedCongruenceCount p H < k ^ 2 := by
  obtain ⟨D, hD⟩ :=
    exists_global_height_layer_count_power_bound hdelta htheta0 htheta hbudget ha hratio
  obtain ⟨P, hP⟩ := exists_height_layer_energy_threshold (D := D) hslack
  refine ⟨P, ?_⟩
  intro p H k hp hodd hlarge hHp htop hcut hheight
  exact
    height_layer_count_energy_budget hodd ha hb hslack hcut hheight (hD p H hodd hHp htop)
      (hP p hlarge)

/-- A natural-power height estimate places the height below the shifted degree-six
cutoff whenever its rational exponent is at most the cutoff exponent. Take the
positive natural root and use monotonicity in the prime exponent. -/
theorem height_le_shifted_cutoff_of_power {p H a d : ℕ} {theta : ℝ} (ha : 0 < a) (hp : 1 ≤ p)
    (hexp : (d : ℝ) / a ≤ 1 / 6 - theta) (hheight : H ^ a ≤ p ^ d) :
    H ≤ shiftedHeightCutoff p theta 6 := by
  have hh : (H : ℝ) ^ a ≤ (p : ℝ) ^ d := by
    simpa only [Nat.cast_pow] using (Nat.cast_le (α := ℝ).mpr hheight)
  have hroot :=
    Real.rpow_le_rpow (pow_nonneg (Nat.cast_nonneg H) a) hh (inv_nonneg.mpr (Nat.cast_nonneg a))
  rw [Real.pow_rpow_inv_natCast (Nat.cast_nonneg H) (ne_of_gt ha), ← Real.rpow_natCast, ←
    Real.rpow_mul (Nat.cast_nonneg p)] at hroot
  have hroot' : (H : ℝ) ≤ (p : ℝ) ^ ((d : ℝ) / a) := by simpa only [div_eq_mul_inv] using hroot
  apply Nat.le_floor
  exact hroot'.trans (Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hp) hexp)

end PseudoPrime.NumberTheory.Heilbronn
