/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.EightDegreeRatioBounds
public import PseudoPrime.NumberTheory.Heilbronn.HeightWeightExchange
public import PseudoPrime.NumberTheory.Heilbronn.HeightLayerEnergyBridge

/-! # Full congruence counts with finite-fiber loss 1/84 -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- For every eta>0 a single constant bounds the full signed count by
CHp^(1/84+eta), uniformly at H≤p^(5/28) and H<p for odd p. Apply exact
height-weight exchange and absorb the harmonic factor using half the slack.
No count estimate remains as an external assumption. -/
theorem exists_uniform_finite_fiber_congruence_bound {eta : ℝ} (heta : 0 < eta) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ (p H : ℕ) [Fact p.Prime],
          Odd p →
            H < p →
            (H : ℝ) ≤ (p : ℝ) ^ (5 / 28 : ℝ) →
            (boundedCongruenceCount p H : ℝ) ≤ C * H * (p : ℝ) ^ (1 / 84 + eta) := by
  have hdelta : 0 < eta / 2 := half_pos heta
  obtain ⟨K, hK, hR⟩ := exists_uniform_finite_fiber_ratio_bound hdelta
  let C : ℝ := 4 * K * (1 + 1 / (eta / 2))
  have hfac : 0 < 1 + 1 / (eta / 2) :=
    add_pos (by norm_num only) (div_pos (by norm_num only) hdelta)
  refine ⟨C, mul_pos (mul_pos (by norm_num only) hK) hfac, ?_⟩
  intro p H hp hodd hHp htop
  have hp1 : (1 : ℝ) ≤ p := Nat.one_le_cast.mpr (Fact.out : p.Prime).pos
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have hcount :=
    boundedCongruenceCount_le_of_uniform_height_ratios hodd hHp hK.le
      (fun T hT ↦ hR p H T hHp ((Nat.cast_le.mpr hT).trans htop))
  have hpow := Real.rpow_le_rpow (Nat.cast_nonneg H) (Nat.cast_le.mpr hHp.le) hdelta.le
  have hlog :=
    (Real.log_natCast_le_rpow_div H hdelta).trans (div_le_div_of_nonneg_right hpow hdelta.le)
  have hone : (1 : ℝ) ≤ (p : ℝ) ^ (eta / 2) := by
    have h := Real.rpow_le_rpow_of_exponent_le hp1 hdelta.le
    simpa only [Real.rpow_zero] using h
  have hlog' : 1 + Real.log H ≤ (1 + 1 / (eta / 2)) * (p : ℝ) ^ (eta / 2) := by
    have hh := add_le_add hone hlog
    convert hh using 1
    ring
  have hm :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlog'
        (mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4) hK.le) (Nat.cast_nonneg H)))
      (Real.rpow_nonneg hp0.le (1 / 84 + eta / 2))
  apply hcount.trans
  convert hm using 1
  dsimp only [C]
  rw [show (1 / 84 + eta : ℝ) = eta / 2 + (1 / 84 + eta / 2) by ring, Real.rpow_add hp0]
  ring

/-- For a fixed positive denominator a and exponent g/a=1/84+eta,
one natural coefficient controls the a-th power of all admissible counts.
Round the common real coefficient once and raise to a. This fixes constants
before prime and height vary in the energy comparison. -/
theorem exists_finite_fiber_count_power_bound {eta : ℝ} {a g : ℕ} (heta : 0 < eta) (ha : 0 < a)
    (hratio : (g : ℝ) / a = 1 / 84 + eta) :
    ∃ D : ℕ,
      ∀ (p H : ℕ) [Fact p.Prime],
        Odd p →
          H < p →
          (H : ℝ) ≤ (p : ℝ) ^ (5 / 28 : ℝ) →
          boundedCongruenceCount p H ^ a ≤ D ^ a * H ^ a * p ^ g := by
  obtain ⟨C, hC, hc⟩ := exists_uniform_finite_fiber_congruence_bound heta
  let D : ℕ := Nat.ceil C
  refine ⟨D, ?_⟩
  intro p H hp hodd hHp htop
  have hfactor : 0 ≤ (H : ℝ) * (p : ℝ) ^ ((g : ℝ) / a) :=
    mul_nonneg (Nat.cast_nonneg H) (Real.rpow_nonneg (Nat.cast_nonneg p) _)
  have hcount : (boundedCongruenceCount p H : ℝ) ≤ (D : ℝ) * H * (p : ℝ) ^ ((g : ℝ) / a) := by
    have hh := hc p H hodd hHp htop
    rw [← hratio] at hh
    have hmul := mul_le_mul_of_nonneg_right (Nat.le_ceil C) hfactor
    exact hh.trans (by simpa only [mul_assoc, D] using hmul)
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (boundedCongruenceCount p H)) hcount a
  have hpid : ((p : ℝ) ^ ((g : ℝ) / a)) ^ a = (p : ℝ) ^ g := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg p),
      div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (ne_of_gt ha)), Real.rpow_natCast]
  rw [mul_pow, mul_pow, hpid] at hpow
  apply Nat.cast_le (α := ℝ).mp
  simpa only [Nat.cast_mul, Nat.cast_pow] using hpow

/-- Fixed rational exponents with 11a+2g<6b admit a uniform energy budget
beyond one prime threshold. Use the finite-fiber count, the proved Heilbronn
energy square bound, and coefficient absorption. This is the interface for
rational cutoffs and subsequent Fermat quotient and MR witness bounds. -/
theorem exists_finite_fiber_energy_budget {eta : ℝ} {a b g : ℕ} (heta : 0 < eta) (ha : 0 < a)
    (hratio : (g : ℝ) / a = 1 / 84 + eta) (hb : b ≤ 2 * a) (hslack : 11 * a + 2 * g < 6 * b) :
    ∃ P : ℕ,
      ∀ (p H k : ℕ) [Fact p.Prime],
        Odd p →
          P ≤ p →
          H < p →
          (H : ℝ) ≤ (p : ℝ) ^ (5 / 28 : ℝ) →
          p ^ b ≤ k ^ a →
          H ^ a ≤ p ^ (2 * a - b) → p * heilbronnEnergy p * boundedCongruenceCount p H < k ^ 2 := by
  obtain ⟨D, hD⟩ := exists_finite_fiber_count_power_bound heta ha hratio
  obtain ⟨P, hP⟩ := exists_height_layer_energy_threshold (D := D) hslack
  refine ⟨P, ?_⟩
  intro p H k hp hodd hlarge hHp htop hcut hheight
  exact
    height_layer_count_energy_budget hodd ha hb hslack hcut hheight (hD p H hodd hHp htop)
      (hP p hlarge)

end PseudoPrime.NumberTheory.Heilbronn
