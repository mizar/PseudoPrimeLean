/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.LogTenThirteenthEnergyBound
public import PseudoPrime.NumberTheory.Heilbronn.TruncatedWeightEnergyAlternatives
public import PseudoPrime.Analysis.LogarithmicPowerAbsorption

/-! # Absorb the thirteenth-energy logarithmic loss before counting -/

public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- For fixed natural `a,D` and positive slack `r`, the energy bound with
logarithmic exponent two gives a power saving beyond one uniform prime
threshold. Raise the proved estimate and absorb its logarithmic factor. -/
theorem thirteenth_energy_power_lt_of_log_square_slack {p : ℕ} [Fact p.Prime] (hodd : Odd p)
    (a D r : ℕ)
    (hlarge : (2 ^ 176 : ℝ) ^ a * (D : ℝ) ^ (13 * a) * (1 + Real.log p) ^ (2 * a) < (p : ℝ) ^ r) :
    (heilbronnEnergy p * D) ^ (13 * a) < p ^ (32 * a + r) := by
  have he :=
    pow_le_pow_left₀ (pow_nonneg (Nat.cast_nonneg (heilbronnEnergy p)) 13)
      (heilbronnEnergy_thirteenth_le_log_square hodd) a
  have hb :
    ((heilbronnEnergy p : ℝ) * D) ^ (13 * a) ≤
      ((2 ^ 176 : ℝ) ^ a * (D : ℝ) ^ (13 * a) * (1 + Real.log p) ^ (2 * a)) *
        (p : ℝ) ^ (32 * a) := by
    convert mul_le_mul_of_nonneg_right he (pow_nonneg (Nat.cast_nonneg D) (13 * a)) using 1 <;>
      simp only [mul_pow, ← pow_mul]
    ring
  have hs :=
    mul_lt_mul_of_pos_right hlarge
      (pow_pos (Nat.cast_pos.mpr (Fact.out : p.Prime).pos : (0 : ℝ) < p) (32 * a))
  have hid : (p : ℝ) ^ r * (p : ℝ) ^ (32 * a) = (p : ℝ) ^ (32 * a + r) := by
    rw [← pow_add, Nat.add_comm]
  exact_mod_cast hb.trans_lt (hs.trans_eq hid)

/-- Inputs: an odd prime `p`, natural parameters `a,D`, a squared coefficient
bound below `p`, and a logarithmic factor whose fourth-power exponent is at
most `p`. Claim: the thirteenth-power Heilbronn energy bound has one full
power of saving beyond `p^(32a)`. Proof: multiply the squared coefficient
and logarithmic inequalities, take the nonnegative square root by comparing
squares, then use the logarithmic-square energy estimate. Role: handles the
unit slack case in finite-fiber counting budgets. -/
theorem thirteenth_energy_power_lt_of_square_slack {p : ℕ} [Fact p.Prime] (hodd : Odd p) (a D : ℕ)
    (hcoeff : (((2 ^ 176 : ℝ) ^ a) * (D : ℝ) ^ (13 * a)) ^ 2 < p)
    (hlog : (1 + Real.log p) ^ (4 * a) ≤ p) :
    (heilbronnEnergy p * D) ^ (13 * a) < p ^ (32 * a + 1) := by
  let C : ℝ := (2 ^ 176 : ℝ) ^ a * (D : ℝ) ^ (13 * a)
  let X : ℝ := (1 + Real.log p) ^ (2 * a)
  have hp : 0 < (p : ℝ) := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have hXpos : 0 < X := pow_pos (by positivity) _
  have hCnonneg : 0 ≤ C := by positivity
  have hXsq : X ^ 2 ≤ p := by
    calc
      X ^ 2 = (1 + Real.log p) ^ (4 * a) := by
        dsimp only [X]
        rw [← pow_mul]
        congr 1
        ring
      _ ≤ p := hlog
  have hsq : (C * X) ^ 2 < (p : ℝ) ^ 2 := by
    have hleft := mul_lt_mul_of_pos_right hcoeff (pow_pos hXpos 2)
    have hright := mul_le_mul_of_nonneg_left hXsq hp.le
    calc
      (C * X) ^ 2 = C ^ 2 * X ^ 2 := by ring
      _ < (p : ℝ) * X ^ 2 := by simpa only [C] using hleft
      _ ≤ (p : ℝ) ^ 2 := by simpa only [pow_two] using hright
  have hmargin : C * X < p := by nlinarith only [hsq, hCnonneg, hXpos, hp]
  have hmargin' :
    (2 ^ 176 : ℝ) ^ a * (D : ℝ) ^ (13 * a) * (1 + Real.log p) ^ (2 * a) < (p : ℝ) ^ 1 := by
    simpa only [C, X, pow_one] using hmargin
  exact thirteenth_energy_power_lt_of_log_square_slack hodd a D 1 hmargin'

/-- For fixed natural `a,D` and positive slack `r`, the actual energy times
`D` has power `13a` smaller than `p^(32a+r)` beyond a uniform prime threshold.
Raise the proved energy estimate and absorb its logarithmic factor. This
keeps the coefficient from the finite-fiber count inside the same budget. -/
theorem exists_thirteenth_energy_power_threshold (a D : ℕ) {r : ℕ} (hr : 0 < r) :
    ∃ P : ℕ,
      ∀ p : ℕ,
        [Fact p.Prime] → Odd p → P ≤ p → (heilbronnEnergy p * D) ^ (13 * a) < p ^ (32 * a + r) := by
  let C : ℝ := (2 ^ 176) ^ a * (D : ℝ) ^ (13 * a)
  have hC : 0 ≤ C :=
    mul_nonneg (pow_nonneg (pow_nonneg (by norm_num only : (0 : ℝ) ≤ 2) 176) a)
      (pow_nonneg (Nat.cast_nonneg D) _)
  have h :=
    PseudoPrime.Analysis.eventually_mul_one_add_log_pow_lt_rpow hC (Nat.cast_pos.mpr hr) (10 * a)
  have hn := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually h
  obtain ⟨P, hP⟩ := Filter.eventually_atTop.mp hn
  refine ⟨P, ?_⟩
  intro p hp hodd hlarge
  apply thirteenth_energy_power_lt_of_log_ten_slack hodd a D r
  simpa only [C, Real.rpow_natCast] using hP p hlarge

/-- The logarithmic exponent-two energy estimate gives a uniform threshold
for the same power saving with a smaller logarithmic absorption cost. -/
theorem exists_log_square_energy_power_threshold (a D : ℕ) {r : ℕ} (hr : 0 < r) :
    ∃ P : ℕ,
      ∀ p : ℕ,
        [Fact p.Prime] → Odd p → P ≤ p → (heilbronnEnergy p * D) ^ (13 * a) < p ^ (32 * a + r) := by
  let C : ℝ := (2 ^ 176) ^ a * (D : ℝ) ^ (13 * a)
  have hC : 0 ≤ C :=
    mul_nonneg (pow_nonneg (pow_nonneg (by norm_num only : (0 : ℝ) ≤ 2) 176) a)
      (pow_nonneg (Nat.cast_nonneg D) _)
  have h :=
    PseudoPrime.Analysis.eventually_mul_one_add_log_pow_lt_rpow hC (Nat.cast_pos.mpr hr) (2 * a)
  have hn := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually h
  obtain ⟨P, hP⟩ := Filter.eventually_atTop.mp hn
  refine ⟨P, ?_⟩
  intro p hp hodd hlarge
  apply thirteenth_energy_power_lt_of_log_square_slack hodd a D r
  simpa only [C, Real.rpow_natCast] using hP p hlarge

end PseudoPrime.NumberTheory.Heilbronn
