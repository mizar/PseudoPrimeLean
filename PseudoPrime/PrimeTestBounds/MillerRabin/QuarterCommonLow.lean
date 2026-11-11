/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import PseudoPrime.PrimeTestBounds.MillerRabin.FromLLS
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028SmallIndex
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEvenCorrection

/-! # Common-scale quarter bounds for small inputs and local subgroups -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- An odd composite with logarithm at most 32 has a quarter-square
witness at any common scale at least 68. The global log-square witness is absorbed
by the larger common scale. This handles the small-input branch of the
nonuniform common-scale argument. -/
theorem quarter_common_small {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {T : ℝ} (hT : 68 ≤ T)
    (hU : Real.log n ≤ 32) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (1 / 4 : ℝ) * T ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hb, hpow, hrest⟩ := exists_prime_millerRabin_witness_le_log_sq hGRH hn ho hc
  have hL : (0 : ℝ) ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (Nat.le_of_lt hn))
  have hlog : (Real.log n) ^ 2 ≤ 32 ^ 2 := by nlinarith only [hL, hU]
  have ht : (68 : ℝ) ^ 2 ≤ T ^ 2 := by nlinarith only [hT]
  have hbound : (Real.log n) ^ 2 ≤ (1 / 4 : ℝ) * T ^ 2 := by nlinarith only [hlog, ht]
  have hf : ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) :=
    PrimeTest.not_strongMillerRabinPass_iff.mpr ⟨hpow, hrest⟩
  exact ⟨p, hp, hb.trans hbound, hf⟩

/-- Under GRH, a proper local subgroup whose modulus has logarithm at most
`T / 2 + 65379 / 12500` yields a rejecting prime at most `T² / 4` when
`T ≥ 64`. The radius-32 anchor supplies the witness used in the small-index
branch of the nonuniform argument. -/
theorem quarter_common_local {n q : ℕ} [NeZero q] (hn : 1 < n) (ho : Odd n) (hqn : q ∣ n)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hpass :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
          ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (a : ZMod q))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {T : ℝ} (hT : 64 ≤ T)
    (hq : Real.log q ≤ T / 2 + 65379 / 12500) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (1 / 4 : ℝ) * T ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hm : ((32 : ℚ), (65379 / 12500 : ℚ), 5) ∈ localEvenAnchors := by decide +kernel
  obtain ⟨p, hp, hb, hf⟩ := exists_prime_reject_of_local_anchor hn ho hqn H hH hpass hGRH hm hq
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hb
  have hmax : max (32 : ℝ) (T / 2 + 65379 / 12500 - 65379 / 12500) ≤ T / 2 := by
    apply max_le <;> linarith only [hT]
  have hnonneg : 0 ≤ max (32 : ℝ) (T / 2 + 65379 / 12500 - 65379 / 12500) :=
    le_trans (by norm_num only) (le_max_left _ _)
  have hsquare := mul_self_le_mul_self hnonneg hmax
  have hbound :
    (max (32 : ℝ) (T / 2 + 65379 / 12500 - 65379 / 12500)) ^ 2 ≤ (1 / 4 : ℝ) * T ^ 2 := by
    nlinarith only [hsquare]
  exact ⟨p, hp, hb.trans hbound, hf⟩

/-- The logarithm of the small-index threshold is below twice the radius-32
anchor correction. An exact rational interval certificate establishes the
comparison used to bound the local modulus. -/
theorem log_small_index_le : Real.log (33000 : ℝ) ≤ 65379 / 6250 := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 33000 16 32 10 (65379 / 6250) = true from by
          decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
  exact h

/-- An input at most `33000³` has logarithm at most 32. Monotonicity and the
certified logarithm of 33000 connect the small-input and small-index cases. -/
theorem log_le_small_index_cube {n : ℕ} (hn : 0 < n) (hsmall : n ≤ (33000 : ℕ) ^ 3) :
    Real.log n ≤ 32 := by
  have hnR : (n : ℝ) ≤ (33000 : ℝ) ^ 3 := by exact_mod_cast hsmall
  have hlog := Real.log_le_log (Nat.cast_pos.mpr hn) hnR
  rw [Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  linarith only [hlog, log_small_index_le]

/-- If `q² ≤ 33000 n` and the logarithm of `n` is at most `T`, the local
modulus fits the radius-32 anchor at scale `T`. Logarithmic monotonicity and
the certified threshold estimate give the required bound. -/
theorem quarter_common_local_log {n q : ℕ} (hn : 0 < n) (hq : 0 < q) (hsize : q ^ 2 ≤ 33000 * n)
    {T : ℝ} (hT : Real.log n ≤ T) : Real.log q ≤ T / 2 + 65379 / 12500 := by
  have hR : (q : ℝ) ^ 2 ≤ (33000 : ℝ) * n := by exact_mod_cast hsize
  have hl := Real.log_le_log (pow_pos (Nat.cast_pos.mpr hq) 2) hR
  rw [Real.log_pow, Real.log_mul (by norm_num only) (Nat.cast_pos.mpr hn).ne'] at hl
  norm_num only [Nat.cast_ofNat] at hl
  linarith only [hl, log_small_index_le, hT]

/-- Under GRH, a nonuniform odd composite at least `33000³` whose Fermat
subgroup contains a subgroup of index at most `33000` has a quarter-square
witness at any common scale `T ≥ 64` bounding its logarithm. The finite-index
classification supplies the proper local subgroup and the radius-32 anchor
then gives a rejecting prime. -/
theorem quarter_common_small_index {n : ℕ} [NeZero n] (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (H : Subgroup (ZMod n)ˣ) (hH : H ≤ PrimeTest.fermatSubgroup n) (hi : H.index ≤ 33000)
    (hlarge : (33000 : ℕ) ^ 3 ≤ n) (hu : ¬UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {T : ℝ} (hT : 64 ≤ T)
    (hscale : Real.log n ≤ T) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (1 / 4 : ℝ) * T ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  rcases localSubgroup_or_uniformKorseltTriple hn ho hc H hH (by decide) hlarge hi with hlocal | ht
  · obtain ⟨q, hq, hqn, hsize, K, hproper, hpass⟩ := hlocal
    let : NeZero q := ⟨Nat.ne_zero_of_lt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
    have hqpos : 0 < q := lt_of_lt_of_le (by decide : 0 < 2) hq
    exact
      quarter_common_local hn ho hqn K hproper hpass hGRH hT
        (quarter_common_local_log (Nat.zero_lt_of_lt hn) hqpos hsize hscale)
  · exact False.elim (hu ht)

/-- Under GRH, a nonuniform odd composite whose Fermat subgroup contains a
subgroup of index at most 33000 has a quarter-square witness at any common
scale `T ≥ 68` bounding its logarithm. Below `33000³` the global log-square bound is
absorbed; above it the finite-index local subgroup supplies the witness. -/
theorem quarter_common_index_le {n : ℕ} [NeZero n] (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (H : Subgroup (ZMod n)ˣ) (hH : H ≤ PrimeTest.fermatSubgroup n) (hi : H.index ≤ 33000)
    (hu : ¬UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {T : ℝ} (hT : 68 ≤ T) (hscale : Real.log n ≤ T) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (1 / 4 : ℝ) * T ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases hlarge : (33000 : ℕ) ^ 3 ≤ n
  · exact quarter_common_small_index hn ho hc H hH hi hlarge hu hGRH (by linarith only [hT]) hscale
  · exact
      quarter_common_small hn ho hc hGRH hT
        (log_le_small_index_cube (Nat.zero_lt_of_lt hn) (Nat.le_of_lt (Nat.lt_of_not_ge hlarge)))

end PseudoPrime.PrimeTestBounds.MillerRabin
