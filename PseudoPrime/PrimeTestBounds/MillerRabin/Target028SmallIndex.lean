/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030High

/-! # Small-index local witnesses for the coefficient 0.28 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A rational logarithm certificate bounds the logarithm of the finite-index
threshold used in the 0.28 middle-range argument. -/
theorem target028_log_index_bound : Real.log (50000000 : ℝ) ≤ 2216 / 125 := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 50000000 26 32 17 (2216 / 125) = true from by
          decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
  exact h

/-- A divisor whose square is at most 50000000 times the input has the
logarithmic size required by the radius-48 local witness. -/
theorem target028_local_log {n q : ℕ} (hn : 0 < n) (hq : 0 < q) (hsize : q ^ 2 ≤ 50000000 * n) :
    Real.log q ≤ (Real.log n + 2216 / 125) / 2 := by
  have hR : (q : ℝ) ^ 2 ≤ (50000000 : ℝ) * n := by exact_mod_cast hsize
  have hl := Real.log_le_log (pow_pos (Nat.cast_pos.mpr hq) 2) hR
  rw [Real.log_pow, Real.log_mul (by norm_num only) (Nat.cast_pos.mpr hn).ne'] at hl
  norm_num only [Nat.cast_ofNat] at hl
  linarith only [hl, target028_log_index_bound]

/-- Under GRH, a proper local subgroup at a divisor bounded by the finite-index
threshold supplies a 0.28 witness from logarithmic scale 106. The radius-48
correction fits inside the 52915/100000 linear cutoff. -/
theorem exists_prime_reject_028_local_index {n q : ℕ} [NeZero q] (hn : 1 < n) (ho : Odd n)
    (hq : 0 < q) (hqn : q ∣ n) (hsize : q ^ 2 ≤ 50000000 * n) (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hpass :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
          ∃ t : (ZMod q)ˣ, t ∈ H ∧ (t : ZMod q) = (a : ZMod q))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (106 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hm : ((48 : ℚ), (579107 / 100000 : ℚ), 6) ∈ localEvenAnchors := by decide +kernel
  have hs := target028_local_log (Nat.zero_lt_of_lt hn) hq hsize
  obtain ⟨p, hp, hb, hf⟩ := exists_prime_reject_of_local_anchor hn ho hqn H hH hpass hGRH hm hs
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hb
  have hmax :
    max (48 : ℝ) ((Real.log n + 2216 / 125) / 2 - 579107 / 100000) ≤
      (52915 / 100000 : ℝ) * Real.log n := by
    apply max_le <;> linarith only [hL]
  have hnonneg : 0 ≤ max (48 : ℝ) ((Real.log n + 2216 / 125) / 2 - 579107 / 100000) :=
    le_trans (by norm_num only) (le_max_left _ _)
  have hsquare := mul_self_le_mul_self hnonneg hmax
  have hfinal :
    (max (48 : ℝ) ((Real.log n + 2216 / 125) / 2 - 579107 / 100000)) ^ 2 ≤
      (7 / 25 : ℝ) * (Real.log n) ^ 2 := by
    nlinarith only [hsquare, sq_nonneg (Real.log n)]
  exact ⟨p, hp, hb.trans hfinal, hf⟩

/-- Under GRH, the finite-index classification gives a 0.28 witness for every
nonuniform odd composite of logarithmic scale at least 106 whose Fermat
subgroup index is at most 50000000. -/
theorem exists_prime_reject_028_small_index {n : ℕ} [NeZero n] (hn : 1 < n) (ho : Odd n)
    (hc : ¬n.Prime) (H : Subgroup (ZMod n)ˣ) (hH : H ≤ PrimeTest.fermatSubgroup n)
    (hi : H.index ≤ 50000000) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (106 : ℝ) ≤ Real.log n) (hU : ¬UniformKorseltTriple n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hJ : (1 : ℕ) ≤ 50000000 := by norm_num only
  have hJ3 : (50000000 : ℕ) ^ 3 ≤ n :=
    (show (50000000 : ℕ) ^ 3 ≤ 10 ^ 27 by norm_num only).trans
      (ten_pow_27_le_of_log100 (by linarith only [hL]))
  rcases localSubgroup_or_uniformKorseltTriple hn ho hc H hH hJ hJ3 hi with hlocal | htriple
  · obtain ⟨q, hq, hqn, hsize, K, hproper, hpass⟩ := hlocal
    let : NeZero q := ⟨Nat.ne_zero_of_lt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
    exact
      exists_prime_reject_028_local_index hn ho (lt_of_lt_of_le (by decide : 0 < 2) hq) hqn hsize K
        hproper hpass hGRH hL
  · exact False.elim (hU htriple)

end PseudoPrime.PrimeTestBounds.MillerRabin
