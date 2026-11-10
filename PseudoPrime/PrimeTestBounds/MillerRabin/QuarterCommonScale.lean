/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCommonLow
import PseudoPrime.PrimeTestBounds.MillerRabin.FromLLS

/-! # Common-scale quarter bounds for small inputs and local subgroups -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- If `n ≤ J³`, `J ≤ r²`, and `r ≥ 150`, the squared logarithm of `n` is
at most `r²`. A logarithm bound anchored at 150 gives the required margin. -/
private theorem quarter_variable_small_log_sq {n J : ℕ} (hn : 1 < n) (hsmall : n ≤ J ^ 3) {r : ℝ}
    (hr : 150 ≤ r) (hJr : (J : ℝ) ≤ r ^ 2) : Real.log n ^ 2 ≤ r ^ 2 := by
  have hcert :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 150 8 32 5 (51 / 10) = true from by
          decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hcert
  have hlogr : Real.log r ≤ (17 / 500 : ℝ) * r := by
    apply Analysis.log_le_mul_of_anchor (a := 150) (by norm_num only) hr
    · nlinarith only [hcert]
    · norm_num only
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  have hnR : (n : ℝ) ≤ (r ^ 2) ^ 3 := by
    calc
      (n : ℝ) ≤ (J : ℝ) ^ 3 := by exact_mod_cast hsmall
      _ ≤ (r ^ 2) ^ 3 := pow_le_pow_left₀ hJ0 hJr 3
  have hl := Real.log_le_log (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn)) hnR
  rw [Real.log_pow, Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hn0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (Nat.le_of_lt hn))
  have hb : Real.log n ≤ (51 / 250 : ℝ) * r := by linarith only [hl, hlogr]
  have hs := mul_self_le_mul_self hn0 hb
  nlinarith only [hs, sq_nonneg r]

/-- Under GRH, a nonuniform odd composite admits a rejecting prime at most
`r²` whenever `r ≥ 150`, `log n ≤ 2r`, and a subgroup of the Fermat subgroup
has index at most `J ≤ r²`. A small input is covered by the global log-square bound;
otherwise the finite-index classification gives the variable-radius witness. -/
theorem quarter_variable_index_le {n J : ℕ} [NeZero n] (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (H : Subgroup (ZMod n)ˣ) (hH : H ≤ PrimeTest.fermatSubgroup n) (hJ : 1 ≤ J) (hi : H.index ≤ J)
    (hu : ¬UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {r : ℝ} (hr : 150 ≤ r) (hJr : (J : ℝ) ≤ r ^ 2) (hscale : Real.log n ≤ 2 * r) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases hlarge : J ^ 3 ≤ n
  · exact quarter_variable_small_index hn ho hc H hH hJ hi hlarge hu hGRH hr hJr hscale
  · obtain ⟨p, hp, hb, hpow, hrest⟩ := exists_prime_millerRabin_witness_le_log_sq hGRH hn ho hc
    have hf : ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) :=
      PrimeTest.not_strongMillerRabinPass_iff.mpr ⟨hpow, hrest⟩
    exact
      ⟨p, hp,
        hb.trans (quarter_variable_small_log_sq hn (Nat.le_of_lt (Nat.lt_of_not_ge hlarge)) hr hJr),
        hf⟩

/-- The small-index half of the nonuniform half-line theorem, specialized to
the Fermat subgroup and `J = floor r²`. Under GRH and `r ≥ 150`, every
nonuniform odd composite of logarithm at most `2r` has a rejecting prime at
most `r²` when the Fermat index is at most `J`. -/
theorem quarter_variable_floor_index {n : ℕ} [NeZero n] (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hu : ¬UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {r : ℝ} (hr : 150 ≤ r) (hscale : Real.log n ≤ 2 * r)
    (hi : (PrimeTest.fermatSubgroup n).index ≤ ⌊r ^ 2⌋₊) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hr2 : (1 : ℝ) ≤ r ^ 2 := by nlinarith only [sq_nonneg (r - 150), hr]
  have hJ : 1 ≤ ⌊r ^ 2⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using hr2)
  have hjr : (⌊r ^ 2⌋₊ : ℝ) ≤ r ^ 2 := Nat.floor_le (sq_nonneg r)
  exact
    quarter_variable_index_le hn ho hc (PrimeTest.fermatSubgroup n) le_rfl hJ hi hu hGRH hr hjr
      hscale

/-- For `T ≥ 300`, the nonuniform small-index branch supplies a rejecting
prime at most `T² / 4` whenever `log n ≤ T` and the Fermat index is at most
`floor (T / 2)²`. The variable-radius theorem is applied at `r = T / 2`. -/
theorem quarter_common_floor_index {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hu : ¬UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {T : ℝ} (hT : 300 ≤ T) (hscale : Real.log n ≤ T)
    (hi : (PrimeTest.fermatSubgroup n).index ≤ ⌊(T / 2) ^ 2⌋₊) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (1 / 4 : ℝ) * T ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  obtain ⟨p, hp, hb, hf⟩ :=
    quarter_variable_floor_index hn ho hc hu hGRH (r := T / 2) (by linarith only [hT])
      (by linarith only [hscale]) hi
  refine ⟨p, hp, ?_, hf⟩
  nlinarith only [hb]

end PseudoPrime.PrimeTestBounds.MillerRabin
