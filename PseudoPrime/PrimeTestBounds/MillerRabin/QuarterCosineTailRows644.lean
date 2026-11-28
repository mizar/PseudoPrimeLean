/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosineSeries644
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSlope644
import all PseudoPrime.Analysis.LogTaylorBounds
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosine644

/-! # Certified bounds on the combined cosine Euler tails -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At nonnegative frequency the cosine conductor coefficient is one
quarter of the scalar profile used in the section 122 linear gain. -/
theorem quarter_cosine_conductor_644 (q : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    (Complex.log q * (quarterSymmetricProfile644 (Real.exp s)⁻¹ : ℂ)).re =
      Real.log q * threeShiftG122 s / 4 := by
  have hp := inv_pos.mpr (Real.exp_pos s)
  have h := quarter_symmetric_transform_644 hp
  have hv :
    quarterSymmetricMellin644.transform (Real.exp s)⁻¹ =
      (quarterSymmetricProfile644 (Real.exp s)⁻¹ : ℂ) :=
    symmetric_line_inversion (c := 0) (by norm_num only) (by norm_num only) hp
  dsimp only at h
  rw [hv] at h
  have he := congrArg Complex.re h
  simp only [Complex.ofReal_re, Real.log_inv, Real.log_exp, abs_neg, abs_of_nonneg hs] at he
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg q), ← Complex.ofReal_mul,
    Complex.ofReal_re, he]
  unfold threeShiftG122
  ring_nf

/-- The difference between the level-one and character Euler sums at
the reciprocal pair of positive scales associated with a frequency. -/
noncomputable def quarterPairedEuler644 {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℝ) : ℝ :=
  let x := Real.exp s
  let E := fun y ↦
    quarterSymmetricSum644 (1 : DirichletCharacter ℂ 1) y - quarterSymmetricSum644 χ y
  E x⁻¹ + E x

/-- For three characters that agree with one on primes through `X`,
the paired Euler differences equal the combined trace tail beyond `X`.
This connects the ordinary and reflected Euler series to the row bounds. -/
theorem quarter_paired_euler_tail_644 {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) {X : ℝ}
    (hX : 0 ≤ X) (s : ℝ) (ha : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1)
    (hb : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hc : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) :
    quarterPairedEuler644 a s + quarterPairedEuler644 b s + quarterPairedEuler644 c s =
      quarterCosineTail644 a b c X s := by
  have hp := Real.exp_pos s
  have hm := inv_pos.mpr hp
  have h₁ := quarter_trace_tail_eq_644 a b c X hm
  have h₂ := quarter_trace_tail_eq_644 a b c X hp
  dsimp only at h₁ h₂
  unfold quarterPairedEuler644 quarterCosineTail644
  dsimp only
  rw [quarter_profile_tail_644 a hX hm ha, quarter_profile_tail_644 a hX hp ha,
    quarter_profile_tail_644 b hX hm hb, quarter_profile_tail_644 b hX hp hb,
    quarter_profile_tail_644 c hX hm hc, quarter_profile_tail_644 c hX hp hc]
  linarith only [h₁, h₂]

/-- Under RH, the signed combination of the seven cosine Euler tails
is bounded below on each section 122 radius row. The trace lower bound
and the character norm bounds allow the certified scalar estimate. -/
theorem quarter_cosine_tail_rows_644 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s)
    (hRH : RiemannHypothesis) {r : ℝ} (hr : 316 ≤ r)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re) :
    let S := quarterCosineTail644 a b c (r ^ 2)
    (if r ≤ 320 then -0.456620
      else if r ≤ 1287 / 4 then -0.452096 else if r ≤ 1609 / 5 then -0.450144 else -0.450088) ≤
      1.54 * S (2687 / 1000) + (-1.508) * S (2707 / 1000) + (-0.0917) * S (3787 / 1000) +
        (-((1.54 ^ 2 + 1.508 ^ 2 + 0.0917 ^ 2) / 2)) * S 0 +
        (1.54 * 1.508) * S (1 / 50) +
        (1.54 * 0.0917) * S (11 / 10) +
        (-(1.508 * 0.0917)) * S (27 / 25) := by
  let τ := fun n : ℕ ↦ (a n).re + (b n).re + (c n).re
  have hτ (n : ℕ) : -1 ≤ τ n ∧ τ n ≤ 3 := by
    refine ⟨ht n, ?_⟩
    dsimp only [τ]
    linarith only [(Complex.re_le_norm _).trans (a.norm_le_one n),
      (Complex.re_le_norm _).trans (b.norm_le_one n),
      (Complex.re_le_norm _).trans (c.norm_le_one n)]
  have hX : (99856 : ℝ) ≤ r ^ 2 :=
    (show (99856 : ℝ) = 316 ^ 2 by norm_num only) ▸ pow_le_pow_left₀ (by norm_num only) hr 2
  have hp := (by norm_num only : (0 : ℝ) < 99856).trans_le hX
  have hlog : (5 : ℝ) ≤ Real.log 99856 :=
    (Analysis.rationalLogIntervalCheck_sound (N := 99856) (j := 16) (n := 20) (lo := 5) (hi := 12)
        (by decide +kernel)).1
  dsimp only
  rw [quarter_cosine_tail_eq_644 a b c hp (hlog.trans (Real.log_le_log (by norm_num only) hX))]
  by_cases h₁ : r ≤ 320
  · rw [ite_eq_left h₁]
    exact quarter_aux_euler_lower_316 hX hRH τ hτ
  rw [ite_eq_right h₁]
  by_cases h₂ : r ≤ 1287 / 4
  · rw [ite_eq_left h₂]
    have h : (102400 : ℝ) ≤ r ^ 2 :=
      (show (102400 : ℝ) = 320 ^ 2 by norm_num only) ▸
        pow_le_pow_left₀ (by norm_num only) (le_of_not_ge h₁) 2
    exact quarter_aux_euler_lower_320 h hRH τ hτ
  rw [ite_eq_right h₂]
  by_cases h₃ : r ≤ 1609 / 5
  · rw [ite_eq_left h₃]
    have h : (1656369 / 16 : ℝ) ≤ r ^ 2 :=
      (show (1656369 / 16 : ℝ) = (1287 / 4) ^ 2 by norm_num only) ▸
        pow_le_pow_left₀ (by norm_num only) (le_of_not_ge h₂) 2
    exact quarter_aux_euler_lower_32175 h hRH τ hτ
  rw [ite_eq_right h₃]
  have h : (2588881 / 25 : ℝ) ≤ r ^ 2 :=
    (show (2588881 / 25 : ℝ) = (1609 / 5) ^ 2 by norm_num only) ▸
      pow_le_pow_left₀ (by norm_num only) (le_of_not_ge h₃) 2
  exact quarter_aux_euler_lower_3218 h hRH τ hτ

end PseudoPrime.PrimeTestBounds.MillerRabin
