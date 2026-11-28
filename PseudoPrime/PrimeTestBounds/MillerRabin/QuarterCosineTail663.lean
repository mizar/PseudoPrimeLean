/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosineCore663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosineSeries656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterProfile663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAuxSlope663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosineCore663

/-! # The paired Euler tail for the six section 137 frequencies -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem aux_mix_tsum {ι : Type*} (F : ℚ → ι → ℝ) (hf : ∀ s, Summable (F s)) :
    quarterAuxMix663 (fun s ↦ ∑' n, F s n) = ∑' n, quarterAuxMix663 (fun s ↦ F s n) := by
  let f := fun i ↦ F (quarterFreq663 i)
  let g := fun i j ↦ F (quarterFreq663 i - quarterFreq663 j)
  let c := fun i : Fin 6 ↦ (quarterCoeff663 i : ℝ)
  have hp (i j : Fin 6) : Summable (fun n ↦ c i * c j * g i j n) := (hf _).mul_left _
  have hrow (i : Fin 6) : Summable (fun n ↦ ∑ j, c i * c j * g i j n) :=
    summable_sum (fun j _ ↦ hp i j)
  have hP : Summable (fun n ↦ ∑ i, ∑ j, c i * c j * g i j n) := summable_sum (fun i _ ↦ hrow i)
  have hS (i : Fin 6) : Summable (fun n ↦ c i * f i n) := (hf _).mul_left _
  have hSS : Summable (fun n ↦ ∑ i, c i * f i n) := summable_sum (fun i _ ↦ hS i)
  have h := Summable.tsum_sub (hP.div_const 2) hSS
  rw [tsum_div_const, Summable.tsum_finsetSum (fun i _ ↦ hrow i),
    Summable.tsum_finsetSum (fun i _ ↦ hS i)] at h
  simpa only [quarterAuxMix663, f, g, c, Summable.tsum_finsetSum (fun j _ ↦ hp _ j),
    tsum_mul_left] using h.symm

private theorem aux_frequency_abs_le (i : Fin 6) : |(quarterFreq663 i : ℝ)| ≤ 10 := by
  have h : ∀ j, |quarterFreq663 j| ≤ 10 := by decide +kernel
  exact_mod_cast h i

private theorem aux_frequency_diff_le (i j : Fin 6) :
    |((quarterFreq663 i - quarterFreq663 j : ℚ) : ℝ)| ≤ 10 := by
  have h : ∀ k l, |quarterFreq663 k - quarterFreq663 l| ≤ 10 := by decide +kernel
  exact_mod_cast h i j

/-- Pairing reciprocal scales and summing all frequencies gives the auxiliary
Euler polynomial weighted by the trace deficit. -/
theorem quarter_cosine_tail_eq_663 {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) {X : ℝ}
    (hX : (322 : ℝ) ^ 2 ≤ X) :
    quarterAuxMix663 (fun s ↦ quarterCosineTail656 a b c X (s : ℝ)) =
      ∑' n : { n : ℕ // ⌊X⌋₊ < n },
        (3 - ((a n.val).re + (b n.val).re + (c n.val).re)) *
          (ArithmeticFunction.vonMangoldt n.val / (n.val : ℝ) ^ (8 / 5 : ℝ)) *
          (quarterProfile663 (Real.log n.val) - quarterAuxProfile656 (Real.log n.val)) := by
  let N := { n : ℕ // ⌊X⌋₊ < n }
  let D := fun n : N ↦ 3 - ((a n.val).re + (b n.val).re + (c n.val).re)
  let F := fun s : ℚ ↦ fun n : N ↦
    D n *
      (ArithmeticFunction.vonMangoldt n.val / Real.sqrt n.val *
        (quarterSymmetricProfile656 (n.val / Real.exp |(s : ℝ)|) +
          quarterSymmetricProfile656 (n.val / (Real.exp |(s : ℝ)|)⁻¹)))
  have hF (s : ℚ) : Summable (F s) := by
    have hp := Real.exp_pos |s|
    have ha := (quarter_trace_tail_hasSum_656 a b c X hp).summable
    have hb := (quarter_trace_tail_hasSum_656 a b c X (inv_pos.mpr hp)).summable
    dsimp only at ha hb
    apply (ha.add hb).congr
    intro n
    simp only [F, D, mul_add]
  change quarterAuxMix663 (fun s ↦ ∑' n, F s n) = _
  rw [aux_mix_tsum F hF]
  apply tsum_congr
  intro n
  have hX₀ := (by norm_num only : (0 : ℝ) < 322 ^ 2).trans_le hX
  have hn := (Nat.floor_lt hX₀.le).mp n.property
  have hn₀ := hX₀.trans hn
  have hlog : 10 ≤ Real.log n.val := by
    have he : Real.exp 10 ≤ (322 : ℝ) ^ 2 := by
      rw [show (10 : ℝ) = 1 * ((10 : ℕ) : ℝ) by norm_num only, Real.exp_mul_natCast]
      exact
        (pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le _).trans (by norm_num only)
    exact (Real.le_log_iff_exp_le hn₀).mpr (he.trans (hX.trans hn.le))
  have hscale :
    Real.exp (-(11 / 10) * Real.log n.val) / Real.sqrt n.val = ((n.val : ℝ) ^ (8 / 5 : ℝ))⁻¹ := by
    rw [mul_comm (-(11 / 10 : ℝ)), ← Real.rpow_def_of_pos hn₀, Real.sqrt_eq_rpow, ←
      Real.rpow_sub hn₀, show -(11 / 10 : ℝ) - 1 / 2 = -(8 / 5) by norm_num only,
      Real.rpow_neg hn₀.le]
  let K := D n * (ArithmeticFunction.vonMangoldt n.val / (n.val : ℝ) ^ (8 / 5 : ℝ))
  have he (s : ℚ) (hs : |(s : ℝ)| ≤ 10) : F s n = K * quarterAuxPair656 s (Real.log n.val) := by
    dsimp only [F, K]
    rw [quarter_cosine_profile_pair_656 hn₀ (hs.trans hlog)]
    linear_combination
      (D n * ArithmeticFunction.vonMangoldt n.val * quarterAuxPair656 s (Real.log n.val)) * hscale
  change
    quarterAuxMix663 (fun s ↦ F s n) =
      K * (quarterProfile663 (Real.log n.val) - quarterAuxProfile656 (Real.log n.val))
  unfold quarterProfile663 quarterAuxMix663
  have h₁ (i : Fin 6) :
    (quarterCoeff663 i : ℝ) * F (quarterFreq663 i) n =
      K * ((quarterCoeff663 i : ℝ) * quarterAuxPair656 (quarterFreq663 i) (Real.log n.val)) := by
    rw [he _ (aux_frequency_abs_le i), mul_left_comm]
  have h₂ (i j : Fin 6) :
    (quarterCoeff663 i : ℝ) * (quarterCoeff663 j : ℝ) * F (quarterFreq663 i - quarterFreq663 j) n =
      K *
        ((quarterCoeff663 i : ℝ) * (quarterCoeff663 j : ℝ) *
          quarterAuxPair656 ((quarterFreq663 i - quarterFreq663 j : ℚ) : ℝ) (Real.log n.val)) := by
    rw [he _ (aux_frequency_diff_le i j), mul_left_comm]
  simp only [h₁, h₂, ← Finset.mul_sum]
  ring

/-- Three primitive even self-inverse characters with prime agreement have
one mixed cosine bound with a shared signed Euler tail. -/
theorem quarter_scaled_cosine_cap_663 {p q k : ℕ} [NeZero p] [NeZero q] [NeZero k]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ k}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hRH : RiemannHypothesis) {r t : ℝ}
    (hr : 328 ≤ r) (hL : Real.log p + Real.log q + Real.log k = 4 * t)
    (hpa : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → a n = 1)
    (hpb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → b n = 1)
    (hpc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → c n = 1) :
    quarterAuxMix663
        (fun t ↦
          quarterCosineContour656 a |(t : ℝ)| + quarterCosineContour656 b |(t : ℝ)| +
            quarterCosineContour656 c |(t : ℝ)|) ≤
      quarterAuxMix663 quarterConductorProfile663 * t - 3.64052193 +
        ∑' n : { n : ℕ // ⌊r ^ 2⌋₊ < n },
          (3 - ((a n.val).re + (b n.val).re + (c n.val).re)) *
            (ArithmeticFunction.vonMangoldt n.val / (n.val : ℝ) ^ (8 / 5 : ℝ)) *
            (quarterProfile663 (Real.log n.val) - quarterAuxProfile656 (Real.log n.val)) := by
  have hX := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 322) (by linarith only [hr] : 322 ≤ r) 2
  have he (t : ℚ) := quarter_three_cosine_split_656 ha hb hc (sq_nonneg r) (t : ℝ) hpa hpb hpc
  simp only [hL] at he
  rw [funext he]
  have hadd (f g : ℚ → ℝ) :
    quarterAuxMix663 (fun t ↦ f t + g t) = quarterAuxMix663 f + quarterAuxMix663 g := by
    simpa only [one_mul, zero_mul, add_zero] using mix_linear f g (fun _ ↦ 0) 1 1 0
  rw [hadd, quarter_cosine_tail_eq_663 a b c hX]
  exact add_le_add (quarter_cosine_core_cap_663 hRH t) le_rfl

/-- Specialize the independent conductor radius to the quarter-square radius. -/
theorem quarter_three_cosine_cap_663 {p q k : ℕ} [NeZero p] [NeZero q] [NeZero k]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ k}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hRH : RiemannHypothesis) {r : ℝ} (hr : 328 ≤ r)
    (hL : Real.log p + Real.log q + Real.log k = 4 * r)
    (hpa : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → a n = 1)
    (hpb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → b n = 1)
    (hpc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → c n = 1) :
    quarterAuxMix663
        (fun t ↦
          quarterCosineContour656 a |(t : ℝ)| + quarterCosineContour656 b |(t : ℝ)| +
            quarterCosineContour656 c |(t : ℝ)|) ≤
      quarterAuxMix663 quarterConductorProfile663 * r - 3.64052193 +
        ∑' n : { n : ℕ // ⌊r ^ 2⌋₊ < n },
          (3 - ((a n.val).re + (b n.val).re + (c n.val).re)) *
            (ArithmeticFunction.vonMangoldt n.val / (n.val : ℝ) ^ (8 / 5 : ℝ)) *
            (quarterProfile663 (Real.log n.val) - quarterAuxProfile656 (Real.log n.val)) := by
  exact quarter_scaled_cosine_cap_663 ha hb hc hRH hr hL hpa hpb hpc

end PseudoPrime.PrimeTestBounds.MillerRabin
