/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.LocalFixedWitness

/-! # Interpolated local witness guard -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The continuous weight rising from zero to one between scales 25 and 26.
It interpolates the moderate quadratic and adaptive local witness bounds. -/
noncomputable def localInterpolationWeight (s : ℝ) : ℝ :=
  min 1 (max 0 (s - 25))

/-- The maximum of 61 and the weighted moderate/adaptive local bound.
The weight changes only on `[25, 26]`; this guard covers all local levels
and forms one candidate in the common local envelope. -/
noncomputable def localInterpolatedGuard (s : ℝ) : ℝ :=
  max 61
    ((1 - localInterpolationWeight s) * ((81 / 100 : ℝ) * s ^ 2) +
      localInterpolationWeight s * (Analysis.adaptivePart2CutoffRoot (max 7 s)) ^ 2)

/-- From scale nine, the guard dominates the `81/100` quadratic. The adaptive
square is larger there and the interpolation weight is nonnegative. This lets
the moderate-scale witness pass through the interpolation interval. -/
theorem local_guard_ge_eighty_one {s : ℝ} (hs : 9 ≤ s) :
    (81 / 100 : ℝ) * s ^ 2 ≤ localInterpolatedGuard s := by
  have hzero : 0 ≤ localInterpolationWeight s := le_min (by norm_num only) (le_max_left _ _)
  have hclamp : max 7 s = s := max_eq_right (by linarith only [hs])
  have hlt := LLS.PaperStatements.fullEndpoint_eightyOne_lt_adaptive hs
  have hp := mul_nonneg hzero (sub_nonneg.mpr (le_of_lt hlt))
  apply le_trans _ (le_max_right _ _)
  rw [hclamp]
  nlinarith only [hp]

/-- From scale 26, the guard dominates the clamped adaptive square. The
interpolation weight is one, so the adaptive candidate is a term of the maximum.
This covers the upper local-scale branch. -/
theorem local_guard_ge_adaptive {s : ℝ} (hs : 26 ≤ s) :
    (Analysis.adaptivePart2CutoffRoot (max 7 s)) ^ 2 ≤ localInterpolatedGuard s := by
  have ht : localInterpolationWeight s = 1 :=
    min_eq_left ((by linarith only [hs] : (1 : ℝ) ≤ s - 25).trans (le_max_right _ _))
  dsimp only [localInterpolatedGuard]
  rw [ht]
  norm_num only [sub_self, zero_mul, one_mul, zero_add]
  exact le_max_right _ _

/-- Under GRH, odd `n > 1`, a proper subgroup at a divisor `q ≥ 5` containing
all passing residues, and `log q ≤ s`, there is a rejecting prime within the
interpolated guard. Use the fixed 61 bound below local level nine, the `81/100`
bound through scale 26, and the adaptive candidate thereafter. This certifies
the remaining candidate of the planned local envelope. -/
theorem exists_prime_reject_local_guard {n q : ℕ} [NeZero q] (hn : 1 < n) (ho : Odd n) (hq : 5 ≤ q)
    (hqn : q ∣ n) (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hpass :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
          ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (a : ZMod q))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {s : ℝ} (hs : Real.log q ≤ s) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ localInterpolatedGuard s ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases hq9 : Real.log q ≤ 9
  · obtain ⟨p, hp, hb, hf⟩ := exists_prime_reject_local_le_sixty_one H hH hpass hGRH hq9
    exact ⟨p, hp, hb.trans (le_max_left _ _), hf⟩
  · by_cases hs26 : s ≤ 26
    · have hq9' : 9 ≤ Real.log q := le_of_lt (lt_of_not_ge hq9)
      obtain ⟨p, hp, hb, hf⟩ :=
        exists_prime_reject_local_eighty_one H hH hpass hGRH hq9' (hs.trans hs26) hs
      exact ⟨p, hp, hb.trans (local_guard_ge_eighty_one (hq9'.trans hs)), hf⟩
    · obtain ⟨p, hp, hb, hf⟩ :=
        exists_prime_reject_local_clamped_min hn ho hq hqn H hH hpass hGRH hs
      exact
        ⟨p, hp, (hb.trans (min_le_left _ _)).trans (local_guard_ge_adaptive (le_of_not_ge hs26)),
          hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
