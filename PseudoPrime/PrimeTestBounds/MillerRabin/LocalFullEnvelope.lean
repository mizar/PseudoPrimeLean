/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.LocalInterpolatedGuard

/-! # Common local Miller–Rabin witness envelope -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The general-subgroup local envelope at scale `s`: the minimum of `s²`,
the clamped adaptive square, and the interpolated moderate-scale guard.
Each candidate supplies a local-to-original rejecting-prime bound under GRH. -/
noncomputable def localBaselineEnvelope (s : ℝ) : ℝ :=
  min (s ^ 2) (min ((Analysis.adaptivePart2CutoffRoot (max 7 s)) ^ 2) (localInterpolatedGuard s))

/-- The common local envelope at scale `s`, combining the general-subgroup
envelope with the twenty even-character corrections. Its bound applies to any
proper local subgroup containing the strong passing residues. -/
noncomputable def localFullEnvelope (s : ℝ) : ℝ :=
  min (localBaselineEnvelope s) (localEvenEnvelope s)

/-- Rearrange the common minimum into the three-candidate bound and the
interpolated guard. The identity uses only associativity and commutativity of
minimum and allows the two actual-witness theorems to be combined. -/
theorem localFullEnvelope_rearrange (s : ℝ) :
    localFullEnvelope s =
      min
        (min ((Analysis.adaptivePart2CutoffRoot (max 7 s)) ^ 2) (min (s ^ 2) (localEvenEnvelope s)))
        (localInterpolatedGuard s) := by
  simp only [localFullEnvelope, localBaselineEnvelope, min_assoc, min_comm, min_left_comm]

/-- Under GRH, if odd `n > 1` has a proper subgroup at a divisor `q ≥ 5`
containing all passing residues and `log q ≤ s`, then a prime rejecting `n`
lies within the common local envelope. Select the smaller of the certified
three-candidate bound and interpolated guard. This is the local witness contract
for the factor-type coverage. -/
theorem exists_prime_reject_local_full {n q : ℕ} [NeZero q] (hn : 1 < n) (ho : Odd n) (hq : 5 ≤ q)
    (hqn : q ∣ n) (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hpass :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
          ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (a : ZMod q))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {s : ℝ} (hs : Real.log q ≤ s) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ localFullEnvelope s ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  rw [localFullEnvelope_rearrange]
  by_cases h :
    (min ((Analysis.adaptivePart2CutoffRoot (max 7 s)) ^ 2) (min (s ^ 2) (localEvenEnvelope s))) ≤
      localInterpolatedGuard s
  · rw [min_eq_left h]
    exact exists_prime_reject_local_clamped_min hn ho hq hqn H hH hpass hGRH hs
  · rw [min_eq_right (le_of_not_ge h)]
    exact exists_prime_reject_local_guard hn ho hq hqn H hH hpass hGRH hs

end PseudoPrime.PrimeTestBounds.MillerRabin
