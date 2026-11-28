/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformTo663
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSmallInputs
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterNonuniformLog8
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeLogSquareBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # The quarter-square Miller–Rabin criterion through logarithm 663 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A prime Miller–Rabin rejecting base up to the given real cutoff. -/
@[expose]
def HasRejectingPrime (n : ℕ) (cutoff : ℝ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ cutoff ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n)

/-- Increasing the cutoff preserves a prime rejecting witness. -/
theorem HasRejectingPrime.mono {n : ℕ} {x y : ℝ} (h : HasRejectingPrime n x) (hxy : x ≤ y) :
    HasRejectingPrime n y := by
  obtain ⟨p, hp, hb, hf⟩ := h
  exact ⟨p, hp, hb.trans hxy, hf⟩

private theorem lt_3000_of_log_le_eight {n : ℕ} (hL : Real.log n ≤ 8) : n < 3000 := by
  by_contra h
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 3000 12 12 (8001 / 1000) (801 / 100) = true by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat] at hl
  have hm := Real.log_le_log (by norm_num only : (0 : ℝ) < 3000) (Nat.cast_le.mpr (le_of_not_gt h))
  have hstrict : (8 : ℝ) < 8001 / 1000 := by norm_num only
  exact (not_lt_of_ge hL) (hstrict.trans_le (hl.trans hm))

/-- Under GRH, the quarter-square cutoff supplies a prime witness through
log 663 and for every nonuniform odd composite. -/
theorem quarter_witness_to663 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hrange : Real.log n ≤ 663 ∨ ¬UniformKorseltTriple n) :
    HasRejectingPrime n (max 2 ((1 / 4 : ℝ) * Real.log n ^ 2)) := by
  by_cases h8 : Real.log n ≤ 8
  · exact exists_prime_reject_quarter_small hn ho hc (lt_3000_of_log_le_eight h8)
  by_cases hu : UniformKorseltTriple n
  · have h :=
      uniform_witness_8_to663 hn ho hu hGRH
        ⟨le_of_not_ge h8, hrange.resolve_right (not_not_intro hu)⟩
    apply HasRejectingPrime.mono h
    rw [show (Real.log n / 2) ^ 2 = (1 / 4 : ℝ) * Real.log n ^ 2 by ring]
    exact le_max_right _ _
  · exact
      HasRejectingPrime.mono (quarter_nonuniform_log8 hn ho hc hu hGRH (le_of_not_ge h8))
        (le_max_right _ _)

/-- A prime base up to the log-square cutoff or two passes for every odd prime. -/
theorem prime_pass_of_log_sq {n p : ℕ} (ho : Odd n) (hn : n.Prime) (hp : p.Prime)
    (hb : (p : ℝ) ≤ max 2 (Real.log n ^ 2)) : PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  rcases le_max_iff.mp hb with htwo | hlarge
  · have hp2 : p = 2 := Nat.le_antisymm (by exact_mod_cast htwo) hp.two_le
    subst p
    exact
      PrimeTest.strongMillerRabinWithBase_eq_true_iff_pass.mp
        (PrimeTest.strongMillerRabinBase2_of_prime_of_ne_two hn (ho.ne_two_of_dvd_nat dvd_rfl))
  · by_contra hnot
    exact
      no_prime_millerRabin_witness_le_log_sq_of_prime ho hn
        ⟨p, hp, hlarge, PrimeTest.not_strongMillerRabinPass_iff.mp hnot⟩

/-- Under GRH, prime bases through the quarter-square cutoff characterize
odd primes with logarithm at most 663. -/
theorem prime_millerRabin_025_L663_criterion
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : 1 < n)
    (hln : Real.log n ≤ 663) (ho : Odd n) :
    (∀ p : ℕ,
        p.Prime →
          (p : ℝ) ≤ max 2 ((1 / 4 : ℝ) * Real.log n ^ 2) →
          PrimeTest.StrongMillerRabinPass n (p : ZMod n)) ↔
      n.Prime := by
  refine ⟨fun h ↦ Classical.byContradiction fun hc ↦ ?_, fun hp p hprime hb ↦ ?_⟩
  · obtain ⟨p, hp, hb, hfail⟩ := quarter_witness_to663 hn ho hc hGRH (Or.inl hln)
    exact hfail (h p hp hb)
  · exact
      prime_pass_of_log_sq ho hp hprime
        (hb.trans (max_le_max_left _ (by nlinarith only [sq_nonneg (Real.log n)])))

end PseudoPrime.PrimeTestBounds.MillerRabin
