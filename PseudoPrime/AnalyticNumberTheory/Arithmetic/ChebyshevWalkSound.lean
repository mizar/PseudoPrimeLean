/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevWalkExecution
import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimePowerWitnessSound
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevFixedStep
import PseudoPrime.Analysis.LogWalkBounds

/-! # Soundness of the sequential fixed-point psi walk -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- The walk state has a positive index and its two integer pairs enclose the
scaled logarithm and Chebyshev psi value at that index. The scale is natural,
so it is nonnegative. -/
def PsiWalkValid (S : ℕ) (s : PsiWalkState) : Prop :=
  0 < s.n ∧
    (s.logLo : ℝ) ≤ S * Real.log s.n ∧
    (S : ℝ) * Real.log s.n ≤ s.logHi ∧
    (s.psiLo : ℝ) ≤ S * Chebyshev.psi s.n ∧ (S : ℝ) * Chebyshev.psi s.n ≤ s.psiHi

/-- A power entry carries lower and upper fixed-point bounds for its base
logarithm. Other entries require no external logarithm certificate. -/
def PsiWalkEntryValid (S : ℕ) : PsiWalkEntry → Prop
  | .power p _ lo hi => (lo : ℝ) ≤ S * Real.log p ∧ (S : ℝ) * Real.log p ≤ hi
  | _ => True

/-- One successful composite-witness update preserves all walk invariants.
The coprime factors prove that the Mangoldt increment vanishes. -/
private theorem composite_step_sound {S : ℕ} {s t : PsiWalkState} {d : ℕ} (hs : PsiWalkValid S s)
    (hstep : psiWalkStep S s (.composite d) = some t) : PsiWalkValid S t := by
  have hl := Analysis.log_increment_fixed_step (S := S) hs.1 hs.2.1 hs.2.2.1
  by_cases hc : ((decide (0 < d) : Bool) && primePowerWitnessCheck (s.n + 1) d) = true
  · have hparts := Bool.and_eq_true_iff.mp hc
    have hd : 0 < d := of_decide_eq_true hparts.1
    have hn : ¬IsPrimePow (s.n + 1) := by
      intro hp
      exact (Nat.ne_of_gt hd) (prime_power_witness_sound hparts.2 hp)
    have hz := ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn
    have hwlo : ((0 : ℕ) : ℝ) ≤ S * ArithmeticFunction.vonMangoldt (s.n + 1) := by
      simp only [Nat.cast_zero, hz, mul_zero, le_refl]
    have hwhi : (S : ℝ) * ArithmeticFunction.vonMangoldt (s.n + 1) ≤ ((0 : ℕ) : ℝ) := by
      simp only [Nat.cast_zero, hz, mul_zero, le_refl]
    have hp := psi_fixed_step s.n S s.psiLo s.psiHi 0 0 hs.2.2.2.1 hs.2.2.2.2 hwlo hwhi
    simp only [psiWalkStep, psiWalkLogStep, hc, ite_true, Option.some.injEq] at hstep
    subst t
    simp only [PsiWalkValid, Nat.add_zero] at hp ⊢
    exact ⟨Nat.zero_lt_succ s.n, hl.1, hl.2, hp.1, hp.2⟩
  · simp only [psiWalkStep, psiWalkLogStep, hc, Bool.false_eq_true, ite_false] at hstep
    cases hstep

/-- One successful prime update preserves the walk invariants. For a prime,
the Mangoldt increment equals its logarithm, whose bounds were just advanced. -/
private theorem prime_step_sound {S : ℕ} {s t : PsiWalkState} (hs : PsiWalkValid S s)
    (hstep : psiWalkStep S s .prime = some t) : PsiWalkValid S t := by
  have hl := Analysis.log_increment_fixed_step (S := S) hs.1 hs.2.1 hs.2.2.1
  simp only [psiWalkStep, psiWalkLogStep] at hstep
  by_cases hp : (s.n + 1).Prime
  · have hwlo :
      ((s.logLo + 2 * S / (2 * s.n + 1) : ℕ) : ℝ) ≤
        S * ArithmeticFunction.vonMangoldt (s.n + 1) := by
      rw [ArithmeticFunction.vonMangoldt_apply_prime hp]
      exact hl.1
    have hwhi :
      (S : ℝ) * ArithmeticFunction.vonMangoldt (s.n + 1) ≤ ((s.logHi + (S / s.n + 1) : ℕ) : ℝ) := by
      rw [ArithmeticFunction.vonMangoldt_apply_prime hp]
      exact hl.2
    have hψ := psi_fixed_step s.n S s.psiLo s.psiHi _ _ hs.2.2.2.1 hs.2.2.2.2 hwlo hwhi
    simp only [hp, decide_true, ite_true, Option.some.injEq] at hstep
    subst t
    exact ⟨Nat.zero_lt_succ s.n, hl.1, hl.2, hψ.1, hψ.2⟩
  · simp only [hp, decide_false, Bool.false_eq_true, ite_false] at hstep
    cases hstep

/-- One successful prime-power update preserves the walk invariants if the
entry's supplied bounds enclose the scaled logarithm of its prime base. -/
private theorem power_step_sound {S : ℕ} {s t : PsiWalkState} {p k lo hi : ℕ}
    (hs : PsiWalkValid S s) (hlo : (lo : ℝ) ≤ S * Real.log p) (hhi : (S : ℝ) * Real.log p ≤ hi)
    (hstep : psiWalkStep S s (.power p k lo hi) = some t) : PsiWalkValid S t := by
  have hl := Analysis.log_increment_fixed_step (S := S) hs.1 hs.2.1 hs.2.2.1
  simp only [psiWalkStep, psiWalkLogStep] at hstep
  by_cases hp : p.Prime
  · by_cases he : p ^ (k + 1) = s.n + 1
    · have hwlo : (lo : ℝ) ≤ S * ArithmeticFunction.vonMangoldt (s.n + 1) := by
        rw [← he, ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero k),
          ArithmeticFunction.vonMangoldt_apply_prime hp]
        exact hlo
      have hwhi : (S : ℝ) * ArithmeticFunction.vonMangoldt (s.n + 1) ≤ hi := by
        rw [← he, ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero k),
          ArithmeticFunction.vonMangoldt_apply_prime hp]
        exact hhi
      have hψ := psi_fixed_step s.n S s.psiLo s.psiHi lo hi hs.2.2.2.1 hs.2.2.2.2 hwlo hwhi
      simp only [hp, he, decide_true, Bool.true_and, ite_true, Option.some.injEq] at hstep
      subst t
      exact ⟨Nat.zero_lt_succ s.n, hl.1, hl.2, hψ.1, hψ.2⟩
    · simp only [he, decide_false, Bool.and_false, Bool.false_eq_true, ite_false] at hstep
      cases hstep
  · simp only [hp, decide_false, Bool.false_and, Bool.false_eq_true, ite_false] at hstep
    cases hstep

/-- A successful checked update preserves the fixed-point walk invariants.
Prime-power entries must carry independently certified logarithm bounds. -/
theorem psi_walk_step_sound {S : ℕ} {s t : PsiWalkState} {e : PsiWalkEntry} (hs : PsiWalkValid S s)
    (he : PsiWalkEntryValid S e) (hstep : psiWalkStep S s e = some t) : PsiWalkValid S t := by
  cases e with
  | composite d => exact composite_step_sound hs hstep
  | prime => exact prime_step_sound hs hstep
  | power p k lo hi => exact power_step_sound hs he.1 he.2 hstep

/-- A successful sequential walk preserves the fixed-point bounds when its
initial state and every prime-power entry satisfy their semantic invariants.
The proof follows the input list structurally and reuses the one-step theorem. -/
theorem psi_walk_sound {S : ℕ} {s t : PsiWalkState} {es : List PsiWalkEntry} (hs : PsiWalkValid S s)
    (he : es.Forall (PsiWalkEntryValid S)) (hwalk : psiWalk S s es = some t) :
    PsiWalkValid S t := by
  induction es generalizing s with
  | nil =>
    simp only [psiWalk, Option.some.injEq] at hwalk
    subst t
    exact hs
  | cons e es ih =>
    have he' := (List.forall_cons _ _ _).mp he
    cases hstep : psiWalkStep S s e with
    | none =>
      simp only [psiWalk, hstep] at hwalk
      cases hwalk
    | some u =>
      have hu := psi_walk_step_sound hs he'.1 hstep
      simp only [psiWalk, hstep] at hwalk
      exact ih hu he'.2 hwalk

end PseudoPrime.AnalyticNumberTheory.Arithmetic
