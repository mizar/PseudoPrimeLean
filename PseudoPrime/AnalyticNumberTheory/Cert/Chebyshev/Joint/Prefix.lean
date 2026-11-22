/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevIntervalPrefix
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.Scan

/-! # Mathematical interpretation of joint prefix updates -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- The four rounded ticks enclose psi and its defect over theta in scaled units.
The final field records cancellation of identical lower ticks at higher prime powers. -/
structure Bounds (p t l h d e : ℝ) : Prop where
  psiLo : l ≤ p
  psiHi : p ≤ h
  defectLo : d ≤ p - t
  defectHi : p - t ≤ e
  thetaLo : l - d ≤ t

/-- Prefix bounds compose with increment bounds by adding each tick component. -/
theorem Bounds.add {p t l h d e P T L H D E : ℝ} (a : Bounds p t l h d e) (b : Bounds P T L H D E) :
    Bounds (p + P) (t + T) (l + L) (h + H) (d + D) (e + E) := by
  refine ⟨add_le_add a.psiLo b.psiLo, add_le_add a.psiHi b.psiHi, ?_, ?_, ?_⟩
  · linarith only [a.defectLo, b.defectLo]
  · linarith only [a.defectHi, b.defectHi]
  · linarith only [a.thetaLo, b.thetaLo]

/-- One integer adds its Mangoldt weight to the psi prefix. -/
theorem psi_next (n : ℕ) :
    Chebyshev.psi (n + 1 : ℕ) = Chebyshev.psi n + ArithmeticFunction.vonMangoldt (n + 1) := by
  simpa only [Nat.Ioc_succ_singleton, Finset.sum_singleton] using
    (Arithmetic.psi_prefix_add_interval (Nat.le_succ n)).symm

/-- One integer adds its logarithm to theta exactly when it is prime. -/
theorem theta_next (n : ℕ) :
    Chebyshev.theta (n + 1 : ℕ) =
      Chebyshev.theta n + (if (n + 1).Prime then Real.log (n + 1 : ℕ) else 0) := by
  simpa only [Finset.sum_filter, Nat.Ioc_succ_singleton, Finset.sum_singleton] using
    (Arithmetic.theta_prefix_add_interval (Nat.le_succ n)).symm

/-- Interpret the four ticks through integer `n` as bounds on the actual scaled
Chebyshev functions. Only scalar data appear in this invariant. -/
def Prefix (n l h d e : ℕ) : Prop :=
  Bounds (scale * Chebyshev.psi n) (scale * Chebyshev.theta n) l h d e

/-- At zero both functions and all four accumulated integer ticks vanish. -/
theorem prefix_zero : Prefix 0 0 0 0 0 := by
  simp only [Prefix, Nat.cast_zero, Chebyshev.psi_zero, Chebyshev.theta_zero, mul_zero]
  exact ⟨le_rfl, le_rfl, (sub_zero 0).ge, (sub_zero 0).le, (sub_zero 0).le⟩

/-- A certified increment at `n + 1` extends a prefix of the true psi and theta.
Rewriting both successor formulas reduces the proof to componentwise addition. -/
theorem prefix_next {n l h d e L H D E : ℕ} (a : Prefix n l h d e)
    (b :
      Bounds (scale * ArithmeticFunction.vonMangoldt (n + 1))
        (scale * (if (n + 1).Prime then Real.log (n + 1 : ℕ) else 0)) L H D E) :
    Prefix (n + 1) (l + L) (h + H) (d + D) (e + E) := by
  rw [Prefix, psi_next, theta_next]
  simpa only [mul_add, Nat.cast_add] using a.add b

/-- A prime adds its certified logarithm to both functions and leaves the defect unchanged. -/
theorem prefix_prime {n l h d e L H : ℕ} (a : Prefix n l h d e) (hp : (n + 1).Prime)
    (lo : (L : ℝ) ≤ scale * Real.log (n + 1 : ℕ)) (hi : (scale : ℝ) * Real.log (n + 1 : ℕ) ≤ H) :
    Prefix (n + 1) (l + L) (h + H) d e := by
  apply prefix_next (D := 0) (E := 0) a
  rw [ArithmeticFunction.vonMangoldt_apply_prime hp, ite_eq_left hp, Nat.cast_zero]
  exact ⟨lo, hi, (sub_self _).ge, (sub_self _).le, (sub_zero _).le.trans lo⟩

/-- A composite prime power adds the same ticks to psi and the defect, preserving theta. -/
theorem prefix_power {n l h d e L H p k : ℕ} (a : Prefix n l h d e) (hn : n + 1 = p ^ k)
    (hp : p.Prime) (hk : k ≠ 0) (hc : ¬(n + 1).Prime) (lo : (L : ℝ) ≤ scale * Real.log p)
    (hi : (scale : ℝ) * Real.log p ≤ H) : Prefix (n + 1) (l + L) (h + H) (d + L) (e + H) := by
  apply prefix_next a
  rw [ite_eq_right hc, hn, ArithmeticFunction.vonMangoldt_apply_pow hk,
    ArithmeticFunction.vonMangoldt_apply_prime hp, mul_zero]
  exact
    ⟨lo, hi, by simpa only [sub_zero] using lo, by simpa only [sub_zero] using hi, (sub_self _).le⟩

/-- At a nonprime which is not a prime power, the entire prefix state stays unchanged. -/
theorem prefix_other {n l h d e : ℕ} (a : Prefix n l h d e) (hp : ¬IsPrimePow (n + 1))
    (hc : ¬(n + 1).Prime) : Prefix (n + 1) l h d e := by
  apply prefix_next (L := 0) (H := 0) (D := 0) (E := 0) a
  rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hp, ite_eq_right hc, mul_zero, Nat.cast_zero]
  exact ⟨le_rfl, le_rfl, (sub_zero 0).ge, (sub_zero 0).le, (sub_zero 0).le⟩

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
