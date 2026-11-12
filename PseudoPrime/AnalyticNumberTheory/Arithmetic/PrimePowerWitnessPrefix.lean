/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimePowerLogCoverage
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimePowerWitnessExecution
import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimePowerWitnessSound

/-! # Prefix bounds from sequential prime-power support witnesses -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- A consecutive half-open natural interval beginning at `a + 1` equals the
corresponding right-closed interval. The proof only uses successor order. -/
private theorem interval_eq (a k : ℕ) : Finset.Ico (a + 1) (a + 1 + k) = Finset.Ioc a (a + k) := by
  ext n
  simp only [Finset.mem_Ico, Finset.mem_Ioc]
  have heq : a + 1 + k = a + k + 1 := by rw [Nat.add_right_comm]
  rw [heq]
  constructor
  · intro h
    exact ⟨Nat.lt_of_succ_le h.1, Nat.le_of_lt_succ h.2⟩
  · intro h
    exact ⟨Nat.succ_le_of_lt h.1, Nat.lt_succ_of_le h.2⟩

/-- A checked stream of prime-power support witnesses and checked logarithm
rows extend a bounded psi prefix across the entire stream. The event list is
matched sequentially to the row values; coverage and distinctness follow from
the witness scan rather than from a separate primality search for each input. -/
theorem psi_prefix_bounds_of_witnesses {a : ℕ} {L U : ℝ} (hL : L ≤ Chebyshev.psi a)
    (hU : Chebyshev.psi a ≤ U) (ws : List ℕ) (rows : List PrimePowerLogRow)
    (hw : primePowerWitnessScan (a + 1) ws = true) (hr : rows.all primePowerLogCheck = true)
    (he : primePowerWitnessEvents (a + 1) ws = rows.map (fun r ↦ r.p ^ (r.k + 1))) :
    L + (rows.map (fun r ↦ (r.lo : ℝ))).sum ≤ Chebyshev.psi (a + ws.length : ℕ) ∧
      Chebyshev.psi (a + ws.length : ℕ) ≤ U + (rows.map (fun r ↦ (r.hi : ℝ))).sum := by
  have hv : ∀ m ∈ primePowerWitnessEvents (a + 1) ws, IsPrimePow m := by
    intro m hm
    rw [he, List.mem_map] at hm
    obtain ⟨r, hrm, rfl⟩ := hm
    have hc := (Bool.and_eq_true_iff.mp (List.all_eq_true.mp hr r hrm)).1
    let : Decidable r.p.Prime := Nat.decidablePrime' r.p
    have hp : r.p.Prime := of_decide_eq_true hc
    exact hp.isPrimePow.pow (Nat.succ_ne_zero r.k)
  have hn : (rows.map (fun r ↦ r.p ^ (r.k + 1))).Nodup := by
    rw [← he]
    exact prime_power_events_nodup hw hv
  have hf := prime_power_events_finset hw hv
  rw [he, interval_eq] at hf
  have hcover := prime_power_rows_cover_of_finset rows hn hf.symm
  exact psi_prefix_bounds_of_rows (Nat.le_add_right a ws.length) hL hU rows hr hcover

end PseudoPrime.AnalyticNumberTheory.Arithmetic
