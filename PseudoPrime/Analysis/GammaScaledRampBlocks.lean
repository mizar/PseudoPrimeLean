/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaRationalRampMoments

/-! # Balanced finite certificates with scaled integer ramp weights -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The finite numeric check for weighted rows on (lo,hi].
The integer weight is exactly D times logLower times rampLower squared.
Prime bases are certified separately by arithmetic reflection. -/
def gammaScaledRampBlockCheck (rows : List (GammaFiniteRampRow × ℤ)) (a : ℚ) (D lo hi : ℕ) : Bool :=
  decide
    (lo ≤ hi ∧
      rows.Forall
        (fun rz ↦
          rz.1.check (2 * a) = true ∧
            (rz.2 : ℚ) = (D : ℚ) * (rz.1.logLower * rz.1.rampLower ^ 2) ∧
            lo < rz.1.index ∧ rz.1.index ≤ hi) ∧
      (rows.map (fun rz ↦ rz.1.index)).Nodup)

/-- A finite checked block with integer weights at a fixed rational anchor.
The rows carry both exact rational endpoints and their scaled integer weights.
Primality and the numeric check certify all invariants; adjacent blocks can be
merged without rerunning numeric row checks or a global distinctness decision. -/
structure GammaScaledRampBlock (a : ℚ) (D lo hi : ℕ) where
  /-- Rational prime-power data paired with the exact scaled weight. -/
  rows : List (GammaFiniteRampRow × ℤ)
  /-- Prime bases, certified independently of the numeric check. -/
  primes : rows.Forall (fun rz ↦ rz.1.prime.Prime)
  /-- All row, interval, weight and distinctness checks succeed. -/
  checked : gammaScaledRampBlockCheck rows a D lo hi = true

/-- Input: any checked block.
Claim: its interval, numeric row and distinctness facts hold.
Proof: decode the finite decision. These facts drive balanced merging. -/
theorem GammaScaledRampBlock.facts {a : ℚ} {D lo hi : ℕ} (b : GammaScaledRampBlock a D lo hi) :
    lo ≤ hi ∧
      b.rows.Forall
        (fun rz ↦
          rz.1.check (2 * a) = true ∧
            (rz.2 : ℚ) = (D : ℚ) * (rz.1.logLower * rz.1.rampLower ^ 2) ∧
            lo < rz.1.index ∧ rz.1.index ≤ hi) ∧
      (b.rows.map (fun rz ↦ rz.1.index)).Nodup := by
  exact of_decide_eq_true b.checked

/-- Input: adjacent checked blocks.
Claim: every concatenated row satisfies the numeric facts on the union interval.
Proof: retain row facts and weaken only the two endpoint inequalities.
This is the row part of balanced certificate composition. -/
theorem GammaScaledRampBlock.append_rows_valid {a : ℚ} {D lo mid hi : ℕ}
    (l : GammaScaledRampBlock a D lo mid) (r : GammaScaledRampBlock a D mid hi) :
    (l.rows ++ r.rows).Forall
      (fun rz ↦
        rz.1.check (2 * a) = true ∧
          (rz.2 : ℚ) = (D : ℚ) * (rz.1.logLower * rz.1.rampLower ^ 2) ∧
          lo < rz.1.index ∧ rz.1.index ≤ hi) := by
  apply List.forall_iff_forall_mem.mpr
  intro rz hmem
  rcases List.mem_append.mp hmem with hl | hr
  · have h := List.forall_iff_forall_mem.mp l.facts.2.1 rz hl
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.trans r.facts.1⟩
  · have h := List.forall_iff_forall_mem.mp r.facts.2.1 rz hr
    exact ⟨h.1, h.2.1, lt_of_le_of_lt l.facts.1 h.2.2.1, h.2.2.2⟩

/-- Input: adjacent checked blocks.
Claim: their concatenated index list has no duplicates.
Proof: the left indices are at most mid and the right indices exceed mid.
This avoids a quadratic global distinctness check on the full payload. -/
theorem GammaScaledRampBlock.append_indices_nodup {a : ℚ} {D lo mid hi : ℕ}
    (l : GammaScaledRampBlock a D lo mid) (r : GammaScaledRampBlock a D mid hi) :
    ((l.rows ++ r.rows).map (fun rz ↦ rz.1.index)).Nodup := by
  rw [List.map_append]
  apply List.nodup_append.mpr
  refine ⟨l.facts.2.2, r.facts.2.2, ?_⟩
  intro i hi j hj heq
  obtain ⟨li, hli, rfl⟩ := List.mem_map.mp hi
  obtain ⟨rj, hrj, rfl⟩ := List.mem_map.mp hj
  have hl := (List.forall_iff_forall_mem.mp l.facts.2.1 li hli).2.2.2
  have hr := (List.forall_iff_forall_mem.mp r.facts.2.1 rj hrj).2.2.1
  exact (not_lt_of_ge (heq ▸ hl)) hr

/-- Input: two checked blocks on adjacent natural intervals.
Claim: their concatenation passes the combined numeric check.
Proof: weaken interval endpoints and derive distinctness from separation.
All expensive finite row checks are reused from the two input blocks. -/
theorem GammaScaledRampBlock.append_checked {a : ℚ} {D lo mid hi : ℕ}
    (l : GammaScaledRampBlock a D lo mid) (r : GammaScaledRampBlock a D mid hi) :
    gammaScaledRampBlockCheck (l.rows ++ r.rows) a D lo hi = true := by
  apply decide_eq_true
  exact ⟨l.facts.1.trans r.facts.1, l.append_rows_valid r, l.append_indices_nodup r⟩

/-- Merge adjacent checked blocks, retaining all row and integer-weight data.
The new primes come from the two lists and numeric validity from append_checked.
This supports balanced payload construction with constant-size merge proofs. -/
def GammaScaledRampBlock.append {a : ℚ} {D lo mid hi : ℕ} (l : GammaScaledRampBlock a D lo mid)
    (r : GammaScaledRampBlock a D mid hi) : GammaScaledRampBlock a D lo hi
    where
  rows := l.rows ++ r.rows
  primes := List.forall_append.mpr ⟨l.primes, r.primes⟩
  checked := l.append_checked r

/-- Input: a checked block starting at zero and a positive anchor.
Output: the existing reusable rational ramp certificate on its unweighted rows.
The integer weights are retained in the block for efficient moment evaluation. -/
def GammaScaledRampBlock.toCertificate {a : ℚ} {D hi : ℕ} (b : GammaScaledRampBlock a D 0 hi)
    (ha : 0 < a) : GammaReservedRampCertificate a := by
  refine ⟨b.rows.map Prod.fst, hi, ha, ?_, ?_, ?_, ?_⟩
  · apply List.forall_iff_forall_mem.mpr
    intro row hrow
    obtain ⟨rz, hz, rfl⟩ := List.mem_map.mp hrow
    exact List.forall_iff_forall_mem.mp b.primes rz hz
  · apply List.forall_iff_forall_mem.mpr
    intro row hrow
    obtain ⟨rz, hz, rfl⟩ := List.mem_map.mp hrow
    exact (List.forall_iff_forall_mem.mp b.facts.2.1 rz hz).1
  · simpa only [List.map_map, Function.comp_def] using b.facts.2.2
  · apply List.forall_iff_forall_mem.mpr
    intro row hrow
    obtain ⟨rz, hz, rfl⟩ := List.mem_map.mp hrow
    exact (List.forall_iff_forall_mem.mp b.facts.2.1 rz hz).2.2

end PseudoPrime.Analysis
