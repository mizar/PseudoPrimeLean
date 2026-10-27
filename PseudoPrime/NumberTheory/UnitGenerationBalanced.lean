/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.UnitGenerationTree
public import Mathlib.Tactic.Ring

/-! # Balanced kernel checks for finite prime-generation certificates

Each Boolean leaf checks a residue; balanced recursion bounds normalization depth.
Twelve packed nodes occupy one integer block, keeping all data lines below 100 characters.
The soundness theorem supplies the existing algebraic generation contract.
-/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- The fixed prime labels through 81 used by small-modulus certificates.
Every label is prime. The following theorem checks this finite table once. -/
def generationPrimeLabels : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]

/-- Every member of the fixed label table is prime.
Reflect its finite prime check and extract the member's result.
This avoids repeating a primality decision at each tree node. -/
theorem generationPrimeLabels_prime {p : ℕ} (h : p ∈ generationPrimeLabels) : p.Prime := by
  have hall : (generationPrimeLabels.all fun r => decide r.Prime) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp hall p h)

/-- Check one residue at q and cap using Boolean arithmetic and the fixed prime table.
Nonunits and the identity need no edge. Other residues must have an eligible parent edge.
The local soundness theorem recovers each generation-tree invariant. -/
def generationFastNode (q cap : ℕ) (tree : ℕ → UnitGenerationNode) (r : ℕ) : Bool :=
  if Nat.gcd r q = 1 then
    if r = 1 then true
    else
      let node := tree r
      decide (node.parent < q) && decide (Nat.Coprime node.parent q) &&
        decide ((tree node.parent).depth < node.depth) &&
        generationPrimeLabels.contains node.prime &&
        decide (¬node.prime ∣ q) &&
        decide (node.prime ≤ cap) &&
        decide (node.parent * node.prime % q = r)
  else true

/-- For a coprime residue, a true local check gives the root or a valid parent edge.
Reflect each arithmetic guard and use the certified prime table.
This is the leaf argument for balanced finite verification. -/
theorem generationFastNode_sound {q cap r : ℕ} {tree : ℕ → UnitGenerationNode}
    (h : generationFastNode q cap tree r = true) (hc : Nat.Coprime r q) :
    r = 1 ∨
      (tree r).parent < q ∧
        Nat.Coprime (tree r).parent q ∧
        (tree (tree r).parent).depth < (tree r).depth ∧
        (tree r).prime.Prime ∧
        ¬(tree r).prime ∣ q ∧
        (tree r).prime ≤ cap ∧ ((tree r).parent * (tree r).prime) % q = r := by
  rw [generationFastNode, ite_eq_left hc] at h
  by_cases hr : r = 1
  · exact Or.inl hr
  rw [ite_eq_right hr] at h
  simp only [Bool.and_eq_true_iff] at h
  exact
    Or.inr
      ⟨of_decide_eq_true h.1.1.1.1.1.1, of_decide_eq_true h.1.1.1.1.1.2,
        of_decide_eq_true h.1.1.1.1.2,
        generationPrimeLabels_prime (List.contains_iff_mem.mp h.1.1.1.2), of_decide_eq_true h.1.1.2,
        of_decide_eq_true h.1.2, of_decide_eq_true h.2⟩

/-- Check residues in a power-of-two block of depth k starting at r.
Skip subblocks starting beyond q and split the others in half.
The balanced recursion supports kernel normalization of large finite certificates. -/
def generationFastBlock (q cap : ℕ) (tree : ℕ → UnitGenerationNode) : ℕ → ℕ → Bool
  | 0, r => if r < q then generationFastNode q cap tree r else true
  | k + 1, r =>
    if q ≤ r then true
    else generationFastBlock q cap tree k r && generationFastBlock q cap tree k (r + 2 ^ k)

/-- A true block check validates each residue within its interval and below q.
Induct on the depth and choose the half containing the residue.
This transfers the executable traversal to pointwise local checks. -/
theorem generationFastBlock_node {q cap k start r : ℕ} {tree : ℕ → UnitGenerationNode}
    (h : generationFastBlock q cap tree k start = true) (hl : start ≤ r) (hu : r < start + 2 ^ k)
    (hr : r < q) : generationFastNode q cap tree r = true := by
  induction k generalizing start with
  | zero =>
    have he : r = start := Nat.le_antisymm (Nat.le_of_lt_succ hu) hl
    subst r
    simpa only [generationFastBlock, ite_eq_left hr] using h
  | succ k ih =>
    have hsq : ¬q ≤ start := Nat.not_le_of_lt (hl.trans_lt hr)
    rw [generationFastBlock, ite_eq_right hsq] at h
    have hc := Bool.and_eq_true_iff.mp h
    by_cases hm : r < start + 2 ^ k
    · exact ih hc.1 hl hm
    · have hlow := Nat.le_of_not_gt hm
      have hsum : start + 2 ^ (k + 1) = (start + 2 ^ k) + 2 ^ k := by
        rw [pow_succ]; ring
      exact ih hc.2 hlow (hsum ▸ hu)

/-- A true root block covering q implies the generation-tree contract.
Apply the interval theorem to each representative in Fin q and the local soundness theorem.
The resulting contract feeds the subgroup-generation argument. -/
theorem generationFastBlock_sound {q cap k : ℕ} {tree : ℕ → UnitGenerationNode}
    (h : generationFastBlock q cap tree k 0 = true) (hq : q ≤ 2 ^ k) :
    UnitGenerationTreeValid q cap tree := by
  intro r hc
  have hnode :=
    generationFastBlock_node h (Nat.zero_le r.val)
      (show r.val < 0 + 2 ^ k by simpa only [Nat.zero_add] using r.isLt.trans_le hq) r.isLt
  exact generationFastNode_sound hnode hc

/-- Decode twelve 22-bit words from each natural-number block.
A word stores parent*1024+prime*8+depth; missing blocks may return zero.
Validity must still check every unit, independently of the certificate generator. -/
def unitGenerationTreeOfBlockBits (blocks : ℕ → ℕ) (r : ℕ) : UnitGenerationNode :=
  let word := blocks (r / 12) / 4194304 ^ (r % 12) % 4194304
  ⟨word / 1024, word / 8 % 128, word % 8⟩

/-- Evaluate a Boolean predicate on a power-of-two interval using balanced recursion.
Depth k and start r determine exactly 2^k consecutive inputs.
This combines neighboring modulus certificates without a large array traversal. -/
def generationBalancedAll (f : ℕ → Bool) : ℕ → ℕ → Bool
  | 0, r => f r
  | k + 1, r => generationBalancedAll f k r && generationBalancedAll f k (r + 2 ^ k)

/-- A true balanced interval check implies its predicate at every contained input.
Split the interval by its midpoint and induct on the depth.
This extracts the certificate for a requested modulus from a checked chunk. -/
theorem generationBalancedAll_sound {f : ℕ → Bool} {k start r : ℕ}
    (h : generationBalancedAll f k start = true) (hl : start ≤ r) (hu : r < start + 2 ^ k) :
    f r = true := by
  induction k generalizing start with
  | zero =>
    have he : r = start := Nat.le_antisymm (Nat.le_of_lt_succ hu) hl
    subst r
    exact h
  | succ k ih =>
    have hc := Bool.and_eq_true_iff.mp h
    by_cases hm : r < start + 2 ^ k
    · exact ih hc.1 hl hm
    · have hsum : start + 2 ^ (k + 1) = (start + 2 ^ k) + 2 ^ k := by
        rw [pow_succ]; ring
      exact ih hc.2 (Nat.le_of_not_gt hm) (hsum ▸ hu)

end PseudoPrime.NumberTheory
