/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaScaledRampEvaluation

/-! # Certified cached integer moments for repeated ramp evaluations -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: a checked block and a cutoff no greater than its lower endpoint.
Claim: its integer prefix moment vanishes.
Proof: every represented index is strictly above the cutoff.
This avoids inspecting any row of a block entirely outside the prefix. -/
theorem GammaScaledRampBlock.prefix_zero {a : ℚ} {D lo hi : ℕ} (b : GammaScaledRampBlock a D lo hi)
    {bound : ℕ} (h : bound ≤ lo) (k : ℕ) : gammaScaledIntegerPrefix b.rows bound k = 0 := by
  have hf : b.rows.filter (fun rz ↦ decide (rz.1.index ≤ bound)) = [] :=
    List.filter_eq_nil_iff.mpr
      (fun rz hz hc ↦
        (not_le_of_gt (h.trans_lt (List.forall_iff_forall_mem.mp b.facts.2.1 rz hz).2.2.1))
          (of_decide_eq_true hc))
  simp only [gammaScaledIntegerPrefix, hf, List.map_nil, List.sum_nil]

/-- Input: a checked block and a cutoff at least its upper endpoint.
Claim: its prefix equals the complete block moment.
Proof: every index lies below both cutoffs, so both filters keep all rows.
This permits reuse of a single certified complete moment. -/
theorem GammaScaledRampBlock.prefix_full {a : ℚ} {D lo hi : ℕ} (b : GammaScaledRampBlock a D lo hi)
    {bound : ℕ} (h : hi ≤ bound) (k : ℕ) :
    gammaScaledIntegerPrefix b.rows bound k = gammaScaledIntegerPrefix b.rows hi k := by
  have hf (v : ℕ) (hv : hi ≤ v) : b.rows.filter (fun rz ↦ decide (rz.1.index ≤ v)) = b.rows :=
    List.filter_eq_self.mpr
      (fun rz hz ↦
        decide_eq_true (((List.forall_iff_forall_mem.mp b.facts.2.1 rz hz).2.2.2).trans hv))
  simp only [gammaScaledIntegerPrefix, hf bound h, hf hi le_rfl]

/-- A checked block tree with a finite cache of complete moments at each leaf.
A leaf's stored integer values are checked against exact sums once. Nodes retain
adjacency. Moment indices beyond a leaf cache use the original exact evaluator.
This representation supports arbitrary prefix cutoffs and moment orders. -/
inductive GammaCachedRampTree (a : ℚ) (D : ℕ) : ℕ → ℕ → Type where
  /-- A checked row block and its certified complete integer moments. -/
  |
  leaf {lo hi : ℕ} (b : GammaScaledRampBlock a D lo hi) (moments : List (ℕ × ℤ))
    (checked : moments.Forall (fun p ↦ p.2 = gammaScaledIntegerPrefix b.rows hi p.1)) :
    GammaCachedRampTree a D lo hi
  /-- Two cached trees on adjacent intervals. -/
  |
  node {lo mid hi : ℕ} (l : GammaCachedRampTree a D lo mid) (r : GammaCachedRampTree a D mid hi) :
    GammaCachedRampTree a D lo hi

/-- Forget cached values, retaining the same proof-carrying row tree. -/
def GammaCachedRampTree.tree {a : ℚ} {D lo hi : ℕ} (t : GammaCachedRampTree a D lo hi) :
    GammaScaledRampTree a D lo hi :=
  match t with
  | .leaf b _ _ => .leaf b
  | .node l r => .node l.tree r.tree

/-- Exact prefix evaluation with complete moments cached at leaves.
Blocks above the cutoff contribute zero; complete blocks use a stored moment.
Only boundary blocks or uncached moment orders inspect their rows. -/
def GammaCachedRampTree.prefixMoment {a : ℚ} {D lo hi : ℕ} (t : GammaCachedRampTree a D lo hi)
    (bound k : ℕ) : ℤ :=
  match t with
  | .leaf (lo := lower) (hi := upper) b moments _ =>
    if bound ≤ lower then 0
    else
      if upper ≤ bound then
        match moments.find? (fun p ↦ p.1 == k) with
        | some p => p.2
        | none => gammaScaledIntegerPrefix b.rows bound k
      else gammaScaledIntegerPrefix b.rows bound k
  | .node l r => l.prefixMoment bound k + r.prefixMoment bound k

/-- Input: any cached tree, prefix cutoff and moment order.
Claim: cached evaluation equals the original exact integer evaluation.
Proof: induct on the tree and use the zero/full block identities.
The cached values affect performance without changing the mathematical value. -/
theorem GammaCachedRampTree.prefixMoment_eq {a : ℚ} {D lo hi : ℕ}
    (t : GammaCachedRampTree a D lo hi) (bound k : ℕ) :
    t.prefixMoment bound k = t.tree.prefixMoment bound k := by
  induction t with
  | leaf b moments
    checked =>
    dsimp only [GammaCachedRampTree.prefixMoment, GammaCachedRampTree.tree,
      GammaScaledRampTree.prefixMoment]
    split
    · rename_i h
      exact (b.prefix_zero h k).symm
    · split
      · rename_i h
        split
        · rename_i p hp
          have hm : p ∈ moments := by
            obtain ⟨_, as, bs, hs, _⟩ := List.find?_eq_some_iff_append.mp hp
            rw [hs]
            exact List.mem_append_right _ (List.mem_cons_self ..)
          have hk : p.1 = k := by
            have hkp := (List.find?_eq_some_iff_append.mp hp).1
            exact beq_iff_eq.mp hkp
          have he := List.forall_iff_forall_mem.mp checked p hm
          rw [hk] at he
          exact he.trans (b.prefix_full h k).symm
        · rfl
      · rfl
  | node l r il ir => exact congrArg₂ (fun u v : ℤ ↦ u + v) il ir

/-- The ramp moment computed from the cached integer prefix evaluator.
All constants and rational divisions agree with the original moment formula. -/
def GammaCachedRampTree.rampMoment {a : ℚ} {D lo hi : ℕ} (t : GammaCachedRampTree a D lo hi) (x : ℚ)
    (k : ℕ) : ℚ :=
  let P := fun (c : ℚ) (j : ℕ) ↦ (t.prefixMoment ⌊c * x⌋₊ j : ℚ) / (D : ℚ)
  P (247 / 100) k +
    ((99 / 40) * (P (99 / 40) k - P (247 / 100) k) -
        (P (99 / 40) (k + 1) - P (247 / 100) (k + 1)) / x) /
      (1 / 200)

/-- The transported lower polynomial evaluated with certified cached moments.
The target and Taylor term count are arbitrary; no extra analytic hypothesis is used. -/
def GammaCachedRampTree.rampLower {a : ℚ} {D lo hi : ℕ} (t : GammaCachedRampTree a D lo hi) (x : ℚ)
    (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, (1 / a - 1 / x) ^ k / (k.factorial : ℚ) * t.rampMoment x k

/-- Input: any cached tree, target and Taylor term count.
Claim: the cached lower evaluation equals the original exact lower polynomial.
Proof: substitute equality of every integer prefix in the finite sum.
This gives the existing witness interfaces a faster interchangeable evaluation. -/
theorem GammaCachedRampTree.rampLower_eq {a : ℚ} {D lo hi : ℕ} (t : GammaCachedRampTree a D lo hi)
    (x : ℚ) (n : ℕ) : t.rampLower x n = t.tree.rampLower x n := by
  simp only [GammaCachedRampTree.rampLower, GammaScaledRampTree.rampLower,
    GammaCachedRampTree.rampMoment, GammaScaledRampTree.rampMoment, t.prefixMoment_eq]

end PseudoPrime.LLS
