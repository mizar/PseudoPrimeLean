/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.UnitGenerationBalanced
public import Mathlib.Data.Nat.Bitwise

/-! # Compact product certificates for generation of finite unit groups -/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- Balanced bitwise union of 2^k natural bitsets starting at start.
The function f supplies each leaf. Balanced depth avoids a long linear
normalization stack in kernel-checked finite generation certificates. -/
def generationBitOr (f : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, start => f start
  | k + 1, start => generationBitOr f k start ||| generationBitOr f k (start + 2 ^ k)

/-- A set bit in the balanced union comes from some leaf.
Induct on the union depth and split the Boolean disjunction.
This is the support direction of the generation certificate soundness proof. -/
theorem generationBitOr_support {f : ℕ → ℕ} {k start r : ℕ}
    (h : (generationBitOr f k start).testBit r = true) : ∃ i : ℕ, (f i).testBit r = true := by
  induction k generalizing start with
  | zero => exact ⟨start, h⟩
  | succ k ih =>
    rw [generationBitOr, Nat.testBit_lor, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ih h
    · exact ih h

/-- A bit set in any leaf in the balanced interval is set in the union.
The bounds start ≤ i < start+2^k select the appropriate half recursively.
Use this to locate every unit residue in the canonical unit mask. -/
theorem generationBitOr_cover {f : ℕ → ℕ} {k start i r : ℕ} (hl : start ≤ i)
    (hu : i < start + 2 ^ k) (h : (f i).testBit r = true) :
    (generationBitOr f k start).testBit r = true := by
  induction k generalizing start with
  | zero =>
    have he : i = start := Nat.le_antisymm (Nat.le_of_lt_succ hu) hl
    subst i
    exact h
  | succ k ih =>
    rw [generationBitOr, Nat.testBit_lor, Bool.or_eq_true]
    by_cases hm : i < start + 2 ^ k
    · exact Or.inl (ih hl hm)
    · have hlow := Nat.le_of_not_gt hm
      have hsum : start + 2 ^ (k + 1) = (start + 2 ^ k) + 2 ^ k := by
        rw [pow_succ]
        ring
      exact Or.inr (ih hlow (hsum ▸ hu))

/-- Evaluate a mixed-radix product of small generators at index i.
Each row stores a natural generator p and digit radix d. The empty product
is one; modular ZMod powers use the existing arithmetic implementation.
Every value lies in any subgroup containing the row generators. -/
def generationProductValue (q : ℕ) : List (ℕ × ℕ) → ℕ → ZMod q
  | [], _ => 1
  | (p, d) :: rows, i => generationProductValue q rows (i / d) * (p : ZMod q) ^ (i % d)

/-- If every row generator has a unit representative in H, every mixed-radix
product also has one. Induct on rows and use subgroup closure under powers
and multiplication. Radix positivity and distinctness are not required:
the coverage checker independently verifies the final generation claim. -/
theorem generationProductValue_mem {q : ℕ} (H : Subgroup (ZMod q)ˣ) {rows : List (ℕ × ℕ)}
    (hrows : ∀ pd ∈ rows, ∃ v ∈ H, (v : ZMod q) = (pd.1 : ZMod q)) (i : ℕ) :
    ∃ v ∈ H, (v : ZMod q) = generationProductValue q rows i := by
  induction rows generalizing i with
  | nil => exact ⟨1, H.one_mem, rfl⟩
  | cons pd rows ih =>
    obtain ⟨v, hv, he⟩ := hrows pd (List.mem_cons_self)
    obtain ⟨u, hu, heu⟩ := ih (fun r hr ↦ hrows r (List.mem_cons_of_mem pd hr)) (i / pd.2)
    refine ⟨u * v ^ (i % pd.2), H.mul_mem hu (H.pow_mem hv _), ?_⟩
    simp only [generationProductValue, Units.val_mul, Units.val_pow_eq_pow_val, heu, he]

/-- Decode five 18-bit product rows. Each word is 64*d+p with p<64;
zero-radix padding is omitted. There is no assumption on decoded data:
the checker validates every prime label and the full unit mask. -/
def generationProductRows (code : ℕ) : List (ℕ × ℕ) :=
  ((List.range 5).map
        (fun j ↦
          let word := code / 262144 ^ j % 262144
          (word % 64, word / 64))).filter
    (fun pd ↦ pd.2 != 0)

/-- Bitset of product residues from indices below q in a depth-k interval.
Repeated products only set the same bit. Equality with the canonical unit
mask, rather than a heuristic size or hash comparison, certifies coverage. -/
def generationProductMask (q k : ℕ) (rows : List (ℕ × ℕ)) : ℕ :=
  generationBitOr (fun i ↦ if i < q then 2 ^ (generationProductValue q rows i).val else 0) k 0

/-- Canonical bitset of all unit representatives below q in a depth-k interval.
A leaf sets bit r exactly when r<q and gcd(r,q)=1. The soundness theorem
requires q≤2^k so every unit representative occurs. -/
def generationUnitMask (q k : ℕ) : ℕ :=
  generationBitOr (fun r ↦ if r < q ∧ Nat.Coprime r q then 2 ^ r else 0) k 0

/-- Validate prime labels, nondivisibility and cap for the decoded product rows,
then compare their exact product bitset with the canonical unit mask.
Only five small rows per modulus are stored; all coverage is checked inside Lean. -/
def generationProductCheck (q cap k code : ℕ) : Bool :=
  let rows := generationProductRows code
  rows.all
      (fun pd ↦ generationPrimeLabels.contains pd.1 && decide (¬pd.1 ∣ q) && decide (pd.1 ≤ cap)) &&
    decide (generationProductMask q k rows = generationUnitMask q k)

/-- At a nonzero q≤2^k, a successful product check forces any subgroup
containing all eligible prime residues through cap to be top.
The canonical mask supplies every unit bit, the product mask identifies a
mixed-radix value, and subgroup closure supplies the corresponding unit.
The generator and its proposed radices are not trusted. -/
theorem subgroup_eq_top_of_generationProductCheck {q cap k code : ℕ} [NeZero q]
    (hcheck : generationProductCheck q cap k code = true) (hq : q ≤ 2 ^ k) (H : Subgroup (ZMod q)ˣ)
    (hprime :
      ∀ p : ℕ, p.Prime → ¬p ∣ q → p ≤ cap → ∀ v : (ZMod q)ˣ, (v : ZMod q) = (p : ZMod q) → v ∈ H) :
    H = ⊤ := by
  have hb := Bool.and_eq_true_iff.mp hcheck
  have heq := of_decide_eq_true hb.2
  have hrows : ∀ pd ∈ generationProductRows code, ∃ v ∈ H, (v : ZMod q) = (pd.1 : ZMod q) := by
    intro pd hpd
    have hh := List.all_eq_true.mp hb.1 pd hpd
    have hs := Bool.and_eq_true_iff.mp hh
    have ht := Bool.and_eq_true_iff.mp hs.1
    have hp := generationPrimeLabels_prime (List.contains_iff_mem.mp ht.1)
    have hd := of_decide_eq_true ht.2
    let v := ZMod.unitOfCoprime pd.1 (hp.coprime_iff_not_dvd.mpr hd)
    have hv : (v : ZMod q) = (pd.1 : ZMod q) := ZMod.coe_unitOfCoprime _ _
    exact ⟨v, hprime pd.1 hp hd (of_decide_eq_true hs.2) v hv, hv⟩
  apply (Subgroup.eq_top_iff' H).mpr
  intro u
  let r := (u : ZMod q).val
  have hr : r < q := ZMod.val_lt _
  have hc : Nat.Coprime r q := by
    apply (ZMod.isUnit_iff_coprime r q).mp
    rw [ZMod.natCast_zmod_val]
    exact u.isUnit
  have hm : (generationUnitMask q k).testBit r = true := by
    apply
      generationBitOr_cover (Nat.zero_le r)
        (show r < 0 + 2 ^ k by simpa only [Nat.zero_add] using hr.trans_le hq)
    rw [ite_eq_left ⟨hr, hc⟩]
    exact Nat.testBit_two_pow_self
  have hg : (generationProductMask q k (generationProductRows code)).testBit r = true := by
    rw [heq]
    exact hm
  obtain ⟨i, hi⟩ := generationBitOr_support hg
  by_cases hiq : i < q
  · rw [ite_eq_left hiq, Nat.testBit_two_pow] at hi
    have he := of_decide_eq_true hi
    change (generationProductValue q (generationProductRows code) i).val = (u : ZMod q).val at he
    have heZ := congrArg (fun j : ℕ ↦ (j : ZMod q)) he
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at heZ
    obtain ⟨v, hv, hev⟩ := generationProductValue_mem H hrows i
    exact (Units.ext (hev.trans heZ)) ▸ hv
  · rw [ite_eq_right hiq, Nat.zero_testBit] at hi
    exact Bool.noConfusion hi

/-- At nonzero q≤2^k, a checked product certificate and a proper subgroup
give a prime not dividing q, at most cap, whose residue is outside the subgroup.
Negate the conclusion and apply the generation soundness theorem.
This is the finite algebraic input for small-modulus analytic bounds. -/
theorem exists_prime_outside_of_generationProductCheck {q cap k code : ℕ} [NeZero q]
    (hcheck : generationProductCheck q cap k code = true) (hq : q ≤ 2 ^ k) (H : Subgroup (ZMod q)ˣ)
    (hH : H ≠ ⊤) : ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ p ≤ cap ∧ ¬∃ v ∈ H, (v : ZMod q) = (p : ZMod q) := by
  by_contra hnone
  apply hH
  apply subgroup_eq_top_of_generationProductCheck hcheck hq H
  intro p hp hd hb u hu
  have hex : ∃ v ∈ H, (v : ZMod q) = (p : ZMod q) := by
    by_contra hh
    exact hnone ⟨p, hp, hd, hb, hh⟩
  obtain ⟨v, hv, hev⟩ := hex
  exact (Units.ext (hev.trans hu.symm)) ▸ hv

end PseudoPrime.NumberTheory
