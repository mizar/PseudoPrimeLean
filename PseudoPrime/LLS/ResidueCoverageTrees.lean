/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.CertificateTree
public import PseudoPrime.NumberTheory.PrimeTreeEnumeration
public import PseudoPrime.NumberTheory.PrimeBitmapCoverage
public import PseudoPrime.LLS.Corollary12Coverage

/-! Shared integer-bounded coverage and divisor routes for residue certificates. -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Check a positive modulus, integer cap and supplied divisor-level list using
a shared prime bitmap. Folding records capped prime residues; divisor masks
exclude only known nonunits. Neither divisor completeness nor primality is required. -/
def bitmapResidueCoverageEntryCheck (bits : ℕ) (e : (ℕ × ℕ) × List (ℕ × ℕ)) : Bool :=
  decide (0 < e.1.1) && NumberTheory.bitmapCoverageCheck bits e.1.1 e.1.2 e.2

/-- A sound prime bitmap and a passing entry check give bounded prime coverage.
The positivity check supplies the nonzero modulus instance; apply bitmap soundness.
This recovers the stored integer cap for the downstream divisor routes. -/
theorem bitmapResidueCoverageEntryCheck_bounded {bits : ℕ}
    (hp : ∀ p, bits.testBit p = true → p.Prime) {e : (ℕ × ℕ) × List (ℕ × ℕ)}
    (hc : bitmapResidueCoverageEntryCheck bits e = true) :
    NumberTheory.BoundedPrimeResidueCoverage e.1.1 e.1.2 := by
  rw [bitmapResidueCoverageEntryCheck, Bool.and_eq_true] at hc
  let : NeZero e.1.1 := ⟨Nat.ne_of_gt (of_decide_eq_true hc.1)⟩
  exact NumberTheory.bitmapCoverageCheck_bounded hp hc.2

/-- A successful lookup in a tree of checked coverage entries yields coverage
at the queried modulus with the stored integer cap. Lookup soundness identifies
the modulus and retrieves its bounded coverage proposition. This interface is
independent of the finite checker and retains the cap needed by divisor transfers. -/
theorem boundedPrimeResidueCoverage_of_tree_lookup {t : BinaryTree (ℕ × ℕ)} {q : ℕ} [NeZero q]
    {e : ℕ × ℕ}
    (ht :
      NumberTheory.certificateTreeForall (fun e ↦ NumberTheory.BoundedPrimeResidueCoverage e.1 e.2)
        t)
    (hl : NumberTheory.certificateTreeLookup Prod.fst t q = some e) :
    NumberTheory.BoundedPrimeResidueCoverage q e.2 := by
  obtain ⟨he, hc⟩ := NumberTheory.certificateTreeForall_lookup ht hl
  exact he ▸ hc

/-- Check a target-to-source modulus route against the direct coverage tree.
Lookup the source cap, require a target modulus at least four, a positive source,
divisibility and a cap below the target's integer bound. Direct coverage is the
special case where source and target coincide. -/
def residueDivisorRouteCheck (core : BinaryTree (ℕ × ℕ)) (e : ℕ × ℕ) : Bool :=
  match NumberTheory.certificateTreeLookup Prod.fst core e.2 with
  | none => false
  | some c => decide (4 ≤ e.1 ∧ e.1 ∣ e.2 ∧ 0 < e.2 ∧ c.2 ≤ residuePrimeCap e.1)

/-- Lookup in a checked route tree gives the least-prime bound at its target.
Retrieve the source's bounded coverage and transfer it to the target divisor;
the checked target cap implies the squared totient-log bound.
The shared prime and coverage proofs require no GRH for this finite step. -/
theorem exists_least_prime_in_residue_le_of_route_lookup {core routes : BinaryTree (ℕ × ℕ)}
    (hcore :
      NumberTheory.certificateTreeForall (fun e ↦ NumberTheory.BoundedPrimeResidueCoverage e.1 e.2)
        core)
    (hroutes : NumberTheory.certificateTreeAllCheck (residueDivisorRouteCheck core) routes = true)
    {q : ℕ} [NeZero q] {e : ℕ × ℕ}
    (hl : NumberTheory.certificateTreeLookup Prod.fst routes q = some e) (a : (ZMod q)ˣ) :
    ∃ p : ℕ,
      IsLeast {n : ℕ | n.Prime ∧ (n : ZMod q) = (a : ZMod q)} p ∧
        (p : ℝ) ≤ ((q.totient : ℝ) * Real.log q) ^ 2 := by
  rcases e with ⟨d, m⟩
  obtain ⟨he, hc⟩ := NumberTheory.certificateTreeAllCheck_lookup hroutes hl
  change d = q at he
  subst d
  cases hm : NumberTheory.certificateTreeLookup Prod.fst core m with
  | none => simp only [residueDivisorRouteCheck, hm, Bool.false_eq_true] at hc
  | some
    c =>
    have hg : 4 ≤ q ∧ q ∣ m ∧ 0 < m ∧ c.2 ≤ residuePrimeCap q :=
      of_decide_eq_true (by simpa only [residueDivisorRouteCheck, hm] using hc)
    let : NeZero m := ⟨Nat.ne_of_gt hg.2.2.1⟩
    exact
      exists_least_prime_in_residue_le_of_divisor_coverage hg.1 hg.2.1
        (boundedPrimeResidueCoverage_of_tree_lookup hcore hm) hg.2.2.2 a

end PseudoPrime.LLS.PaperStatements
