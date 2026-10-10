/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ResidueCoverageTrees
public import PseudoPrime.LLS.ResidueFactorRoutes

/-! Combine checked analytic and divisor routes for the finite modulus range. -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Check whether a modulus has an analytic factor route or a finite divisor route.
Only lookup is performed here; the two route trees are checked separately.
This separates exhaustive range coverage from the arithmetic in each route. -/
def residueRoutePartitionCheck (factorRoutes : BinaryTree (ℕ × List ℕ))
    (divisorRoutes : BinaryTree (ℕ × ℕ)) (q : ℕ) : Bool :=
  match NumberTheory.certificateTreeLookup Prod.fst factorRoutes q with
  | some _ => true
  | none => (NumberTheory.certificateTreeLookup Prod.fst divisorRoutes q).isSome

/-- Checked route trees and a successful partition check give the least-prime bound.
Assume GRH and a modulus at most 20000. Select the analytic route when present;
otherwise transfer checked finite coverage from the divisor route's source.
This joins the two branches before the public Corollary 1.2 proof. -/
theorem exists_least_prime_in_residue_le_of_route_partition {primes : BinaryTree ℕ}
    (hp : NumberTheory.primeTreeChecked primes) {core divisorRoutes : BinaryTree (ℕ × ℕ)}
    {factorRoutes : BinaryTree (ℕ × List ℕ)}
    (hcore :
      NumberTheory.certificateTreeForall (fun e ↦ NumberTheory.BoundedPrimeResidueCoverage e.1 e.2)
        core)
    (hdiv :
      NumberTheory.certificateTreeAllCheck (residueDivisorRouteCheck core) divisorRoutes = true)
    (hfac :
      NumberTheory.certificateTreeAllCheck (residueFactorRouteCheck primes) factorRoutes = true)
    {q : ℕ} [NeZero q] (hc : residueRoutePartitionCheck factorRoutes divisorRoutes q = true)
    (hu : q ≤ 20000) (a : (ZMod q)ˣ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      IsLeast {n : ℕ | n.Prime ∧ (n : ZMod q) = (a : ZMod q)} p ∧
        (p : ℝ) ≤ ((q.totient : ℝ) * Real.log q) ^ 2 := by
  cases hf : NumberTheory.certificateTreeLookup Prod.fst factorRoutes q with
  | some e => exact exists_least_prime_in_residue_le_of_factor_route_lookup hp hfac hf hu a hGRH
  | none =>
    cases hd : NumberTheory.certificateTreeLookup Prod.fst divisorRoutes q with
    | some e => exact exists_least_prime_in_residue_le_of_route_lookup hcore hdiv hd a
    | none =>
      simp only [residueRoutePartitionCheck, hf, hd, Option.isSome_none, Bool.false_eq_true] at hc

/-- A passing lookup check for every offset covers every modulus in the interval.
Given `lo ≤ q < hi`, select offset `q - lo` in the checked list and recover `q`.
This converts the closed finite partition check into a reusable range theorem. -/
theorem residueRoutePartitionCheck_of_all {f : BinaryTree (ℕ × List ℕ)} {d : BinaryTree (ℕ × ℕ)}
    {lo hi q : ℕ}
    (hc : (List.range (hi - lo)).all (fun i ↦ residueRoutePartitionCheck f d (lo + i)) = true)
    (hl : lo ≤ q) (hu : q < hi) : residueRoutePartitionCheck f d q = true := by
  have hm : q - lo ∈ List.range (hi - lo) := List.mem_range.mpr (Nat.sub_lt_sub_right hl hu)
  have hv := List.all_eq_true.mp hc (q - lo) hm
  exact Nat.add_sub_of_le hl ▸ hv

end PseudoPrime.LLS.PaperStatements
