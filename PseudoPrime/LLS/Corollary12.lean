/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Corollary12AnalyticRoutes
public import PseudoPrime.LLS.Corollary12DivisorRoutes
public import PseudoPrime.LLS.ResidueRoutePartition
public import PseudoPrime.LLS.ResiduePrimeBounds
public import PseudoPrime.NumberTheory.TotientPrimeCountBounds

/-! GRH least-prime bounds for all reduced residues, including the finite range. -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Every modulus from four to 5699 occurs in an analytic or divisor route.
The kernel checks only lookup coverage; factor and prime certificates are shared
with their separately verified route trees. -/
private theorem reconstruction_routes_cover :
    (List.range 5696).all
        (fun i ↦
          residueRoutePartitionCheck Corollary12AnalyticRoutes.routes
            Corollary12DivisorRoutes.routes (4 + i)) =
      true := by
  decide +kernel

/-- For a modulus between four and 5699, checked analytic or divisor routes
produce a least prime below the squared totient-log bound under GRH.
The exhaustive lookup check chooses the route; its soundness supplies the bound. -/
private theorem leastPrime_of_lt_shared_lower {q : ℕ} [NeZero q] (hq : 4 ≤ q) (hu : q < 5700)
    (a : (ZMod q)ˣ) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      IsLeast {n : ℕ | n.Prime ∧ (n : ZMod q) = (a : ZMod q)} p ∧
        (p : ℝ) ≤ ((q.totient : ℝ) * Real.log q) ^ 2 := by
  have hc :=
    residueRoutePartitionCheck_of_all (lo := 4) (hi := 5700) reconstruction_routes_cover hq hu
  exact
    exists_least_prime_in_residue_le_of_route_partition Corollary12PrimeCatalog.catalog_checked
      Corollary12DirectCoverage.coreTree_checked Corollary12DivisorRoutes.routes_checked
      Corollary12AnalyticRoutes.routes_checked hc (Nat.le_trans (Nat.le_of_lt hu) (by decide)) a
      hGRH

/-- Under GRH, every unit residue at a modulus at least four has a least prime
at most `(φ(q) log q)²`. Below 5700 use checked analytic and divisor routes;
up to 20000 use the fifth shared interval and a bound of five prime factors;
for larger moduli use the uniform analytic estimate.
This is the complete estimate exported as Corollary 1.2. -/
theorem exists_least_prime_in_residue_le_totient_log_sq {q : ℕ} [NeZero q] (hq : 4 ≤ q)
    (a : (ZMod q)ˣ) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      IsLeast {n : ℕ | n.Prime ∧ (n : ZMod q) = (a : ZMod q)} p ∧
        (p : ℝ) ≤ ((q.totient : ℝ) * Real.log q) ^ 2 := by
  by_cases hlarge : 20000 ≤ q
  · exact exists_least_prime_in_residue_le_totient_log_sq_of_large a hlarge hGRH
  · have hu : q ≤ 20000 := Nat.le_of_lt (Nat.lt_of_not_ge hlarge)
    by_cases hshared : 5700 ≤ q
    · have hc : q.primeFactors.card ≤ 5 :=
        NumberTheory.primeFactors_card_le_five_of_lt_primorial_six (lt_of_le_of_lt hu (by decide))
      exact Corollary12Reconstruction.leastPrime5 a hshared hu hc hGRH
    · exact leastPrime_of_lt_shared_lower hq (Nat.lt_of_not_ge hshared) a hGRH

end PseudoPrime.LLS.PaperStatements
