/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerPrimeBlocks
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerPrimeSplit

/-! # Complete prime-only Euler-center support -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Concatenate the ten checked prime blocks through 50000. The list keeps
the original ordering, and the next theorem certifies complete coverage.
This is the prime-only payload for the Euler-center finite sum. -/
def centerPrimes50000 : List ℕ :=
  (((((((((centerPrimeBlock0 ++ centerPrimeBlock1) ++ centerPrimeBlock2) ++ centerPrimeBlock3) ++
              centerPrimeBlock4) ++
            centerPrimeBlock5) ++
          centerPrimeBlock6) ++
        centerPrimeBlock7) ++
      centerPrimeBlock8) ++
    centerPrimeBlock9)

/-- The complete payload equals the fast-filtered interval list. Combine
the block certificates and exact adjacent-range concatenation identities.
No primality computation is repeated in this aggregation proof. -/
theorem centerPrimes50000_eq :
    centerPrimes50000 =
      (List.range' 0 50001).filter (fun n ↦ @decide n.Prime (Nat.decidablePrime' n)) := by
  rw [centerPrimes50000, centerPrimeBlock0_eq, centerPrimeBlock1_eq, centerPrimeBlock2_eq,
    centerPrimeBlock3_eq, centerPrimeBlock4_eq, centerPrimeBlock5_eq, centerPrimeBlock6_eq,
    centerPrimeBlock7_eq, centerPrimeBlock8_eq, centerPrimeBlock9_eq]
  simp only [← List.filter_append]
  rw [List.range'_append (s := 0) (m := 5000) (n := 5000) (step := 1),
    List.range'_append (s := 0) (m := 10000) (n := 5000) (step := 1),
    List.range'_append (s := 0) (m := 15000) (n := 5000) (step := 1),
    List.range'_append (s := 0) (m := 20000) (n := 5000) (step := 1),
    List.range'_append (s := 0) (m := 25000) (n := 5000) (step := 1),
    List.range'_append (s := 0) (m := 30000) (n := 5000) (step := 1),
    List.range'_append (s := 0) (m := 35000) (n := 5000) (step := 1),
    List.range'_append (s := 0) (m := 40000) (n := 5000) (step := 1),
    List.range'_append (s := 0) (m := 45000) (n := 5001) (step := 1)]

/-- The checked list represents precisely the prime finset through 50000.
Transfer the fast-filtered list to mathematical primality using the generic
membership bridge. This is the support equality for the actual prime sum. -/
theorem centerPrimes50000_finset :
    centerPrimes50000.toFinset = (Finset.Ico 0 50001).filter Nat.Prime :=
  (congrArg (fun l : List ℕ ↦ l.toFinset) centerPrimes50000_eq).trans
    (fast_prime_list_finset 0 50001)

end PseudoPrime.PrimeTestBounds.MillerRabin
