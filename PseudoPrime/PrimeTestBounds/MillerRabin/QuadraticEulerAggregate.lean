/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowBlock0
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowBlock250
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowBlock500
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowBlock750
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowBlock1000
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowBlock1250
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowBlock1500
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowBlock1750
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowBlock2000
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowBlock2250
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowBlock2500
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowBlock2750
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowBlock3000
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowBlock3250
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowBlock3500
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowBlock3750
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowBlock4000
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowBlock4250
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowBlock4500
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowBlock4750
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowBlock5000
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerPrimeSupport
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerHigherData
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowSum

/-! # Exact support matching for all finite Euler-center rows -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

set_option maxRecDepth 40000

/-- Concatenate the independently checked numerical blocks. The ordering is
by the prime-power value; the support theorem below identifies it with the
separate prime and higher-power payloads. -/
noncomputable def centerRows50000 : List EulerCenterRow :=
  centerRows0 ++ centerRows250 ++ centerRows500 ++ centerRows750 ++ centerRows1000 ++
    centerRows1250 ++
    centerRows1500 ++
    centerRows1750 ++
    centerRows2000 ++
    centerRows2250 ++
    centerRows2500 ++
    centerRows2750 ++
    centerRows3000 ++
    centerRows3250 ++
    centerRows3500 ++
    centerRows3750 ++
    centerRows4000 ++
    centerRows4250 ++
    centerRows4500 ++
    centerRows4750 ++
    centerRows5000

/-- Filtering the row indices at exponent one gives exactly the prime
support in its original order. Kernel reduction checks natural-number
indices independently of the numerical endpoint certificates. -/
theorem centerRows50000_prime_indices :
    (centerRows50000.map (fun r ↦ (r.p, r.k))).filter (fun x ↦ x.2 == 0) =
      centerPrimes50000.map (fun p ↦ (p, 0)) := by
  decide +kernel

/-- The 84 higher-power indices permute to the independent support payload.
Kernel evaluation checks multiplicities despite their different orderings. -/
theorem centerRows50000_higher_indices :
    ((centerRows50000.map (fun r ↦ (r.p, r.k))).filter (fun x ↦ !(x.2 == 0))).Perm
      centerHigherPowers := by
  decide +kernel

/-- The numerical rows contain precisely the independently certified support,
with the same multiplicities. Partition by exponent one, then combine the
prime equality and higher-power permutation. This connects rows to support. -/
theorem centerRows50000_index_perm :
    (centerRows50000.map (fun r ↦ (r.p, r.k))).Perm
      ((centerPrimes50000.map (fun p ↦ (p, 0))) ++ centerHigherPowers) := by
  have hh := centerRows50000_higher_indices
  have h :=
    List.filter_append_perm (fun x : ℕ × ℕ ↦ x.2 == 0) (centerRows50000.map (fun r ↦ (r.p, r.k)))
  exact
    h.symm.trans
      ((List.Perm.refl _).append hh |>.trans (centerRows50000_prime_indices ▸ List.Perm.refl _))

end PseudoPrime.PrimeTestBounds.MillerRabin
