/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Phase64EndpointFixedPoint
public import PseudoPrime.Analysis.NaturalIntervalBlocks

/-! # Compact aggregate caps for the endpoint computations -/

@[expose] public section

namespace PseudoPrime.LLS.Phase64EndpointCertificates

/-- Natural lower caps for sixteen right-closed ramp blocks of width 256.
Each cap is an integer at scale 10^10; separate kernel checks validate every block. -/
def rampCaps : ℕ → ℕ
  | 0 => 2330427600000
  | 1 => 2089652100000
  | 2 => 1706195100000
  | 3 => 1505345800000
  | 4 => 1233087700000
  | 5 => 1111155900000
  | 6 => 992442300000
  | 7 => 746194300000
  | 8 => 701450800000
  | 9 => 598147600000
  | 10 => 533613500000
  | 11 => 405186400000
  | 12 => 339735900000
  | 13 => 347441000000
  | 14 => 266546500000
  | 15 => 234285800000
  | _ => 0

/-- Natural upper caps for thirty-two half-open principal blocks of width 1250.
Only aggregate caps are stored; all individual atoms are computed from proved definitions. -/
def principalCaps : ℕ → ℕ
  | 0 => 8765351000000
  | 1 => 4113571000000
  | 2 => 1944821000000
  | 3 => 901047000000
  | 4 => 426605000000
  | 5 => 199657000000
  | 6 => 96606000000
  | 7 => 44963000000
  | 8 => 20445000000
  | 9 => 9817000000
  | 10 => 4704000000
  | 11 => 2127000000
  | 12 => 1060000000
  | 13 => 463000000
  | 14 => 222000000
  | 15 => 101000000
  | 16 => 50000000
  | 17 => 24000000
  | 18 => 12000000
  | 19 => 6000000
  | 20 => 3000000
  | 21 => 2000000
  | 22 => 1000000
  | 23 => 1000000
  | 24 => 1000000
  | 25 => 1000000
  | 26 => 1000000
  | 27 => 1000000
  | 28 => 1000000
  | 29 => 1000000
  | 30 => 1000000
  | 31 => 1000000
  | _ => 0

/-- The lower-cap proposition for one ramp block. Summands are the executable
fixed-point lower atoms, with exact natural arithmetic. -/
def RampBlockValid (i : ℕ) : Prop :=
  rampCaps i ≤ ∑ n ∈ Finset.Ioc (256 * i) (256 * (i + 1)), phase64RampFixedLower n

/-- The principal block proposition checks all supported logarithms and an
upper bound for the computed natural atom sum. This also supplies global log checks. -/
def PrincipalBlockValid (i : ℕ) : Prop :=
  (∀ n ∈ Finset.Ico (1250 * i) (1250 * (i + 1)), phase64EndpointLogCheck n = true) ∧
    (∑ n ∈ Finset.Ico (1250 * i) (1250 * (i + 1)), phase64PrincipalFixedUpper n) ≤ principalCaps i

end PseudoPrime.LLS.Phase64EndpointCertificates
