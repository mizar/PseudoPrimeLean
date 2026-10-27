/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.Phase64EndpointFixedPoint
public import PseudoPrime.Analysis.NaturalIntervalBlocks

/-! # Compact aggregate caps for the endpoint computations -/

@[expose] public section

namespace PseudoPrime.Analysis.Phase64EndpointCertificates

/-- Natural lower caps for sixteen right-closed ramp blocks of width 256.
Each cap is an integer at scale 10^10; separate kernel checks validate every block. -/
def rampCaps : List ℕ :=
  [2330427600000, 2089652100000, 1706195100000, 1505345800000, 1233087700000, 1111155900000,
    992442300000, 746194300000, 701450800000, 598147600000, 533613500000, 405186400000,
    339735900000, 347441000000, 266546500000, 234285800000]

/-- Natural upper caps for thirty-two half-open principal blocks of width 1250.
Only aggregate caps are stored; all individual atoms are computed from proved definitions. -/
def principalCaps : List ℕ :=
  [8765351000000, 4113571000000, 1944821000000, 901047000000, 426605000000, 199657000000,
    96606000000, 44963000000, 20445000000, 9817000000, 4704000000, 2127000000, 1060000000,
    463000000, 222000000, 101000000, 50000000, 24000000, 12000000, 6000000, 3000000, 2000000,
    1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000]

/-- The lower-cap proposition for one ramp block. Summands are the executable
fixed-point lower atoms, with exact natural arithmetic. -/
def RampBlockValid (i : ℕ) : Prop :=
  rampCaps.getD i 0 ≤ ∑ n ∈ Finset.Ioc (256 * i) (256 * (i + 1)), phase64RampFixedLower n

/-- The principal block proposition checks all supported logarithms and an
upper bound for the computed natural atom sum. This also supplies global log checks. -/
def PrincipalBlockValid (i : ℕ) : Prop :=
  (∀ n ∈ Finset.Ico (1250 * i) (1250 * (i + 1)), phase64EndpointLogCheck n = true) ∧
    (∑ n ∈ Finset.Ico (1250 * i) (1250 * (i + 1)), phase64PrincipalFixedUpper n) ≤
      principalCaps.getD i 0

end PseudoPrime.Analysis.Phase64EndpointCertificates
