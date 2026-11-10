/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWeightUpperCertificate

/-! # Principal upper rows at cutoff 56, block 11 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational upper-weight certificates for a block of prime powers. -/
def quarterUpperRows56Block11 : List QuarterUpperWeightRow :=
  [⟨56, 479, 3, 2145, 2148, 515, 519, 21886, 1673638497, 9⟩,
    ⟨56, 487, 3, 2161, 2164, 497, 502, 22068, 1643782515, 8⟩,
    ⟨56, 491, 3, 2170, 2173, 488, 492, 22158, 1629054846, 7⟩,
    ⟨56, 499, 3, 2186, 2189, 470, 475, 22338, 1599994191, 6⟩,
    ⟨56, 503, 3, 2194, 2197, 462, 466, 22427, 1587245300, 6⟩,
    ⟨56, 509, 3, 2206, 2209, 449, 453, 22561, 1566744652, 5⟩,
    ⟨56, 512, 3, 2211, 2214, 443, 448, 22627, 1557372330, 5⟩,
    ⟨56, 521, 3, 2229, 2232, 424, 428, 22825, 1528061590, 4⟩,
    ⟨56, 523, 3, 2233, 2236, 420, 424, 22869, 1521961553, 4⟩,
    ⟨56, 529, 3, 2244, 2247, 408, 412, 23000, 1503807158, 3⟩]

/-- Each listed row satisfies the rational upper-weight checks. -/
theorem quarter_upper_rows56_block11_check :
    quarterUpperRows56Block11.all QuarterUpperWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
