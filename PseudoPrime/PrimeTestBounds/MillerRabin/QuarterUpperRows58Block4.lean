/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWeightUpperCertificate

/-! # Upper principal rows at cutoff 58, block 4 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational weight certificates for a block of prime powers. -/
def quarterUpperRows58Block4 : List QuarterUpperWeightRow :=
  [⟨58, 421, 3, 1981, 1984, 692, 696, 20518, 1997706949, 34⟩,
    ⟨58, 431, 3, 2004, 2007, 667, 671, 20760, 1948383388, 29⟩,
    ⟨58, 433, 3, 2009, 2012, 662, 666, 20808, 1938665787, 28⟩,
    ⟨58, 439, 3, 2023, 2026, 646, 651, 20952, 1907893965, 25⟩,
    ⟨58, 443, 3, 2032, 2035, 637, 641, 21047, 1890799957, 23⟩,
    ⟨58, 449, 3, 2045, 2048, 623, 627, 21189, 1864513195, 21⟩,
    ⟨58, 457, 3, 2063, 2066, 603, 607, 21377, 1827593360, 18⟩,
    ⟨58, 461, 3, 2071, 2074, 595, 599, 21470, 1813030941, 17⟩,
    ⟨58, 463, 3, 2076, 2079, 589, 593, 21517, 1802185325, 16⟩,
    ⟨58, 467, 3, 2084, 2087, 581, 585, 21610, 1787825359, 15⟩,
    ⟨58, 479, 3, 2110, 2113, 552, 557, 21886, 1736722988, 12⟩,
    ⟨58, 487, 3, 2126, 2129, 535, 539, 22068, 1707448238, 11⟩,
    ⟨58, 491, 3, 2135, 2138, 525, 530, 22158, 1690458844, 10⟩,
    ⟨58, 499, 3, 2151, 2154, 508, 512, 22338, 1661963937, 8⟩,
    ⟨58, 503, 3, 2159, 2162, 500, 504, 22427, 1648721267, 8⟩,
    ⟨58, 509, 3, 2171, 2174, 487, 491, 22561, 1627426606, 7⟩,
    ⟨58, 512, 3, 2176, 2179, 481, 485, 22627, 1617691281, 7⟩,
    ⟨58, 521, 3, 2194, 2197, 462, 466, 22825, 1587245300, 6⟩,
    ⟨58, 523, 3, 2198, 2201, 457, 462, 22869, 1579328881, 5⟩,
    ⟨58, 529, 3, 2209, 2212, 446, 450, 23000, 1562051462, 5⟩,
    ⟨58, 541, 3, 2231, 2234, 422, 426, 23259, 1525008521, 4⟩,
    ⟨58, 547, 3, 2243, 2246, 409, 413, 23388, 1505311717, 3⟩,
    ⟨58, 557, 3, 2261, 2264, 389, 394, 23600, 1475504547, 3⟩,
    ⟨58, 563, 3, 2271, 2274, 379, 383, 23727, 1460823033, 2⟩,
    ⟨58, 569, 3, 2282, 2285, 367, 371, 23853, 1443397916, 2⟩]

/-- Each listed row satisfies its rational weight checks. -/
theorem quarter_upper_rows58_block4_check :
    quarterUpperRows58Block4.all QuarterUpperWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
