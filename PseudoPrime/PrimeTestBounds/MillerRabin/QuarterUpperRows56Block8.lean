/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWeightUpperCertificate

/-! # Principal upper rows at cutoff 56, block 8 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational upper-weight certificates for a block of prime powers. -/
def quarterUpperRows56Block8 : List QuarterUpperWeightRow :=
  [⟨56, 311, 2, 1713, 1716, 981, 985, 17635, 2667122026, 165⟩,
    ⟨56, 313, 2, 1719, 1722, 975, 979, 17691, 2651167204, 160⟩,
    ⟨56, 317, 3, 1732, 1735, 961, 965, 17804, 2614309472, 150⟩,
    ⟨56, 331, 3, 1775, 1778, 914, 918, 18193, 2494279720, 120⟩,
    ⟨56, 337, 3, 1793, 1796, 895, 899, 18357, 2447335783, 109⟩,
    ⟨56, 343, 3, 1811, 1814, 875, 880, 18520, 2398875286, 99⟩,
    ⟨56, 347, 3, 1822, 1825, 864, 868, 18627, 2372632262, 93⟩,
    ⟨56, 349, 3, 1828, 1831, 857, 861, 18681, 2356081830, 90⟩,
    ⟨56, 353, 3, 1840, 1843, 844, 848, 18788, 2325650995, 84⟩,
    ⟨56, 359, 3, 1856, 1859, 827, 831, 18947, 2286449089, 77⟩]

/-- Each listed row satisfies the rational upper-weight checks. -/
theorem quarter_upper_rows56_block8_check :
    quarterUpperRows56Block8.all QuarterUpperWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
