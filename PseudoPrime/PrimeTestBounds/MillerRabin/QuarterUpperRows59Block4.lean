/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWeightUpperCertificate

/-! # Upper principal rows at cutoff 59, block 4 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational weight certificates for a block of prime powers. -/
def quarterUpperRows59Block4 : List QuarterUpperWeightRow :=
  [⟨59, 421, 3, 1964, 1967, 710, 714, 20518, 2033991254, 38⟩,
    ⟨59, 431, 3, 1987, 1990, 685, 690, 20760, 1983771832, 32⟩,
    ⟨59, 433, 3, 1992, 1995, 680, 684, 20808, 1973877727, 31⟩,
    ⟨59, 439, 3, 2005, 2008, 666, 670, 20952, 1946435979, 28⟩,
    ⟨59, 443, 3, 2015, 2018, 655, 659, 21047, 1925142513, 26⟩,
    ⟨59, 449, 3, 2028, 2031, 641, 645, 21189, 1898378304, 24⟩,
    ⟨59, 457, 3, 2046, 2049, 622, 626, 21377, 1862649614, 21⟩,
    ⟨59, 461, 3, 2054, 2057, 613, 617, 21470, 1845960979, 19⟩,
    ⟨59, 463, 3, 2059, 2062, 608, 612, 21517, 1836754210, 19⟩,
    ⟨59, 467, 3, 2067, 2070, 599, 603, 21610, 1820297586, 17⟩,
    ⟨59, 479, 3, 2093, 2096, 571, 575, 21886, 1770036198, 14⟩,
    ⟨59, 487, 3, 2109, 2112, 554, 558, 22068, 1740199910, 12⟩,
    ⟨59, 491, 3, 2117, 2120, 545, 549, 22158, 1724608377, 11⟩,
    ⟨59, 499, 3, 2134, 2137, 527, 531, 22338, 1693843145, 10⟩,
    ⟨59, 503, 3, 2142, 2145, 518, 522, 22427, 1678666952, 9⟩,
    ⟨59, 509, 3, 2153, 2156, 506, 510, 22561, 1658643331, 8⟩,
    ⟨59, 512, 3, 2159, 2162, 500, 504, 22627, 1648721267, 8⟩,
    ⟨59, 521, 3, 2177, 2180, 480, 484, 22825, 1616074398, 7⟩,
    ⟨59, 523, 3, 2181, 2184, 476, 480, 22869, 1609623013, 6⟩,
    ⟨59, 529, 3, 2192, 2195, 464, 468, 23000, 1590422967, 6⟩,
    ⟨59, 541, 3, 2214, 2217, 440, 444, 23259, 1552707215, 4⟩,
    ⟨59, 547, 3, 2225, 2228, 428, 432, 23388, 1534186077, 4⟩,
    ⟨59, 557, 3, 2244, 2247, 408, 412, 23600, 1503807158, 3⟩,
    ⟨59, 563, 3, 2254, 2257, 397, 401, 23727, 1487355926, 3⟩,
    ⟨59, 569, 3, 2265, 2268, 385, 389, 23853, 1469614318, 3⟩]

/-- Each listed row satisfies its rational weight checks. -/
theorem quarter_upper_rows59_block4_check :
    quarterUpperRows59Block4.all QuarterUpperWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
