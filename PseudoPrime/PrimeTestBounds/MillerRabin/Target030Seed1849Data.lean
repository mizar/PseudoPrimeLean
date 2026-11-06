/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Seed373Count
public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedPrimeCountGroup

/-! # Additional prime labels through 1849 -/

@[expose] public section

set_option maxRecDepth 32768

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The 209 integers between 373 and 1849 selected as additional prime
labels, in decreasing order. -/
def target030Extra1849 : List ℕ :=
  [1847, 1831, 1823, 1811, 1801, 1789, 1787, 1783, 1777, 1759, 1753, 1747, 1741, 1733, 1723, 1721,
    1709, 1699, 1697, 1693, 1669, 1667, 1663, 1657, 1637, 1627, 1621, 1619, 1613, 1609, 1607, 1601,
    1597, 1583, 1579, 1571, 1567, 1559, 1553, 1549, 1543, 1531, 1523, 1511, 1499, 1493, 1489, 1487,
    1483, 1481, 1471, 1459, 1453, 1451, 1447, 1439, 1433, 1429, 1427, 1423, 1409, 1399, 1381, 1373,
    1367, 1361, 1327, 1321, 1319, 1307, 1303, 1301, 1297, 1291, 1289, 1283, 1279, 1277, 1259, 1249,
    1237, 1231, 1229, 1223, 1217, 1213, 1201, 1193, 1187, 1181, 1171, 1163, 1153, 1151, 1129, 1123,
    1117, 1109, 1103, 1097, 1093, 1091, 1087, 1069, 1063, 1061, 1051, 1049, 1039, 1033, 1031, 1021,
    1019, 1013, 1009, 997, 991, 983, 977, 971, 967, 953, 947, 941, 937, 929, 919, 911, 907, 887,
    883, 881, 877, 863, 859, 857, 853, 839, 829, 827, 823, 821, 811, 809, 797, 787, 773, 769, 761,
    757, 751, 743, 739, 733, 727, 719, 709, 701, 691, 683, 677, 673, 661, 659, 653, 647, 643, 641,
    631, 619, 617, 613, 607, 601, 599, 593, 587, 577, 571, 569, 563, 557, 547, 541, 523, 521, 509,
    503, 499, 491, 487, 479, 467, 463, 461, 457, 449, 443, 439, 433, 431, 421, 419, 409, 401, 397,
    389, 383, 379]

/-- The added labels followed by the previously certified supply through 373. -/
def target030Seed1849Primes : List ℕ :=
  target030Extra1849 ++ target030Seed373Primes

/-- The original weights are kept below 374; every added label has cost 76. -/
def target030Seed1849Weight (p : ℕ) : ℕ :=
  if p ≤ 373 then target030Seed373Weight p else 76

/-- The ordered weights use 209 copies of 76 for the additional labels. -/
def target030Seed1849Weights : List ℕ :=
  List.replicate 209 76 ++ target030Seed373Weights

end PseudoPrime.PrimeTestBounds.MillerRabin
