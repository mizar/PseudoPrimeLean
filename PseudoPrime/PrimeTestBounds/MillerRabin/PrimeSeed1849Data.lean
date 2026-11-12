/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.List.Basic

/-! # Additional prime labels through 1849 -/

@[expose] public section

set_option maxRecDepth 32768

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The 209 integers between 373 and 1849 selected as additional prime
labels, in decreasing order. -/
def primeSeed1849Extra : List ℕ :=
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
def primeSeed1849Primes : List ℕ :=
  primeSeed1849Extra ++
    ([373, 367, 359, 353, 349, 347, 337, 331, 317, 313, 311, 307, 293, 283] ++
      ([281, 277, 271, 269, 263, 257, 251, 241, 239, 233, 229, 227, 223, 211] ++
        ([199, 197, 193, 191, 181, 179, 173, 167, 163, 157, 151, 149, 139, 137, 131, 127] ++
          ([113, 109, 107, 103, 101, 97] ++
            ((([2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43]) ++ [47, 53, 59, 61]) ++
              [67, 71, 73, 79, 83, 89])))))

/-- The original weights are kept below 374; every added label has cost 76. -/
def primeSeed1849Weight (p : ℕ) : ℕ :=
  if p ≤ 373 then
    (if p ≤ 281 then
      (if p ≤ 199 then
        (if p ≤ 113 then
          (if p ≤ 89 then
            (if p ≤ 61 then
              (if p ≤ 43 then
                (if p ≤ 19 then
                  (if p ≤ 2 then 7
                  else
                    if p ≤ 3 then 11
                    else
                      if p ≤ 5 then 17
                      else if p ≤ 7 then 20 else if p ≤ 11 then 24 else if p ≤ 13 then 26 else 30)
                else if p ≤ 23 then 32 else if p ≤ 31 then 35 else 38)
              else if p ≤ 47 then 39 else if p ≤ 53 then 40 else if p ≤ 59 then 41 else 42)
            else if p ≤ 73 then 43 else if p ≤ 79 then 44 else 45)
          else if p ≤ 97 then 46 else if p ≤ 109 then 47 else 48)
        else
          if p ≤ 131 then 49
          else if p ≤ 139 then 50 else if p ≤ 163 then 51 else if p ≤ 181 then 52 else 53)
      else if p ≤ 211 then 54 else if p ≤ 241 then 55 else if p ≤ 269 then 56 else 57)
    else if p ≤ 293 then 57 else if p ≤ 317 then 58 else if p ≤ 359 then 59 else 60)
  else 76

/-- The ordered weights use 209 copies of 76 for the additional labels. -/
def primeSeed1849Weights : List ℕ :=
  List.replicate 209 76 ++
    ([60, 60, 59, 59, 59, 59, 59, 59, 58, 58, 58, 58, 57, 57] ++
      ([57, 57, 57, 56, 56, 56, 56, 55, 55, 55, 55, 55, 55, 54] ++
        ([53, 53, 53, 53, 52, 52, 52, 52, 51, 51, 51, 51, 50, 50, 49, 49] ++
          ([48, 47, 47, 47, 47, 46] ++
            ([7, 11, 17, 20, 24, 26, 30, 30, 32, 35, 35, 38, 38, 38, 39, 40, 41, 42, 43, 43, 43, 44,
              45, 45])))))

end PseudoPrime.PrimeTestBounds.MillerRabin
