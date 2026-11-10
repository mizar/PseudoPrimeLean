/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWeightUpperCertificate

/-! # Principal upper rows at cutoff 56, block 5 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational upper-weight certificates for a block of prime powers. -/
def quarterUpperRows56Block5 : List QuarterUpperWeightRow :=
  [⟨56, 163, 2, 1067, 1070, 1679, 1683, 12767, 5360193086, 1645⟩,
    ⟨56, 167, 2, 1091, 1094, 1653, 1657, 12922, 5222624213, 1543⟩,
    ⟨56, 169, 2, 1103, 1106, 1640, 1644, 13000, 5155169505, 1494⟩,
    ⟨56, 173, 2, 1126, 1129, 1615, 1619, 13152, 5027887916, 1402⟩,
    ⟨56, 179, 2, 1161, 1164, 1577, 1582, 13379, 4840412760, 1276⟩,
    ⟨56, 181, 2, 1172, 1175, 1566, 1570, 13453, 4787459995, 1235⟩,
    ⟨56, 191, 2, 1225, 1228, 1508, 1512, 13820, 4517686374, 1055⟩,
    ⟨56, 193, 2, 1236, 1239, 1496, 1501, 13892, 4463798113, 1024⟩,
    ⟨56, 197, 2, 1256, 1259, 1475, 1479, 14035, 4371035767, 962⟩,
    ⟨56, 199, 2, 1266, 1269, 1464, 1468, 14106, 4323217853, 932⟩]

/-- Each listed row satisfies the rational upper-weight checks. -/
theorem quarter_upper_rows56_block5_check :
    quarterUpperRows56Block5.all QuarterUpperWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
