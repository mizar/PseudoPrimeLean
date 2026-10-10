/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements
public import Mathlib.Tactic.NormNum.LegendreSymbol

/-! Kernel-checkable bounded certificates for LLS Corollary 1.1. -/

@[expose] public section

namespace PseudoPrime.LLS

-- set_option linter.style.setOption false
-- set_option profiler true

/-- Natural cap for the finite nonresidue witness, chosen below a certified
logarithmic-square bound in each interval. -/
def smallNonresidueCap (q : ℕ) : ℕ :=
  if q < 7 then 3 else if q < 23 then 4 else if q < 311 then 8 else 18

/-- A finite list of modulus and nonresidue pairs is checked by positivity,
the interval cap, and its Jacobi symbol. No primality is required for this predicate. -/
def nonresidueTableChecked (table : List (ℕ × ℕ)) : Prop :=
  ∀ e ∈ table, 0 < e.2 ∧ e.2 < smallNonresidueCap e.1 ∧ jacobiSym e.2 e.1 = -1

/-- Appending two checked tables preserves every witness condition. -/
theorem nonresidueTableChecked_append {a b : List (ℕ × ℕ)} (ha : nonresidueTableChecked a)
    (hb : nonresidueTableChecked b) : nonresidueTableChecked (a ++ b) := fun e he ↦
  Or.elim (List.mem_append.mp he) (ha e) (hb e)

/-- A positive Jacobi witness below the finite interval cap. -/
def smallNonresidueAt (q : ℕ) : Prop :=
  ∃ n : ℕ, 0 < n ∧ n < smallNonresidueCap q ∧ jacobiSym n q = -1

/-- A sixteen-modulus interval has a positive Jacobi witness below its cap
for every prime between 5 and 2999. -/
def smallNonresidueBlockChecked (b : ℕ) : Prop :=
  ∀ k : Fin 16,
    5 ≤ 16 * b + k.val →
      16 * b + k.val < 3000 → (16 * b + k.val).Prime → smallNonresidueAt (16 * b + k.val)

/-- Concatenate two consecutive finite collections of certified intervals.
Associativity identifies the offset in the second collection. -/
theorem smallNonresidueBlockGroups_append {s m n : ℕ}
    (ha : ∀ b : Fin m, smallNonresidueBlockChecked (s + b.val))
    (hb : ∀ b : Fin n, smallNonresidueBlockChecked (s + m + b.val)) :
    ∀ b : Fin (m + n), smallNonresidueBlockChecked (s + b.val) :=
  Fin.addCases ha
    (fun b ↦ Eq.mp (congrArg smallNonresidueBlockChecked (Nat.add_assoc s m b.val)) (hb b))

/-- Compare naturals through truncated subtraction, keeping kernel reduction
independent of the common magnitude of the two arguments. -/
def nonresidueNatLe (a b : ℕ) : Bool :=
  a - b == 0

/-- The subtraction check is equivalent to the natural order relation. -/
theorem nonresidueNatLe_iff {a b : ℕ} : nonresidueNatLe a b = true ↔ a ≤ b := by
  simp only [nonresidueNatLe, beq_iff_eq, Nat.sub_eq_zero_iff_le]

/-- Compare table entries using subtraction for their potentially large moduli. -/
def nonresidueEntryEq (a b : ℕ × ℕ) : Bool :=
  nonresidueNatLe a.1 b.1 && nonresidueNatLe b.1 a.1 && (a.2 == b.2)

/-- A successful table-entry comparison is exactly equality of its two components. -/
theorem nonresidueEntryEq_iff {a b : ℕ × ℕ} : nonresidueEntryEq a b = true ↔ a = b := by
  simp only [nonresidueEntryEq, Bool.and_eq_true, nonresidueNatLe_iff, beq_iff_eq,
    ← le_antisymm_iff, Prod.ext_iff]

/-- Searching a table with the subtraction comparison is equivalent to membership. -/
theorem nonresidueEntryMem_iff {a : ℕ × ℕ} {table : List (ℕ × ℕ)} :
    table.any (nonresidueEntryEq a) = true ↔ a ∈ table :=
  List.any_eq_true.trans
    ⟨fun ⟨_e, he, hae⟩ ↦ (nonresidueEntryEq_iff.mp hae).symm ▸ he, fun ha ↦
      ⟨a, ha, nonresidueEntryEq_iff.mpr rfl⟩⟩

/-- A Boolean check of table membership or an explicit proper divisor,
restricted to the moduli in one sixteen-integer interval. -/
def nonresidueCoverageCheck (b : ℕ) (table data : List (ℕ × ℕ)) : Bool :=
  (List.range 16).all fun k ↦
    let q := 16 * b + k
    let e := data.getD k (0, 0)
    (!(nonresidueNatLe 5 q && nonresidueNatLe (q + 1) 3000)) ||
      table.any (nonresidueEntryEq (q, e.1)) ||
      (nonresidueNatLe 2 e.2 && nonresidueNatLe (e.2 + 1) q && (q % e.2 == 0))

/-- A successful Boolean coverage check gives table membership or a proper divisor
for each eligible modulus. This reflection lemma is shared by every finite block. -/
theorem nonresidueCoverageCheck_sound {b : ℕ} {table data : List (ℕ × ℕ)}
    (h : nonresidueCoverageCheck b table data = true) :
    ∀ k : Fin 16,
      5 ≤ 16 * b + k.val →
        16 * b + k.val < 3000 →
        (16 * b + k.val, (data.getD k.val (0, 0)).1) ∈ table ∨
          (2 ≤ (data.getD k.val (0, 0)).2 ∧
            (data.getD k.val (0, 0)).2 < 16 * b + k.val ∧
            (data.getD k.val (0, 0)).2 ∣ 16 * b + k.val) := by
  intro k h5 hlt
  have hk := List.all_eq_true.mp h k.val (List.mem_range.mpr k.isLt)
  simpa only [Nat.succ_le_iff, nonresidueNatLe_iff.mpr h5,
    nonresidueNatLe_iff.mpr (Nat.succ_le_of_lt hlt), Bool.and_true, Bool.not_true, Bool.false_or,
    Bool.or_eq_true, nonresidueEntryMem_iff, Bool.and_eq_true, nonresidueNatLe_iff, beq_iff_eq,
    ← Nat.dvd_iff_mod_eq_zero, and_assoc] using hk

-- BEGIN GENERATED NONRESIDUE TABLES
/-- Candidate nonresidues in certificate block 0. -/
def nonresidueTable0 : List (ℕ × ℕ) :=
  [(5, 2), (7, 3), (11, 2), (13, 2), (17, 3), (19, 2), (23, 5), (29, 2), (31, 3), (37, 2), (41, 3),
    (43, 2), (47, 5), (53, 2), (59, 2), (61, 2)]

/-- Positivity, interval caps, and Jacobi symbols for block 0,
verified by arithmetic normalization and Jacobi reciprocity. -/
theorem nonresidueTable0_checked : nonresidueTableChecked nonresidueTable0 := by
  norm_num only [nonresidueTableChecked, nonresidueTable0, List.mem_cons, List.not_mem_nil,
    forall_eq_or_imp, smallNonresidueCap]
  simp only [ite_true, and_true, true_and, ite_false, false_implies, forall_const]
  norm_num only
  trivial

/-- Candidate nonresidues in certificate block 1. -/
def nonresidueTable1 : List (ℕ × ℕ) :=
  [(67, 2), (71, 7), (73, 5), (79, 3), (83, 2), (89, 3), (97, 5), (101, 2), (103, 3), (107, 2),
    (109, 2), (113, 3), (127, 3), (131, 2), (137, 3), (139, 2)]

/-- Positivity, interval caps, and Jacobi symbols for block 1,
verified by arithmetic normalization and Jacobi reciprocity. -/
theorem nonresidueTable1_checked : nonresidueTableChecked nonresidueTable1 := by
  norm_num only [nonresidueTableChecked, nonresidueTable1, List.mem_cons, List.not_mem_nil,
    forall_eq_or_imp, smallNonresidueCap]
  simp only [ite_true, and_true, true_and, ite_false, false_implies, forall_const]
  norm_num only
  trivial

/-- Candidate nonresidues in certificate block 2. -/
def nonresidueTable2 : List (ℕ × ℕ) :=
  [(149, 2), (151, 3), (157, 2), (163, 2), (167, 5), (173, 2), (179, 2), (181, 2), (191, 7),
    (193, 5), (197, 2), (199, 3), (211, 2), (223, 3), (227, 2), (229, 2)]

/-- Positivity, interval caps, and Jacobi symbols for block 2,
verified by arithmetic normalization and Jacobi reciprocity. -/
theorem nonresidueTable2_checked : nonresidueTableChecked nonresidueTable2 := by
  norm_num only [nonresidueTableChecked, nonresidueTable2, List.mem_cons, List.not_mem_nil,
    forall_eq_or_imp, smallNonresidueCap]
  simp only [ite_true, and_true, true_and, ite_false, false_implies, forall_const]
  norm_num only
  trivial

/-- Candidate nonresidues in certificate block 3. -/
def nonresidueTable3 : List (ℕ × ℕ) :=
  [(233, 3), (239, 7), (241, 7), (251, 2), (257, 3), (263, 5), (269, 2), (271, 3), (277, 2),
    (281, 3), (283, 2), (293, 2), (307, 2), (311, 11), (313, 5), (317, 2)]

/-- Positivity, interval caps, and Jacobi symbols for block 3,
verified by arithmetic normalization and Jacobi reciprocity. -/
theorem nonresidueTable3_checked : nonresidueTableChecked nonresidueTable3 := by
  norm_num only [nonresidueTableChecked, nonresidueTable3, List.mem_cons, List.not_mem_nil,
    forall_eq_or_imp, smallNonresidueCap]
  simp only [ite_true, and_true, true_and, ite_false, false_implies, forall_const]
  norm_num only
  trivial

/-- Candidate nonresidues in certificate block 4. -/
def nonresidueTable4 : List (ℕ × ℕ) :=
  [(331, 2), (337, 5), (347, 2), (349, 2), (353, 3), (359, 7), (367, 3), (373, 2), (379, 2),
    (383, 5), (389, 2), (397, 2), (401, 3), (409, 7), (419, 2), (421, 2)]

/-- Positivity, interval caps, and Jacobi symbols for block 4,
verified by arithmetic normalization and Jacobi reciprocity. -/
theorem nonresidueTable4_checked : nonresidueTableChecked nonresidueTable4 := by
  norm_num only [nonresidueTableChecked, nonresidueTable4, List.mem_cons, List.not_mem_nil,
    forall_eq_or_imp, smallNonresidueCap]
  simp only [and_true, true_and, ite_false, false_implies, forall_const]
  norm_num only
  trivial

/-- Candidate nonresidues in certificate block 5. -/
def nonresidueTable5 : List (ℕ × ℕ) :=
  [(431, 7), (433, 5), (439, 3), (443, 2), (449, 3), (457, 5), (461, 2), (463, 3), (467, 2),
    (479, 13), (487, 3), (491, 2), (499, 2), (503, 5), (509, 2), (521, 3)]

/-- Positivity, interval caps, and Jacobi symbols for block 5,
verified by arithmetic normalization and Jacobi reciprocity. -/
theorem nonresidueTable5_checked : nonresidueTableChecked nonresidueTable5 := by
  norm_num only [nonresidueTableChecked, nonresidueTable5, List.mem_cons, List.not_mem_nil,
    forall_eq_or_imp, smallNonresidueCap]
  simp only [and_true, true_and, ite_false, false_implies, forall_const]
  norm_num only
  trivial

/-- Candidate nonresidues in certificate block 6. -/
def nonresidueTable6 : List (ℕ × ℕ) :=
  [(523, 2), (541, 2), (547, 2), (557, 2), (563, 2), (569, 3), (571, 2), (577, 5), (587, 2),
    (593, 3), (599, 7), (601, 7), (607, 3), (613, 2), (617, 3), (619, 2)]

/-- Positivity, interval caps, and Jacobi symbols for block 6,
verified by arithmetic normalization and Jacobi reciprocity. -/
theorem nonresidueTable6_checked : nonresidueTableChecked nonresidueTable6 := by
  norm_num only [nonresidueTableChecked, nonresidueTable6, List.mem_cons, List.not_mem_nil,
    forall_eq_or_imp, smallNonresidueCap]
  simp only [and_true, true_and, ite_false, false_implies, forall_const]
  norm_num only
  trivial

/-- Candidate nonresidues in certificate block 7. -/
def nonresidueTable7 : List (ℕ × ℕ) :=
  [(631, 3), (641, 3), (643, 2), (647, 5), (653, 2), (659, 2), (661, 2), (673, 5), (677, 2),
    (683, 2), (691, 2), (701, 2), (709, 2), (719, 11), (727, 3), (733, 2)]

/-- Positivity, interval caps, and Jacobi symbols for block 7,
verified by arithmetic normalization and Jacobi reciprocity. -/
theorem nonresidueTable7_checked : nonresidueTableChecked nonresidueTable7 := by
  norm_num only [nonresidueTableChecked, nonresidueTable7, List.mem_cons, List.not_mem_nil,
    forall_eq_or_imp, smallNonresidueCap]
  simp only [and_true, true_and, ite_false, false_implies, forall_const]
  norm_num only
  trivial

/-- Candidate nonresidues in certificate block 8. -/
def nonresidueTable8 : List (ℕ × ℕ) :=
  [(739, 2), (743, 5), (751, 3), (757, 2), (761, 3), (769, 7), (773, 2), (787, 2), (797, 2),
    (809, 3), (811, 2), (821, 2), (823, 3), (827, 2), (829, 2), (839, 11)]

/-- Positivity, interval caps, and Jacobi symbols for block 8,
verified by arithmetic normalization and Jacobi reciprocity. -/
theorem nonresidueTable8_checked : nonresidueTableChecked nonresidueTable8 := by
  norm_num only [nonresidueTableChecked, nonresidueTable8, List.mem_cons, List.not_mem_nil,
    forall_eq_or_imp, smallNonresidueCap]
  simp only [and_true, true_and, ite_false, false_implies, forall_const]
  norm_num only
  trivial

/-- Candidate nonresidues in certificate block 9. -/
def nonresidueTable9 : List (ℕ × ℕ) :=
  [(853, 2), (857, 3), (859, 2), (863, 5), (877, 2), (881, 3), (883, 2), (887, 5), (907, 2),
    (911, 7), (919, 3), (929, 3), (937, 5), (941, 2), (947, 2), (953, 3)]

/-- Positivity, interval caps, and Jacobi symbols for block 9,
verified by arithmetic normalization and Jacobi reciprocity. -/
theorem nonresidueTable9_checked : nonresidueTableChecked nonresidueTable9 := by
  norm_num only [nonresidueTableChecked, nonresidueTable9, List.mem_cons, List.not_mem_nil,
    forall_eq_or_imp, smallNonresidueCap]
  simp only [and_true, true_and, ite_false, false_implies, forall_const]
  norm_num only
  trivial

/-- Candidate nonresidues in certificate block 10. -/
def nonresidueTable10 : List (ℕ × ℕ) :=
  [(967, 3), (971, 2), (977, 3), (983, 5), (991, 3), (997, 2), (1009, 11), (1013, 2), (1019, 2),
    (1021, 2), (1031, 7), (1033, 5), (1039, 3), (1049, 3), (1051, 2), (1061, 2)]

/-- Positivity, interval caps, and Jacobi symbols for block 10,
verified by arithmetic normalization and Jacobi reciprocity. -/
theorem nonresidueTable10_checked : nonresidueTableChecked nonresidueTable10 := by
  norm_num only [nonresidueTableChecked, nonresidueTable10, List.mem_cons, List.not_mem_nil,
    forall_eq_or_imp, smallNonresidueCap]
  simp only [and_true, true_and, ite_false, false_implies, forall_const]
  norm_num only
  trivial

/-- Candidate nonresidues in certificate block 11. -/
def nonresidueTable11 : List (ℕ × ℕ) :=
  [(1063, 3), (1069, 2), (1087, 3), (1091, 2), (1093, 2), (1097, 3), (1103, 5), (1109, 2),
    (1117, 2), (1123, 2), (1129, 11), (1151, 13), (1153, 5), (1163, 2), (1171, 2), (1181, 2)]

/-- Positivity, interval caps, and Jacobi symbols for block 11,
verified by arithmetic normalization and Jacobi reciprocity. -/
theorem nonresidueTable11_checked : nonresidueTableChecked nonresidueTable11 := by
  norm_num only [nonresidueTableChecked, nonresidueTable11, List.mem_cons, List.not_mem_nil,
    forall_eq_or_imp, smallNonresidueCap]
  simp only [and_true, true_and, ite_false, false_implies, forall_const]
  norm_num only
  trivial

/-- Candidate nonresidues in certificate block 12. -/
def nonresidueTable12 : List (ℕ × ℕ) :=
  [(1187, 2), (1193, 3), (1201, 11), (1213, 2), (1217, 3), (1223, 5), (1229, 2), (1231, 3),
    (1237, 2), (1249, 7), (1259, 2), (1277, 2), (1279, 3), (1283, 2), (1289, 3), (1291, 2)]

/-- Positivity, interval caps, and Jacobi symbols for block 12,
verified by arithmetic normalization and Jacobi reciprocity. -/
theorem nonresidueTable12_checked : nonresidueTableChecked nonresidueTable12 := by
  norm_num only [nonresidueTableChecked, nonresidueTable12, List.mem_cons, List.not_mem_nil,
    forall_eq_or_imp, smallNonresidueCap]
  simp only [and_true, true_and, ite_false, false_implies, forall_const]
  norm_num only
  trivial

/-- Candidate nonresidues in certificate block 13. -/
def nonresidueTable13 : List (ℕ × ℕ) :=
  [(1297, 5), (1301, 2), (1303, 3), (1307, 2), (1319, 13), (1321, 7), (1327, 3), (1361, 3),
    (1367, 5), (1373, 2), (1381, 2), (1399, 3), (1409, 3), (1423, 3), (1427, 2), (1429, 2)]

/-- Positivity, interval caps, and Jacobi symbols for block 13,
verified by arithmetic normalization and Jacobi reciprocity. -/
theorem nonresidueTable13_checked : nonresidueTableChecked nonresidueTable13 := by
  norm_num only [nonresidueTableChecked, nonresidueTable13, List.mem_cons, List.not_mem_nil,
    forall_eq_or_imp, smallNonresidueCap]
  simp only [and_true, true_and, ite_false, false_implies, forall_const]
  norm_num only
  trivial

/-- Candidate nonresidues in certificate block 14. -/
def nonresidueTable14 : List (ℕ × ℕ) :=
  [(1433, 3), (1439, 7), (1447, 3), (1451, 2), (1453, 2), (1459, 2), (1471, 3), (1481, 3),
    (1483, 2), (1487, 5), (1489, 7), (1493, 2), (1499, 2), (1511, 11), (1523, 2), (1531, 2)]

/-- Positivity, interval caps, and Jacobi symbols for block 14,
verified by arithmetic normalization and Jacobi reciprocity. -/
theorem nonresidueTable14_checked : nonresidueTableChecked nonresidueTable14 := by
  norm_num only [nonresidueTableChecked, nonresidueTable14, List.mem_cons, List.not_mem_nil,
    forall_eq_or_imp, smallNonresidueCap]
  simp only [and_true, true_and, ite_false, false_implies, forall_const]
  norm_num only
  trivial

/-- Candidate nonresidues in certificate block 15. -/
def nonresidueTable15 : List (ℕ × ℕ) :=
  [(1543, 3), (1549, 2), (1553, 3), (1559, 17), (1567, 3), (1571, 2), (1579, 2), (1583, 5),
    (1597, 2), (1601, 3), (1607, 5), (1609, 7), (1613, 2), (1619, 2), (1621, 2), (1627, 2)]

/-- Positivity, interval caps, and Jacobi symbols for block 15,
verified by arithmetic normalization and Jacobi reciprocity. -/
theorem nonresidueTable15_checked : nonresidueTableChecked nonresidueTable15 := by
  norm_num only [nonresidueTableChecked, nonresidueTable15, List.mem_cons, List.not_mem_nil,
    forall_eq_or_imp, smallNonresidueCap]
  simp only [and_true, true_and, ite_false, false_implies, forall_const]
  norm_num only
  trivial

/-- Candidate nonresidues in certificate block 16. -/
def nonresidueTable16 : List (ℕ × ℕ) :=
  [(1637, 2), (1657, 5), (1663, 3), (1667, 2), (1669, 2), (1693, 2), (1697, 3), (1699, 2),
    (1709, 2), (1721, 3), (1723, 2), (1733, 2), (1741, 2), (1747, 2), (1753, 5), (1759, 3)]

/-- Positivity, interval caps, and Jacobi symbols for block 16,
verified by arithmetic normalization and Jacobi reciprocity. -/
theorem nonresidueTable16_checked : nonresidueTableChecked nonresidueTable16 := by
  norm_num only [nonresidueTableChecked, nonresidueTable16, List.mem_cons, List.not_mem_nil,
    forall_eq_or_imp, smallNonresidueCap]
  simp only [and_true, true_and, ite_false, false_implies, forall_const]
  norm_num only
  trivial

/-- Candidate nonresidues in certificate block 17. -/
def nonresidueTable17 : List (ℕ × ℕ) :=
  [(1777, 5), (1783, 3), (1787, 2), (1789, 2), (1801, 11), (1811, 2), (1823, 5), (1831, 3),
    (1847, 5), (1861, 2), (1867, 2), (1871, 7), (1873, 5), (1877, 2), (1879, 3), (1889, 3)]

/-- Positivity, interval caps, and Jacobi symbols for block 17,
verified by arithmetic normalization and Jacobi reciprocity. -/
theorem nonresidueTable17_checked : nonresidueTableChecked nonresidueTable17 := by
  norm_num only [nonresidueTableChecked, nonresidueTable17, List.mem_cons, List.not_mem_nil,
    forall_eq_or_imp, smallNonresidueCap]
  simp only [and_true, true_and, ite_false, false_implies, forall_const]
  norm_num only
  trivial

/-- Candidate nonresidues in certificate block 18. -/
def nonresidueTable18 : List (ℕ × ℕ) :=
  [(1901, 2), (1907, 2), (1913, 3), (1931, 2), (1933, 2), (1949, 2), (1951, 3), (1973, 2),
    (1979, 2), (1987, 2), (1993, 5), (1997, 2), (1999, 3), (2003, 2), (2011, 2), (2017, 5)]

/-- Positivity, interval caps, and Jacobi symbols for block 18,
verified by arithmetic normalization and Jacobi reciprocity. -/
theorem nonresidueTable18_checked : nonresidueTableChecked nonresidueTable18 := by
  norm_num only [nonresidueTableChecked, nonresidueTable18, List.mem_cons, List.not_mem_nil,
    forall_eq_or_imp, smallNonresidueCap]
  simp only [and_true, true_and, ite_false, false_implies, forall_const]
  norm_num only
  trivial

/-- Candidate nonresidues in certificate block 19. -/
def nonresidueTable19 : List (ℕ × ℕ) :=
  [(2027, 2), (2029, 2), (2039, 7), (2053, 2), (2063, 5), (2069, 2), (2081, 3), (2083, 2),
    (2087, 5), (2089, 7), (2099, 2), (2111, 7), (2113, 5), (2129, 3), (2131, 2), (2137, 5)]

/-- Positivity, interval caps, and Jacobi symbols for block 19,
verified by arithmetic normalization and Jacobi reciprocity. -/
theorem nonresidueTable19_checked : nonresidueTableChecked nonresidueTable19 := by
  norm_num only [nonresidueTableChecked, nonresidueTable19, List.mem_cons, List.not_mem_nil,
    forall_eq_or_imp, smallNonresidueCap]
  simp only [and_true, true_and, ite_false, false_implies, forall_const]
  norm_num only
  trivial

/-- Candidate nonresidues in certificate block 20. -/
def nonresidueTable20 : List (ℕ × ℕ) :=
  [(2141, 2), (2143, 3), (2153, 3), (2161, 7), (2179, 2), (2203, 2), (2207, 5), (2213, 2),
    (2221, 2), (2237, 2), (2239, 3), (2243, 2), (2251, 2), (2267, 2), (2269, 2), (2273, 3)]

/-- Positivity, interval caps, and Jacobi symbols for block 20,
verified by arithmetic normalization and Jacobi reciprocity. -/
theorem nonresidueTable20_checked : nonresidueTableChecked nonresidueTable20 := by
  norm_num only [nonresidueTableChecked, nonresidueTable20, List.mem_cons, List.not_mem_nil,
    forall_eq_or_imp, smallNonresidueCap]
  simp only [and_true, true_and, ite_false, false_implies, forall_const]
  norm_num only
  trivial

/-- Candidate nonresidues in certificate block 21. -/
def nonresidueTable21 : List (ℕ × ℕ) :=
  [(2281, 7), (2287, 3), (2293, 2), (2297, 3), (2309, 2), (2311, 3), (2333, 2), (2339, 2),
    (2341, 2), (2347, 2), (2351, 13), (2357, 2), (2371, 2), (2377, 5), (2381, 2), (2383, 3)]

/-- Positivity, interval caps, and Jacobi symbols for block 21,
verified by arithmetic normalization and Jacobi reciprocity. -/
theorem nonresidueTable21_checked : nonresidueTableChecked nonresidueTable21 := by
  norm_num only [nonresidueTableChecked, nonresidueTable21, List.mem_cons, List.not_mem_nil,
    forall_eq_or_imp, smallNonresidueCap]
  simp only [and_true, true_and, ite_false, false_implies, forall_const]
  norm_num only
  trivial

/-- Candidate nonresidues in certificate block 22. -/
def nonresidueTable22 : List (ℕ × ℕ) :=
  [(2389, 2), (2393, 3), (2399, 11), (2411, 2), (2417, 3), (2423, 5), (2437, 2), (2441, 3),
    (2447, 5), (2459, 2), (2467, 2), (2473, 5), (2477, 2), (2503, 3), (2521, 11), (2531, 2)]

/-- Positivity, interval caps, and Jacobi symbols for block 22,
verified by arithmetic normalization and Jacobi reciprocity. -/
theorem nonresidueTable22_checked : nonresidueTableChecked nonresidueTable22 := by
  norm_num only [nonresidueTableChecked, nonresidueTable22, List.mem_cons, List.not_mem_nil,
    forall_eq_or_imp, smallNonresidueCap]
  simp only [and_true, true_and, ite_false, false_implies, forall_const]
  norm_num only
  trivial

/-- Candidate nonresidues in certificate block 23. -/
def nonresidueTable23 : List (ℕ × ℕ) :=
  [(2539, 2), (2543, 5), (2549, 2), (2551, 3), (2557, 2), (2579, 2), (2591, 7), (2593, 5),
    (2609, 3), (2617, 5), (2621, 2), (2633, 3), (2647, 3), (2657, 3), (2659, 2), (2663, 5)]

/-- Positivity, interval caps, and Jacobi symbols for block 23,
verified by arithmetic normalization and Jacobi reciprocity. -/
theorem nonresidueTable23_checked : nonresidueTableChecked nonresidueTable23 := by
  norm_num only [nonresidueTableChecked, nonresidueTable23, List.mem_cons, List.not_mem_nil,
    forall_eq_or_imp, smallNonresidueCap]
  simp only [and_true, true_and, ite_false, false_implies, forall_const]
  norm_num only
  trivial

/-- Candidate nonresidues in certificate block 24. -/
def nonresidueTable24 : List (ℕ × ℕ) :=
  [(2671, 3), (2677, 2), (2683, 2), (2687, 5), (2689, 13), (2693, 2), (2699, 2), (2707, 2),
    (2711, 7), (2713, 5), (2719, 3), (2729, 3), (2731, 2), (2741, 2), (2749, 2), (2753, 3)]

/-- Positivity, interval caps, and Jacobi symbols for block 24,
verified by arithmetic normalization and Jacobi reciprocity. -/
theorem nonresidueTable24_checked : nonresidueTableChecked nonresidueTable24 := by
  norm_num only [nonresidueTableChecked, nonresidueTable24, List.mem_cons, List.not_mem_nil,
    forall_eq_or_imp, smallNonresidueCap]
  simp only [and_true, true_and, ite_false, false_implies, forall_const]
  norm_num only
  trivial

/-- Candidate nonresidues in certificate block 25. -/
def nonresidueTable25 : List (ℕ × ℕ) :=
  [(2767, 3), (2777, 3), (2789, 2), (2791, 3), (2797, 2), (2801, 3), (2803, 2), (2819, 2),
    (2833, 5), (2837, 2), (2843, 2), (2851, 2), (2857, 5), (2861, 2), (2879, 7), (2887, 3)]

/-- Positivity, interval caps, and Jacobi symbols for block 25,
verified by arithmetic normalization and Jacobi reciprocity. -/
theorem nonresidueTable25_checked : nonresidueTableChecked nonresidueTable25 := by
  norm_num only [nonresidueTableChecked, nonresidueTable25, List.mem_cons, List.not_mem_nil,
    forall_eq_or_imp, smallNonresidueCap]
  simp only [and_true, true_and, ite_false, false_implies, forall_const]
  norm_num only
  trivial

/-- Candidate nonresidues in certificate block 26. -/
def nonresidueTable26 : List (ℕ × ℕ) :=
  [(2897, 3), (2903, 5), (2909, 2), (2917, 2), (2927, 5), (2939, 2), (2953, 5), (2957, 2),
    (2963, 2), (2969, 3), (2971, 2), (2999, 17)]

/-- Positivity, interval caps, and Jacobi symbols for block 26,
verified by arithmetic normalization and Jacobi reciprocity. -/
theorem nonresidueTable26_checked : nonresidueTableChecked nonresidueTable26 := by
  norm_num only [nonresidueTableChecked, nonresidueTable26, List.mem_cons, List.not_mem_nil,
    forall_eq_or_imp, smallNonresidueCap]
  simp only [and_true, true_and, ite_false, false_implies, forall_const]
  norm_num only
  trivial

/-- Witnesses or proper divisors for the sixteen integers beginning at 0.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData0 : List (ℕ × ℕ) :=
  [(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (2, 0), (0, 2), (3, 0), (0, 2), (0, 3), (0, 2), (2, 0),
    (0, 2), (2, 0), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 0 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock0 :
    ∀ k : Fin 16,
      5 ≤ 16 * 0 + k.val →
        16 * 0 + k.val < 3000 →
        (16 * 0 + k.val, (nonresidueCoverageData0.getD k.val (0, 0)).1) ∈ (nonresidueTable0) ∨
          (2 ≤ (nonresidueCoverageData0.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData0.getD k.val (0, 0)).2 < 16 * 0 + k.val ∧
            (nonresidueCoverageData0.getD k.val (0, 0)).2 ∣ 16 * 0 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 0 (nonresidueTable0) nonresidueCoverageData0 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 0,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock0_checked : smallNonresidueBlockChecked 0 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock0 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData0.getD k.val (0, 0)).1,
        nonresidueTable0_checked (16 * 0 + k.val, (nonresidueCoverageData0.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 16.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData1 : List (ℕ × ℕ) :=
  [(0, 2), (3, 0), (0, 2), (2, 0), (0, 2), (0, 3), (0, 2), (5, 0), (0, 2), (0, 5), (0, 2), (0, 3),
    (0, 2), (2, 0), (0, 2), (3, 0)]

/-- Every eligible integer beginning at 16 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock1 :
    ∀ k : Fin 16,
      5 ≤ 16 * 1 + k.val →
        16 * 1 + k.val < 3000 →
        (16 * 1 + k.val, (nonresidueCoverageData1.getD k.val (0, 0)).1) ∈ (nonresidueTable0) ∨
          (2 ≤ (nonresidueCoverageData1.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData1.getD k.val (0, 0)).2 < 16 * 1 + k.val ∧
            (nonresidueCoverageData1.getD k.val (0, 0)).2 ∣ 16 * 1 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 1 (nonresidueTable0) nonresidueCoverageData1 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 16,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock1_checked : smallNonresidueBlockChecked 1 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock1 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData1.getD k.val (0, 0)).1,
        nonresidueTable0_checked (16 * 1 + k.val, (nonresidueCoverageData1.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 32.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData2 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (0, 5), (0, 2), (2, 0), (0, 2), (0, 3), (0, 2), (3, 0), (0, 2), (2, 0),
    (0, 2), (0, 3), (0, 2), (5, 0)]

/-- Every eligible integer beginning at 32 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock2 :
    ∀ k : Fin 16,
      5 ≤ 16 * 2 + k.val →
        16 * 2 + k.val < 3000 →
        (16 * 2 + k.val, (nonresidueCoverageData2.getD k.val (0, 0)).1) ∈ (nonresidueTable0) ∨
          (2 ≤ (nonresidueCoverageData2.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData2.getD k.val (0, 0)).2 < 16 * 2 + k.val ∧
            (nonresidueCoverageData2.getD k.val (0, 0)).2 ∣ 16 * 2 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 2 (nonresidueTable0) nonresidueCoverageData2 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 32,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock2_checked : smallNonresidueBlockChecked 2 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock2 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData2.getD k.val (0, 0)).1,
        nonresidueTable0_checked (16 * 2 + k.val, (nonresidueCoverageData2.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 48.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData3 : List (ℕ × ℕ) :=
  [(0, 2), (0, 7), (0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (0, 5), (0, 2), (0, 3), (0, 2), (2, 0),
    (0, 2), (2, 0), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 48 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock3 :
    ∀ k : Fin 16,
      5 ≤ 16 * 3 + k.val →
        16 * 3 + k.val < 3000 →
        (16 * 3 + k.val, (nonresidueCoverageData3.getD k.val (0, 0)).1) ∈ (nonresidueTable0) ∨
          (2 ≤ (nonresidueCoverageData3.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData3.getD k.val (0, 0)).2 < 16 * 3 + k.val ∧
            (nonresidueCoverageData3.getD k.val (0, 0)).2 ∣ 16 * 3 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 3 (nonresidueTable0) nonresidueCoverageData3 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 48,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock3_checked : smallNonresidueBlockChecked 3 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock3 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData3.getD k.val (0, 0)).1,
        nonresidueTable0_checked (16 * 3 + k.val, (nonresidueCoverageData3.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 64.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData4 : List (ℕ × ℕ) :=
  [(0, 2), (0, 5), (0, 2), (2, 0), (0, 2), (0, 3), (0, 2), (7, 0), (0, 2), (5, 0), (0, 2), (0, 3),
    (0, 2), (0, 7), (0, 2), (3, 0)]

/-- Every eligible integer beginning at 64 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock4 :
    ∀ k : Fin 16,
      5 ≤ 16 * 4 + k.val →
        16 * 4 + k.val < 3000 →
        (16 * 4 + k.val, (nonresidueCoverageData4.getD k.val (0, 0)).1) ∈ (nonresidueTable1) ∨
          (2 ≤ (nonresidueCoverageData4.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData4.getD k.val (0, 0)).2 < 16 * 4 + k.val ∧
            (nonresidueCoverageData4.getD k.val (0, 0)).2 ∣ 16 * 4 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 4 (nonresidueTable1) nonresidueCoverageData4 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 64,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock4_checked : smallNonresidueBlockChecked 4 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock4 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData4.getD k.val (0, 0)).1,
        nonresidueTable1_checked (16 * 4 + k.val, (nonresidueCoverageData4.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 80.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData5 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (0, 5), (0, 2), (0, 3), (0, 2), (3, 0), (0, 2), (0, 7),
    (0, 2), (0, 3), (0, 2), (0, 5)]

/-- Every eligible integer beginning at 80 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock5 :
    ∀ k : Fin 16,
      5 ≤ 16 * 5 + k.val →
        16 * 5 + k.val < 3000 →
        (16 * 5 + k.val, (nonresidueCoverageData5.getD k.val (0, 0)).1) ∈ (nonresidueTable1) ∨
          (2 ≤ (nonresidueCoverageData5.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData5.getD k.val (0, 0)).2 < 16 * 5 + k.val ∧
            (nonresidueCoverageData5.getD k.val (0, 0)).2 ∣ 16 * 5 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 5 (nonresidueTable1) nonresidueCoverageData5 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 80,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock5_checked : smallNonresidueBlockChecked 5 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock5 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData5.getD k.val (0, 0)).1,
        nonresidueTable1_checked (16 * 5 + k.val, (nonresidueCoverageData5.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 96.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData6 : List (ℕ × ℕ) :=
  [(0, 2), (5, 0), (0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (3, 0), (0, 2), (0, 3), (0, 2), (2, 0),
    (0, 2), (2, 0), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 96 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock6 :
    ∀ k : Fin 16,
      5 ≤ 16 * 6 + k.val →
        16 * 6 + k.val < 3000 →
        (16 * 6 + k.val, (nonresidueCoverageData6.getD k.val (0, 0)).1) ∈ (nonresidueTable1) ∨
          (2 ≤ (nonresidueCoverageData6.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData6.getD k.val (0, 0)).2 < 16 * 6 + k.val ∧
            (nonresidueCoverageData6.getD k.val (0, 0)).2 ∣ 16 * 6 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 6 (nonresidueTable1) nonresidueCoverageData6 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 96,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock6_checked : smallNonresidueBlockChecked 6 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock6 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData6.getD k.val (0, 0)).1,
        nonresidueTable1_checked (16 * 6 + k.val, (nonresidueCoverageData6.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 112.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData7 : List (ℕ × ℕ) :=
  [(0, 2), (3, 0), (0, 2), (0, 5), (0, 2), (0, 3), (0, 2), (0, 7), (0, 2), (0, 11), (0, 2), (0, 3),
    (0, 2), (0, 5), (0, 2), (3, 0)]

/-- Every eligible integer beginning at 112 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock7 :
    ∀ k : Fin 16,
      5 ≤ 16 * 7 + k.val →
        16 * 7 + k.val < 3000 →
        (16 * 7 + k.val, (nonresidueCoverageData7.getD k.val (0, 0)).1) ∈ (nonresidueTable1) ∨
          (2 ≤ (nonresidueCoverageData7.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData7.getD k.val (0, 0)).2 < 16 * 7 + k.val ∧
            (nonresidueCoverageData7.getD k.val (0, 0)).2 ∣ 16 * 7 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 7 (nonresidueTable1) nonresidueCoverageData7 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 112,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock7_checked : smallNonresidueBlockChecked 7 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock7 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData7.getD k.val (0, 0)).1,
        nonresidueTable1_checked (16 * 7 + k.val, (nonresidueCoverageData7.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 128.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData8 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (0, 7), (0, 2), (0, 3), (0, 2), (3, 0), (0, 2), (2, 0),
    (0, 2), (0, 3), (0, 2), (0, 11)]

/-- Every eligible integer beginning at 128 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock8 :
    ∀ k : Fin 16,
      5 ≤ 16 * 8 + k.val →
        16 * 8 + k.val < 3000 →
        (16 * 8 + k.val, (nonresidueCoverageData8.getD k.val (0, 0)).1) ∈ (nonresidueTable1) ∨
          (2 ≤ (nonresidueCoverageData8.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData8.getD k.val (0, 0)).2 < 16 * 8 + k.val ∧
            (nonresidueCoverageData8.getD k.val (0, 0)).2 ∣ 16 * 8 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 8 (nonresidueTable1) nonresidueCoverageData8 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 128,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock8_checked : smallNonresidueBlockChecked 8 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock8 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData8.getD k.val (0, 0)).1,
        nonresidueTable1_checked (16 * 8 + k.val, (nonresidueCoverageData8.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 144.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData9 : List (ℕ × ℕ) :=
  [(0, 2), (0, 5), (0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (3, 0), (0, 2), (0, 3), (0, 2), (0, 5),
    (0, 2), (2, 0), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 144 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock9 :
    ∀ k : Fin 16,
      5 ≤ 16 * 9 + k.val →
        16 * 9 + k.val < 3000 →
        (16 * 9 + k.val, (nonresidueCoverageData9.getD k.val (0, 0)).1) ∈ (nonresidueTable2) ∨
          (2 ≤ (nonresidueCoverageData9.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData9.getD k.val (0, 0)).2 < 16 * 9 + k.val ∧
            (nonresidueCoverageData9.getD k.val (0, 0)).2 ∣ 16 * 9 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 9 (nonresidueTable2) nonresidueCoverageData9 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 144,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock9_checked : smallNonresidueBlockChecked 9 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock9 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData9.getD k.val (0, 0)).1,
        nonresidueTable2_checked (16 * 9 + k.val, (nonresidueCoverageData9.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 160.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData10 : List (ℕ × ℕ) :=
  [(0, 2), (0, 7), (0, 2), (2, 0), (0, 2), (0, 3), (0, 2), (5, 0), (0, 2), (0, 13), (0, 2), (0, 3),
    (0, 2), (2, 0), (0, 2), (0, 5)]

/-- Every eligible integer beginning at 160 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock10 :
    ∀ k : Fin 16,
      5 ≤ 16 * 10 + k.val →
        16 * 10 + k.val < 3000 →
        (16 * 10 + k.val, (nonresidueCoverageData10.getD k.val (0, 0)).1) ∈ (nonresidueTable2) ∨
          (2 ≤ (nonresidueCoverageData10.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData10.getD k.val (0, 0)).2 < 16 * 10 + k.val ∧
            (nonresidueCoverageData10.getD k.val (0, 0)).2 ∣ 16 * 10 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 10 (nonresidueTable2) nonresidueCoverageData10 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 160,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock10_checked : smallNonresidueBlockChecked 10 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock10 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData10.getD k.val (0, 0)).1,
        nonresidueTable2_checked (16 * 10 + k.val, (nonresidueCoverageData10.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 176.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData11 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (2, 0), (0, 2), (0, 3), (0, 2), (0, 5), (0, 2), (0, 11),
    (0, 2), (0, 3), (0, 2), (7, 0)]

/-- Every eligible integer beginning at 176 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock11 :
    ∀ k : Fin 16,
      5 ≤ 16 * 11 + k.val →
        16 * 11 + k.val < 3000 →
        (16 * 11 + k.val, (nonresidueCoverageData11.getD k.val (0, 0)).1) ∈ (nonresidueTable2) ∨
          (2 ≤ (nonresidueCoverageData11.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData11.getD k.val (0, 0)).2 < 16 * 11 + k.val ∧
            (nonresidueCoverageData11.getD k.val (0, 0)).2 ∣ 16 * 11 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 11 (nonresidueTable2) nonresidueCoverageData11 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 176,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock11_checked : smallNonresidueBlockChecked 11 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock11 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData11.getD k.val (0, 0)).1,
        nonresidueTable2_checked (16 * 11 + k.val, (nonresidueCoverageData11.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 192.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData12 : List (ℕ × ℕ) :=
  [(0, 2), (5, 0), (0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (3, 0), (0, 2), (0, 3), (0, 2), (0, 7),
    (0, 2), (0, 5), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 192 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock12 :
    ∀ k : Fin 16,
      5 ≤ 16 * 12 + k.val →
        16 * 12 + k.val < 3000 →
        (16 * 12 + k.val, (nonresidueCoverageData12.getD k.val (0, 0)).1) ∈ (nonresidueTable2) ∨
          (2 ≤ (nonresidueCoverageData12.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData12.getD k.val (0, 0)).2 < 16 * 12 + k.val ∧
            (nonresidueCoverageData12.getD k.val (0, 0)).2 ∣ 16 * 12 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 12 (nonresidueTable2) nonresidueCoverageData12 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 192,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock12_checked : smallNonresidueBlockChecked 12 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock12 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData12.getD k.val (0, 0)).1,
        nonresidueTable2_checked (16 * 12 + k.val, (nonresidueCoverageData12.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 208.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData13 : List (ℕ × ℕ) :=
  [(0, 2), (0, 11), (0, 2), (2, 0), (0, 2), (0, 3), (0, 2), (0, 5), (0, 2), (0, 7), (0, 2), (0, 3),
    (0, 2), (0, 13), (0, 2), (3, 0)]

/-- Every eligible integer beginning at 208 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock13 :
    ∀ k : Fin 16,
      5 ≤ 16 * 13 + k.val →
        16 * 13 + k.val < 3000 →
        (16 * 13 + k.val, (nonresidueCoverageData13.getD k.val (0, 0)).1) ∈ (nonresidueTable2) ∨
          (2 ≤ (nonresidueCoverageData13.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData13.getD k.val (0, 0)).2 < 16 * 13 + k.val ∧
            (nonresidueCoverageData13.getD k.val (0, 0)).2 ∣ 16 * 13 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 13 (nonresidueTable2) nonresidueCoverageData13 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 208,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock13_checked : smallNonresidueBlockChecked 13 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock13 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData13.getD k.val (0, 0)).1,
        nonresidueTable2_checked (16 * 13 + k.val, (nonresidueCoverageData13.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 224.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData14 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (2, 0), (0, 2), (0, 3), (0, 2), (3, 0), (0, 2), (0, 5),
    (0, 2), (0, 3), (0, 2), (7, 0)]

/-- Every eligible integer beginning at 224 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock14 :
    ∀ k : Fin 16,
      5 ≤ 16 * 14 + k.val →
        16 * 14 + k.val < 3000 →
        (16 * 14 + k.val, (nonresidueCoverageData14.getD k.val (0, 0)).1) ∈
            (nonresidueTable2 ++ nonresidueTable3) ∨
          (2 ≤ (nonresidueCoverageData14.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData14.getD k.val (0, 0)).2 < 16 * 14 + k.val ∧
            (nonresidueCoverageData14.getD k.val (0, 0)).2 ∣ 16 * 14 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl :
      nonresidueCoverageCheck 14 (nonresidueTable2 ++ nonresidueTable3) nonresidueCoverageData14 =
        true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 224,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock14_checked : smallNonresidueBlockChecked 14 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock14 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData14.getD k.val (0, 0)).1,
        (nonresidueTableChecked_append nonresidueTable2_checked nonresidueTable3_checked)
          (16 * 14 + k.val, (nonresidueCoverageData14.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 240.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData15 : List (ℕ × ℕ) :=
  [(0, 2), (7, 0), (0, 2), (0, 3), (0, 2), (0, 5), (0, 2), (0, 13), (0, 2), (0, 3), (0, 2), (2, 0),
    (0, 2), (0, 11), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 240 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock15 :
    ∀ k : Fin 16,
      5 ≤ 16 * 15 + k.val →
        16 * 15 + k.val < 3000 →
        (16 * 15 + k.val, (nonresidueCoverageData15.getD k.val (0, 0)).1) ∈ (nonresidueTable3) ∨
          (2 ≤ (nonresidueCoverageData15.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData15.getD k.val (0, 0)).2 < 16 * 15 + k.val ∧
            (nonresidueCoverageData15.getD k.val (0, 0)).2 ∣ 16 * 15 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 15 (nonresidueTable3) nonresidueCoverageData15 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 240,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock15_checked : smallNonresidueBlockChecked 15 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock15 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData15.getD k.val (0, 0)).1,
        nonresidueTable3_checked (16 * 15 + k.val, (nonresidueCoverageData15.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 256.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData16 : List (ℕ × ℕ) :=
  [(0, 2), (3, 0), (0, 2), (0, 7), (0, 2), (0, 3), (0, 2), (5, 0), (0, 2), (0, 5), (0, 2), (0, 3),
    (0, 2), (2, 0), (0, 2), (3, 0)]

/-- Every eligible integer beginning at 256 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock16 :
    ∀ k : Fin 16,
      5 ≤ 16 * 16 + k.val →
        16 * 16 + k.val < 3000 →
        (16 * 16 + k.val, (nonresidueCoverageData16.getD k.val (0, 0)).1) ∈ (nonresidueTable3) ∨
          (2 ≤ (nonresidueCoverageData16.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData16.getD k.val (0, 0)).2 < 16 * 16 + k.val ∧
            (nonresidueCoverageData16.getD k.val (0, 0)).2 ∣ 16 * 16 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 16 (nonresidueTable3) nonresidueCoverageData16 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 256,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock16_checked : smallNonresidueBlockChecked 16 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock16 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData16.getD k.val (0, 0)).1,
        nonresidueTable3_checked (16 * 16 + k.val, (nonresidueCoverageData16.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 272.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData17 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (0, 5), (0, 2), (2, 0), (0, 2), (0, 3), (0, 2), (3, 0), (0, 2), (2, 0),
    (0, 2), (0, 3), (0, 2), (0, 7)]

/-- Every eligible integer beginning at 272 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock17 :
    ∀ k : Fin 16,
      5 ≤ 16 * 17 + k.val →
        16 * 17 + k.val < 3000 →
        (16 * 17 + k.val, (nonresidueCoverageData17.getD k.val (0, 0)).1) ∈ (nonresidueTable3) ∨
          (2 ≤ (nonresidueCoverageData17.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData17.getD k.val (0, 0)).2 < 16 * 17 + k.val ∧
            (nonresidueCoverageData17.getD k.val (0, 0)).2 ∣ 16 * 17 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 17 (nonresidueTable3) nonresidueCoverageData17 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 272,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock17_checked : smallNonresidueBlockChecked 17 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock17 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData17.getD k.val (0, 0)).1,
        nonresidueTable3_checked (16 * 17 + k.val, (nonresidueCoverageData17.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 288.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData18 : List (ℕ × ℕ) :=
  [(0, 2), (0, 17), (0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (0, 5), (0, 2), (0, 3), (0, 2), (0, 13),
    (0, 2), (0, 7), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 288 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock18 :
    ∀ k : Fin 16,
      5 ≤ 16 * 18 + k.val →
        16 * 18 + k.val < 3000 →
        (16 * 18 + k.val, (nonresidueCoverageData18.getD k.val (0, 0)).1) ∈ (nonresidueTable3) ∨
          (2 ≤ (nonresidueCoverageData18.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData18.getD k.val (0, 0)).2 < 16 * 18 + k.val ∧
            (nonresidueCoverageData18.getD k.val (0, 0)).2 ∣ 16 * 18 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 18 (nonresidueTable3) nonresidueCoverageData18 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 288,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock18_checked : smallNonresidueBlockChecked 18 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock18 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData18.getD k.val (0, 0)).1,
        nonresidueTable3_checked (16 * 18 + k.val, (nonresidueCoverageData18.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 304.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData19 : List (ℕ × ℕ) :=
  [(0, 2), (0, 5), (0, 2), (2, 0), (0, 2), (0, 3), (0, 2), (11, 0), (0, 2), (5, 0), (0, 2), (0, 3),
    (0, 2), (2, 0), (0, 2), (0, 11)]

/-- Every eligible integer beginning at 304 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock19 :
    ∀ k : Fin 16,
      5 ≤ 16 * 19 + k.val →
        16 * 19 + k.val < 3000 →
        (16 * 19 + k.val, (nonresidueCoverageData19.getD k.val (0, 0)).1) ∈ (nonresidueTable3) ∨
          (2 ≤ (nonresidueCoverageData19.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData19.getD k.val (0, 0)).2 < 16 * 19 + k.val ∧
            (nonresidueCoverageData19.getD k.val (0, 0)).2 ∣ 16 * 19 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 19 (nonresidueTable3) nonresidueCoverageData19 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 304,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock19_checked : smallNonresidueBlockChecked 19 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock19 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData19.getD k.val (0, 0)).1,
        nonresidueTable3_checked (16 * 19 + k.val, (nonresidueCoverageData19.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 320.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData20 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (0, 17), (0, 2), (0, 5), (0, 2), (0, 3), (0, 2), (0, 7), (0, 2), (2, 0),
    (0, 2), (0, 3), (0, 2), (0, 5)]

/-- Every eligible integer beginning at 320 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock20 :
    ∀ k : Fin 16,
      5 ≤ 16 * 20 + k.val →
        16 * 20 + k.val < 3000 →
        (16 * 20 + k.val, (nonresidueCoverageData20.getD k.val (0, 0)).1) ∈ (nonresidueTable4) ∨
          (2 ≤ (nonresidueCoverageData20.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData20.getD k.val (0, 0)).2 < 16 * 20 + k.val ∧
            (nonresidueCoverageData20.getD k.val (0, 0)).2 ∣ 16 * 20 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 20 (nonresidueTable4) nonresidueCoverageData20 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 320,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock20_checked : smallNonresidueBlockChecked 20 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock20 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData20.getD k.val (0, 0)).1,
        nonresidueTable4_checked (16 * 20 + k.val, (nonresidueCoverageData20.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 336.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData21 : List (ℕ × ℕ) :=
  [(0, 2), (5, 0), (0, 2), (0, 3), (0, 2), (0, 11), (0, 2), (0, 7), (0, 2), (0, 3), (0, 2), (2, 0),
    (0, 2), (2, 0), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 336 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock21 :
    ∀ k : Fin 16,
      5 ≤ 16 * 21 + k.val →
        16 * 21 + k.val < 3000 →
        (16 * 21 + k.val, (nonresidueCoverageData21.getD k.val (0, 0)).1) ∈ (nonresidueTable4) ∨
          (2 ≤ (nonresidueCoverageData21.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData21.getD k.val (0, 0)).2 < 16 * 21 + k.val ∧
            (nonresidueCoverageData21.getD k.val (0, 0)).2 ∣ 16 * 21 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 21 (nonresidueTable4) nonresidueCoverageData21 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 336,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock21_checked : smallNonresidueBlockChecked 21 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock21 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData21.getD k.val (0, 0)).1,
        nonresidueTable4_checked (16 * 21 + k.val, (nonresidueCoverageData21.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 352.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData22 : List (ℕ × ℕ) :=
  [(0, 2), (3, 0), (0, 2), (0, 5), (0, 2), (0, 3), (0, 2), (7, 0), (0, 2), (0, 19), (0, 2), (0, 3),
    (0, 2), (0, 5), (0, 2), (3, 0)]

/-- Every eligible integer beginning at 352 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock22 :
    ∀ k : Fin 16,
      5 ≤ 16 * 22 + k.val →
        16 * 22 + k.val < 3000 →
        (16 * 22 + k.val, (nonresidueCoverageData22.getD k.val (0, 0)).1) ∈ (nonresidueTable4) ∨
          (2 ≤ (nonresidueCoverageData22.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData22.getD k.val (0, 0)).2 < 16 * 22 + k.val ∧
            (nonresidueCoverageData22.getD k.val (0, 0)).2 ∣ 16 * 22 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 22 (nonresidueTable4) nonresidueCoverageData22 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 352,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock22_checked : smallNonresidueBlockChecked 22 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock22 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData22.getD k.val (0, 0)).1,
        nonresidueTable4_checked (16 * 22 + k.val, (nonresidueCoverageData22.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 368.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData23 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (0, 7), (0, 2), (2, 0), (0, 2), (0, 3), (0, 2), (0, 13), (0, 2), (2, 0),
    (0, 2), (0, 3), (0, 2), (5, 0)]

/-- Every eligible integer beginning at 368 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock23 :
    ∀ k : Fin 16,
      5 ≤ 16 * 23 + k.val →
        16 * 23 + k.val < 3000 →
        (16 * 23 + k.val, (nonresidueCoverageData23.getD k.val (0, 0)).1) ∈ (nonresidueTable4) ∨
          (2 ≤ (nonresidueCoverageData23.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData23.getD k.val (0, 0)).2 < 16 * 23 + k.val ∧
            (nonresidueCoverageData23.getD k.val (0, 0)).2 ∣ 16 * 23 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 23 (nonresidueTable4) nonresidueCoverageData23 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 368,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock23_checked : smallNonresidueBlockChecked 23 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock23 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData23.getD k.val (0, 0)).1,
        nonresidueTable4_checked (16 * 23 + k.val, (nonresidueCoverageData23.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 384.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData24 : List (ℕ × ℕ) :=
  [(0, 2), (0, 5), (0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (0, 17), (0, 2), (0, 3), (0, 2), (0, 5),
    (0, 2), (2, 0), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 384 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock24 :
    ∀ k : Fin 16,
      5 ≤ 16 * 24 + k.val →
        16 * 24 + k.val < 3000 →
        (16 * 24 + k.val, (nonresidueCoverageData24.getD k.val (0, 0)).1) ∈ (nonresidueTable4) ∨
          (2 ≤ (nonresidueCoverageData24.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData24.getD k.val (0, 0)).2 < 16 * 24 + k.val ∧
            (nonresidueCoverageData24.getD k.val (0, 0)).2 ∣ 16 * 24 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 24 (nonresidueTable4) nonresidueCoverageData24 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 384,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock24_checked : smallNonresidueBlockChecked 24 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock24 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData24.getD k.val (0, 0)).1,
        nonresidueTable4_checked (16 * 24 + k.val, (nonresidueCoverageData24.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 400.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData25 : List (ℕ × ℕ) :=
  [(0, 2), (3, 0), (0, 2), (0, 13), (0, 2), (0, 3), (0, 2), (0, 11), (0, 2), (7, 0), (0, 2), (0, 3),
    (0, 2), (0, 7), (0, 2), (0, 5)]

/-- Every eligible integer beginning at 400 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock25 :
    ∀ k : Fin 16,
      5 ≤ 16 * 25 + k.val →
        16 * 25 + k.val < 3000 →
        (16 * 25 + k.val, (nonresidueCoverageData25.getD k.val (0, 0)).1) ∈ (nonresidueTable4) ∨
          (2 ≤ (nonresidueCoverageData25.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData25.getD k.val (0, 0)).2 < 16 * 25 + k.val ∧
            (nonresidueCoverageData25.getD k.val (0, 0)).2 ∣ 16 * 25 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 25 (nonresidueTable4) nonresidueCoverageData25 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 400,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock25_checked : smallNonresidueBlockChecked 25 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock25 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData25.getD k.val (0, 0)).1,
        nonresidueTable4_checked (16 * 25 + k.val, (nonresidueCoverageData25.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 416.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData26 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (2, 0), (0, 2), (0, 3), (0, 2), (0, 5), (0, 2), (0, 7),
    (0, 2), (0, 3), (0, 2), (7, 0)]

/-- Every eligible integer beginning at 416 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock26 :
    ∀ k : Fin 16,
      5 ≤ 16 * 26 + k.val →
        16 * 26 + k.val < 3000 →
        (16 * 26 + k.val, (nonresidueCoverageData26.getD k.val (0, 0)).1) ∈
            (nonresidueTable4 ++ nonresidueTable5) ∨
          (2 ≤ (nonresidueCoverageData26.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData26.getD k.val (0, 0)).2 < 16 * 26 + k.val ∧
            (nonresidueCoverageData26.getD k.val (0, 0)).2 ∣ 16 * 26 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl :
      nonresidueCoverageCheck 26 (nonresidueTable4 ++ nonresidueTable5) nonresidueCoverageData26 =
        true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 416,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock26_checked : smallNonresidueBlockChecked 26 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock26 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData26.getD k.val (0, 0)).1,
        (nonresidueTableChecked_append nonresidueTable4_checked nonresidueTable5_checked)
          (16 * 26 + k.val, (nonresidueCoverageData26.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 432.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData27 : List (ℕ × ℕ) :=
  [(0, 2), (5, 0), (0, 2), (0, 3), (0, 2), (0, 19), (0, 2), (3, 0), (0, 2), (0, 3), (0, 2), (2, 0),
    (0, 2), (0, 5), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 432 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock27 :
    ∀ k : Fin 16,
      5 ≤ 16 * 27 + k.val →
        16 * 27 + k.val < 3000 →
        (16 * 27 + k.val, (nonresidueCoverageData27.getD k.val (0, 0)).1) ∈ (nonresidueTable5) ∨
          (2 ≤ (nonresidueCoverageData27.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData27.getD k.val (0, 0)).2 < 16 * 27 + k.val ∧
            (nonresidueCoverageData27.getD k.val (0, 0)).2 ∣ 16 * 27 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 27 (nonresidueTable5) nonresidueCoverageData27 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 432,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock27_checked : smallNonresidueBlockChecked 27 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock27 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData27.getD k.val (0, 0)).1,
        nonresidueTable5_checked (16 * 27 + k.val, (nonresidueCoverageData27.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 448.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData28 : List (ℕ × ℕ) :=
  [(0, 2), (3, 0), (0, 2), (0, 11), (0, 2), (0, 3), (0, 2), (0, 5), (0, 2), (5, 0), (0, 2), (0, 3),
    (0, 2), (2, 0), (0, 2), (3, 0)]

/-- Every eligible integer beginning at 448 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock28 :
    ∀ k : Fin 16,
      5 ≤ 16 * 28 + k.val →
        16 * 28 + k.val < 3000 →
        (16 * 28 + k.val, (nonresidueCoverageData28.getD k.val (0, 0)).1) ∈ (nonresidueTable5) ∨
          (2 ≤ (nonresidueCoverageData28.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData28.getD k.val (0, 0)).2 < 16 * 28 + k.val ∧
            (nonresidueCoverageData28.getD k.val (0, 0)).2 ∣ 16 * 28 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 28 (nonresidueTable5) nonresidueCoverageData28 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 448,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock28_checked : smallNonresidueBlockChecked 28 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock28 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData28.getD k.val (0, 0)).1,
        nonresidueTable5_checked (16 * 28 + k.val, (nonresidueCoverageData28.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 464.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData29 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (0, 7), (0, 2), (0, 3), (0, 2), (0, 11), (0, 2), (0, 5),
    (0, 2), (0, 3), (0, 2), (13, 0)]

/-- Every eligible integer beginning at 464 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock29 :
    ∀ k : Fin 16,
      5 ≤ 16 * 29 + k.val →
        16 * 29 + k.val < 3000 →
        (16 * 29 + k.val, (nonresidueCoverageData29.getD k.val (0, 0)).1) ∈ (nonresidueTable5) ∨
          (2 ≤ (nonresidueCoverageData29.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData29.getD k.val (0, 0)).2 < 16 * 29 + k.val ∧
            (nonresidueCoverageData29.getD k.val (0, 0)).2 ∣ 16 * 29 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 29 (nonresidueTable5) nonresidueCoverageData29 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 464,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock29_checked : smallNonresidueBlockChecked 29 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock29 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData29.getD k.val (0, 0)).1,
        nonresidueTable5_checked (16 * 29 + k.val, (nonresidueCoverageData29.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 480.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData30 : List (ℕ × ℕ) :=
  [(0, 2), (0, 13), (0, 2), (0, 3), (0, 2), (0, 5), (0, 2), (3, 0), (0, 2), (0, 3), (0, 2), (2, 0),
    (0, 2), (0, 17), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 480 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock30 :
    ∀ k : Fin 16,
      5 ≤ 16 * 30 + k.val →
        16 * 30 + k.val < 3000 →
        (16 * 30 + k.val, (nonresidueCoverageData30.getD k.val (0, 0)).1) ∈ (nonresidueTable5) ∨
          (2 ≤ (nonresidueCoverageData30.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData30.getD k.val (0, 0)).2 < 16 * 30 + k.val ∧
            (nonresidueCoverageData30.getD k.val (0, 0)).2 ∣ 16 * 30 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 30 (nonresidueTable5) nonresidueCoverageData30 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 480,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock30_checked : smallNonresidueBlockChecked 30 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock30 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData30.getD k.val (0, 0)).1,
        nonresidueTable5_checked (16 * 30 + k.val, (nonresidueCoverageData30.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 496.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData31 : List (ℕ × ℕ) :=
  [(0, 2), (0, 7), (0, 2), (2, 0), (0, 2), (0, 3), (0, 2), (5, 0), (0, 2), (0, 5), (0, 2), (0, 3),
    (0, 2), (2, 0), (0, 2), (0, 7)]

/-- Every eligible integer beginning at 496 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock31 :
    ∀ k : Fin 16,
      5 ≤ 16 * 31 + k.val →
        16 * 31 + k.val < 3000 →
        (16 * 31 + k.val, (nonresidueCoverageData31.getD k.val (0, 0)).1) ∈ (nonresidueTable5) ∨
          (2 ≤ (nonresidueCoverageData31.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData31.getD k.val (0, 0)).2 < 16 * 31 + k.val ∧
            (nonresidueCoverageData31.getD k.val (0, 0)).2 ∣ 16 * 31 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 31 (nonresidueTable5) nonresidueCoverageData31 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 496,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock31_checked : smallNonresidueBlockChecked 31 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock31 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData31.getD k.val (0, 0)).1,
        nonresidueTable5_checked (16 * 31 + k.val, (nonresidueCoverageData31.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 512.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData32 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (0, 5), (0, 2), (0, 11), (0, 2), (0, 3), (0, 2), (3, 0), (0, 2), (2, 0),
    (0, 2), (0, 3), (0, 2), (0, 17)]

/-- Every eligible integer beginning at 512 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock32 :
    ∀ k : Fin 16,
      5 ≤ 16 * 32 + k.val →
        16 * 32 + k.val < 3000 →
        (16 * 32 + k.val, (nonresidueCoverageData32.getD k.val (0, 0)).1) ∈
            (nonresidueTable5 ++ nonresidueTable6) ∨
          (2 ≤ (nonresidueCoverageData32.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData32.getD k.val (0, 0)).2 < 16 * 32 + k.val ∧
            (nonresidueCoverageData32.getD k.val (0, 0)).2 ∣ 16 * 32 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl :
      nonresidueCoverageCheck 32 (nonresidueTable5 ++ nonresidueTable6) nonresidueCoverageData32 =
        true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 512,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock32_checked : smallNonresidueBlockChecked 32 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock32 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData32.getD k.val (0, 0)).1,
        (nonresidueTableChecked_append nonresidueTable5_checked nonresidueTable6_checked)
          (16 * 32 + k.val, (nonresidueCoverageData32.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 528.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData33 : List (ℕ × ℕ) :=
  [(0, 2), (0, 23), (0, 2), (0, 3), (0, 2), (0, 13), (0, 2), (0, 5), (0, 2), (0, 3), (0, 2), (0, 7),
    (0, 2), (2, 0), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 528 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock33 :
    ∀ k : Fin 16,
      5 ≤ 16 * 33 + k.val →
        16 * 33 + k.val < 3000 →
        (16 * 33 + k.val, (nonresidueCoverageData33.getD k.val (0, 0)).1) ∈ (nonresidueTable6) ∨
          (2 ≤ (nonresidueCoverageData33.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData33.getD k.val (0, 0)).2 < 16 * 33 + k.val ∧
            (nonresidueCoverageData33.getD k.val (0, 0)).2 ∣ 16 * 33 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 33 (nonresidueTable6) nonresidueCoverageData33 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 528,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock33_checked : smallNonresidueBlockChecked 33 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock33 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData33.getD k.val (0, 0)).1,
        nonresidueTable6_checked (16 * 33 + k.val, (nonresidueCoverageData33.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 544.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData34 : List (ℕ × ℕ) :=
  [(0, 2), (0, 5), (0, 2), (2, 0), (0, 2), (0, 3), (0, 2), (0, 19), (0, 2), (0, 7), (0, 2), (0, 3),
    (0, 2), (2, 0), (0, 2), (0, 13)]

/-- Every eligible integer beginning at 544 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock34 :
    ∀ k : Fin 16,
      5 ≤ 16 * 34 + k.val →
        16 * 34 + k.val < 3000 →
        (16 * 34 + k.val, (nonresidueCoverageData34.getD k.val (0, 0)).1) ∈ (nonresidueTable6) ∨
          (2 ≤ (nonresidueCoverageData34.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData34.getD k.val (0, 0)).2 < 16 * 34 + k.val ∧
            (nonresidueCoverageData34.getD k.val (0, 0)).2 ∣ 16 * 34 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 34 (nonresidueTable6) nonresidueCoverageData34 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 544,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock34_checked : smallNonresidueBlockChecked 34 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock34 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData34.getD k.val (0, 0)).1,
        nonresidueTable6_checked (16 * 34 + k.val, (nonresidueCoverageData34.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 560.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData35 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (0, 5), (0, 2), (0, 3), (0, 2), (3, 0), (0, 2), (2, 0),
    (0, 2), (0, 3), (0, 2), (0, 5)]

/-- Every eligible integer beginning at 560 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock35 :
    ∀ k : Fin 16,
      5 ≤ 16 * 35 + k.val →
        16 * 35 + k.val < 3000 →
        (16 * 35 + k.val, (nonresidueCoverageData35.getD k.val (0, 0)).1) ∈ (nonresidueTable6) ∨
          (2 ≤ (nonresidueCoverageData35.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData35.getD k.val (0, 0)).2 < 16 * 35 + k.val ∧
            (nonresidueCoverageData35.getD k.val (0, 0)).2 ∣ 16 * 35 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 35 (nonresidueTable6) nonresidueCoverageData35 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 560,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock35_checked : smallNonresidueBlockChecked 35 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock35 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData35.getD k.val (0, 0)).1,
        nonresidueTable6_checked (16 * 35 + k.val, (nonresidueCoverageData35.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 576.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData36 : List (ℕ × ℕ) :=
  [(0, 2), (5, 0), (0, 2), (0, 3), (0, 2), (0, 7), (0, 2), (0, 11), (0, 2), (0, 3), (0, 2), (2, 0),
    (0, 2), (0, 19), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 576 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock36 :
    ∀ k : Fin 16,
      5 ≤ 16 * 36 + k.val →
        16 * 36 + k.val < 3000 →
        (16 * 36 + k.val, (nonresidueCoverageData36.getD k.val (0, 0)).1) ∈ (nonresidueTable6) ∨
          (2 ≤ (nonresidueCoverageData36.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData36.getD k.val (0, 0)).2 < 16 * 36 + k.val ∧
            (nonresidueCoverageData36.getD k.val (0, 0)).2 ∣ 16 * 36 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 36 (nonresidueTable6) nonresidueCoverageData36 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 576,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock36_checked : smallNonresidueBlockChecked 36 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock36 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData36.getD k.val (0, 0)).1,
        nonresidueTable6_checked (16 * 36 + k.val, (nonresidueCoverageData36.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 592.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData37 : List (ℕ × ℕ) :=
  [(0, 2), (3, 0), (0, 2), (0, 5), (0, 2), (0, 3), (0, 2), (7, 0), (0, 2), (7, 0), (0, 2), (0, 3),
    (0, 2), (0, 5), (0, 2), (3, 0)]

/-- Every eligible integer beginning at 592 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock37 :
    ∀ k : Fin 16,
      5 ≤ 16 * 37 + k.val →
        16 * 37 + k.val < 3000 →
        (16 * 37 + k.val, (nonresidueCoverageData37.getD k.val (0, 0)).1) ∈ (nonresidueTable6) ∨
          (2 ≤ (nonresidueCoverageData37.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData37.getD k.val (0, 0)).2 < 16 * 37 + k.val ∧
            (nonresidueCoverageData37.getD k.val (0, 0)).2 ∣ 16 * 37 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 37 (nonresidueTable6) nonresidueCoverageData37 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 592,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock37_checked : smallNonresidueBlockChecked 37 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock37 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData37.getD k.val (0, 0)).1,
        nonresidueTable6_checked (16 * 37 + k.val, (nonresidueCoverageData37.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 608.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData38 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (0, 13), (0, 2), (2, 0), (0, 2), (0, 3), (0, 2), (3, 0), (0, 2), (2, 0),
    (0, 2), (0, 3), (0, 2), (0, 7)]

/-- Every eligible integer beginning at 608 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock38 :
    ∀ k : Fin 16,
      5 ≤ 16 * 38 + k.val →
        16 * 38 + k.val < 3000 →
        (16 * 38 + k.val, (nonresidueCoverageData38.getD k.val (0, 0)).1) ∈ (nonresidueTable6) ∨
          (2 ≤ (nonresidueCoverageData38.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData38.getD k.val (0, 0)).2 < 16 * 38 + k.val ∧
            (nonresidueCoverageData38.getD k.val (0, 0)).2 ∣ 16 * 38 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 38 (nonresidueTable6) nonresidueCoverageData38 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 608,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock38_checked : smallNonresidueBlockChecked 38 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock38 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData38.getD k.val (0, 0)).1,
        nonresidueTable6_checked (16 * 38 + k.val, (nonresidueCoverageData38.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 624.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData39 : List (ℕ × ℕ) :=
  [(0, 2), (0, 5), (0, 2), (0, 3), (0, 2), (0, 17), (0, 2), (3, 0), (0, 2), (0, 3), (0, 2), (0, 5),
    (0, 2), (0, 7), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 624 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock39 :
    ∀ k : Fin 16,
      5 ≤ 16 * 39 + k.val →
        16 * 39 + k.val < 3000 →
        (16 * 39 + k.val, (nonresidueCoverageData39.getD k.val (0, 0)).1) ∈ (nonresidueTable7) ∨
          (2 ≤ (nonresidueCoverageData39.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData39.getD k.val (0, 0)).2 < 16 * 39 + k.val ∧
            (nonresidueCoverageData39.getD k.val (0, 0)).2 ∣ 16 * 39 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 39 (nonresidueTable7) nonresidueCoverageData39 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 624,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock39_checked : smallNonresidueBlockChecked 39 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock39 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData39.getD k.val (0, 0)).1,
        nonresidueTable7_checked (16 * 39 + k.val, (nonresidueCoverageData39.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 640.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData40 : List (ℕ × ℕ) :=
  [(0, 2), (3, 0), (0, 2), (2, 0), (0, 2), (0, 3), (0, 2), (5, 0), (0, 2), (0, 11), (0, 2), (0, 3),
    (0, 2), (2, 0), (0, 2), (0, 5)]

/-- Every eligible integer beginning at 640 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock40 :
    ∀ k : Fin 16,
      5 ≤ 16 * 40 + k.val →
        16 * 40 + k.val < 3000 →
        (16 * 40 + k.val, (nonresidueCoverageData40.getD k.val (0, 0)).1) ∈ (nonresidueTable7) ∨
          (2 ≤ (nonresidueCoverageData40.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData40.getD k.val (0, 0)).2 < 16 * 40 + k.val ∧
            (nonresidueCoverageData40.getD k.val (0, 0)).2 ∣ 16 * 40 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 40 (nonresidueTable7) nonresidueCoverageData40 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 640,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock40_checked : smallNonresidueBlockChecked 40 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock40 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData40.getD k.val (0, 0)).1,
        nonresidueTable7_checked (16 * 40 + k.val, (nonresidueCoverageData40.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 656.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData41 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (2, 0), (0, 2), (0, 3), (0, 2), (0, 5), (0, 2), (0, 23),
    (0, 2), (0, 3), (0, 2), (0, 11)]

/-- Every eligible integer beginning at 656 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock41 :
    ∀ k : Fin 16,
      5 ≤ 16 * 41 + k.val →
        16 * 41 + k.val < 3000 →
        (16 * 41 + k.val, (nonresidueCoverageData41.getD k.val (0, 0)).1) ∈ (nonresidueTable7) ∨
          (2 ≤ (nonresidueCoverageData41.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData41.getD k.val (0, 0)).2 < 16 * 41 + k.val ∧
            (nonresidueCoverageData41.getD k.val (0, 0)).2 ∣ 16 * 41 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 41 (nonresidueTable7) nonresidueCoverageData41 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 656,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock41_checked : smallNonresidueBlockChecked 41 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock41 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData41.getD k.val (0, 0)).1,
        nonresidueTable7_checked (16 * 41 + k.val, (nonresidueCoverageData41.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 672.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData42 : List (ℕ × ℕ) :=
  [(0, 2), (5, 0), (0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (0, 7), (0, 2), (0, 3), (0, 2), (2, 0),
    (0, 2), (0, 5), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 672 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock42 :
    ∀ k : Fin 16,
      5 ≤ 16 * 42 + k.val →
        16 * 42 + k.val < 3000 →
        (16 * 42 + k.val, (nonresidueCoverageData42.getD k.val (0, 0)).1) ∈ (nonresidueTable7) ∨
          (2 ≤ (nonresidueCoverageData42.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData42.getD k.val (0, 0)).2 < 16 * 42 + k.val ∧
            (nonresidueCoverageData42.getD k.val (0, 0)).2 ∣ 16 * 42 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 42 (nonresidueTable7) nonresidueCoverageData42 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 672,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock42_checked : smallNonresidueBlockChecked 42 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock42 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData42.getD k.val (0, 0)).1,
        nonresidueTable7_checked (16 * 42 + k.val, (nonresidueCoverageData42.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 688.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData43 : List (ℕ × ℕ) :=
  [(0, 2), (0, 13), (0, 2), (2, 0), (0, 2), (0, 3), (0, 2), (0, 5), (0, 2), (0, 17), (0, 2), (0, 3),
    (0, 2), (2, 0), (0, 2), (0, 19)]

/-- Every eligible integer beginning at 688 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock43 :
    ∀ k : Fin 16,
      5 ≤ 16 * 43 + k.val →
        16 * 43 + k.val < 3000 →
        (16 * 43 + k.val, (nonresidueCoverageData43.getD k.val (0, 0)).1) ∈ (nonresidueTable7) ∨
          (2 ≤ (nonresidueCoverageData43.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData43.getD k.val (0, 0)).2 < 16 * 43 + k.val ∧
            (nonresidueCoverageData43.getD k.val (0, 0)).2 ∣ 16 * 43 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 43 (nonresidueTable7) nonresidueCoverageData43 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 688,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock43_checked : smallNonresidueBlockChecked 43 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock43 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData43.getD k.val (0, 0)).1,
        nonresidueTable7_checked (16 * 43 + k.val, (nonresidueCoverageData43.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 704.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData44 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (0, 7), (0, 2), (2, 0), (0, 2), (0, 3), (0, 2), (0, 23), (0, 2), (0, 5),
    (0, 2), (0, 3), (0, 2), (11, 0)]

/-- Every eligible integer beginning at 704 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock44 :
    ∀ k : Fin 16,
      5 ≤ 16 * 44 + k.val →
        16 * 44 + k.val < 3000 →
        (16 * 44 + k.val, (nonresidueCoverageData44.getD k.val (0, 0)).1) ∈ (nonresidueTable7) ∨
          (2 ≤ (nonresidueCoverageData44.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData44.getD k.val (0, 0)).2 < 16 * 44 + k.val ∧
            (nonresidueCoverageData44.getD k.val (0, 0)).2 ∣ 16 * 44 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 44 (nonresidueTable7) nonresidueCoverageData44 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 704,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock44_checked : smallNonresidueBlockChecked 44 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock44 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData44.getD k.val (0, 0)).1,
        nonresidueTable7_checked (16 * 44 + k.val, (nonresidueCoverageData44.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 720.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData45 : List (ℕ × ℕ) :=
  [(0, 2), (0, 7), (0, 2), (0, 3), (0, 2), (0, 5), (0, 2), (3, 0), (0, 2), (0, 3), (0, 2), (0, 17),
    (0, 2), (2, 0), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 720 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock45 :
    ∀ k : Fin 16,
      5 ≤ 16 * 45 + k.val →
        16 * 45 + k.val < 3000 →
        (16 * 45 + k.val, (nonresidueCoverageData45.getD k.val (0, 0)).1) ∈ (nonresidueTable7) ∨
          (2 ≤ (nonresidueCoverageData45.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData45.getD k.val (0, 0)).2 < 16 * 45 + k.val ∧
            (nonresidueCoverageData45.getD k.val (0, 0)).2 ∣ 16 * 45 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 45 (nonresidueTable7) nonresidueCoverageData45 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 720,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock45_checked : smallNonresidueBlockChecked 45 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock45 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData45.getD k.val (0, 0)).1,
        nonresidueTable7_checked (16 * 45 + k.val, (nonresidueCoverageData45.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 736.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData46 : List (ℕ × ℕ) :=
  [(0, 2), (0, 11), (0, 2), (2, 0), (0, 2), (0, 3), (0, 2), (5, 0), (0, 2), (0, 5), (0, 2), (0, 3),
    (0, 2), (0, 7), (0, 2), (3, 0)]

/-- Every eligible integer beginning at 736 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock46 :
    ∀ k : Fin 16,
      5 ≤ 16 * 46 + k.val →
        16 * 46 + k.val < 3000 →
        (16 * 46 + k.val, (nonresidueCoverageData46.getD k.val (0, 0)).1) ∈ (nonresidueTable8) ∨
          (2 ≤ (nonresidueCoverageData46.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData46.getD k.val (0, 0)).2 < 16 * 46 + k.val ∧
            (nonresidueCoverageData46.getD k.val (0, 0)).2 ∣ 16 * 46 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 46 (nonresidueTable8) nonresidueCoverageData46 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 736,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock46_checked : smallNonresidueBlockChecked 46 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock46 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData46.getD k.val (0, 0)).1,
        nonresidueTable8_checked (16 * 46 + k.val, (nonresidueCoverageData46.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 752.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData47 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (0, 5), (0, 2), (2, 0), (0, 2), (0, 3), (0, 2), (3, 0), (0, 2), (0, 7),
    (0, 2), (0, 3), (0, 2), (0, 13)]

/-- Every eligible integer beginning at 752 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock47 :
    ∀ k : Fin 16,
      5 ≤ 16 * 47 + k.val →
        16 * 47 + k.val < 3000 →
        (16 * 47 + k.val, (nonresidueCoverageData47.getD k.val (0, 0)).1) ∈ (nonresidueTable8) ∨
          (2 ≤ (nonresidueCoverageData47.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData47.getD k.val (0, 0)).2 < 16 * 47 + k.val ∧
            (nonresidueCoverageData47.getD k.val (0, 0)).2 ∣ 16 * 47 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 47 (nonresidueTable8) nonresidueCoverageData47 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 752,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock47_checked : smallNonresidueBlockChecked 47 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock47 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData47.getD k.val (0, 0)).1,
        nonresidueTable8_checked (16 * 47 + k.val, (nonresidueCoverageData47.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 768.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData48 : List (ℕ × ℕ) :=
  [(0, 2), (7, 0), (0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (0, 5), (0, 2), (0, 3), (0, 2), (0, 19),
    (0, 2), (0, 11), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 768 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock48 :
    ∀ k : Fin 16,
      5 ≤ 16 * 48 + k.val →
        16 * 48 + k.val < 3000 →
        (16 * 48 + k.val, (nonresidueCoverageData48.getD k.val (0, 0)).1) ∈ (nonresidueTable8) ∨
          (2 ≤ (nonresidueCoverageData48.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData48.getD k.val (0, 0)).2 < 16 * 48 + k.val ∧
            (nonresidueCoverageData48.getD k.val (0, 0)).2 ∣ 16 * 48 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 48 (nonresidueTable8) nonresidueCoverageData48 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 768,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock48_checked : smallNonresidueBlockChecked 48 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock48 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData48.getD k.val (0, 0)).1,
        nonresidueTable8_checked (16 * 48 + k.val, (nonresidueCoverageData48.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 784.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData49 : List (ℕ × ℕ) :=
  [(0, 2), (0, 5), (0, 2), (2, 0), (0, 2), (0, 3), (0, 2), (0, 7), (0, 2), (0, 13), (0, 2), (0, 3),
    (0, 2), (2, 0), (0, 2), (0, 17)]

/-- Every eligible integer beginning at 784 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock49 :
    ∀ k : Fin 16,
      5 ≤ 16 * 49 + k.val →
        16 * 49 + k.val < 3000 →
        (16 * 49 + k.val, (nonresidueCoverageData49.getD k.val (0, 0)).1) ∈ (nonresidueTable8) ∨
          (2 ≤ (nonresidueCoverageData49.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData49.getD k.val (0, 0)).2 < 16 * 49 + k.val ∧
            (nonresidueCoverageData49.getD k.val (0, 0)).2 ∣ 16 * 49 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 49 (nonresidueTable8) nonresidueCoverageData49 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 784,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock49_checked : smallNonresidueBlockChecked 49 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock49 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData49.getD k.val (0, 0)).1,
        nonresidueTable8_checked (16 * 49 + k.val, (nonresidueCoverageData49.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 800.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData50 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (0, 11), (0, 2), (0, 5), (0, 2), (0, 3), (0, 2), (3, 0), (0, 2), (2, 0),
    (0, 2), (0, 3), (0, 2), (0, 5)]

/-- Every eligible integer beginning at 800 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock50 :
    ∀ k : Fin 16,
      5 ≤ 16 * 50 + k.val →
        16 * 50 + k.val < 3000 →
        (16 * 50 + k.val, (nonresidueCoverageData50.getD k.val (0, 0)).1) ∈ (nonresidueTable8) ∨
          (2 ≤ (nonresidueCoverageData50.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData50.getD k.val (0, 0)).2 < 16 * 50 + k.val ∧
            (nonresidueCoverageData50.getD k.val (0, 0)).2 ∣ 16 * 50 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 50 (nonresidueTable8) nonresidueCoverageData50 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 800,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock50_checked : smallNonresidueBlockChecked 50 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock50 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData50.getD k.val (0, 0)).1,
        nonresidueTable8_checked (16 * 50 + k.val, (nonresidueCoverageData50.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 816.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData51 : List (ℕ × ℕ) :=
  [(0, 2), (0, 19), (0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (3, 0), (0, 2), (0, 3), (0, 2), (2, 0),
    (0, 2), (2, 0), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 816 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock51 :
    ∀ k : Fin 16,
      5 ≤ 16 * 51 + k.val →
        16 * 51 + k.val < 3000 →
        (16 * 51 + k.val, (nonresidueCoverageData51.getD k.val (0, 0)).1) ∈ (nonresidueTable8) ∨
          (2 ≤ (nonresidueCoverageData51.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData51.getD k.val (0, 0)).2 < 16 * 51 + k.val ∧
            (nonresidueCoverageData51.getD k.val (0, 0)).2 ∣ 16 * 51 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 51 (nonresidueTable8) nonresidueCoverageData51 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 816,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock51_checked : smallNonresidueBlockChecked 51 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock51 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData51.getD k.val (0, 0)).1,
        nonresidueTable8_checked (16 * 51 + k.val, (nonresidueCoverageData51.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 832.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData52 : List (ℕ × ℕ) :=
  [(0, 2), (0, 7), (0, 2), (0, 5), (0, 2), (0, 3), (0, 2), (11, 0), (0, 2), (0, 29), (0, 2), (0, 3),
    (0, 2), (0, 5), (0, 2), (0, 7)]

/-- Every eligible integer beginning at 832 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock52 :
    ∀ k : Fin 16,
      5 ≤ 16 * 52 + k.val →
        16 * 52 + k.val < 3000 →
        (16 * 52 + k.val, (nonresidueCoverageData52.getD k.val (0, 0)).1) ∈ (nonresidueTable8) ∨
          (2 ≤ (nonresidueCoverageData52.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData52.getD k.val (0, 0)).2 < 16 * 52 + k.val ∧
            (nonresidueCoverageData52.getD k.val (0, 0)).2 ∣ 16 * 52 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 52 (nonresidueTable8) nonresidueCoverageData52 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 832,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock52_checked : smallNonresidueBlockChecked 52 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock52 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData52.getD k.val (0, 0)).1,
        nonresidueTable8_checked (16 * 52 + k.val, (nonresidueCoverageData52.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 848.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData53 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (0, 23), (0, 2), (2, 0), (0, 2), (0, 3), (0, 2), (3, 0), (0, 2), (2, 0),
    (0, 2), (0, 3), (0, 2), (5, 0)]

/-- Every eligible integer beginning at 848 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock53 :
    ∀ k : Fin 16,
      5 ≤ 16 * 53 + k.val →
        16 * 53 + k.val < 3000 →
        (16 * 53 + k.val, (nonresidueCoverageData53.getD k.val (0, 0)).1) ∈ (nonresidueTable9) ∨
          (2 ≤ (nonresidueCoverageData53.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData53.getD k.val (0, 0)).2 < 16 * 53 + k.val ∧
            (nonresidueCoverageData53.getD k.val (0, 0)).2 ∣ 16 * 53 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 53 (nonresidueTable9) nonresidueCoverageData53 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 848,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock53_checked : smallNonresidueBlockChecked 53 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock53 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData53.getD k.val (0, 0)).1,
        nonresidueTable9_checked (16 * 53 + k.val, (nonresidueCoverageData53.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 864.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData54 : List (ℕ × ℕ) :=
  [(0, 2), (0, 5), (0, 2), (0, 3), (0, 2), (0, 11), (0, 2), (0, 13), (0, 2), (0, 3), (0, 2), (0, 5),
    (0, 2), (2, 0), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 864 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock54 :
    ∀ k : Fin 16,
      5 ≤ 16 * 54 + k.val →
        16 * 54 + k.val < 3000 →
        (16 * 54 + k.val, (nonresidueCoverageData54.getD k.val (0, 0)).1) ∈ (nonresidueTable9) ∨
          (2 ≤ (nonresidueCoverageData54.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData54.getD k.val (0, 0)).2 < 16 * 54 + k.val ∧
            (nonresidueCoverageData54.getD k.val (0, 0)).2 ∣ 16 * 54 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 54 (nonresidueTable9) nonresidueCoverageData54 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 864,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock54_checked : smallNonresidueBlockChecked 54 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock54 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData54.getD k.val (0, 0)).1,
        nonresidueTable9_checked (16 * 54 + k.val, (nonresidueCoverageData54.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 880.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData55 : List (ℕ × ℕ) :=
  [(0, 2), (3, 0), (0, 2), (2, 0), (0, 2), (0, 3), (0, 2), (5, 0), (0, 2), (0, 7), (0, 2), (0, 3),
    (0, 2), (0, 19), (0, 2), (0, 5)]

/-- Every eligible integer beginning at 880 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock55 :
    ∀ k : Fin 16,
      5 ≤ 16 * 55 + k.val →
        16 * 55 + k.val < 3000 →
        (16 * 55 + k.val, (nonresidueCoverageData55.getD k.val (0, 0)).1) ∈ (nonresidueTable9) ∨
          (2 ≤ (nonresidueCoverageData55.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData55.getD k.val (0, 0)).2 < 16 * 55 + k.val ∧
            (nonresidueCoverageData55.getD k.val (0, 0)).2 ∣ 16 * 55 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 55 (nonresidueTable9) nonresidueCoverageData55 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 880,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock55_checked : smallNonresidueBlockChecked 55 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock55 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData55.getD k.val (0, 0)).1,
        nonresidueTable9_checked (16 * 55 + k.val, (nonresidueCoverageData55.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 896.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData56 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (0, 29), (0, 2), (0, 17), (0, 2), (0, 3), (0, 2), (0, 5), (0, 2), (2, 0),
    (0, 2), (0, 3), (0, 2), (7, 0)]

/-- Every eligible integer beginning at 896 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock56 :
    ∀ k : Fin 16,
      5 ≤ 16 * 56 + k.val →
        16 * 56 + k.val < 3000 →
        (16 * 56 + k.val, (nonresidueCoverageData56.getD k.val (0, 0)).1) ∈ (nonresidueTable9) ∨
          (2 ≤ (nonresidueCoverageData56.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData56.getD k.val (0, 0)).2 < 16 * 56 + k.val ∧
            (nonresidueCoverageData56.getD k.val (0, 0)).2 ∣ 16 * 56 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 56 (nonresidueTable9) nonresidueCoverageData56 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 896,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock56_checked : smallNonresidueBlockChecked 56 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock56 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData56.getD k.val (0, 0)).1,
        nonresidueTable9_checked (16 * 56 + k.val, (nonresidueCoverageData56.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 912.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData57 : List (ℕ × ℕ) :=
  [(0, 2), (0, 11), (0, 2), (0, 3), (0, 2), (0, 7), (0, 2), (3, 0), (0, 2), (0, 3), (0, 2), (0, 13),
    (0, 2), (0, 5), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 912 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock57 :
    ∀ k : Fin 16,
      5 ≤ 16 * 57 + k.val →
        16 * 57 + k.val < 3000 →
        (16 * 57 + k.val, (nonresidueCoverageData57.getD k.val (0, 0)).1) ∈ (nonresidueTable9) ∨
          (2 ≤ (nonresidueCoverageData57.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData57.getD k.val (0, 0)).2 < 16 * 57 + k.val ∧
            (nonresidueCoverageData57.getD k.val (0, 0)).2 ∣ 16 * 57 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 57 (nonresidueTable9) nonresidueCoverageData57 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 912,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock57_checked : smallNonresidueBlockChecked 57 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock57 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData57.getD k.val (0, 0)).1,
        nonresidueTable9_checked (16 * 57 + k.val, (nonresidueCoverageData57.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 928.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData58 : List (ℕ × ℕ) :=
  [(0, 2), (3, 0), (0, 2), (0, 7), (0, 2), (0, 3), (0, 2), (0, 5), (0, 2), (5, 0), (0, 2), (0, 3),
    (0, 2), (2, 0), (0, 2), (0, 23)]

/-- Every eligible integer beginning at 928 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock58 :
    ∀ k : Fin 16,
      5 ≤ 16 * 58 + k.val →
        16 * 58 + k.val < 3000 →
        (16 * 58 + k.val, (nonresidueCoverageData58.getD k.val (0, 0)).1) ∈ (nonresidueTable9) ∨
          (2 ≤ (nonresidueCoverageData58.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData58.getD k.val (0, 0)).2 < 16 * 58 + k.val ∧
            (nonresidueCoverageData58.getD k.val (0, 0)).2 ∣ 16 * 58 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 58 (nonresidueTable9) nonresidueCoverageData58 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 928,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock58_checked : smallNonresidueBlockChecked 58 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock58 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData58.getD k.val (0, 0)).1,
        nonresidueTable9_checked (16 * 58 + k.val, (nonresidueCoverageData58.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 944.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData59 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (0, 13), (0, 2), (0, 3), (0, 2), (3, 0), (0, 2), (0, 5),
    (0, 2), (0, 3), (0, 2), (0, 7)]

/-- Every eligible integer beginning at 944 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock59 :
    ∀ k : Fin 16,
      5 ≤ 16 * 59 + k.val →
        16 * 59 + k.val < 3000 →
        (16 * 59 + k.val, (nonresidueCoverageData59.getD k.val (0, 0)).1) ∈ (nonresidueTable9) ∨
          (2 ≤ (nonresidueCoverageData59.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData59.getD k.val (0, 0)).2 < 16 * 59 + k.val ∧
            (nonresidueCoverageData59.getD k.val (0, 0)).2 ∣ 16 * 59 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 59 (nonresidueTable9) nonresidueCoverageData59 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 944,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock59_checked : smallNonresidueBlockChecked 59 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock59 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData59.getD k.val (0, 0)).1,
        nonresidueTable9_checked (16 * 59 + k.val, (nonresidueCoverageData59.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 960.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData60 : List (ℕ × ℕ) :=
  [(0, 2), (0, 31), (0, 2), (0, 3), (0, 2), (0, 5), (0, 2), (3, 0), (0, 2), (0, 3), (0, 2), (2, 0),
    (0, 2), (0, 7), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 960 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock60 :
    ∀ k : Fin 16,
      5 ≤ 16 * 60 + k.val →
        16 * 60 + k.val < 3000 →
        (16 * 60 + k.val, (nonresidueCoverageData60.getD k.val (0, 0)).1) ∈ (nonresidueTable10) ∨
          (2 ≤ (nonresidueCoverageData60.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData60.getD k.val (0, 0)).2 < 16 * 60 + k.val ∧
            (nonresidueCoverageData60.getD k.val (0, 0)).2 ∣ 16 * 60 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 60 (nonresidueTable10) nonresidueCoverageData60 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 960,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock60_checked : smallNonresidueBlockChecked 60 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock60 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData60.getD k.val (0, 0)).1,
        nonresidueTable10_checked (16 * 60 + k.val, (nonresidueCoverageData60.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 976.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData61 : List (ℕ × ℕ) :=
  [(0, 2), (3, 0), (0, 2), (0, 11), (0, 2), (0, 3), (0, 2), (5, 0), (0, 2), (0, 5), (0, 2), (0, 3),
    (0, 2), (0, 23), (0, 2), (3, 0)]

/-- Every eligible integer beginning at 976 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock61 :
    ∀ k : Fin 16,
      5 ≤ 16 * 61 + k.val →
        16 * 61 + k.val < 3000 →
        (16 * 61 + k.val, (nonresidueCoverageData61.getD k.val (0, 0)).1) ∈ (nonresidueTable10) ∨
          (2 ≤ (nonresidueCoverageData61.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData61.getD k.val (0, 0)).2 < 16 * 61 + k.val ∧
            (nonresidueCoverageData61.getD k.val (0, 0)).2 ∣ 16 * 61 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 61 (nonresidueTable10) nonresidueCoverageData61 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 976,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock61_checked : smallNonresidueBlockChecked 61 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock61 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData61.getD k.val (0, 0)).1,
        nonresidueTable10_checked (16 * 61 + k.val, (nonresidueCoverageData61.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 992.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData62 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (0, 5), (0, 2), (2, 0), (0, 2), (0, 3), (0, 2), (0, 7), (0, 2), (0, 17),
    (0, 2), (0, 3), (0, 2), (0, 19)]

/-- Every eligible integer beginning at 992 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock62 :
    ∀ k : Fin 16,
      5 ≤ 16 * 62 + k.val →
        16 * 62 + k.val < 3000 →
        (16 * 62 + k.val, (nonresidueCoverageData62.getD k.val (0, 0)).1) ∈ (nonresidueTable10) ∨
          (2 ≤ (nonresidueCoverageData62.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData62.getD k.val (0, 0)).2 < 16 * 62 + k.val ∧
            (nonresidueCoverageData62.getD k.val (0, 0)).2 ∣ 16 * 62 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 62 (nonresidueTable10) nonresidueCoverageData62 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 992,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock62_checked : smallNonresidueBlockChecked 62 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock62 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData62.getD k.val (0, 0)).1,
        nonresidueTable10_checked (16 * 62 + k.val, (nonresidueCoverageData62.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1008.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData63 : List (ℕ × ℕ) :=
  [(0, 2), (11, 0), (0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (0, 5), (0, 2), (0, 3), (0, 2), (2, 0),
    (0, 2), (2, 0), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 1008 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock63 :
    ∀ k : Fin 16,
      5 ≤ 16 * 63 + k.val →
        16 * 63 + k.val < 3000 →
        (16 * 63 + k.val, (nonresidueCoverageData63.getD k.val (0, 0)).1) ∈ (nonresidueTable10) ∨
          (2 ≤ (nonresidueCoverageData63.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData63.getD k.val (0, 0)).2 < 16 * 63 + k.val ∧
            (nonresidueCoverageData63.getD k.val (0, 0)).2 ∣ 16 * 63 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 63 (nonresidueTable10) nonresidueCoverageData63 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1008,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock63_checked : smallNonresidueBlockChecked 63 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock63 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData63.getD k.val (0, 0)).1,
        nonresidueTable10_checked (16 * 63 + k.val, (nonresidueCoverageData63.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1024.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData64 : List (ℕ × ℕ) :=
  [(0, 2), (0, 5), (0, 2), (0, 13), (0, 2), (0, 3), (0, 2), (7, 0), (0, 2), (5, 0), (0, 2), (0, 3),
    (0, 2), (0, 17), (0, 2), (3, 0)]

/-- Every eligible integer beginning at 1024 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock64 :
    ∀ k : Fin 16,
      5 ≤ 16 * 64 + k.val →
        16 * 64 + k.val < 3000 →
        (16 * 64 + k.val, (nonresidueCoverageData64.getD k.val (0, 0)).1) ∈ (nonresidueTable10) ∨
          (2 ≤ (nonresidueCoverageData64.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData64.getD k.val (0, 0)).2 < 16 * 64 + k.val ∧
            (nonresidueCoverageData64.getD k.val (0, 0)).2 ∣ 16 * 64 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 64 (nonresidueTable10) nonresidueCoverageData64 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1024,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock64_checked : smallNonresidueBlockChecked 64 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock64 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData64.getD k.val (0, 0)).1,
        nonresidueTable10_checked (16 * 64 + k.val, (nonresidueCoverageData64.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1040.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData65 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (0, 7), (0, 2), (0, 5), (0, 2), (0, 3), (0, 2), (3, 0), (0, 2), (2, 0),
    (0, 2), (0, 3), (0, 2), (0, 5)]

/-- Every eligible integer beginning at 1040 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock65 :
    ∀ k : Fin 16,
      5 ≤ 16 * 65 + k.val →
        16 * 65 + k.val < 3000 →
        (16 * 65 + k.val, (nonresidueCoverageData65.getD k.val (0, 0)).1) ∈ (nonresidueTable10) ∨
          (2 ≤ (nonresidueCoverageData65.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData65.getD k.val (0, 0)).2 < 16 * 65 + k.val ∧
            (nonresidueCoverageData65.getD k.val (0, 0)).2 ∣ 16 * 65 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 65 (nonresidueTable10) nonresidueCoverageData65 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1040,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock65_checked : smallNonresidueBlockChecked 65 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock65 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData65.getD k.val (0, 0)).1,
        nonresidueTable10_checked (16 * 65 + k.val, (nonresidueCoverageData65.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1056.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData66 : List (ℕ × ℕ) :=
  [(0, 2), (0, 7), (0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (3, 0), (0, 2), (0, 3), (0, 2), (0, 11),
    (0, 2), (2, 0), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 1056 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock66 :
    ∀ k : Fin 16,
      5 ≤ 16 * 66 + k.val →
        16 * 66 + k.val < 3000 →
        (16 * 66 + k.val, (nonresidueCoverageData66.getD k.val (0, 0)).1) ∈
            (nonresidueTable10 ++ nonresidueTable11) ∨
          (2 ≤ (nonresidueCoverageData66.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData66.getD k.val (0, 0)).2 < 16 * 66 + k.val ∧
            (nonresidueCoverageData66.getD k.val (0, 0)).2 ∣ 16 * 66 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl :
      nonresidueCoverageCheck 66 (nonresidueTable10 ++ nonresidueTable11) nonresidueCoverageData66 =
        true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1056,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock66_checked : smallNonresidueBlockChecked 66 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock66 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData66.getD k.val (0, 0)).1,
        (nonresidueTableChecked_append nonresidueTable10_checked nonresidueTable11_checked)
          (16 * 66 + k.val, (nonresidueCoverageData66.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1072.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData67 : List (ℕ × ℕ) :=
  [(0, 2), (0, 29), (0, 2), (0, 5), (0, 2), (0, 3), (0, 2), (0, 13), (0, 2), (0, 23), (0, 2),
    (0, 3), (0, 2), (0, 5), (0, 2), (3, 0)]

/-- Every eligible integer beginning at 1072 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock67 :
    ∀ k : Fin 16,
      5 ≤ 16 * 67 + k.val →
        16 * 67 + k.val < 3000 →
        (16 * 67 + k.val, (nonresidueCoverageData67.getD k.val (0, 0)).1) ∈ (nonresidueTable11) ∨
          (2 ≤ (nonresidueCoverageData67.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData67.getD k.val (0, 0)).2 < 16 * 67 + k.val ∧
            (nonresidueCoverageData67.getD k.val (0, 0)).2 ∣ 16 * 67 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 67 (nonresidueTable11) nonresidueCoverageData67 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1072,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock67_checked : smallNonresidueBlockChecked 67 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock67 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData67.getD k.val (0, 0)).1,
        nonresidueTable11_checked (16 * 67 + k.val, (nonresidueCoverageData67.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1088.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData68 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (2, 0), (0, 2), (0, 3), (0, 2), (3, 0), (0, 2), (0, 7),
    (0, 2), (0, 3), (0, 2), (5, 0)]

/-- Every eligible integer beginning at 1088 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock68 :
    ∀ k : Fin 16,
      5 ≤ 16 * 68 + k.val →
        16 * 68 + k.val < 3000 →
        (16 * 68 + k.val, (nonresidueCoverageData68.getD k.val (0, 0)).1) ∈ (nonresidueTable11) ∨
          (2 ≤ (nonresidueCoverageData68.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData68.getD k.val (0, 0)).2 < 16 * 68 + k.val ∧
            (nonresidueCoverageData68.getD k.val (0, 0)).2 ∣ 16 * 68 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 68 (nonresidueTable11) nonresidueCoverageData68 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1088,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock68_checked : smallNonresidueBlockChecked 68 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock68 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData68.getD k.val (0, 0)).1,
        nonresidueTable11_checked (16 * 68 + k.val, (nonresidueCoverageData68.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1104.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData69 : List (ℕ × ℕ) :=
  [(0, 2), (0, 5), (0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (0, 11), (0, 2), (0, 3), (0, 2), (0, 5),
    (0, 2), (2, 0), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 1104 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock69 :
    ∀ k : Fin 16,
      5 ≤ 16 * 69 + k.val →
        16 * 69 + k.val < 3000 →
        (16 * 69 + k.val, (nonresidueCoverageData69.getD k.val (0, 0)).1) ∈ (nonresidueTable11) ∨
          (2 ≤ (nonresidueCoverageData69.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData69.getD k.val (0, 0)).2 < 16 * 69 + k.val ∧
            (nonresidueCoverageData69.getD k.val (0, 0)).2 ∣ 16 * 69 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 69 (nonresidueTable11) nonresidueCoverageData69 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1104,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock69_checked : smallNonresidueBlockChecked 69 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock69 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData69.getD k.val (0, 0)).1,
        nonresidueTable11_checked (16 * 69 + k.val, (nonresidueCoverageData69.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1120.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData70 : List (ℕ × ℕ) :=
  [(0, 2), (0, 19), (0, 2), (2, 0), (0, 2), (0, 3), (0, 2), (0, 7), (0, 2), (11, 0), (0, 2), (0, 3),
    (0, 2), (0, 11), (0, 2), (0, 5)]

/-- Every eligible integer beginning at 1120 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock70 :
    ∀ k : Fin 16,
      5 ≤ 16 * 70 + k.val →
        16 * 70 + k.val < 3000 →
        (16 * 70 + k.val, (nonresidueCoverageData70.getD k.val (0, 0)).1) ∈ (nonresidueTable11) ∨
          (2 ≤ (nonresidueCoverageData70.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData70.getD k.val (0, 0)).2 < 16 * 70 + k.val ∧
            (nonresidueCoverageData70.getD k.val (0, 0)).2 ∣ 16 * 70 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 70 (nonresidueTable11) nonresidueCoverageData70 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1120,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock70_checked : smallNonresidueBlockChecked 70 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock70 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData70.getD k.val (0, 0)).1,
        nonresidueTable11_checked (16 * 70 + k.val, (nonresidueCoverageData70.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1136.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData71 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (0, 17), (0, 2), (0, 7), (0, 2), (0, 3), (0, 2), (0, 5), (0, 2), (0, 31),
    (0, 2), (0, 3), (0, 2), (13, 0)]

/-- Every eligible integer beginning at 1136 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock71 :
    ∀ k : Fin 16,
      5 ≤ 16 * 71 + k.val →
        16 * 71 + k.val < 3000 →
        (16 * 71 + k.val, (nonresidueCoverageData71.getD k.val (0, 0)).1) ∈ (nonresidueTable11) ∨
          (2 ≤ (nonresidueCoverageData71.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData71.getD k.val (0, 0)).2 < 16 * 71 + k.val ∧
            (nonresidueCoverageData71.getD k.val (0, 0)).2 ∣ 16 * 71 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 71 (nonresidueTable11) nonresidueCoverageData71 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1136,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock71_checked : smallNonresidueBlockChecked 71 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock71 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData71.getD k.val (0, 0)).1,
        nonresidueTable11_checked (16 * 71 + k.val, (nonresidueCoverageData71.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1152.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData72 : List (ℕ × ℕ) :=
  [(0, 2), (5, 0), (0, 2), (0, 3), (0, 2), (0, 13), (0, 2), (0, 19), (0, 2), (0, 3), (0, 2), (2, 0),
    (0, 2), (0, 5), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 1152 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock72 :
    ∀ k : Fin 16,
      5 ≤ 16 * 72 + k.val →
        16 * 72 + k.val < 3000 →
        (16 * 72 + k.val, (nonresidueCoverageData72.getD k.val (0, 0)).1) ∈ (nonresidueTable11) ∨
          (2 ≤ (nonresidueCoverageData72.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData72.getD k.val (0, 0)).2 < 16 * 72 + k.val ∧
            (nonresidueCoverageData72.getD k.val (0, 0)).2 ∣ 16 * 72 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 72 (nonresidueTable11) nonresidueCoverageData72 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1152,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock72_checked : smallNonresidueBlockChecked 72 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock72 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData72.getD k.val (0, 0)).1,
        nonresidueTable11_checked (16 * 72 + k.val, (nonresidueCoverageData72.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1168.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData73 : List (ℕ × ℕ) :=
  [(0, 2), (0, 7), (0, 2), (2, 0), (0, 2), (0, 3), (0, 2), (0, 5), (0, 2), (0, 11), (0, 2), (0, 3),
    (0, 2), (2, 0), (0, 2), (0, 7)]

/-- Every eligible integer beginning at 1168 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock73 :
    ∀ k : Fin 16,
      5 ≤ 16 * 73 + k.val →
        16 * 73 + k.val < 3000 →
        (16 * 73 + k.val, (nonresidueCoverageData73.getD k.val (0, 0)).1) ∈ (nonresidueTable11) ∨
          (2 ≤ (nonresidueCoverageData73.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData73.getD k.val (0, 0)).2 < 16 * 73 + k.val ∧
            (nonresidueCoverageData73.getD k.val (0, 0)).2 ∣ 16 * 73 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 73 (nonresidueTable11) nonresidueCoverageData73 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1168,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock73_checked : smallNonresidueBlockChecked 73 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock73 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData73.getD k.val (0, 0)).1,
        nonresidueTable11_checked (16 * 73 + k.val, (nonresidueCoverageData73.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1184.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData74 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (0, 29), (0, 2), (0, 3), (0, 2), (3, 0), (0, 2), (0, 5),
    (0, 2), (0, 3), (0, 2), (0, 11)]

/-- Every eligible integer beginning at 1184 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock74 :
    ∀ k : Fin 16,
      5 ≤ 16 * 74 + k.val →
        16 * 74 + k.val < 3000 →
        (16 * 74 + k.val, (nonresidueCoverageData74.getD k.val (0, 0)).1) ∈ (nonresidueTable12) ∨
          (2 ≤ (nonresidueCoverageData74.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData74.getD k.val (0, 0)).2 < 16 * 74 + k.val ∧
            (nonresidueCoverageData74.getD k.val (0, 0)).2 ∣ 16 * 74 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 74 (nonresidueTable12) nonresidueCoverageData74 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1184,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock74_checked : smallNonresidueBlockChecked 74 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock74 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData74.getD k.val (0, 0)).1,
        nonresidueTable12_checked (16 * 74 + k.val, (nonresidueCoverageData74.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1200.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData75 : List (ℕ × ℕ) :=
  [(0, 2), (11, 0), (0, 2), (0, 3), (0, 2), (0, 5), (0, 2), (0, 17), (0, 2), (0, 3), (0, 2), (0, 7),
    (0, 2), (2, 0), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 1200 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock75 :
    ∀ k : Fin 16,
      5 ≤ 16 * 75 + k.val →
        16 * 75 + k.val < 3000 →
        (16 * 75 + k.val, (nonresidueCoverageData75.getD k.val (0, 0)).1) ∈ (nonresidueTable12) ∨
          (2 ≤ (nonresidueCoverageData75.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData75.getD k.val (0, 0)).2 < 16 * 75 + k.val ∧
            (nonresidueCoverageData75.getD k.val (0, 0)).2 ∣ 16 * 75 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 75 (nonresidueTable12) nonresidueCoverageData75 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1200,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock75_checked : smallNonresidueBlockChecked 75 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock75 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData75.getD k.val (0, 0)).1,
        nonresidueTable12_checked (16 * 75 + k.val, (nonresidueCoverageData75.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1216.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData76 : List (ℕ × ℕ) :=
  [(0, 2), (3, 0), (0, 2), (0, 23), (0, 2), (0, 3), (0, 2), (5, 0), (0, 2), (0, 5), (0, 2), (0, 3),
    (0, 2), (2, 0), (0, 2), (3, 0)]

/-- Every eligible integer beginning at 1216 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock76 :
    ∀ k : Fin 16,
      5 ≤ 16 * 76 + k.val →
        16 * 76 + k.val < 3000 →
        (16 * 76 + k.val, (nonresidueCoverageData76.getD k.val (0, 0)).1) ∈ (nonresidueTable12) ∨
          (2 ≤ (nonresidueCoverageData76.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData76.getD k.val (0, 0)).2 < 16 * 76 + k.val ∧
            (nonresidueCoverageData76.getD k.val (0, 0)).2 ∣ 16 * 76 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 76 (nonresidueTable12) nonresidueCoverageData76 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1216,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock76_checked : smallNonresidueBlockChecked 76 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock76 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData76.getD k.val (0, 0)).1,
        nonresidueTable12_checked (16 * 76 + k.val, (nonresidueCoverageData76.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1232.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData77 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (0, 5), (0, 2), (2, 0), (0, 2), (0, 3), (0, 2), (0, 17), (0, 2), (0, 11),
    (0, 2), (0, 3), (0, 2), (0, 29)]

/-- Every eligible integer beginning at 1232 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock77 :
    ∀ k : Fin 16,
      5 ≤ 16 * 77 + k.val →
        16 * 77 + k.val < 3000 →
        (16 * 77 + k.val, (nonresidueCoverageData77.getD k.val (0, 0)).1) ∈ (nonresidueTable12) ∨
          (2 ≤ (nonresidueCoverageData77.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData77.getD k.val (0, 0)).2 < 16 * 77 + k.val ∧
            (nonresidueCoverageData77.getD k.val (0, 0)).2 ∣ 16 * 77 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 77 (nonresidueTable12) nonresidueCoverageData77 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1232,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock77_checked : smallNonresidueBlockChecked 77 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock77 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData77.getD k.val (0, 0)).1,
        nonresidueTable12_checked (16 * 77 + k.val, (nonresidueCoverageData77.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1248.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData78 : List (ℕ × ℕ) :=
  [(0, 2), (7, 0), (0, 2), (0, 3), (0, 2), (0, 7), (0, 2), (0, 5), (0, 2), (0, 3), (0, 2), (2, 0),
    (0, 2), (0, 13), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 1248 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock78 :
    ∀ k : Fin 16,
      5 ≤ 16 * 78 + k.val →
        16 * 78 + k.val < 3000 →
        (16 * 78 + k.val, (nonresidueCoverageData78.getD k.val (0, 0)).1) ∈ (nonresidueTable12) ∨
          (2 ≤ (nonresidueCoverageData78.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData78.getD k.val (0, 0)).2 < 16 * 78 + k.val ∧
            (nonresidueCoverageData78.getD k.val (0, 0)).2 ∣ 16 * 78 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 78 (nonresidueTable12) nonresidueCoverageData78 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1248,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock78_checked : smallNonresidueBlockChecked 78 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock78 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData78.getD k.val (0, 0)).1,
        nonresidueTable12_checked (16 * 78 + k.val, (nonresidueCoverageData78.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1264.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData79 : List (ℕ × ℕ) :=
  [(0, 2), (0, 5), (0, 2), (0, 7), (0, 2), (0, 3), (0, 2), (0, 31), (0, 2), (0, 19), (0, 2), (0, 3),
    (0, 2), (2, 0), (0, 2), (3, 0)]

/-- Every eligible integer beginning at 1264 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock79 :
    ∀ k : Fin 16,
      5 ≤ 16 * 79 + k.val →
        16 * 79 + k.val < 3000 →
        (16 * 79 + k.val, (nonresidueCoverageData79.getD k.val (0, 0)).1) ∈ (nonresidueTable12) ∨
          (2 ≤ (nonresidueCoverageData79.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData79.getD k.val (0, 0)).2 < 16 * 79 + k.val ∧
            (nonresidueCoverageData79.getD k.val (0, 0)).2 ∣ 16 * 79 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 79 (nonresidueTable12) nonresidueCoverageData79 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1264,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock79_checked : smallNonresidueBlockChecked 79 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock79 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData79.getD k.val (0, 0)).1,
        nonresidueTable12_checked (16 * 79 + k.val, (nonresidueCoverageData79.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1280.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData80 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (0, 5), (0, 2), (0, 3), (0, 2), (3, 0), (0, 2), (2, 0),
    (0, 2), (0, 3), (0, 2), (0, 5)]

/-- Every eligible integer beginning at 1280 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock80 :
    ∀ k : Fin 16,
      5 ≤ 16 * 80 + k.val →
        16 * 80 + k.val < 3000 →
        (16 * 80 + k.val, (nonresidueCoverageData80.getD k.val (0, 0)).1) ∈ (nonresidueTable12) ∨
          (2 ≤ (nonresidueCoverageData80.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData80.getD k.val (0, 0)).2 < 16 * 80 + k.val ∧
            (nonresidueCoverageData80.getD k.val (0, 0)).2 ∣ 16 * 80 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 80 (nonresidueTable12) nonresidueCoverageData80 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1280,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock80_checked : smallNonresidueBlockChecked 80 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock80 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData80.getD k.val (0, 0)).1,
        nonresidueTable12_checked (16 * 80 + k.val, (nonresidueCoverageData80.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1296.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData81 : List (ℕ × ℕ) :=
  [(0, 2), (5, 0), (0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (3, 0), (0, 2), (0, 3), (0, 2), (2, 0),
    (0, 2), (0, 7), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 1296 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock81 :
    ∀ k : Fin 16,
      5 ≤ 16 * 81 + k.val →
        16 * 81 + k.val < 3000 →
        (16 * 81 + k.val, (nonresidueCoverageData81.getD k.val (0, 0)).1) ∈ (nonresidueTable13) ∨
          (2 ≤ (nonresidueCoverageData81.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData81.getD k.val (0, 0)).2 < 16 * 81 + k.val ∧
            (nonresidueCoverageData81.getD k.val (0, 0)).2 ∣ 16 * 81 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 81 (nonresidueTable13) nonresidueCoverageData81 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1296,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock81_checked : smallNonresidueBlockChecked 81 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock81 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData81.getD k.val (0, 0)).1,
        nonresidueTable13_checked (16 * 81 + k.val, (nonresidueCoverageData81.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1312.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData82 : List (ℕ × ℕ) :=
  [(0, 2), (0, 13), (0, 2), (0, 5), (0, 2), (0, 3), (0, 2), (13, 0), (0, 2), (7, 0), (0, 2), (0, 3),
    (0, 2), (0, 5), (0, 2), (3, 0)]

/-- Every eligible integer beginning at 1312 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock82 :
    ∀ k : Fin 16,
      5 ≤ 16 * 82 + k.val →
        16 * 82 + k.val < 3000 →
        (16 * 82 + k.val, (nonresidueCoverageData82.getD k.val (0, 0)).1) ∈ (nonresidueTable13) ∨
          (2 ≤ (nonresidueCoverageData82.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData82.getD k.val (0, 0)).2 < 16 * 82 + k.val ∧
            (nonresidueCoverageData82.getD k.val (0, 0)).2 ∣ 16 * 82 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 82 (nonresidueTable13) nonresidueCoverageData82 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1312,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock82_checked : smallNonresidueBlockChecked 82 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock82 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData82.getD k.val (0, 0)).1,
        nonresidueTable13_checked (16 * 82 + k.val, (nonresidueCoverageData82.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1328.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData83 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (0, 11), (0, 2), (0, 31), (0, 2), (0, 3), (0, 2), (0, 7), (0, 2),
    (0, 13), (0, 2), (0, 3), (0, 2), (0, 17)]

/-- Every eligible integer beginning at 1328 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock83 :
    ∀ k : Fin 16,
      5 ≤ 16 * 83 + k.val →
        16 * 83 + k.val < 3000 →
        (16 * 83 + k.val, (nonresidueCoverageData83.getD k.val (0, 0)).1) ∈ (nonresidueTable0) ∨
          (2 ≤ (nonresidueCoverageData83.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData83.getD k.val (0, 0)).2 < 16 * 83 + k.val ∧
            (nonresidueCoverageData83.getD k.val (0, 0)).2 ∣ 16 * 83 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 83 (nonresidueTable0) nonresidueCoverageData83 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1328,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock83_checked : smallNonresidueBlockChecked 83 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock83 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData83.getD k.val (0, 0)).1,
        nonresidueTable0_checked (16 * 83 + k.val, (nonresidueCoverageData83.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1344.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData84 : List (ℕ × ℕ) :=
  [(0, 2), (0, 5), (0, 2), (0, 3), (0, 2), (0, 19), (0, 2), (0, 7), (0, 2), (0, 3), (0, 2), (0, 5),
    (0, 2), (0, 23), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 1344 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock84 :
    ∀ k : Fin 16,
      5 ≤ 16 * 84 + k.val →
        16 * 84 + k.val < 3000 →
        (16 * 84 + k.val, (nonresidueCoverageData84.getD k.val (0, 0)).1) ∈ (nonresidueTable0) ∨
          (2 ≤ (nonresidueCoverageData84.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData84.getD k.val (0, 0)).2 < 16 * 84 + k.val ∧
            (nonresidueCoverageData84.getD k.val (0, 0)).2 ∣ 16 * 84 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 84 (nonresidueTable0) nonresidueCoverageData84 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1344,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock84_checked : smallNonresidueBlockChecked 84 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock84 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData84.getD k.val (0, 0)).1,
        nonresidueTable0_checked (16 * 84 + k.val, (nonresidueCoverageData84.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1360.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData85 : List (ℕ × ℕ) :=
  [(0, 2), (3, 0), (0, 2), (0, 29), (0, 2), (0, 3), (0, 2), (5, 0), (0, 2), (0, 37), (0, 2), (0, 3),
    (0, 2), (2, 0), (0, 2), (0, 5)]

/-- Every eligible integer beginning at 1360 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock85 :
    ∀ k : Fin 16,
      5 ≤ 16 * 85 + k.val →
        16 * 85 + k.val < 3000 →
        (16 * 85 + k.val, (nonresidueCoverageData85.getD k.val (0, 0)).1) ∈ (nonresidueTable13) ∨
          (2 ≤ (nonresidueCoverageData85.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData85.getD k.val (0, 0)).2 < 16 * 85 + k.val ∧
            (nonresidueCoverageData85.getD k.val (0, 0)).2 ∣ 16 * 85 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 85 (nonresidueTable13) nonresidueCoverageData85 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1360,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock85_checked : smallNonresidueBlockChecked 85 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock85 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData85.getD k.val (0, 0)).1,
        nonresidueTable13_checked (16 * 85 + k.val, (nonresidueCoverageData85.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1376.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData86 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (0, 7), (0, 2), (2, 0), (0, 2), (0, 3), (0, 2), (0, 5), (0, 2), (0, 19),
    (0, 2), (0, 3), (0, 2), (0, 13)]

/-- Every eligible integer beginning at 1376 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock86 :
    ∀ k : Fin 16,
      5 ≤ 16 * 86 + k.val →
        16 * 86 + k.val < 3000 →
        (16 * 86 + k.val, (nonresidueCoverageData86.getD k.val (0, 0)).1) ∈ (nonresidueTable13) ∨
          (2 ≤ (nonresidueCoverageData86.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData86.getD k.val (0, 0)).2 < 16 * 86 + k.val ∧
            (nonresidueCoverageData86.getD k.val (0, 0)).2 ∣ 16 * 86 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 86 (nonresidueTable13) nonresidueCoverageData86 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1376,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock86_checked : smallNonresidueBlockChecked 86 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock86 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData86.getD k.val (0, 0)).1,
        nonresidueTable13_checked (16 * 86 + k.val, (nonresidueCoverageData86.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1392.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData87 : List (ℕ × ℕ) :=
  [(0, 2), (0, 7), (0, 2), (0, 3), (0, 2), (0, 11), (0, 2), (3, 0), (0, 2), (0, 3), (0, 2), (0, 23),
    (0, 2), (0, 5), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 1392 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock87 :
    ∀ k : Fin 16,
      5 ≤ 16 * 87 + k.val →
        16 * 87 + k.val < 3000 →
        (16 * 87 + k.val, (nonresidueCoverageData87.getD k.val (0, 0)).1) ∈ (nonresidueTable13) ∨
          (2 ≤ (nonresidueCoverageData87.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData87.getD k.val (0, 0)).2 < 16 * 87 + k.val ∧
            (nonresidueCoverageData87.getD k.val (0, 0)).2 ∣ 16 * 87 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 87 (nonresidueTable13) nonresidueCoverageData87 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1392,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock87_checked : smallNonresidueBlockChecked 87 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock87 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData87.getD k.val (0, 0)).1,
        nonresidueTable13_checked (16 * 87 + k.val, (nonresidueCoverageData87.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1408.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData88 : List (ℕ × ℕ) :=
  [(0, 2), (3, 0), (0, 2), (0, 17), (0, 2), (0, 3), (0, 2), (0, 5), (0, 2), (0, 13), (0, 2), (0, 3),
    (0, 2), (0, 7), (0, 2), (3, 0)]

/-- Every eligible integer beginning at 1408 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock88 :
    ∀ k : Fin 16,
      5 ≤ 16 * 88 + k.val →
        16 * 88 + k.val < 3000 →
        (16 * 88 + k.val, (nonresidueCoverageData88.getD k.val (0, 0)).1) ∈ (nonresidueTable13) ∨
          (2 ≤ (nonresidueCoverageData88.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData88.getD k.val (0, 0)).2 < 16 * 88 + k.val ∧
            (nonresidueCoverageData88.getD k.val (0, 0)).2 ∣ 16 * 88 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 88 (nonresidueTable13) nonresidueCoverageData88 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1408,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock88_checked : smallNonresidueBlockChecked 88 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock88 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData88.getD k.val (0, 0)).1,
        nonresidueTable13_checked (16 * 88 + k.val, (nonresidueCoverageData88.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1424.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData89 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (2, 0), (0, 2), (0, 3), (0, 2), (3, 0), (0, 2), (0, 5),
    (0, 2), (0, 3), (0, 2), (7, 0)]

/-- Every eligible integer beginning at 1424 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock89 :
    ∀ k : Fin 16,
      5 ≤ 16 * 89 + k.val →
        16 * 89 + k.val < 3000 →
        (16 * 89 + k.val, (nonresidueCoverageData89.getD k.val (0, 0)).1) ∈
            (nonresidueTable13 ++ nonresidueTable14) ∨
          (2 ≤ (nonresidueCoverageData89.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData89.getD k.val (0, 0)).2 < 16 * 89 + k.val ∧
            (nonresidueCoverageData89.getD k.val (0, 0)).2 ∣ 16 * 89 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl :
      nonresidueCoverageCheck 89 (nonresidueTable13 ++ nonresidueTable14) nonresidueCoverageData89 =
        true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1424,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock89_checked : smallNonresidueBlockChecked 89 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock89 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData89.getD k.val (0, 0)).1,
        (nonresidueTableChecked_append nonresidueTable13_checked nonresidueTable14_checked)
          (16 * 89 + k.val, (nonresidueCoverageData89.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1440.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData90 : List (ℕ × ℕ) :=
  [(0, 2), (0, 11), (0, 2), (0, 3), (0, 2), (0, 5), (0, 2), (3, 0), (0, 2), (0, 3), (0, 2), (2, 0),
    (0, 2), (2, 0), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 1440 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock90 :
    ∀ k : Fin 16,
      5 ≤ 16 * 90 + k.val →
        16 * 90 + k.val < 3000 →
        (16 * 90 + k.val, (nonresidueCoverageData90.getD k.val (0, 0)).1) ∈ (nonresidueTable14) ∨
          (2 ≤ (nonresidueCoverageData90.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData90.getD k.val (0, 0)).2 < 16 * 90 + k.val ∧
            (nonresidueCoverageData90.getD k.val (0, 0)).2 ∣ 16 * 90 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 90 (nonresidueTable14) nonresidueCoverageData90 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1440,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock90_checked : smallNonresidueBlockChecked 90 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock90 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData90.getD k.val (0, 0)).1,
        nonresidueTable14_checked (16 * 90 + k.val, (nonresidueCoverageData90.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1456.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData91 : List (ℕ × ℕ) :=
  [(0, 2), (0, 31), (0, 2), (2, 0), (0, 2), (0, 3), (0, 2), (0, 7), (0, 2), (0, 5), (0, 2), (0, 3),
    (0, 2), (0, 13), (0, 2), (3, 0)]

/-- Every eligible integer beginning at 1456 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock91 :
    ∀ k : Fin 16,
      5 ≤ 16 * 91 + k.val →
        16 * 91 + k.val < 3000 →
        (16 * 91 + k.val, (nonresidueCoverageData91.getD k.val (0, 0)).1) ∈ (nonresidueTable14) ∨
          (2 ≤ (nonresidueCoverageData91.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData91.getD k.val (0, 0)).2 < 16 * 91 + k.val ∧
            (nonresidueCoverageData91.getD k.val (0, 0)).2 ∣ 16 * 91 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 91 (nonresidueTable14) nonresidueCoverageData91 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1456,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock91_checked : smallNonresidueBlockChecked 91 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock91 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData91.getD k.val (0, 0)).1,
        nonresidueTable14_checked (16 * 91 + k.val, (nonresidueCoverageData91.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1472.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData92 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (0, 5), (0, 2), (0, 7), (0, 2), (0, 3), (0, 2), (3, 0), (0, 2), (2, 0),
    (0, 2), (0, 3), (0, 2), (5, 0)]

/-- Every eligible integer beginning at 1472 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock92 :
    ∀ k : Fin 16,
      5 ≤ 16 * 92 + k.val →
        16 * 92 + k.val < 3000 →
        (16 * 92 + k.val, (nonresidueCoverageData92.getD k.val (0, 0)).1) ∈ (nonresidueTable14) ∨
          (2 ≤ (nonresidueCoverageData92.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData92.getD k.val (0, 0)).2 < 16 * 92 + k.val ∧
            (nonresidueCoverageData92.getD k.val (0, 0)).2 ∣ 16 * 92 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 92 (nonresidueTable14) nonresidueCoverageData92 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1472,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock92_checked : smallNonresidueBlockChecked 92 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock92 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData92.getD k.val (0, 0)).1,
        nonresidueTable14_checked (16 * 92 + k.val, (nonresidueCoverageData92.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1488.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData93 : List (ℕ × ℕ) :=
  [(0, 2), (7, 0), (0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (0, 5), (0, 2), (0, 3), (0, 2), (2, 0),
    (0, 2), (0, 19), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 1488 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock93 :
    ∀ k : Fin 16,
      5 ≤ 16 * 93 + k.val →
        16 * 93 + k.val < 3000 →
        (16 * 93 + k.val, (nonresidueCoverageData93.getD k.val (0, 0)).1) ∈ (nonresidueTable14) ∨
          (2 ≤ (nonresidueCoverageData93.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData93.getD k.val (0, 0)).2 < 16 * 93 + k.val ∧
            (nonresidueCoverageData93.getD k.val (0, 0)).2 ∣ 16 * 93 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 93 (nonresidueTable14) nonresidueCoverageData93 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1488,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock93_checked : smallNonresidueBlockChecked 93 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock93 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData93.getD k.val (0, 0)).1,
        nonresidueTable14_checked (16 * 93 + k.val, (nonresidueCoverageData93.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1504.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData94 : List (ℕ × ℕ) :=
  [(0, 2), (0, 5), (0, 2), (0, 11), (0, 2), (0, 3), (0, 2), (11, 0), (0, 2), (0, 17), (0, 2),
    (0, 3), (0, 2), (0, 37), (0, 2), (0, 7)]

/-- Every eligible integer beginning at 1504 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock94 :
    ∀ k : Fin 16,
      5 ≤ 16 * 94 + k.val →
        16 * 94 + k.val < 3000 →
        (16 * 94 + k.val, (nonresidueCoverageData94.getD k.val (0, 0)).1) ∈ (nonresidueTable14) ∨
          (2 ≤ (nonresidueCoverageData94.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData94.getD k.val (0, 0)).2 < 16 * 94 + k.val ∧
            (nonresidueCoverageData94.getD k.val (0, 0)).2 ∣ 16 * 94 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 94 (nonresidueTable14) nonresidueCoverageData94 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1504,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock94_checked : smallNonresidueBlockChecked 94 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock94 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData94.getD k.val (0, 0)).1,
        nonresidueTable14_checked (16 * 94 + k.val, (nonresidueCoverageData94.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1520.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData95 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (0, 5), (0, 2), (0, 3), (0, 2), (0, 11), (0, 2), (2, 0),
    (0, 2), (0, 3), (0, 2), (0, 5)]

/-- Every eligible integer beginning at 1520 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock95 :
    ∀ k : Fin 16,
      5 ≤ 16 * 95 + k.val →
        16 * 95 + k.val < 3000 →
        (16 * 95 + k.val, (nonresidueCoverageData95.getD k.val (0, 0)).1) ∈ (nonresidueTable14) ∨
          (2 ≤ (nonresidueCoverageData95.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData95.getD k.val (0, 0)).2 < 16 * 95 + k.val ∧
            (nonresidueCoverageData95.getD k.val (0, 0)).2 ∣ 16 * 95 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 95 (nonresidueTable14) nonresidueCoverageData95 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1520,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock95_checked : smallNonresidueBlockChecked 95 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock95 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData95.getD k.val (0, 0)).1,
        nonresidueTable14_checked (16 * 95 + k.val, (nonresidueCoverageData95.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1536.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData96 : List (ℕ × ℕ) :=
  [(0, 2), (0, 29), (0, 2), (0, 3), (0, 2), (0, 23), (0, 2), (3, 0), (0, 2), (0, 3), (0, 2), (0, 7),
    (0, 2), (2, 0), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 1536 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock96 :
    ∀ k : Fin 16,
      5 ≤ 16 * 96 + k.val →
        16 * 96 + k.val < 3000 →
        (16 * 96 + k.val, (nonresidueCoverageData96.getD k.val (0, 0)).1) ∈ (nonresidueTable15) ∨
          (2 ≤ (nonresidueCoverageData96.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData96.getD k.val (0, 0)).2 < 16 * 96 + k.val ∧
            (nonresidueCoverageData96.getD k.val (0, 0)).2 ∣ 16 * 96 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 96 (nonresidueTable15) nonresidueCoverageData96 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1536,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock96_checked : smallNonresidueBlockChecked 96 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock96 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData96.getD k.val (0, 0)).1,
        nonresidueTable15_checked (16 * 96 + k.val, (nonresidueCoverageData96.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1552.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData97 : List (ℕ × ℕ) :=
  [(0, 2), (3, 0), (0, 2), (0, 5), (0, 2), (0, 3), (0, 2), (17, 0), (0, 2), (0, 7), (0, 2), (0, 3),
    (0, 2), (0, 5), (0, 2), (3, 0)]

/-- Every eligible integer beginning at 1552 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock97 :
    ∀ k : Fin 16,
      5 ≤ 16 * 97 + k.val →
        16 * 97 + k.val < 3000 →
        (16 * 97 + k.val, (nonresidueCoverageData97.getD k.val (0, 0)).1) ∈ (nonresidueTable15) ∨
          (2 ≤ (nonresidueCoverageData97.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData97.getD k.val (0, 0)).2 < 16 * 97 + k.val ∧
            (nonresidueCoverageData97.getD k.val (0, 0)).2 ∣ 16 * 97 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 97 (nonresidueTable15) nonresidueCoverageData97 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1552,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock97_checked : smallNonresidueBlockChecked 97 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock97 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData97.getD k.val (0, 0)).1,
        nonresidueTable15_checked (16 * 97 + k.val, (nonresidueCoverageData97.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1568.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData98 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (0, 11), (0, 2), (0, 3), (0, 2), (0, 19), (0, 2), (2, 0),
    (0, 2), (0, 3), (0, 2), (5, 0)]

/-- Every eligible integer beginning at 1568 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock98 :
    ∀ k : Fin 16,
      5 ≤ 16 * 98 + k.val →
        16 * 98 + k.val < 3000 →
        (16 * 98 + k.val, (nonresidueCoverageData98.getD k.val (0, 0)).1) ∈ (nonresidueTable15) ∨
          (2 ≤ (nonresidueCoverageData98.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData98.getD k.val (0, 0)).2 < 16 * 98 + k.val ∧
            (nonresidueCoverageData98.getD k.val (0, 0)).2 ∣ 16 * 98 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 98 (nonresidueTable15) nonresidueCoverageData98 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1568,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock98_checked : smallNonresidueBlockChecked 98 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock98 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData98.getD k.val (0, 0)).1,
        nonresidueTable15_checked (16 * 98 + k.val, (nonresidueCoverageData98.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1584.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData99 : List (ℕ × ℕ) :=
  [(0, 2), (0, 5), (0, 2), (0, 3), (0, 2), (0, 7), (0, 2), (0, 37), (0, 2), (0, 3), (0, 2), (0, 5),
    (0, 2), (2, 0), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 1584 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock99 :
    ∀ k : Fin 16,
      5 ≤ 16 * 99 + k.val →
        16 * 99 + k.val < 3000 →
        (16 * 99 + k.val, (nonresidueCoverageData99.getD k.val (0, 0)).1) ∈ (nonresidueTable15) ∨
          (2 ≤ (nonresidueCoverageData99.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData99.getD k.val (0, 0)).2 < 16 * 99 + k.val ∧
            (nonresidueCoverageData99.getD k.val (0, 0)).2 ∣ 16 * 99 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 99 (nonresidueTable15) nonresidueCoverageData99 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1584,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock99_checked : smallNonresidueBlockChecked 99 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock99 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData99.getD k.val (0, 0)).1,
        nonresidueTable15_checked (16 * 99 + k.val, (nonresidueCoverageData99.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1600.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData100 : List (ℕ × ℕ) :=
  [(0, 2), (3, 0), (0, 2), (0, 7), (0, 2), (0, 3), (0, 2), (5, 0), (0, 2), (7, 0), (0, 2), (0, 3),
    (0, 2), (2, 0), (0, 2), (0, 5)]

/-- Every eligible integer beginning at 1600 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock100 :
    ∀ k : Fin 16,
      5 ≤ 16 * 100 + k.val →
        16 * 100 + k.val < 3000 →
        (16 * 100 + k.val, (nonresidueCoverageData100.getD k.val (0, 0)).1) ∈ (nonresidueTable15) ∨
          (2 ≤ (nonresidueCoverageData100.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData100.getD k.val (0, 0)).2 < 16 * 100 + k.val ∧
            (nonresidueCoverageData100.getD k.val (0, 0)).2 ∣ 16 * 100 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 100 (nonresidueTable15) nonresidueCoverageData100 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1600,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock100_checked : smallNonresidueBlockChecked 100 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock100 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData100.getD k.val (0, 0)).1,
        nonresidueTable15_checked
          (16 * 100 + k.val, (nonresidueCoverageData100.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1616.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData101 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (2, 0), (0, 2), (0, 3), (0, 2), (0, 5), (0, 2), (2, 0),
    (0, 2), (0, 3), (0, 2), (0, 7)]

/-- Every eligible integer beginning at 1616 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock101 :
    ∀ k : Fin 16,
      5 ≤ 16 * 101 + k.val →
        16 * 101 + k.val < 3000 →
        (16 * 101 + k.val, (nonresidueCoverageData101.getD k.val (0, 0)).1) ∈ (nonresidueTable15) ∨
          (2 ≤ (nonresidueCoverageData101.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData101.getD k.val (0, 0)).2 < 16 * 101 + k.val ∧
            (nonresidueCoverageData101.getD k.val (0, 0)).2 ∣ 16 * 101 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 101 (nonresidueTable15) nonresidueCoverageData101 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1616,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock101_checked : smallNonresidueBlockChecked 101 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock101 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData101.getD k.val (0, 0)).1,
        nonresidueTable15_checked
          (16 * 101 + k.val, (nonresidueCoverageData101.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1632.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData102 : List (ℕ × ℕ) :=
  [(0, 2), (0, 23), (0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (0, 11), (0, 2), (0, 3), (0, 2),
    (0, 31), (0, 2), (0, 5), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 1632 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock102 :
    ∀ k : Fin 16,
      5 ≤ 16 * 102 + k.val →
        16 * 102 + k.val < 3000 →
        (16 * 102 + k.val, (nonresidueCoverageData102.getD k.val (0, 0)).1) ∈ (nonresidueTable16) ∨
          (2 ≤ (nonresidueCoverageData102.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData102.getD k.val (0, 0)).2 < 16 * 102 + k.val ∧
            (nonresidueCoverageData102.getD k.val (0, 0)).2 ∣ 16 * 102 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 102 (nonresidueTable16) nonresidueCoverageData102 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1632,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock102_checked : smallNonresidueBlockChecked 102 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock102 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData102.getD k.val (0, 0)).1,
        nonresidueTable16_checked
          (16 * 102 + k.val, (nonresidueCoverageData102.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1648.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData103 : List (ℕ × ℕ) :=
  [(0, 2), (0, 17), (0, 2), (0, 13), (0, 2), (0, 3), (0, 2), (0, 5), (0, 2), (5, 0), (0, 2), (0, 3),
    (0, 2), (0, 11), (0, 2), (3, 0)]

/-- Every eligible integer beginning at 1648 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock103 :
    ∀ k : Fin 16,
      5 ≤ 16 * 103 + k.val →
        16 * 103 + k.val < 3000 →
        (16 * 103 + k.val, (nonresidueCoverageData103.getD k.val (0, 0)).1) ∈ (nonresidueTable16) ∨
          (2 ≤ (nonresidueCoverageData103.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData103.getD k.val (0, 0)).2 < 16 * 103 + k.val ∧
            (nonresidueCoverageData103.getD k.val (0, 0)).2 ∣ 16 * 103 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 103 (nonresidueTable16) nonresidueCoverageData103 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1648,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock103_checked : smallNonresidueBlockChecked 103 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock103 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData103.getD k.val (0, 0)).1,
        nonresidueTable16_checked
          (16 * 103 + k.val, (nonresidueCoverageData103.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1664.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData104 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (2, 0), (0, 2), (0, 3), (0, 2), (0, 7), (0, 2), (0, 5),
    (0, 2), (0, 3), (0, 2), (0, 23)]

/-- Every eligible integer beginning at 1664 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock104 :
    ∀ k : Fin 16,
      5 ≤ 16 * 104 + k.val →
        16 * 104 + k.val < 3000 →
        (16 * 104 + k.val, (nonresidueCoverageData104.getD k.val (0, 0)).1) ∈ (nonresidueTable16) ∨
          (2 ≤ (nonresidueCoverageData104.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData104.getD k.val (0, 0)).2 < 16 * 104 + k.val ∧
            (nonresidueCoverageData104.getD k.val (0, 0)).2 ∣ 16 * 104 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 104 (nonresidueTable16) nonresidueCoverageData104 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1664,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock104_checked : smallNonresidueBlockChecked 104 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock104 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData104.getD k.val (0, 0)).1,
        nonresidueTable16_checked
          (16 * 104 + k.val, (nonresidueCoverageData104.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1680.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData105 : List (ℕ × ℕ) :=
  [(0, 2), (0, 41), (0, 2), (0, 3), (0, 2), (0, 5), (0, 2), (0, 7), (0, 2), (0, 3), (0, 2), (0, 19),
    (0, 2), (2, 0), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 1680 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock105 :
    ∀ k : Fin 16,
      5 ≤ 16 * 105 + k.val →
        16 * 105 + k.val < 3000 →
        (16 * 105 + k.val, (nonresidueCoverageData105.getD k.val (0, 0)).1) ∈ (nonresidueTable16) ∨
          (2 ≤ (nonresidueCoverageData105.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData105.getD k.val (0, 0)).2 < 16 * 105 + k.val ∧
            (nonresidueCoverageData105.getD k.val (0, 0)).2 ∣ 16 * 105 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 105 (nonresidueTable16) nonresidueCoverageData105 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1680,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock105_checked : smallNonresidueBlockChecked 105 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock105 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData105.getD k.val (0, 0)).1,
        nonresidueTable16_checked
          (16 * 105 + k.val, (nonresidueCoverageData105.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1696.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData106 : List (ℕ × ℕ) :=
  [(0, 2), (3, 0), (0, 2), (2, 0), (0, 2), (0, 3), (0, 2), (0, 13), (0, 2), (0, 5), (0, 2), (0, 3),
    (0, 2), (2, 0), (0, 2), (0, 29)]

/-- Every eligible integer beginning at 1696 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock106 :
    ∀ k : Fin 16,
      5 ≤ 16 * 106 + k.val →
        16 * 106 + k.val < 3000 →
        (16 * 106 + k.val, (nonresidueCoverageData106.getD k.val (0, 0)).1) ∈ (nonresidueTable16) ∨
          (2 ≤ (nonresidueCoverageData106.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData106.getD k.val (0, 0)).2 < 16 * 106 + k.val ∧
            (nonresidueCoverageData106.getD k.val (0, 0)).2 ∣ 16 * 106 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 106 (nonresidueTable16) nonresidueCoverageData106 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1696,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock106_checked : smallNonresidueBlockChecked 106 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock106 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData106.getD k.val (0, 0)).1,
        nonresidueTable16_checked
          (16 * 106 + k.val, (nonresidueCoverageData106.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1712.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData107 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (0, 5), (0, 2), (0, 17), (0, 2), (0, 3), (0, 2), (3, 0), (0, 2), (2, 0),
    (0, 2), (0, 3), (0, 2), (0, 11)]

/-- Every eligible integer beginning at 1712 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock107 :
    ∀ k : Fin 16,
      5 ≤ 16 * 107 + k.val →
        16 * 107 + k.val < 3000 →
        (16 * 107 + k.val, (nonresidueCoverageData107.getD k.val (0, 0)).1) ∈ (nonresidueTable16) ∨
          (2 ≤ (nonresidueCoverageData107.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData107.getD k.val (0, 0)).2 < 16 * 107 + k.val ∧
            (nonresidueCoverageData107.getD k.val (0, 0)).2 ∣ 16 * 107 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 107 (nonresidueTable16) nonresidueCoverageData107 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1712,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock107_checked : smallNonresidueBlockChecked 107 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock107 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData107.getD k.val (0, 0)).1,
        nonresidueTable16_checked
          (16 * 107 + k.val, (nonresidueCoverageData107.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1728.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData108 : List (ℕ × ℕ) :=
  [(0, 2), (0, 7), (0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (0, 5), (0, 2), (0, 3), (0, 2), (0, 37),
    (0, 2), (2, 0), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 1728 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock108 :
    ∀ k : Fin 16,
      5 ≤ 16 * 108 + k.val →
        16 * 108 + k.val < 3000 →
        (16 * 108 + k.val, (nonresidueCoverageData108.getD k.val (0, 0)).1) ∈ (nonresidueTable16) ∨
          (2 ≤ (nonresidueCoverageData108.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData108.getD k.val (0, 0)).2 < 16 * 108 + k.val ∧
            (nonresidueCoverageData108.getD k.val (0, 0)).2 ∣ 16 * 108 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 108 (nonresidueTable16) nonresidueCoverageData108 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1728,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock108_checked : smallNonresidueBlockChecked 108 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock108 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData108.getD k.val (0, 0)).1,
        nonresidueTable16_checked
          (16 * 108 + k.val, (nonresidueCoverageData108.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1744.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData109 : List (ℕ × ℕ) :=
  [(0, 2), (0, 5), (0, 2), (2, 0), (0, 2), (0, 3), (0, 2), (0, 17), (0, 2), (5, 0), (0, 2), (0, 3),
    (0, 2), (0, 7), (0, 2), (3, 0)]

/-- Every eligible integer beginning at 1744 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock109 :
    ∀ k : Fin 16,
      5 ≤ 16 * 109 + k.val →
        16 * 109 + k.val < 3000 →
        (16 * 109 + k.val, (nonresidueCoverageData109.getD k.val (0, 0)).1) ∈ (nonresidueTable16) ∨
          (2 ≤ (nonresidueCoverageData109.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData109.getD k.val (0, 0)).2 < 16 * 109 + k.val ∧
            (nonresidueCoverageData109.getD k.val (0, 0)).2 ∣ 16 * 109 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 109 (nonresidueTable16) nonresidueCoverageData109 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1744,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock109_checked : smallNonresidueBlockChecked 109 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock109 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData109.getD k.val (0, 0)).1,
        nonresidueTable16_checked
          (16 * 109 + k.val, (nonresidueCoverageData109.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1760.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData110 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (0, 41), (0, 2), (0, 5), (0, 2), (0, 3), (0, 2), (0, 29), (0, 2), (0, 7),
    (0, 2), (0, 3), (0, 2), (0, 5)]

/-- Every eligible integer beginning at 1760 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock110 :
    ∀ k : Fin 16,
      5 ≤ 16 * 110 + k.val →
        16 * 110 + k.val < 3000 →
        (16 * 110 + k.val, (nonresidueCoverageData110.getD k.val (0, 0)).1) ∈ (nonresidueTable0) ∨
          (2 ≤ (nonresidueCoverageData110.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData110.getD k.val (0, 0)).2 < 16 * 110 + k.val ∧
            (nonresidueCoverageData110.getD k.val (0, 0)).2 ∣ 16 * 110 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 110 (nonresidueTable0) nonresidueCoverageData110 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1760,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock110_checked : smallNonresidueBlockChecked 110 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock110 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData110.getD k.val (0, 0)).1,
        nonresidueTable0_checked (16 * 110 + k.val, (nonresidueCoverageData110.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1776.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData111 : List (ℕ × ℕ) :=
  [(0, 2), (5, 0), (0, 2), (0, 3), (0, 2), (0, 13), (0, 2), (3, 0), (0, 2), (0, 3), (0, 2), (2, 0),
    (0, 2), (2, 0), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 1776 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock111 :
    ∀ k : Fin 16,
      5 ≤ 16 * 111 + k.val →
        16 * 111 + k.val < 3000 →
        (16 * 111 + k.val, (nonresidueCoverageData111.getD k.val (0, 0)).1) ∈ (nonresidueTable17) ∨
          (2 ≤ (nonresidueCoverageData111.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData111.getD k.val (0, 0)).2 < 16 * 111 + k.val ∧
            (nonresidueCoverageData111.getD k.val (0, 0)).2 ∣ 16 * 111 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 111 (nonresidueTable17) nonresidueCoverageData111 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1776,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock111_checked : smallNonresidueBlockChecked 111 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock111 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData111.getD k.val (0, 0)).1,
        nonresidueTable17_checked
          (16 * 111 + k.val, (nonresidueCoverageData111.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1792.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData112 : List (ℕ × ℕ) :=
  [(0, 2), (0, 11), (0, 2), (0, 5), (0, 2), (0, 3), (0, 2), (0, 7), (0, 2), (11, 0), (0, 2), (0, 3),
    (0, 2), (0, 5), (0, 2), (0, 13)]

/-- Every eligible integer beginning at 1792 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock112 :
    ∀ k : Fin 16,
      5 ≤ 16 * 112 + k.val →
        16 * 112 + k.val < 3000 →
        (16 * 112 + k.val, (nonresidueCoverageData112.getD k.val (0, 0)).1) ∈ (nonresidueTable17) ∨
          (2 ≤ (nonresidueCoverageData112.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData112.getD k.val (0, 0)).2 < 16 * 112 + k.val ∧
            (nonresidueCoverageData112.getD k.val (0, 0)).2 ∣ 16 * 112 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 112 (nonresidueTable17) nonresidueCoverageData112 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1792,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock112_checked : smallNonresidueBlockChecked 112 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock112 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData112.getD k.val (0, 0)).1,
        nonresidueTable17_checked
          (16 * 112 + k.val, (nonresidueCoverageData112.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1808.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData113 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (0, 7), (0, 2), (0, 3), (0, 2), (0, 23), (0, 2), (0, 17),
    (0, 2), (0, 3), (0, 2), (5, 0)]

/-- Every eligible integer beginning at 1808 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock113 :
    ∀ k : Fin 16,
      5 ≤ 16 * 113 + k.val →
        16 * 113 + k.val < 3000 →
        (16 * 113 + k.val, (nonresidueCoverageData113.getD k.val (0, 0)).1) ∈ (nonresidueTable17) ∨
          (2 ≤ (nonresidueCoverageData113.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData113.getD k.val (0, 0)).2 < 16 * 113 + k.val ∧
            (nonresidueCoverageData113.getD k.val (0, 0)).2 ∣ 16 * 113 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 113 (nonresidueTable17) nonresidueCoverageData113 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1808,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock113_checked : smallNonresidueBlockChecked 113 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock113 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData113.getD k.val (0, 0)).1,
        nonresidueTable17_checked
          (16 * 113 + k.val, (nonresidueCoverageData113.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1824.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData114 : List (ℕ × ℕ) :=
  [(0, 2), (0, 5), (0, 2), (0, 3), (0, 2), (0, 31), (0, 2), (3, 0), (0, 2), (0, 3), (0, 2), (0, 5),
    (0, 2), (0, 11), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 1824 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock114 :
    ∀ k : Fin 16,
      5 ≤ 16 * 114 + k.val →
        16 * 114 + k.val < 3000 →
        (16 * 114 + k.val, (nonresidueCoverageData114.getD k.val (0, 0)).1) ∈ (nonresidueTable17) ∨
          (2 ≤ (nonresidueCoverageData114.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData114.getD k.val (0, 0)).2 < 16 * 114 + k.val ∧
            (nonresidueCoverageData114.getD k.val (0, 0)).2 ∣ 16 * 114 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 114 (nonresidueTable17) nonresidueCoverageData114 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1824,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock114_checked : smallNonresidueBlockChecked 114 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock114 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData114.getD k.val (0, 0)).1,
        nonresidueTable17_checked
          (16 * 114 + k.val, (nonresidueCoverageData114.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1840.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData115 : List (ℕ × ℕ) :=
  [(0, 2), (0, 7), (0, 2), (0, 19), (0, 2), (0, 3), (0, 2), (5, 0), (0, 2), (0, 43), (0, 2), (0, 3),
    (0, 2), (0, 17), (0, 2), (0, 5)]

/-- Every eligible integer beginning at 1840 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock115 :
    ∀ k : Fin 16,
      5 ≤ 16 * 115 + k.val →
        16 * 115 + k.val < 3000 →
        (16 * 115 + k.val, (nonresidueCoverageData115.getD k.val (0, 0)).1) ∈ (nonresidueTable17) ∨
          (2 ≤ (nonresidueCoverageData115.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData115.getD k.val (0, 0)).2 < 16 * 115 + k.val ∧
            (nonresidueCoverageData115.getD k.val (0, 0)).2 ∣ 16 * 115 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 115 (nonresidueTable17) nonresidueCoverageData115 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1840,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock115_checked : smallNonresidueBlockChecked 115 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock115 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData115.getD k.val (0, 0)).1,
        nonresidueTable17_checked
          (16 * 115 + k.val, (nonresidueCoverageData115.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1856.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData116 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (0, 11), (0, 2), (2, 0), (0, 2), (0, 3), (0, 2), (0, 5), (0, 2), (2, 0),
    (0, 2), (0, 3), (0, 2), (7, 0)]

/-- Every eligible integer beginning at 1856 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock116 :
    ∀ k : Fin 16,
      5 ≤ 16 * 116 + k.val →
        16 * 116 + k.val < 3000 →
        (16 * 116 + k.val, (nonresidueCoverageData116.getD k.val (0, 0)).1) ∈ (nonresidueTable17) ∨
          (2 ≤ (nonresidueCoverageData116.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData116.getD k.val (0, 0)).2 < 16 * 116 + k.val ∧
            (nonresidueCoverageData116.getD k.val (0, 0)).2 ∣ 16 * 116 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 116 (nonresidueTable17) nonresidueCoverageData116 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1856,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock116_checked : smallNonresidueBlockChecked 116 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock116 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData116.getD k.val (0, 0)).1,
        nonresidueTable17_checked
          (16 * 116 + k.val, (nonresidueCoverageData116.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1872.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData117 : List (ℕ × ℕ) :=
  [(0, 2), (5, 0), (0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (3, 0), (0, 2), (0, 3), (0, 2), (0, 7),
    (0, 2), (0, 5), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 1872 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock117 :
    ∀ k : Fin 16,
      5 ≤ 16 * 117 + k.val →
        16 * 117 + k.val < 3000 →
        (16 * 117 + k.val, (nonresidueCoverageData117.getD k.val (0, 0)).1) ∈ (nonresidueTable17) ∨
          (2 ≤ (nonresidueCoverageData117.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData117.getD k.val (0, 0)).2 < 16 * 117 + k.val ∧
            (nonresidueCoverageData117.getD k.val (0, 0)).2 ∣ 16 * 117 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 117 (nonresidueTable17) nonresidueCoverageData117 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1872,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock117_checked : smallNonresidueBlockChecked 117 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock117 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData117.getD k.val (0, 0)).1,
        nonresidueTable17_checked
          (16 * 117 + k.val, (nonresidueCoverageData117.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1888.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData118 : List (ℕ × ℕ) :=
  [(0, 2), (3, 0), (0, 2), (0, 31), (0, 2), (0, 3), (0, 2), (0, 5), (0, 2), (0, 7), (0, 2), (0, 3),
    (0, 2), (2, 0), (0, 2), (0, 11)]

/-- Every eligible integer beginning at 1888 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock118 :
    ∀ k : Fin 16,
      5 ≤ 16 * 118 + k.val →
        16 * 118 + k.val < 3000 →
        (16 * 118 + k.val, (nonresidueCoverageData118.getD k.val (0, 0)).1) ∈
            (nonresidueTable17 ++ nonresidueTable18) ∨
          (2 ≤ (nonresidueCoverageData118.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData118.getD k.val (0, 0)).2 < 16 * 118 + k.val ∧
            (nonresidueCoverageData118.getD k.val (0, 0)).2 ∣ 16 * 118 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl :
      nonresidueCoverageCheck 118 (nonresidueTable17 ++ nonresidueTable18)
          nonresidueCoverageData118 =
        true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1888,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock118_checked : smallNonresidueBlockChecked 118 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock118 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData118.getD k.val (0, 0)).1,
        (nonresidueTableChecked_append nonresidueTable17_checked nonresidueTable18_checked)
          (16 * 118 + k.val, (nonresidueCoverageData118.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1904.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData119 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (0, 23), (0, 2), (0, 3), (0, 2), (3, 0), (0, 2), (0, 5),
    (0, 2), (0, 3), (0, 2), (0, 19)]

/-- Every eligible integer beginning at 1904 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock119 :
    ∀ k : Fin 16,
      5 ≤ 16 * 119 + k.val →
        16 * 119 + k.val < 3000 →
        (16 * 119 + k.val, (nonresidueCoverageData119.getD k.val (0, 0)).1) ∈ (nonresidueTable18) ∨
          (2 ≤ (nonresidueCoverageData119.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData119.getD k.val (0, 0)).2 < 16 * 119 + k.val ∧
            (nonresidueCoverageData119.getD k.val (0, 0)).2 ∣ 16 * 119 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 119 (nonresidueTable18) nonresidueCoverageData119 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1904,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock119_checked : smallNonresidueBlockChecked 119 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock119 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData119.getD k.val (0, 0)).1,
        nonresidueTable18_checked
          (16 * 119 + k.val, (nonresidueCoverageData119.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1920.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData120 : List (ℕ × ℕ) :=
  [(0, 2), (0, 17), (0, 2), (0, 3), (0, 2), (0, 5), (0, 2), (0, 41), (0, 2), (0, 3), (0, 2), (2, 0),
    (0, 2), (2, 0), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 1920 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock120 :
    ∀ k : Fin 16,
      5 ≤ 16 * 120 + k.val →
        16 * 120 + k.val < 3000 →
        (16 * 120 + k.val, (nonresidueCoverageData120.getD k.val (0, 0)).1) ∈ (nonresidueTable18) ∨
          (2 ≤ (nonresidueCoverageData120.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData120.getD k.val (0, 0)).2 < 16 * 120 + k.val ∧
            (nonresidueCoverageData120.getD k.val (0, 0)).2 ∣ 16 * 120 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 120 (nonresidueTable18) nonresidueCoverageData120 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1920,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock120_checked : smallNonresidueBlockChecked 120 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock120 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData120.getD k.val (0, 0)).1,
        nonresidueTable18_checked
          (16 * 120 + k.val, (nonresidueCoverageData120.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1936.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData121 : List (ℕ × ℕ) :=
  [(0, 2), (0, 13), (0, 2), (0, 7), (0, 2), (0, 3), (0, 2), (0, 29), (0, 2), (0, 5), (0, 2), (0, 3),
    (0, 2), (2, 0), (0, 2), (3, 0)]

/-- Every eligible integer beginning at 1936 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock121 :
    ∀ k : Fin 16,
      5 ≤ 16 * 121 + k.val →
        16 * 121 + k.val < 3000 →
        (16 * 121 + k.val, (nonresidueCoverageData121.getD k.val (0, 0)).1) ∈ (nonresidueTable18) ∨
          (2 ≤ (nonresidueCoverageData121.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData121.getD k.val (0, 0)).2 < 16 * 121 + k.val ∧
            (nonresidueCoverageData121.getD k.val (0, 0)).2 ∣ 16 * 121 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 121 (nonresidueTable18) nonresidueCoverageData121 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1936,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock121_checked : smallNonresidueBlockChecked 121 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock121 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData121.getD k.val (0, 0)).1,
        nonresidueTable18_checked
          (16 * 121 + k.val, (nonresidueCoverageData121.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1952.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData122 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (0, 5), (0, 2), (0, 19), (0, 2), (0, 3), (0, 2), (0, 37), (0, 2),
    (0, 13), (0, 2), (0, 3), (0, 2), (0, 7)]

/-- Every eligible integer beginning at 1952 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock122 :
    ∀ k : Fin 16,
      5 ≤ 16 * 122 + k.val →
        16 * 122 + k.val < 3000 →
        (16 * 122 + k.val, (nonresidueCoverageData122.getD k.val (0, 0)).1) ∈ (nonresidueTable0) ∨
          (2 ≤ (nonresidueCoverageData122.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData122.getD k.val (0, 0)).2 < 16 * 122 + k.val ∧
            (nonresidueCoverageData122.getD k.val (0, 0)).2 ∣ 16 * 122 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 122 (nonresidueTable0) nonresidueCoverageData122 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1952,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock122_checked : smallNonresidueBlockChecked 122 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock122 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData122.getD k.val (0, 0)).1,
        nonresidueTable0_checked (16 * 122 + k.val, (nonresidueCoverageData122.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1968.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData123 : List (ℕ × ℕ) :=
  [(0, 2), (0, 11), (0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (0, 5), (0, 2), (0, 3), (0, 2), (2, 0),
    (0, 2), (0, 7), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 1968 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock123 :
    ∀ k : Fin 16,
      5 ≤ 16 * 123 + k.val →
        16 * 123 + k.val < 3000 →
        (16 * 123 + k.val, (nonresidueCoverageData123.getD k.val (0, 0)).1) ∈ (nonresidueTable18) ∨
          (2 ≤ (nonresidueCoverageData123.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData123.getD k.val (0, 0)).2 < 16 * 123 + k.val ∧
            (nonresidueCoverageData123.getD k.val (0, 0)).2 ∣ 16 * 123 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 123 (nonresidueTable18) nonresidueCoverageData123 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1968,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock123_checked : smallNonresidueBlockChecked 123 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock123 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData123.getD k.val (0, 0)).1,
        nonresidueTable18_checked
          (16 * 123 + k.val, (nonresidueCoverageData123.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 1984.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData124 : List (ℕ × ℕ) :=
  [(0, 2), (0, 5), (0, 2), (2, 0), (0, 2), (0, 3), (0, 2), (0, 11), (0, 2), (5, 0), (0, 2), (0, 3),
    (0, 2), (2, 0), (0, 2), (3, 0)]

/-- Every eligible integer beginning at 1984 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock124 :
    ∀ k : Fin 16,
      5 ≤ 16 * 124 + k.val →
        16 * 124 + k.val < 3000 →
        (16 * 124 + k.val, (nonresidueCoverageData124.getD k.val (0, 0)).1) ∈ (nonresidueTable18) ∨
          (2 ≤ (nonresidueCoverageData124.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData124.getD k.val (0, 0)).2 < 16 * 124 + k.val ∧
            (nonresidueCoverageData124.getD k.val (0, 0)).2 ∣ 16 * 124 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 124 (nonresidueTable18) nonresidueCoverageData124 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 1984,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock124_checked : smallNonresidueBlockChecked 124 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock124 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData124.getD k.val (0, 0)).1,
        nonresidueTable18_checked
          (16 * 124 + k.val, (nonresidueCoverageData124.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2000.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData125 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (0, 5), (0, 2), (0, 3), (0, 2), (0, 7), (0, 2), (2, 0),
    (0, 2), (0, 3), (0, 2), (0, 5)]

/-- Every eligible integer beginning at 2000 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock125 :
    ∀ k : Fin 16,
      5 ≤ 16 * 125 + k.val →
        16 * 125 + k.val < 3000 →
        (16 * 125 + k.val, (nonresidueCoverageData125.getD k.val (0, 0)).1) ∈ (nonresidueTable18) ∨
          (2 ≤ (nonresidueCoverageData125.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData125.getD k.val (0, 0)).2 < 16 * 125 + k.val ∧
            (nonresidueCoverageData125.getD k.val (0, 0)).2 ∣ 16 * 125 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 125 (nonresidueTable18) nonresidueCoverageData125 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2000,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock125_checked : smallNonresidueBlockChecked 125 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock125 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData125.getD k.val (0, 0)).1,
        nonresidueTable18_checked
          (16 * 125 + k.val, (nonresidueCoverageData125.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2016.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData126 : List (ℕ × ℕ) :=
  [(0, 2), (5, 0), (0, 2), (0, 3), (0, 2), (0, 43), (0, 2), (0, 7), (0, 2), (0, 3), (0, 2), (2, 0),
    (0, 2), (2, 0), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 2016 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock126 :
    ∀ k : Fin 16,
      5 ≤ 16 * 126 + k.val →
        16 * 126 + k.val < 3000 →
        (16 * 126 + k.val, (nonresidueCoverageData126.getD k.val (0, 0)).1) ∈
            (nonresidueTable18 ++ nonresidueTable19) ∨
          (2 ≤ (nonresidueCoverageData126.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData126.getD k.val (0, 0)).2 < 16 * 126 + k.val ∧
            (nonresidueCoverageData126.getD k.val (0, 0)).2 ∣ 16 * 126 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl :
      nonresidueCoverageCheck 126 (nonresidueTable18 ++ nonresidueTable19)
          nonresidueCoverageData126 =
        true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2016,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock126_checked : smallNonresidueBlockChecked 126 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock126 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData126.getD k.val (0, 0)).1,
        (nonresidueTableChecked_append nonresidueTable18_checked nonresidueTable19_checked)
          (16 * 126 + k.val, (nonresidueCoverageData126.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2032.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData127 : List (ℕ × ℕ) :=
  [(0, 2), (0, 19), (0, 2), (0, 5), (0, 2), (0, 3), (0, 2), (7, 0), (0, 2), (0, 13), (0, 2), (0, 3),
    (0, 2), (0, 5), (0, 2), (0, 23)]

/-- Every eligible integer beginning at 2032 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock127 :
    ∀ k : Fin 16,
      5 ≤ 16 * 127 + k.val →
        16 * 127 + k.val < 3000 →
        (16 * 127 + k.val, (nonresidueCoverageData127.getD k.val (0, 0)).1) ∈ (nonresidueTable19) ∨
          (2 ≤ (nonresidueCoverageData127.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData127.getD k.val (0, 0)).2 < 16 * 127 + k.val ∧
            (nonresidueCoverageData127.getD k.val (0, 0)).2 ∣ 16 * 127 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 127 (nonresidueTable19) nonresidueCoverageData127 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2032,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock127_checked : smallNonresidueBlockChecked 127 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock127 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData127.getD k.val (0, 0)).1,
        nonresidueTable19_checked
          (16 * 127 + k.val, (nonresidueCoverageData127.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2048.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData128 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (0, 7), (0, 2), (2, 0), (0, 2), (0, 3), (0, 2), (0, 11), (0, 2), (0, 29),
    (0, 2), (0, 3), (0, 2), (5, 0)]

/-- Every eligible integer beginning at 2048 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock128 :
    ∀ k : Fin 16,
      5 ≤ 16 * 128 + k.val →
        16 * 128 + k.val < 3000 →
        (16 * 128 + k.val, (nonresidueCoverageData128.getD k.val (0, 0)).1) ∈ (nonresidueTable19) ∨
          (2 ≤ (nonresidueCoverageData128.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData128.getD k.val (0, 0)).2 < 16 * 128 + k.val ∧
            (nonresidueCoverageData128.getD k.val (0, 0)).2 ∣ 16 * 128 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 128 (nonresidueTable19) nonresidueCoverageData128 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2048,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock128_checked : smallNonresidueBlockChecked 128 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock128 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData128.getD k.val (0, 0)).1,
        nonresidueTable19_checked
          (16 * 128 + k.val, (nonresidueCoverageData128.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2064.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData129 : List (ℕ × ℕ) :=
  [(0, 2), (0, 5), (0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (0, 19), (0, 2), (0, 3), (0, 2), (0, 5),
    (0, 2), (0, 31), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 2064 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock129 :
    ∀ k : Fin 16,
      5 ≤ 16 * 129 + k.val →
        16 * 129 + k.val < 3000 →
        (16 * 129 + k.val, (nonresidueCoverageData129.getD k.val (0, 0)).1) ∈ (nonresidueTable19) ∨
          (2 ≤ (nonresidueCoverageData129.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData129.getD k.val (0, 0)).2 < 16 * 129 + k.val ∧
            (nonresidueCoverageData129.getD k.val (0, 0)).2 ∣ 16 * 129 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 129 (nonresidueTable19) nonresidueCoverageData129 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2064,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock129_checked : smallNonresidueBlockChecked 129 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock129 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData129.getD k.val (0, 0)).1,
        nonresidueTable19_checked
          (16 * 129 + k.val, (nonresidueCoverageData129.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2080.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData130 : List (ℕ × ℕ) :=
  [(0, 2), (3, 0), (0, 2), (2, 0), (0, 2), (0, 3), (0, 2), (5, 0), (0, 2), (7, 0), (0, 2), (0, 3),
    (0, 2), (0, 7), (0, 2), (0, 5)]

/-- Every eligible integer beginning at 2080 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock130 :
    ∀ k : Fin 16,
      5 ≤ 16 * 130 + k.val →
        16 * 130 + k.val < 3000 →
        (16 * 130 + k.val, (nonresidueCoverageData130.getD k.val (0, 0)).1) ∈ (nonresidueTable19) ∨
          (2 ≤ (nonresidueCoverageData130.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData130.getD k.val (0, 0)).2 < 16 * 130 + k.val ∧
            (nonresidueCoverageData130.getD k.val (0, 0)).2 ∣ 16 * 130 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 130 (nonresidueTable19) nonresidueCoverageData130 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2080,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock130_checked : smallNonresidueBlockChecked 130 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock130 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData130.getD k.val (0, 0)).1,
        nonresidueTable19_checked
          (16 * 130 + k.val, (nonresidueCoverageData130.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2096.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData131 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (0, 11), (0, 2), (0, 3), (0, 2), (0, 5), (0, 2), (0, 7),
    (0, 2), (0, 3), (0, 2), (7, 0)]

/-- Every eligible integer beginning at 2096 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock131 :
    ∀ k : Fin 16,
      5 ≤ 16 * 131 + k.val →
        16 * 131 + k.val < 3000 →
        (16 * 131 + k.val, (nonresidueCoverageData131.getD k.val (0, 0)).1) ∈ (nonresidueTable19) ∨
          (2 ≤ (nonresidueCoverageData131.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData131.getD k.val (0, 0)).2 < 16 * 131 + k.val ∧
            (nonresidueCoverageData131.getD k.val (0, 0)).2 ∣ 16 * 131 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 131 (nonresidueTable19) nonresidueCoverageData131 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2096,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock131_checked : smallNonresidueBlockChecked 131 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock131 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData131.getD k.val (0, 0)).1,
        nonresidueTable19_checked
          (16 * 131 + k.val, (nonresidueCoverageData131.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2112.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData132 : List (ℕ × ℕ) :=
  [(0, 2), (5, 0), (0, 2), (0, 3), (0, 2), (0, 29), (0, 2), (0, 13), (0, 2), (0, 3), (0, 2),
    (0, 11), (0, 2), (0, 5), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 2112 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock132 :
    ∀ k : Fin 16,
      5 ≤ 16 * 132 + k.val →
        16 * 132 + k.val < 3000 →
        (16 * 132 + k.val, (nonresidueCoverageData132.getD k.val (0, 0)).1) ∈ (nonresidueTable19) ∨
          (2 ≤ (nonresidueCoverageData132.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData132.getD k.val (0, 0)).2 < 16 * 132 + k.val ∧
            (nonresidueCoverageData132.getD k.val (0, 0)).2 ∣ 16 * 132 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 132 (nonresidueTable19) nonresidueCoverageData132 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2112,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock132_checked : smallNonresidueBlockChecked 132 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock132 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData132.getD k.val (0, 0)).1,
        nonresidueTable19_checked
          (16 * 132 + k.val, (nonresidueCoverageData132.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2128.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData133 : List (ℕ × ℕ) :=
  [(0, 2), (3, 0), (0, 2), (2, 0), (0, 2), (0, 3), (0, 2), (0, 5), (0, 2), (5, 0), (0, 2), (0, 3),
    (0, 2), (2, 0), (0, 2), (3, 0)]

/-- Every eligible integer beginning at 2128 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock133 :
    ∀ k : Fin 16,
      5 ≤ 16 * 133 + k.val →
        16 * 133 + k.val < 3000 →
        (16 * 133 + k.val, (nonresidueCoverageData133.getD k.val (0, 0)).1) ∈
            (nonresidueTable19 ++ nonresidueTable20) ∨
          (2 ≤ (nonresidueCoverageData133.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData133.getD k.val (0, 0)).2 < 16 * 133 + k.val ∧
            (nonresidueCoverageData133.getD k.val (0, 0)).2 ∣ 16 * 133 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl :
      nonresidueCoverageCheck 133 (nonresidueTable19 ++ nonresidueTable20)
          nonresidueCoverageData133 =
        true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2128,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock133_checked : smallNonresidueBlockChecked 133 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock133 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData133.getD k.val (0, 0)).1,
        (nonresidueTableChecked_append nonresidueTable19_checked nonresidueTable20_checked)
          (16 * 133 + k.val, (nonresidueCoverageData133.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2144.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData134 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (0, 19), (0, 2), (0, 7), (0, 2), (0, 3), (0, 2), (3, 0), (0, 2), (0, 5),
    (0, 2), (0, 3), (0, 2), (0, 17)]

/-- Every eligible integer beginning at 2144 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock134 :
    ∀ k : Fin 16,
      5 ≤ 16 * 134 + k.val →
        16 * 134 + k.val < 3000 →
        (16 * 134 + k.val, (nonresidueCoverageData134.getD k.val (0, 0)).1) ∈ (nonresidueTable20) ∨
          (2 ≤ (nonresidueCoverageData134.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData134.getD k.val (0, 0)).2 < 16 * 134 + k.val ∧
            (nonresidueCoverageData134.getD k.val (0, 0)).2 ∣ 16 * 134 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 134 (nonresidueTable20) nonresidueCoverageData134 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2144,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock134_checked : smallNonresidueBlockChecked 134 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock134 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData134.getD k.val (0, 0)).1,
        nonresidueTable20_checked
          (16 * 134 + k.val, (nonresidueCoverageData134.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2160.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData135 : List (ℕ × ℕ) :=
  [(0, 2), (7, 0), (0, 2), (0, 3), (0, 2), (0, 5), (0, 2), (0, 11), (0, 2), (0, 3), (0, 2), (0, 13),
    (0, 2), (0, 41), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 2160 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock135 :
    ∀ k : Fin 16,
      5 ≤ 16 * 135 + k.val →
        16 * 135 + k.val < 3000 →
        (16 * 135 + k.val, (nonresidueCoverageData135.getD k.val (0, 0)).1) ∈ (nonresidueTable20) ∨
          (2 ≤ (nonresidueCoverageData135.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData135.getD k.val (0, 0)).2 < 16 * 135 + k.val ∧
            (nonresidueCoverageData135.getD k.val (0, 0)).2 ∣ 16 * 135 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 135 (nonresidueTable20) nonresidueCoverageData135 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2160,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock135_checked : smallNonresidueBlockChecked 135 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock135 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData135.getD k.val (0, 0)).1,
        nonresidueTable20_checked
          (16 * 135 + k.val, (nonresidueCoverageData135.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2176.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData136 : List (ℕ × ℕ) :=
  [(0, 2), (0, 7), (0, 2), (2, 0), (0, 2), (0, 3), (0, 2), (0, 37), (0, 2), (0, 5), (0, 2), (0, 3),
    (0, 2), (0, 11), (0, 2), (0, 7)]

/-- Every eligible integer beginning at 2176 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock136 :
    ∀ k : Fin 16,
      5 ≤ 16 * 136 + k.val →
        16 * 136 + k.val < 3000 →
        (16 * 136 + k.val, (nonresidueCoverageData136.getD k.val (0, 0)).1) ∈ (nonresidueTable20) ∨
          (2 ≤ (nonresidueCoverageData136.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData136.getD k.val (0, 0)).2 < 16 * 136 + k.val ∧
            (nonresidueCoverageData136.getD k.val (0, 0)).2 ∣ 16 * 136 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 136 (nonresidueTable20) nonresidueCoverageData136 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2176,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock136_checked : smallNonresidueBlockChecked 136 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock136 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData136.getD k.val (0, 0)).1,
        nonresidueTable20_checked
          (16 * 136 + k.val, (nonresidueCoverageData136.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2192.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData137 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (0, 5), (0, 2), (0, 13), (0, 2), (0, 3), (0, 2), (0, 31), (0, 2), (2, 0),
    (0, 2), (0, 3), (0, 2), (5, 0)]

/-- Every eligible integer beginning at 2192 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock137 :
    ∀ k : Fin 16,
      5 ≤ 16 * 137 + k.val →
        16 * 137 + k.val < 3000 →
        (16 * 137 + k.val, (nonresidueCoverageData137.getD k.val (0, 0)).1) ∈ (nonresidueTable20) ∨
          (2 ≤ (nonresidueCoverageData137.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData137.getD k.val (0, 0)).2 < 16 * 137 + k.val ∧
            (nonresidueCoverageData137.getD k.val (0, 0)).2 ∣ 16 * 137 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 137 (nonresidueTable20) nonresidueCoverageData137 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2192,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock137_checked : smallNonresidueBlockChecked 137 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock137 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData137.getD k.val (0, 0)).1,
        nonresidueTable20_checked
          (16 * 137 + k.val, (nonresidueCoverageData137.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2208.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData138 : List (ℕ × ℕ) :=
  [(0, 2), (0, 47), (0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (0, 5), (0, 2), (0, 3), (0, 2), (0, 7),
    (0, 2), (2, 0), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 2208 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock138 :
    ∀ k : Fin 16,
      5 ≤ 16 * 138 + k.val →
        16 * 138 + k.val < 3000 →
        (16 * 138 + k.val, (nonresidueCoverageData138.getD k.val (0, 0)).1) ∈ (nonresidueTable20) ∨
          (2 ≤ (nonresidueCoverageData138.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData138.getD k.val (0, 0)).2 < 16 * 138 + k.val ∧
            (nonresidueCoverageData138.getD k.val (0, 0)).2 ∣ 16 * 138 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 138 (nonresidueTable20) nonresidueCoverageData138 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2208,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock138_checked : smallNonresidueBlockChecked 138 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock138 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData138.getD k.val (0, 0)).1,
        nonresidueTable20_checked
          (16 * 138 + k.val, (nonresidueCoverageData138.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2224.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData139 : List (ℕ × ℕ) :=
  [(0, 2), (0, 5), (0, 2), (0, 17), (0, 2), (0, 3), (0, 2), (0, 23), (0, 2), (0, 7), (0, 2), (0, 3),
    (0, 2), (2, 0), (0, 2), (3, 0)]

/-- Every eligible integer beginning at 2224 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock139 :
    ∀ k : Fin 16,
      5 ≤ 16 * 139 + k.val →
        16 * 139 + k.val < 3000 →
        (16 * 139 + k.val, (nonresidueCoverageData139.getD k.val (0, 0)).1) ∈ (nonresidueTable20) ∨
          (2 ≤ (nonresidueCoverageData139.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData139.getD k.val (0, 0)).2 < 16 * 139 + k.val ∧
            (nonresidueCoverageData139.getD k.val (0, 0)).2 ∣ 16 * 139 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 139 (nonresidueTable20) nonresidueCoverageData139 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2224,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock139_checked : smallNonresidueBlockChecked 139 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock139 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData139.getD k.val (0, 0)).1,
        nonresidueTable20_checked
          (16 * 139 + k.val, (nonresidueCoverageData139.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2240.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData140 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (0, 5), (0, 2), (0, 3), (0, 2), (0, 13), (0, 2), (2, 0),
    (0, 2), (0, 3), (0, 2), (0, 5)]

/-- Every eligible integer beginning at 2240 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock140 :
    ∀ k : Fin 16,
      5 ≤ 16 * 140 + k.val →
        16 * 140 + k.val < 3000 →
        (16 * 140 + k.val, (nonresidueCoverageData140.getD k.val (0, 0)).1) ∈ (nonresidueTable20) ∨
          (2 ≤ (nonresidueCoverageData140.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData140.getD k.val (0, 0)).2 < 16 * 140 + k.val ∧
            (nonresidueCoverageData140.getD k.val (0, 0)).2 ∣ 16 * 140 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 140 (nonresidueTable20) nonresidueCoverageData140 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2240,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock140_checked : smallNonresidueBlockChecked 140 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock140 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData140.getD k.val (0, 0)).1,
        nonresidueTable20_checked
          (16 * 140 + k.val, (nonresidueCoverageData140.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2256.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData141 : List (ℕ × ℕ) :=
  [(0, 2), (0, 37), (0, 2), (0, 3), (0, 2), (0, 7), (0, 2), (0, 31), (0, 2), (0, 3), (0, 2), (2, 0),
    (0, 2), (2, 0), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 2256 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock141 :
    ∀ k : Fin 16,
      5 ≤ 16 * 141 + k.val →
        16 * 141 + k.val < 3000 →
        (16 * 141 + k.val, (nonresidueCoverageData141.getD k.val (0, 0)).1) ∈ (nonresidueTable20) ∨
          (2 ≤ (nonresidueCoverageData141.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData141.getD k.val (0, 0)).2 < 16 * 141 + k.val ∧
            (nonresidueCoverageData141.getD k.val (0, 0)).2 ∣ 16 * 141 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 141 (nonresidueTable20) nonresidueCoverageData141 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2256,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock141_checked : smallNonresidueBlockChecked 141 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock141 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData141.getD k.val (0, 0)).1,
        nonresidueTable20_checked
          (16 * 141 + k.val, (nonresidueCoverageData141.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2272.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData142 : List (ℕ × ℕ) :=
  [(0, 2), (3, 0), (0, 2), (0, 5), (0, 2), (0, 3), (0, 2), (0, 43), (0, 2), (7, 0), (0, 2), (0, 3),
    (0, 2), (0, 5), (0, 2), (3, 0)]

/-- Every eligible integer beginning at 2272 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock142 :
    ∀ k : Fin 16,
      5 ≤ 16 * 142 + k.val →
        16 * 142 + k.val < 3000 →
        (16 * 142 + k.val, (nonresidueCoverageData142.getD k.val (0, 0)).1) ∈
            (nonresidueTable20 ++ nonresidueTable21) ∨
          (2 ≤ (nonresidueCoverageData142.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData142.getD k.val (0, 0)).2 < 16 * 142 + k.val ∧
            (nonresidueCoverageData142.getD k.val (0, 0)).2 ∣ 16 * 142 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl :
      nonresidueCoverageCheck 142 (nonresidueTable20 ++ nonresidueTable21)
          nonresidueCoverageData142 =
        true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2272,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock142_checked : smallNonresidueBlockChecked 142 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock142 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData142.getD k.val (0, 0)).1,
        (nonresidueTableChecked_append nonresidueTable20_checked nonresidueTable21_checked)
          (16 * 142 + k.val, (nonresidueCoverageData142.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2288.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData143 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (0, 29), (0, 2), (2, 0), (0, 2), (0, 3), (0, 2), (3, 0), (0, 2), (0, 11),
    (0, 2), (0, 3), (0, 2), (0, 7)]

/-- Every eligible integer beginning at 2288 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock143 :
    ∀ k : Fin 16,
      5 ≤ 16 * 143 + k.val →
        16 * 143 + k.val < 3000 →
        (16 * 143 + k.val, (nonresidueCoverageData143.getD k.val (0, 0)).1) ∈ (nonresidueTable21) ∨
          (2 ≤ (nonresidueCoverageData143.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData143.getD k.val (0, 0)).2 < 16 * 143 + k.val ∧
            (nonresidueCoverageData143.getD k.val (0, 0)).2 ∣ 16 * 143 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 143 (nonresidueTable21) nonresidueCoverageData143 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2288,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock143_checked : smallNonresidueBlockChecked 143 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock143 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData143.getD k.val (0, 0)).1,
        nonresidueTable21_checked
          (16 * 143 + k.val, (nonresidueCoverageData143.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2304.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData144 : List (ℕ × ℕ) :=
  [(0, 2), (0, 5), (0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (3, 0), (0, 2), (0, 3), (0, 2), (0, 5),
    (0, 2), (0, 7), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 2304 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock144 :
    ∀ k : Fin 16,
      5 ≤ 16 * 144 + k.val →
        16 * 144 + k.val < 3000 →
        (16 * 144 + k.val, (nonresidueCoverageData144.getD k.val (0, 0)).1) ∈ (nonresidueTable21) ∨
          (2 ≤ (nonresidueCoverageData144.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData144.getD k.val (0, 0)).2 < 16 * 144 + k.val ∧
            (nonresidueCoverageData144.getD k.val (0, 0)).2 ∣ 16 * 144 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 144 (nonresidueTable21) nonresidueCoverageData144 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2304,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock144_checked : smallNonresidueBlockChecked 144 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock144 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData144.getD k.val (0, 0)).1,
        nonresidueTable21_checked
          (16 * 144 + k.val, (nonresidueCoverageData144.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2320.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData145 : List (ℕ × ℕ) :=
  [(0, 2), (0, 11), (0, 2), (0, 23), (0, 2), (0, 3), (0, 2), (0, 13), (0, 2), (0, 17), (0, 2),
    (0, 3), (0, 2), (2, 0), (0, 2), (0, 5)]

/-- Every eligible integer beginning at 2320 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock145 :
    ∀ k : Fin 16,
      5 ≤ 16 * 145 + k.val →
        16 * 145 + k.val < 3000 →
        (16 * 145 + k.val, (nonresidueCoverageData145.getD k.val (0, 0)).1) ∈ (nonresidueTable21) ∨
          (2 ≤ (nonresidueCoverageData145.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData145.getD k.val (0, 0)).2 < 16 * 145 + k.val ∧
            (nonresidueCoverageData145.getD k.val (0, 0)).2 ∣ 16 * 145 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 145 (nonresidueTable21) nonresidueCoverageData145 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2320,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock145_checked : smallNonresidueBlockChecked 145 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock145 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData145.getD k.val (0, 0)).1,
        nonresidueTable21_checked
          (16 * 145 + k.val, (nonresidueCoverageData145.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2336.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData146 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (2, 0), (0, 2), (0, 3), (0, 2), (0, 5), (0, 2), (2, 0),
    (0, 2), (0, 3), (0, 2), (13, 0)]

/-- Every eligible integer beginning at 2336 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock146 :
    ∀ k : Fin 16,
      5 ≤ 16 * 146 + k.val →
        16 * 146 + k.val < 3000 →
        (16 * 146 + k.val, (nonresidueCoverageData146.getD k.val (0, 0)).1) ∈ (nonresidueTable21) ∨
          (2 ≤ (nonresidueCoverageData146.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData146.getD k.val (0, 0)).2 < 16 * 146 + k.val ∧
            (nonresidueCoverageData146.getD k.val (0, 0)).2 ∣ 16 * 146 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 146 (nonresidueTable21) nonresidueCoverageData146 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2336,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock146_checked : smallNonresidueBlockChecked 146 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock146 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData146.getD k.val (0, 0)).1,
        nonresidueTable21_checked
          (16 * 146 + k.val, (nonresidueCoverageData146.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2352.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData147 : List (ℕ × ℕ) :=
  [(0, 2), (0, 13), (0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (0, 7), (0, 2), (0, 3), (0, 2), (0, 17),
    (0, 2), (0, 5), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 2352 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock147 :
    ∀ k : Fin 16,
      5 ≤ 16 * 147 + k.val →
        16 * 147 + k.val < 3000 →
        (16 * 147 + k.val, (nonresidueCoverageData147.getD k.val (0, 0)).1) ∈ (nonresidueTable21) ∨
          (2 ≤ (nonresidueCoverageData147.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData147.getD k.val (0, 0)).2 < 16 * 147 + k.val ∧
            (nonresidueCoverageData147.getD k.val (0, 0)).2 ∣ 16 * 147 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 147 (nonresidueTable21) nonresidueCoverageData147 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2352,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock147_checked : smallNonresidueBlockChecked 147 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock147 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData147.getD k.val (0, 0)).1,
        nonresidueTable21_checked
          (16 * 147 + k.val, (nonresidueCoverageData147.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2368.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData148 : List (ℕ × ℕ) :=
  [(0, 2), (0, 23), (0, 2), (2, 0), (0, 2), (0, 3), (0, 2), (0, 5), (0, 2), (5, 0), (0, 2), (0, 3),
    (0, 2), (2, 0), (0, 2), (3, 0)]

/-- Every eligible integer beginning at 2368 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock148 :
    ∀ k : Fin 16,
      5 ≤ 16 * 148 + k.val →
        16 * 148 + k.val < 3000 →
        (16 * 148 + k.val, (nonresidueCoverageData148.getD k.val (0, 0)).1) ∈ (nonresidueTable21) ∨
          (2 ≤ (nonresidueCoverageData148.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData148.getD k.val (0, 0)).2 < 16 * 148 + k.val ∧
            (nonresidueCoverageData148.getD k.val (0, 0)).2 ∣ 16 * 148 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 148 (nonresidueTable21) nonresidueCoverageData148 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2368,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock148_checked : smallNonresidueBlockChecked 148 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock148 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData148.getD k.val (0, 0)).1,
        nonresidueTable21_checked
          (16 * 148 + k.val, (nonresidueCoverageData148.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2384.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData149 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (0, 7), (0, 2), (2, 0), (0, 2), (0, 3), (0, 2), (3, 0), (0, 2), (0, 5),
    (0, 2), (0, 3), (0, 2), (11, 0)]

/-- Every eligible integer beginning at 2384 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock149 :
    ∀ k : Fin 16,
      5 ≤ 16 * 149 + k.val →
        16 * 149 + k.val < 3000 →
        (16 * 149 + k.val, (nonresidueCoverageData149.getD k.val (0, 0)).1) ∈ (nonresidueTable22) ∨
          (2 ≤ (nonresidueCoverageData149.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData149.getD k.val (0, 0)).2 < 16 * 149 + k.val ∧
            (nonresidueCoverageData149.getD k.val (0, 0)).2 ∣ 16 * 149 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 149 (nonresidueTable22) nonresidueCoverageData149 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2384,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock149_checked : smallNonresidueBlockChecked 149 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock149 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData149.getD k.val (0, 0)).1,
        nonresidueTable22_checked
          (16 * 149 + k.val, (nonresidueCoverageData149.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2400.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData150 : List (ℕ × ℕ) :=
  [(0, 2), (0, 7), (0, 2), (0, 3), (0, 2), (0, 5), (0, 2), (0, 29), (0, 2), (0, 3), (0, 2), (2, 0),
    (0, 2), (0, 19), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 2400 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock150 :
    ∀ k : Fin 16,
      5 ≤ 16 * 150 + k.val →
        16 * 150 + k.val < 3000 →
        (16 * 150 + k.val, (nonresidueCoverageData150.getD k.val (0, 0)).1) ∈ (nonresidueTable22) ∨
          (2 ≤ (nonresidueCoverageData150.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData150.getD k.val (0, 0)).2 < 16 * 150 + k.val ∧
            (nonresidueCoverageData150.getD k.val (0, 0)).2 ∣ 16 * 150 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 150 (nonresidueTable22) nonresidueCoverageData150 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2400,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock150_checked : smallNonresidueBlockChecked 150 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock150 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData150.getD k.val (0, 0)).1,
        nonresidueTable22_checked
          (16 * 150 + k.val, (nonresidueCoverageData150.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2416.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData151 : List (ℕ × ℕ) :=
  [(0, 2), (3, 0), (0, 2), (0, 41), (0, 2), (0, 3), (0, 2), (5, 0), (0, 2), (0, 5), (0, 2), (0, 3),
    (0, 2), (0, 7), (0, 2), (0, 11)]

/-- Every eligible integer beginning at 2416 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock151 :
    ∀ k : Fin 16,
      5 ≤ 16 * 151 + k.val →
        16 * 151 + k.val < 3000 →
        (16 * 151 + k.val, (nonresidueCoverageData151.getD k.val (0, 0)).1) ∈ (nonresidueTable22) ∨
          (2 ≤ (nonresidueCoverageData151.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData151.getD k.val (0, 0)).2 < 16 * 151 + k.val ∧
            (nonresidueCoverageData151.getD k.val (0, 0)).2 ∣ 16 * 151 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 151 (nonresidueTable22) nonresidueCoverageData151 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2416,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock151_checked : smallNonresidueBlockChecked 151 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock151 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData151.getD k.val (0, 0)).1,
        nonresidueTable22_checked
          (16 * 151 + k.val, (nonresidueCoverageData151.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2432.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData152 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (0, 5), (0, 2), (2, 0), (0, 2), (0, 3), (0, 2), (3, 0), (0, 2), (0, 7),
    (0, 2), (0, 3), (0, 2), (5, 0)]

/-- Every eligible integer beginning at 2432 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock152 :
    ∀ k : Fin 16,
      5 ≤ 16 * 152 + k.val →
        16 * 152 + k.val < 3000 →
        (16 * 152 + k.val, (nonresidueCoverageData152.getD k.val (0, 0)).1) ∈ (nonresidueTable22) ∨
          (2 ≤ (nonresidueCoverageData152.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData152.getD k.val (0, 0)).2 < 16 * 152 + k.val ∧
            (nonresidueCoverageData152.getD k.val (0, 0)).2 ∣ 16 * 152 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 152 (nonresidueTable22) nonresidueCoverageData152 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2432,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock152_checked : smallNonresidueBlockChecked 152 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock152 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData152.getD k.val (0, 0)).1,
        nonresidueTable22_checked
          (16 * 152 + k.val, (nonresidueCoverageData152.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2448.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData153 : List (ℕ × ℕ) :=
  [(0, 2), (0, 31), (0, 2), (0, 3), (0, 2), (0, 11), (0, 2), (0, 5), (0, 2), (0, 3), (0, 2), (2, 0),
    (0, 2), (0, 23), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 2448 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock153 :
    ∀ k : Fin 16,
      5 ≤ 16 * 153 + k.val →
        16 * 153 + k.val < 3000 →
        (16 * 153 + k.val, (nonresidueCoverageData153.getD k.val (0, 0)).1) ∈ (nonresidueTable22) ∨
          (2 ≤ (nonresidueCoverageData153.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData153.getD k.val (0, 0)).2 < 16 * 153 + k.val ∧
            (nonresidueCoverageData153.getD k.val (0, 0)).2 ∣ 16 * 153 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 153 (nonresidueTable22) nonresidueCoverageData153 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2448,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock153_checked : smallNonresidueBlockChecked 153 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock153 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData153.getD k.val (0, 0)).1,
        nonresidueTable22_checked
          (16 * 153 + k.val, (nonresidueCoverageData153.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2464.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData154 : List (ℕ × ℕ) :=
  [(0, 2), (0, 5), (0, 2), (2, 0), (0, 2), (0, 3), (0, 2), (0, 7), (0, 2), (5, 0), (0, 2), (0, 3),
    (0, 2), (2, 0), (0, 2), (0, 37)]

/-- Every eligible integer beginning at 2464 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock154 :
    ∀ k : Fin 16,
      5 ≤ 16 * 154 + k.val →
        16 * 154 + k.val < 3000 →
        (16 * 154 + k.val, (nonresidueCoverageData154.getD k.val (0, 0)).1) ∈ (nonresidueTable22) ∨
          (2 ≤ (nonresidueCoverageData154.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData154.getD k.val (0, 0)).2 < 16 * 154 + k.val ∧
            (nonresidueCoverageData154.getD k.val (0, 0)).2 ∣ 16 * 154 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 154 (nonresidueTable22) nonresidueCoverageData154 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2464,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock154_checked : smallNonresidueBlockChecked 154 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock154 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData154.getD k.val (0, 0)).1,
        nonresidueTable22_checked
          (16 * 154 + k.val, (nonresidueCoverageData154.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2480.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData155 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (0, 13), (0, 2), (0, 5), (0, 2), (0, 3), (0, 2), (0, 19), (0, 2),
    (0, 47), (0, 2), (0, 3), (0, 2), (0, 5)]

/-- Every eligible integer beginning at 2480 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock155 :
    ∀ k : Fin 16,
      5 ≤ 16 * 155 + k.val →
        16 * 155 + k.val < 3000 →
        (16 * 155 + k.val, (nonresidueCoverageData155.getD k.val (0, 0)).1) ∈ (nonresidueTable0) ∨
          (2 ≤ (nonresidueCoverageData155.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData155.getD k.val (0, 0)).2 < 16 * 155 + k.val ∧
            (nonresidueCoverageData155.getD k.val (0, 0)).2 ∣ 16 * 155 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 155 (nonresidueTable0) nonresidueCoverageData155 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2480,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock155_checked : smallNonresidueBlockChecked 155 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock155 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData155.getD k.val (0, 0)).1,
        nonresidueTable0_checked (16 * 155 + k.val, (nonresidueCoverageData155.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2496.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData156 : List (ℕ × ℕ) :=
  [(0, 2), (0, 11), (0, 2), (0, 3), (0, 2), (0, 41), (0, 2), (3, 0), (0, 2), (0, 3), (0, 2),
    (0, 23), (0, 2), (0, 13), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 2496 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock156 :
    ∀ k : Fin 16,
      5 ≤ 16 * 156 + k.val →
        16 * 156 + k.val < 3000 →
        (16 * 156 + k.val, (nonresidueCoverageData156.getD k.val (0, 0)).1) ∈ (nonresidueTable22) ∨
          (2 ≤ (nonresidueCoverageData156.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData156.getD k.val (0, 0)).2 < 16 * 156 + k.val ∧
            (nonresidueCoverageData156.getD k.val (0, 0)).2 ∣ 16 * 156 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 156 (nonresidueTable22) nonresidueCoverageData156 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2496,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock156_checked : smallNonresidueBlockChecked 156 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock156 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData156.getD k.val (0, 0)).1,
        nonresidueTable22_checked
          (16 * 156 + k.val, (nonresidueCoverageData156.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2512.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData157 : List (ℕ × ℕ) :=
  [(0, 2), (0, 7), (0, 2), (0, 5), (0, 2), (0, 3), (0, 2), (0, 11), (0, 2), (11, 0), (0, 2), (0, 3),
    (0, 2), (0, 5), (0, 2), (0, 7)]

/-- Every eligible integer beginning at 2512 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock157 :
    ∀ k : Fin 16,
      5 ≤ 16 * 157 + k.val →
        16 * 157 + k.val < 3000 →
        (16 * 157 + k.val, (nonresidueCoverageData157.getD k.val (0, 0)).1) ∈ (nonresidueTable22) ∨
          (2 ≤ (nonresidueCoverageData157.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData157.getD k.val (0, 0)).2 < 16 * 157 + k.val ∧
            (nonresidueCoverageData157.getD k.val (0, 0)).2 ∣ 16 * 157 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 157 (nonresidueTable22) nonresidueCoverageData157 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2512,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock157_checked : smallNonresidueBlockChecked 157 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock157 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData157.getD k.val (0, 0)).1,
        nonresidueTable22_checked
          (16 * 157 + k.val, (nonresidueCoverageData157.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2528.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData158 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (0, 17), (0, 2), (0, 3), (0, 2), (0, 43), (0, 2), (2, 0),
    (0, 2), (0, 3), (0, 2), (5, 0)]

/-- Every eligible integer beginning at 2528 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock158 :
    ∀ k : Fin 16,
      5 ≤ 16 * 158 + k.val →
        16 * 158 + k.val < 3000 →
        (16 * 158 + k.val, (nonresidueCoverageData158.getD k.val (0, 0)).1) ∈
            (nonresidueTable22 ++ nonresidueTable23) ∨
          (2 ≤ (nonresidueCoverageData158.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData158.getD k.val (0, 0)).2 < 16 * 158 + k.val ∧
            (nonresidueCoverageData158.getD k.val (0, 0)).2 ∣ 16 * 158 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl :
      nonresidueCoverageCheck 158 (nonresidueTable22 ++ nonresidueTable23)
          nonresidueCoverageData158 =
        true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2528,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock158_checked : smallNonresidueBlockChecked 158 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock158 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData158.getD k.val (0, 0)).1,
        (nonresidueTableChecked_append nonresidueTable22_checked nonresidueTable23_checked)
          (16 * 158 + k.val, (nonresidueCoverageData158.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2544.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData159 : List (ℕ × ℕ) :=
  [(0, 2), (0, 5), (0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (3, 0), (0, 2), (0, 3), (0, 2), (0, 5),
    (0, 2), (2, 0), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 2544 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock159 :
    ∀ k : Fin 16,
      5 ≤ 16 * 159 + k.val →
        16 * 159 + k.val < 3000 →
        (16 * 159 + k.val, (nonresidueCoverageData159.getD k.val (0, 0)).1) ∈ (nonresidueTable23) ∨
          (2 ≤ (nonresidueCoverageData159.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData159.getD k.val (0, 0)).2 < 16 * 159 + k.val ∧
            (nonresidueCoverageData159.getD k.val (0, 0)).2 ∣ 16 * 159 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 159 (nonresidueTable23) nonresidueCoverageData159 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2544,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock159_checked : smallNonresidueBlockChecked 159 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock159 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData159.getD k.val (0, 0)).1,
        nonresidueTable23_checked
          (16 * 159 + k.val, (nonresidueCoverageData159.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2560.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData160 : List (ℕ × ℕ) :=
  [(0, 2), (0, 13), (0, 2), (0, 11), (0, 2), (0, 3), (0, 2), (0, 17), (0, 2), (0, 7), (0, 2),
    (0, 3), (0, 2), (0, 31), (0, 2), (0, 5)]

/-- Every eligible integer beginning at 2560 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock160 :
    ∀ k : Fin 16,
      5 ≤ 16 * 160 + k.val →
        16 * 160 + k.val < 3000 →
        (16 * 160 + k.val, (nonresidueCoverageData160.getD k.val (0, 0)).1) ∈ (nonresidueTable0) ∨
          (2 ≤ (nonresidueCoverageData160.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData160.getD k.val (0, 0)).2 < 16 * 160 + k.val ∧
            (nonresidueCoverageData160.getD k.val (0, 0)).2 ∣ 16 * 160 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 160 (nonresidueTable0) nonresidueCoverageData160 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2560,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock160_checked : smallNonresidueBlockChecked 160 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock160 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData160.getD k.val (0, 0)).1,
        nonresidueTable0_checked (16 * 160 + k.val, (nonresidueCoverageData160.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2576.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData161 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (0, 29), (0, 2), (0, 3), (0, 2), (0, 5), (0, 2), (0, 13),
    (0, 2), (0, 3), (0, 2), (7, 0)]

/-- Every eligible integer beginning at 2576 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock161 :
    ∀ k : Fin 16,
      5 ≤ 16 * 161 + k.val →
        16 * 161 + k.val < 3000 →
        (16 * 161 + k.val, (nonresidueCoverageData161.getD k.val (0, 0)).1) ∈ (nonresidueTable23) ∨
          (2 ≤ (nonresidueCoverageData161.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData161.getD k.val (0, 0)).2 < 16 * 161 + k.val ∧
            (nonresidueCoverageData161.getD k.val (0, 0)).2 ∣ 16 * 161 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 161 (nonresidueTable23) nonresidueCoverageData161 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2576,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock161_checked : smallNonresidueBlockChecked 161 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock161 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData161.getD k.val (0, 0)).1,
        nonresidueTable23_checked
          (16 * 161 + k.val, (nonresidueCoverageData161.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2592.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData162 : List (ℕ × ℕ) :=
  [(0, 2), (5, 0), (0, 2), (0, 3), (0, 2), (0, 7), (0, 2), (0, 23), (0, 2), (0, 3), (0, 2), (0, 19),
    (0, 2), (0, 5), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 2592 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock162 :
    ∀ k : Fin 16,
      5 ≤ 16 * 162 + k.val →
        16 * 162 + k.val < 3000 →
        (16 * 162 + k.val, (nonresidueCoverageData162.getD k.val (0, 0)).1) ∈ (nonresidueTable23) ∨
          (2 ≤ (nonresidueCoverageData162.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData162.getD k.val (0, 0)).2 < 16 * 162 + k.val ∧
            (nonresidueCoverageData162.getD k.val (0, 0)).2 ∣ 16 * 162 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 162 (nonresidueTable23) nonresidueCoverageData162 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2592,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock162_checked : smallNonresidueBlockChecked 162 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock162 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData162.getD k.val (0, 0)).1,
        nonresidueTable23_checked
          (16 * 162 + k.val, (nonresidueCoverageData162.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2608.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData163 : List (ℕ × ℕ) :=
  [(0, 2), (3, 0), (0, 2), (0, 7), (0, 2), (0, 3), (0, 2), (0, 5), (0, 2), (5, 0), (0, 2), (0, 3),
    (0, 2), (2, 0), (0, 2), (0, 43)]

/-- Every eligible integer beginning at 2608 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock163 :
    ∀ k : Fin 16,
      5 ≤ 16 * 163 + k.val →
        16 * 163 + k.val < 3000 →
        (16 * 163 + k.val, (nonresidueCoverageData163.getD k.val (0, 0)).1) ∈ (nonresidueTable23) ∨
          (2 ≤ (nonresidueCoverageData163.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData163.getD k.val (0, 0)).2 < 16 * 163 + k.val ∧
            (nonresidueCoverageData163.getD k.val (0, 0)).2 ∣ 16 * 163 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 163 (nonresidueTable23) nonresidueCoverageData163 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2608,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock163_checked : smallNonresidueBlockChecked 163 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock163 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData163.getD k.val (0, 0)).1,
        nonresidueTable23_checked
          (16 * 163 + k.val, (nonresidueCoverageData163.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2624.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData164 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (0, 37), (0, 2), (0, 11), (0, 2), (0, 3), (0, 2), (3, 0), (0, 2), (0, 5),
    (0, 2), (0, 3), (0, 2), (0, 7)]

/-- Every eligible integer beginning at 2624 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock164 :
    ∀ k : Fin 16,
      5 ≤ 16 * 164 + k.val →
        16 * 164 + k.val < 3000 →
        (16 * 164 + k.val, (nonresidueCoverageData164.getD k.val (0, 0)).1) ∈ (nonresidueTable23) ∨
          (2 ≤ (nonresidueCoverageData164.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData164.getD k.val (0, 0)).2 < 16 * 164 + k.val ∧
            (nonresidueCoverageData164.getD k.val (0, 0)).2 ∣ 16 * 164 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 164 (nonresidueTable23) nonresidueCoverageData164 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2624,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock164_checked : smallNonresidueBlockChecked 164 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock164 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData164.getD k.val (0, 0)).1,
        nonresidueTable23_checked
          (16 * 164 + k.val, (nonresidueCoverageData164.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2640.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData165 : List (ℕ × ℕ) :=
  [(0, 2), (0, 19), (0, 2), (0, 3), (0, 2), (0, 5), (0, 2), (3, 0), (0, 2), (0, 3), (0, 2), (0, 11),
    (0, 2), (0, 7), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 2640 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock165 :
    ∀ k : Fin 16,
      5 ≤ 16 * 165 + k.val →
        16 * 165 + k.val < 3000 →
        (16 * 165 + k.val, (nonresidueCoverageData165.getD k.val (0, 0)).1) ∈ (nonresidueTable23) ∨
          (2 ≤ (nonresidueCoverageData165.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData165.getD k.val (0, 0)).2 < 16 * 165 + k.val ∧
            (nonresidueCoverageData165.getD k.val (0, 0)).2 ∣ 16 * 165 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 165 (nonresidueTable23) nonresidueCoverageData165 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2640,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock165_checked : smallNonresidueBlockChecked 165 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock165 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData165.getD k.val (0, 0)).1,
        nonresidueTable23_checked
          (16 * 165 + k.val, (nonresidueCoverageData165.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2656.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData166 : List (ℕ × ℕ) :=
  [(0, 2), (3, 0), (0, 2), (2, 0), (0, 2), (0, 3), (0, 2), (5, 0), (0, 2), (0, 5), (0, 2), (0, 3),
    (0, 2), (0, 17), (0, 2), (3, 0)]

/-- Every eligible integer beginning at 2656 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock166 :
    ∀ k : Fin 16,
      5 ≤ 16 * 166 + k.val →
        16 * 166 + k.val < 3000 →
        (16 * 166 + k.val, (nonresidueCoverageData166.getD k.val (0, 0)).1) ∈
            (nonresidueTable23 ++ nonresidueTable24) ∨
          (2 ≤ (nonresidueCoverageData166.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData166.getD k.val (0, 0)).2 < 16 * 166 + k.val ∧
            (nonresidueCoverageData166.getD k.val (0, 0)).2 ∣ 16 * 166 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl :
      nonresidueCoverageCheck 166 (nonresidueTable23 ++ nonresidueTable24)
          nonresidueCoverageData166 =
        true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2656,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock166_checked : smallNonresidueBlockChecked 166 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock166 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData166.getD k.val (0, 0)).1,
        (nonresidueTableChecked_append nonresidueTable23_checked nonresidueTable24_checked)
          (16 * 166 + k.val, (nonresidueCoverageData166.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2672.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData167 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (0, 5), (0, 2), (2, 0), (0, 2), (0, 3), (0, 2), (0, 7), (0, 2), (2, 0),
    (0, 2), (0, 3), (0, 2), (5, 0)]

/-- Every eligible integer beginning at 2672 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock167 :
    ∀ k : Fin 16,
      5 ≤ 16 * 167 + k.val →
        16 * 167 + k.val < 3000 →
        (16 * 167 + k.val, (nonresidueCoverageData167.getD k.val (0, 0)).1) ∈ (nonresidueTable24) ∨
          (2 ≤ (nonresidueCoverageData167.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData167.getD k.val (0, 0)).2 < 16 * 167 + k.val ∧
            (nonresidueCoverageData167.getD k.val (0, 0)).2 ∣ 16 * 167 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 167 (nonresidueTable24) nonresidueCoverageData167 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2672,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock167_checked : smallNonresidueBlockChecked 167 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock167 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData167.getD k.val (0, 0)).1,
        nonresidueTable24_checked
          (16 * 167 + k.val, (nonresidueCoverageData167.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2688.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData168 : List (ℕ × ℕ) :=
  [(0, 2), (13, 0), (0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (0, 5), (0, 2), (0, 3), (0, 2), (2, 0),
    (0, 2), (0, 37), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 2688 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock168 :
    ∀ k : Fin 16,
      5 ≤ 16 * 168 + k.val →
        16 * 168 + k.val < 3000 →
        (16 * 168 + k.val, (nonresidueCoverageData168.getD k.val (0, 0)).1) ∈ (nonresidueTable24) ∨
          (2 ≤ (nonresidueCoverageData168.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData168.getD k.val (0, 0)).2 < 16 * 168 + k.val ∧
            (nonresidueCoverageData168.getD k.val (0, 0)).2 ∣ 16 * 168 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 168 (nonresidueTable24) nonresidueCoverageData168 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2688,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock168_checked : smallNonresidueBlockChecked 168 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock168 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData168.getD k.val (0, 0)).1,
        nonresidueTable24_checked
          (16 * 168 + k.val, (nonresidueCoverageData168.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2704.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData169 : List (ℕ × ℕ) :=
  [(0, 2), (0, 5), (0, 2), (2, 0), (0, 2), (0, 3), (0, 2), (7, 0), (0, 2), (5, 0), (0, 2), (0, 3),
    (0, 2), (0, 11), (0, 2), (3, 0)]

/-- Every eligible integer beginning at 2704 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock169 :
    ∀ k : Fin 16,
      5 ≤ 16 * 169 + k.val →
        16 * 169 + k.val < 3000 →
        (16 * 169 + k.val, (nonresidueCoverageData169.getD k.val (0, 0)).1) ∈ (nonresidueTable24) ∨
          (2 ≤ (nonresidueCoverageData169.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData169.getD k.val (0, 0)).2 < 16 * 169 + k.val ∧
            (nonresidueCoverageData169.getD k.val (0, 0)).2 ∣ 16 * 169 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 169 (nonresidueTable24) nonresidueCoverageData169 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2704,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock169_checked : smallNonresidueBlockChecked 169 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock169 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData169.getD k.val (0, 0)).1,
        nonresidueTable24_checked
          (16 * 169 + k.val, (nonresidueCoverageData169.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2720.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData170 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (0, 7), (0, 2), (0, 5), (0, 2), (0, 3), (0, 2), (3, 0), (0, 2), (2, 0),
    (0, 2), (0, 3), (0, 2), (0, 5)]

/-- Every eligible integer beginning at 2720 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock170 :
    ∀ k : Fin 16,
      5 ≤ 16 * 170 + k.val →
        16 * 170 + k.val < 3000 →
        (16 * 170 + k.val, (nonresidueCoverageData170.getD k.val (0, 0)).1) ∈ (nonresidueTable24) ∨
          (2 ≤ (nonresidueCoverageData170.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData170.getD k.val (0, 0)).2 < 16 * 170 + k.val ∧
            (nonresidueCoverageData170.getD k.val (0, 0)).2 ∣ 16 * 170 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 170 (nonresidueTable24) nonresidueCoverageData170 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2720,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock170_checked : smallNonresidueBlockChecked 170 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock170 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData170.getD k.val (0, 0)).1,
        nonresidueTable24_checked
          (16 * 170 + k.val, (nonresidueCoverageData170.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2736.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData171 : List (ℕ × ℕ) :=
  [(0, 2), (0, 7), (0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (0, 13), (0, 2), (0, 3), (0, 2), (0, 41),
    (0, 2), (2, 0), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 2736 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock171 :
    ∀ k : Fin 16,
      5 ≤ 16 * 171 + k.val →
        16 * 171 + k.val < 3000 →
        (16 * 171 + k.val, (nonresidueCoverageData171.getD k.val (0, 0)).1) ∈ (nonresidueTable24) ∨
          (2 ≤ (nonresidueCoverageData171.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData171.getD k.val (0, 0)).2 < 16 * 171 + k.val ∧
            (nonresidueCoverageData171.getD k.val (0, 0)).2 ∣ 16 * 171 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 171 (nonresidueTable24) nonresidueCoverageData171 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2736,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock171_checked : smallNonresidueBlockChecked 171 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock171 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData171.getD k.val (0, 0)).1,
        nonresidueTable24_checked
          (16 * 171 + k.val, (nonresidueCoverageData171.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2752.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData172 : List (ℕ × ℕ) :=
  [(0, 2), (3, 0), (0, 2), (0, 5), (0, 2), (0, 3), (0, 2), (0, 31), (0, 2), (0, 11), (0, 2), (0, 3),
    (0, 2), (0, 5), (0, 2), (3, 0)]

/-- Every eligible integer beginning at 2752 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock172 :
    ∀ k : Fin 16,
      5 ≤ 16 * 172 + k.val →
        16 * 172 + k.val < 3000 →
        (16 * 172 + k.val, (nonresidueCoverageData172.getD k.val (0, 0)).1) ∈
            (nonresidueTable24 ++ nonresidueTable25) ∨
          (2 ≤ (nonresidueCoverageData172.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData172.getD k.val (0, 0)).2 < 16 * 172 + k.val ∧
            (nonresidueCoverageData172.getD k.val (0, 0)).2 ∣ 16 * 172 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl :
      nonresidueCoverageCheck 172 (nonresidueTable24 ++ nonresidueTable25)
          nonresidueCoverageData172 =
        true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2752,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock172_checked : smallNonresidueBlockChecked 172 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock172 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData172.getD k.val (0, 0)).1,
        (nonresidueTableChecked_append nonresidueTable24_checked nonresidueTable25_checked)
          (16 * 172 + k.val, (nonresidueCoverageData172.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2768.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData173 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (0, 17), (0, 2), (0, 47), (0, 2), (0, 3), (0, 2), (3, 0), (0, 2), (0, 7),
    (0, 2), (0, 3), (0, 2), (0, 11)]

/-- Every eligible integer beginning at 2768 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock173 :
    ∀ k : Fin 16,
      5 ≤ 16 * 173 + k.val →
        16 * 173 + k.val < 3000 →
        (16 * 173 + k.val, (nonresidueCoverageData173.getD k.val (0, 0)).1) ∈ (nonresidueTable25) ∨
          (2 ≤ (nonresidueCoverageData173.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData173.getD k.val (0, 0)).2 < 16 * 173 + k.val ∧
            (nonresidueCoverageData173.getD k.val (0, 0)).2 ∣ 16 * 173 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 173 (nonresidueTable25) nonresidueCoverageData173 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2768,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock173_checked : smallNonresidueBlockChecked 173 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock173 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData173.getD k.val (0, 0)).1,
        nonresidueTable25_checked
          (16 * 173 + k.val, (nonresidueCoverageData173.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2784.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData174 : List (ℕ × ℕ) :=
  [(0, 2), (0, 5), (0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (3, 0), (0, 2), (0, 3), (0, 2), (0, 5),
    (0, 2), (2, 0), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 2784 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock174 :
    ∀ k : Fin 16,
      5 ≤ 16 * 174 + k.val →
        16 * 174 + k.val < 3000 →
        (16 * 174 + k.val, (nonresidueCoverageData174.getD k.val (0, 0)).1) ∈ (nonresidueTable25) ∨
          (2 ≤ (nonresidueCoverageData174.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData174.getD k.val (0, 0)).2 < 16 * 174 + k.val ∧
            (nonresidueCoverageData174.getD k.val (0, 0)).2 ∣ 16 * 174 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 174 (nonresidueTable25) nonresidueCoverageData174 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2784,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock174_checked : smallNonresidueBlockChecked 174 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock174 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData174.getD k.val (0, 0)).1,
        nonresidueTable25_checked
          (16 * 174 + k.val, (nonresidueCoverageData174.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2800.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData175 : List (ℕ × ℕ) :=
  [(0, 2), (3, 0), (0, 2), (2, 0), (0, 2), (0, 3), (0, 2), (0, 7), (0, 2), (0, 53), (0, 2), (0, 3),
    (0, 2), (0, 29), (0, 2), (0, 5)]

/-- Every eligible integer beginning at 2800 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock175 :
    ∀ k : Fin 16,
      5 ≤ 16 * 175 + k.val →
        16 * 175 + k.val < 3000 →
        (16 * 175 + k.val, (nonresidueCoverageData175.getD k.val (0, 0)).1) ∈ (nonresidueTable25) ∨
          (2 ≤ (nonresidueCoverageData175.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData175.getD k.val (0, 0)).2 < 16 * 175 + k.val ∧
            (nonresidueCoverageData175.getD k.val (0, 0)).2 ∣ 16 * 175 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 175 (nonresidueTable25) nonresidueCoverageData175 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2800,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock175_checked : smallNonresidueBlockChecked 175 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock175 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData175.getD k.val (0, 0)).1,
        nonresidueTable25_checked
          (16 * 175 + k.val, (nonresidueCoverageData175.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2816.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData176 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (0, 7), (0, 2), (0, 3), (0, 2), (0, 5), (0, 2), (0, 11),
    (0, 2), (0, 3), (0, 2), (0, 19)]

/-- Every eligible integer beginning at 2816 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock176 :
    ∀ k : Fin 16,
      5 ≤ 16 * 176 + k.val →
        16 * 176 + k.val < 3000 →
        (16 * 176 + k.val, (nonresidueCoverageData176.getD k.val (0, 0)).1) ∈ (nonresidueTable25) ∨
          (2 ≤ (nonresidueCoverageData176.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData176.getD k.val (0, 0)).2 < 16 * 176 + k.val ∧
            (nonresidueCoverageData176.getD k.val (0, 0)).2 ∣ 16 * 176 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 176 (nonresidueTable25) nonresidueCoverageData176 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2816,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock176_checked : smallNonresidueBlockChecked 176 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock176 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData176.getD k.val (0, 0)).1,
        nonresidueTable25_checked
          (16 * 176 + k.val, (nonresidueCoverageData176.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2832.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData177 : List (ℕ × ℕ) :=
  [(0, 2), (5, 0), (0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (0, 17), (0, 2), (0, 3), (0, 2), (2, 0),
    (0, 2), (0, 5), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 2832 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock177 :
    ∀ k : Fin 16,
      5 ≤ 16 * 177 + k.val →
        16 * 177 + k.val < 3000 →
        (16 * 177 + k.val, (nonresidueCoverageData177.getD k.val (0, 0)).1) ∈ (nonresidueTable25) ∨
          (2 ≤ (nonresidueCoverageData177.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData177.getD k.val (0, 0)).2 < 16 * 177 + k.val ∧
            (nonresidueCoverageData177.getD k.val (0, 0)).2 ∣ 16 * 177 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 177 (nonresidueTable25) nonresidueCoverageData177 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2832,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock177_checked : smallNonresidueBlockChecked 177 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock177 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData177.getD k.val (0, 0)).1,
        nonresidueTable25_checked
          (16 * 177 + k.val, (nonresidueCoverageData177.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2848.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData178 : List (ℕ × ℕ) :=
  [(0, 2), (0, 7), (0, 2), (2, 0), (0, 2), (0, 3), (0, 2), (0, 5), (0, 2), (5, 0), (0, 2), (0, 3),
    (0, 2), (2, 0), (0, 2), (0, 7)]

/-- Every eligible integer beginning at 2848 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock178 :
    ∀ k : Fin 16,
      5 ≤ 16 * 178 + k.val →
        16 * 178 + k.val < 3000 →
        (16 * 178 + k.val, (nonresidueCoverageData178.getD k.val (0, 0)).1) ∈ (nonresidueTable25) ∨
          (2 ≤ (nonresidueCoverageData178.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData178.getD k.val (0, 0)).2 < 16 * 178 + k.val ∧
            (nonresidueCoverageData178.getD k.val (0, 0)).2 ∣ 16 * 178 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 178 (nonresidueTable25) nonresidueCoverageData178 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2848,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock178_checked : smallNonresidueBlockChecked 178 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock178 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData178.getD k.val (0, 0)).1,
        nonresidueTable25_checked
          (16 * 178 + k.val, (nonresidueCoverageData178.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2864.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData179 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (0, 47), (0, 2), (0, 19), (0, 2), (0, 3), (0, 2), (0, 13), (0, 2),
    (0, 5), (0, 2), (0, 3), (0, 2), (7, 0)]

/-- Every eligible integer beginning at 2864 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock179 :
    ∀ k : Fin 16,
      5 ≤ 16 * 179 + k.val →
        16 * 179 + k.val < 3000 →
        (16 * 179 + k.val, (nonresidueCoverageData179.getD k.val (0, 0)).1) ∈ (nonresidueTable25) ∨
          (2 ≤ (nonresidueCoverageData179.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData179.getD k.val (0, 0)).2 < 16 * 179 + k.val ∧
            (nonresidueCoverageData179.getD k.val (0, 0)).2 ∣ 16 * 179 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 179 (nonresidueTable25) nonresidueCoverageData179 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2864,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock179_checked : smallNonresidueBlockChecked 179 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock179 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData179.getD k.val (0, 0)).1,
        nonresidueTable25_checked
          (16 * 179 + k.val, (nonresidueCoverageData179.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2880.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData180 : List (ℕ × ℕ) :=
  [(0, 2), (0, 43), (0, 2), (0, 3), (0, 2), (0, 5), (0, 2), (3, 0), (0, 2), (0, 3), (0, 2), (0, 7),
    (0, 2), (0, 11), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 2880 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock180 :
    ∀ k : Fin 16,
      5 ≤ 16 * 180 + k.val →
        16 * 180 + k.val < 3000 →
        (16 * 180 + k.val, (nonresidueCoverageData180.getD k.val (0, 0)).1) ∈ (nonresidueTable25) ∨
          (2 ≤ (nonresidueCoverageData180.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData180.getD k.val (0, 0)).2 < 16 * 180 + k.val ∧
            (nonresidueCoverageData180.getD k.val (0, 0)).2 ∣ 16 * 180 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 180 (nonresidueTable25) nonresidueCoverageData180 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2880,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock180_checked : smallNonresidueBlockChecked 180 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock180 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData180.getD k.val (0, 0)).1,
        nonresidueTable25_checked
          (16 * 180 + k.val, (nonresidueCoverageData180.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2896.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData181 : List (ℕ × ℕ) :=
  [(0, 2), (3, 0), (0, 2), (0, 13), (0, 2), (0, 3), (0, 2), (5, 0), (0, 2), (0, 5), (0, 2), (0, 3),
    (0, 2), (2, 0), (0, 2), (0, 41)]

/-- Every eligible integer beginning at 2896 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock181 :
    ∀ k : Fin 16,
      5 ≤ 16 * 181 + k.val →
        16 * 181 + k.val < 3000 →
        (16 * 181 + k.val, (nonresidueCoverageData181.getD k.val (0, 0)).1) ∈ (nonresidueTable26) ∨
          (2 ≤ (nonresidueCoverageData181.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData181.getD k.val (0, 0)).2 < 16 * 181 + k.val ∧
            (nonresidueCoverageData181.getD k.val (0, 0)).2 ∣ 16 * 181 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 181 (nonresidueTable26) nonresidueCoverageData181 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2896,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock181_checked : smallNonresidueBlockChecked 181 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock181 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData181.getD k.val (0, 0)).1,
        nonresidueTable26_checked
          (16 * 181 + k.val, (nonresidueCoverageData181.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2912.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData182 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (0, 5), (0, 2), (2, 0), (0, 2), (0, 3), (0, 2), (0, 23), (0, 2), (0, 37),
    (0, 2), (0, 3), (0, 2), (5, 0)]

/-- Every eligible integer beginning at 2912 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock182 :
    ∀ k : Fin 16,
      5 ≤ 16 * 182 + k.val →
        16 * 182 + k.val < 3000 →
        (16 * 182 + k.val, (nonresidueCoverageData182.getD k.val (0, 0)).1) ∈ (nonresidueTable26) ∨
          (2 ≤ (nonresidueCoverageData182.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData182.getD k.val (0, 0)).2 < 16 * 182 + k.val ∧
            (nonresidueCoverageData182.getD k.val (0, 0)).2 ∣ 16 * 182 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 182 (nonresidueTable26) nonresidueCoverageData182 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2912,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock182_checked : smallNonresidueBlockChecked 182 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock182 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData182.getD k.val (0, 0)).1,
        nonresidueTable26_checked
          (16 * 182 + k.val, (nonresidueCoverageData182.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2928.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData183 : List (ℕ × ℕ) :=
  [(0, 2), (0, 29), (0, 2), (0, 3), (0, 2), (0, 7), (0, 2), (0, 5), (0, 2), (0, 3), (0, 2), (2, 0),
    (0, 2), (0, 17), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 2928 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock183 :
    ∀ k : Fin 16,
      5 ≤ 16 * 183 + k.val →
        16 * 183 + k.val < 3000 →
        (16 * 183 + k.val, (nonresidueCoverageData183.getD k.val (0, 0)).1) ∈ (nonresidueTable26) ∨
          (2 ≤ (nonresidueCoverageData183.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData183.getD k.val (0, 0)).2 < 16 * 183 + k.val ∧
            (nonresidueCoverageData183.getD k.val (0, 0)).2 ∣ 16 * 183 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 183 (nonresidueTable26) nonresidueCoverageData183 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2928,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock183_checked : smallNonresidueBlockChecked 183 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock183 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData183.getD k.val (0, 0)).1,
        nonresidueTable26_checked
          (16 * 183 + k.val, (nonresidueCoverageData183.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2944.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData184 : List (ℕ × ℕ) :=
  [(0, 2), (0, 5), (0, 2), (0, 7), (0, 2), (0, 3), (0, 2), (0, 13), (0, 2), (5, 0), (0, 2), (0, 3),
    (0, 2), (2, 0), (0, 2), (0, 11)]

/-- Every eligible integer beginning at 2944 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock184 :
    ∀ k : Fin 16,
      5 ≤ 16 * 184 + k.val →
        16 * 184 + k.val < 3000 →
        (16 * 184 + k.val, (nonresidueCoverageData184.getD k.val (0, 0)).1) ∈ (nonresidueTable26) ∨
          (2 ≤ (nonresidueCoverageData184.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData184.getD k.val (0, 0)).2 < 16 * 184 + k.val ∧
            (nonresidueCoverageData184.getD k.val (0, 0)).2 ∣ 16 * 184 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 184 (nonresidueTable26) nonresidueCoverageData184 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2944,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock184_checked : smallNonresidueBlockChecked 184 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock184 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData184.getD k.val (0, 0)).1,
        nonresidueTable26_checked
          (16 * 184 + k.val, (nonresidueCoverageData184.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2960.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData185 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 2), (2, 0), (0, 2), (0, 5), (0, 2), (0, 3), (0, 2), (3, 0), (0, 2), (2, 0),
    (0, 2), (0, 3), (0, 2), (0, 5)]

/-- Every eligible integer beginning at 2960 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock185 :
    ∀ k : Fin 16,
      5 ≤ 16 * 185 + k.val →
        16 * 185 + k.val < 3000 →
        (16 * 185 + k.val, (nonresidueCoverageData185.getD k.val (0, 0)).1) ∈ (nonresidueTable26) ∨
          (2 ≤ (nonresidueCoverageData185.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData185.getD k.val (0, 0)).2 < 16 * 185 + k.val ∧
            (nonresidueCoverageData185.getD k.val (0, 0)).2 ∣ 16 * 185 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 185 (nonresidueTable26) nonresidueCoverageData185 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2960,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock185_checked : smallNonresidueBlockChecked 185 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock185 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData185.getD k.val (0, 0)).1,
        nonresidueTable26_checked
          (16 * 185 + k.val, (nonresidueCoverageData185.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2976.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData186 : List (ℕ × ℕ) :=
  [(0, 2), (0, 13), (0, 2), (0, 3), (0, 2), (0, 11), (0, 2), (0, 19), (0, 2), (0, 3), (0, 2),
    (0, 29), (0, 2), (0, 7), (0, 2), (0, 3)]

/-- Every eligible integer beginning at 2976 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock186 :
    ∀ k : Fin 16,
      5 ≤ 16 * 186 + k.val →
        16 * 186 + k.val < 3000 →
        (16 * 186 + k.val, (nonresidueCoverageData186.getD k.val (0, 0)).1) ∈ (nonresidueTable0) ∨
          (2 ≤ (nonresidueCoverageData186.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData186.getD k.val (0, 0)).2 < 16 * 186 + k.val ∧
            (nonresidueCoverageData186.getD k.val (0, 0)).2 ∣ 16 * 186 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 186 (nonresidueTable0) nonresidueCoverageData186 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2976,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock186_checked : smallNonresidueBlockChecked 186 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock186 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData186.getD k.val (0, 0)).1,
        nonresidueTable0_checked (16 * 186 + k.val, (nonresidueCoverageData186.getD k.val (0, 0)).1)
          hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Witnesses or proper divisors for the sixteen integers beginning at 2992.
Both components are candidate data, checked by the coverage theorem. -/
def nonresidueCoverageData187 : List (ℕ × ℕ) :=
  [(0, 2), (0, 41), (0, 2), (0, 5), (0, 2), (0, 3), (0, 2), (17, 0), (0, 0), (0, 0), (0, 0), (0, 0),
    (0, 0), (0, 0), (0, 0), (0, 0)]

/-- Every eligible integer beginning at 2992 has a listed witness or a proper divisor.
Kernel decision verifies membership and divisibility independently
of Python's prime enumeration. -/
theorem nonresidueCoverageBlock187 :
    ∀ k : Fin 16,
      5 ≤ 16 * 187 + k.val →
        16 * 187 + k.val < 3000 →
        (16 * 187 + k.val, (nonresidueCoverageData187.getD k.val (0, 0)).1) ∈ (nonresidueTable26) ∨
          (2 ≤ (nonresidueCoverageData187.getD k.val (0, 0)).2 ∧
            (nonresidueCoverageData187.getD k.val (0, 0)).2 < 16 * 187 + k.val ∧
            (nonresidueCoverageData187.getD k.val (0, 0)).2 ∣ 16 * 187 + k.val) :=
  nonresidueCoverageCheck_sound
    (rfl : nonresidueCoverageCheck 187 (nonresidueTable26) nonresidueCoverageData187 = true)

/-- Positive capped Jacobi witnesses throughout the interval beginning at 2992,
obtained by combining exhaustive table coverage with the checked witness entries. -/
theorem smallNonresidueBlock187_checked : smallNonresidueBlockChecked 187 := fun k hk hlt hp ↦
  Or.elim (nonresidueCoverageBlock187 k hk hlt)
    (fun hn ↦
      ⟨(nonresidueCoverageData187.getD k.val (0, 0)).1,
        nonresidueTable26_checked
          (16 * 187 + k.val, (nonresidueCoverageData187.getD k.val (0, 0)).1) hn⟩)
    (fun hd ↦ False.elim (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1 hp))

/-- Finite assembly of certificate intervals 0 through 15. -/
theorem smallNonresidueBlockGroup0 : ∀ b : Fin 16, smallNonresidueBlockChecked (0 + b.val) :=
  (Fin.cases smallNonresidueBlock0_checked
    (Fin.cases smallNonresidueBlock1_checked
      (Fin.cases smallNonresidueBlock2_checked
        (Fin.cases smallNonresidueBlock3_checked
          (Fin.cases smallNonresidueBlock4_checked
            (Fin.cases smallNonresidueBlock5_checked
              (Fin.cases smallNonresidueBlock6_checked
                (Fin.cases smallNonresidueBlock7_checked
                  (Fin.cases smallNonresidueBlock8_checked
                    (Fin.cases smallNonresidueBlock9_checked
                      (Fin.cases smallNonresidueBlock10_checked
                        (Fin.cases smallNonresidueBlock11_checked
                          (Fin.cases smallNonresidueBlock12_checked
                            (Fin.cases smallNonresidueBlock13_checked
                              (Fin.cases smallNonresidueBlock14_checked
                                (Fin.cases smallNonresidueBlock15_checked
                                  (fun b ↦ Fin.elim0 b)))))))))))))))))

/-- Finite assembly of certificate intervals 16 through 31. -/
theorem smallNonresidueBlockGroup1 : ∀ b : Fin 16, smallNonresidueBlockChecked (16 + b.val) :=
  (Fin.cases smallNonresidueBlock16_checked
    (Fin.cases smallNonresidueBlock17_checked
      (Fin.cases smallNonresidueBlock18_checked
        (Fin.cases smallNonresidueBlock19_checked
          (Fin.cases smallNonresidueBlock20_checked
            (Fin.cases smallNonresidueBlock21_checked
              (Fin.cases smallNonresidueBlock22_checked
                (Fin.cases smallNonresidueBlock23_checked
                  (Fin.cases smallNonresidueBlock24_checked
                    (Fin.cases smallNonresidueBlock25_checked
                      (Fin.cases smallNonresidueBlock26_checked
                        (Fin.cases smallNonresidueBlock27_checked
                          (Fin.cases smallNonresidueBlock28_checked
                            (Fin.cases smallNonresidueBlock29_checked
                              (Fin.cases smallNonresidueBlock30_checked
                                (Fin.cases smallNonresidueBlock31_checked
                                  (fun b ↦ Fin.elim0 b)))))))))))))))))

/-- Finite assembly of certificate intervals 32 through 47. -/
theorem smallNonresidueBlockGroup2 : ∀ b : Fin 16, smallNonresidueBlockChecked (32 + b.val) :=
  (Fin.cases smallNonresidueBlock32_checked
    (Fin.cases smallNonresidueBlock33_checked
      (Fin.cases smallNonresidueBlock34_checked
        (Fin.cases smallNonresidueBlock35_checked
          (Fin.cases smallNonresidueBlock36_checked
            (Fin.cases smallNonresidueBlock37_checked
              (Fin.cases smallNonresidueBlock38_checked
                (Fin.cases smallNonresidueBlock39_checked
                  (Fin.cases smallNonresidueBlock40_checked
                    (Fin.cases smallNonresidueBlock41_checked
                      (Fin.cases smallNonresidueBlock42_checked
                        (Fin.cases smallNonresidueBlock43_checked
                          (Fin.cases smallNonresidueBlock44_checked
                            (Fin.cases smallNonresidueBlock45_checked
                              (Fin.cases smallNonresidueBlock46_checked
                                (Fin.cases smallNonresidueBlock47_checked
                                  (fun b ↦ Fin.elim0 b)))))))))))))))))

/-- Finite assembly of certificate intervals 48 through 63. -/
theorem smallNonresidueBlockGroup3 : ∀ b : Fin 16, smallNonresidueBlockChecked (48 + b.val) :=
  (Fin.cases smallNonresidueBlock48_checked
    (Fin.cases smallNonresidueBlock49_checked
      (Fin.cases smallNonresidueBlock50_checked
        (Fin.cases smallNonresidueBlock51_checked
          (Fin.cases smallNonresidueBlock52_checked
            (Fin.cases smallNonresidueBlock53_checked
              (Fin.cases smallNonresidueBlock54_checked
                (Fin.cases smallNonresidueBlock55_checked
                  (Fin.cases smallNonresidueBlock56_checked
                    (Fin.cases smallNonresidueBlock57_checked
                      (Fin.cases smallNonresidueBlock58_checked
                        (Fin.cases smallNonresidueBlock59_checked
                          (Fin.cases smallNonresidueBlock60_checked
                            (Fin.cases smallNonresidueBlock61_checked
                              (Fin.cases smallNonresidueBlock62_checked
                                (Fin.cases smallNonresidueBlock63_checked
                                  (fun b ↦ Fin.elim0 b)))))))))))))))))

/-- Finite assembly of certificate intervals 64 through 79. -/
theorem smallNonresidueBlockGroup4 : ∀ b : Fin 16, smallNonresidueBlockChecked (64 + b.val) :=
  (Fin.cases smallNonresidueBlock64_checked
    (Fin.cases smallNonresidueBlock65_checked
      (Fin.cases smallNonresidueBlock66_checked
        (Fin.cases smallNonresidueBlock67_checked
          (Fin.cases smallNonresidueBlock68_checked
            (Fin.cases smallNonresidueBlock69_checked
              (Fin.cases smallNonresidueBlock70_checked
                (Fin.cases smallNonresidueBlock71_checked
                  (Fin.cases smallNonresidueBlock72_checked
                    (Fin.cases smallNonresidueBlock73_checked
                      (Fin.cases smallNonresidueBlock74_checked
                        (Fin.cases smallNonresidueBlock75_checked
                          (Fin.cases smallNonresidueBlock76_checked
                            (Fin.cases smallNonresidueBlock77_checked
                              (Fin.cases smallNonresidueBlock78_checked
                                (Fin.cases smallNonresidueBlock79_checked
                                  (fun b ↦ Fin.elim0 b)))))))))))))))))

/-- Finite assembly of certificate intervals 80 through 95. -/
theorem smallNonresidueBlockGroup5 : ∀ b : Fin 16, smallNonresidueBlockChecked (80 + b.val) :=
  (Fin.cases smallNonresidueBlock80_checked
    (Fin.cases smallNonresidueBlock81_checked
      (Fin.cases smallNonresidueBlock82_checked
        (Fin.cases smallNonresidueBlock83_checked
          (Fin.cases smallNonresidueBlock84_checked
            (Fin.cases smallNonresidueBlock85_checked
              (Fin.cases smallNonresidueBlock86_checked
                (Fin.cases smallNonresidueBlock87_checked
                  (Fin.cases smallNonresidueBlock88_checked
                    (Fin.cases smallNonresidueBlock89_checked
                      (Fin.cases smallNonresidueBlock90_checked
                        (Fin.cases smallNonresidueBlock91_checked
                          (Fin.cases smallNonresidueBlock92_checked
                            (Fin.cases smallNonresidueBlock93_checked
                              (Fin.cases smallNonresidueBlock94_checked
                                (Fin.cases smallNonresidueBlock95_checked
                                  (fun b ↦ Fin.elim0 b)))))))))))))))))

/-- Finite assembly of certificate intervals 96 through 111. -/
theorem smallNonresidueBlockGroup6 : ∀ b : Fin 16, smallNonresidueBlockChecked (96 + b.val) :=
  (Fin.cases smallNonresidueBlock96_checked
    (Fin.cases smallNonresidueBlock97_checked
      (Fin.cases smallNonresidueBlock98_checked
        (Fin.cases smallNonresidueBlock99_checked
          (Fin.cases smallNonresidueBlock100_checked
            (Fin.cases smallNonresidueBlock101_checked
              (Fin.cases smallNonresidueBlock102_checked
                (Fin.cases smallNonresidueBlock103_checked
                  (Fin.cases smallNonresidueBlock104_checked
                    (Fin.cases smallNonresidueBlock105_checked
                      (Fin.cases smallNonresidueBlock106_checked
                        (Fin.cases smallNonresidueBlock107_checked
                          (Fin.cases smallNonresidueBlock108_checked
                            (Fin.cases smallNonresidueBlock109_checked
                              (Fin.cases smallNonresidueBlock110_checked
                                (Fin.cases smallNonresidueBlock111_checked
                                  (fun b ↦ Fin.elim0 b)))))))))))))))))

/-- Finite assembly of certificate intervals 112 through 127. -/
theorem smallNonresidueBlockGroup7 : ∀ b : Fin 16, smallNonresidueBlockChecked (112 + b.val) :=
  (Fin.cases smallNonresidueBlock112_checked
    (Fin.cases smallNonresidueBlock113_checked
      (Fin.cases smallNonresidueBlock114_checked
        (Fin.cases smallNonresidueBlock115_checked
          (Fin.cases smallNonresidueBlock116_checked
            (Fin.cases smallNonresidueBlock117_checked
              (Fin.cases smallNonresidueBlock118_checked
                (Fin.cases smallNonresidueBlock119_checked
                  (Fin.cases smallNonresidueBlock120_checked
                    (Fin.cases smallNonresidueBlock121_checked
                      (Fin.cases smallNonresidueBlock122_checked
                        (Fin.cases smallNonresidueBlock123_checked
                          (Fin.cases smallNonresidueBlock124_checked
                            (Fin.cases smallNonresidueBlock125_checked
                              (Fin.cases smallNonresidueBlock126_checked
                                (Fin.cases smallNonresidueBlock127_checked
                                  (fun b ↦ Fin.elim0 b)))))))))))))))))

/-- Finite assembly of certificate intervals 128 through 143. -/
theorem smallNonresidueBlockGroup8 : ∀ b : Fin 16, smallNonresidueBlockChecked (128 + b.val) :=
  (Fin.cases smallNonresidueBlock128_checked
    (Fin.cases smallNonresidueBlock129_checked
      (Fin.cases smallNonresidueBlock130_checked
        (Fin.cases smallNonresidueBlock131_checked
          (Fin.cases smallNonresidueBlock132_checked
            (Fin.cases smallNonresidueBlock133_checked
              (Fin.cases smallNonresidueBlock134_checked
                (Fin.cases smallNonresidueBlock135_checked
                  (Fin.cases smallNonresidueBlock136_checked
                    (Fin.cases smallNonresidueBlock137_checked
                      (Fin.cases smallNonresidueBlock138_checked
                        (Fin.cases smallNonresidueBlock139_checked
                          (Fin.cases smallNonresidueBlock140_checked
                            (Fin.cases smallNonresidueBlock141_checked
                              (Fin.cases smallNonresidueBlock142_checked
                                (Fin.cases smallNonresidueBlock143_checked
                                  (fun b ↦ Fin.elim0 b)))))))))))))))))

/-- Finite assembly of certificate intervals 144 through 159. -/
theorem smallNonresidueBlockGroup9 : ∀ b : Fin 16, smallNonresidueBlockChecked (144 + b.val) :=
  (Fin.cases smallNonresidueBlock144_checked
    (Fin.cases smallNonresidueBlock145_checked
      (Fin.cases smallNonresidueBlock146_checked
        (Fin.cases smallNonresidueBlock147_checked
          (Fin.cases smallNonresidueBlock148_checked
            (Fin.cases smallNonresidueBlock149_checked
              (Fin.cases smallNonresidueBlock150_checked
                (Fin.cases smallNonresidueBlock151_checked
                  (Fin.cases smallNonresidueBlock152_checked
                    (Fin.cases smallNonresidueBlock153_checked
                      (Fin.cases smallNonresidueBlock154_checked
                        (Fin.cases smallNonresidueBlock155_checked
                          (Fin.cases smallNonresidueBlock156_checked
                            (Fin.cases smallNonresidueBlock157_checked
                              (Fin.cases smallNonresidueBlock158_checked
                                (Fin.cases smallNonresidueBlock159_checked
                                  (fun b ↦ Fin.elim0 b)))))))))))))))))

/-- Finite assembly of certificate intervals 160 through 175. -/
theorem smallNonresidueBlockGroup10 : ∀ b : Fin 16, smallNonresidueBlockChecked (160 + b.val) :=
  (Fin.cases smallNonresidueBlock160_checked
    (Fin.cases smallNonresidueBlock161_checked
      (Fin.cases smallNonresidueBlock162_checked
        (Fin.cases smallNonresidueBlock163_checked
          (Fin.cases smallNonresidueBlock164_checked
            (Fin.cases smallNonresidueBlock165_checked
              (Fin.cases smallNonresidueBlock166_checked
                (Fin.cases smallNonresidueBlock167_checked
                  (Fin.cases smallNonresidueBlock168_checked
                    (Fin.cases smallNonresidueBlock169_checked
                      (Fin.cases smallNonresidueBlock170_checked
                        (Fin.cases smallNonresidueBlock171_checked
                          (Fin.cases smallNonresidueBlock172_checked
                            (Fin.cases smallNonresidueBlock173_checked
                              (Fin.cases smallNonresidueBlock174_checked
                                (Fin.cases smallNonresidueBlock175_checked
                                  (fun b ↦ Fin.elim0 b)))))))))))))))))

/-- Finite assembly of certificate intervals 176 through 187. -/
theorem smallNonresidueBlockGroup11 : ∀ b : Fin 12, smallNonresidueBlockChecked (176 + b.val) :=
  (Fin.cases smallNonresidueBlock176_checked
    (Fin.cases smallNonresidueBlock177_checked
      (Fin.cases smallNonresidueBlock178_checked
        (Fin.cases smallNonresidueBlock179_checked
          (Fin.cases smallNonresidueBlock180_checked
            (Fin.cases smallNonresidueBlock181_checked
              (Fin.cases smallNonresidueBlock182_checked
                (Fin.cases smallNonresidueBlock183_checked
                  (Fin.cases smallNonresidueBlock184_checked
                    (Fin.cases smallNonresidueBlock185_checked
                      (Fin.cases smallNonresidueBlock186_checked
                        (Fin.cases smallNonresidueBlock187_checked (fun b ↦ Fin.elim0 b)))))))))))))

/-- All 188 bounded intervals are certified by finite case assembly.
The last interval is restricted to moduli below 3000 in its predicate. -/
theorem smallNonresidueBlocks_checked : ∀ b : Fin 188, smallNonresidueBlockChecked b.val := fun b ↦
  Eq.mp (congrArg smallNonresidueBlockChecked (Nat.zero_add b.val))
    ((smallNonresidueBlockGroups_append smallNonresidueBlockGroup0
        (smallNonresidueBlockGroups_append smallNonresidueBlockGroup1
          (smallNonresidueBlockGroups_append smallNonresidueBlockGroup2
            (smallNonresidueBlockGroups_append smallNonresidueBlockGroup3
              (smallNonresidueBlockGroups_append smallNonresidueBlockGroup4
                (smallNonresidueBlockGroups_append smallNonresidueBlockGroup5
                  (smallNonresidueBlockGroups_append smallNonresidueBlockGroup6
                    (smallNonresidueBlockGroups_append smallNonresidueBlockGroup7
                      (smallNonresidueBlockGroups_append smallNonresidueBlockGroup8
                        (smallNonresidueBlockGroups_append smallNonresidueBlockGroup9
                          (smallNonresidueBlockGroups_append smallNonresidueBlockGroup10
                            smallNonresidueBlockGroup11)))))))))))
      b)

-- END GENERATED NONRESIDUE TABLES

/-- Every prime between 5 and 2999 has a positive capped Jacobi witness.
Division by 16 locates its certified interval; the division identity restores the modulus. -/
theorem exists_smallNonresidue {q : ℕ} (hp : q.Prime) (h5 : 5 ≤ q) (hq : q < 3000) :
    smallNonresidueAt q :=
  let b : Fin 188 :=
    ⟨q / 16, Nat.div_lt_of_lt_mul (hq.trans_le (of_decide_eq_true rfl : 3000 ≤ 16 * 188))⟩
  let k : Fin 16 := ⟨q % 16, Nat.mod_lt q (of_decide_eq_true rfl : 0 < 16)⟩
  let certificate : 5 ≤ q → q < 3000 → q.Prime → smallNonresidueAt q :=
    Eq.mp
      (congrArg (fun r : ℕ ↦ 5 ≤ r → r < 3000 → r.Prime → smallNonresidueAt r)
        (Nat.div_add_mod q 16))
      (smallNonresidueBlocks_checked b k)
  certificate h5 hq hp

end PseudoPrime.LLS
