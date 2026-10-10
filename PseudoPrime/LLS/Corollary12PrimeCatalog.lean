/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.PrimeTreeEnumeration
public import Mathlib.Tactic.NormNum.Prime

/-! Shared prime catalog for the finite part of Corollary 1.2.
Regenerate with generate_corollary12_catalog.py. -/

@[expose] public section

namespace PseudoPrime.LLS.Corollary12PrimeCatalog

/-- A balanced subtree of submitted prime labels. -/
def subtree0 : BinaryTree ℕ :=
  (.node 29
    (.node 13 (.node 7 (.node 5 (.node 3 .nil .nil) .nil) (.node 11 .nil .nil))
      (.node 19 (.node 17 .nil .nil) (.node 23 .nil .nil)))
    (.node 47 (.node 41 (.node 37 (.node 31 .nil .nil) .nil) (.node 43 .nil .nil))
      (.node 59 (.node 53 .nil .nil) (.node 61 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree0_checked : NumberTheory.primeTreeChecked subtree0 := by
  norm_num only [subtree0, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree1 : BinaryTree ℕ :=
  (.node 107
    (.node 89 (.node 79 (.node 73 (.node 71 .nil .nil) .nil) (.node 83 .nil .nil))
      (.node 101 (.node 97 .nil .nil) (.node 103 .nil .nil)))
    (.node 131 (.node 113 (.node 109 .nil .nil) (.node 127 .nil .nil))
      (.node 139 (.node 137 .nil .nil) (.node 149 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree1_checked : NumberTheory.primeTreeChecked subtree1 := by
  norm_num only [subtree1, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree2 : BinaryTree ℕ :=
  .node 67 subtree0 subtree1

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree2_checked : NumberTheory.primeTreeChecked subtree2 := by
  exact ⟨by norm_num only, subtree0_checked, subtree1_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree3 : BinaryTree ℕ :=
  (.node 197
    (.node 179 (.node 167 (.node 163 (.node 157 .nil .nil) .nil) (.node 173 .nil .nil))
      (.node 191 (.node 181 .nil .nil) (.node 193 .nil .nil)))
    (.node 227 (.node 211 (.node 199 .nil .nil) (.node 223 .nil .nil))
      (.node 233 (.node 229 .nil .nil) (.node 239 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree3_checked : NumberTheory.primeTreeChecked subtree3 := by
  norm_num only [subtree3, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree4 : BinaryTree ℕ :=
  (.node 293
    (.node 271 (.node 263 (.node 257 (.node 251 .nil .nil) .nil) (.node 269 .nil .nil))
      (.node 281 (.node 277 .nil .nil) (.node 283 .nil .nil)))
    (.node 317 (.node 311 (.node 307 .nil .nil) (.node 313 .nil .nil))
      (.node 337 (.node 331 .nil .nil) (.node 347 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree4_checked : NumberTheory.primeTreeChecked subtree4 := by
  norm_num only [subtree4, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree5 : BinaryTree ℕ :=
  .node 241 subtree3 subtree4

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree5_checked : NumberTheory.primeTreeChecked subtree5 := by
  exact ⟨by norm_num only, subtree3_checked, subtree4_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree6 : BinaryTree ℕ :=
  .node 151 subtree2 subtree5

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree6_checked : NumberTheory.primeTreeChecked subtree6 := by
  exact ⟨by norm_num only, subtree2_checked, subtree5_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree7 : BinaryTree ℕ :=
  (.node 401
    (.node 379 (.node 367 (.node 359 (.node 353 .nil .nil) .nil) (.node 373 .nil .nil))
      (.node 389 (.node 383 .nil .nil) (.node 397 .nil .nil)))
    (.node 433 (.node 421 (.node 419 (.node 409 .nil .nil) .nil) (.node 431 .nil .nil))
      (.node 443 (.node 439 .nil .nil) (.node 449 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree7_checked : NumberTheory.primeTreeChecked subtree7 := by
  norm_num only [subtree7, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree8 : BinaryTree ℕ :=
  (.node 509
    (.node 487 (.node 467 (.node 463 (.node 461 .nil .nil) .nil) (.node 479 .nil .nil))
      (.node 499 (.node 491 .nil .nil) (.node 503 .nil .nil)))
    (.node 547 (.node 523 (.node 521 .nil .nil) (.node 541 .nil .nil))
      (.node 563 (.node 557 .nil .nil) (.node 569 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree8_checked : NumberTheory.primeTreeChecked subtree8 := by
  norm_num only [subtree8, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree9 : BinaryTree ℕ :=
  .node 457 subtree7 subtree8

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree9_checked : NumberTheory.primeTreeChecked subtree9 := by
  exact ⟨by norm_num only, subtree7_checked, subtree8_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree10 : BinaryTree ℕ :=
  (.node 619
    (.node 601 (.node 593 (.node 587 (.node 577 .nil .nil) .nil) (.node 599 .nil .nil))
      (.node 613 (.node 607 .nil .nil) (.node 617 .nil .nil)))
    (.node 647 (.node 641 (.node 631 .nil .nil) (.node 643 .nil .nil))
      (.node 659 (.node 653 .nil .nil) (.node 661 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree10_checked : NumberTheory.primeTreeChecked subtree10 := by
  norm_num only [subtree10, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree11 : BinaryTree ℕ :=
  (.node 739
    (.node 709 (.node 691 (.node 683 (.node 677 .nil .nil) .nil) (.node 701 .nil .nil))
      (.node 727 (.node 719 .nil .nil) (.node 733 .nil .nil)))
    (.node 761 (.node 751 (.node 743 .nil .nil) (.node 757 .nil .nil))
      (.node 773 (.node 769 .nil .nil) (.node 787 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree11_checked : NumberTheory.primeTreeChecked subtree11 := by
  norm_num only [subtree11, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree12 : BinaryTree ℕ :=
  .node 673 subtree10 subtree11

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree12_checked : NumberTheory.primeTreeChecked subtree12 := by
  exact ⟨by norm_num only, subtree10_checked, subtree11_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree13 : BinaryTree ℕ :=
  .node 571 subtree9 subtree12

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree13_checked : NumberTheory.primeTreeChecked subtree13 := by
  exact ⟨by norm_num only, subtree9_checked, subtree12_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree14 : BinaryTree ℕ :=
  .node 349 subtree6 subtree13

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree14_checked : NumberTheory.primeTreeChecked subtree14 := by
  exact ⟨by norm_num only, subtree6_checked, subtree13_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree15 : BinaryTree ℕ :=
  (.node 857
    (.node 827 (.node 821 (.node 811 (.node 809 .nil .nil) .nil) (.node 823 .nil .nil))
      (.node 839 (.node 829 .nil .nil) (.node 853 .nil .nil)))
    (.node 883 (.node 877 (.node 863 (.node 859 .nil .nil) .nil) (.node 881 .nil .nil))
      (.node 907 (.node 887 .nil .nil) (.node 911 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree15_checked : NumberTheory.primeTreeChecked subtree15 := by
  norm_num only [subtree15, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree16 : BinaryTree ℕ :=
  (.node 983
    (.node 953 (.node 941 (.node 937 (.node 929 .nil .nil) .nil) (.node 947 .nil .nil))
      (.node 971 (.node 967 .nil .nil) (.node 977 .nil .nil)))
    (.node 1013 (.node 997 (.node 991 .nil .nil) (.node 1009 .nil .nil))
      (.node 1021 (.node 1019 .nil .nil) (.node 1031 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree16_checked : NumberTheory.primeTreeChecked subtree16 := by
  norm_num only [subtree16, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree17 : BinaryTree ℕ :=
  .node 919 subtree15 subtree16

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree17_checked : NumberTheory.primeTreeChecked subtree17 := by
  exact ⟨by norm_num only, subtree15_checked, subtree16_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree18 : BinaryTree ℕ :=
  (.node 1093
    (.node 1063 (.node 1051 (.node 1049 (.node 1039 .nil .nil) .nil) (.node 1061 .nil .nil))
      (.node 1087 (.node 1069 .nil .nil) (.node 1091 .nil .nil)))
    (.node 1117 (.node 1103 (.node 1097 .nil .nil) (.node 1109 .nil .nil))
      (.node 1129 (.node 1123 .nil .nil) (.node 1151 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree18_checked : NumberTheory.primeTreeChecked subtree18 := by
  norm_num only [subtree18, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree19 : BinaryTree ℕ :=
  (.node 1223
    (.node 1193 (.node 1181 (.node 1171 (.node 1163 .nil .nil) .nil) (.node 1187 .nil .nil))
      (.node 1213 (.node 1201 .nil .nil) (.node 1217 .nil .nil)))
    (.node 1249 (.node 1231 (.node 1229 .nil .nil) (.node 1237 .nil .nil))
      (.node 1277 (.node 1259 .nil .nil) (.node 1279 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree19_checked : NumberTheory.primeTreeChecked subtree19 := by
  norm_num only [subtree19, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree20 : BinaryTree ℕ :=
  .node 1153 subtree18 subtree19

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree20_checked : NumberTheory.primeTreeChecked subtree20 := by
  exact ⟨by norm_num only, subtree18_checked, subtree19_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree21 : BinaryTree ℕ :=
  .node 1033 subtree17 subtree20

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree21_checked : NumberTheory.primeTreeChecked subtree21 := by
  exact ⟨by norm_num only, subtree17_checked, subtree20_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree22 : BinaryTree ℕ :=
  (.node 1327
    (.node 1303 (.node 1297 (.node 1291 (.node 1289 .nil .nil) .nil) (.node 1301 .nil .nil))
      (.node 1319 (.node 1307 .nil .nil) (.node 1321 .nil .nil)))
    (.node 1399 (.node 1373 (.node 1367 (.node 1361 .nil .nil) .nil) (.node 1381 .nil .nil))
      (.node 1423 (.node 1409 .nil .nil) (.node 1427 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree22_checked : NumberTheory.primeTreeChecked subtree22 := by
  norm_num only [subtree22, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree23 : BinaryTree ℕ :=
  (.node 1483
    (.node 1453 (.node 1447 (.node 1439 (.node 1433 .nil .nil) .nil) (.node 1451 .nil .nil))
      (.node 1471 (.node 1459 .nil .nil) (.node 1481 .nil .nil)))
    (.node 1499 (.node 1489 (.node 1487 .nil .nil) (.node 1493 .nil .nil))
      (.node 1523 (.node 1511 .nil .nil) (.node 1531 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree23_checked : NumberTheory.primeTreeChecked subtree23 := by
  norm_num only [subtree23, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree24 : BinaryTree ℕ :=
  .node 1429 subtree22 subtree23

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree24_checked : NumberTheory.primeTreeChecked subtree24 := by
  exact ⟨by norm_num only, subtree22_checked, subtree23_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree25 : BinaryTree ℕ :=
  (.node 1601
    (.node 1571 (.node 1559 (.node 1553 (.node 1549 .nil .nil) .nil) (.node 1567 .nil .nil))
      (.node 1583 (.node 1579 .nil .nil) (.node 1597 .nil .nil)))
    (.node 1619 (.node 1609 (.node 1607 .nil .nil) (.node 1613 .nil .nil))
      (.node 1627 (.node 1621 .nil .nil) (.node 1637 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree25_checked : NumberTheory.primeTreeChecked subtree25 := by
  norm_num only [subtree25, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree26 : BinaryTree ℕ :=
  (.node 1723
    (.node 1697 (.node 1669 (.node 1667 (.node 1663 .nil .nil) .nil) (.node 1693 .nil .nil))
      (.node 1709 (.node 1699 .nil .nil) (.node 1721 .nil .nil)))
    (.node 1753 (.node 1741 (.node 1733 .nil .nil) (.node 1747 .nil .nil))
      (.node 1777 (.node 1759 .nil .nil) (.node 1783 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree26_checked : NumberTheory.primeTreeChecked subtree26 := by
  norm_num only [subtree26, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree27 : BinaryTree ℕ :=
  .node 1657 subtree25 subtree26

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree27_checked : NumberTheory.primeTreeChecked subtree27 := by
  exact ⟨by norm_num only, subtree25_checked, subtree26_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree28 : BinaryTree ℕ :=
  .node 1543 subtree24 subtree27

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree28_checked : NumberTheory.primeTreeChecked subtree28 := by
  exact ⟨by norm_num only, subtree24_checked, subtree27_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree29 : BinaryTree ℕ :=
  .node 1283 subtree21 subtree28

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree29_checked : NumberTheory.primeTreeChecked subtree29 := by
  exact ⟨by norm_num only, subtree21_checked, subtree28_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree30 : BinaryTree ℕ :=
  .node 797 subtree14 subtree29

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree30_checked : NumberTheory.primeTreeChecked subtree30 := by
  exact ⟨by norm_num only, subtree14_checked, subtree29_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree31 : BinaryTree ℕ :=
  (.node 1871
    (.node 1831 (.node 1811 (.node 1801 (.node 1789 .nil .nil) .nil) (.node 1823 .nil .nil))
      (.node 1861 (.node 1847 .nil .nil) (.node 1867 .nil .nil)))
    (.node 1901 (.node 1879 (.node 1877 (.node 1873 .nil .nil) .nil) (.node 1889 .nil .nil))
      (.node 1913 (.node 1907 .nil .nil) (.node 1931 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree31_checked : NumberTheory.primeTreeChecked subtree31 := by
  norm_num only [subtree31, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree32 : BinaryTree ℕ :=
  (.node 2003
    (.node 1987 (.node 1973 (.node 1951 (.node 1949 .nil .nil) .nil) (.node 1979 .nil .nil))
      (.node 1997 (.node 1993 .nil .nil) (.node 1999 .nil .nil)))
    (.node 2029 (.node 2017 (.node 2011 .nil .nil) (.node 2027 .nil .nil))
      (.node 2053 (.node 2039 .nil .nil) (.node 2063 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree32_checked : NumberTheory.primeTreeChecked subtree32 := by
  norm_num only [subtree32, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree33 : BinaryTree ℕ :=
  .node 1933 subtree31 subtree32

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree33_checked : NumberTheory.primeTreeChecked subtree33 := by
  exact ⟨by norm_num only, subtree31_checked, subtree32_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree34 : BinaryTree ℕ :=
  (.node 2131
    (.node 2099 (.node 2087 (.node 2083 (.node 2081 .nil .nil) .nil) (.node 2089 .nil .nil))
      (.node 2113 (.node 2111 .nil .nil) (.node 2129 .nil .nil)))
    (.node 2153 (.node 2141 (.node 2137 .nil .nil) (.node 2143 .nil .nil))
      (.node 2179 (.node 2161 .nil .nil) (.node 2203 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree34_checked : NumberTheory.primeTreeChecked subtree34 := by
  norm_num only [subtree34, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree35 : BinaryTree ℕ :=
  (.node 2273
    (.node 2243 (.node 2237 (.node 2221 (.node 2213 .nil .nil) .nil) (.node 2239 .nil .nil))
      (.node 2267 (.node 2251 .nil .nil) (.node 2269 .nil .nil)))
    (.node 2297 (.node 2287 (.node 2281 .nil .nil) (.node 2293 .nil .nil))
      (.node 2311 (.node 2309 .nil .nil) (.node 2333 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree35_checked : NumberTheory.primeTreeChecked subtree35 := by
  norm_num only [subtree35, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree36 : BinaryTree ℕ :=
  .node 2207 subtree34 subtree35

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree36_checked : NumberTheory.primeTreeChecked subtree36 := by
  exact ⟨by norm_num only, subtree34_checked, subtree35_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree37 : BinaryTree ℕ :=
  .node 2069 subtree33 subtree36

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree37_checked : NumberTheory.primeTreeChecked subtree37 := by
  exact ⟨by norm_num only, subtree33_checked, subtree36_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree38 : BinaryTree ℕ :=
  (.node 2389
    (.node 2371 (.node 2351 (.node 2347 (.node 2341 .nil .nil) .nil) (.node 2357 .nil .nil))
      (.node 2381 (.node 2377 .nil .nil) (.node 2383 .nil .nil)))
    (.node 2423 (.node 2411 (.node 2399 (.node 2393 .nil .nil) .nil) (.node 2417 .nil .nil))
      (.node 2441 (.node 2437 .nil .nil) (.node 2447 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree38_checked : NumberTheory.primeTreeChecked subtree38 := by
  norm_num only [subtree38, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree39 : BinaryTree ℕ :=
  (.node 2549
    (.node 2521 (.node 2477 (.node 2473 (.node 2467 .nil .nil) .nil) (.node 2503 .nil .nil))
      (.node 2539 (.node 2531 .nil .nil) (.node 2543 .nil .nil)))
    (.node 2591 (.node 2557 (.node 2551 .nil .nil) (.node 2579 .nil .nil))
      (.node 2609 (.node 2593 .nil .nil) (.node 2617 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree39_checked : NumberTheory.primeTreeChecked subtree39 := by
  norm_num only [subtree39, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree40 : BinaryTree ℕ :=
  .node 2459 subtree38 subtree39

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree40_checked : NumberTheory.primeTreeChecked subtree40 := by
  exact ⟨by norm_num only, subtree38_checked, subtree39_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree41 : BinaryTree ℕ :=
  (.node 2687
    (.node 2663 (.node 2657 (.node 2647 (.node 2633 .nil .nil) .nil) (.node 2659 .nil .nil))
      (.node 2677 (.node 2671 .nil .nil) (.node 2683 .nil .nil)))
    (.node 2707 (.node 2693 (.node 2689 .nil .nil) (.node 2699 .nil .nil))
      (.node 2713 (.node 2711 .nil .nil) (.node 2719 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree41_checked : NumberTheory.primeTreeChecked subtree41 := by
  norm_num only [subtree41, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree42 : BinaryTree ℕ :=
  (.node 2797
    (.node 2767 (.node 2749 (.node 2741 (.node 2731 .nil .nil) .nil) (.node 2753 .nil .nil))
      (.node 2789 (.node 2777 .nil .nil) (.node 2791 .nil .nil)))
    (.node 2833 (.node 2803 (.node 2801 .nil .nil) (.node 2819 .nil .nil))
      (.node 2843 (.node 2837 .nil .nil) (.node 2851 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree42_checked : NumberTheory.primeTreeChecked subtree42 := by
  norm_num only [subtree42, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree43 : BinaryTree ℕ :=
  .node 2729 subtree41 subtree42

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree43_checked : NumberTheory.primeTreeChecked subtree43 := by
  exact ⟨by norm_num only, subtree41_checked, subtree42_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree44 : BinaryTree ℕ :=
  .node 2621 subtree40 subtree43

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree44_checked : NumberTheory.primeTreeChecked subtree44 := by
  exact ⟨by norm_num only, subtree40_checked, subtree43_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree45 : BinaryTree ℕ :=
  .node 2339 subtree37 subtree44

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree45_checked : NumberTheory.primeTreeChecked subtree45 := by
  exact ⟨by norm_num only, subtree37_checked, subtree44_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree46 : BinaryTree ℕ :=
  (.node 2939
    (.node 2903 (.node 2887 (.node 2879 (.node 2861 .nil .nil) .nil) (.node 2897 .nil .nil))
      (.node 2917 (.node 2909 .nil .nil) (.node 2927 .nil .nil)))
    (.node 2971 (.node 2963 (.node 2957 (.node 2953 .nil .nil) .nil) (.node 2969 .nil .nil))
      (.node 3001 (.node 2999 .nil .nil) (.node 3011 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree46_checked : NumberTheory.primeTreeChecked subtree46 := by
  norm_num only [subtree46, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree47 : BinaryTree ℕ :=
  (.node 3089
    (.node 3061 (.node 3041 (.node 3037 (.node 3023 .nil .nil) .nil) (.node 3049 .nil .nil))
      (.node 3079 (.node 3067 .nil .nil) (.node 3083 .nil .nil)))
    (.node 3137 (.node 3119 (.node 3109 .nil .nil) (.node 3121 .nil .nil))
      (.node 3167 (.node 3163 .nil .nil) (.node 3169 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree47_checked : NumberTheory.primeTreeChecked subtree47 := by
  norm_num only [subtree47, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree48 : BinaryTree ℕ :=
  .node 3019 subtree46 subtree47

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree48_checked : NumberTheory.primeTreeChecked subtree48 := by
  exact ⟨by norm_num only, subtree46_checked, subtree47_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree49 : BinaryTree ℕ :=
  (.node 3253
    (.node 3217 (.node 3203 (.node 3191 (.node 3187 .nil .nil) .nil) (.node 3209 .nil .nil))
      (.node 3229 (.node 3221 .nil .nil) (.node 3251 .nil .nil)))
    (.node 3299 (.node 3259 (.node 3257 .nil .nil) (.node 3271 .nil .nil))
      (.node 3307 (.node 3301 .nil .nil) (.node 3313 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree49_checked : NumberTheory.primeTreeChecked subtree49 := by
  norm_num only [subtree49, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree50 : BinaryTree ℕ :=
  (.node 3373
    (.node 3347 (.node 3331 (.node 3329 (.node 3323 .nil .nil) .nil) (.node 3343 .nil .nil))
      (.node 3361 (.node 3359 .nil .nil) (.node 3371 .nil .nil)))
    (.node 3413 (.node 3391 (.node 3389 .nil .nil) (.node 3407 .nil .nil))
      (.node 3449 (.node 3433 .nil .nil) (.node 3457 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree50_checked : NumberTheory.primeTreeChecked subtree50 := by
  norm_num only [subtree50, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree51 : BinaryTree ℕ :=
  .node 3319 subtree49 subtree50

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree51_checked : NumberTheory.primeTreeChecked subtree51 := by
  exact ⟨by norm_num only, subtree49_checked, subtree50_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree52 : BinaryTree ℕ :=
  .node 3181 subtree48 subtree51

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree52_checked : NumberTheory.primeTreeChecked subtree52 := by
  exact ⟨by norm_num only, subtree48_checked, subtree51_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree53 : BinaryTree ℕ :=
  (.node 3529
    (.node 3499 (.node 3469 (.node 3467 (.node 3463 .nil .nil) .nil) (.node 3491 .nil .nil))
      (.node 3517 (.node 3511 .nil .nil) (.node 3527 .nil .nil)))
    (.node 3557 (.node 3541 (.node 3539 (.node 3533 .nil .nil) .nil) (.node 3547 .nil .nil))
      (.node 3571 (.node 3559 .nil .nil) (.node 3581 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree53_checked : NumberTheory.primeTreeChecked subtree53 := by
  norm_num only [subtree53, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree54 : BinaryTree ℕ :=
  (.node 3659
    (.node 3623 (.node 3613 (.node 3607 (.node 3593 .nil .nil) .nil) (.node 3617 .nil .nil))
      (.node 3637 (.node 3631 .nil .nil) (.node 3643 .nil .nil)))
    (.node 3691 (.node 3673 (.node 3671 .nil .nil) (.node 3677 .nil .nil))
      (.node 3701 (.node 3697 .nil .nil) (.node 3709 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree54_checked : NumberTheory.primeTreeChecked subtree54 := by
  norm_num only [subtree54, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree55 : BinaryTree ℕ :=
  .node 3583 subtree53 subtree54

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree55_checked : NumberTheory.primeTreeChecked subtree55 := by
  exact ⟨by norm_num only, subtree53_checked, subtree54_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree56 : BinaryTree ℕ :=
  (.node 3797
    (.node 3767 (.node 3739 (.node 3733 (.node 3727 .nil .nil) .nil) (.node 3761 .nil .nil))
      (.node 3779 (.node 3769 .nil .nil) (.node 3793 .nil .nil)))
    (.node 3833 (.node 3821 (.node 3803 .nil .nil) (.node 3823 .nil .nil))
      (.node 3851 (.node 3847 .nil .nil) (.node 3853 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree56_checked : NumberTheory.primeTreeChecked subtree56 := by
  norm_num only [subtree56, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree57 : BinaryTree ℕ :=
  (.node 3929
    (.node 3911 (.node 3889 (.node 3881 (.node 3877 .nil .nil) .nil) (.node 3907 .nil .nil))
      (.node 3919 (.node 3917 .nil .nil) (.node 3923 .nil .nil)))
    (.node 3967 (.node 3943 (.node 3931 .nil .nil) (.node 3947 .nil .nil))
      (.node 4001 (.node 3989 .nil .nil) (.node 4003 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree57_checked : NumberTheory.primeTreeChecked subtree57 := by
  norm_num only [subtree57, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree58 : BinaryTree ℕ :=
  .node 3863 subtree56 subtree57

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree58_checked : NumberTheory.primeTreeChecked subtree58 := by
  exact ⟨by norm_num only, subtree56_checked, subtree57_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree59 : BinaryTree ℕ :=
  .node 3719 subtree55 subtree58

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree59_checked : NumberTheory.primeTreeChecked subtree59 := by
  exact ⟨by norm_num only, subtree55_checked, subtree58_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree60 : BinaryTree ℕ :=
  .node 3461 subtree52 subtree59

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree60_checked : NumberTheory.primeTreeChecked subtree60 := by
  exact ⟨by norm_num only, subtree52_checked, subtree59_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree61 : BinaryTree ℕ :=
  .node 2857 subtree45 subtree60

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree61_checked : NumberTheory.primeTreeChecked subtree61 := by
  exact ⟨by norm_num only, subtree45_checked, subtree60_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree62 : BinaryTree ℕ :=
  .node 1787 subtree30 subtree61

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree62_checked : NumberTheory.primeTreeChecked subtree62 := by
  exact ⟨by norm_num only, subtree30_checked, subtree61_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree63 : BinaryTree ℕ :=
  (.node 4079
    (.node 4049 (.node 4021 (.node 4019 (.node 4013 .nil .nil) .nil) (.node 4027 .nil .nil))
      (.node 4057 (.node 4051 .nil .nil) (.node 4073 .nil .nil)))
    (.node 4127 (.node 4099 (.node 4093 (.node 4091 .nil .nil) .nil) (.node 4111 .nil .nil))
      (.node 4133 (.node 4129 .nil .nil) (.node 4139 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree63_checked : NumberTheory.primeTreeChecked subtree63 := by
  norm_num only [subtree63, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree64 : BinaryTree ℕ :=
  (.node 4231
    (.node 4211 (.node 4177 (.node 4159 (.node 4157 .nil .nil) .nil) (.node 4201 .nil .nil))
      (.node 4219 (.node 4217 .nil .nil) (.node 4229 .nil .nil)))
    (.node 4259 (.node 4243 (.node 4241 .nil .nil) (.node 4253 .nil .nil))
      (.node 4271 (.node 4261 .nil .nil) (.node 4273 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree64_checked : NumberTheory.primeTreeChecked subtree64 := by
  norm_num only [subtree64, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree65 : BinaryTree ℕ :=
  .node 4153 subtree63 subtree64

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree65_checked : NumberTheory.primeTreeChecked subtree65 := by
  exact ⟨by norm_num only, subtree63_checked, subtree64_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree66 : BinaryTree ℕ :=
  (.node 4373
    (.node 4339 (.node 4327 (.node 4297 (.node 4289 .nil .nil) .nil) (.node 4337 .nil .nil))
      (.node 4357 (.node 4349 .nil .nil) (.node 4363 .nil .nil)))
    (.node 4421 (.node 4397 (.node 4391 .nil .nil) (.node 4409 .nil .nil))
      (.node 4441 (.node 4423 .nil .nil) (.node 4447 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree66_checked : NumberTheory.primeTreeChecked subtree66 := by
  norm_num only [subtree66, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree67 : BinaryTree ℕ :=
  (.node 4519
    (.node 4493 (.node 4481 (.node 4463 (.node 4457 .nil .nil) .nil) (.node 4483 .nil .nil))
      (.node 4513 (.node 4507 .nil .nil) (.node 4517 .nil .nil)))
    (.node 4561 (.node 4547 (.node 4523 .nil .nil) (.node 4549 .nil .nil))
      (.node 4583 (.node 4567 .nil .nil) (.node 4591 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree67_checked : NumberTheory.primeTreeChecked subtree67 := by
  norm_num only [subtree67, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree68 : BinaryTree ℕ :=
  .node 4451 subtree66 subtree67

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree68_checked : NumberTheory.primeTreeChecked subtree68 := by
  exact ⟨by norm_num only, subtree66_checked, subtree67_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree69 : BinaryTree ℕ :=
  .node 4283 subtree65 subtree68

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree69_checked : NumberTheory.primeTreeChecked subtree69 := by
  exact ⟨by norm_num only, subtree65_checked, subtree68_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree70 : BinaryTree ℕ :=
  (.node 4663
    (.node 4643 (.node 4637 (.node 4621 (.node 4603 .nil .nil) .nil) (.node 4639 .nil .nil))
      (.node 4651 (.node 4649 .nil .nil) (.node 4657 .nil .nil)))
    (.node 4721 (.node 4691 (.node 4679 (.node 4673 .nil .nil) .nil) (.node 4703 .nil .nil))
      (.node 4729 (.node 4723 .nil .nil) (.node 4733 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree70_checked : NumberTheory.primeTreeChecked subtree70 := by
  norm_num only [subtree70, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree71 : BinaryTree ℕ :=
  (.node 4817
    (.node 4793 (.node 4787 (.node 4783 (.node 4759 .nil .nil) .nil) (.node 4789 .nil .nil))
      (.node 4801 (.node 4799 .nil .nil) (.node 4813 .nil .nil)))
    (.node 4877 (.node 4861 (.node 4831 .nil .nil) (.node 4871 .nil .nil))
      (.node 4903 (.node 4889 .nil .nil) (.node 4909 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree71_checked : NumberTheory.primeTreeChecked subtree71 := by
  norm_num only [subtree71, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree72 : BinaryTree ℕ :=
  .node 4751 subtree70 subtree71

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree72_checked : NumberTheory.primeTreeChecked subtree72 := by
  exact ⟨by norm_num only, subtree70_checked, subtree71_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree73 : BinaryTree ℕ :=
  (.node 4973
    (.node 4951 (.node 4937 (.node 4933 (.node 4931 .nil .nil) .nil) (.node 4943 .nil .nil))
      (.node 4967 (.node 4957 .nil .nil) (.node 4969 .nil .nil)))
    (.node 5003 (.node 4993 (.node 4987 .nil .nil) (.node 4999 .nil .nil))
      (.node 5011 (.node 5009 .nil .nil) (.node 5021 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree73_checked : NumberTheory.primeTreeChecked subtree73 := by
  norm_num only [subtree73, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree74 : BinaryTree ℕ :=
  (.node 5107
    (.node 5081 (.node 5059 (.node 5051 (.node 5039 .nil .nil) .nil) (.node 5077 .nil .nil))
      (.node 5099 (.node 5087 .nil .nil) (.node 5101 .nil .nil)))
    (.node 5153 (.node 5119 (.node 5113 .nil .nil) (.node 5147 .nil .nil))
      (.node 5171 (.node 5167 .nil .nil) (.node 5179 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree74_checked : NumberTheory.primeTreeChecked subtree74 := by
  norm_num only [subtree74, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree75 : BinaryTree ℕ :=
  .node 5023 subtree73 subtree74

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree75_checked : NumberTheory.primeTreeChecked subtree75 := by
  exact ⟨by norm_num only, subtree73_checked, subtree74_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree76 : BinaryTree ℕ :=
  .node 4919 subtree72 subtree75

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree76_checked : NumberTheory.primeTreeChecked subtree76 := by
  exact ⟨by norm_num only, subtree72_checked, subtree75_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree77 : BinaryTree ℕ :=
  .node 4597 subtree69 subtree76

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree77_checked : NumberTheory.primeTreeChecked subtree77 := by
  exact ⟨by norm_num only, subtree69_checked, subtree76_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree78 : BinaryTree ℕ :=
  (.node 5279
    (.node 5233 (.node 5227 (.node 5209 (.node 5197 .nil .nil) .nil) (.node 5231 .nil .nil))
      (.node 5261 (.node 5237 .nil .nil) (.node 5273 .nil .nil)))
    (.node 5323 (.node 5303 (.node 5297 (.node 5281 .nil .nil) .nil) (.node 5309 .nil .nil))
      (.node 5347 (.node 5333 .nil .nil) (.node 5351 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree78_checked : NumberTheory.primeTreeChecked subtree78 := by
  norm_num only [subtree78, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree79 : BinaryTree ℕ :=
  (.node 5437
    (.node 5413 (.node 5399 (.node 5393 (.node 5387 .nil .nil) .nil) (.node 5407 .nil .nil))
      (.node 5419 (.node 5417 .nil .nil) (.node 5431 .nil .nil)))
    (.node 5471 (.node 5443 (.node 5441 .nil .nil) (.node 5449 .nil .nil))
      (.node 5479 (.node 5477 .nil .nil) (.node 5483 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree79_checked : NumberTheory.primeTreeChecked subtree79 := by
  norm_num only [subtree79, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree80 : BinaryTree ℕ :=
  .node 5381 subtree78 subtree79

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree80_checked : NumberTheory.primeTreeChecked subtree80 := by
  exact ⟨by norm_num only, subtree78_checked, subtree79_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree81 : BinaryTree ℕ :=
  (.node 5569
    (.node 5527 (.node 5519 (.node 5507 (.node 5503 .nil .nil) .nil) (.node 5521 .nil .nil))
      (.node 5557 (.node 5531 .nil .nil) (.node 5563 .nil .nil)))
    (.node 5623 (.node 5581 (.node 5573 .nil .nil) (.node 5591 .nil .nil))
      (.node 5641 (.node 5639 .nil .nil) (.node 5647 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree81_checked : NumberTheory.primeTreeChecked subtree81 := by
  norm_num only [subtree81, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree82 : BinaryTree ℕ :=
  (.node 5711
    (.node 5683 (.node 5659 (.node 5657 (.node 5653 .nil .nil) .nil) (.node 5669 .nil .nil))
      (.node 5693 (.node 5689 .nil .nil) (.node 5701 .nil .nil)))
    (.node 5743 (.node 5737 (.node 5717 .nil .nil) (.node 5741 .nil .nil))
      (.node 5779 (.node 5749 .nil .nil) (.node 5783 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree82_checked : NumberTheory.primeTreeChecked subtree82 := by
  norm_num only [subtree82, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree83 : BinaryTree ℕ :=
  .node 5651 subtree81 subtree82

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree83_checked : NumberTheory.primeTreeChecked subtree83 := by
  exact ⟨by norm_num only, subtree81_checked, subtree82_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree84 : BinaryTree ℕ :=
  .node 5501 subtree80 subtree83

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree84_checked : NumberTheory.primeTreeChecked subtree84 := by
  exact ⟨by norm_num only, subtree80_checked, subtree83_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree85 : BinaryTree ℕ :=
  (.node 5851
    (.node 5827 (.node 5813 (.node 5807 (.node 5801 .nil .nil) .nil) (.node 5821 .nil .nil))
      (.node 5843 (.node 5839 .nil .nil) (.node 5849 .nil .nil)))
    (.node 5879 (.node 5867 (.node 5861 (.node 5857 .nil .nil) .nil) (.node 5869 .nil .nil))
      (.node 5897 (.node 5881 .nil .nil) (.node 5903 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree85_checked : NumberTheory.primeTreeChecked subtree85 := by
  norm_num only [subtree85, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree86 : BinaryTree ℕ :=
  (.node 6037
    (.node 5987 (.node 5953 (.node 5939 (.node 5927 .nil .nil) .nil) (.node 5981 .nil .nil))
      (.node 6011 (.node 6007 .nil .nil) (.node 6029 .nil .nil)))
    (.node 6067 (.node 6047 (.node 6043 .nil .nil) (.node 6053 .nil .nil))
      (.node 6079 (.node 6073 .nil .nil) (.node 6089 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree86_checked : NumberTheory.primeTreeChecked subtree86 := by
  norm_num only [subtree86, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree87 : BinaryTree ℕ :=
  .node 5923 subtree85 subtree86

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree87_checked : NumberTheory.primeTreeChecked subtree87 := by
  exact ⟨by norm_num only, subtree85_checked, subtree86_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree88 : BinaryTree ℕ :=
  (.node 6173
    (.node 6133 (.node 6121 (.node 6113 (.node 6101 .nil .nil) .nil) (.node 6131 .nil .nil))
      (.node 6151 (.node 6143 .nil .nil) (.node 6163 .nil .nil)))
    (.node 6211 (.node 6199 (.node 6197 .nil .nil) (.node 6203 .nil .nil))
      (.node 6221 (.node 6217 .nil .nil) (.node 6229 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree88_checked : NumberTheory.primeTreeChecked subtree88 := by
  norm_num only [subtree88, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree89 : BinaryTree ℕ :=
  (.node 6311
    (.node 6277 (.node 6269 (.node 6263 (.node 6257 .nil .nil) .nil) (.node 6271 .nil .nil))
      (.node 6299 (.node 6287 .nil .nil) (.node 6301 .nil .nil)))
    (.node 6337 (.node 6323 (.node 6317 .nil .nil) (.node 6329 .nil .nil))
      (.node 6353 (.node 6343 .nil .nil) (.node 6359 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree89_checked : NumberTheory.primeTreeChecked subtree89 := by
  norm_num only [subtree89, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree90 : BinaryTree ℕ :=
  .node 6247 subtree88 subtree89

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree90_checked : NumberTheory.primeTreeChecked subtree90 := by
  exact ⟨by norm_num only, subtree88_checked, subtree89_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree91 : BinaryTree ℕ :=
  .node 6091 subtree87 subtree90

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree91_checked : NumberTheory.primeTreeChecked subtree91 := by
  exact ⟨by norm_num only, subtree87_checked, subtree90_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree92 : BinaryTree ℕ :=
  .node 5791 subtree84 subtree91

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree92_checked : NumberTheory.primeTreeChecked subtree92 := by
  exact ⟨by norm_num only, subtree84_checked, subtree91_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree93 : BinaryTree ℕ :=
  .node 5189 subtree77 subtree92

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree93_checked : NumberTheory.primeTreeChecked subtree93 := by
  exact ⟨by norm_num only, subtree77_checked, subtree92_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree94 : BinaryTree ℕ :=
  (.node 6451
    (.node 6397 (.node 6379 (.node 6373 (.node 6367 .nil .nil) .nil) (.node 6389 .nil .nil))
      (.node 6427 (.node 6421 .nil .nil) (.node 6449 .nil .nil)))
    (.node 6521 (.node 6481 (.node 6473 (.node 6469 .nil .nil) .nil) (.node 6491 .nil .nil))
      (.node 6547 (.node 6529 .nil .nil) (.node 6551 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree94_checked : NumberTheory.primeTreeChecked subtree94 := by
  norm_num only [subtree94, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree95 : BinaryTree ℕ :=
  (.node 6637
    (.node 6581 (.node 6571 (.node 6569 (.node 6563 .nil .nil) .nil) (.node 6577 .nil .nil))
      (.node 6607 (.node 6599 .nil .nil) (.node 6619 .nil .nil)))
    (.node 6673 (.node 6659 (.node 6653 .nil .nil) (.node 6661 .nil .nil))
      (.node 6689 (.node 6679 .nil .nil) (.node 6691 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree95_checked : NumberTheory.primeTreeChecked subtree95 := by
  norm_num only [subtree95, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree96 : BinaryTree ℕ :=
  .node 6553 subtree94 subtree95

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree96_checked : NumberTheory.primeTreeChecked subtree96 := by
  exact ⟨by norm_num only, subtree94_checked, subtree95_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree97 : BinaryTree ℕ :=
  (.node 6781
    (.node 6737 (.node 6719 (.node 6709 (.node 6703 .nil .nil) .nil) (.node 6733 .nil .nil))
      (.node 6763 (.node 6761 .nil .nil) (.node 6779 .nil .nil)))
    (.node 6823 (.node 6793 (.node 6791 .nil .nil) (.node 6803 .nil .nil))
      (.node 6829 (.node 6827 .nil .nil) (.node 6833 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree97_checked : NumberTheory.primeTreeChecked subtree97 := by
  norm_num only [subtree97, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree98 : BinaryTree ℕ :=
  (.node 6917
    (.node 6883 (.node 6869 (.node 6863 (.node 6857 .nil .nil) .nil) (.node 6871 .nil .nil))
      (.node 6907 (.node 6899 .nil .nil) (.node 6911 .nil .nil)))
    (.node 6961 (.node 6949 (.node 6947 .nil .nil) (.node 6959 .nil .nil))
      (.node 6971 (.node 6967 .nil .nil) (.node 6977 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree98_checked : NumberTheory.primeTreeChecked subtree98 := by
  norm_num only [subtree98, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree99 : BinaryTree ℕ :=
  .node 6841 subtree97 subtree98

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree99_checked : NumberTheory.primeTreeChecked subtree99 := by
  exact ⟨by norm_num only, subtree97_checked, subtree98_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree100 : BinaryTree ℕ :=
  .node 6701 subtree96 subtree99

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree100_checked : NumberTheory.primeTreeChecked subtree100 := by
  exact ⟨by norm_num only, subtree96_checked, subtree99_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree101 : BinaryTree ℕ :=
  (.node 7057
    (.node 7019 (.node 7001 (.node 6997 (.node 6991 .nil .nil) .nil) (.node 7013 .nil .nil))
      (.node 7039 (.node 7027 .nil .nil) (.node 7043 .nil .nil)))
    (.node 7121 (.node 7103 (.node 7079 (.node 7069 .nil .nil) .nil) (.node 7109 .nil .nil))
      (.node 7129 (.node 7127 .nil .nil) (.node 7151 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree101_checked : NumberTheory.primeTreeChecked subtree101 := by
  norm_num only [subtree101, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree102 : BinaryTree ℕ :=
  (.node 7237
    (.node 7211 (.node 7193 (.node 7187 (.node 7177 .nil .nil) .nil) (.node 7207 .nil .nil))
      (.node 7219 (.node 7213 .nil .nil) (.node 7229 .nil .nil)))
    (.node 7283 (.node 7247 (.node 7243 .nil .nil) (.node 7253 .nil .nil))
      (.node 7307 (.node 7297 .nil .nil) (.node 7309 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree102_checked : NumberTheory.primeTreeChecked subtree102 := by
  norm_num only [subtree102, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree103 : BinaryTree ℕ :=
  .node 7159 subtree101 subtree102

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree103_checked : NumberTheory.primeTreeChecked subtree103 := by
  exact ⟨by norm_num only, subtree101_checked, subtree102_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree104 : BinaryTree ℕ :=
  (.node 7433
    (.node 7369 (.node 7349 (.node 7333 (.node 7331 .nil .nil) .nil) (.node 7351 .nil .nil))
      (.node 7411 (.node 7393 .nil .nil) (.node 7417 .nil .nil)))
    (.node 7477 (.node 7457 (.node 7451 .nil .nil) (.node 7459 .nil .nil))
      (.node 7487 (.node 7481 .nil .nil) (.node 7489 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree104_checked : NumberTheory.primeTreeChecked subtree104 := by
  norm_num only [subtree104, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree105 : BinaryTree ℕ :=
  (.node 7559
    (.node 7537 (.node 7523 (.node 7517 (.node 7507 .nil .nil) .nil) (.node 7529 .nil .nil))
      (.node 7547 (.node 7541 .nil .nil) (.node 7549 .nil .nil)))
    (.node 7583 (.node 7573 (.node 7561 .nil .nil) (.node 7577 .nil .nil))
      (.node 7591 (.node 7589 .nil .nil) (.node 7603 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree105_checked : NumberTheory.primeTreeChecked subtree105 := by
  norm_num only [subtree105, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree106 : BinaryTree ℕ :=
  .node 7499 subtree104 subtree105

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree106_checked : NumberTheory.primeTreeChecked subtree106 := by
  exact ⟨by norm_num only, subtree104_checked, subtree105_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree107 : BinaryTree ℕ :=
  .node 7321 subtree103 subtree106

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree107_checked : NumberTheory.primeTreeChecked subtree107 := by
  exact ⟨by norm_num only, subtree103_checked, subtree106_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree108 : BinaryTree ℕ :=
  .node 6983 subtree100 subtree107

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree108_checked : NumberTheory.primeTreeChecked subtree108 := by
  exact ⟨by norm_num only, subtree100_checked, subtree107_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree109 : BinaryTree ℕ :=
  (.node 7691
    (.node 7669 (.node 7643 (.node 7639 (.node 7621 .nil .nil) .nil) (.node 7649 .nil .nil))
      (.node 7681 (.node 7673 .nil .nil) (.node 7687 .nil .nil)))
    (.node 7727 (.node 7717 (.node 7703 (.node 7699 .nil .nil) .nil) (.node 7723 .nil .nil))
      (.node 7753 (.node 7741 .nil .nil) (.node 7757 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree109_checked : NumberTheory.primeTreeChecked subtree109 := by
  norm_num only [subtree109, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree110 : BinaryTree ℕ :=
  (.node 7873
    (.node 7829 (.node 7817 (.node 7793 (.node 7789 .nil .nil) .nil) (.node 7823 .nil .nil))
      (.node 7853 (.node 7841 .nil .nil) (.node 7867 .nil .nil)))
    (.node 7901 (.node 7879 (.node 7877 .nil .nil) (.node 7883 .nil .nil))
      (.node 7919 (.node 7907 .nil .nil) (.node 7927 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree110_checked : NumberTheory.primeTreeChecked subtree110 := by
  norm_num only [subtree110, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree111 : BinaryTree ℕ :=
  .node 7759 subtree109 subtree110

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree111_checked : NumberTheory.primeTreeChecked subtree111 := by
  exact ⟨by norm_num only, subtree109_checked, subtree110_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree112 : BinaryTree ℕ :=
  (.node 8039
    (.node 7993 (.node 7951 (.node 7949 (.node 7937 .nil .nil) .nil) (.node 7963 .nil .nil))
      (.node 8011 (.node 8009 .nil .nil) (.node 8017 .nil .nil)))
    (.node 8081 (.node 8059 (.node 8053 .nil .nil) (.node 8069 .nil .nil))
      (.node 8089 (.node 8087 .nil .nil) (.node 8093 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree112_checked : NumberTheory.primeTreeChecked subtree112 := by
  norm_num only [subtree112, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree113 : BinaryTree ℕ :=
  (.node 8191
    (.node 8161 (.node 8123 (.node 8117 (.node 8111 .nil .nil) .nil) (.node 8147 .nil .nil))
      (.node 8171 (.node 8167 .nil .nil) (.node 8179 .nil .nil)))
    (.node 8231 (.node 8219 (.node 8209 .nil .nil) (.node 8221 .nil .nil))
      (.node 8237 (.node 8233 .nil .nil) (.node 8243 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree113_checked : NumberTheory.primeTreeChecked subtree113 := by
  norm_num only [subtree113, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree114 : BinaryTree ℕ :=
  .node 8101 subtree112 subtree113

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree114_checked : NumberTheory.primeTreeChecked subtree114 := by
  exact ⟨by norm_num only, subtree112_checked, subtree113_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree115 : BinaryTree ℕ :=
  .node 7933 subtree111 subtree114

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree115_checked : NumberTheory.primeTreeChecked subtree115 := by
  exact ⟨by norm_num only, subtree111_checked, subtree114_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree116 : BinaryTree ℕ :=
  (.node 8329
    (.node 8293 (.node 8287 (.node 8273 (.node 8269 .nil .nil) .nil) (.node 8291 .nil .nil))
      (.node 8311 (.node 8297 .nil .nil) (.node 8317 .nil .nil)))
    (.node 8387 (.node 8369 (.node 8363 (.node 8353 .nil .nil) .nil) (.node 8377 .nil .nil))
      (.node 8419 (.node 8389 .nil .nil) (.node 8423 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree116_checked : NumberTheory.primeTreeChecked subtree116 := by
  norm_num only [subtree116, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree117 : BinaryTree ℕ :=
  (.node 8527
    (.node 8467 (.node 8447 (.node 8443 (.node 8431 .nil .nil) .nil) (.node 8461 .nil .nil))
      (.node 8513 (.node 8501 .nil .nil) (.node 8521 .nil .nil)))
    (.node 8563 (.node 8539 (.node 8537 .nil .nil) (.node 8543 .nil .nil))
      (.node 8581 (.node 8573 .nil .nil) (.node 8597 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree117_checked : NumberTheory.primeTreeChecked subtree117 := by
  norm_num only [subtree117, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree118 : BinaryTree ℕ :=
  .node 8429 subtree116 subtree117

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree118_checked : NumberTheory.primeTreeChecked subtree118 := by
  exact ⟨by norm_num only, subtree116_checked, subtree117_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree119 : BinaryTree ℕ :=
  (.node 8677
    (.node 8641 (.node 8627 (.node 8623 (.node 8609 .nil .nil) .nil) (.node 8629 .nil .nil))
      (.node 8663 (.node 8647 .nil .nil) (.node 8669 .nil .nil)))
    (.node 8699 (.node 8689 (.node 8681 .nil .nil) (.node 8693 .nil .nil))
      (.node 8713 (.node 8707 .nil .nil) (.node 8719 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree119_checked : NumberTheory.primeTreeChecked subtree119 := by
  norm_num only [subtree119, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree120 : BinaryTree ℕ :=
  (.node 8807
    (.node 8761 (.node 8747 (.node 8741 (.node 8737 .nil .nil) .nil) (.node 8753 .nil .nil))
      (.node 8783 (.node 8779 .nil .nil) (.node 8803 .nil .nil)))
    (.node 8837 (.node 8821 (.node 8819 .nil .nil) (.node 8831 .nil .nil))
      (.node 8849 (.node 8839 .nil .nil) (.node 8861 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree120_checked : NumberTheory.primeTreeChecked subtree120 := by
  norm_num only [subtree120, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree121 : BinaryTree ℕ :=
  .node 8731 subtree119 subtree120

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree121_checked : NumberTheory.primeTreeChecked subtree121 := by
  exact ⟨by norm_num only, subtree119_checked, subtree120_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree122 : BinaryTree ℕ :=
  .node 8599 subtree118 subtree121

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree122_checked : NumberTheory.primeTreeChecked subtree122 := by
  exact ⟨by norm_num only, subtree118_checked, subtree121_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree123 : BinaryTree ℕ :=
  .node 8263 subtree115 subtree122

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree123_checked : NumberTheory.primeTreeChecked subtree123 := by
  exact ⟨by norm_num only, subtree115_checked, subtree122_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree124 : BinaryTree ℕ :=
  .node 7607 subtree108 subtree123

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree124_checked : NumberTheory.primeTreeChecked subtree124 := by
  exact ⟨by norm_num only, subtree108_checked, subtree123_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree125 : BinaryTree ℕ :=
  .node 6361 subtree93 subtree124

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree125_checked : NumberTheory.primeTreeChecked subtree125 := by
  exact ⟨by norm_num only, subtree93_checked, subtree124_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree126 : BinaryTree ℕ :=
  .node 4007 subtree62 subtree125

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree126_checked : NumberTheory.primeTreeChecked subtree126 := by
  exact ⟨by norm_num only, subtree62_checked, subtree125_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree127 : BinaryTree ℕ :=
  (.node 8963
    (.node 8929 (.node 8893 (.node 8887 (.node 8867 .nil .nil) .nil) (.node 8923 .nil .nil))
      (.node 8941 (.node 8933 .nil .nil) (.node 8951 .nil .nil)))
    (.node 9007 (.node 8999 (.node 8971 (.node 8969 .nil .nil) .nil) (.node 9001 .nil .nil))
      (.node 9013 (.node 9011 .nil .nil) (.node 9029 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree127_checked : NumberTheory.primeTreeChecked subtree127 := by
  norm_num only [subtree127, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree128 : BinaryTree ℕ :=
  (.node 9133
    (.node 9091 (.node 9059 (.node 9049 (.node 9043 .nil .nil) .nil) (.node 9067 .nil .nil))
      (.node 9109 (.node 9103 .nil .nil) (.node 9127 .nil .nil)))
    (.node 9161 (.node 9151 (.node 9137 .nil .nil) (.node 9157 .nil .nil))
      (.node 9181 (.node 9173 .nil .nil) (.node 9187 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree128_checked : NumberTheory.primeTreeChecked subtree128 := by
  norm_num only [subtree128, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree129 : BinaryTree ℕ :=
  .node 9041 subtree127 subtree128

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree129_checked : NumberTheory.primeTreeChecked subtree129 := by
  exact ⟨by norm_num only, subtree127_checked, subtree128_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree130 : BinaryTree ℕ :=
  (.node 9281
    (.node 9239 (.node 9221 (.node 9209 (.node 9203 .nil .nil) .nil) (.node 9227 .nil .nil))
      (.node 9257 (.node 9241 .nil .nil) (.node 9277 .nil .nil)))
    (.node 9319 (.node 9293 (.node 9283 .nil .nil) (.node 9311 .nil .nil))
      (.node 9337 (.node 9323 .nil .nil) (.node 9341 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree130_checked : NumberTheory.primeTreeChecked subtree130 := by
  norm_num only [subtree130, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree131 : BinaryTree ℕ :=
  (.node 9421
    (.node 9397 (.node 9377 (.node 9371 (.node 9349 .nil .nil) .nil) (.node 9391 .nil .nil))
      (.node 9413 (.node 9403 .nil .nil) (.node 9419 .nil .nil)))
    (.node 9439 (.node 9433 (.node 9431 .nil .nil) (.node 9437 .nil .nil))
      (.node 9463 (.node 9461 .nil .nil) (.node 9467 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree131_checked : NumberTheory.primeTreeChecked subtree131 := by
  norm_num only [subtree131, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree132 : BinaryTree ℕ :=
  .node 9343 subtree130 subtree131

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree132_checked : NumberTheory.primeTreeChecked subtree132 := by
  exact ⟨by norm_num only, subtree130_checked, subtree131_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree133 : BinaryTree ℕ :=
  .node 9199 subtree129 subtree132

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree133_checked : NumberTheory.primeTreeChecked subtree133 := by
  exact ⟨by norm_num only, subtree129_checked, subtree132_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree134 : BinaryTree ℕ :=
  (.node 9551
    (.node 9521 (.node 9497 (.node 9491 (.node 9479 .nil .nil) .nil) (.node 9511 .nil .nil))
      (.node 9539 (.node 9533 .nil .nil) (.node 9547 .nil .nil)))
    (.node 9623 (.node 9613 (.node 9601 (.node 9587 .nil .nil) .nil) (.node 9619 .nil .nil))
      (.node 9631 (.node 9629 .nil .nil) (.node 9643 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree134_checked : NumberTheory.primeTreeChecked subtree134 := by
  norm_num only [subtree134, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree135 : BinaryTree ℕ :=
  (.node 9739
    (.node 9697 (.node 9679 (.node 9677 (.node 9661 .nil .nil) .nil) (.node 9689 .nil .nil))
      (.node 9721 (.node 9719 .nil .nil) (.node 9733 .nil .nil)))
    (.node 9769 (.node 9749 (.node 9743 .nil .nil) (.node 9767 .nil .nil))
      (.node 9787 (.node 9781 .nil .nil) (.node 9791 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree135_checked : NumberTheory.primeTreeChecked subtree135 := by
  norm_num only [subtree135, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree136 : BinaryTree ℕ :=
  .node 9649 subtree134 subtree135

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree136_checked : NumberTheory.primeTreeChecked subtree136 := by
  exact ⟨by norm_num only, subtree134_checked, subtree135_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree137 : BinaryTree ℕ :=
  (.node 9871
    (.node 9839 (.node 9829 (.node 9817 (.node 9811 .nil .nil) .nil) (.node 9833 .nil .nil))
      (.node 9857 (.node 9851 .nil .nil) (.node 9859 .nil .nil)))
    (.node 9907 (.node 9887 (.node 9883 .nil .nil) (.node 9901 .nil .nil))
      (.node 9929 (.node 9923 .nil .nil) (.node 9931 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree137_checked : NumberTheory.primeTreeChecked subtree137 := by
  norm_num only [subtree137, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree138 : BinaryTree ℕ :=
  (.node 10067
    (.node 10009 (.node 9973 (.node 9967 (.node 9949 .nil .nil) .nil) (.node 10007 .nil .nil))
      (.node 10039 (.node 10037 .nil .nil) (.node 10061 .nil .nil)))
    (.node 10093 (.node 10079 (.node 10069 .nil .nil) (.node 10091 .nil .nil))
      (.node 10103 (.node 10099 .nil .nil) (.node 10111 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree138_checked : NumberTheory.primeTreeChecked subtree138 := by
  norm_num only [subtree138, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree139 : BinaryTree ℕ :=
  .node 9941 subtree137 subtree138

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree139_checked : NumberTheory.primeTreeChecked subtree139 := by
  exact ⟨by norm_num only, subtree137_checked, subtree138_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree140 : BinaryTree ℕ :=
  .node 9803 subtree136 subtree139

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree140_checked : NumberTheory.primeTreeChecked subtree140 := by
  exact ⟨by norm_num only, subtree136_checked, subtree139_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree141 : BinaryTree ℕ :=
  .node 9473 subtree133 subtree140

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree141_checked : NumberTheory.primeTreeChecked subtree141 := by
  exact ⟨by norm_num only, subtree133_checked, subtree140_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree142 : BinaryTree ℕ :=
  (.node 10193
    (.node 10163 (.node 10151 (.node 10141 (.node 10139 .nil .nil) .nil) (.node 10159 .nil .nil))
      (.node 10177 (.node 10169 .nil .nil) (.node 10181 .nil .nil)))
    (.node 10253 (.node 10243 (.node 10223 (.node 10211 .nil .nil) .nil) (.node 10247 .nil .nil))
      (.node 10267 (.node 10259 .nil .nil) (.node 10271 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree142_checked : NumberTheory.primeTreeChecked subtree142 := by
  norm_num only [subtree142, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree143 : BinaryTree ℕ :=
  (.node 10343
    (.node 10321 (.node 10303 (.node 10301 (.node 10289 .nil .nil) .nil) (.node 10313 .nil .nil))
      (.node 10333 (.node 10331 .nil .nil) (.node 10337 .nil .nil)))
    (.node 10399 (.node 10369 (.node 10357 .nil .nil) (.node 10391 .nil .nil))
      (.node 10429 (.node 10427 .nil .nil) (.node 10433 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree143_checked : NumberTheory.primeTreeChecked subtree143 := by
  norm_num only [subtree143, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree144 : BinaryTree ℕ :=
  .node 10273 subtree142 subtree143

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree144_checked : NumberTheory.primeTreeChecked subtree144 := by
  exact ⟨by norm_num only, subtree142_checked, subtree143_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree145 : BinaryTree ℕ :=
  (.node 10529
    (.node 10487 (.node 10463 (.node 10459 (.node 10457 .nil .nil) .nil) (.node 10477 .nil .nil))
      (.node 10501 (.node 10499 .nil .nil) (.node 10513 .nil .nil)))
    (.node 10589 (.node 10559 (.node 10531 .nil .nil) (.node 10567 .nil .nil))
      (.node 10601 (.node 10597 .nil .nil) (.node 10607 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree145_checked : NumberTheory.primeTreeChecked subtree145 := by
  norm_num only [subtree145, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree146 : BinaryTree ℕ :=
  (.node 10691
    (.node 10657 (.node 10639 (.node 10631 (.node 10627 .nil .nil) .nil) (.node 10651 .nil .nil))
      (.node 10667 (.node 10663 .nil .nil) (.node 10687 .nil .nil)))
    (.node 10729 (.node 10711 (.node 10709 .nil .nil) (.node 10723 .nil .nil))
      (.node 10739 (.node 10733 .nil .nil) (.node 10753 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree146_checked : NumberTheory.primeTreeChecked subtree146 := by
  norm_num only [subtree146, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree147 : BinaryTree ℕ :=
  .node 10613 subtree145 subtree146

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree147_checked : NumberTheory.primeTreeChecked subtree147 := by
  exact ⟨by norm_num only, subtree145_checked, subtree146_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree148 : BinaryTree ℕ :=
  .node 10453 subtree144 subtree147

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree148_checked : NumberTheory.primeTreeChecked subtree148 := by
  exact ⟨by norm_num only, subtree144_checked, subtree147_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree149 : BinaryTree ℕ :=
  (.node 10861
    (.node 10837 (.node 10799 (.node 10789 (.node 10781 .nil .nil) .nil) (.node 10831 .nil .nil))
      (.node 10853 (.node 10847 .nil .nil) (.node 10859 .nil .nil)))
    (.node 10903 (.node 10889 (.node 10883 (.node 10867 .nil .nil) .nil) (.node 10891 .nil .nil))
      (.node 10937 (.node 10909 .nil .nil) (.node 10939 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree149_checked : NumberTheory.primeTreeChecked subtree149 := by
  norm_num only [subtree149, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree150 : BinaryTree ℕ :=
  (.node 11057
    (.node 10993 (.node 10979 (.node 10973 (.node 10957 .nil .nil) .nil) (.node 10987 .nil .nil))
      (.node 11027 (.node 11003 .nil .nil) (.node 11047 .nil .nil)))
    (.node 11083 (.node 11069 (.node 11059 .nil .nil) (.node 11071 .nil .nil))
      (.node 11093 (.node 11087 .nil .nil) (.node 11113 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree150_checked : NumberTheory.primeTreeChecked subtree150 := by
  norm_num only [subtree150, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree151 : BinaryTree ℕ :=
  .node 10949 subtree149 subtree150

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree151_checked : NumberTheory.primeTreeChecked subtree151 := by
  exact ⟨by norm_num only, subtree149_checked, subtree150_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree152 : BinaryTree ℕ :=
  (.node 11197
    (.node 11161 (.node 11149 (.node 11131 (.node 11119 .nil .nil) .nil) (.node 11159 .nil .nil))
      (.node 11173 (.node 11171 .nil .nil) (.node 11177 .nil .nil)))
    (.node 11251 (.node 11239 (.node 11213 .nil .nil) (.node 11243 .nil .nil))
      (.node 11261 (.node 11257 .nil .nil) (.node 11273 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree152_checked : NumberTheory.primeTreeChecked subtree152 := by
  norm_num only [subtree152, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree153 : BinaryTree ℕ :=
  (.node 11369
    (.node 11321 (.node 11311 (.node 11299 (.node 11287 .nil .nil) .nil) (.node 11317 .nil .nil))
      (.node 11351 (.node 11329 .nil .nil) (.node 11353 .nil .nil)))
    (.node 11411 (.node 11393 (.node 11383 .nil .nil) (.node 11399 .nil .nil))
      (.node 11437 (.node 11423 .nil .nil) (.node 11443 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree153_checked : NumberTheory.primeTreeChecked subtree153 := by
  norm_num only [subtree153, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree154 : BinaryTree ℕ :=
  .node 11279 subtree152 subtree153

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree154_checked : NumberTheory.primeTreeChecked subtree154 := by
  exact ⟨by norm_num only, subtree152_checked, subtree153_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree155 : BinaryTree ℕ :=
  .node 11117 subtree151 subtree154

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree155_checked : NumberTheory.primeTreeChecked subtree155 := by
  exact ⟨by norm_num only, subtree151_checked, subtree154_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree156 : BinaryTree ℕ :=
  .node 10771 subtree148 subtree155

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree156_checked : NumberTheory.primeTreeChecked subtree156 := by
  exact ⟨by norm_num only, subtree148_checked, subtree155_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree157 : BinaryTree ℕ :=
  .node 10133 subtree141 subtree156

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree157_checked : NumberTheory.primeTreeChecked subtree157 := by
  exact ⟨by norm_num only, subtree141_checked, subtree156_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree158 : BinaryTree ℕ :=
  (.node 11527
    (.node 11491 (.node 11483 (.node 11471 (.node 11467 .nil .nil) .nil) (.node 11489 .nil .nil))
      (.node 11503 (.node 11497 .nil .nil) (.node 11519 .nil .nil)))
    (.node 11593 (.node 11579 (.node 11551 (.node 11549 .nil .nil) .nil) (.node 11587 .nil .nil))
      (.node 11617 (.node 11597 .nil .nil) (.node 11621 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree158_checked : NumberTheory.primeTreeChecked subtree158 := by
  norm_num only [subtree158, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree159 : BinaryTree ℕ :=
  (.node 11731
    (.node 11699 (.node 11681 (.node 11677 (.node 11657 .nil .nil) .nil) (.node 11689 .nil .nil))
      (.node 11717 (.node 11701 .nil .nil) (.node 11719 .nil .nil)))
    (.node 11783 (.node 11777 (.node 11743 .nil .nil) (.node 11779 .nil .nil))
      (.node 11801 (.node 11789 .nil .nil) (.node 11807 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree159_checked : NumberTheory.primeTreeChecked subtree159 := by
  norm_num only [subtree159, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree160 : BinaryTree ℕ :=
  .node 11633 subtree158 subtree159

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree160_checked : NumberTheory.primeTreeChecked subtree160 := by
  exact ⟨by norm_num only, subtree158_checked, subtree159_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree161 : BinaryTree ℕ :=
  (.node 11897
    (.node 11839 (.node 11831 (.node 11827 (.node 11821 .nil .nil) .nil) (.node 11833 .nil .nil))
      (.node 11867 (.node 11863 .nil .nil) (.node 11887 .nil .nil)))
    (.node 11927 (.node 11909 (.node 11903 .nil .nil) (.node 11923 .nil .nil))
      (.node 11939 (.node 11933 .nil .nil) (.node 11941 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree161_checked : NumberTheory.primeTreeChecked subtree161 := by
  norm_num only [subtree161, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree162 : BinaryTree ℕ :=
  (.node 12041
    (.node 11987 (.node 11971 (.node 11969 (.node 11959 .nil .nil) .nil) (.node 11981 .nil .nil))
      (.node 12011 (.node 12007 .nil .nil) (.node 12037 .nil .nil)))
    (.node 12073 (.node 12049 (.node 12043 .nil .nil) (.node 12071 .nil .nil))
      (.node 12101 (.node 12097 .nil .nil) (.node 12107 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree162_checked : NumberTheory.primeTreeChecked subtree162 := by
  norm_num only [subtree162, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree163 : BinaryTree ℕ :=
  .node 11953 subtree161 subtree162

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree163_checked : NumberTheory.primeTreeChecked subtree163 := by
  exact ⟨by norm_num only, subtree161_checked, subtree162_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree164 : BinaryTree ℕ :=
  .node 11813 subtree160 subtree163

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree164_checked : NumberTheory.primeTreeChecked subtree164 := by
  exact ⟨by norm_num only, subtree160_checked, subtree163_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree165 : BinaryTree ℕ :=
  (.node 12203
    (.node 12157 (.node 12143 (.node 12119 (.node 12113 .nil .nil) .nil) (.node 12149 .nil .nil))
      (.node 12163 (.node 12161 .nil .nil) (.node 12197 .nil .nil)))
    (.node 12251 (.node 12239 (.node 12227 (.node 12211 .nil .nil) .nil) (.node 12241 .nil .nil))
      (.node 12263 (.node 12253 .nil .nil) (.node 12269 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree165_checked : NumberTheory.primeTreeChecked subtree165 := by
  norm_num only [subtree165, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree166 : BinaryTree ℕ :=
  (.node 12377
    (.node 12329 (.node 12301 (.node 12289 (.node 12281 .nil .nil) .nil) (.node 12323 .nil .nil))
      (.node 12347 (.node 12343 .nil .nil) (.node 12373 .nil .nil)))
    (.node 12409 (.node 12391 (.node 12379 .nil .nil) (.node 12401 .nil .nil))
      (.node 12421 (.node 12413 .nil .nil) (.node 12433 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree166_checked : NumberTheory.primeTreeChecked subtree166 := by
  norm_num only [subtree166, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree167 : BinaryTree ℕ :=
  .node 12277 subtree165 subtree166

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree167_checked : NumberTheory.primeTreeChecked subtree167 := by
  exact ⟨by norm_num only, subtree165_checked, subtree166_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree168 : BinaryTree ℕ :=
  (.node 12511
    (.node 12487 (.node 12473 (.node 12457 (.node 12451 .nil .nil) .nil) (.node 12479 .nil .nil))
      (.node 12497 (.node 12491 .nil .nil) (.node 12503 .nil .nil)))
    (.node 12541 (.node 12527 (.node 12517 .nil .nil) (.node 12539 .nil .nil))
      (.node 12553 (.node 12547 .nil .nil) (.node 12569 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree168_checked : NumberTheory.primeTreeChecked subtree168 := by
  norm_num only [subtree168, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree169 : BinaryTree ℕ :=
  (.node 12647
    (.node 12613 (.node 12601 (.node 12589 (.node 12583 .nil .nil) .nil) (.node 12611 .nil .nil))
      (.node 12637 (.node 12619 .nil .nil) (.node 12641 .nil .nil)))
    (.node 12689 (.node 12659 (.node 12653 .nil .nil) (.node 12671 .nil .nil))
      (.node 12703 (.node 12697 .nil .nil) (.node 12713 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree169_checked : NumberTheory.primeTreeChecked subtree169 := by
  norm_num only [subtree169, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree170 : BinaryTree ℕ :=
  .node 12577 subtree168 subtree169

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree170_checked : NumberTheory.primeTreeChecked subtree170 := by
  exact ⟨by norm_num only, subtree168_checked, subtree169_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree171 : BinaryTree ℕ :=
  .node 12437 subtree167 subtree170

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree171_checked : NumberTheory.primeTreeChecked subtree171 := by
  exact ⟨by norm_num only, subtree167_checked, subtree170_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree172 : BinaryTree ℕ :=
  .node 12109 subtree164 subtree171

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree172_checked : NumberTheory.primeTreeChecked subtree172 := by
  exact ⟨by norm_num only, subtree164_checked, subtree171_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree173 : BinaryTree ℕ :=
  (.node 12821
    (.node 12781 (.node 12757 (.node 12743 (.node 12739 .nil .nil) .nil) (.node 12763 .nil .nil))
      (.node 12799 (.node 12791 .nil .nil) (.node 12809 .nil .nil)))
    (.node 12889 (.node 12841 (.node 12829 (.node 12823 .nil .nil) .nil) (.node 12853 .nil .nil))
      (.node 12899 (.node 12893 .nil .nil) (.node 12907 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree173_checked : NumberTheory.primeTreeChecked subtree173 := by
  norm_num only [subtree173, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree174 : BinaryTree ℕ :=
  (.node 12979
    (.node 12953 (.node 12923 (.node 12919 (.node 12917 .nil .nil) .nil) (.node 12941 .nil .nil))
      (.node 12967 (.node 12959 .nil .nil) (.node 12973 .nil .nil)))
    (.node 13007 (.node 13001 (.node 12983 .nil .nil) (.node 13003 .nil .nil))
      (.node 13033 (.node 13009 .nil .nil) (.node 13037 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree174_checked : NumberTheory.primeTreeChecked subtree174 := by
  norm_num only [subtree174, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree175 : BinaryTree ℕ :=
  .node 12911 subtree173 subtree174

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree175_checked : NumberTheory.primeTreeChecked subtree175 := by
  exact ⟨by norm_num only, subtree173_checked, subtree174_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree176 : BinaryTree ℕ :=
  (.node 13147
    (.node 13103 (.node 13093 (.node 13063 (.node 13049 .nil .nil) .nil) (.node 13099 .nil .nil))
      (.node 13121 (.node 13109 .nil .nil) (.node 13127 .nil .nil)))
    (.node 13171 (.node 13159 (.node 13151 .nil .nil) (.node 13163 .nil .nil))
      (.node 13183 (.node 13177 .nil .nil) (.node 13187 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree176_checked : NumberTheory.primeTreeChecked subtree176 := by
  norm_num only [subtree176, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree177 : BinaryTree ℕ :=
  (.node 13309
    (.node 13259 (.node 13241 (.node 13229 (.node 13219 .nil .nil) .nil) (.node 13249 .nil .nil))
      (.node 13291 (.node 13267 .nil .nil) (.node 13297 .nil .nil)))
    (.node 13337 (.node 13327 (.node 13313 .nil .nil) (.node 13331 .nil .nil))
      (.node 13367 (.node 13339 .nil .nil) (.node 13381 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree177_checked : NumberTheory.primeTreeChecked subtree177 := by
  norm_num only [subtree177, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree178 : BinaryTree ℕ :=
  .node 13217 subtree176 subtree177

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree178_checked : NumberTheory.primeTreeChecked subtree178 := by
  exact ⟨by norm_num only, subtree176_checked, subtree177_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree179 : BinaryTree ℕ :=
  .node 13043 subtree175 subtree178

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree179_checked : NumberTheory.primeTreeChecked subtree179 := by
  exact ⟨by norm_num only, subtree175_checked, subtree178_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree180 : BinaryTree ℕ :=
  (.node 13469
    (.node 13441 (.node 13417 (.node 13411 (.node 13399 .nil .nil) .nil) (.node 13421 .nil .nil))
      (.node 13457 (.node 13451 .nil .nil) (.node 13463 .nil .nil)))
    (.node 13523 (.node 13499 (.node 13487 (.node 13477 .nil .nil) .nil) (.node 13513 .nil .nil))
      (.node 13553 (.node 13537 .nil .nil) (.node 13567 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree180_checked : NumberTheory.primeTreeChecked subtree180 := by
  norm_num only [subtree180, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree181 : BinaryTree ℕ :=
  (.node 13679
    (.node 13627 (.node 13613 (.node 13597 (.node 13591 .nil .nil) .nil) (.node 13619 .nil .nil))
      (.node 13649 (.node 13633 .nil .nil) (.node 13669 .nil .nil)))
    (.node 13693 (.node 13687 (.node 13681 .nil .nil) (.node 13691 .nil .nil))
      (.node 13709 (.node 13697 .nil .nil) (.node 13711 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree181_checked : NumberTheory.primeTreeChecked subtree181 := by
  norm_num only [subtree181, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree182 : BinaryTree ℕ :=
  .node 13577 subtree180 subtree181

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree182_checked : NumberTheory.primeTreeChecked subtree182 := by
  exact ⟨by norm_num only, subtree180_checked, subtree181_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree183 : BinaryTree ℕ :=
  (.node 13799
    (.node 13759 (.node 13751 (.node 13729 (.node 13723 .nil .nil) .nil) (.node 13757 .nil .nil))
      (.node 13781 (.node 13763 .nil .nil) (.node 13789 .nil .nil)))
    (.node 13841 (.node 13829 (.node 13807 .nil .nil) (.node 13831 .nil .nil))
      (.node 13873 (.node 13859 .nil .nil) (.node 13877 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree183_checked : NumberTheory.primeTreeChecked subtree183 := by
  norm_num only [subtree183, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree184 : BinaryTree ℕ :=
  (.node 13963
    (.node 13913 (.node 13903 (.node 13901 (.node 13883 .nil .nil) .nil) (.node 13907 .nil .nil))
      (.node 13931 (.node 13921 .nil .nil) (.node 13933 .nil .nil)))
    (.node 14009 (.node 13997 (.node 13967 .nil .nil) (.node 13999 .nil .nil))
      (.node 14029 (.node 14011 .nil .nil) (.node 14033 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree184_checked : NumberTheory.primeTreeChecked subtree184 := by
  norm_num only [subtree184, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree185 : BinaryTree ℕ :=
  .node 13879 subtree183 subtree184

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree185_checked : NumberTheory.primeTreeChecked subtree185 := by
  exact ⟨by norm_num only, subtree183_checked, subtree184_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree186 : BinaryTree ℕ :=
  .node 13721 subtree182 subtree185

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree186_checked : NumberTheory.primeTreeChecked subtree186 := by
  exact ⟨by norm_num only, subtree182_checked, subtree185_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree187 : BinaryTree ℕ :=
  .node 13397 subtree179 subtree186

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree187_checked : NumberTheory.primeTreeChecked subtree187 := by
  exact ⟨by norm_num only, subtree179_checked, subtree186_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree188 : BinaryTree ℕ :=
  .node 12721 subtree172 subtree187

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree188_checked : NumberTheory.primeTreeChecked subtree188 := by
  exact ⟨by norm_num only, subtree172_checked, subtree187_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree189 : BinaryTree ℕ :=
  .node 11447 subtree157 subtree188

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree189_checked : NumberTheory.primeTreeChecked subtree189 := by
  exact ⟨by norm_num only, subtree157_checked, subtree188_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree190 : BinaryTree ℕ :=
  (.node 14153
    (.node 14087 (.node 14081 (.node 14071 (.node 14057 .nil .nil) .nil) (.node 14083 .nil .nil))
      (.node 14143 (.node 14107 .nil .nil) (.node 14149 .nil .nil)))
    (.node 14207 (.node 14177 (.node 14173 (.node 14159 .nil .nil) .nil) (.node 14197 .nil .nil))
      (.node 14243 (.node 14221 .nil .nil) (.node 14249 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree190_checked : NumberTheory.primeTreeChecked subtree190 := by
  norm_num only [subtree190, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree191 : BinaryTree ℕ :=
  (.node 14369
    (.node 14323 (.node 14303 (.node 14293 (.node 14281 .nil .nil) .nil) (.node 14321 .nil .nil))
      (.node 14341 (.node 14327 .nil .nil) (.node 14347 .nil .nil)))
    (.node 14407 (.node 14389 (.node 14387 .nil .nil) (.node 14401 .nil .nil))
      (.node 14419 (.node 14411 .nil .nil) (.node 14423 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree191_checked : NumberTheory.primeTreeChecked subtree191 := by
  norm_num only [subtree191, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree192 : BinaryTree ℕ :=
  .node 14251 subtree190 subtree191

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree192_checked : NumberTheory.primeTreeChecked subtree192 := by
  exact ⟨by norm_num only, subtree190_checked, subtree191_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree193 : BinaryTree ℕ :=
  (.node 14533
    (.node 14479 (.node 14449 (.node 14447 (.node 14437 .nil .nil) .nil) (.node 14461 .nil .nil))
      (.node 14503 (.node 14489 .nil .nil) (.node 14519 .nil .nil)))
    (.node 14551 (.node 14543 (.node 14537 .nil .nil) (.node 14549 .nil .nil))
      (.node 14561 (.node 14557 .nil .nil) (.node 14563 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree193_checked : NumberTheory.primeTreeChecked subtree193 := by
  norm_num only [subtree193, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree194 : BinaryTree ℕ :=
  (.node 14669
    (.node 14633 (.node 14627 (.node 14621 (.node 14593 .nil .nil) .nil) (.node 14629 .nil .nil))
      (.node 14653 (.node 14639 .nil .nil) (.node 14657 .nil .nil)))
    (.node 14717 (.node 14699 (.node 14683 .nil .nil) (.node 14713 .nil .nil))
      (.node 14731 (.node 14723 .nil .nil) (.node 14737 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree194_checked : NumberTheory.primeTreeChecked subtree194 := by
  norm_num only [subtree194, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree195 : BinaryTree ℕ :=
  .node 14591 subtree193 subtree194

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree195_checked : NumberTheory.primeTreeChecked subtree195 := by
  exact ⟨by norm_num only, subtree193_checked, subtree194_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree196 : BinaryTree ℕ :=
  .node 14431 subtree192 subtree195

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree196_checked : NumberTheory.primeTreeChecked subtree196 := by
  exact ⟨by norm_num only, subtree192_checked, subtree195_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree197 : BinaryTree ℕ :=
  (.node 14813
    (.node 14771 (.node 14759 (.node 14753 (.node 14747 .nil .nil) .nil) (.node 14767 .nil .nil))
      (.node 14783 (.node 14779 .nil .nil) (.node 14797 .nil .nil)))
    (.node 14851 (.node 14831 (.node 14827 (.node 14821 .nil .nil) .nil) (.node 14843 .nil .nil))
      (.node 14869 (.node 14867 .nil .nil) (.node 14879 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree197_checked : NumberTheory.primeTreeChecked subtree197 := by
  norm_num only [subtree197, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree198 : BinaryTree ℕ :=
  (.node 14969
    (.node 14939 (.node 14923 (.node 14897 (.node 14891 .nil .nil) .nil) (.node 14929 .nil .nil))
      (.node 14951 (.node 14947 .nil .nil) (.node 14957 .nil .nil)))
    (.node 15031 (.node 15013 (.node 14983 .nil .nil) (.node 15017 .nil .nil))
      (.node 15061 (.node 15053 .nil .nil) (.node 15073 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree198_checked : NumberTheory.primeTreeChecked subtree198 := by
  norm_num only [subtree198, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree199 : BinaryTree ℕ :=
  .node 14887 subtree197 subtree198

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree199_checked : NumberTheory.primeTreeChecked subtree199 := by
  exact ⟨by norm_num only, subtree197_checked, subtree198_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree200 : BinaryTree ℕ :=
  (.node 15149
    (.node 15121 (.node 15101 (.node 15091 (.node 15083 .nil .nil) .nil) (.node 15107 .nil .nil))
      (.node 15137 (.node 15131 .nil .nil) (.node 15139 .nil .nil)))
    (.node 15193 (.node 15173 (.node 15161 .nil .nil) (.node 15187 .nil .nil))
      (.node 15217 (.node 15199 .nil .nil) (.node 15227 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree200_checked : NumberTheory.primeTreeChecked subtree200 := by
  norm_num only [subtree200, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree201 : BinaryTree ℕ :=
  (.node 15299
    (.node 15271 (.node 15263 (.node 15259 (.node 15241 .nil .nil) .nil) (.node 15269 .nil .nil))
      (.node 15287 (.node 15277 .nil .nil) (.node 15289 .nil .nil)))
    (.node 15329 (.node 15313 (.node 15307 .nil .nil) (.node 15319 .nil .nil))
      (.node 15349 (.node 15331 .nil .nil) (.node 15359 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree201_checked : NumberTheory.primeTreeChecked subtree201 := by
  norm_num only [subtree201, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree202 : BinaryTree ℕ :=
  .node 15233 subtree200 subtree201

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree202_checked : NumberTheory.primeTreeChecked subtree202 := by
  exact ⟨by norm_num only, subtree200_checked, subtree201_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree203 : BinaryTree ℕ :=
  .node 15077 subtree199 subtree202

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree203_checked : NumberTheory.primeTreeChecked subtree203 := by
  exact ⟨by norm_num only, subtree199_checked, subtree202_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree204 : BinaryTree ℕ :=
  .node 14741 subtree196 subtree203

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree204_checked : NumberTheory.primeTreeChecked subtree204 := by
  exact ⟨by norm_num only, subtree196_checked, subtree203_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree205 : BinaryTree ℕ :=
  (.node 15443
    (.node 15401 (.node 15383 (.node 15377 (.node 15373 .nil .nil) .nil) (.node 15391 .nil .nil))
      (.node 15427 (.node 15413 .nil .nil) (.node 15439 .nil .nil)))
    (.node 15493 (.node 15467 (.node 15461 (.node 15451 .nil .nil) .nil) (.node 15473 .nil .nil))
      (.node 15511 (.node 15497 .nil .nil) (.node 15527 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree205_checked : NumberTheory.primeTreeChecked subtree205 := by
  norm_num only [subtree205, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree206 : BinaryTree ℕ :=
  (.node 15629
    (.node 15583 (.node 15569 (.node 15559 (.node 15551 .nil .nil) .nil) (.node 15581 .nil .nil))
      (.node 15607 (.node 15601 .nil .nil) (.node 15619 .nil .nil)))
    (.node 15649 (.node 15643 (.node 15641 .nil .nil) (.node 15647 .nil .nil))
      (.node 15667 (.node 15661 .nil .nil) (.node 15671 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree206_checked : NumberTheory.primeTreeChecked subtree206 := by
  norm_num only [subtree206, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree207 : BinaryTree ℕ :=
  .node 15541 subtree205 subtree206

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree207_checked : NumberTheory.primeTreeChecked subtree207 := by
  exact ⟨by norm_num only, subtree205_checked, subtree206_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree208 : BinaryTree ℕ :=
  (.node 15767
    (.node 15737 (.node 15731 (.node 15727 (.node 15683 .nil .nil) .nil) (.node 15733 .nil .nil))
      (.node 15749 (.node 15739 .nil .nil) (.node 15761 .nil .nil)))
    (.node 15797 (.node 15787 (.node 15773 .nil .nil) (.node 15791 .nil .nil))
      (.node 15809 (.node 15803 .nil .nil) (.node 15817 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree208_checked : NumberTheory.primeTreeChecked subtree208 := by
  norm_num only [subtree208, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree209 : BinaryTree ℕ :=
  (.node 15919
    (.node 15889 (.node 15881 (.node 15877 (.node 15859 .nil .nil) .nil) (.node 15887 .nil .nil))
      (.node 15907 (.node 15901 .nil .nil) (.node 15913 .nil .nil)))
    (.node 15971 (.node 15937 (.node 15923 .nil .nil) (.node 15959 .nil .nil))
      (.node 15991 (.node 15973 .nil .nil) (.node 16001 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree209_checked : NumberTheory.primeTreeChecked subtree209 := by
  norm_num only [subtree209, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree210 : BinaryTree ℕ :=
  .node 15823 subtree208 subtree209

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree210_checked : NumberTheory.primeTreeChecked subtree210 := by
  exact ⟨by norm_num only, subtree208_checked, subtree209_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree211 : BinaryTree ℕ :=
  .node 15679 subtree207 subtree210

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree211_checked : NumberTheory.primeTreeChecked subtree211 := by
  exact ⟨by norm_num only, subtree207_checked, subtree210_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree212 : BinaryTree ℕ :=
  (.node 16091
    (.node 16067 (.node 16061 (.node 16057 (.node 16033 .nil .nil) .nil) (.node 16063 .nil .nil))
      (.node 16073 (.node 16069 .nil .nil) (.node 16087 .nil .nil)))
    (.node 16139 (.node 16111 (.node 16103 (.node 16097 .nil .nil) .nil) (.node 16127 .nil .nil))
      (.node 16183 (.node 16141 .nil .nil) (.node 16187 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree212_checked : NumberTheory.primeTreeChecked subtree212 := by
  norm_num only [subtree212, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree213 : BinaryTree ℕ :=
  (.node 16273
    (.node 16231 (.node 16223 (.node 16217 (.node 16193 .nil .nil) .nil) (.node 16229 .nil .nil))
      (.node 16253 (.node 16249 .nil .nil) (.node 16267 .nil .nil)))
    (.node 16339 (.node 16319 (.node 16301 .nil .nil) (.node 16333 .nil .nil))
      (.node 16361 (.node 16349 .nil .nil) (.node 16363 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree213_checked : NumberTheory.primeTreeChecked subtree213 := by
  norm_num only [subtree213, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree214 : BinaryTree ℕ :=
  .node 16189 subtree212 subtree213

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree214_checked : NumberTheory.primeTreeChecked subtree214 := by
  exact ⟨by norm_num only, subtree212_checked, subtree213_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree215 : BinaryTree ℕ :=
  (.node 16453
    (.node 16427 (.node 16417 (.node 16411 (.node 16381 .nil .nil) .nil) (.node 16421 .nil .nil))
      (.node 16447 (.node 16433 .nil .nil) (.node 16451 .nil .nil)))
    (.node 16493 (.node 16481 (.node 16477 .nil .nil) (.node 16487 .nil .nil))
      (.node 16529 (.node 16519 .nil .nil) (.node 16547 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree215_checked : NumberTheory.primeTreeChecked subtree215 := by
  norm_num only [subtree215, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree216 : BinaryTree ℕ :=
  (.node 16649
    (.node 16607 (.node 16573 (.node 16567 (.node 16561 .nil .nil) .nil) (.node 16603 .nil .nil))
      (.node 16631 (.node 16619 .nil .nil) (.node 16633 .nil .nil)))
    (.node 16673 (.node 16657 (.node 16651 .nil .nil) (.node 16661 .nil .nil))
      (.node 16693 (.node 16691 .nil .nil) (.node 16699 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree216_checked : NumberTheory.primeTreeChecked subtree216 := by
  norm_num only [subtree216, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree217 : BinaryTree ℕ :=
  .node 16553 subtree215 subtree216

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree217_checked : NumberTheory.primeTreeChecked subtree217 := by
  exact ⟨by norm_num only, subtree215_checked, subtree216_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree218 : BinaryTree ℕ :=
  .node 16369 subtree214 subtree217

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree218_checked : NumberTheory.primeTreeChecked subtree218 := by
  exact ⟨by norm_num only, subtree214_checked, subtree217_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree219 : BinaryTree ℕ :=
  .node 16007 subtree211 subtree218

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree219_checked : NumberTheory.primeTreeChecked subtree219 := by
  exact ⟨by norm_num only, subtree211_checked, subtree218_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree220 : BinaryTree ℕ :=
  .node 15361 subtree204 subtree219

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree220_checked : NumberTheory.primeTreeChecked subtree220 := by
  exact ⟨by norm_num only, subtree204_checked, subtree219_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree221 : BinaryTree ℕ :=
  (.node 16829
    (.node 16763 (.node 16747 (.node 16741 (.node 16729 .nil .nil) .nil) (.node 16759 .nil .nil))
      (.node 16811 (.node 16787 .nil .nil) (.node 16823 .nil .nil)))
    (.node 16883 (.node 16871 (.node 16843 (.node 16831 .nil .nil) .nil) (.node 16879 .nil .nil))
      (.node 16901 (.node 16889 .nil .nil) (.node 16903 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree221_checked : NumberTheory.primeTreeChecked subtree221 := by
  norm_num only [subtree221, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree222 : BinaryTree ℕ :=
  (.node 16993
    (.node 16963 (.node 16937 (.node 16931 (.node 16927 .nil .nil) .nil) (.node 16943 .nil .nil))
      (.node 16981 (.node 16979 .nil .nil) (.node 16987 .nil .nil)))
    (.node 17029 (.node 17021 (.node 17011 .nil .nil) (.node 17027 .nil .nil))
      (.node 17041 (.node 17033 .nil .nil) (.node 17047 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree222_checked : NumberTheory.primeTreeChecked subtree222 := by
  norm_num only [subtree222, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree223 : BinaryTree ℕ :=
  .node 16921 subtree221 subtree222

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree223_checked : NumberTheory.primeTreeChecked subtree223 := by
  exact ⟨by norm_num only, subtree221_checked, subtree222_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree224 : BinaryTree ℕ :=
  (.node 17167
    (.node 17117 (.node 17099 (.node 17093 (.node 17077 .nil .nil) .nil) (.node 17107 .nil .nil))
      (.node 17137 (.node 17123 .nil .nil) (.node 17159 .nil .nil)))
    (.node 17203 (.node 17189 (.node 17183 .nil .nil) (.node 17191 .nil .nil))
      (.node 17209 (.node 17207 .nil .nil) (.node 17231 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree224_checked : NumberTheory.primeTreeChecked subtree224 := by
  norm_num only [subtree224, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree225 : BinaryTree ℕ :=
  (.node 17341
    (.node 17317 (.node 17293 (.node 17291 (.node 17257 .nil .nil) .nil) (.node 17299 .nil .nil))
      (.node 17327 (.node 17321 .nil .nil) (.node 17333 .nil .nil)))
    (.node 17383 (.node 17359 (.node 17351 .nil .nil) (.node 17377 .nil .nil))
      (.node 17389 (.node 17387 .nil .nil) (.node 17393 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree225_checked : NumberTheory.primeTreeChecked subtree225 := by
  norm_num only [subtree225, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree226 : BinaryTree ℕ :=
  .node 17239 subtree224 subtree225

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree226_checked : NumberTheory.primeTreeChecked subtree226 := by
  exact ⟨by norm_num only, subtree224_checked, subtree225_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree227 : BinaryTree ℕ :=
  .node 17053 subtree223 subtree226

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree227_checked : NumberTheory.primeTreeChecked subtree227 := by
  exact ⟨by norm_num only, subtree223_checked, subtree226_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree228 : BinaryTree ℕ :=
  (.node 17483
    (.node 17449 (.node 17431 (.node 17419 (.node 17417 .nil .nil) .nil) (.node 17443 .nil .nil))
      (.node 17471 (.node 17467 .nil .nil) (.node 17477 .nil .nil)))
    (.node 17519 (.node 17497 (.node 17491 (.node 17489 .nil .nil) .nil) (.node 17509 .nil .nil))
      (.node 17551 (.node 17539 .nil .nil) (.node 17569 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree228_checked : NumberTheory.primeTreeChecked subtree228 := by
  norm_num only [subtree228, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree229 : BinaryTree ℕ :=
  (.node 17659
    (.node 17609 (.node 17597 (.node 17581 (.node 17579 .nil .nil) .nil) (.node 17599 .nil .nil))
      (.node 17627 (.node 17623 .nil .nil) (.node 17657 .nil .nil)))
    (.node 17707 (.node 17681 (.node 17669 .nil .nil) (.node 17683 .nil .nil))
      (.node 17729 (.node 17713 .nil .nil) (.node 17737 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree229_checked : NumberTheory.primeTreeChecked subtree229 := by
  norm_num only [subtree229, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree230 : BinaryTree ℕ :=
  .node 17573 subtree228 subtree229

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree230_checked : NumberTheory.primeTreeChecked subtree230 := by
  exact ⟨by norm_num only, subtree228_checked, subtree229_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree231 : BinaryTree ℕ :=
  (.node 17839
    (.node 17791 (.node 17783 (.node 17761 (.node 17749 .nil .nil) .nil) (.node 17789 .nil .nil))
      (.node 17827 (.node 17807 .nil .nil) (.node 17837 .nil .nil)))
    (.node 17891 (.node 17863 (.node 17851 .nil .nil) (.node 17881 .nil .nil))
      (.node 17909 (.node 17903 .nil .nil) (.node 17911 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree231_checked : NumberTheory.primeTreeChecked subtree231 := by
  norm_num only [subtree231, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree232 : BinaryTree ℕ :=
  (.node 17987
    (.node 17959 (.node 17939 (.node 17929 (.node 17923 .nil .nil) .nil) (.node 17957 .nil .nil))
      (.node 17977 (.node 17971 .nil .nil) (.node 17981 .nil .nil)))
    (.node 18043 (.node 18013 (.node 17989 .nil .nil) (.node 18041 .nil .nil))
      (.node 18049 (.node 18047 .nil .nil) (.node 18059 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree232_checked : NumberTheory.primeTreeChecked subtree232 := by
  norm_num only [subtree232, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree233 : BinaryTree ℕ :=
  .node 17921 subtree231 subtree232

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree233_checked : NumberTheory.primeTreeChecked subtree233 := by
  exact ⟨by norm_num only, subtree231_checked, subtree232_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree234 : BinaryTree ℕ :=
  .node 17747 subtree230 subtree233

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree234_checked : NumberTheory.primeTreeChecked subtree234 := by
  exact ⟨by norm_num only, subtree230_checked, subtree233_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree235 : BinaryTree ℕ :=
  .node 17401 subtree227 subtree234

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree235_checked : NumberTheory.primeTreeChecked subtree235 := by
  exact ⟨by norm_num only, subtree227_checked, subtree234_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree236 : BinaryTree ℕ :=
  (.node 18143
    (.node 18121 (.node 18097 (.node 18089 (.node 18077 .nil .nil) .nil) (.node 18119 .nil .nil))
      (.node 18131 (.node 18127 .nil .nil) (.node 18133 .nil .nil)))
    (.node 18199 (.node 18181 (.node 18169 (.node 18149 .nil .nil) .nil) (.node 18191 .nil .nil))
      (.node 18217 (.node 18211 .nil .nil) (.node 18223 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree236_checked : NumberTheory.primeTreeChecked subtree236 := by
  norm_num only [subtree236, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree237 : BinaryTree ℕ :=
  (.node 18307
    (.node 18269 (.node 18253 (.node 18251 (.node 18233 .nil .nil) .nil) (.node 18257 .nil .nil))
      (.node 18289 (.node 18287 .nil .nil) (.node 18301 .nil .nil)))
    (.node 18341 (.node 18313 (.node 18311 .nil .nil) (.node 18329 .nil .nil))
      (.node 18367 (.node 18353 .nil .nil) (.node 18371 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree237_checked : NumberTheory.primeTreeChecked subtree237 := by
  norm_num only [subtree237, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree238 : BinaryTree ℕ :=
  .node 18229 subtree236 subtree237

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree238_checked : NumberTheory.primeTreeChecked subtree238 := by
  exact ⟨by norm_num only, subtree236_checked, subtree237_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree239 : BinaryTree ℕ :=
  (.node 18457
    (.node 18433 (.node 18413 (.node 18401 (.node 18397 .nil .nil) .nil) (.node 18427 .nil .nil))
      (.node 18443 (.node 18439 .nil .nil) (.node 18451 .nil .nil)))
    (.node 18503 (.node 18481 (.node 18461 .nil .nil) (.node 18493 .nil .nil))
      (.node 18521 (.node 18517 .nil .nil) (.node 18523 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree239_checked : NumberTheory.primeTreeChecked subtree239 := by
  norm_num only [subtree239, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree240 : BinaryTree ℕ :=
  (.node 18671
    (.node 18593 (.node 18583 (.node 18553 (.node 18541 .nil .nil) .nil) (.node 18587 .nil .nil))
      (.node 18637 (.node 18617 .nil .nil) (.node 18661 .nil .nil)))
    (.node 18713 (.node 18691 (.node 18679 .nil .nil) (.node 18701 .nil .nil))
      (.node 18731 (.node 18719 .nil .nil) (.node 18743 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree240_checked : NumberTheory.primeTreeChecked subtree240 := by
  norm_num only [subtree240, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree241 : BinaryTree ℕ :=
  .node 18539 subtree239 subtree240

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree241_checked : NumberTheory.primeTreeChecked subtree241 := by
  exact ⟨by norm_num only, subtree239_checked, subtree240_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree242 : BinaryTree ℕ :=
  .node 18379 subtree238 subtree241

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree242_checked : NumberTheory.primeTreeChecked subtree242 := by
  exact ⟨by norm_num only, subtree238_checked, subtree241_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree243 : BinaryTree ℕ :=
  (.node 18869
    (.node 18797 (.node 18787 (.node 18773 (.node 18757 .nil .nil) .nil) (.node 18793 .nil .nil))
      (.node 18839 (.node 18803 .nil .nil) (.node 18859 .nil .nil)))
    (.node 18917 (.node 18911 (.node 18899 .nil .nil) (.node 18913 .nil .nil))
      (.node 18947 (.node 18919 .nil .nil) (.node 18959 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree243_checked : NumberTheory.primeTreeChecked subtree243 := by
  norm_num only [subtree243, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree244 : BinaryTree ℕ :=
  (.node 19073
    (.node 19031 (.node 19009 (.node 19001 (.node 18979 .nil .nil) .nil) (.node 19013 .nil .nil))
      (.node 19051 (.node 19037 .nil .nil) (.node 19069 .nil .nil)))
    (.node 19121 (.node 19081 (.node 19079 .nil .nil) (.node 19087 .nil .nil))
      (.node 19141 (.node 19139 .nil .nil) (.node 19157 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree244_checked : NumberTheory.primeTreeChecked subtree244 := by
  norm_num only [subtree244, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree245 : BinaryTree ℕ :=
  .node 18973 subtree243 subtree244

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree245_checked : NumberTheory.primeTreeChecked subtree245 := by
  exact ⟨by norm_num only, subtree243_checked, subtree244_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree246 : BinaryTree ℕ :=
  (.node 19249
    (.node 19213 (.node 19207 (.node 19183 (.node 19181 .nil .nil) .nil) (.node 19211 .nil .nil))
      (.node 19231 (.node 19219 .nil .nil) (.node 19237 .nil .nil)))
    (.node 19289 (.node 19267 (.node 19259 .nil .nil) (.node 19273 .nil .nil))
      (.node 19309 (.node 19301 .nil .nil) (.node 19319 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree246_checked : NumberTheory.primeTreeChecked subtree246 := by
  norm_num only [subtree246, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree247 : BinaryTree ℕ :=
  (.node 19423
    (.node 19391 (.node 19381 (.node 19379 (.node 19373 .nil .nil) .nil) (.node 19387 .nil .nil))
      (.node 19417 (.node 19403 .nil .nil) (.node 19421 .nil .nil)))
    (.node 19441 (.node 19429 (.node 19427 .nil .nil) (.node 19433 .nil .nil))
      (.node 19457 (.node 19447 .nil .nil) (.node 19463 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree247_checked : NumberTheory.primeTreeChecked subtree247 := by
  norm_num only [subtree247, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree248 : BinaryTree ℕ :=
  .node 19333 subtree246 subtree247

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree248_checked : NumberTheory.primeTreeChecked subtree248 := by
  exact ⟨by norm_num only, subtree246_checked, subtree247_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree249 : BinaryTree ℕ :=
  .node 19163 subtree245 subtree248

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree249_checked : NumberTheory.primeTreeChecked subtree249 := by
  exact ⟨by norm_num only, subtree245_checked, subtree248_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree250 : BinaryTree ℕ :=
  .node 18749 subtree242 subtree249

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree250_checked : NumberTheory.primeTreeChecked subtree250 := by
  exact ⟨by norm_num only, subtree242_checked, subtree249_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree251 : BinaryTree ℕ :=
  .node 18061 subtree235 subtree250

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree251_checked : NumberTheory.primeTreeChecked subtree251 := by
  exact ⟨by norm_num only, subtree235_checked, subtree250_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree252 : BinaryTree ℕ :=
  .node 16703 subtree220 subtree251

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree252_checked : NumberTheory.primeTreeChecked subtree252 := by
  exact ⟨by norm_num only, subtree220_checked, subtree251_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree253 : BinaryTree ℕ :=
  .node 14051 subtree189 subtree252

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree253_checked : NumberTheory.primeTreeChecked subtree253 := by
  exact ⟨by norm_num only, subtree189_checked, subtree252_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree254 : BinaryTree ℕ :=
  .node 8863 subtree126 subtree253

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree254_checked : NumberTheory.primeTreeChecked subtree254 := by
  exact ⟨by norm_num only, subtree126_checked, subtree253_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree255 : BinaryTree ℕ :=
  (.node 19543
    (.node 19501 (.node 19483 (.node 19477 (.node 19471 .nil .nil) .nil) (.node 19489 .nil .nil))
      (.node 19531 (.node 19507 .nil .nil) (.node 19541 .nil .nil)))
    (.node 19583 (.node 19571 (.node 19559 (.node 19553 .nil .nil) .nil) (.node 19577 .nil .nil))
      (.node 19603 (.node 19597 .nil .nil) (.node 19609 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree255_checked : NumberTheory.primeTreeChecked subtree255 := by
  norm_num only [subtree255, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree256 : BinaryTree ℕ :=
  (.node 19751
    (.node 19709 (.node 19697 (.node 19687 (.node 19681 .nil .nil) .nil) (.node 19699 .nil .nil))
      (.node 19727 (.node 19717 .nil .nil) (.node 19739 .nil .nil)))
    (.node 19777 (.node 19759 (.node 19753 .nil .nil) (.node 19763 .nil .nil))
      (.node 19801 (.node 19793 .nil .nil) (.node 19813 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree256_checked : NumberTheory.primeTreeChecked subtree256 := by
  norm_num only [subtree256, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree257 : BinaryTree ℕ :=
  .node 19661 subtree255 subtree256

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree257_checked : NumberTheory.primeTreeChecked subtree257 := by
  exact ⟨by norm_num only, subtree255_checked, subtree256_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree258 : BinaryTree ℕ :=
  (.node 19919
    (.node 19867 (.node 19853 (.node 19843 (.node 19841 .nil .nil) .nil) (.node 19861 .nil .nil))
      (.node 19891 (.node 19889 .nil .nil) (.node 19913 .nil .nil)))
    (.node 19961 (.node 19937 (.node 19927 .nil .nil) (.node 19949 .nil .nil))
      (.node 19973 (.node 19963 .nil .nil) (.node 19979 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree258_checked : NumberTheory.primeTreeChecked subtree258 := by
  norm_num only [subtree258, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree259 : BinaryTree ℕ :=
  (.node 20063
    (.node 20023 (.node 20011 (.node 19997 (.node 19993 .nil .nil) .nil) (.node 20021 .nil .nil))
      (.node 20047 (.node 20029 .nil .nil) (.node 20051 .nil .nil)))
    (.node 20107 (.node 20089 (.node 20071 .nil .nil) (.node 20101 .nil .nil))
      (.node 20117 (.node 20113 .nil .nil) (.node 20123 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree259_checked : NumberTheory.primeTreeChecked subtree259 := by
  norm_num only [subtree259, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree260 : BinaryTree ℕ :=
  .node 19991 subtree258 subtree259

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree260_checked : NumberTheory.primeTreeChecked subtree260 := by
  exact ⟨by norm_num only, subtree258_checked, subtree259_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree261 : BinaryTree ℕ :=
  .node 19819 subtree257 subtree260

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree261_checked : NumberTheory.primeTreeChecked subtree261 := by
  exact ⟨by norm_num only, subtree257_checked, subtree260_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree262 : BinaryTree ℕ :=
  (.node 20219
    (.node 20173 (.node 20149 (.node 20147 (.node 20143 .nil .nil) .nil) (.node 20161 .nil .nil))
      (.node 20183 (.node 20177 .nil .nil) (.node 20201 .nil .nil)))
    (.node 20269 (.node 20249 (.node 20233 (.node 20231 .nil .nil) .nil) (.node 20261 .nil .nil))
      (.node 20297 (.node 20287 .nil .nil) (.node 20323 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree262_checked : NumberTheory.primeTreeChecked subtree262 := by
  norm_num only [subtree262, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree263 : BinaryTree ℕ :=
  (.node 20393
    (.node 20357 (.node 20347 (.node 20341 (.node 20333 .nil .nil) .nil) (.node 20353 .nil .nil))
      (.node 20369 (.node 20359 .nil .nil) (.node 20389 .nil .nil)))
    (.node 20431 (.node 20407 (.node 20399 .nil .nil) (.node 20411 .nil .nil))
      (.node 20443 (.node 20441 .nil .nil) (.node 20477 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree263_checked : NumberTheory.primeTreeChecked subtree263 := by
  norm_num only [subtree263, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree264 : BinaryTree ℕ :=
  .node 20327 subtree262 subtree263

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree264_checked : NumberTheory.primeTreeChecked subtree264 := by
  exact ⟨by norm_num only, subtree262_checked, subtree263_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree265 : BinaryTree ℕ :=
  (.node 20563
    (.node 20533 (.node 20509 (.node 20507 (.node 20483 .nil .nil) .nil) (.node 20521 .nil .nil))
      (.node 20549 (.node 20543 .nil .nil) (.node 20551 .nil .nil)))
    (.node 20627 (.node 20599 (.node 20593 .nil .nil) (.node 20611 .nil .nil))
      (.node 20641 (.node 20639 .nil .nil) (.node 20663 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree265_checked : NumberTheory.primeTreeChecked subtree265 := by
  norm_num only [subtree265, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree266 : BinaryTree ℕ :=
  (.node 20753
    (.node 20731 (.node 20717 (.node 20707 (.node 20693 .nil .nil) .nil) (.node 20719 .nil .nil))
      (.node 20747 (.node 20743 .nil .nil) (.node 20749 .nil .nil)))
    (.node 20789 (.node 20771 (.node 20759 .nil .nil) (.node 20773 .nil .nil))
      (.node 20809 (.node 20807 .nil .nil) (.node 20849 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree266_checked : NumberTheory.primeTreeChecked subtree266 := by
  norm_num only [subtree266, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree267 : BinaryTree ℕ :=
  .node 20681 subtree265 subtree266

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree267_checked : NumberTheory.primeTreeChecked subtree267 := by
  exact ⟨by norm_num only, subtree265_checked, subtree266_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree268 : BinaryTree ℕ :=
  .node 20479 subtree264 subtree267

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree268_checked : NumberTheory.primeTreeChecked subtree268 := by
  exact ⟨by norm_num only, subtree264_checked, subtree267_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree269 : BinaryTree ℕ :=
  .node 20129 subtree261 subtree268

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree269_checked : NumberTheory.primeTreeChecked subtree269 := by
  exact ⟨by norm_num only, subtree261_checked, subtree268_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree270 : BinaryTree ℕ :=
  (.node 20939
    (.node 20899 (.node 20887 (.node 20879 (.node 20873 .nil .nil) .nil) (.node 20897 .nil .nil))
      (.node 20921 (.node 20903 .nil .nil) (.node 20929 .nil .nil)))
    (.node 20983 (.node 20963 (.node 20959 (.node 20947 .nil .nil) .nil) (.node 20981 .nil .nil))
      (.node 21011 (.node 21001 .nil .nil) (.node 21013 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree270_checked : NumberTheory.primeTreeChecked subtree270 := by
  norm_num only [subtree270, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree271 : BinaryTree ℕ :=
  (.node 21107
    (.node 21061 (.node 21031 (.node 21023 (.node 21019 .nil .nil) .nil) (.node 21059 .nil .nil))
      (.node 21089 (.node 21067 .nil .nil) (.node 21101 .nil .nil)))
    (.node 21149 (.node 21139 (.node 21121 .nil .nil) (.node 21143 .nil .nil))
      (.node 21163 (.node 21157 .nil .nil) (.node 21169 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree271_checked : NumberTheory.primeTreeChecked subtree271 := by
  norm_num only [subtree271, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree272 : BinaryTree ℕ :=
  .node 21017 subtree270 subtree271

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree272_checked : NumberTheory.primeTreeChecked subtree272 := by
  exact ⟨by norm_num only, subtree270_checked, subtree271_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree273 : BinaryTree ℕ :=
  (.node 21277
    (.node 21221 (.node 21193 (.node 21191 (.node 21187 .nil .nil) .nil) (.node 21211 .nil .nil))
      (.node 21247 (.node 21227 .nil .nil) (.node 21269 .nil .nil)))
    (.node 21319 (.node 21313 (.node 21283 .nil .nil) (.node 21317 .nil .nil))
      (.node 21341 (.node 21323 .nil .nil) (.node 21347 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree273_checked : NumberTheory.primeTreeChecked subtree273 := by
  norm_num only [subtree273, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree274 : BinaryTree ℕ :=
  (.node 21467
    (.node 21401 (.node 21391 (.node 21383 (.node 21379 .nil .nil) .nil) (.node 21397 .nil .nil))
      (.node 21419 (.node 21407 .nil .nil) (.node 21433 .nil .nil)))
    (.node 21493 (.node 21487 (.node 21481 .nil .nil) (.node 21491 .nil .nil))
      (.node 21503 (.node 21499 .nil .nil) (.node 21517 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree274_checked : NumberTheory.primeTreeChecked subtree274 := by
  norm_num only [subtree274, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree275 : BinaryTree ℕ :=
  .node 21377 subtree273 subtree274

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree275_checked : NumberTheory.primeTreeChecked subtree275 := by
  exact ⟨by norm_num only, subtree273_checked, subtree274_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree276 : BinaryTree ℕ :=
  .node 21179 subtree272 subtree275

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree276_checked : NumberTheory.primeTreeChecked subtree276 := by
  exact ⟨by norm_num only, subtree272_checked, subtree275_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree277 : BinaryTree ℕ :=
  (.node 21589
    (.node 21563 (.node 21557 (.node 21529 (.node 21523 .nil .nil) .nil) (.node 21559 .nil .nil))
      (.node 21577 (.node 21569 .nil .nil) (.node 21587 .nil .nil)))
    (.node 21617 (.node 21611 (.node 21601 (.node 21599 .nil .nil) .nil) (.node 21613 .nil .nil))
      (.node 21649 (.node 21647 .nil .nil) (.node 21661 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree277_checked : NumberTheory.primeTreeChecked subtree277 := by
  norm_num only [subtree277, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree278 : BinaryTree ℕ :=
  (.node 21767
    (.node 21737 (.node 21713 (.node 21701 (.node 21683 .nil .nil) .nil) (.node 21727 .nil .nil))
      (.node 21751 (.node 21739 .nil .nil) (.node 21757 .nil .nil)))
    (.node 21803 (.node 21787 (.node 21773 .nil .nil) (.node 21799 .nil .nil))
      (.node 21821 (.node 21817 .nil .nil) (.node 21839 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree278_checked : NumberTheory.primeTreeChecked subtree278 := by
  norm_num only [subtree278, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree279 : BinaryTree ℕ :=
  .node 21673 subtree277 subtree278

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree279_checked : NumberTheory.primeTreeChecked subtree279 := by
  exact ⟨by norm_num only, subtree277_checked, subtree278_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree280 : BinaryTree ℕ :=
  (.node 21937
    (.node 21881 (.node 21863 (.node 21859 (.node 21851 .nil .nil) .nil) (.node 21871 .nil .nil))
      (.node 21911 (.node 21893 .nil .nil) (.node 21929 .nil .nil)))
    (.node 21991 (.node 21961 (.node 21943 .nil .nil) (.node 21977 .nil .nil))
      (.node 22003 (.node 21997 .nil .nil) (.node 22013 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree280_checked : NumberTheory.primeTreeChecked subtree280 := by
  norm_num only [subtree280, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree281 : BinaryTree ℕ :=
  (.node 22091
    (.node 22063 (.node 22039 (.node 22037 (.node 22031 .nil .nil) .nil) (.node 22051 .nil .nil))
      (.node 22073 (.node 22067 .nil .nil) (.node 22079 .nil .nil)))
    (.node 22123 (.node 22109 (.node 22093 .nil .nil) (.node 22111 .nil .nil))
      (.node 22133 (.node 22129 .nil .nil) (.node 22147 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree281_checked : NumberTheory.primeTreeChecked subtree281 := by
  norm_num only [subtree281, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree282 : BinaryTree ℕ :=
  .node 22027 subtree280 subtree281

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree282_checked : NumberTheory.primeTreeChecked subtree282 := by
  exact ⟨by norm_num only, subtree280_checked, subtree281_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree283 : BinaryTree ℕ :=
  .node 21841 subtree279 subtree282

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree283_checked : NumberTheory.primeTreeChecked subtree283 := by
  exact ⟨by norm_num only, subtree279_checked, subtree282_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree284 : BinaryTree ℕ :=
  .node 21521 subtree276 subtree283

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree284_checked : NumberTheory.primeTreeChecked subtree284 := by
  exact ⟨by norm_num only, subtree276_checked, subtree283_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree285 : BinaryTree ℕ :=
  .node 20857 subtree269 subtree284

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree285_checked : NumberTheory.primeTreeChecked subtree285 := by
  exact ⟨by norm_num only, subtree269_checked, subtree284_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree286 : BinaryTree ℕ :=
  (.node 22271
    (.node 22193 (.node 22171 (.node 22159 (.node 22157 .nil .nil) .nil) (.node 22189 .nil .nil))
      (.node 22247 (.node 22229 .nil .nil) (.node 22259 .nil .nil)))
    (.node 22291 (.node 22279 (.node 22277 (.node 22273 .nil .nil) .nil) (.node 22283 .nil .nil))
      (.node 22307 (.node 22303 .nil .nil) (.node 22343 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree286_checked : NumberTheory.primeTreeChecked subtree286 := by
  norm_num only [subtree286, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree287 : BinaryTree ℕ :=
  (.node 22447
    (.node 22397 (.node 22381 (.node 22369 (.node 22367 .nil .nil) .nil) (.node 22391 .nil .nil))
      (.node 22433 (.node 22409 .nil .nil) (.node 22441 .nil .nil)))
    (.node 22483 (.node 22469 (.node 22453 .nil .nil) (.node 22481 .nil .nil))
      (.node 22511 (.node 22501 .nil .nil) (.node 22531 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree287_checked : NumberTheory.primeTreeChecked subtree287 := by
  norm_num only [subtree287, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree288 : BinaryTree ℕ :=
  .node 22349 subtree286 subtree287

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree288_checked : NumberTheory.primeTreeChecked subtree288 := by
  exact ⟨by norm_num only, subtree286_checked, subtree287_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree289 : BinaryTree ℕ :=
  (.node 22637
    (.node 22573 (.node 22567 (.node 22549 (.node 22543 .nil .nil) .nil) (.node 22571 .nil .nil))
      (.node 22619 (.node 22613 .nil .nil) (.node 22621 .nil .nil)))
    (.node 22669 (.node 22643 (.node 22639 .nil .nil) (.node 22651 .nil .nil))
      (.node 22691 (.node 22679 .nil .nil) (.node 22697 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree289_checked : NumberTheory.primeTreeChecked subtree289 := by
  norm_num only [subtree289, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree290 : BinaryTree ℕ :=
  (.node 22777
    (.node 22739 (.node 22721 (.node 22717 (.node 22709 .nil .nil) .nil) (.node 22727 .nil .nil))
      (.node 22751 (.node 22741 .nil .nil) (.node 22769 .nil .nil)))
    (.node 22811 (.node 22787 (.node 22783 .nil .nil) (.node 22807 .nil .nil))
      (.node 22853 (.node 22817 .nil .nil) (.node 22859 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree290_checked : NumberTheory.primeTreeChecked subtree290 := by
  norm_num only [subtree290, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree291 : BinaryTree ℕ :=
  .node 22699 subtree289 subtree290

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree291_checked : NumberTheory.primeTreeChecked subtree291 := by
  exact ⟨by norm_num only, subtree289_checked, subtree290_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree292 : BinaryTree ℕ :=
  .node 22541 subtree288 subtree291

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree292_checked : NumberTheory.primeTreeChecked subtree292 := by
  exact ⟨by norm_num only, subtree288_checked, subtree291_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree293 : BinaryTree ℕ :=
  (.node 22963
    (.node 22921 (.node 22901 (.node 22877 (.node 22871 .nil .nil) .nil) (.node 22907 .nil .nil))
      (.node 22943 (.node 22937 .nil .nil) (.node 22961 .nil .nil)))
    (.node 23017 (.node 23003 (.node 22993 (.node 22973 .nil .nil) .nil) (.node 23011 .nil .nil))
      (.node 23027 (.node 23021 .nil .nil) (.node 23029 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree293_checked : NumberTheory.primeTreeChecked subtree293 := by
  norm_num only [subtree293, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree294 : BinaryTree ℕ :=
  (.node 23099
    (.node 23063 (.node 23057 (.node 23053 (.node 23041 .nil .nil) .nil) (.node 23059 .nil .nil))
      (.node 23081 (.node 23071 .nil .nil) (.node 23087 .nil .nil)))
    (.node 23159 (.node 23131 (.node 23117 .nil .nil) (.node 23143 .nil .nil))
      (.node 23173 (.node 23167 .nil .nil) (.node 23189 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree294_checked : NumberTheory.primeTreeChecked subtree294 := by
  norm_num only [subtree294, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree295 : BinaryTree ℕ :=
  .node 23039 subtree293 subtree294

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree295_checked : NumberTheory.primeTreeChecked subtree295 := by
  exact ⟨by norm_num only, subtree293_checked, subtree294_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree296 : BinaryTree ℕ :=
  (.node 23293
    (.node 23251 (.node 23209 (.node 23203 (.node 23201 .nil .nil) .nil) (.node 23227 .nil .nil))
      (.node 23279 (.node 23269 .nil .nil) (.node 23291 .nil .nil)))
    (.node 23327 (.node 23311 (.node 23297 .nil .nil) (.node 23321 .nil .nil))
      (.node 23339 (.node 23333 .nil .nil) (.node 23357 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree296_checked : NumberTheory.primeTreeChecked subtree296 := by
  norm_num only [subtree296, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree297 : BinaryTree ℕ :=
  (.node 23509
    (.node 23447 (.node 23417 (.node 23399 (.node 23371 .nil .nil) .nil) (.node 23431 .nil .nil))
      (.node 23473 (.node 23459 .nil .nil) (.node 23497 .nil .nil)))
    (.node 23549 (.node 23537 (.node 23531 .nil .nil) (.node 23539 .nil .nil))
      (.node 23561 (.node 23557 .nil .nil) (.node 23563 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree297_checked : NumberTheory.primeTreeChecked subtree297 := by
  norm_num only [subtree297, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree298 : BinaryTree ℕ :=
  .node 23369 subtree296 subtree297

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree298_checked : NumberTheory.primeTreeChecked subtree298 := by
  exact ⟨by norm_num only, subtree296_checked, subtree297_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree299 : BinaryTree ℕ :=
  .node 23197 subtree295 subtree298

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree299_checked : NumberTheory.primeTreeChecked subtree299 := by
  exact ⟨by norm_num only, subtree295_checked, subtree298_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree300 : BinaryTree ℕ :=
  .node 22861 subtree292 subtree299

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree300_checked : NumberTheory.primeTreeChecked subtree300 := by
  exact ⟨by norm_num only, subtree292_checked, subtree299_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree301 : BinaryTree ℕ :=
  (.node 23633
    (.node 23609 (.node 23599 (.node 23593 (.node 23581 .nil .nil) .nil) (.node 23603 .nil .nil))
      (.node 23627 (.node 23623 .nil .nil) (.node 23629 .nil .nil)))
    (.node 23687 (.node 23671 (.node 23669 (.node 23663 .nil .nil) .nil) (.node 23677 .nil .nil))
      (.node 23719 (.node 23689 .nil .nil) (.node 23741 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree301_checked : NumberTheory.primeTreeChecked subtree301 := by
  norm_num only [subtree301, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree302 : BinaryTree ℕ :=
  (.node 23819
    (.node 23773 (.node 23761 (.node 23753 (.node 23747 .nil .nil) .nil) (.node 23767 .nil .nil))
      (.node 23801 (.node 23789 .nil .nil) (.node 23813 .nil .nil)))
    (.node 23857 (.node 23831 (.node 23827 .nil .nil) (.node 23833 .nil .nil))
      (.node 23873 (.node 23869 .nil .nil) (.node 23879 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree302_checked : NumberTheory.primeTreeChecked subtree302 := by
  norm_num only [subtree302, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree303 : BinaryTree ℕ :=
  .node 23743 subtree301 subtree302

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree303_checked : NumberTheory.primeTreeChecked subtree303 := by
  exact ⟨by norm_num only, subtree301_checked, subtree302_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree304 : BinaryTree ℕ :=
  (.node 23977
    (.node 23917 (.node 23909 (.node 23899 (.node 23893 .nil .nil) .nil) (.node 23911 .nil .nil))
      (.node 23957 (.node 23929 .nil .nil) (.node 23971 .nil .nil)))
    (.node 24007 (.node 23993 (.node 23981 .nil .nil) (.node 24001 .nil .nil))
      (.node 24023 (.node 24019 .nil .nil) (.node 24029 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree304_checked : NumberTheory.primeTreeChecked subtree304 := by
  norm_num only [subtree304, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree305 : BinaryTree ℕ :=
  (.node 24107
    (.node 24083 (.node 24071 (.node 24061 (.node 24049 .nil .nil) .nil) (.node 24077 .nil .nil))
      (.node 24097 (.node 24091 .nil .nil) (.node 24103 .nil .nil)))
    (.node 24133 (.node 24113 (.node 24109 .nil .nil) (.node 24121 .nil .nil))
      (.node 24151 (.node 24137 .nil .nil) (.node 24169 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree305_checked : NumberTheory.primeTreeChecked subtree305 := by
  norm_num only [subtree305, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree306 : BinaryTree ℕ :=
  .node 24043 subtree304 subtree305

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree306_checked : NumberTheory.primeTreeChecked subtree306 := by
  exact ⟨by norm_num only, subtree304_checked, subtree305_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree307 : BinaryTree ℕ :=
  .node 23887 subtree303 subtree306

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree307_checked : NumberTheory.primeTreeChecked subtree307 := by
  exact ⟨by norm_num only, subtree303_checked, subtree306_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree308 : BinaryTree ℕ :=
  (.node 24281
    (.node 24229 (.node 24203 (.node 24197 (.node 24181 .nil .nil) .nil) (.node 24223 .nil .nil))
      (.node 24247 (.node 24239 .nil .nil) (.node 24251 .nil .nil)))
    (.node 24371 (.node 24337 (.node 24329 (.node 24317 .nil .nil) .nil) (.node 24359 .nil .nil))
      (.node 24379 (.node 24373 .nil .nil) (.node 24391 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree308_checked : NumberTheory.primeTreeChecked subtree308 := by
  norm_num only [subtree308, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree309 : BinaryTree ℕ :=
  (.node 24499
    (.node 24443 (.node 24421 (.node 24419 (.node 24413 .nil .nil) .nil) (.node 24439 .nil .nil))
      (.node 24473 (.node 24469 .nil .nil) (.node 24481 .nil .nil)))
    (.node 24533 (.node 24517 (.node 24509 .nil .nil) (.node 24527 .nil .nil))
      (.node 24551 (.node 24547 .nil .nil) (.node 24571 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree309_checked : NumberTheory.primeTreeChecked subtree309 := by
  norm_num only [subtree309, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree310 : BinaryTree ℕ :=
  .node 24407 subtree308 subtree309

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree310_checked : NumberTheory.primeTreeChecked subtree310 := by
  exact ⟨by norm_num only, subtree308_checked, subtree309_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree311 : BinaryTree ℕ :=
  (.node 24697
    (.node 24671 (.node 24631 (.node 24623 (.node 24611 .nil .nil) .nil) (.node 24659 .nil .nil))
      (.node 24683 (.node 24677 .nil .nil) (.node 24691 .nil .nil)))
    (.node 24763 (.node 24733 (.node 24709 .nil .nil) (.node 24749 .nil .nil))
      (.node 24781 (.node 24767 .nil .nil) (.node 24793 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree311_checked : NumberTheory.primeTreeChecked subtree311 := by
  norm_num only [subtree311, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree312 : BinaryTree ℕ :=
  (.node 24907
    (.node 24851 (.node 24841 (.node 24821 (.node 24809 .nil .nil) .nil) (.node 24847 .nil .nil))
      (.node 24877 (.node 24859 .nil .nil) (.node 24889 .nil .nil)))
    (.node 24943 (.node 24919 (.node 24917 .nil .nil) (.node 24923 .nil .nil))
      (.node 24967 (.node 24953 .nil .nil) (.node 24971 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree312_checked : NumberTheory.primeTreeChecked subtree312 := by
  norm_num only [subtree312, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree313 : BinaryTree ℕ :=
  .node 24799 subtree311 subtree312

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree313_checked : NumberTheory.primeTreeChecked subtree313 := by
  exact ⟨by norm_num only, subtree311_checked, subtree312_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree314 : BinaryTree ℕ :=
  .node 24593 subtree310 subtree313

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree314_checked : NumberTheory.primeTreeChecked subtree314 := by
  exact ⟨by norm_num only, subtree310_checked, subtree313_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree315 : BinaryTree ℕ :=
  .node 24179 subtree307 subtree314

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree315_checked : NumberTheory.primeTreeChecked subtree315 := by
  exact ⟨by norm_num only, subtree307_checked, subtree314_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree316 : BinaryTree ℕ :=
  .node 23567 subtree300 subtree315

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree316_checked : NumberTheory.primeTreeChecked subtree316 := by
  exact ⟨by norm_num only, subtree300_checked, subtree315_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree317 : BinaryTree ℕ :=
  .node 22153 subtree285 subtree316

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree317_checked : NumberTheory.primeTreeChecked subtree317 := by
  exact ⟨by norm_num only, subtree285_checked, subtree316_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree318 : BinaryTree ℕ :=
  (.node 25087
    (.node 25033 (.node 25013 (.node 24989 (.node 24979 .nil .nil) .nil) (.node 25031 .nil .nil))
      (.node 25057 (.node 25037 .nil .nil) (.node 25073 .nil .nil)))
    (.node 25127 (.node 25117 (.node 25111 (.node 25097 .nil .nil) .nil) (.node 25121 .nil .nil))
      (.node 25153 (.node 25147 .nil .nil) (.node 25163 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree318_checked : NumberTheory.primeTreeChecked subtree318 := by
  norm_num only [subtree318, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree319 : BinaryTree ℕ :=
  (.node 25253
    (.node 25229 (.node 25189 (.node 25183 (.node 25171 .nil .nil) .nil) (.node 25219 .nil .nil))
      (.node 25243 (.node 25237 .nil .nil) (.node 25247 .nil .nil)))
    (.node 25307 (.node 25301 (.node 25261 .nil .nil) (.node 25303 .nil .nil))
      (.node 25321 (.node 25309 .nil .nil) (.node 25339 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree319_checked : NumberTheory.primeTreeChecked subtree319 := by
  norm_num only [subtree319, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree320 : BinaryTree ℕ :=
  .node 25169 subtree318 subtree319

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree320_checked : NumberTheory.primeTreeChecked subtree320 := by
  exact ⟨by norm_num only, subtree318_checked, subtree319_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree321 : BinaryTree ℕ :=
  (.node 25439
    (.node 25391 (.node 25367 (.node 25357 (.node 25349 .nil .nil) .nil) (.node 25373 .nil .nil))
      (.node 25411 (.node 25409 .nil .nil) (.node 25423 .nil .nil)))
    (.node 25463 (.node 25453 (.node 25447 .nil .nil) (.node 25457 .nil .nil))
      (.node 25471 (.node 25469 .nil .nil) (.node 25523 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree321_checked : NumberTheory.primeTreeChecked subtree321 := by
  norm_num only [subtree321, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree322 : BinaryTree ℕ :=
  (.node 25609
    (.node 25583 (.node 25577 (.node 25561 (.node 25541 .nil .nil) .nil) (.node 25579 .nil .nil))
      (.node 25601 (.node 25589 .nil .nil) (.node 25603 .nil .nil)))
    (.node 25643 (.node 25633 (.node 25621 .nil .nil) (.node 25639 .nil .nil))
      (.node 25667 (.node 25657 .nil .nil) (.node 25673 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree322_checked : NumberTheory.primeTreeChecked subtree322 := by
  norm_num only [subtree322, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree323 : BinaryTree ℕ :=
  .node 25537 subtree321 subtree322

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree323_checked : NumberTheory.primeTreeChecked subtree323 := by
  exact ⟨by norm_num only, subtree321_checked, subtree322_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree324 : BinaryTree ℕ :=
  .node 25343 subtree320 subtree323

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree324_checked : NumberTheory.primeTreeChecked subtree324 := by
  exact ⟨by norm_num only, subtree320_checked, subtree323_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree325 : BinaryTree ℕ :=
  (.node 25771
    (.node 25741 (.node 25717 (.node 25703 (.node 25693 .nil .nil) .nil) (.node 25733 .nil .nil))
      (.node 25759 (.node 25747 .nil .nil) (.node 25763 .nil .nil)))
    (.node 25841 (.node 25801 (.node 25799 (.node 25793 .nil .nil) .nil) (.node 25819 .nil .nil))
      (.node 25849 (.node 25847 .nil .nil) (.node 25867 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree325_checked : NumberTheory.primeTreeChecked subtree325 := by
  norm_num only [subtree325, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree326 : BinaryTree ℕ :=
  (.node 25951
    (.node 25931 (.node 25913 (.node 25903 (.node 25889 .nil .nil) .nil) (.node 25919 .nil .nil))
      (.node 25939 (.node 25933 .nil .nil) (.node 25943 .nil .nil)))
    (.node 25999 (.node 25981 (.node 25969 .nil .nil) (.node 25997 .nil .nil))
      (.node 26017 (.node 26003 .nil .nil) (.node 26021 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree326_checked : NumberTheory.primeTreeChecked subtree326 := by
  norm_num only [subtree326, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree327 : BinaryTree ℕ :=
  .node 25873 subtree325 subtree326

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree327_checked : NumberTheory.primeTreeChecked subtree327 := by
  exact ⟨by norm_num only, subtree325_checked, subtree326_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree328 : BinaryTree ℕ :=
  (.node 26141
    (.node 26107 (.node 26083 (.node 26053 (.node 26041 .nil .nil) .nil) (.node 26099 .nil .nil))
      (.node 26113 (.node 26111 .nil .nil) (.node 26119 .nil .nil)))
    (.node 26177 (.node 26161 (.node 26153 .nil .nil) (.node 26171 .nil .nil))
      (.node 26189 (.node 26183 .nil .nil) (.node 26203 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree328_checked : NumberTheory.primeTreeChecked subtree328 := by
  norm_num only [subtree328, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree329 : BinaryTree ℕ :=
  (.node 26297
    (.node 26261 (.node 26249 (.node 26237 (.node 26227 .nil .nil) .nil) (.node 26251 .nil .nil))
      (.node 26267 (.node 26263 .nil .nil) (.node 26293 .nil .nil)))
    (.node 26339 (.node 26317 (.node 26309 .nil .nil) (.node 26321 .nil .nil))
      (.node 26357 (.node 26347 .nil .nil) (.node 26371 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree329_checked : NumberTheory.primeTreeChecked subtree329 := by
  norm_num only [subtree329, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree330 : BinaryTree ℕ :=
  .node 26209 subtree328 subtree329

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree330_checked : NumberTheory.primeTreeChecked subtree330 := by
  exact ⟨by norm_num only, subtree328_checked, subtree329_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree331 : BinaryTree ℕ :=
  .node 26029 subtree327 subtree330

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree331_checked : NumberTheory.primeTreeChecked subtree331 := by
  exact ⟨by norm_num only, subtree327_checked, subtree330_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree332 : BinaryTree ℕ :=
  .node 25679 subtree324 subtree331

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree332_checked : NumberTheory.primeTreeChecked subtree332 := by
  exact ⟨by norm_num only, subtree324_checked, subtree331_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree333 : BinaryTree ℕ :=
  (.node 26459
    (.node 26423 (.node 26407 (.node 26399 (.node 26393 .nil .nil) .nil) (.node 26417 .nil .nil))
      (.node 26437 (.node 26431 .nil .nil) (.node 26449 .nil .nil)))
    (.node 26513 (.node 26497 (.node 26489 (.node 26479 .nil .nil) .nil) (.node 26501 .nil .nil))
      (.node 26557 (.node 26539 .nil .nil) (.node 26561 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree333_checked : NumberTheory.primeTreeChecked subtree333 := by
  norm_num only [subtree333, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree334 : BinaryTree ℕ :=
  (.node 26683
    (.node 26641 (.node 26627 (.node 26597 (.node 26591 .nil .nil) .nil) (.node 26633 .nil .nil))
      (.node 26669 (.node 26647 .nil .nil) (.node 26681 .nil .nil)))
    (.node 26701 (.node 26693 (.node 26687 .nil .nil) (.node 26699 .nil .nil))
      (.node 26713 (.node 26711 .nil .nil) (.node 26717 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree334_checked : NumberTheory.primeTreeChecked subtree334 := by
  norm_num only [subtree334, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree335 : BinaryTree ℕ :=
  .node 26573 subtree333 subtree334

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree335_checked : NumberTheory.primeTreeChecked subtree335 := by
  exact ⟨by norm_num only, subtree333_checked, subtree334_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree336 : BinaryTree ℕ :=
  (.node 26821
    (.node 26777 (.node 26737 (.node 26731 (.node 26729 .nil .nil) .nil) (.node 26759 .nil .nil))
      (.node 26801 (.node 26783 .nil .nil) (.node 26813 .nil .nil)))
    (.node 26861 (.node 26839 (.node 26833 .nil .nil) (.node 26849 .nil .nil))
      (.node 26879 (.node 26863 .nil .nil) (.node 26881 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree336_checked : NumberTheory.primeTreeChecked subtree336 := by
  norm_num only [subtree336, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree337 : BinaryTree ℕ :=
  (.node 26981
    (.node 26947 (.node 26921 (.node 26903 (.node 26893 .nil .nil) .nil) (.node 26927 .nil .nil))
      (.node 26953 (.node 26951 .nil .nil) (.node 26959 .nil .nil)))
    (.node 27017 (.node 26993 (.node 26987 .nil .nil) (.node 27011 .nil .nil))
      (.node 27043 (.node 27031 .nil .nil) (.node 27059 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree337_checked : NumberTheory.primeTreeChecked subtree337 := by
  norm_num only [subtree337, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree338 : BinaryTree ℕ :=
  .node 26891 subtree336 subtree337

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree338_checked : NumberTheory.primeTreeChecked subtree338 := by
  exact ⟨by norm_num only, subtree336_checked, subtree337_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree339 : BinaryTree ℕ :=
  .node 26723 subtree335 subtree338

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree339_checked : NumberTheory.primeTreeChecked subtree339 := by
  exact ⟨by norm_num only, subtree335_checked, subtree338_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree340 : BinaryTree ℕ :=
  (.node 27143
    (.node 27103 (.node 27077 (.node 27073 (.node 27067 .nil .nil) .nil) (.node 27091 .nil .nil))
      (.node 27109 (.node 27107 .nil .nil) (.node 27127 .nil .nil)))
    (.node 27239 (.node 27197 (.node 27191 (.node 27179 .nil .nil) .nil) (.node 27211 .nil .nil))
      (.node 27253 (.node 27241 .nil .nil) (.node 27259 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree340_checked : NumberTheory.primeTreeChecked subtree340 := by
  norm_num only [subtree340, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree341 : BinaryTree ℕ :=
  (.node 27397
    (.node 27329 (.node 27283 (.node 27281 (.node 27277 .nil .nil) .nil) (.node 27299 .nil .nil))
      (.node 27361 (.node 27337 .nil .nil) (.node 27367 .nil .nil)))
    (.node 27431 (.node 27409 (.node 27407 .nil .nil) (.node 27427 .nil .nil))
      (.node 27449 (.node 27437 .nil .nil) (.node 27457 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree341_checked : NumberTheory.primeTreeChecked subtree341 := by
  norm_num only [subtree341, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree342 : BinaryTree ℕ :=
  .node 27271 subtree340 subtree341

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree342_checked : NumberTheory.primeTreeChecked subtree342 := by
  exact ⟨by norm_num only, subtree340_checked, subtree341_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree343 : BinaryTree ℕ :=
  (.node 27581
    (.node 27529 (.node 27509 (.node 27487 (.node 27481 .nil .nil) .nil) (.node 27527 .nil .nil))
      (.node 27541 (.node 27539 .nil .nil) (.node 27551 .nil .nil)))
    (.node 27631 (.node 27611 (.node 27583 .nil .nil) (.node 27617 .nil .nil))
      (.node 27653 (.node 27647 .nil .nil) (.node 27673 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree343_checked : NumberTheory.primeTreeChecked subtree343 := by
  norm_num only [subtree343, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree344 : BinaryTree ℕ :=
  (.node 27763
    (.node 27739 (.node 27701 (.node 27697 (.node 27691 .nil .nil) .nil) (.node 27737 .nil .nil))
      (.node 27749 (.node 27743 .nil .nil) (.node 27751 .nil .nil)))
    (.node 27791 (.node 27773 (.node 27767 .nil .nil) (.node 27779 .nil .nil))
      (.node 27799 (.node 27793 .nil .nil) (.node 27803 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree344_checked : NumberTheory.primeTreeChecked subtree344 := by
  norm_num only [subtree344, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree345 : BinaryTree ℕ :=
  .node 27689 subtree343 subtree344

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree345_checked : NumberTheory.primeTreeChecked subtree345 := by
  exact ⟨by norm_num only, subtree343_checked, subtree344_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree346 : BinaryTree ℕ :=
  .node 27479 subtree342 subtree345

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree346_checked : NumberTheory.primeTreeChecked subtree346 := by
  exact ⟨by norm_num only, subtree342_checked, subtree345_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree347 : BinaryTree ℕ :=
  .node 27061 subtree339 subtree346

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree347_checked : NumberTheory.primeTreeChecked subtree347 := by
  exact ⟨by norm_num only, subtree339_checked, subtree346_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree348 : BinaryTree ℕ :=
  .node 26387 subtree332 subtree347

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree348_checked : NumberTheory.primeTreeChecked subtree348 := by
  exact ⟨by norm_num only, subtree332_checked, subtree347_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree349 : BinaryTree ℕ :=
  (.node 27919
    (.node 27883 (.node 27847 (.node 27823 (.node 27817 .nil .nil) .nil) (.node 27851 .nil .nil))
      (.node 27901 (.node 27893 .nil .nil) (.node 27917 .nil .nil)))
    (.node 27961 (.node 27947 (.node 27943 (.node 27941 .nil .nil) .nil) (.node 27953 .nil .nil))
      (.node 27983 (.node 27967 .nil .nil) (.node 27997 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree349_checked : NumberTheory.primeTreeChecked subtree349 := by
  norm_num only [subtree349, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree350 : BinaryTree ℕ :=
  (.node 28099
    (.node 28069 (.node 28031 (.node 28027 (.node 28019 .nil .nil) .nil) (.node 28051 .nil .nil))
      (.node 28087 (.node 28081 .nil .nil) (.node 28097 .nil .nil)))
    (.node 28151 (.node 28111 (.node 28109 .nil .nil) (.node 28123 .nil .nil))
      (.node 28181 (.node 28163 .nil .nil) (.node 28183 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree350_checked : NumberTheory.primeTreeChecked subtree350 := by
  norm_num only [subtree350, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree351 : BinaryTree ℕ :=
  .node 28001 subtree349 subtree350

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree351_checked : NumberTheory.primeTreeChecked subtree351 := by
  exact ⟨by norm_num only, subtree349_checked, subtree350_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree352 : BinaryTree ℕ :=
  (.node 28307
    (.node 28279 (.node 28229 (.node 28219 (.node 28211 .nil .nil) .nil) (.node 28277 .nil .nil))
      (.node 28289 (.node 28283 .nil .nil) (.node 28297 .nil .nil)))
    (.node 28351 (.node 28319 (.node 28309 .nil .nil) (.node 28349 .nil .nil))
      (.node 28403 (.node 28387 .nil .nil) (.node 28409 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree352_checked : NumberTheory.primeTreeChecked subtree352 := by
  norm_num only [subtree352, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree353 : BinaryTree ℕ :=
  (.node 28513
    (.node 28463 (.node 28439 (.node 28433 (.node 28429 .nil .nil) .nil) (.node 28447 .nil .nil))
      (.node 28493 (.node 28477 .nil .nil) (.node 28499 .nil .nil)))
    (.node 28547 (.node 28537 (.node 28517 .nil .nil) (.node 28541 .nil .nil))
      (.node 28559 (.node 28549 .nil .nil) (.node 28571 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree353_checked : NumberTheory.primeTreeChecked subtree353 := by
  norm_num only [subtree353, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree354 : BinaryTree ℕ :=
  .node 28411 subtree352 subtree353

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree354_checked : NumberTheory.primeTreeChecked subtree354 := by
  exact ⟨by norm_num only, subtree352_checked, subtree353_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree355 : BinaryTree ℕ :=
  .node 28201 subtree351 subtree354

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree355_checked : NumberTheory.primeTreeChecked subtree355 := by
  exact ⟨by norm_num only, subtree351_checked, subtree354_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree356 : BinaryTree ℕ :=
  (.node 28631
    (.node 28607 (.node 28597 (.node 28591 (.node 28579 .nil .nil) .nil) (.node 28603 .nil .nil))
      (.node 28621 (.node 28619 .nil .nil) (.node 28627 .nil .nil)))
    (.node 28663 (.node 28657 (.node 28649 (.node 28643 .nil .nil) .nil) (.node 28661 .nil .nil))
      (.node 28687 (.node 28669 .nil .nil) (.node 28697 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree356_checked : NumberTheory.primeTreeChecked subtree356 := by
  norm_num only [subtree356, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree357 : BinaryTree ℕ :=
  (.node 28793
    (.node 28753 (.node 28729 (.node 28723 (.node 28711 .nil .nil) .nil) (.node 28751 .nil .nil))
      (.node 28771 (.node 28759 .nil .nil) (.node 28789 .nil .nil)))
    (.node 28837 (.node 28813 (.node 28807 .nil .nil) (.node 28817 .nil .nil))
      (.node 28859 (.node 28843 .nil .nil) (.node 28867 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree357_checked : NumberTheory.primeTreeChecked subtree357 := by
  norm_num only [subtree357, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree358 : BinaryTree ℕ :=
  .node 28703 subtree356 subtree357

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree358_checked : NumberTheory.primeTreeChecked subtree358 := by
  exact ⟨by norm_num only, subtree356_checked, subtree357_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree359 : BinaryTree ℕ :=
  (.node 28979
    (.node 28927 (.node 28909 (.node 28901 (.node 28879 .nil .nil) .nil) (.node 28921 .nil .nil))
      (.node 28949 (.node 28933 .nil .nil) (.node 28961 .nil .nil)))
    (.node 29023 (.node 29017 (.node 29009 .nil .nil) (.node 29021 .nil .nil))
      (.node 29033 (.node 29027 .nil .nil) (.node 29059 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree359_checked : NumberTheory.primeTreeChecked subtree359 := by
  norm_num only [subtree359, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree360 : BinaryTree ℕ :=
  (.node 29167
    (.node 29131 (.node 29123 (.node 29101 (.node 29077 .nil .nil) .nil) (.node 29129 .nil .nil))
      (.node 29147 (.node 29137 .nil .nil) (.node 29153 .nil .nil)))
    (.node 29201 (.node 29179 (.node 29173 .nil .nil) (.node 29191 .nil .nil))
      (.node 29209 (.node 29207 .nil .nil) (.node 29221 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree360_checked : NumberTheory.primeTreeChecked subtree360 := by
  norm_num only [subtree360, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree361 : BinaryTree ℕ :=
  .node 29063 subtree359 subtree360

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree361_checked : NumberTheory.primeTreeChecked subtree361 := by
  exact ⟨by norm_num only, subtree359_checked, subtree360_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree362 : BinaryTree ℕ :=
  .node 28871 subtree358 subtree361

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree362_checked : NumberTheory.primeTreeChecked subtree362 := by
  exact ⟨by norm_num only, subtree358_checked, subtree361_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree363 : BinaryTree ℕ :=
  .node 28573 subtree355 subtree362

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree363_checked : NumberTheory.primeTreeChecked subtree363 := by
  exact ⟨by norm_num only, subtree355_checked, subtree362_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree364 : BinaryTree ℕ :=
  (.node 29333
    (.node 29297 (.node 29269 (.node 29251 (.node 29243 .nil .nil) .nil) (.node 29287 .nil .nil))
      (.node 29311 (.node 29303 .nil .nil) (.node 29327 .nil .nil)))
    (.node 29387 (.node 29363 (.node 29347 (.node 29339 .nil .nil) .nil) (.node 29383 .nil .nil))
      (.node 29399 (.node 29389 .nil .nil) (.node 29411 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree364_checked : NumberTheory.primeTreeChecked subtree364 := by
  norm_num only [subtree364, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree365 : BinaryTree ℕ :=
  (.node 29531
    (.node 29473 (.node 29443 (.node 29437 (.node 29429 .nil .nil) .nil) (.node 29453 .nil .nil))
      (.node 29501 (.node 29483 .nil .nil) (.node 29527 .nil .nil)))
    (.node 29573 (.node 29567 (.node 29537 .nil .nil) (.node 29569 .nil .nil))
      (.node 29587 (.node 29581 .nil .nil) (.node 29599 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree365_checked : NumberTheory.primeTreeChecked subtree365 := by
  norm_num only [subtree365, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree366 : BinaryTree ℕ :=
  .node 29423 subtree364 subtree365

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree366_checked : NumberTheory.primeTreeChecked subtree366 := by
  exact ⟨by norm_num only, subtree364_checked, subtree365_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree367 : BinaryTree ℕ :=
  (.node 29741
    (.node 29669 (.node 29641 (.node 29633 (.node 29629 .nil .nil) .nil) (.node 29663 .nil .nil))
      (.node 29717 (.node 29671 .nil .nil) (.node 29723 .nil .nil)))
    (.node 29789 (.node 29759 (.node 29753 .nil .nil) (.node 29761 .nil .nil))
      (.node 29819 (.node 29803 .nil .nil) (.node 29833 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree367_checked : NumberTheory.primeTreeChecked subtree367 := by
  norm_num only [subtree367, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree368 : BinaryTree ℕ :=
  (.node 29927
    (.node 29879 (.node 29867 (.node 29863 (.node 29851 .nil .nil) .nil) (.node 29873 .nil .nil))
      (.node 29917 (.node 29881 .nil .nil) (.node 29921 .nil .nil)))
    (.node 29989 (.node 29959 (.node 29947 .nil .nil) (.node 29983 .nil .nil))
      (.node 30013 (.node 30011 .nil .nil) (.node 30029 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree368_checked : NumberTheory.primeTreeChecked subtree368 := by
  norm_num only [subtree368, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree369 : BinaryTree ℕ :=
  .node 29837 subtree367 subtree368

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree369_checked : NumberTheory.primeTreeChecked subtree369 := by
  exact ⟨by norm_num only, subtree367_checked, subtree368_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree370 : BinaryTree ℕ :=
  .node 29611 subtree366 subtree369

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree370_checked : NumberTheory.primeTreeChecked subtree370 := by
  exact ⟨by norm_num only, subtree366_checked, subtree369_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree371 : BinaryTree ℕ :=
  (.node 30133
    (.node 30097 (.node 30089 (.node 30071 (.node 30059 .nil .nil) .nil) (.node 30091 .nil .nil))
      (.node 30113 (.node 30109 .nil .nil) (.node 30119 .nil .nil)))
    (.node 30181 (.node 30161 (.node 30139 .nil .nil) (.node 30169 .nil .nil))
      (.node 30197 (.node 30187 .nil .nil) (.node 30211 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree371_checked : NumberTheory.primeTreeChecked subtree371 := by
  norm_num only [subtree371, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree372 : BinaryTree ℕ :=
  (.node 30323
    (.node 30271 (.node 30259 (.node 30253 (.node 30241 .nil .nil) .nil) (.node 30269 .nil .nil))
      (.node 30313 (.node 30307 .nil .nil) (.node 30319 .nil .nil)))
    (.node 30389 (.node 30347 (.node 30341 .nil .nil) (.node 30367 .nil .nil))
      (.node 30403 (.node 30391 .nil .nil) (.node 30427 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree372_checked : NumberTheory.primeTreeChecked subtree372 := by
  norm_num only [subtree372, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree373 : BinaryTree ℕ :=
  .node 30223 subtree371 subtree372

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree373_checked : NumberTheory.primeTreeChecked subtree373 := by
  exact ⟨by norm_num only, subtree371_checked, subtree372_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree374 : BinaryTree ℕ :=
  (.node 30539
    (.node 30493 (.node 30469 (.node 30467 (.node 30449 .nil .nil) .nil) (.node 30491 .nil .nil))
      (.node 30509 (.node 30497 .nil .nil) (.node 30529 .nil .nil)))
    (.node 30577 (.node 30557 (.node 30553 .nil .nil) (.node 30559 .nil .nil))
      (.node 30631 (.node 30593 .nil .nil) (.node 30637 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree374_checked : NumberTheory.primeTreeChecked subtree374 := by
  norm_num only [subtree374, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree375 : BinaryTree ℕ :=
  (.node 30727
    (.node 30697 (.node 30677 (.node 30671 (.node 30661 .nil .nil) .nil) (.node 30689 .nil .nil))
      (.node 30707 (.node 30703 .nil .nil) (.node 30713 .nil .nil)))
    (.node 30781 (.node 30763 (.node 30757 .nil .nil) (.node 30773 .nil .nil))
      (.node 30809 (.node 30803 .nil .nil) (.node 30817 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree375_checked : NumberTheory.primeTreeChecked subtree375 := by
  norm_num only [subtree375, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree376 : BinaryTree ℕ :=
  .node 30643 subtree374 subtree375

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree376_checked : NumberTheory.primeTreeChecked subtree376 := by
  exact ⟨by norm_num only, subtree374_checked, subtree375_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree377 : BinaryTree ℕ :=
  .node 30431 subtree373 subtree376

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree377_checked : NumberTheory.primeTreeChecked subtree377 := by
  exact ⟨by norm_num only, subtree373_checked, subtree376_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree378 : BinaryTree ℕ :=
  .node 30047 subtree370 subtree377

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree378_checked : NumberTheory.primeTreeChecked subtree378 := by
  exact ⟨by norm_num only, subtree370_checked, subtree377_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree379 : BinaryTree ℕ :=
  .node 29231 subtree363 subtree378

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree379_checked : NumberTheory.primeTreeChecked subtree379 := by
  exact ⟨by norm_num only, subtree363_checked, subtree378_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree380 : BinaryTree ℕ :=
  .node 27809 subtree348 subtree379

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree380_checked : NumberTheory.primeTreeChecked subtree380 := by
  exact ⟨by norm_num only, subtree348_checked, subtree379_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree381 : BinaryTree ℕ :=
  .node 24977 subtree317 subtree380

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree381_checked : NumberTheory.primeTreeChecked subtree381 := by
  exact ⟨by norm_num only, subtree317_checked, subtree380_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree382 : BinaryTree ℕ :=
  (.node 30911
    (.node 30869 (.node 30853 (.node 30841 (.node 30839 .nil .nil) .nil) (.node 30859 .nil .nil))
      (.node 30881 (.node 30871 .nil .nil) (.node 30893 .nil .nil)))
    (.node 30971 (.node 30941 (.node 30937 (.node 30931 .nil .nil) .nil) (.node 30949 .nil .nil))
      (.node 31013 (.node 30977 .nil .nil) (.node 31019 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree382_checked : NumberTheory.primeTreeChecked subtree382 := by
  norm_num only [subtree382, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree383 : BinaryTree ℕ :=
  (.node 31123
    (.node 31079 (.node 31063 (.node 31051 (.node 31039 .nil .nil) .nil) (.node 31069 .nil .nil))
      (.node 31091 (.node 31081 .nil .nil) (.node 31121 .nil .nil)))
    (.node 31153 (.node 31147 (.node 31139 .nil .nil) (.node 31151 .nil .nil))
      (.node 31177 (.node 31159 .nil .nil) (.node 31181 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree383_checked : NumberTheory.primeTreeChecked subtree383 := by
  norm_num only [subtree383, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree384 : BinaryTree ℕ :=
  .node 31033 subtree382 subtree383

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree384_checked : NumberTheory.primeTreeChecked subtree384 := by
  exact ⟨by norm_num only, subtree382_checked, subtree383_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree385 : BinaryTree ℕ :=
  (.node 31253
    (.node 31231 (.node 31219 (.node 31193 (.node 31189 .nil .nil) .nil) (.node 31223 .nil .nil))
      (.node 31247 (.node 31237 .nil .nil) (.node 31249 .nil .nil)))
    (.node 31277 (.node 31267 (.node 31259 .nil .nil) (.node 31271 .nil .nil))
      (.node 31319 (.node 31307 .nil .nil) (.node 31321 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree385_checked : NumberTheory.primeTreeChecked subtree385 := by
  norm_num only [subtree385, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree386 : BinaryTree ℕ :=
  (.node 31477
    (.node 31387 (.node 31357 (.node 31337 (.node 31333 .nil .nil) .nil) (.node 31379 .nil .nil))
      (.node 31393 (.node 31391 .nil .nil) (.node 31397 .nil .nil)))
    (.node 31517 (.node 31489 (.node 31481 .nil .nil) (.node 31511 .nil .nil))
      (.node 31541 (.node 31531 .nil .nil) (.node 31567 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree386_checked : NumberTheory.primeTreeChecked subtree386 := by
  norm_num only [subtree386, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree387 : BinaryTree ℕ :=
  .node 31327 subtree385 subtree386

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree387_checked : NumberTheory.primeTreeChecked subtree387 := by
  exact ⟨by norm_num only, subtree385_checked, subtree386_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree388 : BinaryTree ℕ :=
  .node 31183 subtree384 subtree387

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree388_checked : NumberTheory.primeTreeChecked subtree388 := by
  exact ⟨by norm_num only, subtree384_checked, subtree387_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree389 : BinaryTree ℕ :=
  (.node 31687
    (.node 31643 (.node 31607 (.node 31601 (.node 31583 .nil .nil) .nil) (.node 31627 .nil .nil))
      (.node 31663 (.node 31657 .nil .nil) (.node 31667 .nil .nil)))
    (.node 31741 (.node 31727 (.node 31721 (.node 31699 .nil .nil) .nil) (.node 31729 .nil .nil))
      (.node 31769 (.node 31751 .nil .nil) (.node 31771 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree389_checked : NumberTheory.primeTreeChecked subtree389 := by
  norm_num only [subtree389, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree390 : BinaryTree ℕ :=
  (.node 31957
    (.node 31873 (.node 31849 (.node 31847 (.node 31799 .nil .nil) .nil) (.node 31859 .nil .nil))
      (.node 31891 (.node 31883 .nil .nil) (.node 31907 .nil .nil)))
    (.node 31991 (.node 31973 (.node 31963 .nil .nil) (.node 31981 .nil .nil))
      (.node 32027 (.node 32009 .nil .nil) (.node 32029 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree390_checked : NumberTheory.primeTreeChecked subtree390 := by
  norm_num only [subtree390, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree391 : BinaryTree ℕ :=
  .node 31793 subtree389 subtree390

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree391_checked : NumberTheory.primeTreeChecked subtree391 := by
  exact ⟨by norm_num only, subtree389_checked, subtree390_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree392 : BinaryTree ℕ :=
  (.node 32119
    (.node 32083 (.node 32069 (.node 32063 (.node 32059 .nil .nil) .nil) (.node 32077 .nil .nil))
      (.node 32099 (.node 32089 .nil .nil) (.node 32117 .nil .nil)))
    (.node 32173 (.node 32143 (.node 32141 .nil .nil) (.node 32159 .nil .nil))
      (.node 32189 (.node 32183 .nil .nil) (.node 32191 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree392_checked : NumberTheory.primeTreeChecked subtree392 := by
  norm_num only [subtree392, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree393 : BinaryTree ℕ :=
  (.node 32303
    (.node 32257 (.node 32237 (.node 32233 (.node 32213 .nil .nil) .nil) (.node 32251 .nil .nil))
      (.node 32297 (.node 32261 .nil .nil) (.node 32299 .nil .nil)))
    (.node 32327 (.node 32321 (.node 32309 .nil .nil) (.node 32323 .nil .nil))
      (.node 32359 (.node 32353 .nil .nil) (.node 32363 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree393_checked : NumberTheory.primeTreeChecked subtree393 := by
  norm_num only [subtree393, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree394 : BinaryTree ℕ :=
  .node 32203 subtree392 subtree393

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree394_checked : NumberTheory.primeTreeChecked subtree394 := by
  exact ⟨by norm_num only, subtree392_checked, subtree393_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree395 : BinaryTree ℕ :=
  .node 32057 subtree391 subtree394

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree395_checked : NumberTheory.primeTreeChecked subtree395 := by
  exact ⟨by norm_num only, subtree391_checked, subtree394_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree396 : BinaryTree ℕ :=
  .node 31573 subtree388 subtree395

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree396_checked : NumberTheory.primeTreeChecked subtree396 := by
  exact ⟨by norm_num only, subtree388_checked, subtree395_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree397 : BinaryTree ℕ :=
  (.node 32479
    (.node 32429 (.node 32413 (.node 32401 (.node 32381 .nil .nil) .nil) (.node 32423 .nil .nil))
      (.node 32443 (.node 32441 .nil .nil) (.node 32467 .nil .nil)))
    (.node 32531 (.node 32503 (.node 32497 (.node 32491 .nil .nil) .nil) (.node 32507 .nil .nil))
      (.node 32537 (.node 32533 .nil .nil) (.node 32561 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree397_checked : NumberTheory.primeTreeChecked subtree397 := by
  norm_num only [subtree397, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree398 : BinaryTree ℕ :=
  (.node 32687
    (.node 32609 (.node 32587 (.node 32579 (.node 32569 .nil .nil) .nil) (.node 32603 .nil .nil))
      (.node 32647 (.node 32621 .nil .nil) (.node 32653 .nil .nil)))
    (.node 32717 (.node 32707 (.node 32693 .nil .nil) (.node 32713 .nil .nil))
      (.node 32749 (.node 32719 .nil .nil) (.node 32771 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree398_checked : NumberTheory.primeTreeChecked subtree398 := by
  norm_num only [subtree398, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree399 : BinaryTree ℕ :=
  .node 32563 subtree397 subtree398

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree399_checked : NumberTheory.primeTreeChecked subtree399 := by
  exact ⟨by norm_num only, subtree397_checked, subtree398_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree400 : BinaryTree ℕ :=
  (.node 32869
    (.node 32831 (.node 32801 (.node 32797 (.node 32783 .nil .nil) .nil) (.node 32803 .nil .nil))
      (.node 32839 (.node 32833 .nil .nil) (.node 32843 .nil .nil)))
    (.node 32917 (.node 32909 (.node 32887 .nil .nil) (.node 32911 .nil .nil))
      (.node 32941 (.node 32939 .nil .nil) (.node 32969 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree400_checked : NumberTheory.primeTreeChecked subtree400 := by
  norm_num only [subtree400, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree401 : BinaryTree ℕ :=
  (.node 33049
    (.node 33013 (.node 32993 (.node 32987 (.node 32983 .nil .nil) .nil) (.node 32999 .nil .nil))
      (.node 33029 (.node 33023 .nil .nil) (.node 33037 .nil .nil)))
    (.node 33083 (.node 33071 (.node 33053 .nil .nil) (.node 33073 .nil .nil))
      (.node 33107 (.node 33091 .nil .nil) (.node 33113 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree401_checked : NumberTheory.primeTreeChecked subtree401 := by
  norm_num only [subtree401, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree402 : BinaryTree ℕ :=
  .node 32971 subtree400 subtree401

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree402_checked : NumberTheory.primeTreeChecked subtree402 := by
  exact ⟨by norm_num only, subtree400_checked, subtree401_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree403 : BinaryTree ℕ :=
  .node 32779 subtree399 subtree402

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree403_checked : NumberTheory.primeTreeChecked subtree403 := by
  exact ⟨by norm_num only, subtree399_checked, subtree402_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree404 : BinaryTree ℕ :=
  (.node 33247
    (.node 33181 (.node 33161 (.node 33151 (.node 33149 .nil .nil) .nil) (.node 33179 .nil .nil))
      (.node 33211 (.node 33203 .nil .nil) (.node 33223 .nil .nil)))
    (.node 33329 (.node 33311 (.node 33301 (.node 33289 .nil .nil) .nil) (.node 33317 .nil .nil))
      (.node 33347 (.node 33331 .nil .nil) (.node 33349 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree404_checked : NumberTheory.primeTreeChecked subtree404 := by
  norm_num only [subtree404, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree405 : BinaryTree ℕ :=
  (.node 33479
    (.node 33409 (.node 33391 (.node 33377 (.node 33359 .nil .nil) .nil) (.node 33403 .nil .nil))
      (.node 33457 (.node 33427 .nil .nil) (.node 33461 .nil .nil)))
    (.node 33521 (.node 33493 (.node 33487 .nil .nil) (.node 33503 .nil .nil))
      (.node 33547 (.node 33529 .nil .nil) (.node 33563 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree405_checked : NumberTheory.primeTreeChecked subtree405 := by
  norm_num only [subtree405, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree406 : BinaryTree ℕ :=
  .node 33353 subtree404 subtree405

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree406_checked : NumberTheory.primeTreeChecked subtree406 := by
  exact ⟨by norm_num only, subtree404_checked, subtree405_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree407 : BinaryTree ℕ :=
  (.node 33637
    (.node 33613 (.node 33589 (.node 33587 (.node 33581 .nil .nil) .nil) (.node 33599 .nil .nil))
      (.node 33623 (.node 33617 .nil .nil) (.node 33629 .nil .nil)))
    (.node 33703 (.node 33647 (.node 33641 .nil .nil) (.node 33679 .nil .nil))
      (.node 33739 (.node 33713 .nil .nil) (.node 33749 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree407_checked : NumberTheory.primeTreeChecked subtree407 := by
  norm_num only [subtree407, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree408 : BinaryTree ℕ :=
  (.node 33829
    (.node 33797 (.node 33769 (.node 33767 (.node 33757 .nil .nil) .nil) (.node 33773 .nil .nil))
      (.node 33811 (.node 33809 .nil .nil) (.node 33827 .nil .nil)))
    (.node 33889 (.node 33857 (.node 33851 .nil .nil) (.node 33871 .nil .nil))
      (.node 33911 (.node 33893 .nil .nil) (.node 33923 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree408_checked : NumberTheory.primeTreeChecked subtree408 := by
  norm_num only [subtree408, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree409 : BinaryTree ℕ :=
  .node 33751 subtree407 subtree408

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree409_checked : NumberTheory.primeTreeChecked subtree409 := by
  exact ⟨by norm_num only, subtree407_checked, subtree408_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree410 : BinaryTree ℕ :=
  .node 33569 subtree406 subtree409

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree410_checked : NumberTheory.primeTreeChecked subtree410 := by
  exact ⟨by norm_num only, subtree406_checked, subtree409_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree411 : BinaryTree ℕ :=
  .node 33119 subtree403 subtree410

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree411_checked : NumberTheory.primeTreeChecked subtree411 := by
  exact ⟨by norm_num only, subtree403_checked, subtree410_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree412 : BinaryTree ℕ :=
  .node 32369 subtree396 subtree411

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree412_checked : NumberTheory.primeTreeChecked subtree412 := by
  exact ⟨by norm_num only, subtree396_checked, subtree411_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree413 : BinaryTree ℕ :=
  (.node 34123
    (.node 34019 (.node 33961 (.node 33941 (.node 33937 .nil .nil) .nil) (.node 33967 .nil .nil))
      (.node 34057 (.node 34033 .nil .nil) (.node 34061 .nil .nil)))
    (.node 34211 (.node 34171 (.node 34159 (.node 34147 .nil .nil) .nil) (.node 34183 .nil .nil))
      (.node 34217 (.node 34213 .nil .nil) (.node 34231 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree413_checked : NumberTheory.primeTreeChecked subtree413 := by
  norm_num only [subtree413, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree414 : BinaryTree ℕ :=
  (.node 34361
    (.node 34283 (.node 34267 (.node 34261 (.node 34259 .nil .nil) .nil) (.node 34273 .nil .nil))
      (.node 34319 (.node 34301 .nil .nil) (.node 34351 .nil .nil)))
    (.node 34403 (.node 34369 (.node 34367 .nil .nil) (.node 34381 .nil .nil))
      (.node 34429 (.node 34421 .nil .nil) (.node 34439 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree414_checked : NumberTheory.primeTreeChecked subtree414 := by
  norm_num only [subtree414, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree415 : BinaryTree ℕ :=
  .node 34253 subtree413 subtree414

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree415_checked : NumberTheory.primeTreeChecked subtree415 := by
  exact ⟨by norm_num only, subtree413_checked, subtree414_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree416 : BinaryTree ℕ :=
  (.node 34537
    (.node 34501 (.node 34487 (.node 34483 (.node 34471 .nil .nil) .nil) (.node 34499 .nil .nil))
      (.node 34513 (.node 34511 .nil .nil) (.node 34519 .nil .nil)))
    (.node 34603 (.node 34589 (.node 34543 .nil .nil) (.node 34591 .nil .nil))
      (.node 34631 (.node 34607 .nil .nil) (.node 34649 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree416_checked : NumberTheory.primeTreeChecked subtree416 := by
  norm_num only [subtree416, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree417 : BinaryTree ℕ :=
  (.node 34747
    (.node 34693 (.node 34679 (.node 34673 (.node 34667 .nil .nil) .nil) (.node 34687 .nil .nil))
      (.node 34721 (.node 34703 .nil .nil) (.node 34729 .nil .nil)))
    (.node 34807 (.node 34763 (.node 34757 .nil .nil) (.node 34781 .nil .nil))
      (.node 34841 (.node 34819 .nil .nil) (.node 34843 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree417_checked : NumberTheory.primeTreeChecked subtree417 := by
  norm_num only [subtree417, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree418 : BinaryTree ℕ :=
  .node 34651 subtree416 subtree417

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree418_checked : NumberTheory.primeTreeChecked subtree418 := by
  exact ⟨by norm_num only, subtree416_checked, subtree417_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree419 : BinaryTree ℕ :=
  .node 34469 subtree415 subtree418

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree419_checked : NumberTheory.primeTreeChecked subtree419 := by
  exact ⟨by norm_num only, subtree415_checked, subtree418_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree420 : BinaryTree ℕ :=
  (.node 35051
    (.node 34963 (.node 34939 (.node 34877 (.node 34871 .nil .nil) .nil) (.node 34961 .nil .nil))
      (.node 35023 (.node 34981 .nil .nil) (.node 35027 .nil .nil)))
    (.node 35099 (.node 35083 (.node 35059 (.node 35053 .nil .nil) .nil) (.node 35089 .nil .nil))
      (.node 35111 (.node 35107 .nil .nil) (.node 35117 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree420_checked : NumberTheory.primeTreeChecked subtree420 := by
  norm_num only [subtree420, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree421 : BinaryTree ℕ :=
  (.node 35251
    (.node 35171 (.node 35153 (.node 35149 (.node 35141 .nil .nil) .nil) (.node 35159 .nil .nil))
      (.node 35221 (.node 35201 .nil .nil) (.node 35227 .nil .nil)))
    (.node 35281 (.node 35267 (.node 35257 .nil .nil) (.node 35279 .nil .nil))
      (.node 35311 (.node 35291 .nil .nil) (.node 35317 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree421_checked : NumberTheory.primeTreeChecked subtree421 := by
  norm_num only [subtree421, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree422 : BinaryTree ℕ :=
  .node 35129 subtree420 subtree421

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree422_checked : NumberTheory.primeTreeChecked subtree422 := by
  exact ⟨by norm_num only, subtree420_checked, subtree421_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree423 : BinaryTree ℕ :=
  (.node 35461
    (.node 35407 (.node 35363 (.node 35353 (.node 35339 .nil .nil) .nil) (.node 35401 .nil .nil))
      (.node 35423 (.node 35419 .nil .nil) (.node 35437 .nil .nil)))
    (.node 35521 (.node 35507 (.node 35491 .nil .nil) (.node 35509 .nil .nil))
      (.node 35531 (.node 35527 .nil .nil) (.node 35533 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree423_checked : NumberTheory.primeTreeChecked subtree423 := by
  norm_num only [subtree423, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree424 : BinaryTree ℕ :=
  (.node 35677
    (.node 35593 (.node 35573 (.node 35569 (.node 35543 .nil .nil) .nil) (.node 35591 .nil .nil))
      (.node 35603 (.node 35597 .nil .nil) (.node 35617 .nil .nil)))
    (.node 35759 (.node 35731 (.node 35729 .nil .nil) (.node 35753 .nil .nil))
      (.node 35797 (.node 35771 .nil .nil) (.node 35801 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree424_checked : NumberTheory.primeTreeChecked subtree424 := by
  norm_num only [subtree424, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree425 : BinaryTree ℕ :=
  .node 35537 subtree423 subtree424

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree425_checked : NumberTheory.primeTreeChecked subtree425 := by
  exact ⟨by norm_num only, subtree423_checked, subtree424_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree426 : BinaryTree ℕ :=
  .node 35323 subtree422 subtree425

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree426_checked : NumberTheory.primeTreeChecked subtree426 := by
  exact ⟨by norm_num only, subtree422_checked, subtree425_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree427 : BinaryTree ℕ :=
  .node 34849 subtree419 subtree426

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree427_checked : NumberTheory.primeTreeChecked subtree427 := by
  exact ⟨by norm_num only, subtree419_checked, subtree426_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree428 : BinaryTree ℕ :=
  (.node 35911
    (.node 35863 (.node 35837 (.node 35831 (.node 35809 .nil .nil) .nil) (.node 35839 .nil .nil))
      (.node 35897 (.node 35879 .nil .nil) (.node 35899 .nil .nil)))
    (.node 35969 (.node 35951 (.node 35933 (.node 35923 .nil .nil) .nil) (.node 35963 .nil .nil))
      (.node 36007 (.node 35999 .nil .nil) (.node 36013 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree428_checked : NumberTheory.primeTreeChecked subtree428 := by
  norm_num only [subtree428, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree429 : BinaryTree ℕ :=
  (.node 36191
    (.node 36131 (.node 36073 (.node 36061 (.node 36037 .nil .nil) .nil) (.node 36083 .nil .nil))
      (.node 36161 (.node 36137 .nil .nil) (.node 36187 .nil .nil)))
    (.node 36251 (.node 36217 (.node 36209 .nil .nil) (.node 36241 .nil .nil))
      (.node 36277 (.node 36263 .nil .nil) (.node 36307 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree429_checked : NumberTheory.primeTreeChecked subtree429 := by
  norm_num only [subtree429, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree430 : BinaryTree ℕ :=
  .node 36017 subtree428 subtree429

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree430_checked : NumberTheory.primeTreeChecked subtree430 := by
  exact ⟨by norm_num only, subtree428_checked, subtree429_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree431 : BinaryTree ℕ :=
  (.node 36473
    (.node 36451 (.node 36373 (.node 36353 (.node 36341 .nil .nil) .nil) (.node 36383 .nil .nil))
      (.node 36467 (.node 36457 .nil .nil) (.node 36469 .nil .nil)))
    (.node 36523 (.node 36493 (.node 36479 .nil .nil) (.node 36497 .nil .nil))
      (.node 36541 (.node 36529 .nil .nil) (.node 36559 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree431_checked : NumberTheory.primeTreeChecked subtree431 := by
  norm_num only [subtree431, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree432 : BinaryTree ℕ :=
  (.node 36683
    (.node 36637 (.node 36599 (.node 36587 (.node 36571 .nil .nil) .nil) (.node 36607 .nil .nil))
      (.node 36671 (.node 36653 .nil .nil) (.node 36677 .nil .nil)))
    (.node 36779 (.node 36739 (.node 36713 .nil .nil) (.node 36761 .nil .nil))
      (.node 36791 (.node 36781 .nil .nil) (.node 36793 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree432_checked : NumberTheory.primeTreeChecked subtree432 := by
  norm_num only [subtree432, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree433 : BinaryTree ℕ :=
  .node 36563 subtree431 subtree432

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree433_checked : NumberTheory.primeTreeChecked subtree433 := by
  exact ⟨by norm_num only, subtree431_checked, subtree432_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree434 : BinaryTree ℕ :=
  .node 36319 subtree430 subtree433

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree434_checked : NumberTheory.primeTreeChecked subtree434 := by
  exact ⟨by norm_num only, subtree430_checked, subtree433_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree435 : BinaryTree ℕ :=
  (.node 36973
    (.node 36887 (.node 36871 (.node 36857 (.node 36847 .nil .nil) .nil) (.node 36877 .nil .nil))
      (.node 36943 (.node 36919 .nil .nil) (.node 36947 .nil .nil)))
    (.node 37057 (.node 37003 (.node 36997 (.node 36979 .nil .nil) .nil) (.node 37021 .nil .nil))
      (.node 37087 (.node 37061 .nil .nil) (.node 37097 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree435_checked : NumberTheory.primeTreeChecked subtree435 := by
  norm_num only [subtree435, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree436 : BinaryTree ℕ :=
  (.node 37307
    (.node 37201 (.node 37171 (.node 37159 (.node 37139 .nil .nil) .nil) (.node 37181 .nil .nil))
      (.node 37273 (.node 37223 .nil .nil) (.node 37277 .nil .nil)))
    (.node 37339 (.node 37313 (.node 37309 .nil .nil) (.node 37321 .nil .nil))
      (.node 37361 (.node 37357 .nil .nil) (.node 37363 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree436_checked : NumberTheory.primeTreeChecked subtree436 := by
  norm_num only [subtree436, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree437 : BinaryTree ℕ :=
  .node 37123 subtree435 subtree436

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree437_checked : NumberTheory.primeTreeChecked subtree437 := by
  exact ⟨by norm_num only, subtree435_checked, subtree436_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree438 : BinaryTree ℕ :=
  (.node 37529
    (.node 37483 (.node 37447 (.node 37441 (.node 37397 .nil .nil) .nil) (.node 37463 .nil .nil))
      (.node 37507 (.node 37489 .nil .nil) (.node 37517 .nil .nil)))
    (.node 37561 (.node 37547 (.node 37537 .nil .nil) (.node 37549 .nil .nil))
      (.node 37571 (.node 37567 .nil .nil) (.node 37579 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree438_checked : NumberTheory.primeTreeChecked subtree438 := by
  norm_num only [subtree438, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree439 : BinaryTree ℕ :=
  (.node 37747
    (.node 37663 (.node 37643 (.node 37633 (.node 37607 .nil .nil) .nil) (.node 37649 .nil .nil))
      (.node 37699 (.node 37691 .nil .nil) (.node 37717 .nil .nil)))
    (.node 37811 (.node 37783 (.node 37781 .nil .nil) (.node 37799 .nil .nil))
      (.node 37831 (.node 37813 .nil .nil) (.node 37847 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree439_checked : NumberTheory.primeTreeChecked subtree439 := by
  norm_num only [subtree439, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree440 : BinaryTree ℕ :=
  .node 37589 subtree438 subtree439

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree440_checked : NumberTheory.primeTreeChecked subtree440 := by
  exact ⟨by norm_num only, subtree438_checked, subtree439_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree441 : BinaryTree ℕ :=
  .node 37369 subtree437 subtree440

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree441_checked : NumberTheory.primeTreeChecked subtree441 := by
  exact ⟨by norm_num only, subtree437_checked, subtree440_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree442 : BinaryTree ℕ :=
  .node 36821 subtree434 subtree441

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree442_checked : NumberTheory.primeTreeChecked subtree442 := by
  exact ⟨by norm_num only, subtree434_checked, subtree441_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree443 : BinaryTree ℕ :=
  .node 35803 subtree427 subtree442

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree443_checked : NumberTheory.primeTreeChecked subtree443 := by
  exact ⟨by norm_num only, subtree427_checked, subtree442_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree444 : BinaryTree ℕ :=
  .node 33931 subtree412 subtree443

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree444_checked : NumberTheory.primeTreeChecked subtree444 := by
  exact ⟨by norm_num only, subtree412_checked, subtree443_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree445 : BinaryTree ℕ :=
  (.node 38047
    (.node 37987 (.node 37897 (.node 37889 (.node 37871 .nil .nil) .nil) (.node 37951 .nil .nil))
      (.node 37997 (.node 37993 .nil .nil) (.node 38039 .nil .nil)))
    (.node 38167 (.node 38119 (.node 38113 (.node 38053 .nil .nil) .nil) (.node 38149 .nil .nil))
      (.node 38201 (.node 38189 .nil .nil) (.node 38231 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree445_checked : NumberTheory.primeTreeChecked subtree445 := by
  norm_num only [subtree445, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree446 : BinaryTree ℕ :=
  (.node 38461
    (.node 38303 (.node 38287 (.node 38281 (.node 38273 .nil .nil) .nil) (.node 38299 .nil .nil))
      (.node 38333 (.node 38327 .nil .nil) (.node 38371 .nil .nil)))
    (.node 38567 (.node 38557 (.node 38501 .nil .nil) (.node 38561 .nil .nil))
      (.node 38609 (.node 38593 .nil .nil) (.node 38611 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree446_checked : NumberTheory.primeTreeChecked subtree446 := by
  norm_num only [subtree446, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree447 : BinaryTree ℕ :=
  .node 38239 subtree445 subtree446

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree447_checked : NumberTheory.primeTreeChecked subtree447 := by
  exact ⟨by norm_num only, subtree445_checked, subtree446_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree448 : BinaryTree ℕ :=
  (.node 38713
    (.node 38677 (.node 38653 (.node 38651 (.node 38639 .nil .nil) .nil) (.node 38671 .nil .nil))
      (.node 38707 (.node 38699 .nil .nil) (.node 38711 .nil .nil)))
    (.node 38803 (.node 38767 (.node 38747 .nil .nil) (.node 38783 .nil .nil))
      (.node 38993 (.node 38933 .nil .nil) (.node 39019 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree448_checked : NumberTheory.primeTreeChecked subtree448 := by
  norm_num only [subtree448, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree449 : BinaryTree ℕ :=
  (.node 39241
    (.node 39209 (.node 39113 (.node 39097 (.node 39089 .nil .nil) .nil) (.node 39163 .nil .nil))
      (.node 39229 (.node 39227 .nil .nil) (.node 39233 .nil .nil)))
    (.node 39313 (.node 39293 (.node 39251 .nil .nil) (.node 39301 .nil .nil))
      (.node 39341 (.node 39323 .nil .nil) (.node 39359 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree449_checked : NumberTheory.primeTreeChecked subtree449 := by
  norm_num only [subtree449, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree450 : BinaryTree ℕ :=
  .node 39041 subtree448 subtree449

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree450_checked : NumberTheory.primeTreeChecked subtree450 := by
  exact ⟨by norm_num only, subtree448_checked, subtree449_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree451 : BinaryTree ℕ :=
  .node 38629 subtree447 subtree450

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree451_checked : NumberTheory.primeTreeChecked subtree451 := by
  exact ⟨by norm_num only, subtree447_checked, subtree450_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree452 : BinaryTree ℕ :=
  (.node 39671
    (.node 39511 (.node 39499 (.node 39419 (.node 39371 .nil .nil) .nil) (.node 39503 .nil .nil))
      (.node 39631 (.node 39607 .nil .nil) (.node 39659 .nil .nil)))
    (.node 39821 (.node 39791 (.node 39779 (.node 39679 .nil .nil) .nil) (.node 39799 .nil .nil))
      (.node 39847 (.node 39839 .nil .nil) (.node 39863 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree452_checked : NumberTheory.primeTreeChecked subtree452 := by
  norm_num only [subtree452, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree453 : BinaryTree ℕ :=
  (.node 40039
    (.node 39989 (.node 39937 (.node 39901 (.node 39887 .nil .nil) .nil) (.node 39971 .nil .nil))
      (.node 40013 (.node 40009 .nil .nil) (.node 40037 .nil .nil)))
    (.node 40153 (.node 40127 (.node 40099 .nil .nil) (.node 40151 .nil .nil))
      (.node 40169 (.node 40163 .nil .nil) (.node 40177 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree453_checked : NumberTheory.primeTreeChecked subtree453 := by
  norm_num only [subtree453, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree454 : BinaryTree ℕ :=
  .node 39877 subtree452 subtree453

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree454_checked : NumberTheory.primeTreeChecked subtree454 := by
  exact ⟨by norm_num only, subtree452_checked, subtree453_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree455 : BinaryTree ℕ :=
  (.node 40487
    (.node 40277 (.node 40231 (.node 40213 (.node 40193 .nil .nil) .nil) (.node 40237 .nil .nil))
      (.node 40361 (.node 40343 .nil .nil) (.node 40429 .nil .nil)))
    (.node 40583 (.node 40507 (.node 40499 .nil .nil) (.node 40559 .nil .nil))
      (.node 40637 (.node 40627 .nil .nil) (.node 40697 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree455_checked : NumberTheory.primeTreeChecked subtree455 := by
  norm_num only [subtree455, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree456 : BinaryTree ℕ :=
  (.node 40961
    (.node 40849 (.node 40813 (.node 40787 (.node 40771 .nil .nil) .nil) (.node 40841 .nil .nil))
      (.node 40897 (.node 40853 .nil .nil) (.node 40949 .nil .nil)))
    (.node 41057 (.node 41023 (.node 40993 .nil .nil) (.node 41039 .nil .nil))
      (.node 41117 (.node 41081 .nil .nil) (.node 41131 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree456_checked : NumberTheory.primeTreeChecked subtree456 := by
  norm_num only [subtree456, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree457 : BinaryTree ℕ :=
  .node 40751 subtree455 subtree456

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree457_checked : NumberTheory.primeTreeChecked subtree457 := by
  exact ⟨by norm_num only, subtree455_checked, subtree456_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree458 : BinaryTree ℕ :=
  .node 40189 subtree454 subtree457

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree458_checked : NumberTheory.primeTreeChecked subtree458 := by
  exact ⟨by norm_num only, subtree454_checked, subtree457_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree459 : BinaryTree ℕ :=
  .node 39367 subtree451 subtree458

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree459_checked : NumberTheory.primeTreeChecked subtree459 := by
  exact ⟨by norm_num only, subtree451_checked, subtree458_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree460 : BinaryTree ℕ :=
  (.node 41299
    (.node 41203 (.node 41177 (.node 41161 (.node 41149 .nil .nil) .nil) (.node 41201 .nil .nil))
      (.node 41233 (.node 41227 .nil .nil) (.node 41257 .nil .nil)))
    (.node 41507 (.node 41453 (.node 41381 (.node 41351 .nil .nil) .nil) (.node 41479 .nil .nil))
      (.node 41539 (.node 41519 .nil .nil) (.node 41593 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree460_checked : NumberTheory.primeTreeChecked subtree460 := by
  norm_num only [subtree460, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree461 : BinaryTree ℕ :=
  (.node 41771
    (.node 41669 (.node 41617 (.node 41611 (.node 41609 .nil .nil) .nil) (.node 41659 .nil .nil))
      (.node 41729 (.node 41687 .nil .nil) (.node 41759 .nil .nil)))
    (.node 41851 (.node 41813 (.node 41801 .nil .nil) (.node 41843 .nil .nil))
      (.node 41887 (.node 41863 .nil .nil) (.node 41897 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree461_checked : NumberTheory.primeTreeChecked subtree461 := by
  norm_num only [subtree461, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree462 : BinaryTree ℕ :=
  .node 41603 subtree460 subtree461

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree462_checked : NumberTheory.primeTreeChecked subtree462 := by
  exact ⟨by norm_num only, subtree460_checked, subtree461_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree463 : BinaryTree ℕ :=
  (.node 42083
    (.node 42013 (.node 41969 (.node 41947 (.node 41941 .nil .nil) .nil) (.node 41983 .nil .nil))
      (.node 42043 (.node 42019 .nil .nil) (.node 42061 .nil .nil)))
    (.node 42223 (.node 42169 (.node 42139 .nil .nil) (.node 42197 .nil .nil))
      (.node 42283 (.node 42281 .nil .nil) (.node 42359 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree463_checked : NumberTheory.primeTreeChecked subtree463 := by
  norm_num only [subtree463, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree464 : BinaryTree ℕ :=
  (.node 42571
    (.node 42463 (.node 42437 (.node 42397 (.node 42391 .nil .nil) .nil) (.node 42443 .nil .nil))
      (.node 42509 (.node 42487 .nil .nil) (.node 42533 .nil .nil)))
    (.node 42709 (.node 42643 (.node 42589 .nil .nil) (.node 42689 .nil .nil))
      (.node 42767 (.node 42751 .nil .nil) (.node 42787 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree464_checked : NumberTheory.primeTreeChecked subtree464 := by
  norm_num only [subtree464, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree465 : BinaryTree ℕ :=
  .node 42379 subtree463 subtree464

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree465_checked : NumberTheory.primeTreeChecked subtree465 := by
  exact ⟨by norm_num only, subtree463_checked, subtree464_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree466 : BinaryTree ℕ :=
  .node 41927 subtree462 subtree465

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree466_checked : NumberTheory.primeTreeChecked subtree466 := by
  exact ⟨by norm_num only, subtree462_checked, subtree465_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree467 : BinaryTree ℕ :=
  (.node 42967
    (.node 42901 (.node 42863 (.node 42859 (.node 42839 .nil .nil) .nil) (.node 42899 .nil .nil))
      (.node 42953 (.node 42937 .nil .nil) (.node 42961 .nil .nil)))
    (.node 43117 (.node 43067 (.node 43063 (.node 42989 .nil .nil) .nil) (.node 43103 .nil .nil))
      (.node 43151 (.node 43133 .nil .nil) (.node 43159 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree467_checked : NumberTheory.primeTreeChecked subtree467 := by
  norm_num only [subtree467, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree468 : BinaryTree ℕ :=
  (.node 43627
    (.node 43541 (.node 43291 (.node 43283 (.node 43237 .nil .nil) .nil) (.node 43397 .nil .nil))
      (.node 43573 (.node 43543 .nil .nil) (.node 43577 .nil .nil)))
    (.node 43759 (.node 43711 (.node 43661 .nil .nil) (.node 43721 .nil .nil))
      (.node 43787 (.node 43781 .nil .nil) (.node 43801 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree468_checked : NumberTheory.primeTreeChecked subtree468 := by
  norm_num only [subtree468, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree469 : BinaryTree ℕ :=
  .node 43189 subtree467 subtree468

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree469_checked : NumberTheory.primeTreeChecked subtree469 := by
  exact ⟨by norm_num only, subtree467_checked, subtree468_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree470 : BinaryTree ℕ :=
  (.node 44059
    (.node 43951 (.node 43891 (.node 43889 (.node 43867 .nil .nil) .nil) (.node 43913 .nil .nil))
      (.node 43987 (.node 43973 .nil .nil) (.node 44017 .nil .nil)))
    (.node 44101 (.node 44087 (.node 44071 .nil .nil) (.node 44089 .nil .nil))
      (.node 44131 (.node 44129 .nil .nil) (.node 44171 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree470_checked : NumberTheory.primeTreeChecked subtree470 := by
  norm_num only [subtree470, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree471 : BinaryTree ℕ :=
  (.node 44449
    (.node 44351 (.node 44281 (.node 44269 (.node 44267 .nil .nil) .nil) (.node 44293 .nil .nil))
      (.node 44389 (.node 44381 .nil .nil) (.node 44417 .nil .nil)))
    (.node 44549 (.node 44501 (.node 44491 .nil .nil) (.node 44543 .nil .nil))
      (.node 44623 (.node 44617 .nil .nil) (.node 44633 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree471_checked : NumberTheory.primeTreeChecked subtree471 := by
  norm_num only [subtree471, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree472 : BinaryTree ℕ :=
  .node 44249 subtree470 subtree471

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree472_checked : NumberTheory.primeTreeChecked subtree472 := by
  exact ⟨by norm_num only, subtree470_checked, subtree471_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree473 : BinaryTree ℕ :=
  .node 43853 subtree469 subtree472

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree473_checked : NumberTheory.primeTreeChecked subtree473 := by
  exact ⟨by norm_num only, subtree469_checked, subtree472_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree474 : BinaryTree ℕ :=
  .node 42829 subtree466 subtree473

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree474_checked : NumberTheory.primeTreeChecked subtree474 := by
  exact ⟨by norm_num only, subtree466_checked, subtree473_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree475 : BinaryTree ℕ :=
  .node 41143 subtree459 subtree474

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree475_checked : NumberTheory.primeTreeChecked subtree475 := by
  exact ⟨by norm_num only, subtree459_checked, subtree474_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree476 : BinaryTree ℕ :=
  (.node 44797
    (.node 44729 (.node 44683 (.node 44651 (.node 44647 .nil .nil) .nil) (.node 44701 .nil .nil))
      (.node 44773 (.node 44753 .nil .nil) (.node 44789 .nil .nil)))
    (.node 44939 (.node 44887 (.node 44879 (.node 44867 .nil .nil) .nil) (.node 44893 .nil .nil))
      (.node 44959 (.node 44953 .nil .nil) (.node 44983 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree476_checked : NumberTheory.primeTreeChecked subtree476 := by
  norm_num only [subtree476, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree477 : BinaryTree ℕ :=
  (.node 45319
    (.node 45139 (.node 45121 (.node 45119 (.node 45053 .nil .nil) .nil) (.node 45127 .nil .nil))
      (.node 45281 (.node 45191 .nil .nil) (.node 45307 .nil .nil)))
    (.node 45503 (.node 45439 (.node 45337 .nil .nil) (.node 45491 .nil .nil))
      (.node 45569 (.node 45533 .nil .nil) (.node 45587 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree477_checked : NumberTheory.primeTreeChecked subtree477 := by
  norm_num only [subtree477, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree478 : BinaryTree ℕ :=
  .node 45013 subtree476 subtree477

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree478_checked : NumberTheory.primeTreeChecked subtree478 := by
  exact ⟨by norm_num only, subtree476_checked, subtree477_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree479 : BinaryTree ℕ :=
  (.node 46337
    (.node 46181 (.node 45817 (.node 45673 (.node 45667 .nil .nil) .nil) (.node 46091 .nil .nil))
      (.node 46273 (.node 46229 .nil .nil) (.node 46307 .nil .nil)))
    (.node 46441 (.node 46411 (.node 46351 .nil .nil) (.node 46439 .nil .nil))
      (.node 46477 (.node 46451 .nil .nil) (.node 46499 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree479_checked : NumberTheory.primeTreeChecked subtree479 := by
  norm_num only [subtree479, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree480 : BinaryTree ℕ :=
  (.node 46727
    (.node 46663 (.node 46639 (.node 46619 (.node 46523 .nil .nil) .nil) (.node 46643 .nil .nil))
      (.node 46687 (.node 46681 .nil .nil) (.node 46691 .nil .nil)))
    (.node 47119 (.node 46811 (.node 46757 .nil .nil) (.node 47111 .nil .nil))
      (.node 47189 (.node 47123 .nil .nil) (.node 47207 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree480_checked : NumberTheory.primeTreeChecked subtree480 := by
  norm_num only [subtree480, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree481 : BinaryTree ℕ :=
  .node 46507 subtree479 subtree480

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree481_checked : NumberTheory.primeTreeChecked subtree481 := by
  exact ⟨by norm_num only, subtree479_checked, subtree480_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree482 : BinaryTree ℕ :=
  .node 45613 subtree478 subtree481

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree482_checked : NumberTheory.primeTreeChecked subtree482 := by
  exact ⟨by norm_num only, subtree478_checked, subtree481_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree483 : BinaryTree ℕ :=
  (.node 47777
    (.node 47591 (.node 47543 (.node 47407 (.node 47351 .nil .nil) .nil) (.node 47581 .nil .nil))
      (.node 47701 (.node 47681 .nil .nil) (.node 47717 .nil .nil)))
    (.node 47981 (.node 47917 (.node 47857 (.node 47797 .nil .nil) .nil) (.node 47969 .nil .nil))
      (.node 48029 (.node 48017 .nil .nil) (.node 48073 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree483_checked : NumberTheory.primeTreeChecked subtree483 := by
  norm_num only [subtree483, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree484 : BinaryTree ℕ :=
  (.node 48761
    (.node 48437 (.node 48247 (.node 48131 (.node 48091 .nil .nil) .nil) (.node 48299 .nil .nil))
      (.node 48541 (.node 48523 .nil .nil) (.node 48589 .nil .nil)))
    (.node 49009 (.node 48889 (.node 48787 .nil .nil) (.node 49003 .nil .nil))
      (.node 49043 (.node 49019 .nil .nil) (.node 49157 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree484_checked : NumberTheory.primeTreeChecked subtree484 := by
  norm_num only [subtree484, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree485 : BinaryTree ℕ :=
  .node 48079 subtree483 subtree484

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree485_checked : NumberTheory.primeTreeChecked subtree485 := by
  exact ⟨by norm_num only, subtree483_checked, subtree484_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree486 : BinaryTree ℕ :=
  (.node 49663
    (.node 49547 (.node 49331 (.node 49297 (.node 49177 .nil .nil) .nil) (.node 49433 .nil .nil))
      (.node 49597 (.node 49559 .nil .nil) (.node 49603 .nil .nil)))
    (.node 50321 (.node 49853 (.node 49831 .nil .nil) (.node 50263 .nil .nil))
      (.node 50497 (.node 50341 .nil .nil) (.node 50527 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree486_checked : NumberTheory.primeTreeChecked subtree486 := by
  norm_num only [subtree486, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree487 : BinaryTree ℕ :=
  (.node 51059
    (.node 50893 (.node 50773 (.node 50671 (.node 50627 .nil .nil) .nil) (.node 50891 .nil .nil))
      (.node 50971 (.node 50923 .nil .nil) (.node 51031 .nil .nil)))
    (.node 51341 (.node 51199 (.node 51133 .nil .nil) (.node 51307 .nil .nil))
      (.node 51487 (.node 51439 .nil .nil) (.node 51581 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree487_checked : NumberTheory.primeTreeChecked subtree487 := by
  norm_num only [subtree487, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree488 : BinaryTree ℕ :=
  .node 50551 subtree486 subtree487

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree488_checked : NumberTheory.primeTreeChecked subtree488 := by
  exact ⟨by norm_num only, subtree486_checked, subtree487_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree489 : BinaryTree ℕ :=
  .node 49171 subtree485 subtree488

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree489_checked : NumberTheory.primeTreeChecked subtree489 := by
  exact ⟨by norm_num only, subtree485_checked, subtree488_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree490 : BinaryTree ℕ :=
  .node 47317 subtree482 subtree489

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree490_checked : NumberTheory.primeTreeChecked subtree490 := by
  exact ⟨by norm_num only, subtree482_checked, subtree489_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree491 : BinaryTree ℕ :=
  (.node 52237
    (.node 51839 (.node 51719 (.node 51713 (.node 51613 .nil .nil) .nil) (.node 51797 .nil .nil))
      (.node 52021 (.node 51949 .nil .nil) (.node 52147 .nil .nil)))
    (.node 52541 (.node 52391 (.node 52363 (.node 52361 .nil .nil) .nil) (.node 52501 .nil .nil))
      (.node 52627 (.node 52553 .nil .nil) (.node 52691 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree491_checked : NumberTheory.primeTreeChecked subtree491 := by
  norm_num only [subtree491, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree492 : BinaryTree ℕ :=
  (.node 53377
    (.node 53117 (.node 52901 (.node 52733 (.node 52727 .nil .nil) .nil) (.node 52957 .nil .nil))
      (.node 53197 (.node 53161 .nil .nil) (.node 53269 .nil .nil)))
    (.node 53731 (.node 53503 (.node 53453 .nil .nil) (.node 53549 .nil .nil))
      (.node 54251 (.node 54059 .nil .nil) (.node 54269 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree492_checked : NumberTheory.primeTreeChecked subtree492 := by
  norm_num only [subtree492, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree493 : BinaryTree ℕ :=
  .node 52697 subtree491 subtree492

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree493_checked : NumberTheory.primeTreeChecked subtree493 := by
  exact ⟨by norm_num only, subtree491_checked, subtree492_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree494 : BinaryTree ℕ :=
  (.node 55001
    (.node 54869 (.node 54623 (.node 54443 (.node 54403 .nil .nil) .nil) (.node 54673 .nil .nil))
      (.node 54919 (.node 54917 .nil .nil) (.node 54973 .nil .nil)))
    (.node 55621 (.node 55163 (.node 55009 .nil .nil) (.node 55487 .nil .nil))
      (.node 55823 (.node 55819 .nil .nil) (.node 55871 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree494_checked : NumberTheory.primeTreeChecked subtree494 := by
  norm_num only [subtree494, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree495 : BinaryTree ℕ :=
  (.node 57143
    (.node 56687 (.node 56527 (.node 56239 (.node 56039 .nil .nil) .nil) (.node 56681 .nil .nil))
      (.node 56999 (.node 56713 .nil .nil) (.node 57041 .nil .nil)))
    (.node 57269 (.node 57191 (.node 57179 .nil .nil) (.node 57223 .nil .nil))
      (.node 57467 (.node 57413 .nil .nil) (.node 57593 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree495_checked : NumberTheory.primeTreeChecked subtree495 := by
  norm_num only [subtree495, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree496 : BinaryTree ℕ :=
  .node 55897 subtree494 subtree495

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree496_checked : NumberTheory.primeTreeChecked subtree496 := by
  exact ⟨by norm_num only, subtree494_checked, subtree495_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree497 : BinaryTree ℕ :=
  .node 54323 subtree493 subtree496

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree497_checked : NumberTheory.primeTreeChecked subtree497 := by
  exact ⟨by norm_num only, subtree493_checked, subtree496_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree498 : BinaryTree ℕ :=
  (.node 59119
    (.node 58727 (.node 58427 (.node 58147 (.node 57847 .nil .nil) .nil) (.node 58567 .nil .nil))
      (.node 59069 (.node 58763 .nil .nil) (.node 59083 .nil .nil)))
    (.node 59629 (.node 59387 (.node 59377 .nil .nil) (.node 59627 .nil .nil))
      (.node 59809 (.node 59743 .nil .nil) (.node 59879 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree498_checked : NumberTheory.primeTreeChecked subtree498 := by
  norm_num only [subtree498, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree499 : BinaryTree ℕ :=
  (.node 62131
    (.node 60859 (.node 60623 (.node 60383 (.node 60107 .nil .nil) .nil) (.node 60631 .nil .nil))
      (.node 61357 (.node 61001 .nil .nil) (.node 61469 .nil .nil)))
    (.node 62549 (.node 62297 (.node 62201 .nil .nil) (.node 62327 .nil .nil))
      (.node 63197 (.node 62927 .nil .nil) (.node 63541 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree499_checked : NumberTheory.primeTreeChecked subtree499 := by
  norm_num only [subtree499, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree500 : BinaryTree ℕ :=
  .node 59887 subtree498 subtree499

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree500_checked : NumberTheory.primeTreeChecked subtree500 := by
  exact ⟨by norm_num only, subtree498_checked, subtree499_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree501 : BinaryTree ℕ :=
  (.node 68791
    (.node 66071 (.node 65327 (.node 64817 (.node 63809 .nil .nil) .nil) (.node 65651 .nil .nil))
      (.node 68053 (.node 67511 .nil .nil) (.node 68633 .nil .nil)))
    (.node 70111 (.node 68947 (.node 68909 .nil .nil) (.node 69929 .nil .nil))
      (.node 71081 (.node 70309 .nil .nil) (.node 71293 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree501_checked : NumberTheory.primeTreeChecked subtree501 := by
  norm_num only [subtree501, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree502 : BinaryTree ℕ :=
  (.node 76831
    (.node 73721 (.node 73351 (.node 72253 (.node 71789 .nil .nil) .nil) (.node 73421 .nil .nil))
      (.node 75913 (.node 75041 .nil .nil) (.node 76463 .nil .nil)))
    (.node 89519 (.node 78889 (.node 77587 .nil .nil) (.node 80809 .nil .nil))
      (.node 91283 (.node 90001 .nil .nil) (.node 105649 .nil .nil))))

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree502_checked : NumberTheory.primeTreeChecked subtree502 := by
  norm_num only [subtree502, NumberTheory.primeTreeChecked]
  simp only [true_and]

/-- A balanced subtree of submitted prime labels. -/
def subtree503 : BinaryTree ℕ :=
  .node 71347 subtree501 subtree502

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree503_checked : NumberTheory.primeTreeChecked subtree503 := by
  exact ⟨by norm_num only, subtree501_checked, subtree502_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree504 : BinaryTree ℕ :=
  .node 63703 subtree500 subtree503

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree504_checked : NumberTheory.primeTreeChecked subtree504 := by
  exact ⟨by norm_num only, subtree500_checked, subtree503_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree505 : BinaryTree ℕ :=
  .node 57839 subtree497 subtree504

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree505_checked : NumberTheory.primeTreeChecked subtree505 := by
  exact ⟨by norm_num only, subtree497_checked, subtree504_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree506 : BinaryTree ℕ :=
  .node 51607 subtree490 subtree505

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree506_checked : NumberTheory.primeTreeChecked subtree506 := by
  exact ⟨by norm_num only, subtree490_checked, subtree505_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree507 : BinaryTree ℕ :=
  .node 44641 subtree475 subtree506

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree507_checked : NumberTheory.primeTreeChecked subtree507 := by
  exact ⟨by norm_num only, subtree475_checked, subtree506_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree508 : BinaryTree ℕ :=
  .node 37853 subtree444 subtree507

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree508_checked : NumberTheory.primeTreeChecked subtree508 := by
  exact ⟨by norm_num only, subtree444_checked, subtree507_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree509 : BinaryTree ℕ :=
  .node 30829 subtree381 subtree508

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree509_checked : NumberTheory.primeTreeChecked subtree509 := by
  exact ⟨by norm_num only, subtree381_checked, subtree508_checked⟩

/-- A balanced subtree of submitted prime labels. -/
def subtree510 : BinaryTree ℕ :=
  .node 19469 subtree254 subtree509

/-- All labels are prime, by normalization at the leaves and shared child proofs.
This invariant supplies primality for every capped catalog enumeration. -/
private theorem subtree510_checked : NumberTheory.primeTreeChecked subtree510 := by
  exact ⟨by norm_num only, subtree254_checked, subtree509_checked⟩

/-- Balanced catalog of the submitted prime witnesses.
Ordering permits capped enumeration; primality is certified separately. -/
def catalog : BinaryTree ℕ :=
  subtree510

/-- Every catalog label is prime. Combine the previously checked subtrees.
This proof is shared by all direct residue coverage certificates. -/
theorem catalog_checked : NumberTheory.primeTreeChecked catalog := by exact subtree510_checked

end PseudoPrime.LLS.Corollary12PrimeCatalog
