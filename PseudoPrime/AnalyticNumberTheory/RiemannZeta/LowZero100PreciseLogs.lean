/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PreciseLogArithmetic
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PreciseLogs.Block00
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PreciseLogs.Block01
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PreciseLogs.Block02
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PreciseLogs.Block03
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PreciseLogs.Block04
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PreciseLogs.Block05
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PreciseLogs.Block06
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PreciseLogs.Block07

/-! # Shared precise logarithm checks for the low-zero endpoints -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

private theorem endpoint_precise_log_of_block (n a : ℕ)
    (hblock : ∀ i : Fin 16, endpointPreciseLogCheck (i.val + a) = true) (ha : a ≤ n)
    (hb : n < a + 16) : endpointPreciseLogCheck n = true := by
  have hi : n - a < 16 := Nat.sub_lt_left_of_lt_add ha hb
  simpa only [Fin.val_mk, Nat.sub_add_cancel ha] using hblock ⟨n - a, hi⟩

/-- Every integer from 1 through 128 passes the precise rational logarithm check.
The proof combines eight independently kernel-checked blocks without indexing a list. -/
theorem endpoint_precise_log_checks (n : ℕ) (hn : n ∈ Finset.Icc (1 : ℕ) 128) :
    endpointPreciseLogCheck n = true := by
  have hn1 := (Finset.mem_Icc.mp hn).1
  have hn128 := (Finset.mem_Icc.mp hn).2
  by_cases h1 : n < 17
  · exact endpoint_precise_log_of_block n 1 endpoint_precise_log_block00 hn1 h1
  by_cases h2 : n < 33
  · exact endpoint_precise_log_of_block n 17 endpoint_precise_log_block01 (Nat.le_of_not_gt h1) h2
  by_cases h3 : n < 49
  · exact endpoint_precise_log_of_block n 33 endpoint_precise_log_block02 (Nat.le_of_not_gt h2) h3
  by_cases h4 : n < 65
  · exact endpoint_precise_log_of_block n 49 endpoint_precise_log_block03 (Nat.le_of_not_gt h3) h4
  by_cases h5 : n < 81
  · exact endpoint_precise_log_of_block n 65 endpoint_precise_log_block04 (Nat.le_of_not_gt h4) h5
  by_cases h6 : n < 97
  · exact endpoint_precise_log_of_block n 81 endpoint_precise_log_block05 (Nat.le_of_not_gt h5) h6
  by_cases h7 : n < 113
  · exact endpoint_precise_log_of_block n 97 endpoint_precise_log_block06 (Nat.le_of_not_gt h6) h7
  · exact
      endpoint_precise_log_of_block n 113 endpoint_precise_log_block07 (Nat.le_of_not_gt h7)
        (Nat.lt_succ_of_le hn128)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
