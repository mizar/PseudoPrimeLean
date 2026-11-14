/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100CachedLogs
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100CacheChecks.Block00
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100CacheChecks.Block01
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100CacheChecks.Block02
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100CacheChecks.Block03
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100CacheChecks.Block04
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100CacheChecks.Block05
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100CacheChecks.Block06
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100CacheChecks.Block07

/-! # Identities for cached low-zero endpoint logarithms -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

private theorem endpoint_cached_log_of_block (n a : ℕ)
    (hblock : ∀ i : Fin 16, endpointCachedLog (i.val + a) = endpointPreciseLog (i.val + a))
    (ha : a ≤ n) (hb : n < a + 16) : endpointCachedLog n = endpointPreciseLog n := by
  have hi : n - a < 16 := Nat.sub_lt_left_of_lt_add ha hb
  simpa only [Fin.val_mk, Nat.sub_add_cancel ha] using hblock ⟨n - a, hi⟩

/-- For every integer from 1 through 128, the cached logarithm equals its Taylor calculation.
The proof combines eight independently kernel-checked blocks without indexing a list. -/
theorem endpoint_cached_logs_eq (n : ℕ) (hn : n ∈ Finset.Icc (1 : ℕ) 128) :
    endpointCachedLog n = endpointPreciseLog n := by
  have hn1 := (Finset.mem_Icc.mp hn).1
  have hn128 := (Finset.mem_Icc.mp hn).2
  by_cases h1 : n < 17
  · exact endpoint_cached_log_of_block n 1 endpoint_cached_log_block00 hn1 h1
  by_cases h2 : n < 33
  · exact endpoint_cached_log_of_block n 17 endpoint_cached_log_block01 (Nat.le_of_not_gt h1) h2
  by_cases h3 : n < 49
  · exact endpoint_cached_log_of_block n 33 endpoint_cached_log_block02 (Nat.le_of_not_gt h2) h3
  by_cases h4 : n < 65
  · exact endpoint_cached_log_of_block n 49 endpoint_cached_log_block03 (Nat.le_of_not_gt h3) h4
  by_cases h5 : n < 81
  · exact endpoint_cached_log_of_block n 65 endpoint_cached_log_block04 (Nat.le_of_not_gt h4) h5
  by_cases h6 : n < 97
  · exact endpoint_cached_log_of_block n 81 endpoint_cached_log_block05 (Nat.le_of_not_gt h5) h6
  by_cases h7 : n < 113
  · exact endpoint_cached_log_of_block n 97 endpoint_cached_log_block06 (Nat.le_of_not_gt h6) h7
  · exact
      endpoint_cached_log_of_block n 113 endpoint_cached_log_block07 (Nat.le_of_not_gt h7)
        (Nat.lt_succ_of_le hn128)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
