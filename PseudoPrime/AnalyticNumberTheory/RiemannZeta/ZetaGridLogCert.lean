/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridLogArithmetic

/-! # Kernel-checked logarithms for the height-100 grid -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

set_option maxRecDepth 4096 in
-- The finite universal decision traverses 512 certificates and needs deeper recursion.
set_option maxHeartbeats 0 in
-- The kernel performs exact rational Taylor checks for all 512 integers.
/-- All logarithm checks for `1 ≤ n ≤ 512` succeed. The values are computed
from rational Taylor bounds, and the finite universal statement is verified
by the kernel without importing a table or using list indexing. -/
theorem grid_log_check_all : ∀ n ∈ Finset.Icc (1 : ℕ) 512, gridLogCheck n = true := by
  have h : ∀ i : Fin 512, gridLogCheck (1 + i.val) = true := by decide +kernel
  intro n hn
  have hn1 := (Finset.mem_Icc.mp hn).1
  have hn2 := (Finset.mem_Icc.mp hn).2
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn1
  have hlt : n - 1 < 512 := lt_of_lt_of_le (Nat.sub_lt hnpos Nat.zero_lt_one) hn2
  have heq : 1 + (n - 1) = n := by rw [Nat.add_comm, Nat.sub_add_cancel hn1]
  simpa only [Fin.val_mk, heq] using h ⟨n - 1, hlt⟩

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
