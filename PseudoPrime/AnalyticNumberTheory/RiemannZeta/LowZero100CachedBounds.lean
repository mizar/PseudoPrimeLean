/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100CachedArithmetic
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PreciseRotatedBounds
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100CacheIdentity

/-! # Soundness of cached low-zero endpoint evaluation -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

private theorem endpoint_cached_finite_eq (t : ℚ) :
    endpointCachedFinite t = endpointPreciseFinite t := by
  have hs :
    (∑ n ∈ Finset.Icc (1 : ℕ) 127, endpointPowerApprox t (endpointCachedLog n)) =
      (∑ n ∈ Finset.Icc (1 : ℕ) 127, endpointPowerApprox t (endpointPreciseLog n)) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [endpoint_cached_logs_eq n
        (Finset.mem_Icc.mpr
          ⟨(Finset.mem_Icc.mp hn).1, Nat.le_trans (Finset.mem_Icc.mp hn).2 (by norm_num only)⟩)]
  have h128 := endpoint_cached_logs_eq 128 (Finset.mem_Icc.mpr ⟨by norm_num only, by norm_num only⟩)
  simp only [endpointCachedFinite, endpointPreciseFinite, endpointPreciseCorrection, hs, h128]

/-- For every rational ordinate, the cached and Taylor-based rotated finite calculations
agree exactly. The proof uses the 128 internally checked logarithm identities. -/
theorem endpoint_cached_rotated_eq (t : ℚ) :
    endpointCachedRotated t = endpointPreciseRotated t := by
  rw [endpointCachedRotated, endpointPreciseRotated, endpoint_cached_finite_eq t]

/-- For `14 ≤ t ≤ 100`, a successful precise phase check bounds the difference between
normalized zeta and the cached rational calculation by `3/2500000`. This transfers the
analytic estimate through the verified cached-logarithm identities. -/
theorem abs_endpoint_cached_zeta (t : ℚ) (ht14 : 14 ≤ t) (ht100 : t ≤ 100)
    (hcheck : endpointPrecisePhaseCheck t = true) :
    |RiemannXi.normalizedZeta t - ((endpointCachedRotated t).1 : ℝ)| ≤ 3 / 2500000 := by
  rw [endpoint_cached_rotated_eq]
  exact abs_endpoint_precise_zeta t ht14 ht100 hcheck

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
