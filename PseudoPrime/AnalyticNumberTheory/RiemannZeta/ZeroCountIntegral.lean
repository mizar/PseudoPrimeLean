/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeightCounting
import PseudoPrime.Analysis.FiniteHeightAbel

/-! # Integrability of height-counting functions

Identify the closed-height zero count with a finite step-function prefix.
-/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For `0 ≤ t ≤ T`, the nontrivial zero count at `t` is the finite height
prefix taken over the ledger through `T`. The closed endpoint is preserved. -/
private theorem zeroCount_eq_heightPrefix {T t : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    Analysis.FiniteHeightAbel.heightPrefix (zerosUpTo T) (fun ρ ↦ |ρ.im|)
        (fun ρ ↦ (riemannZetaZeroMultiplicity ρ : ℝ)) t =
      zeroCount t := by
  classical
  rw [zeroCount_eq_sum]
  unfold Analysis.FiniteHeightAbel.heightPrefix
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext ρ
    rw [Finset.mem_filter, mem_zerosUpTo (ht.trans htT), mem_zerosUpTo ht]
    constructor
    · rintro ⟨⟨hz, hre, hT⟩, hheight⟩
      exact ⟨hz, hre, hheight⟩
    · rintro ⟨hz, hre, hheight⟩
      exact ⟨⟨hz, hre, hheight.trans htT⟩, hheight⟩
  · intro ρ hρ
    rfl

/-- The nontrivial zero count is interval integrable on `0 ≤ a ≤ b`.
On this interval it agrees with a finite sum of integrable step functions. -/
theorem zeroCount_integrable {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable zeroCount MeasureTheory.volume a b := by
  have h :=
    Analysis.FiniteHeightAbel.intervalIntegrable_prefix (zerosUpTo b) (fun ρ ↦ |ρ.im|)
      (fun ρ ↦ (riemannZetaZeroMultiplicity ρ : ℝ)) a b
  apply h.congr
  intro t ht
  rw [Set.uIoc_of_le hab] at ht
  exact zeroCount_eq_heightPrefix (ha.trans ht.1.le) ht.2

/-- For `0 < a ≤ b`, the zero count times the inverse-square kernel is
interval integrable. Multiply the finite-prefix count by a continuous kernel. -/
theorem zeroCount_invSq_integrable {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t ↦ zeroCount t / t ^ 2) MeasureTheory.volume a b := by
  have hp := zeroCount_integrable ha.le hab
  have hc : ContinuousOn (fun t : ℝ ↦ t⁻¹ ^ 2) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    intro t ht
    exact ((continuousAt_id.inv₀ (ne_of_gt (lt_of_lt_of_le ha ht.1))).pow 2) |>.continuousWithinAt
  have h := hp.mul_continuousOn hc
  simpa only [div_eq_mul_inv, ← inv_pow] using h

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
