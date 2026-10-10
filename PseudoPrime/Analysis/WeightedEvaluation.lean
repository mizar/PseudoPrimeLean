/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Summable positive weighted evaluation of continuous functions

Nonnegative summable atomic weights define a continuous complex linear functional.
The total mass bounds its operator norm and the error of uniform approximation.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For points in a compact space and nonnegative real weights, each weighted complex
evaluation of a continuous function has norm at most its weight times the supremum norm.
Use positivity to remove the absolute value of the weight.
This is the common majorant for weighted atomic series. -/
theorem norm_weightedEvalTerm_le {ι X : Type*} [TopologicalSpace X] [CompactSpace X] (p : ι → X)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (f : C(X, ℂ)) (i : ι) : ‖(w i : ℂ) * f (p i)‖ ≤ w i * ‖f‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i)]
  exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (hw i)

/-- Nonnegative summable real weights on points of a compact space make every weighted
continuous complex evaluation series absolutely convergent. Bound the evaluation by
the supremum norm times the weight. This justifies addition and scalar multiplication
inside the atomic functional. -/
theorem summable_weightedEval {ι X : Type*} [TopologicalSpace X] [CompactSpace X] (p : ι → X)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : Summable w) (f : C(X, ℂ)) :
    Summable (fun i => (w i : ℂ) * f (p i)) := by
  exact (hs.mul_right ‖f‖).of_norm_bounded (norm_weightedEvalTerm_le p w hw f)

/-- For nonnegative summable weights, the weighted evaluation sum of a continuous
complex function has norm at most total mass times its supremum norm.
Apply the norm comparison for series to the summable scalar majorant.
This is the boundedness estimate for the atomic functional. -/
theorem norm_weightedEvalSum_le {ι X : Type*} [TopologicalSpace X] [CompactSpace X] (p : ι → X)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : Summable w) (f : C(X, ℂ)) :
    ‖∑' i, (w i : ℂ) * f (p i)‖ ≤ (∑' i, w i) * ‖f‖ := by
  exact tsum_of_norm_bounded (hs.hasSum.mul_right ‖f‖) (norm_weightedEvalTerm_le p w hw f)

/-- For points in a compact space with nonnegative summable real weights, send each
continuous complex function to its weighted evaluation series.
Absolute convergence permits addition and complex scalar multiplication termwise.
This linear map is promoted to a continuous map by the total-mass bound. -/
noncomputable def weightedEvalLinearMap {ι X : Type*} [TopologicalSpace X] [CompactSpace X]
    (p : ι → X) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : Summable w) : C(X, ℂ) →ₗ[ℂ] ℂ
    where
  toFun f := ∑' i, (w i : ℂ) * f (p i)
  map_add' f g := by
    simp only [ContinuousMap.add_apply, mul_add]
    exact (summable_weightedEval p w hw hs f).tsum_add (summable_weightedEval p w hw hs g)
  map_smul' c f := by
    simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [show (fun i => (w i : ℂ) * (c * f (p i))) = (fun i => c * ((w i : ℂ) * f (p i))) by
        funext i; ring]
    exact tsum_mul_left

/-- The continuous complex linear functional given by summable nonnegative atomic
weights on points of a compact space. Its value is the weighted evaluation series,
and total mass bounds the operator norm. This gives a common interface for uniform
approximation of weighted zero distributions. -/
noncomputable def weightedEval {ι X : Type*} [TopologicalSpace X] [CompactSpace X] (p : ι → X)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : Summable w) : C(X, ℂ) →L[ℂ] ℂ :=
  (weightedEvalLinearMap p w hw hs).mkContinuous (∑' i, w i) (norm_weightedEvalSum_le p w hw hs)

/-- The positive atomic functional evaluates a continuous function by its weighted
series. This is the defining formula after promotion to a continuous linear map.
It connects moment identities to the functional interface. -/
theorem weightedEval_apply {ι X : Type*} [TopologicalSpace X] [CompactSpace X] (p : ι → X)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : Summable w) (f : C(X, ℂ)) :
    weightedEval p w hw hs f = ∑' i, (w i : ℂ) * f (p i) :=
  rfl

/-- The operator norm of the positive atomic functional is at most the total weight.
Use nonnegativity of total mass and the pointwise supremum-norm estimate.
This uniform bound permits extending convergence from dense test functions. -/
theorem norm_weightedEval_le {ι X : Type*} [TopologicalSpace X] [CompactSpace X] (p : ι → X)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : Summable w) : ‖weightedEval p w hw hs‖ ≤ ∑' i, w i := by
  apply ContinuousLinearMap.opNorm_le_bound _ (tsum_nonneg hw)
  exact norm_weightedEvalSum_le p w hw hs

/-- For two continuous complex functions on a compact space, the difference of their
weighted evaluations has norm at most total mass times their uniform distance.
Use linearity and the evaluation norm bound. This controls the error when approximating
continuous test functions by finite combinations of monomials. -/
theorem norm_weightedEval_sub_le {ι X : Type*} [TopologicalSpace X] [CompactSpace X] (p : ι → X)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : Summable w) (f g : C(X, ℂ)) :
    ‖weightedEval p w hw hs f - weightedEval p w hw hs g‖ ≤ (∑' i, w i) * ‖f - g‖ := by
  rw [← map_sub]
  exact norm_weightedEvalSum_le p w hw hs (f - g)

end PseudoPrime.Analysis
