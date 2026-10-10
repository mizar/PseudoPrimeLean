/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.CayleyIntegral
public import Mathlib.Topology.Algebra.Support

/-!
# Compactly supported Cayley circle tests

The real-height Cayley map is an open embedding. Compactly supported functions extend
continuously by zero, and weighted tests convert circle averages into real-line integrals.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The real-height Cayley parametrization is continuous.
Compose continuous arctangent, its affine angular coordinate, and circle exponential. -/
theorem continuous_cayleyCircle : Continuous cayleyCircle :=
  Circle.exp.continuous.comp ((Real.continuous_arctan.const_mul 2).add_const Real.pi)

/-- Distinct finite real heights give distinct Cayley circle points.
Their angles lie strictly between zero and two pi, where the exponential is injective;
arctangent injectivity then recovers the height. -/
theorem cayleyCircle_injective : Function.Injective cayleyCircle := by
  intro t u h
  have ht := Real.arctan_mem_Ioo t
  have hu := Real.arctan_mem_Ioo u
  have htu :=
    Circle.exp_injOn_of_forall_sub_mem_Ioo (s := Set.Ioo (0 : ℝ) (2 * Real.pi))
      (fun x hx y hy => by constructor <;> linarith only [hx.1, hx.2, hy.1, hy.2])
      (show 2 * Real.arctan t + Real.pi ∈ Set.Ioo 0 (2 * Real.pi) from
        ⟨by linarith only [ht.1], by linarith only [ht.2]⟩)
      (show 2 * Real.arctan u + Real.pi ∈ Set.Ioo 0 (2 * Real.pi) from
        ⟨by linarith only [hu.1], by linarith only [hu.2]⟩)
      h
  apply Real.arctan_injective
  linarith only [htu]

/-- The Cayley parameter is an open embedding into the real line.
Its strictly increasing map has the open, order-connected range (0,1). -/
theorem isOpenEmbedding_cayleyParameter : Topology.IsOpenEmbedding cayleyParameter := by
  refine ⟨cayleyParameter_strictMono.isEmbedding_of_ordConnected ?_, ?_⟩
  · rw [range_cayleyParameter]
    exact Set.ordConnected_Ioo
  · rw [range_cayleyParameter]
    exact isOpen_Ioo

/-- The Cayley map is an open embedding of the real line into the circle.
Combine the open arctangent coordinate with the locally homeomorphic circle exponential
and use injectivity; this permits continuous extension of compactly supported tests. -/
theorem isOpenEmbedding_cayleyCircle : Topology.IsOpenEmbedding cayleyCircle := by
  have ha : Topology.IsOpenEmbedding (fun t : ℝ => 2 * Real.pi * t) :=
    (Homeomorph.mulLeft₀ (2 * Real.pi) (mul_ne_zero two_ne_zero Real.pi_ne_zero)).isOpenEmbedding
  have ho :=
    isLocalHomeomorph_circleExp.isOpenMap.comp
      (ha.isOpenMap.comp isOpenEmbedding_cayleyParameter.isOpenMap)
  apply
    Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap continuous_cayleyCircle
      cayleyCircle_injective
  convert ho using 1
  funext t
  rw [Function.comp_apply, Function.comp_apply, cayleyParameter_angle]
  rfl

/-- Any continuous complex real-line function with compact support extends through
the Cayley embedding to a continuous circle function with the same pullback.
Transport to the open image and extend by zero; compact support ensures continuity at infinity. -/
theorem exists_circle_extension (g : ℝ → ℂ) (hg : Continuous g) (hs : HasCompactSupport g) :
    ∃ f : C(Circle, ℂ), ∀ t, f (cayleyCircle t) = g t := by
  let e := isOpenEmbedding_cayleyCircle.toIsEmbedding.toHomeomorph
  let h : Set.range cayleyCircle → ℂ := g ∘ e.symm
  have hc : Continuous h := hg.comp e.symm.continuous
  have hh : HasCompactSupport h := hs.comp_homeomorph e.symm
  let f : C(Circle, ℂ) :=
    ⟨Function.extend Subtype.val h 0,
      HasCompactSupport.continuous_extend_zero isOpenEmbedding_cayleyCircle.isOpen_range hc hh⟩
  refine ⟨f, fun t => ?_⟩
  have he :=
    congrFun (Function.extend_comp Subtype.val_injective h (0 : Circle → ℂ))
      (⟨cayleyCircle t, Set.mem_range_self t⟩ : Set.range cayleyCircle)
  change Function.extend Subtype.val h 0 (cayleyCircle t) = g t
  change
    Function.extend Subtype.val h 0 (cayleyCircle t) =
      h ⟨cayleyCircle t, Set.mem_range_self t⟩ at he
  rw [he]
  change g (e.symm ⟨cayleyCircle t, Set.mem_range_self t⟩) = g t
  rw [Topology.IsEmbedding.toHomeomorph_symm_apply]

/-- A continuous compactly supported real-line function g admits a continuous circle
test with pullback (1+t^2)*g(t) and circle average (integral g)/pi.
Extend the weighted function by zero and cancel the positive Jacobian denominator.
Half its average recovers the kernel integral normalized by two pi. -/
theorem exists_circle_weighted_extension (g : ℝ → ℂ) (hg : Continuous g)
    (hs : HasCompactSupport g) :
    ∃ f : C(Circle, ℂ),
      (∀ t, f (cayleyCircle t) = ((1 + t ^ 2 : ℝ) : ℂ) * g t) ∧
        circleAverage f = (1 / Real.pi : ℝ) • ∫ t : ℝ, g t := by
  let w : ℝ → ℂ := fun t => ((1 + t ^ 2 : ℝ) : ℂ)
  have hw : Continuous w :=
    Complex.continuous_ofReal.comp (continuous_const.add (continuous_id.pow 2))
  obtain ⟨f, hf⟩ := exists_circle_extension (w * g) (hw.mul hg) hs.mul_left
  refine ⟨f, hf, ?_⟩
  rw [circleAverage_cayleyCircle]
  have he :
    ∀ t : ℝ, (1 / (Real.pi * (1 + t ^ 2))) • f (cayleyCircle t) = (1 / Real.pi : ℝ) • g t := by
    intro t
    rw [hf]
    change (1 / (Real.pi * (1 + t ^ 2))) • (((1 + t ^ 2 : ℝ) : ℂ) * g t) = _
    rw [← Complex.real_smul, smul_smul]
    congr 1
    rw [← div_div]
    exact div_mul_cancel₀ _ (by nlinarith only [sq_nonneg t] : (1 + t ^ 2 : ℝ) ≠ 0)
  rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ he)]
  exact MeasureTheory.integral_smul _ _

end PseudoPrime.Analysis
