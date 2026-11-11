/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Algebra.Module.LocallyConvex

/-! # Continuous logarithms and arguments along real intervals -/

public section

namespace PseudoPrime.Analysis

/-- A continuous nonzero complex-valued function on a nonempty closed real
interval admits a continuous logarithm on that interval. Extend the function
by clamping to the endpoints and lift it through the complex exponential. -/
theorem exists_continuous_log_Icc {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (hne : ∀ x ∈ Set.Icc a b, f x ≠ 0) :
    ∃ g : ℝ → ℂ, ContinuousOn g (Set.Icc a b) ∧ ∀ x ∈ Set.Icc a b, Complex.exp (g x) = f x := by
  let clamp : ℝ → ℝ := fun x ↦ min (max x a) b
  have hclamp : Continuous clamp := (continuous_id.max continuous_const).min continuous_const
  have hmem (x : ℝ) : clamp x ∈ Set.Icc a b := by
    exact ⟨le_min (le_max_right _ _) hab, min_le_right _ _⟩
  have hcont : Continuous (f ∘ clamp) := hf.comp_continuous hclamp hmem
  have : ContractibleSpace (Set.univ : Set ℝ) :=
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)).contractibleSpace Set.univ_nonempty
  have hsimple : IsSimplyConnected (Set.univ : Set ℝ) :=
    SimplyConnectedSpace.ofContractible (Set.univ : Set ℝ)
  have hnonzero : 0 ∉ (f ∘ clamp) '' (Set.univ : Set ℝ) := by
    rintro ⟨x, hx, heq⟩
    exact hne (clamp x) (hmem x) heq
  obtain ⟨g, hg, he⟩ :=
    Complex.exists_continuousOn_eqOn_exp_comp hsimple isOpen_univ hcont.continuousOn hnonzero
  refine ⟨g, hg.mono (Set.subset_univ _), ?_⟩
  intro x hx
  have hh : clamp x = x := by
    dsimp only [clamp]
    rw [max_eq_left hx.1, min_eq_left hx.2]
  have he' := he (Set.mem_univ x)
  change Complex.exp (g x) = f (clamp x) at he'
  rwa [hh] at he'

/-- A continuous logarithm on a nonempty closed interval can be normalized
to any prescribed logarithm of the right endpoint. Translate a continuous
lift by the difference between the prescribed value and its endpoint. -/
theorem exists_continuous_log_Icc_with_value {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (hne : ∀ x ∈ Set.Icc a b, f x ≠ 0) {w : ℂ}
    (hw : Complex.exp w = f b) :
    ∃ g : ℝ → ℂ,
      ContinuousOn g (Set.Icc a b) ∧ (∀ x ∈ Set.Icc a b, Complex.exp (g x) = f x) ∧ g b = w := by
  obtain ⟨h, hh, he⟩ := exists_continuous_log_Icc hab hf hne
  let g : ℝ → ℂ := fun x => h x + (w - h b)
  have hb : b ∈ Set.Icc a b := ⟨hab, le_refl b⟩
  refine ⟨g, hh.add continuousOn_const, ?_, ?_⟩
  · intro x hx
    dsimp only [g]
    rw [Complex.exp_add, Complex.exp_sub, hw, he b hb, div_self (hne b hb), mul_one, he x hx]
  · dsimp only [g]
    ring

/-- A continuous nonzero complex-valued function on a nonempty closed real
interval admits a continuous real argument. Taking the imaginary part of a
continuous logarithm yields the polar identity on the whole interval. -/
theorem exists_continuous_arg_Icc {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (hne : ∀ x ∈ Set.Icc a b, f x ≠ 0) :
    ∃ φ : ℝ → ℝ,
      ContinuousOn φ (Set.Icc a b) ∧
        ∀ x ∈ Set.Icc a b, f x = (‖f x‖ : ℂ) * Complex.exp ((φ x : ℂ) * Complex.I) := by
  obtain ⟨g, hg, he⟩ := exists_continuous_log_Icc hab hf hne
  refine ⟨fun x ↦ (g x).im, Complex.continuous_im.comp_continuousOn hg, ?_⟩
  intro x hx
  have hnorm : ‖f x‖ = Real.exp (g x).re := by rw [← he x hx, Complex.norm_exp]
  calc
    f x = Complex.exp (g x) := (he x hx).symm
    _ = (Real.exp (g x).re : ℂ) * Complex.exp (((g x).im : ℂ) * Complex.I) := by
      calc
        Complex.exp (g x) = Complex.exp (((g x).re : ℂ) + ((g x).im : ℂ) * Complex.I) :=
          congrArg Complex.exp (Complex.re_add_im (g x)).symm
        _ = (Real.exp (g x).re : ℂ) * Complex.exp (((g x).im : ℂ) * Complex.I) := by
          rw [Complex.exp_add, Complex.ofReal_exp]
    _ = (‖f x‖ : ℂ) * Complex.exp (((g x).im : ℂ) * Complex.I) := by rw [hnorm]

/-- A nonzero continuous path on a nonempty closed interval admits a
continuous polar argument whose right-end value is the imaginary part of a
prescribed logarithm of that endpoint. Normalize the continuous logarithm
first and then take its imaginary part. -/
theorem exists_continuous_arg_Icc_with_value {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (hne : ∀ x ∈ Set.Icc a b, f x ≠ 0) {w : ℂ}
    (hw : Complex.exp w = f b) :
    ∃ φ : ℝ → ℝ,
      ContinuousOn φ (Set.Icc a b) ∧
        (∀ x ∈ Set.Icc a b, f x = (‖f x‖ : ℂ) * Complex.exp ((φ x : ℂ) * Complex.I)) ∧
        φ b = w.im := by
  obtain ⟨g, hg, he, hb⟩ := exists_continuous_log_Icc_with_value hab hf hne hw
  refine ⟨fun x ↦ (g x).im, Complex.continuous_im.comp_continuousOn hg, ?_, ?_⟩
  · intro x hx
    have hnorm : ‖f x‖ = Real.exp (g x).re := by rw [← he x hx, Complex.norm_exp]
    calc
      f x = Complex.exp (g x) := (he x hx).symm
      _ = (Real.exp (g x).re : ℂ) * Complex.exp (((g x).im : ℂ) * Complex.I) := by
        calc
          Complex.exp (g x) = Complex.exp (((g x).re : ℂ) + ((g x).im : ℂ) * Complex.I) :=
            congrArg Complex.exp (Complex.re_add_im (g x)).symm
          _ = (Real.exp (g x).re : ℂ) * Complex.exp (((g x).im : ℂ) * Complex.I) := by
            rw [Complex.exp_add, Complex.ofReal_exp]
      _ = (‖f x‖ : ℂ) * Complex.exp (((g x).im : ℂ) * Complex.I) := by rw [hnorm]
  · exact congrArg Complex.im hb

end PseudoPrime.Analysis
