/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.LSeries.HurwitzZetaEven

/-! # Finite sums of weak functional-equation pairs -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- A finite sum of functions locally integrable on the positive half-line
is locally integrable there. This is used for finite theta-kernel sums. -/
theorem locallyIntegrableOn_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ)
    (hf : ∀ i ∈ s, MeasureTheory.LocallyIntegrableOn (f i) (Set.Ioi 0)) :
    MeasureTheory.LocallyIntegrableOn (Finset.sum s f) (Set.Ioi 0) :=
  Finset.sum_induction f (fun g ↦ MeasureTheory.LocallyIntegrableOn g (Set.Ioi 0))
    (fun _ _ ↦ MeasureTheory.LocallyIntegrableOn.add) (MeasureTheory.locallyIntegrableOn_const 0) hf

/-- Form a weak functional-equation pair by a weighted finite sum of pairs
of weight one. Their root numbers are absorbed into the second kernel, so
the resulting pair has root number one. -/
noncomputable def sumWeakFEPair {ι : Type*} [Fintype ι] (P : ι → WeakFEPair ℂ)
    (hk : ∀ i, (P i).k = 1) (w : ι → ℂ) : WeakFEPair ℂ
    where
  f := Finset.sum Finset.univ (fun i ↦ w i • (P i).f)
  g := Finset.sum Finset.univ (fun i ↦ (w i * (P i).ε) • (P i).g)
  k := 1
  ε := 1
  f₀ := Finset.sum Finset.univ (fun i ↦ w i * (P i).f₀)
  g₀ := Finset.sum Finset.univ (fun i ↦ w i * (P i).ε * (P i).g₀)
  hf_int := locallyIntegrableOn_sum Finset.univ _ (fun i _ ↦ (P i).hf_int.smul (w i))
  hg_int := locallyIntegrableOn_sum Finset.univ _ (fun i _ ↦ (P i).hg_int.smul (w i * (P i).ε))
  hk := zero_lt_one
  hε := one_ne_zero
  h_feq x hx := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, one_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [(P i).h_feq x hx, hk i]
    simp only [smul_eq_mul]
    ring
  hf_top r := by
    have h :=
      Asymptotics.IsBigO.fun_sum (s := Finset.univ)
        (fun i _ ↦ ((P i).hf_top r).const_mul_left (w i))
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← Finset.sum_sub_distrib,
      mul_sub] using h
  hg_top r := by
    have h :=
      Asymptotics.IsBigO.fun_sum (s := Finset.univ)
        (fun i _ ↦ ((P i).hg_top r).const_mul_left (w i * (P i).ε))
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← Finset.sum_sub_distrib,
      mul_sub] using h

end PseudoPrime.Analysis
