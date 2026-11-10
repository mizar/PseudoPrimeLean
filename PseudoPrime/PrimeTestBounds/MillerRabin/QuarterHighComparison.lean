/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterHighSupport
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTriangularAverage
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterScaleOneAbel

/-! # High-index triangular subgroup comparison -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Divide the two-scale principal comparison by a positive index after
bounding the conductor cost by `(h - 1)T`. Nonnegative width and scale let
the negative width correction be discarded, yielding the scalar inequality
used by the large-index contradiction. -/
theorem quarter_high_comparison_scalar {h a T C Q P S : ℝ} (hh : 1 ≤ h) (ha : 0 ≤ a) (hT : 0 ≤ T)
    (hC : C ≤ (h - 1) * T)
    (hmain : h * Q + 2 * (h - 1) * P ≤ S + 2 * a * C + (-3 * a + 18) * (h - 1)) :
    Q + 2 * P ≤ 2 * a * T + 18 + (S + 2 * P) / h := by
  have hh0 : 0 < h := by linarith only [hh]
  have hmul := mul_le_mul_of_nonneg_left hC (show 0 ≤ 2 * a by linarith only [ha])
  have hdisc := mul_nonneg (sub_nonneg.mpr hh) ha
  have hTprod := mul_nonneg ha hT
  have hbound : (Q + 2 * P - (2 * a * T + 18)) * h ≤ S + 2 * P := by
    nlinarith only [hmain, hmul, hdisc, hTprod]
  have hdiv := (le_div_iff₀ hh0).2 hbound
  linarith only [hdiv]

/-- Under GRH, if an odd input has no rejecting prime through a triangular
support endpoint `X ≥ 1`, the finite forward principal sum and the scale-one
principal sum satisfy the displayed two-scale inequality. The proof combines
the subgroup arithmetic lower bounds with the primitive-character upper
bound, keeping the exact conductor sum and the full forward principal sum.
This is the analytic comparison used by the high-index quarter-bound branch. -/
theorem quarter_high_principal_comparison {n : ℕ} [NeZero n] (hn : 1 < n) (ho : Odd n) {a X : ℝ}
    (ha : 0 < a) (hX : 1 ≤ X) (hbound : Real.log X = 2 * a)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hnone : ¬∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n)) :
    let K := LLS.PaperStatements.triangularMellinKernel ha
    let H := PrimeTest.fermatSubgroup n
    (H.index : ℝ) * (∑ m ∈ Finset.Icc 1 ⌊X⌋₊, (K.summand (1 : DirichletCharacter ℂ 1) X m).re) +
        2 * ((H.index : ℝ) - 1) * (∑' m : ℕ, K.summand (1 : DirichletCharacter ℂ 1) 1 m).re ≤
      (∑' m : ℕ, K.summand (1 : DirichletCharacter ℂ 1) X m).re +
        2 * a * LLS.PaperStatements.subgroupConductorLogSum H +
        (-3 * a + 18) * ((H.index : ℝ) - 1) := by
  classical
  let _ := Classical.propDecidable
  let K := LLS.PaperStatements.triangularMellinKernel ha
  let H := PrimeTest.fermatSubgroup n
  let A := NumberTheory.subgroupAnnihilator H
  let S := Finset.univ.erase (1 : A)
  let F := fun χ : A ↦ (∑' m : ℕ, K.summand χ.val.primitiveCharacter 1 m).re
  have hfront := quarter_forward_principal_le hn ho ha hX hnone
  have hcredit := quarter_scale_one_pair_lower hn ho ha hX hbound.ge hnone
  have hup := quarter_triangular_annihilator_bound ha H hGRH hX hbound
  have hinv (χ : A) : (∑' m : ℕ, K.summand (χ.val.primitiveCharacter)⁻¹ 1 m).re = F χ := by
    let : NeZero χ.val.conductor := ⟨χ.val.conductor_ne_zero⟩
    exact
      LLS.PaperStatements.MellinKernel.tsum_summand_inv_re_eq K χ.val.primitiveCharacter
        (by norm_num only)
  have heq := Finset.sum_congr (s₁ := S) rfl (fun χ _ ↦ hinv χ)
  dsimp only at hcredit hfront hup ⊢
  simp only [Finset.sum_add_distrib] at hcredit
  change
    _ ≤
      (∑ χ ∈ S, F χ) + ∑ χ ∈ S, (∑' m : ℕ, K.summand (χ.val.primitiveCharacter)⁻¹ 1 m).re at hcredit
  rw [heq] at hcredit
  change _ ≤ _ + ∑ χ ∈ S, (∑' m : ℕ, K.summand χ.val.primitiveCharacter X m).re at hfront
  change
    (∑ χ ∈ S, (∑' m : ℕ, K.summand χ.val.primitiveCharacter X m).re) + 2 * (∑ χ ∈ S, F χ) ≤ _ at hup
  linarith only [hfront, hcredit, hup]

/-- Under GRH, if an odd input has no rejecting prime through the triangular
support endpoint `X` and `log n ≤ T`, the finite forward principal sum plus
twice the scale-one principal sum is bounded by `2aT + 18` and the full
principal costs divided by the Fermat index. Bound the sum of primitive
conductor logarithms by the ambient level and divide the subgroup comparison
by its positive finite index. This is the main high-index analytic reduction. -/
theorem quarter_high_principal_divided {n : ℕ} [NeZero n] (hn : 1 < n) (ho : Odd n) {a X T : ℝ}
    (ha : 0 < a) (hX : 1 ≤ X) (hbound : Real.log X = 2 * a) (hT : 0 ≤ T) (hscale : Real.log n ≤ T)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hnone : ¬∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n)) :
    let K := LLS.PaperStatements.triangularMellinKernel ha
    let H := PrimeTest.fermatSubgroup n
    (∑ m ∈ Finset.Icc 1 ⌊X⌋₊, (K.summand (1 : DirichletCharacter ℂ 1) X m).re) +
        2 * (∑' m : ℕ, K.summand (1 : DirichletCharacter ℂ 1) 1 m).re ≤
      2 * a * T + 18 +
        ((∑' m : ℕ, K.summand (1 : DirichletCharacter ℂ 1) X m).re +
            2 * (∑' m : ℕ, K.summand (1 : DirichletCharacter ℂ 1) 1 m).re) /
          H.index := by
  let H := PrimeTest.fermatSubgroup n
  have hcard : 1 ≤ H.index := by
    rw [← NumberTheory.card_subgroupAnnihilator H]
    exact Fintype.card_pos
  have hindex : (1 : ℝ) ≤ H.index := by exact_mod_cast hcard
  have hcond := LLS.PaperStatements.subgroupConductorLogSum_le H
  have hmul := mul_le_mul_of_nonneg_left hscale (sub_nonneg.mpr hindex)
  have hcost : LLS.PaperStatements.subgroupConductorLogSum H ≤ ((H.index : ℝ) - 1) * T :=
    hcond.trans hmul
  have hmain := quarter_high_principal_comparison hn ho ha hX hbound hGRH hnone
  exact quarter_high_comparison_scalar hindex ha.le hT hcost hmain

/-- Under GRH and absence of a rejecting prime through `r²`, the finite
forward principal sum plus twice the scale-one principal sum is strictly
below `2aT + 31` when the Fermat index exceeds `floor r²`. Abel summation
and the unconditional Chebyshev estimate bound both principal sums. -/
theorem quarter_high_principal_cost {n : ℕ} [NeZero n] (hn : 1 < n) (ho : Odd n) {a r T : ℝ}
    (ha : 0 < a) (hr : 100 ≤ r) (hbound : Real.log (r ^ 2) = 2 * a) (hT : 0 ≤ T)
    (hscale : Real.log n ≤ T) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hindex : ⌊r ^ 2⌋₊ < (PrimeTest.fermatSubgroup n).index)
    (hnone :
      ¬∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n)) :
    let K := LLS.PaperStatements.triangularMellinKernel ha
    (∑ m ∈ Finset.Icc 1 ⌊r ^ 2⌋₊, (K.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) m).re) +
        2 * (∑' m : ℕ, K.summand (1 : DirichletCharacter ℂ 1) 1 m).re <
      2 * a * T + 31 := by
  have hr2 : (1 : ℝ) ≤ r ^ 2 := by nlinarith only [sq_nonneg (r - 100), hr]
  have hS := quarter_forward_principal_upper ha hr2 hbound
  have hP := quarter_scale_one_principal_le ha hr2 hbound
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by linarith only [hr])] at hP
  have hmain := quarter_high_principal_divided hn ho ha hr2 hbound hT hscale hGRH hnone
  have hcost := quarter_high_index_cost hr hindex hS hP
  dsimp only at hmain ⊢
  linarith only [hmain, hcost]

/-- The high-index comparison with the combined forward and scale-one sums
written as one Abel expression. Its nonnegative variation weight exposes the
Chebyshev lower bound needed for the final quantitative contradiction. -/
theorem quarter_high_abel_cost {n : ℕ} [NeZero n] (hn : 1 < n) (ho : Odd n) {a r T : ℝ} (ha : 0 < a)
    (hr : 100 ≤ r) (hbound : Real.log (r ^ 2) = 2 * a) (hT : 0 ≤ T) (hscale : Real.log n ≤ T)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hindex : ⌊r ^ 2⌋₊ < (PrimeTest.fermatSubgroup n).index)
    (hnone :
      ¬∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n)) :
    (2 * a * (r ^ 2) ^ (-1 / 2 : ℝ)) * Chebyshev.psi (r ^ 2) +
        (∫ t in Set.Ioc 1 (r ^ 2),
          (t ^ (-3 / 2 : ℝ) * (2 * a + 1 - Real.log t / 2)) * Chebyshev.psi t) <
      2 * a * T + 31 := by
  have hr2 : (1 : ℝ) ≤ r ^ 2 := by nlinarith only [sq_nonneg (r - 100), hr]
  have h := quarter_high_principal_cost hn ho ha hr hbound hT hscale hGRH hindex hnone
  dsimp only at h
  rw [quarter_joint_principal_abel ha hr2 hbound] at h
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
