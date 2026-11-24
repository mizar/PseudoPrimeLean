/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.SincDamping
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.OrdinateTail
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.SincTailAbel
import all PseudoPrime.Analysis.SineMajorant

/-! # Sinc bounds for finite integrated zero sums -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH a finite set of nontrivial zeros with positive absolute ordinates
contributes at most its multiplicity-weighted sinc sum and radial correction,
times the common endpoint factor for the additive explicit formula. -/
theorem integrated_sinc_sum_le (hRH : RiemannHypothesis) (S : Finset ℂ)
    (hz : ∀ ρ ∈ S, riemannZeta ρ = 0) (hr : ∀ ρ ∈ S, 0 ≤ ρ.re) (hy : ∀ ρ ∈ S, 0 < |ρ.im|) {x η : ℝ}
    (hx : 0 < x) (hη : 0 < η) :
    ‖∑ ρ ∈ S,
          (riemannZetaZeroMultiplicity ρ : ℂ) *
              ((x : ℂ) ^ (ρ + 1) - ((x * Real.exp (-η) : ℝ) : ℂ) ^ (ρ + 1)) /
            (ρ * (ρ + 1))‖ ≤
      x ^ (3 / 2 : ℝ) * (1 - Real.exp (-η)) *
        (∑ ρ ∈ S,
          (riemannZetaZeroMultiplicity ρ : ℝ) *
            (Analysis.sincWeight (η / 2 * |ρ.im|) / |ρ.im| + (3 / 2) / |ρ.im| ^ 2)) := by
  apply (norm_sum_le _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ρ hρ
  have hline :=
    RiemannXi.xi_zero_re_eq_half_of_riemannHypothesis hRH
      (RiemannXi.xi_zero_of_zeta_zero_of_re_nonneg (hz ρ hρ) (hr ρ hρ))
  rw [mul_div_assoc, norm_mul, Complex.norm_natCast, mul_left_comm]
  exact
    mul_le_mul_of_nonneg_left (Analysis.critical_power_diff_le hx hη hline (hy ρ hρ))
      (Nat.cast_nonneg _)

/-- Above height 100 the radial part of every finite integrated sum is bounded
by the full inverse-square tail, independently of the truncation height. -/
theorem integrated_sinc_above_hundred (hRH : RiemannHypothesis) (S : Finset ℂ)
    (hz : ∀ ρ ∈ S, riemannZeta ρ = 0) (hr : ∀ ρ ∈ S, 0 ≤ ρ.re) (hy : ∀ ρ ∈ S, 100 < |ρ.im|)
    {x η : ℝ} (hx : 0 < x) (hη : 0 < η) :
    ‖∑ ρ ∈ S,
          (riemannZetaZeroMultiplicity ρ : ℂ) *
              ((x : ℂ) ^ (ρ + 1) - ((x * Real.exp (-η) : ℝ) : ℂ) ^ (ρ + 1)) /
            (ρ * (ρ + 1))‖ ≤
      x ^ (3 / 2 : ℝ) * (1 - Real.exp (-η)) *
        ((∑ ρ ∈ S,
            (riemannZetaZeroMultiplicity ρ : ℝ) * (Analysis.sincWeight (η / 2 * |ρ.im|) / |ρ.im|)) +
          3 / 2 * ordinateTail 100) := by
  apply
    (integrated_sinc_sum_le hRH S hz hr (fun ρ h ↦ lt_trans (by norm_num only) (hy ρ h)) hx
        hη).trans
  apply
    mul_le_mul_of_nonneg_left _
      (mul_nonneg (Real.rpow_nonneg hx.le _)
        (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hη.le))))
  simp only [mul_add, Finset.sum_add_distrib]
  apply add_le_add le_rfl
  apply
    le_trans _
      (mul_le_mul_of_nonneg_left (finite_ordinate_tail_le hRH S 100 hz hr hy)
        (by norm_num only : (0 : ℝ) ≤ 3 / 2))
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun ρ _ ↦ le_of_eq (by ring)

/-- A finite sinc sum above 100 is bounded by the reciprocal ledger up to
the scaled cutoff and the summable strict tail. The cutoff itself belongs to the ledger. -/
theorem finite_sinc_split_le (hRH : RiemannHypothesis) (S : Finset ℂ)
    (hz : ∀ ρ ∈ S, riemannZeta ρ = 0) (hr : ∀ ρ ∈ S, 0 ≤ ρ.re) (hy : ∀ ρ ∈ S, 100 < |ρ.im|)
    {β T : ℝ} (hb : 0 < β) (hT : 100 ≤ T) (hc : β * T = 2 / 5) :
    let f := fun ρ : ℂ ↦
      (riemannZetaZeroMultiplicity ρ : ℝ) * (Analysis.sincWeight (β * |ρ.im|) / |ρ.im|)
    let w := fun ρ : ℂ ↦ if riemannZeta ρ = 0 ∧ 0 ≤ ρ.re ∧ T < |ρ.im| then f ρ else 0
    ∑ ρ ∈ S, f ρ ≤ zeroReciprocalSum T - zeroReciprocalSum 100 + ∑' ρ, w ρ := by
  classical
  intro f w
  let p := fun ρ : ℂ ↦ |ρ.im| ≤ T
  let g := fun ρ : ℂ ↦ (riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im|
  have h0 : (0 : ℝ) ≤ 100 := by norm_num only
  have hs : S.filter p ⊆ zerosUpTo T \ zerosUpTo 100 := by
    intro ρ h
    obtain ⟨hm, hp⟩ := Finset.mem_filter.mp h
    exact
      Finset.mem_sdiff.mpr
        ⟨(mem_zerosUpTo (h0.trans hT)).mpr ⟨hz ρ hm, hr ρ hm, hp⟩, fun hh ↦
          (hy ρ hm).not_ge ((mem_zerosUpTo h0).mp hh).2.2⟩
  have ha : ∑ ρ ∈ S.filter p, f ρ ≤ zeroReciprocalSum T - zeroReciprocalSum 100 := by
    rw [zeroReciprocalSum_eq, zeroReciprocalSum_eq, ←
      Finset.sum_sdiff_eq_sub (zerosUpTo_mono h0 hT)]
    apply
      le_trans _
        (Finset.sum_le_sum_of_subset_of_nonneg (f := g) hs
          (fun ρ _ _ ↦ div_nonneg (Nat.cast_nonneg _) (abs_nonneg _)))
    apply Finset.sum_le_sum
    intro ρ hm
    have hp := (mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hm).2 hb.le).trans hc.le
    simp only [f, g, Analysis.sincWeight, ite_eq_left hp, mul_one_div]
    exact le_rfl
  have ht := (sincTail_summable hRH hb hc.ge).sum_le_tsum (S.filter (fun ρ ↦ ¬p ρ))
  have hn (ρ : ℂ) : 0 ≤ w ρ := by
    dsimp only [w]
    split
    next h =>
      have hp := mul_pos hb ((h0.trans hT).trans_lt h.2.2)
      exact
        mul_nonneg (Nat.cast_nonneg _)
          (div_nonneg
            ((div_nonneg (abs_nonneg _) hp.le).trans (Analysis.abs_sin_div_le_sincWeight hp))
            (abs_nonneg _))
    next => exact le_rfl
  rw [← Finset.sum_filter_add_sum_filter_not S p]
  apply add_le_add ha
  apply le_trans _ (ht (fun ρ _ ↦ hn ρ))
  apply Finset.sum_le_sum
  intro ρ hm
  obtain ⟨hm, hp⟩ := Finset.mem_filter.mp hm
  exact le_of_eq (ite_eq_left (And.intro (hz ρ hm) ⟨hr ρ hm, lt_of_not_ge hp⟩)).symm

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
