/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountConjugation

/-! # Conjugate-invariant finite sums over zeta zeros -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH, a real-valued conjugate-invariant weight on the finite zero
ledger has total sum twice its positive-height sum. The conjugation bijection
preserves the cutoff and the zero-free interval excludes real zeros. -/
theorem zero_sum_eq_two_positive (hRH : RiemannHypothesis) {T : ℝ} (hT : 0 ≤ T) (f : ℂ → ℝ)
    (hf : ∀ ρ ∈ zerosUpTo T, f ((starRingEnd ℂ) ρ) = f ρ) :
    (∑ ρ ∈ zerosUpTo T, f ρ) = 2 * ∑ ρ ∈ (zerosUpTo T).filter (fun ρ ↦ 0 < ρ.im), f ρ := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not (zerosUpTo T) (fun ρ : ℂ ↦ 0 < ρ.im) f
  rw [← hsplit]
  have heq :
    (∑ ρ ∈ (zerosUpTo T).filter (fun ρ ↦ ¬0 < ρ.im), f ρ) =
      ∑ ρ ∈ (zerosUpTo T).filter (fun ρ ↦ 0 < ρ.im), f ρ := by
    apply Finset.sum_bij (fun ρ _ ↦ (starRingEnd ℂ) ρ)
    · intro ρ hρ
      have hh := Finset.mem_filter.mp hρ
      have hz := (mem_zerosUpTo hT).1 hh.1
      have hgap := zero_height_gt_two_pi hRH hz.1 hz.2.1
      have hneg : ρ.im < 0 := by
        have hp : 0 < 2 * Real.pi := mul_pos (by norm_num only) Real.pi_pos
        have hnon : ρ.im ≠ 0 := by
          intro he
          rw [he, abs_zero] at hgap
          linarith only [hgap, hp]
        exact lt_of_le_of_ne (le_of_not_gt hh.2) hnon
      apply Finset.mem_filter.mpr
      constructor
      · apply (mem_zerosUpTo hT).2
        refine ⟨?_, ?_, ?_⟩
        · rw [riemannZeta_conj, hz.1, map_zero]
        · simpa only [Complex.conj_re] using hz.2.1
        · simpa only [Complex.conj_im, abs_neg] using hz.2.2
      · simpa only [Complex.conj_im] using neg_pos.mpr hneg
    · intro ρ hρ σ hσ h
      have hh := congrArg (starRingEnd ℂ) h
      simpa only [starRingEnd_self_apply] using hh
    · intro σ hσ
      refine ⟨(starRingEnd ℂ) σ, ?_, ?_⟩
      · have hh := Finset.mem_filter.mp hσ
        have hz := (mem_zerosUpTo hT).1 hh.1
        apply Finset.mem_filter.mpr
        constructor
        · apply (mem_zerosUpTo hT).2
          refine ⟨?_, ?_, ?_⟩
          · rw [riemannZeta_conj, hz.1, map_zero]
          · simpa only [Complex.conj_re] using hz.2.1
          · simpa only [Complex.conj_im, abs_neg] using hz.2.2
        · simp only [Complex.conj_im, not_lt]
          linarith only [hh.2]
      · exact starRingEnd_self_apply σ
    · intro ρ hρ
      exact (hf ρ (Finset.mem_filter.mp hρ).1).symm
  rw [heq]
  ring

/-- Under RH, the multiplicity-weighted reciprocal height sum equals twice
the corresponding positive-height sum. Conjugation preserves multiplicity
and absolute height, and positive heights have no absolute-value sign. -/
theorem zeroReciprocal_eq_two_positive (hRH : RiemannHypothesis) {T : ℝ} (hT : 0 ≤ T) :
    zeroReciprocalSum T =
      2 *
        ∑ ρ ∈ (zerosUpTo T).filter (fun ρ ↦ 0 < ρ.im),
          (riemannZetaZeroMultiplicity ρ : ℝ) / ρ.im := by
  rw [zeroReciprocalSum_eq]
  have h :=
    zero_sum_eq_two_positive hRH hT (fun ρ ↦ (riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im|)
      (by
        intro ρ hρ
        have hz := (mem_zerosUpTo hT).1 hρ
        have hr :=
          RiemannXi.xi_zero_re_eq_half_of_riemannHypothesis hRH
            (RiemannXi.xi_zero_of_zeta_zero_of_re_nonneg hz.1 hz.2.1)
        have hne : ρ ≠ 1 := by
          intro he
          rw [he, Complex.one_re] at hr
          norm_num only at hr
        rw [multiplicity_conj hne]
        simp only [Complex.conj_im, abs_neg])
  rw [h]
  congr 1
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [abs_of_pos (Finset.mem_filter.mp hρ).2]

/-- An enumeration whose entries are positive-height zeros and which contains
every such zero through `T` is exactly the positive part of the zero ledger.
This transfers a completeness theorem to finite sum identities. -/
theorem positive_ledger_eq_image {T : ℝ} {n : ℕ} (z : Fin n → ℂ)
    (hz : ∀ i, z i ∈ zerosUpTo T ∧ 0 < (z i).im) (hc : ∀ ρ ∈ zerosUpTo T, 0 < ρ.im → ∃ i, ρ = z i) :
    (zerosUpTo T).filter (fun ρ ↦ 0 < ρ.im) = Finset.univ.image z := by
  classical
  ext ρ
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro h
    obtain ⟨i, hi⟩ := hc ρ h.1 h.2
    exact ⟨i, hi.symm⟩
  · rintro ⟨i, rfl⟩
    exact hz i

/-- Under RH, an injective enumeration of all positive-height zeros through
`T`, each of multiplicity one, gives the two-sided zero count `2 * n`.
The hypothesis describes a ledger rather than exposing a numerical table. -/
theorem zeroCount_of_simple_enumeration (hRH : RiemannHypothesis) {T : ℝ} (hT : 0 ≤ T) {n : ℕ}
    (z : Fin n → ℂ) (hinj : Function.Injective z)
    (hledger : (zerosUpTo T).filter (fun ρ ↦ 0 < ρ.im) = Finset.univ.image z)
    (hm : ∀ i, riemannZetaZeroMultiplicity (z i) = 1) : zeroCount T = 2 * n := by
  rw [zeroCount_eq_sum]
  have h :=
    zero_sum_eq_two_positive hRH hT (fun ρ ↦ (riemannZetaZeroMultiplicity ρ : ℝ))
      (by
        intro ρ hρ
        have hz := (mem_zerosUpTo hT).1 hρ
        have hr :=
          RiemannXi.xi_zero_re_eq_half_of_riemannHypothesis hRH
            (RiemannXi.xi_zero_of_zeta_zero_of_re_nonneg hz.1 hz.2.1)
        have hne : ρ ≠ 1 := by
          intro he
          rw [he, Complex.one_re] at hr
          norm_num only at hr
        rw [multiplicity_conj hne])
  rw [h, hledger, Finset.sum_image]
  · simp only [hm, Nat.cast_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one]
  · intro a ha b hb hab
    exact hinj hab

/-- Under RH, an injective enumeration of all positive-height zeros through
`T`, each of multiplicity one, converts the two-sided reciprocal zero sum
into twice the sum of the inverse enumerated ordinates. -/
theorem zeroReciprocal_of_simple_enumeration (hRH : RiemannHypothesis) {T : ℝ} (hT : 0 ≤ T) {n : ℕ}
    (z : Fin n → ℂ) (g : Fin n → ℝ) (hinj : Function.Injective z)
    (hledger : (zerosUpTo T).filter (fun ρ ↦ 0 < ρ.im) = Finset.univ.image z)
    (hm : ∀ i, riemannZetaZeroMultiplicity (z i) = 1) (him : ∀ i, (z i).im = g i) :
    zeroReciprocalSum T = ∑ i, (2 : ℝ) / g i := by
  rw [zeroReciprocal_eq_two_positive hRH hT]
  rw [hledger, Finset.sum_image]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hm i, him i]
    norm_num only [Nat.cast_one]
    ring
  · intro a ha b hb hab
    exact hinj hab

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
