/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.SelectedZeroBudget

/-! # Exact finite zero partitions with selected unit copies -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- A finite complex sum splits exactly at two ordered height cutoffs.
No triangle inequality is used, so the head retains its signed contribution. -/
theorem finite_height_sum_split (S : Finset ℂ) {A T : ℝ} (hAT : A ≤ T) (f : ℂ → ℂ) :
    (∑ ρ ∈ S, f ρ) =
      (∑ ρ ∈ S.filter (fun ρ ↦ |ρ.im| ≤ A), f ρ) +
        (∑ ρ ∈ S.filter (fun ρ ↦ A < |ρ.im| ∧ |ρ.im| ≤ T), f ρ) +
        (∑ ρ ∈ S.filter (fun ρ ↦ ¬|ρ.im| ≤ T), f ρ) := by
  classical
  let H := S.filter (fun ρ ↦ |ρ.im| ≤ A)
  let R := S.filter (fun ρ ↦ ¬|ρ.im| ≤ A)
  let M := S.filter (fun ρ ↦ A < |ρ.im| ∧ |ρ.im| ≤ T)
  let U := S.filter (fun ρ ↦ ¬|ρ.im| ≤ T)
  have heM : R.filter (fun ρ ↦ |ρ.im| ≤ T) = M := by
    ext ρ
    simp only [R, M, Finset.mem_filter, not_le]
    constructor
    · rintro ⟨⟨hs, ha⟩, ht⟩
      exact ⟨hs, ha, ht⟩
    · rintro ⟨hs, ha, ht⟩
      exact ⟨⟨hs, ha⟩, ht⟩
  have heU : R.filter (fun ρ ↦ ¬|ρ.im| ≤ T) = U := by
    ext ρ
    simp only [R, U, Finset.mem_filter, not_le]
    constructor
    · rintro ⟨⟨hs, ha⟩, ht⟩
      exact ⟨hs, ht⟩
    · rintro ⟨hs, ht⟩
      exact ⟨⟨hs, lt_of_le_of_lt hAT ht⟩, ht⟩
  have hs1 := Finset.sum_filter_add_sum_filter_not S (fun ρ : ℂ ↦ |ρ.im| ≤ A) f
  have hs2 := Finset.sum_filter_add_sum_filter_not R (fun ρ : ℂ ↦ |ρ.im| ≤ T) f
  rw [heM, heU] at hs2
  have hs : (∑ ρ ∈ S, f ρ) = (∑ ρ ∈ H, f ρ) + (∑ ρ ∈ M, f ρ) + (∑ ρ ∈ U, f ρ) := by
    change (∑ ρ ∈ H, f ρ) + (∑ ρ ∈ R, f ρ) = _ at hs1
    rw [← hs2] at hs1
    rw [← hs1]
    ring
  exact hs

/-- Separate one copy of each selected middle-band zero from the exact finite
sum, retaining the low head, residual middle weights and high tail separately. -/
theorem selected_height_sum_split (S Q : Finset ℂ) {A T : ℝ} (hAT : A ≤ T)
    (hQ : Q ⊆ S.filter (fun ρ ↦ A < |ρ.im| ∧ |ρ.im| ≤ T)) (f : ℂ → ℂ) :
    (∑ ρ ∈ S, (riemannZetaZeroMultiplicity ρ : ℂ) * f ρ) =
      (∑ ρ ∈ S.filter (fun ρ ↦ |ρ.im| ≤ A), (riemannZetaZeroMultiplicity ρ : ℂ) * f ρ) +
        ((∑ ρ ∈ Q, f ρ) +
          ∑ ρ ∈ S.filter (fun ρ ↦ A < |ρ.im| ∧ |ρ.im| ≤ T),
            ((((riemannZetaZeroMultiplicity ρ : ℝ) - (if ρ ∈ Q then 1 else 0) : ℝ) : ℂ) * f ρ)) +
        (∑ ρ ∈ S.filter (fun ρ ↦ ¬|ρ.im| ≤ T), (riemannZetaZeroMultiplicity ρ : ℂ) * f ρ) := by
  classical rw [finite_height_sum_split S hAT, selected_copy_sum _ Q hQ f]

/-- Subtract the signed low head and selected copies before taking a norm.
The exact finite partition leaves only the residual middle and high tail, so
separate bounds on those two pieces add without losing the head's sign. -/
theorem selected_remainder_norm_le (S Q : Finset ℂ) {A T : ℝ} (hAT : A ≤ T)
    (hQ : Q ⊆ S.filter (fun ρ ↦ A < |ρ.im| ∧ |ρ.im| ≤ T)) (f : ℂ → ℂ) {B C : ℝ}
    (hm :
      ‖∑ ρ ∈ S.filter (fun ρ ↦ A < |ρ.im| ∧ |ρ.im| ≤ T),
            ((((riemannZetaZeroMultiplicity ρ : ℝ) - (if ρ ∈ Q then 1 else 0) : ℝ) : ℂ) * f ρ)‖ ≤
        B)
    (hu : ‖∑ ρ ∈ S.filter (fun ρ ↦ ¬|ρ.im| ≤ T), (riemannZetaZeroMultiplicity ρ : ℂ) * f ρ‖ ≤ C) :
    ‖(∑ ρ ∈ S, (riemannZetaZeroMultiplicity ρ : ℂ) * f ρ) -
          (∑ ρ ∈ S.filter (fun ρ ↦ |ρ.im| ≤ A), (riemannZetaZeroMultiplicity ρ : ℂ) * f ρ) -
          (∑ ρ ∈ Q, f ρ)‖ ≤
      B + C := by
  classical
  rw [selected_height_sum_split S Q hAT hQ f]
  have he (h q m u : ℂ) : h + (q + m) + u - h - q = m + u := by ring
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add hm hu)

/-- Real signed cancellation with an explicit scalar remainder costs at most
one beyond the two complex residual budgets. This is the finite inequality
used before passing the integrated explicit formula to its limit. -/
theorem selected_remainder_real_le {z head middle tail : ℂ} {r B C : ℝ}
    (hz : z = head + middle + tail) (hm : ‖middle‖ ≤ B) (ht : ‖tail‖ ≤ C) (hr : |r| ≤ 1) :
    |(-z).re + head.re + r| ≤ B + C + 1 := by
  have he : (-z).re + head.re + r = -(middle + tail).re + r := by
    rw [hz, Complex.neg_re, Complex.add_re, Complex.add_re, Complex.add_re]
    ring
  rw [he]
  have hb :=
    (Complex.abs_re_le_norm (middle + tail)).trans
      ((norm_add_le middle tail).trans (add_le_add hm ht))
  have htri := abs_add_le (-(middle + tail).re) r
  rw [abs_neg] at htri
  exact htri.trans (add_le_add hb hr)

/-- Under RH, the head-cancelled finite integrated kernel is controlled by
the residual reciprocal budget and the actual ordinate tail. The selected set
must lie in the finite middle band; no tail certificate is an extra assumption. -/
theorem selected_finite_kernel_le (hRH : RiemannHypothesis) (S Q : Finset ℂ)
    (hz : ∀ ρ ∈ S, riemannZeta ρ = 0) (hre : ∀ ρ ∈ S, 0 ≤ ρ.re) (hρ : ∀ ρ ∈ S, ρ ≠ 1) {A T a b : ℝ}
    (hA : 0 ≤ A) (hAT : A ≤ T) (ha : 0 < a) (hab : a < b)
    (hQ : Q ⊆ S.filter (fun ρ ↦ A < |ρ.im| ∧ |ρ.im| ≤ T)) :
    let f : ℂ → ℂ := fun ρ ↦ ((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) / (ρ * (ρ + 1))
    ‖(∑ ρ ∈ S, (riemannZetaZeroMultiplicity ρ : ℂ) * f ρ) -
          (∑ ρ ∈ S.filter (fun ρ ↦ |ρ.im| ≤ A), (riemannZetaZeroMultiplicity ρ : ℂ) * f ρ) -
          (∑ ρ ∈ Q, f ρ)‖ ≤
      (b - a) * (Real.sqrt b * (zeroReciprocalSum T - zeroReciprocalSum A - ∑ ρ ∈ Q, 1 / |ρ.im|)) +
        (b ^ (3 / 2 : ℝ) + a ^ (3 / 2 : ℝ)) * ordinateTail T := by
  classical
  let M := S.filter (fun ρ ↦ A < |ρ.im| ∧ |ρ.im| ≤ T)
  let U := S.filter (fun ρ ↦ ¬|ρ.im| ≤ T)
  have hmS : ∀ ρ ∈ M, ρ ∈ S := fun ρ h ↦ (Finset.mem_filter.mp h).1
  have huS : ∀ ρ ∈ U, ρ ∈ S := fun ρ h ↦ (Finset.mem_filter.mp h).1
  have hM : M ⊆ (zerosUpTo T).filter (fun ρ ↦ A < |ρ.im|) := by
    intro ρ hmem
    have h := Finset.mem_filter.mp hmem
    exact
      Finset.mem_filter.mpr ⟨(mem_zerosUpTo (hA.trans hAT)).mpr ⟨hz ρ h.1, hre ρ h.1, h.2.2⟩, h.2.1⟩
  have hqS : ∀ ρ ∈ Q, ρ ∈ S := fun ρ h ↦ hmS ρ (hQ h)
  have hm :=
    selected_band_kernel_le hRH hA hAT ha hab M Q hM (fun ρ h ↦ hM (hQ h))
      (fun ρ h ↦ hρ ρ (hmS ρ h)) (fun ρ h ↦ hρ ρ (hqS ρ h))
  have hu :=
    selected_high_kernel_le hRH U (fun ρ h ↦ hz ρ (huS ρ h)) (fun ρ h ↦ hre ρ (huS ρ h)) ha hab
      (fun ρ h ↦ lt_of_not_ge (Finset.mem_filter.mp h).2)
  have hm' := (div_le_iff₀ (sub_pos.mpr hab)).mp hm
  have hu' := (div_le_iff₀ (sub_pos.mpr hab)).mp hu
  have he :
    ((b ^ (3 / 2 : ℝ) + a ^ (3 / 2 : ℝ)) / (b - a) * ordinateTail T) * (b - a) =
      (b ^ (3 / 2 : ℝ) + a ^ (3 / 2 : ℝ)) * ordinateTail T := by
    rw [mul_right_comm, div_mul_cancel₀ _ (sub_pos.mpr hab).ne']
  rw [he] at hu'
  have h :=
    selected_remainder_norm_le S Q hAT hQ
      (fun ρ ↦ ((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) / (ρ * (ρ + 1))) hm' hu'
  simpa only [mul_comm] using h

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
