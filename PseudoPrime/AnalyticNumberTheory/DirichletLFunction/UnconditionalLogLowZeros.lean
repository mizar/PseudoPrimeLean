/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.UnconditionalLogKernelBounds

/-! # Unconditional finite low-height regularized zero sums -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- A positive local multiplicity bound implies an explicit bounded-height count
for every finite set of completed zeros. Partition the ordinates into the integer
bins from `-H` to `H`, bound each bin, and count the bins. This reusable comparison
retains divisor multiplicity and does not require RH or a boundary gap. -/
theorem sum_completed_divisor_le_bounded_height_unconditionally {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} {K : ℝ} (hK : 0 < K)
    (hcount :
      ∀ (t : ℝ) (S : Finset ℂ),
        (∀ ρ ∈ S, |ρ.im - t| ≤ 1) →
          ∑ ρ ∈ S, (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) ≤
            K * (Real.log q + Real.log (4 + |t|) + 1))
    (H : ℕ) (S : Finset ℂ) (hh : ∀ ρ ∈ S, |ρ.im| ≤ H) :
    ∑ ρ ∈ S, (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) ≤
      (2 * (H : ℝ) + 1) * K * (Real.log q + Real.log (4 + (H : ℝ)) + 1) := by
  let J := Finset.Icc (-(H : ℤ)) H
  have hmaps (ρ : ℂ) (hρ : ρ ∈ S) : ⌊ρ.im⌋ ∈ J := by
    apply Finset.mem_Icc.mpr
    constructor
    · apply Int.le_floor.mpr
      exact_mod_cast (abs_le.mp (hh ρ hρ)).1
    · have h := Int.floor_mono (abs_le.mp (hh ρ hρ)).2
      simpa only [Int.floor_natCast] using h
  have hcard : J.card = 2 * H + 1 := by
    change (Finset.Icc (-(H : ℤ)) H).card = 2 * H + 1
    rw [Int.card_Icc]
    have he : (H : ℤ) + 1 - (-(H : ℤ)) = ((2 * H + 1 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [he, Int.toNat_natCast]
  have hlocal (k : ℤ) (hk : k ∈ J) :
    ∑ ρ ∈ S.filter (fun ρ ↦ ⌊ρ.im⌋ = k),
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) ≤
      K * (Real.log q + Real.log (4 + (H : ℝ)) + 1) := by
    have hwindow (ρ : ℂ) (hρ : ρ ∈ S.filter (fun ρ ↦ ⌊ρ.im⌋ = k)) : |ρ.im - (k : ℝ)| ≤ 1 := by
      rw [← (Finset.mem_filter.mp hρ).2]
      exact Analysis.abs_sub_int_floor_le_one ρ.im
    have hlocal := hcount (k : ℝ) (S.filter (fun ρ ↦ ⌊ρ.im⌋ = k)) hwindow
    have hklo : -(H : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hk).1
    have hkhi : (k : ℝ) ≤ H := by exact_mod_cast (Finset.mem_Icc.mp hk).2
    have habs : |(k : ℝ)| ≤ H := abs_le.mpr ⟨hklo, hkhi⟩
    have hlog :=
      Real.log_le_log (by linarith only [abs_nonneg (k : ℝ)] : 0 < 4 + |(k : ℝ)|)
        (add_le_add le_rfl habs)
    exact hlocal.trans (mul_le_mul_of_nonneg_left (by linarith only [hlog]) hK.le)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  calc
    _ ≤ ∑ _k ∈ J, K * (Real.log q + Real.log (4 + (H : ℝ)) + 1) := Finset.sum_le_sum hlocal
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, hcard, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
        Nat.cast_one]
      ring

/-- One positive absolute constant bounds every finite regularized zero sum with
real parts at most one half and ordinate bounded by a natural height. The character
is primitive nonprincipal with nonprincipal inverse and the scale is at least two.
Multiply the uniform bounded-height count by the origin-free kernel estimate.
This discharges the local counting input for the low left-strip error. -/
theorem exists_sum_norm_regularizedLogHalfZeroTerm_leftStrip_lowHeight_bound :
    ∃ K : ℝ,
      0 < K ∧
        ∀ (q : ℕ) [NeZero q],
          2 ≤ q →
            ∀ (χ : DirichletCharacter ℂ q),
              χ.IsPrimitive →
                χ ≠ 1 →
                χ⁻¹ ≠ 1 →
                ∀ (x : ℝ),
                  2 ≤ x →
                    ∀ (H : ℕ) (S : Finset ℂ),
                      (∀ ρ ∈ S, ρ.re ≤ 1 / 2) →
                        (∀ ρ ∈ S, |ρ.im| ≤ H) →
                        ∑ ρ ∈ S, ‖regularizedLogHalfZeroTerm χ x ρ‖ ≤
                          ((2 * (H : ℝ) + 1) * K * (Real.log q + Real.log (4 + (H : ℝ)) + 1)) *
                            (2 * Real.sqrt x * (Real.log x) ^ 2 +
                              Real.log 2 * (Real.log x + 1)) := by
  obtain ⟨K, hK, hcount⟩ := exists_uniform_local_zeroMultiplicity_bound_unconditionally
  refine ⟨K, hK, ?_⟩
  intro q _ hq χ hp hne hinv x hx H S hre hh
  have hc :=
    sum_completed_divisor_le_bounded_height_unconditionally hK (hcount q hq χ hp hne hinv) H S hh
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by linarith only [hx])
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num only)
  have hB : 0 ≤ 2 * Real.sqrt x * (Real.log x) ^ 2 + Real.log 2 * (Real.log x + 1) :=
    add_nonneg (mul_nonneg (mul_nonneg (by norm_num only) (Real.sqrt_nonneg x)) (sq_nonneg _))
      (mul_nonneg hlog2 (by linarith only [hlogx]))
  calc
    _ ≤
        ∑ ρ ∈ S,
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
            (2 * Real.sqrt x * (Real.log x) ^ 2 + Real.log 2 * (Real.log x + 1)) :=
      Finset.sum_le_sum
        (fun ρ hρ ↦ norm_regularizedLogHalfZeroTerm_le_low_re hp hne hinv hx (hre ρ hρ))
    _ =
        (∑ ρ ∈ S, (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ)) *
          (2 * Real.sqrt x * (Real.log x) ^ 2 + Real.log 2 * (Real.log x + 1)) :=
      by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hc hB

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
