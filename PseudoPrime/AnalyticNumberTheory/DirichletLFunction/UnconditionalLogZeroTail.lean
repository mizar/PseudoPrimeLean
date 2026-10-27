/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.UnconditionalLocalZeroCount
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.UnconditionalLogExplicitFormula
public import PseudoPrime.Analysis.QuadraticDecaySeries

/-! # Unconditional high-zero tails for the logarithmic half-scale formula -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For a nonprincipal character, scale at least two, and ordinate of absolute value
at least one, the half-scale zero term is bounded by `4x` times divisor multiplicity
over the quadratic ordinate weight. Subtract the two full-scale terms and compare
norm square with ordinate square. This gives an unconditional high-zero majorant. -/
theorem norm_completedLogHalfZeroTerm_le_quadratic_unconditionally {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hne : χ ≠ 1) {x : ℝ} (hx : 2 ≤ x) {ρ : ℂ} (hρ : 1 ≤ |ρ.im|) :
    ‖completedLogHalfZeroTerm χ x ρ‖ ≤
      4 * x * (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) / (1 + ρ.im ^ 2) := by
  let D : ℝ := MeromorphicOn.divisor χ.completedLFunction Set.univ ρ
  have hAn : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := fun z _ ↦
    (χ.differentiable_completedLFunction hne).analyticAt z
  have hD : 0 ≤ D := by
    change (0 : ℝ) ≤ (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ)
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAn ρ
  have hi : 1 ≤ ρ.im ^ 2 := by nlinarith only [sq_abs ρ.im, hρ]
  have hden : 0 < 1 + ρ.im ^ 2 := by linarith only [hi]
  have hsq : 0 < Complex.normSq ρ := by
    rw [Complex.normSq_apply]
    nlinarith only [hi, sq_nonneg ρ.re]
  have hratio : D / Complex.normSq ρ ≤ 2 * D / (1 + ρ.im ^ 2) := by
    rw [div_le_div_iff₀ hsq hden]
    rw [Complex.normSq_apply]
    have h1 := mul_nonneg hD (by linarith only [hi] : 0 ≤ ρ.im ^ 2 - 1)
    have h2 := mul_nonneg hD (sq_nonneg ρ.re)
    nlinarith only [h1, h2]
  have hfirst := norm_completedLogZeroTerm_le_unconditionally hne (by linarith only [hx] : 1 ≤ x) ρ
  have hsecond :=
    norm_completedLogZeroTerm_le_unconditionally hne (by linarith only [hx] : 1 ≤ x / 2) ρ
  have hx0 : 0 ≤ x := by linarith only [hx]
  rw [completedLogHalfZeroTerm_eq_sub χ hx0]
  have hr := mul_le_mul_of_nonneg_left hratio hx0
  have hmass : 0 ≤ D / Complex.normSq ρ := div_nonneg hD hsq.le
  calc
    _ ≤ ‖completedLogZeroTerm χ x ρ‖ + ‖completedLogZeroTerm χ (x / 2) ρ‖ := norm_sub_le _ _
    _ ≤ x * (D / Complex.normSq ρ) + (x / 2) * (D / Complex.normSq ρ) := add_le_add hfirst hsecond
    _ ≤ _ := by
      change _ ≤ 4 * x * D / (1 + ρ.im ^ 2)
      have hp := mul_nonneg hx0 hmass
      simp only [div_eq_mul_inv] at hr hp ⊢
      nlinarith only [hr, hp]

/-- Given a local multiplicity bound, a finite set in one integer ordinate bin above
absolute height one has an explicit quadratic-weight bound. The scale is at least
two and the character is nonprincipal. Compare each zero term with its bin weight
and sum multiplicities; this is the finite-bin input to the high-zero tail. -/
theorem sum_norm_completedLogHalfZeroTerm_bin_unconditionally {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hne : χ ≠ 1) {K x : ℝ} (hx : 2 ≤ x)
    (hcount :
      ∀ (t : ℝ) (S : Finset ℂ),
        (∀ ρ ∈ S, |ρ.im - t| ≤ 1) →
          ∑ ρ ∈ S, (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) ≤
            K * (Real.log q + Real.log (4 + |t|) + 1))
    (k : ℤ) (S : Finset ℂ) (hS : ∀ ρ ∈ S, ⌊ρ.im⌋ = k) (hh : ∀ ρ ∈ S, 1 ≤ |ρ.im|) :
    ∑ ρ ∈ S, ‖completedLogHalfZeroTerm χ x ρ‖ ≤
      (12 * x * K / (1 + (k : ℝ) ^ 2)) * (Real.log q + Real.log (4 + |(k : ℝ)|) + 1) := by
  have hx0 : 0 ≤ x := by linarith only [hx]
  have hwindow (ρ : ℂ) (hρ : ρ ∈ S) : |ρ.im - (k : ℝ)| ≤ 1 := by
    rw [← hS ρ hρ]
    exact Analysis.abs_sub_int_floor_le_one ρ.im
  have hc := hcount (k : ℝ) S hwindow
  have hden : 0 < 1 + (k : ℝ) ^ 2 := by nlinarith only [sq_nonneg (k : ℝ)]
  have hp (ρ : ℂ) (hρ : ρ ∈ S) :
    ‖completedLogHalfZeroTerm χ x ρ‖ ≤
      (12 * x / (1 + (k : ℝ) ^ 2)) *
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) := by
    have hdρ : 0 < 1 + ρ.im ^ 2 := by nlinarith only [sq_nonneg ρ.im]
    have hcmp := Analysis.quadraticDenominator_le_of_dist_le_one (hwindow ρ hρ)
    have hratio : 4 / (1 + ρ.im ^ 2) ≤ 12 / (1 + (k : ℝ) ^ 2) := by
      rw [div_le_div_iff₀ hdρ hden]
      nlinarith only [hcmp]
    have hAn : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := fun z _ ↦
      (χ.differentiable_completedLFunction hne).analyticAt z
    have hD : 0 ≤ (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) := by
      exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAn ρ
    have hf := mul_le_mul_of_nonneg_right hratio (mul_nonneg hx0 hD)
    calc
      _ ≤ 4 * x * (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) / (1 + ρ.im ^ 2) :=
        norm_completedLogHalfZeroTerm_le_quadratic_unconditionally hne hx (hh ρ hρ)
      _ ≤ _ := by convert hf using 1 <;> ring
  calc
    _ ≤
        ∑ ρ ∈ S,
          (12 * x / (1 + (k : ℝ) ^ 2)) *
            (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) :=
      Finset.sum_le_sum hp
    _ =
        (12 * x / (1 + (k : ℝ) ^ 2)) *
          ∑ ρ ∈ S, (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) :=
      by rw [Finset.mul_sum]
    _ ≤ (12 * x / (1 + (k : ℝ) ^ 2)) * (K * (Real.log q + Real.log (4 + |(k : ℝ)|) + 1)) :=
      mul_le_mul_of_nonneg_left hc (div_nonneg (by linarith only [hx0]) hden.le)
    _ = _ := by ring

/-- For a nonprincipal character of modulus at least two and scale at least two,
a positive local multiplicity constant gives an explicit high-zero finite-sum bound.
Partition by integer ordinate bins and sum the inverse-quadratic and logarithmic
tails. Multiplicities and both signs of the ordinate are retained. -/
theorem sum_norm_completedLogHalfZeroTerm_tail_unconditionally {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hne : χ ≠ 1) {K x : ℝ} (hK : 0 < K) (hx : 2 ≤ x)
    (hcount :
      ∀ (t : ℝ) (S : Finset ℂ),
        (∀ ρ ∈ S, |ρ.im - t| ≤ 1) →
          ∑ ρ ∈ S, (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) ≤
            K * (Real.log q + Real.log (4 + |t|) + 1))
    (H : ℕ) (hH : 2 ≤ H) (S : Finset ℂ) (hheight : ∀ ρ ∈ S, (H + 1 : ℕ) ≤ |ρ.im|) :
    ∑ ρ ∈ S, ‖completedLogHalfZeroTerm χ x ρ‖ ≤
      24 * x * K * Real.log q / ((H - 1 : ℕ) : ℝ) +
        192 * x * K * (Real.log ((H + 3 : ℕ) : ℝ) + 2) / (H + 3) := by
  let J := S.image (fun ρ : ℂ ↦ (⌊ρ.im⌋ : ℤ))
  have hJ : ∀ k ∈ J, H ≤ k.natAbs := by
    intro k hk
    obtain ⟨ρ, hρ, he⟩ := Finset.mem_image.mp hk
    rw [← he]
    have hdist : |ρ.im - (⌊ρ.im⌋ : ℝ)| ≤ 1 := by
      exact
        abs_le.mpr
          ⟨by linarith only [Int.floor_le ρ.im], by linarith only [Int.lt_floor_add_one ρ.im]⟩
    have htriangle : |ρ.im| ≤ 1 + |(⌊ρ.im⌋ : ℝ)| := by
      calc
        |ρ.im| = |(ρ.im - (⌊ρ.im⌋ : ℝ)) + (⌊ρ.im⌋ : ℝ)| :=
          congrArg abs (sub_add_cancel ρ.im (⌊ρ.im⌋ : ℝ)).symm
        _ ≤ |ρ.im - (⌊ρ.im⌋ : ℝ)| + |(⌊ρ.im⌋ : ℝ)| := by
          simpa only [Real.norm_eq_abs] using norm_add_le (ρ.im - (⌊ρ.im⌋ : ℝ)) (⌊ρ.im⌋ : ℝ)
        _ ≤ _ := add_le_add_left hdist _
    have hheight' := hheight ρ hρ
    have hreal : (H : ℝ) ≤ |(⌊ρ.im⌋ : ℝ)| := by
      have hhr : (H : ℝ) + 1 ≤ |ρ.im| := by exact_mod_cast hheight'
      linarith only [hhr, htriangle]
    have hInt : (H : ℤ) ≤ |⌊ρ.im⌋| := by exact_mod_cast hreal
    have hCastInt : (H : ℤ) ≤ ((⌊ρ.im⌋ : ℤ).natAbs : ℤ) := by
      simpa only [Int.natCast_natAbs] using hInt
    exact_mod_cast hCastInt
  have hfiber :=
    Finset.sum_fiberwise_of_maps_to (s := S) (t := J) (fun ρ hρ ↦ Finset.mem_image_of_mem _ hρ)
      (fun ρ : ℂ ↦ ‖completedLogHalfZeroTerm χ x ρ‖)
  have hlocal :
    ∀ k ∈ J,
      (∑ ρ ∈ S.filter (fun ρ ↦ (⌊ρ.im⌋ : ℤ) = k), ‖completedLogHalfZeroTerm χ x ρ‖) ≤
        (12 * x * K / (1 + (k : ℝ) ^ 2)) * (Real.log q + (Real.log (4 + |(k : ℝ)|) + 1)) := by
    intro k hk
    rw [← add_assoc]
    apply
      sum_norm_completedLogHalfZeroTerm_bin_unconditionally hne hx hcount k
        (S.filter (fun ρ ↦ (⌊ρ.im⌋ : ℤ) = k))
    · intro ρ hρ
      exact (Finset.mem_filter.mp hρ).2
    · intro ρ hρ
      have hh := hheight ρ (Finset.mem_filter.mp hρ).1
      have hhr : (H : ℝ) + 1 ≤ |ρ.im| := by exact_mod_cast hh
      have hHreal : (2 : ℝ) ≤ H := by exact_mod_cast hH
      linarith only [hhr, hHreal]
  have hsumBin :
    (∑ k ∈ J, ∑ ρ ∈ S.filter (fun ρ ↦ (⌊ρ.im⌋ : ℤ) = k), ‖completedLogHalfZeroTerm χ x ρ‖) ≤
      ∑ k ∈ J,
        (12 * x * K / (1 + (k : ℝ) ^ 2)) * (Real.log q + (Real.log (4 + |(k : ℝ)|) + 1)) := by
    apply Finset.sum_le_sum
    intro k hk
    exact hlocal k hk
  have hsplit :
    (∑ k ∈ J, (12 * x * K / (1 + (k : ℝ) ^ 2)) * (Real.log q + (Real.log (4 + |(k : ℝ)|) + 1))) =
      12 * x * K * Real.log q * (∑ k ∈ J, 1 / (1 + (k : ℝ) ^ 2)) +
        12 * x * K * (∑ k ∈ J, (Real.log (4 + |(k : ℝ)|) + 1) / (1 + (k : ℝ) ^ 2)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hInv := Analysis.sum_inverse_quadratic_le_of_forall_ge H hH J hJ
  have hLog := Analysis.sum_logWeighted_quadratic_le_of_forall_ge H hH J hJ
  have hlogq : 0 ≤ Real.log q :=
    Real.log_nonneg
      (by
        have hqreal : (2 : ℝ) ≤ q := by exact_mod_cast hq
        linarith only [hqreal])
  have h1 :=
    mul_le_mul_of_nonneg_left hInv
      (mul_nonneg (mul_nonneg (by linarith only [hx] : 0 ≤ 12 * x) hK.le) hlogq)
  have h2 := mul_le_mul_of_nonneg_left hLog (mul_nonneg (by linarith only [hx] : 0 ≤ 12 * x) hK.le)
  rw [← hfiber]
  calc
    (∑ k ∈ J, ∑ ρ ∈ S.filter (fun ρ ↦ (⌊ρ.im⌋ : ℤ) = k), ‖completedLogHalfZeroTerm χ x ρ‖) ≤
        ∑ k ∈ J, (12 * x * K / (1 + (k : ℝ) ^ 2)) * (Real.log q + (Real.log (4 + |(k : ℝ)|) + 1)) :=
      hsumBin
    _ =
        12 * x * K * Real.log q * (∑ k ∈ J, 1 / (1 + (k : ℝ) ^ 2)) +
          12 * x * K * (∑ k ∈ J, (Real.log (4 + |(k : ℝ)|) + 1) / (1 + (k : ℝ) ^ 2)) :=
      hsplit
    _ ≤
        12 * x * K * Real.log q * (2 / ((H - 1 : ℕ) : ℝ)) +
          12 * x * K * (16 * (Real.log ((H + 3 : ℕ) : ℝ) + 2) / (H + 3)) :=
      add_le_add h1 h2
    _ =
        24 * x * K * Real.log q / ((H - 1 : ℕ) : ℝ) +
          192 * x * K * (Real.log ((H + 3 : ℕ) : ℝ) + 2) / (H + 3) :=
      by ring

/-- There is one positive absolute constant controlling the full absolute half-scale
zero tail for every primitive nonprincipal character and its nonprincipal inverse.
For moduli and scales at least two, the bound decays as logarithmic height over
height. Apply the unconditional local count to finite filtered sums and pass to
the nonnegative tsum. This discharges the local counting input without RH. -/
theorem exists_tsum_norm_completedLogHalfZeroTerm_tail_bound_unconditionally :
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
                    ∀ (H : ℕ),
                      2 ≤ H →
                        (∑' ρ : ℂ,
                            if (H + 1 : ℕ) ≤ |ρ.im| then ‖completedLogHalfZeroTerm χ x ρ‖ else 0) ≤
                          24 * x * K * Real.log q / ((H - 1 : ℕ) : ℝ) +
                            192 * x * K * (Real.log ((H + 3 : ℕ) : ℝ) + 2) / (H + 3) := by
  obtain ⟨K, hK, hcount⟩ := exists_uniform_local_zeroMultiplicity_bound_unconditionally
  refine ⟨K, hK, ?_⟩
  intro q _ hq χ hp hne hinv x hx H hH
  apply Real.tsum_le_of_sum_le (fun ρ ↦ ite_nonneg (norm_nonneg _) le_rfl)
  intro S
  have hs :=
    sum_norm_completedLogHalfZeroTerm_tail_unconditionally hq hne hK hx (hcount q hq χ hp hne hinv)
      H hH (S.filter (fun ρ ↦ (H + 1 : ℕ) ≤ |ρ.im|)) (fun ρ hρ ↦ (Finset.mem_filter.mp hρ).2)
  simpa only [Finset.sum_filter] using hs

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
