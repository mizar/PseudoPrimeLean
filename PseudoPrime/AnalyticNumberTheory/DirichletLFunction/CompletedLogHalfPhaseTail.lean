/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.CompletedLogHalfZeros
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.CompletedShiftedZeros
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LocalZeroCount
public import PseudoPrime.Analysis.QuadraticDecaySeries

/-!
# Height-bin bounds for the completed half-phase zero sum

The local zero count and the pointwise quadratic kernel estimate give a uniform bound
for every finite set of zeros in one integer height bin.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- A finite set of zeros in one integer height bin contributes at most the local
multiplicity bound times an inverse quadratic weight. The hypotheses are individual GRH,
primitivity, and nonprincipality of the character and its inverse. The floor condition
places the set in the radius-one window used by the uniform local zero-count theorem.
This is the finite-bin input for quantitative tails of the actual completed zero series. -/
theorem sum_norm_completedLogHalfPhaseTerm_le_bin_bound :
    ∃ A : ℝ,
      0 < A ∧
        ∀ (q : ℕ) [NeZero q],
          2 ≤ q →
            ∀ (χ : DirichletCharacter ℂ q),
              GRH.DirichletRiemannHypothesis χ →
                χ.IsPrimitive →
                χ ≠ 1 →
                χ⁻¹ ≠ 1 →
                ∀ (v : ℝ) (k : ℤ) (S : Finset ℂ),
                  (∀ ρ ∈ S, ⌊ρ.im⌋ = k) →
                    ∑ ρ ∈ S, ‖completedLogHalfPhaseTerm χ v ρ‖ ≤
                      (24 / (1 + (k : ℝ) ^ 2)) *
                        (Real.log q + 2 * A * (Real.log (4 + |(k : ℝ)|) + 1)) := by
  obtain ⟨A, hA, hcount⟩ := exists_uniform_local_zeroMultiplicity_bound
  refine ⟨A, hA, ?_⟩
  intro q hqInst hq χ hRH hp hne hinv v k S hS
  have hwindow : ∀ ρ ∈ S, |ρ.im - (k : ℝ)| ≤ 1 := by
    intro ρ hρ
    rw [← hS ρ hρ]
    exact Analysis.abs_sub_int_floor_le_one ρ.im
  have hlocal := hcount (q := q) hq χ hRH hp hne hinv (k : ℝ) S hwindow
  have hDsum :
    ∑ ρ ∈ S, (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) ≤
      Real.log q + 2 * A * (Real.log (4 + |(k : ℝ)|) + 1) :=
    hlocal
  have hden : 0 ≤ 24 / (1 + (k : ℝ) ^ 2) := by
    exact div_nonneg (by norm_num only) (by nlinarith only [sq_nonneg (k : ℝ)])
  calc
    ∑ ρ ∈ S, ‖completedLogHalfPhaseTerm χ v ρ‖ ≤
        ∑ ρ ∈ S,
          (24 / (1 + (k : ℝ) ^ 2)) * (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) :=
      by
      apply Finset.sum_le_sum
      intro ρ hρ
      have hdist : |ρ.im - (k : ℝ)| ≤ 1 := hwindow ρ hρ
      have hdenCmp := Analysis.quadraticDenominator_le_of_dist_le_one hdist
      have hratio : 8 / (1 + ρ.im ^ 2) ≤ 24 / (1 + (k : ℝ) ^ 2) := by
        have hleft : 0 < 1 + ρ.im ^ 2 := by nlinarith only [sq_nonneg ρ.im]
        have hright : 0 < 1 + (k : ℝ) ^ 2 := by nlinarith only [sq_nonneg (k : ℝ)]
        rw [div_le_div_iff₀ hleft hright]
        nlinarith only [hdenCmp]
      have ha : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := fun z _ ↦
        (DirichletCharacter.differentiable_completedLFunction hne).analyticAt z
      have hD : 0 ≤ (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) := by
        exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg ha ρ
      have hterm := norm_completedLogHalfPhaseTerm_le_eight_quadratic_weight hRH hp hne hinv v ρ
      have hfactor :
        (8 / (1 + ρ.im ^ 2)) * (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) ≤
          (24 / (1 + (k : ℝ) ^ 2)) * (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) :=
        mul_le_mul_of_nonneg_right hratio hD
      calc
        ‖completedLogHalfPhaseTerm χ v ρ‖ ≤
            8 * (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) / (1 + ρ.im ^ 2) :=
          hterm
        _ = (8 / (1 + ρ.im ^ 2)) * (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) := by
          ring
        _ ≤ _ := hfactor
    _ =
        (24 / (1 + (k : ℝ) ^ 2)) *
          ∑ ρ ∈ S, (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) :=
      by rw [Finset.mul_sum]
    _ ≤ (24 / (1 + (k : ℝ) ^ 2)) * (Real.log q + 2 * A * (Real.log (4 + |(k : ℝ)|) + 1)) :=
      mul_le_mul_of_nonneg_left hDsum hden

/-- A finite set of zeros with ordinates of absolute value below three meets at most six
integer floor bins. The local zero-count estimate gives a uniform bound for the complete
low-height portion, including the central zero. -/
theorem exists_sum_norm_completedLogHalfPhaseTerm_belowThree_bound :
    ∃ A : ℝ,
      0 < A ∧
        ∀ (q : ℕ) [NeZero q],
          2 ≤ q →
            ∀ (χ : DirichletCharacter ℂ q),
              GRH.DirichletRiemannHypothesis χ →
                χ.IsPrimitive →
                χ ≠ 1 →
                χ⁻¹ ≠ 1 →
                ∀ (v : ℝ) (S : Finset ℂ),
                  (∀ ρ ∈ S, |ρ.im| < 3) →
                    ∑ ρ ∈ S, ‖completedLogHalfPhaseTerm χ v ρ‖ ≤
                      144 * (Real.log q + 2 * A * (Real.log 7 + 1)) := by
  obtain ⟨A, hA, hbin⟩ := sum_norm_completedLogHalfPhaseTerm_le_bin_bound
  refine ⟨A, hA, ?_⟩
  intro q hqInst hq χ hRH hp hne hinv v S hS
  let J := S.image (fun ρ : ℂ ↦ (⌊ρ.im⌋ : ℤ))
  have hJ : ∀ k ∈ J, k ∈ Finset.Icc (-3 : ℤ) 2 := by
    intro k hk
    obtain ⟨ρ, hρ, he⟩ := Finset.mem_image.mp hk
    rw [← he]
    have hbounds := abs_lt.mp (hS ρ hρ)
    have hfloorNext : ρ.im < (⌊ρ.im⌋ : ℝ) + 1 := Int.lt_floor_add_one ρ.im
    have hfloorLoReal : (-4 : ℝ) < (⌊ρ.im⌋ : ℝ) := by linarith only [hbounds.1, hfloorNext]
    have hfloorLo : (-4 : ℤ) < ⌊ρ.im⌋ := by exact_mod_cast hfloorLoReal
    have hfloorHiReal : (⌊ρ.im⌋ : ℝ) < 3 := by exact lt_of_le_of_lt (Int.floor_le ρ.im) hbounds.2
    have hfloorHi : (⌊ρ.im⌋ : ℤ) < 3 := by exact_mod_cast hfloorHiReal
    have hlow : (-3 : ℤ) ≤ ⌊ρ.im⌋ := by omega
    have hupp' : ⌊ρ.im⌋ ≤ 2 := by omega
    exact Finset.mem_Icc.mpr ⟨hlow, hupp'⟩
  have hfiber :=
    Finset.sum_fiberwise_of_maps_to (s := S) (t := J) (fun ρ hρ ↦ Finset.mem_image_of_mem _ hρ)
      (fun ρ : ℂ ↦ ‖completedLogHalfPhaseTerm χ v ρ‖)
  have hlocal :
    ∀ k ∈ J,
      (∑ ρ ∈ S.filter (fun ρ ↦ (⌊ρ.im⌋ : ℤ) = k), ‖completedLogHalfPhaseTerm χ v ρ‖) ≤
        24 * (Real.log q + 2 * A * (Real.log 7 + 1)) := by
    intro k hk
    have hbin' :=
      hbin q hq χ hRH hp hne hinv v k (S.filter (fun ρ ↦ (⌊ρ.im⌋ : ℤ) = k))
        (fun ρ hρ ↦ (Finset.mem_filter.mp hρ).2)
    have hkI := Finset.mem_Icc.mp (hJ k hk)
    have hrealBounds : -3 ≤ (k : ℝ) ∧ (k : ℝ) ≤ 3 := by
      constructor
      · exact_mod_cast hkI.1
      · have hkr : (k : ℝ) ≤ 2 := by exact_mod_cast hkI.2
        linarith only [hkr]
    have habs : |(k : ℝ)| ≤ 3 := abs_le.mpr hrealBounds
    have hlogArg : 1 ≤ 4 + |(k : ℝ)| := by
      have := abs_nonneg (k : ℝ)
      linarith only [this]
    have hlog : Real.log (4 + |(k : ℝ)|) ≤ Real.log 7 := by
      apply Real.log_le_log (by positivity)
      linarith only [habs]
    have hqreal : 2 ≤ (q : ℝ) := by exact_mod_cast hq
    have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by linarith only [hqreal])
    have hlogfactor : 0 ≤ Real.log (4 + |(k : ℝ)|) + 1 :=
      add_nonneg (Real.log_nonneg hlogArg) (by norm_num only)
    have hD : 0 ≤ Real.log q + 2 * A * (Real.log (4 + |(k : ℝ)|) + 1) :=
      add_nonneg hlogq (mul_nonneg (by positivity) hlogfactor)
    have hbracket :
      Real.log q + 2 * A * (Real.log (4 + |(k : ℝ)|) + 1) ≤
        Real.log q + 2 * A * (Real.log 7 + 1) := by
      have hA2 : 0 ≤ 2 * A := by positivity
      nlinarith only [hlog, hA2]
    have hden : 1 ≤ 1 + (k : ℝ) ^ 2 := by nlinarith only [sq_nonneg (k : ℝ)]
    have hcoeff : 24 / (1 + (k : ℝ) ^ 2) ≤ 24 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith only [hden]
    calc
      (∑ ρ ∈ S.filter (fun ρ ↦ (⌊ρ.im⌋ : ℤ) = k), ‖completedLogHalfPhaseTerm χ v ρ‖) ≤
          (24 / (1 + (k : ℝ) ^ 2)) * (Real.log q + 2 * A * (Real.log (4 + |(k : ℝ)|) + 1)) :=
        hbin'
      _ ≤ 24 * (Real.log q + 2 * A * (Real.log 7 + 1)) := by
        exact mul_le_mul hcoeff hbracket hD (by positivity)
  have hsum :
    (∑ k ∈ J, ∑ ρ ∈ S.filter (fun ρ ↦ (⌊ρ.im⌋ : ℤ) = k), ‖completedLogHalfPhaseTerm χ v ρ‖) ≤
      (J.card : ℝ) * (24 * (Real.log q + 2 * A * (Real.log 7 + 1))) := by
    calc
      _ ≤ ∑ k ∈ J, 24 * (Real.log q + 2 * A * (Real.log 7 + 1)) := by
        apply Finset.sum_le_sum
        intro k hk
        exact hlocal k hk
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  have hcard : J.card ≤ 6 := by
    calc
      J.card ≤ (Finset.Icc (-3 : ℤ) 2).card := Finset.card_le_card hJ
      _ = 6 := by decide
  have hCnonneg : 0 ≤ 24 * (Real.log q + 2 * A * (Real.log 7 + 1)) := by positivity
  rw [← hfiber]
  calc
    (∑ k ∈ J, ∑ ρ ∈ S.filter (fun ρ ↦ (⌊ρ.im⌋ : ℤ) = k), ‖completedLogHalfPhaseTerm χ v ρ‖) ≤
        (J.card : ℝ) * (24 * (Real.log q + 2 * A * (Real.log 7 + 1))) :=
      hsum
    _ ≤ 6 * (24 * (Real.log q + 2 * A * (Real.log 7 + 1))) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hCnonneg
    _ = _ := by ring

/-- A finite set with ordinates between absolute heights two and three is covered by
the uniform estimate for all heights below three. -/
theorem exists_sum_norm_completedLogHalfPhaseTerm_lowBand_bound :
    ∃ A : ℝ,
      0 < A ∧
        ∀ (q : ℕ) [NeZero q],
          2 ≤ q →
            ∀ (χ : DirichletCharacter ℂ q),
              GRH.DirichletRiemannHypothesis χ →
                χ.IsPrimitive →
                χ ≠ 1 →
                χ⁻¹ ≠ 1 →
                ∀ (v : ℝ) (S : Finset ℂ),
                  (∀ ρ ∈ S, 2 ≤ |ρ.im| ∧ |ρ.im| < 3) →
                    ∑ ρ ∈ S, ‖completedLogHalfPhaseTerm χ v ρ‖ ≤
                      144 * (Real.log q + 2 * A * (Real.log 7 + 1)) := by
  obtain ⟨A, hA, hbelow⟩ := exists_sum_norm_completedLogHalfPhaseTerm_belowThree_bound
  refine ⟨A, hA, ?_⟩
  intro q hqInst hq χ hRH hp hne hinv v S hS
  exact hbelow q hq χ hRH hp hne hinv v S (fun ρ hρ ↦ (hS ρ hρ).2)

/-- A finite set of completed-L zeros above an integer height cutoff has an explicit
conductor and logarithmic-height bound. Partition the set by the floor of each ordinate,
apply the local bin estimate, and sum the inverse-quadratic and logarithmic tails. The
cutoff is H+1 so every occupied bin has absolute index at least H. -/
theorem exists_sum_norm_completedLogHalfPhaseTerm_tail_bound :
    ∃ A : ℝ,
      0 < A ∧
        ∀ (q : ℕ) [NeZero q],
          2 ≤ q →
            ∀ (χ : DirichletCharacter ℂ q),
              GRH.DirichletRiemannHypothesis χ →
                χ.IsPrimitive →
                χ ≠ 1 →
                χ⁻¹ ≠ 1 →
                ∀ (H : ℕ),
                  2 ≤ H →
                    ∀ (v : ℝ) (S : Finset ℂ),
                      (∀ ρ ∈ S, (H + 1 : ℕ) ≤ |ρ.im|) →
                        ∑ ρ ∈ S, ‖completedLogHalfPhaseTerm χ v ρ‖ ≤
                          48 * Real.log q / ((H - 1 : ℕ) : ℝ) +
                            768 * A * (Real.log ((H + 3 : ℕ) : ℝ) + 2) / (H + 3) := by
  obtain ⟨A, hA, hbin⟩ := sum_norm_completedLogHalfPhaseTerm_le_bin_bound
  refine ⟨A, hA, ?_⟩
  intro q hqInst hq χ hRH hp hne hinv H hH v S hheight
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
      (fun ρ : ℂ ↦ ‖completedLogHalfPhaseTerm χ v ρ‖)
  have hlocal :
    ∀ k ∈ J,
      (∑ ρ ∈ S.filter (fun ρ ↦ (⌊ρ.im⌋ : ℤ) = k), ‖completedLogHalfPhaseTerm χ v ρ‖) ≤
        (24 / (1 + (k : ℝ) ^ 2)) * (Real.log q + 2 * A * (Real.log (4 + |(k : ℝ)|) + 1)) := by
    intro k hk
    apply hbin q hq χ hRH hp hne hinv v k (S.filter (fun ρ ↦ (⌊ρ.im⌋ : ℤ) = k))
    intro ρ hρ
    exact (Finset.mem_filter.mp hρ).2
  have hsumBin :
    (∑ k ∈ J, ∑ ρ ∈ S.filter (fun ρ ↦ (⌊ρ.im⌋ : ℤ) = k), ‖completedLogHalfPhaseTerm χ v ρ‖) ≤
      ∑ k ∈ J,
        (24 / (1 + (k : ℝ) ^ 2)) * (Real.log q + 2 * A * (Real.log (4 + |(k : ℝ)|) + 1)) := by
    apply Finset.sum_le_sum
    intro k hk
    exact hlocal k hk
  have hsplit :
    (∑ k ∈ J, (24 / (1 + (k : ℝ) ^ 2)) * (Real.log q + 2 * A * (Real.log (4 + |(k : ℝ)|) + 1))) =
      24 * Real.log q * (∑ k ∈ J, 1 / (1 + (k : ℝ) ^ 2)) +
        48 * A * (∑ k ∈ J, (Real.log (4 + |(k : ℝ)|) + 1) / (1 + (k : ℝ) ^ 2)) := by
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
  have h1 := mul_le_mul_of_nonneg_left hInv (by positivity : 0 ≤ 24 * Real.log q)
  have h2 := mul_le_mul_of_nonneg_left hLog (by positivity : 0 ≤ 48 * A)
  rw [← hfiber]
  calc
    (∑ k ∈ J, ∑ ρ ∈ S.filter (fun ρ ↦ (⌊ρ.im⌋ : ℤ) = k), ‖completedLogHalfPhaseTerm χ v ρ‖) ≤
        ∑ k ∈ J, (24 / (1 + (k : ℝ) ^ 2)) * (Real.log q + 2 * A * (Real.log (4 + |(k : ℝ)|) + 1)) :=
      hsumBin
    _ =
        24 * Real.log q * (∑ k ∈ J, 1 / (1 + (k : ℝ) ^ 2)) +
          48 * A * (∑ k ∈ J, (Real.log (4 + |(k : ℝ)|) + 1) / (1 + (k : ℝ) ^ 2)) :=
      hsplit
    _ ≤
        24 * Real.log q * (2 / ((H - 1 : ℕ) : ℝ)) +
          48 * A * (16 * (Real.log ((H + 3 : ℕ) : ℝ) + 2) / (H + 3)) :=
      add_le_add h1 h2
    _ =
        48 * Real.log q / ((H - 1 : ℕ) : ℝ) +
          768 * A * (Real.log ((H + 3 : ℕ) : ℝ) + 2) / (H + 3) :=
      by ring

/-- The full absolute completed-L zero tail above H+1 obeys the finite-set bound with
the same uniform constant. Apply the nonnegative tsum criterion to finite filtered sets.
This is a quantitative tail estimate for the actual completed zero series. -/
theorem exists_tsum_norm_completedLogHalfPhaseTerm_tail_bound :
    ∃ A : ℝ,
      0 < A ∧
        ∀ (q : ℕ) [NeZero q],
          2 ≤ q →
            ∀ (χ : DirichletCharacter ℂ q),
              GRH.DirichletRiemannHypothesis χ →
                χ.IsPrimitive →
                χ ≠ 1 →
                χ⁻¹ ≠ 1 →
                ∀ (H : ℕ),
                  2 ≤ H →
                    ∀ (v : ℝ),
                      (∑' ρ : ℂ,
                          if (H + 1 : ℕ) ≤ |ρ.im| then ‖completedLogHalfPhaseTerm χ v ρ‖ else 0) ≤
                        48 * Real.log q / ((H - 1 : ℕ) : ℝ) +
                          768 * A * (Real.log ((H + 3 : ℕ) : ℝ) + 2) / (H + 3) := by
  obtain ⟨A, hA, hfinite⟩ := exists_sum_norm_completedLogHalfPhaseTerm_tail_bound
  refine ⟨A, hA, ?_⟩
  intro q hqInst hq χ hRH hp hne hinv H hH v
  apply Real.tsum_le_of_sum_le (fun ρ ↦ ite_nonneg (norm_nonneg _) le_rfl)
  intro S
  have hs :=
    hfinite q hq χ hRH hp hne hinv H hH v (S.filter (fun ρ ↦ (H + 1 : ℕ) ≤ |ρ.im|))
      (fun ρ hρ ↦ (Finset.mem_filter.mp hρ).2)
  simpa only [Finset.sum_filter] using hs

/-- Under an individual Dirichlet GRH hypothesis, the completed half-phase terms are
absolutely summable. Split finite sums at height three, use the bounded low-height bins
and the integer tail estimate, then apply the finite-sum criterion for summability. -/
theorem exists_summable_norm_completedLogHalfPhaseTerm :
    ∃ K : ℝ,
      0 < K ∧
        ∀ (q : ℕ) [NeZero q],
          2 ≤ q →
            ∀ (χ : DirichletCharacter ℂ q),
              GRH.DirichletRiemannHypothesis χ →
                χ.IsPrimitive →
                χ ≠ 1 →
                χ⁻¹ ≠ 1 → ∀ v : ℝ, Summable (fun ρ : ℂ ↦ ‖completedLogHalfPhaseTerm χ v ρ‖) := by
  obtain ⟨Alo, hAlo, hlow⟩ := exists_sum_norm_completedLogHalfPhaseTerm_belowThree_bound
  obtain ⟨Ahi, hAhi, hhigh⟩ := exists_sum_norm_completedLogHalfPhaseTerm_tail_bound
  let K := 192 + 288 * Alo * (Real.log 7 + 1) + 768 * Ahi * (Real.log 5 + 2) / 5
  have hK : 0 < K := by
    dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro q hqInst hq χ hRH hp hne hinv v
  have hqreal : 2 ≤ (q : ℝ) := by exact_mod_cast hq
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by linarith only [hqreal])
  have hfinite :
    ∀ S : Finset ℂ, (∑ ρ ∈ S, ‖completedLogHalfPhaseTerm χ v ρ‖) ≤ K * (Real.log q + 1) := by
    intro S
    have hsplit :=
      Finset.sum_filter_add_sum_filter_not S (fun ρ : ℂ ↦ (3 : ℝ) ≤ |ρ.im|)
        (fun ρ : ℂ ↦ ‖completedLogHalfPhaseTerm χ v ρ‖)
    have hlo :=
      hlow q hq χ hRH hp hne hinv v (S.filter (fun ρ : ℂ ↦ ¬((3 : ℝ) ≤ |ρ.im|)))
        (fun ρ hr ↦ by
          have hm := Finset.mem_filter.mp hr
          exact not_le.mp hm.2)
    have hhi :=
      hhigh q hq χ hRH hp hne hinv 2 (by norm_num only) v (S.filter (fun ρ : ℂ ↦ (3 : ℝ) ≤ |ρ.im|))
        (fun ρ hr ↦ by
          have hm := Finset.mem_filter.mp hr
          exact_mod_cast hm.2)
    have hlog7 : 0 ≤ Real.log 7 := Real.log_nonneg (by norm_num only)
    have hlow' :
      (∑ ρ ∈ S.filter (fun ρ : ℂ ↦ ¬((3 : ℝ) ≤ |ρ.im|)), ‖completedLogHalfPhaseTerm χ v ρ‖) ≤
        (144 + 288 * Alo * (Real.log 7 + 1)) * (Real.log q + 1) := by
      have h := hlo
      nlinarith only [h, hlogq, hlog7, show 0 ≤ Alo * (Real.log 7 + 1) by positivity]
    have hlog5 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num only)
    have hhigh' :
      (∑ ρ ∈ S.filter (fun ρ : ℂ ↦ (3 : ℝ) ≤ |ρ.im|), ‖completedLogHalfPhaseTerm χ v ρ‖) ≤
        (48 + 768 * Ahi * (Real.log 5 + 2) / 5) * (Real.log q + 1) := by
      have h := hhi
      norm_num only [Nat.cast_ofNat] at h
      nlinarith only [h, hlogq, hlog5, show 0 ≤ Ahi * (Real.log 5 + 2) by positivity]
    have hsum :
      (∑ ρ ∈ S.filter (fun ρ : ℂ ↦ (3 : ℝ) ≤ |ρ.im|), ‖completedLogHalfPhaseTerm χ v ρ‖) +
          (∑ ρ ∈ S.filter (fun ρ : ℂ ↦ ¬((3 : ℝ) ≤ |ρ.im|)), ‖completedLogHalfPhaseTerm χ v ρ‖) ≤
        K * (Real.log q + 1) := by
      dsimp only [K]
      nlinarith only [hlow', hhigh', hlogq]
    rw [← hsplit]
    exact hsum
  exact summable_of_sum_le (fun ρ : ℂ ↦ norm_nonneg _) hfinite

/-- Under individual GRH, bound the total absolute mass of the completed half-phase
series by a uniform constant times `log q + 1`. Combine the finite low-height
estimate with the quantitative tail at height three. This records the scale
available from absolute values alone; it does not estimate cancellation in the
signed phase. -/
theorem exists_tsum_norm_completedLogHalfPhaseTerm_log_bound :
    ∃ K : ℝ,
      0 < K ∧
        ∀ (q : ℕ) [NeZero q],
          2 ≤ q →
            ∀ (χ : DirichletCharacter ℂ q),
              GRH.DirichletRiemannHypothesis χ →
                χ.IsPrimitive →
                χ ≠ 1 →
                χ⁻¹ ≠ 1 →
                ∀ v : ℝ, (∑' ρ : ℂ, ‖completedLogHalfPhaseTerm χ v ρ‖) ≤ K * (Real.log q + 1) := by
  obtain ⟨Alo, hAlo, hlow⟩ := exists_sum_norm_completedLogHalfPhaseTerm_belowThree_bound
  obtain ⟨Ahi, hAhi, hhigh⟩ := exists_sum_norm_completedLogHalfPhaseTerm_tail_bound
  let K := 192 + 288 * Alo * (Real.log 7 + 1) + 768 * Ahi * (Real.log 5 + 2) / 5
  have hK : 0 < K := by
    dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro q hqInst hq χ hRH hp hne hinv v
  have hqreal : 2 ≤ (q : ℝ) := by exact_mod_cast hq
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by linarith only [hqreal])
  have hfinite :
    ∀ S : Finset ℂ, (∑ ρ ∈ S, ‖completedLogHalfPhaseTerm χ v ρ‖) ≤ K * (Real.log q + 1) := by
    intro S
    have hsplit :=
      Finset.sum_filter_add_sum_filter_not S (fun ρ : ℂ ↦ (3 : ℝ) ≤ |ρ.im|)
        (fun ρ : ℂ ↦ ‖completedLogHalfPhaseTerm χ v ρ‖)
    have hlo :=
      hlow q hq χ hRH hp hne hinv v (S.filter (fun ρ : ℂ ↦ ¬((3 : ℝ) ≤ |ρ.im|)))
        (fun ρ hr ↦ not_le.mp (Finset.mem_filter.mp hr).2)
    have hhi :=
      hhigh q hq χ hRH hp hne hinv 2 (by norm_num only) v (S.filter (fun ρ : ℂ ↦ (3 : ℝ) ≤ |ρ.im|))
        (fun ρ hr ↦ by exact_mod_cast (Finset.mem_filter.mp hr).2)
    have hlog7 : 0 ≤ Real.log 7 := Real.log_nonneg (by norm_num only)
    have hlow' :
      (∑ ρ ∈ S.filter (fun ρ : ℂ ↦ ¬((3 : ℝ) ≤ |ρ.im|)), ‖completedLogHalfPhaseTerm χ v ρ‖) ≤
        (144 + 288 * Alo * (Real.log 7 + 1)) * (Real.log q + 1) := by
      have h := hlo
      nlinarith only [h, hlogq, hlog7, show 0 ≤ Alo * (Real.log 7 + 1) by positivity]
    have hlog5 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num only)
    have hhigh' :
      (∑ ρ ∈ S.filter (fun ρ : ℂ ↦ (3 : ℝ) ≤ |ρ.im|), ‖completedLogHalfPhaseTerm χ v ρ‖) ≤
        (48 + 768 * Ahi * (Real.log 5 + 2) / 5) * (Real.log q + 1) := by
      have h := hhi
      norm_num only [Nat.cast_ofNat] at h
      nlinarith only [h, hlogq, hlog5, show 0 ≤ Ahi * (Real.log 5 + 2) by positivity]
    have hsum :
      (∑ ρ ∈ S.filter (fun ρ : ℂ ↦ (3 : ℝ) ≤ |ρ.im|), ‖completedLogHalfPhaseTerm χ v ρ‖) +
          (∑ ρ ∈ S.filter (fun ρ : ℂ ↦ ¬((3 : ℝ) ≤ |ρ.im|)), ‖completedLogHalfPhaseTerm χ v ρ‖) ≤
        K * (Real.log q + 1) := by
      dsimp only [K]
      nlinarith only [hlow', hhigh', hlogq]
    rw [← hsplit]
    exact hsum
  exact Real.tsum_le_of_sum_le (fun ρ ↦ norm_nonneg _) hfinite

/-! A real cutoff converts the integer-tail estimate once the denominator losses are
bounded uniformly by the cutoff. -/

/-- Convert an integer-height tail estimate to a real cutoff in the range `T ≥ 4`.
The inverse-quadratic term loses at most a factor four, while the logarithmic term
loses at most a factor two. -/
theorem real_cutoff_tail_arithmetic_bound (A q : ℝ) (H : ℕ) (T : ℝ) (hA : 0 < A) (hq : 2 ≤ q)
    (hT : 4 ≤ T) (hlo : T - 2 < (H : ℝ)) (hhi : (H : ℝ) ≤ T - 1) :
    48 * Real.log q / ((H - 1 : ℕ) : ℝ) +
        768 * A * (Real.log ((H + 3 : ℕ) : ℝ) + 2) / ((H + 3 : ℕ) : ℝ) ≤
      (192 + 1536 * A) * (Real.log q + Real.log (T + 4) + 1) / T := by
  have hH : 2 ≤ H := by
    have hr : (2 : ℝ) ≤ H := by linarith only [hlo, hT]
    exact_mod_cast hr
  have hden : 0 < ((H - 1 : ℕ) : ℝ) := by
    have hn : 0 < H - 1 := by omega
    exact_mod_cast hn
  have hcast : ((H - 1 : ℕ) : ℝ) = (H : ℝ) - 1 := by
    exact_mod_cast (Nat.cast_sub (show 1 ≤ H by omega))
  have hTpos : 0 < T := by linarith only [hT]
  have hinv : 1 / ((H - 1 : ℕ) : ℝ) ≤ 4 / T := by
    rw [div_le_div_iff₀ hden hTpos]
    rw [hcast]
    nlinarith only [hT, hlo]
  have hc : ((H + 3 : ℕ) : ℝ) = (H : ℝ) + 3 := by exact Nat.cast_add H 3
  have hratio2 : 1 / ((H + 3 : ℕ) : ℝ) ≤ 1 / T := by
    have hden2 : 0 < ((H + 3 : ℕ) : ℝ) := by positivity
    rw [hc]
    apply one_div_le_one_div_of_le
    · linarith only [hT]
    · linarith only [hlo]
  have hlog : Real.log ((H + 3 : ℕ) : ℝ) ≤ Real.log (T + 4) := by
    rw [hc]
    apply Real.log_le_log (by positivity)
    linarith only [hhi]
  have hlognonneg : 0 ≤ Real.log (T + 4) := by
    apply Real.log_nonneg
    linarith only [hT]
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by linarith only [hq])
  have hfirst : 48 * Real.log q / ((H - 1 : ℕ) : ℝ) ≤ 192 * Real.log q / T := by
    calc
      48 * Real.log q / ((H - 1 : ℕ) : ℝ) = 48 * Real.log q * (1 / ((H - 1 : ℕ) : ℝ)) := by ring
      _ ≤ 48 * Real.log q * (4 / T) := by
        apply mul_le_mul_of_nonneg_left hinv
        positivity
      _ = 192 * Real.log q / T := by ring
  have hsecond :
    768 * A * (Real.log ((H + 3 : ℕ) : ℝ) + 2) / ((H + 3 : ℕ) : ℝ) ≤
      1536 * A * (Real.log (T + 4) + 1) / T := by
    have hnum : Real.log ((H + 3 : ℕ) : ℝ) + 2 ≤ 2 * (Real.log (T + 4) + 1) := by
      nlinarith only [hlog, hlognonneg]
    have hcoef : 0 ≤ 768 * A := by positivity
    calc
      768 * A * (Real.log ((H + 3 : ℕ) : ℝ) + 2) / ((H + 3 : ℕ) : ℝ) =
          768 * A * (Real.log ((H + 3 : ℕ) : ℝ) + 2) * (1 / ((H + 3 : ℕ) : ℝ)) :=
        by ring
      _ ≤ 768 * A * (2 * (Real.log (T + 4) + 1)) * (1 / T) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hnum hcoef
        · exact hratio2
        · positivity
        · positivity
      _ = 1536 * A * (Real.log (T + 4) + 1) / T := by ring
  have hsum := add_le_add hfirst hsecond
  have hfinalNum :
    192 * Real.log q + 1536 * A * (Real.log (T + 4) + 1) ≤
      (192 + 1536 * A) * (Real.log q + Real.log (T + 4) + 1) := by
    have hprod : 0 ≤ A * Real.log q := mul_nonneg (le_of_lt hA) hlogq
    nlinarith only [hprod, hlogq, hlognonneg]
  have hfinal := div_le_div_of_nonneg_right hfinalNum (le_of_lt hTpos)
  calc
    _ ≤ 192 * Real.log q / T + 1536 * A * (Real.log (T + 4) + 1) / T := hsum
    _ = (192 * Real.log q + 1536 * A * (Real.log (T + 4) + 1)) / T := by ring
    _ ≤ _ := hfinal

/-- The absolute completed zero tail above every real height `T ≥ 4` has a uniform
conductor and logarithmic-height bound. Take the integer bin immediately below `T`,
use the finite tail estimate on each finite filtered set, and then apply the cutoff
comparison. -/
theorem exists_tsum_norm_completedLogHalfPhaseTerm_real_tail_bound :
    ∃ A : ℝ,
      0 < A ∧
        ∀ (q : ℕ) [NeZero q],
          2 ≤ q →
            ∀ (χ : DirichletCharacter ℂ q),
              GRH.DirichletRiemannHypothesis χ →
                χ.IsPrimitive →
                χ ≠ 1 →
                χ⁻¹ ≠ 1 →
                ∀ (T : ℝ),
                  4 ≤ T →
                    ∀ (v : ℝ),
                      (∑' ρ : ℂ, if T ≤ |ρ.im| then ‖completedLogHalfPhaseTerm χ v ρ‖ else 0) ≤
                        (192 + 1536 * A) * (Real.log q + Real.log (T + 4) + 1) / T := by
  obtain ⟨A, hA, hfinite⟩ := exists_sum_norm_completedLogHalfPhaseTerm_tail_bound
  refine ⟨A, hA, ?_⟩
  intro q hqInst hq χ hRH hp hne hinv T hT v
  let floorT : ℤ := ⌊T⌋
  have hfloorLe : (floorT : ℝ) ≤ T := Int.floor_le T
  have hTfloor : T - 1 < (floorT : ℝ) := by
    have h := Int.lt_floor_add_one T
    linarith only [h]
  have hfloor3 : (3 : ℝ) < (floorT : ℝ) := by linarith only [hTfloor, hT]
  have hfloor3Int : (3 : ℤ) < floorT := by exact_mod_cast hfloor3
  have hfloorNonneg : 0 ≤ floorT := by omega
  let M : ℕ := floorT.natAbs
  have hMreal : (M : ℝ) = (floorT : ℝ) := by
    dsimp only [M]
    have heq : (floorT.natAbs : ℤ) = floorT := Int.natAbs_of_nonneg hfloorNonneg
    exact congrArg (fun z : ℤ => (z : ℝ)) heq
  let H : ℕ := M - 1
  have hH2 : 2 ≤ H := by
    dsimp only [H, M]; omega
  have hHplus : H + 1 = M := by
    dsimp only [H]; omega
  have hHreal : (H : ℝ) = (floorT : ℝ) - 1 := by
    dsimp only [H]
    have hsub : 1 ≤ M := by
      dsimp only [M]; omega
    rw [Nat.cast_sub hsub, hMreal]
    norm_num
  have hlo : T - 2 < (H : ℝ) := by
    rw [hHreal]; linarith only [hTfloor]
  have hhi : (H : ℝ) ≤ T - 1 := by
    rw [hHreal]; linarith only [hfloorLe]
  have hqreal : 2 ≤ (q : ℝ) := by exact_mod_cast hq
  have hrealTailBound :
    (∑' ρ : ℂ, if T ≤ |ρ.im| then ‖completedLogHalfPhaseTerm χ v ρ‖ else 0) ≤
      48 * Real.log q / ((H - 1 : ℕ) : ℝ) +
        768 * A * (Real.log ((H + 3 : ℕ) : ℝ) + 2) / ((H + 3 : ℕ) : ℝ) := by
    apply Real.tsum_le_of_sum_le (fun ρ => ite_nonneg (norm_nonneg _) le_rfl)
    intro S
    have hs :=
      hfinite q hq χ hRH hp hne hinv H hH2 v (S.filter (fun ρ => T ≤ |ρ.im|))
        (fun ρ hr => by
          have hTρ := (Finset.mem_filter.mp hr).2
          have hreal : ((H + 1 : ℕ) : ℝ) ≤ |ρ.im| := by
            rw [hHplus, hMreal]
            exact le_trans hfloorLe hTρ
          exact_mod_cast hreal)
    norm_num only [Finset.sum_filter, Nat.cast_add] at hs ⊢
    exact hs
  have hcutoff := real_cutoff_tail_arithmetic_bound A q H T hA (by exact_mod_cast hq) hT hlo hhi
  calc
    (∑' ρ : ℂ, if T ≤ |ρ.im| then ‖completedLogHalfPhaseTerm χ v ρ‖ else 0) ≤
        48 * Real.log q / ((H - 1 : ℕ) : ℝ) +
          768 * A * (Real.log ((H + 3 : ℕ) : ℝ) + 2) / ((H + 3 : ℕ) : ℝ) :=
      hrealTailBound
    _ ≤ (192 + 1536 * A) * (Real.log q + Real.log (T + 4) + 1) / T := hcutoff

/-- The central completed half-phase term has nonnegative real part for every nonprincipal
character. Its negative contribution to the signed phase is therefore nonpositive. Analyticity
gives nonnegative central multiplicity, and the norm of `2^(-1/2)` is at most one. -/
theorem nonneg_re_completedLogHalfPhaseTerm_at_center {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hne : χ ≠ 1) (v : ℝ) :
    0 ≤ (completedLogHalfPhaseTerm χ v ((1 / 2 : ℝ) : ℂ)).re := by
  let ρ : ℂ := ((1 / 2 : ℝ) : ℂ)
  let D := MeromorphicOn.divisor χ.completedLFunction Set.univ ρ
  have hD : 0 ≤ (D : ℝ) := by
    have ha : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := fun z _ =>
      (DirichletCharacter.differentiable_completedLFunction hne).analyticAt z
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg ha ρ
  have hpow : ‖(2 : ℂ) ^ (-ρ)‖ ≤ 1 := by
    change ‖Complex.ofReal (2 : ℝ) ^ (-ρ)‖ ≤ 1
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num only : (0 : ℝ) < 2)]
    have hre : (-ρ).re = -(1 / 2 : ℝ) := by
      dsimp only [ρ]
      rw [Complex.neg_re, Complex.ofReal_re]
    rw [hre]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num only) (by norm_num only)
  have hsub : 0 ≤ (1 - (2 : ℂ) ^ (-ρ)).re := by
    rw [Complex.sub_re, Complex.one_re]
    have h := Complex.abs_re_le_norm ((2 : ℂ) ^ (-ρ))
    rw [abs_le] at h
    linarith only [h.2, hpow]
  have him : ρ.im = 0 := by
    dsimp only [ρ]; rw [Complex.ofReal_im]
  have hden : ρ ^ 2 = ((1 / 4 : ℝ) : ℂ) := by
    dsimp only [ρ]
    rw [← Complex.ofReal_pow]
    congr 1
    norm_num only
  have hexp : Complex.exp ((ρ.im * v : ℝ) * Complex.I) = 1 := by
    rw [him]
    simp only [zero_mul, Complex.ofReal_zero, zero_mul, Complex.exp_zero]
  have hterm : (completedLogHalfPhaseTerm χ v ρ).re = 4 * (D : ℝ) * (1 - (2 : ℂ) ^ (-ρ)).re := by
    change
      (((D : ℂ) * (1 - (2 : ℂ) ^ (-ρ)) / ρ ^ 2) * Complex.exp ((ρ.im * v : ℝ) * Complex.I)).re = _
    rw [hexp, mul_one, hden, Complex.div_ofReal_re, Complex.mul_re, Complex.intCast_re,
      Complex.intCast_im]
    simp only [Complex.sub_re, Complex.one_re, zero_mul, sub_zero]
    ring
  rw [show ((1 / 2 : ℝ) : ℂ) = ρ by rfl, hterm]
  exact mul_nonneg (mul_nonneg (by norm_num only) hD) hsub

/-- At the central point, the half-phase contribution is exactly
$4(1-2^{-1/2})m_0$, where $m_0$ is the completed-function divisor at $1/2$.
The phase is one there, the denominator is $1/4$, and the positive real base power
reduces to the real power $2^{-1/2}$. -/
theorem re_completedLogHalfPhaseTerm_at_center_eq_multiplicity_formula {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (v : ℝ) :
    (completedLogHalfPhaseTerm χ v ((1 / 2 : ℝ) : ℂ)).re =
      4 * (MeromorphicOn.divisor χ.completedLFunction Set.univ ((1 / 2 : ℝ) : ℂ) : ℝ) *
        (1 - (2 : ℝ) ^ (-1 / 2 : ℝ)) := by
  let ρ : ℂ := ((1 / 2 : ℝ) : ℂ)
  let D := MeromorphicOn.divisor χ.completedLFunction Set.univ ρ
  have him : ρ.im = 0 := by
    dsimp only [ρ]
    rw [Complex.ofReal_im]
  have hden : ρ ^ 2 = ((1 / 4 : ℝ) : ℂ) := by
    dsimp only [ρ]
    rw [← Complex.ofReal_pow]
    congr 1
    norm_num only
  have hexp : Complex.exp ((ρ.im * v : ℝ) * Complex.I) = 1 := by
    rw [him]
    simp only [zero_mul, Complex.ofReal_zero, zero_mul, Complex.exp_zero]
  have hterm : (completedLogHalfPhaseTerm χ v ρ).re = 4 * (D : ℝ) * (1 - (2 : ℂ) ^ (-ρ)).re := by
    change
      (((D : ℂ) * (1 - (2 : ℂ) ^ (-ρ)) / ρ ^ 2) * Complex.exp ((ρ.im * v : ℝ) * Complex.I)).re = _
    rw [hexp, mul_one, hden, Complex.div_ofReal_re, Complex.mul_re, Complex.intCast_re,
      Complex.intCast_im]
    simp only [Complex.sub_re, Complex.one_re, zero_mul, sub_zero]
    ring
  have hpow : ((2 : ℂ) ^ (-ρ)).re = (2 : ℝ) ^ (-1 / 2 : ℝ) := by
    have hb : (2 : ℂ) = Complex.ofReal (2 : ℝ) := (Complex.ofReal_ofNat 2).symm
    rw [show -ρ = ((-1 / 2 : ℝ) : ℂ) by
        dsimp only [ρ]
        push_cast
        ring]
    rw [hb, Complex.cpow_ofReal]
    have hn : ‖Complex.ofReal (2 : ℝ)‖ = 2 := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by norm_num only : (0 : ℝ) ≤ 2)]
    have ha : (Complex.ofReal (2 : ℝ)).arg = 0 :=
      Complex.arg_ofReal_of_nonneg (by norm_num only : (0 : ℝ) ≤ 2)
    rw [hn, ha]
    have ht :
      Complex.ofReal (Real.cos (0 * (-1 / 2 : ℝ))) +
          Complex.ofReal (Real.sin (0 * (-1 / 2 : ℝ))) * Complex.I =
        1 := by
      simp only [zero_mul, Real.cos_zero, Real.sin_zero, Complex.ofReal_one, Complex.ofReal_zero,
        zero_mul, add_zero]
    rw [ht, mul_one, Complex.ofReal_re]
  rw [show ((1 / 2 : ℝ) : ℂ) = ρ by rfl, hterm]
  change 4 * (D : ℝ) * (1 - (2 : ℂ) ^ (-ρ)).re = 4 * (D : ℝ) * (1 - (2 : ℝ) ^ (-1 / 2 : ℝ))
  rw [Complex.sub_re, Complex.one_re, hpow]

/-- Under only the individual Dirichlet GRH, the signed phase is at most the real part
of the negative sum over the complement of the central point. Absolute summability follows
from the low-height and tail bounds, so no global GRH assumption is needed. -/
theorem logarithmicHalfPhase_le_complement_of_dirichletRH {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (v : ℝ) :
    logarithmicHalfPhase χ v ≤
      -(∑' ρ : ↑((({((1 / 2 : ℝ) : ℂ)} : Finset ℂ) : Set ℂ)ᶜ),
            completedLogHalfPhaseTerm χ v ρ).re := by
  obtain ⟨K, hK, hnorm⟩ := exists_summable_norm_completedLogHalfPhaseTerm
  have hs := (hnorm N hN χ hRH hp hne hinv v).of_norm
  have hsplit := hs.sum_add_tsum_compl (s := ({((1 / 2 : ℝ) : ℂ)} : Finset ℂ))
  rw [Finset.sum_singleton] at hsplit
  unfold logarithmicHalfPhase
  rw [← hsplit]
  simp only [Complex.add_re]
  have hc := nonneg_re_completedLogHalfPhaseTerm_at_center χ hne v
  linarith only [hc]

/-- Under individual Dirichlet GRH, split the absolutely convergent sum over the complement
of the central point at any real height. The two summands contain terms below and above
the cutoff, respectively. -/
theorem tsum_completedLogHalfPhaseTerm_complement_eq_low_add_high {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (v T : ℝ) :
    (∑' ρ : { ρ : ℂ // ρ ∈ (({((1 / 2 : ℝ) : ℂ)} : Finset ℂ) : Set ℂ)ᶜ },
        completedLogHalfPhaseTerm χ v ρ.val) =
      (∑' ρ : { ρ : ℂ // ρ ∈ (({((1 / 2 : ℝ) : ℂ)} : Finset ℂ) : Set ℂ)ᶜ },
          if |ρ.val.im| < T then completedLogHalfPhaseTerm χ v ρ.val else 0) +
        (∑' ρ : { ρ : ℂ // ρ ∈ (({((1 / 2 : ℝ) : ℂ)} : Finset ℂ) : Set ℂ)ᶜ },
          if T ≤ |ρ.val.im| then completedLogHalfPhaseTerm χ v ρ.val else 0) := by
  obtain ⟨_, _, hnorm⟩ := exists_summable_norm_completedLogHalfPhaseTerm
  have hfull := (hnorm N hN χ hRH hp hne hinv v).of_norm
  let S : Set ℂ := (({((1 / 2 : ℝ) : ℂ)} : Finset ℂ) : Set ℂ)ᶜ
  let α := { ρ : ℂ // ρ ∈ S }
  let g : α → ℂ := fun ρ ↦ completedLogHalfPhaseTerm χ v ρ.val
  let lo : α → ℂ := fun ρ ↦ if |ρ.val.im| < T then g ρ else 0
  let hi : α → ℂ := fun ρ ↦ if T ≤ |ρ.val.im| then g ρ else 0
  have hg : Summable g := hfull.subtype _
  have hgn : Summable (fun ρ : α ↦ ‖g ρ‖) := hg.norm
  have hloN : Summable (fun ρ : α ↦ ‖lo ρ‖) :=
    Summable.of_norm_bounded hgn
      (fun ρ ↦ by
        dsimp only [lo]
        by_cases hr : |ρ.val.im| < T
        · rw [ite_eq_left hr, norm_norm]
        · rw [ite_eq_right hr, norm_zero]
          simpa only [norm_zero] using norm_nonneg (g ρ))
  have hhiN : Summable (fun ρ : α ↦ ‖hi ρ‖) :=
    Summable.of_norm_bounded hgn
      (fun ρ ↦ by
        dsimp only [hi]
        by_cases hr : T ≤ |ρ.val.im|
        · rw [ite_eq_left hr, norm_norm]
        · rw [ite_eq_right hr, norm_zero]
          simpa only [norm_zero] using norm_nonneg (g ρ))
  have hlo : Summable lo := hloN.of_norm
  have hhi : Summable hi := hhiN.of_norm
  have hpoint : g = lo + hi := by
    funext ρ
    by_cases hr : |ρ.val.im| < T
    · change g ρ = (if |ρ.val.im| < T then g ρ else 0) + (if T ≤ |ρ.val.im| then g ρ else 0)
      rw [ite_eq_left hr, ite_eq_right (not_le.mpr hr), add_zero]
    · have hge : T ≤ |ρ.val.im| := le_of_not_gt hr
      change g ρ = (if |ρ.val.im| < T then g ρ else 0) + (if T ≤ |ρ.val.im| then g ρ else 0)
      rw [ite_eq_right hr, ite_eq_left hge, zero_add]
  calc
    (∑' ρ : α, g ρ) = ∑' ρ : α, (lo ρ + hi ρ) := tsum_congr (fun ρ ↦ congrFun hpoint ρ)
    _ = (∑' ρ : α, lo ρ) + ∑' ρ : α, hi ρ := hlo.tsum_add hhi

/-- A conductor-uniform quantitative absolute tail bound holds for every real height
$T \ge 2$. For $T \ge 4$ use the integer-bin tail estimate. For $2 \le T < 4$, split
the tail at height three and bound the remaining height bins by the local zero count.
The constant depends only on the uniform local zero-multiplicity constant. -/
theorem exists_tsum_norm_completedLogHalfPhaseTerm_all_real_tail_bound :
    ∃ C : ℝ,
      0 < C ∧
        ∀ (q : ℕ) [NeZero q],
          2 ≤ q →
            ∀ (χ : DirichletCharacter ℂ q),
              GRH.DirichletRiemannHypothesis χ →
                χ.IsPrimitive →
                χ ≠ 1 →
                χ⁻¹ ≠ 1 →
                ∀ (T : ℝ),
                  2 ≤ T →
                    ∀ (v : ℝ),
                      (∑' ρ : ℂ, if T ≤ |ρ.im| then ‖completedLogHalfPhaseTerm χ v ρ‖ else 0) ≤
                        C * (Real.log q + Real.log (T + 4) + 1) / T := by
  obtain ⟨Ar, hAr, hreal⟩ := exists_tsum_norm_completedLogHalfPhaseTerm_real_tail_bound
  obtain ⟨Ai, hAi, hfinite⟩ := exists_sum_norm_completedLogHalfPhaseTerm_tail_bound
  obtain ⟨Al, hAl, hlow⟩ := exists_sum_norm_completedLogHalfPhaseTerm_lowBand_bound
  let K := 192 + 768 * Ai * (Real.log 5 + 2) / 5 + 288 * Al * (Real.log 7 + 1)
  let C := (192 + 1536 * Ar) + 4 * K
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro q hqInst hq χ hRH hp hne hinv T hT v
  have hqreal : 2 ≤ (q : ℝ) := by exact_mod_cast hq
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by linarith only [hqreal])
  by_cases hlarge : 4 ≤ T
  · have hlargeTail := hreal q hq χ hRH hp hne hinv T hlarge v
    have hlogT : 0 ≤ Real.log (T + 4) := Real.log_nonneg (by linarith only [hT])
    have hden : 0 ≤ (Real.log q + Real.log (T + 4) + 1) / T :=
      div_nonneg (by linarith only [hlogq, hlogT]) (by linarith only [hT])
    have hcoeff : 192 + 1536 * Ar ≤ C := by
      rw [show C = (192 + 1536 * Ar) + 4 * K from rfl]
      nlinarith only [hK]
    calc
      (∑' ρ : ℂ, if T ≤ |ρ.im| then ‖completedLogHalfPhaseTerm χ v ρ‖ else 0) ≤
          (192 + 1536 * Ar) * (Real.log q + Real.log (T + 4) + 1) / T :=
        hlargeTail
      _ = (192 + 1536 * Ar) * ((Real.log q + Real.log (T + 4) + 1) / T) := by ring
      _ ≤ C * ((Real.log q + Real.log (T + 4) + 1) / T) := mul_le_mul_of_nonneg_right hcoeff hden
      _ = C * (Real.log q + Real.log (T + 4) + 1) / T := by ring
  · have hTupper : T < 4 := lt_of_not_ge hlarge
    let ST := fun (S : Finset ℂ) => S.filter (fun ρ => T ≤ |ρ.im|)
    have hsmallFinite :
      ∀ S : Finset ℂ, (∑ ρ ∈ ST S, ‖completedLogHalfPhaseTerm χ v ρ‖) ≤ K * (Real.log q + 1) := by
      intro S
      have hsplit :=
        Finset.sum_filter_add_sum_filter_not (ST S) (fun ρ => (3 : ℝ) ≤ |ρ.im|)
          (fun ρ : ℂ => ‖completedLogHalfPhaseTerm χ v ρ‖)
      have hhigh :=
        @hfinite q hqInst hq χ hRH hp hne hinv 2 (by norm_num only) v
          ((ST S).filter (fun ρ => (3 : ℝ) ≤ |ρ.im|)) (fun ρ hr => (Finset.mem_filter.mp hr).2)
      have hlow' :=
        @hlow q hqInst hq χ hRH hp hne hinv v ((ST S).filter (fun ρ => ¬((3 : ℝ) ≤ |ρ.im|)))
          (fun ρ hr => by
            have hmem := Finset.mem_filter.mp hr
            have hTρ := (Finset.mem_filter.mp hmem.1).2
            have hnot3 := hmem.2
            constructor
            · exact le_trans (by exact_mod_cast hT) hTρ
            · exact not_le.mp hnot3)
      have hlog5 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num only)
      have hlog7 : 0 ≤ Real.log 7 := Real.log_nonneg (by norm_num only)
      have hAlog5 : 0 ≤ Ai * (Real.log 5 + 2) := mul_nonneg (le_of_lt hAi) (by positivity)
      have hAlog7 : 0 ≤ Al * (Real.log 7 + 1) := mul_nonneg (le_of_lt hAl) (by positivity)
      have hhigh' :
        (∑ ρ ∈ (ST S).filter (fun ρ => (3 : ℝ) ≤ |ρ.im|), ‖completedLogHalfPhaseTerm χ v ρ‖) ≤
          (48 + 768 * Ai * (Real.log 5 + 2) / 5) * (Real.log q + 1) := by
        have h := hhigh
        norm_num only [Nat.cast_ofNat] at h
        nlinarith only [h, hlogq, hAlog5, hlog5]
      have hlow'' :
        (∑ ρ ∈ (ST S).filter (fun ρ => ¬((3 : ℝ) ≤ |ρ.im|)), ‖completedLogHalfPhaseTerm χ v ρ‖) ≤
          (144 + 288 * Al * (Real.log 7 + 1)) * (Real.log q + 1) := by
        have h := hlow'
        nlinarith only [h, hlogq, hAlog7, hlog7]
      rw [← hsplit]
      dsimp only [K]
      nlinarith only [hhigh', hlow'', hlogq]
    have hsmallTail :
      (∑' ρ : ℂ, if T ≤ |ρ.im| then ‖completedLogHalfPhaseTerm χ v ρ‖ else 0) ≤
        K * (Real.log q + 1) := by
      apply Real.tsum_le_of_sum_le (fun ρ => ite_nonneg (norm_nonneg _) le_rfl)
      intro S
      have hs := hsmallFinite S
      simpa only [ST, Finset.sum_filter] using hs
    have hlogT : 0 ≤ Real.log (T + 4) := Real.log_nonneg (by linarith only [hT])
    have hZ : 0 ≤ Real.log q + Real.log (T + 4) + 1 := by linarith only [hlogq, hlogT]
    have hZlarge : Real.log q + 1 ≤ Real.log q + Real.log (T + 4) + 1 := by linarith only [hlogT]
    have hprod : T * (Real.log q + 1) ≤ 4 * (Real.log q + Real.log (T + 4) + 1) := by
      have hTle : T ≤ 4 := le_of_lt hTupper
      exact mul_le_mul hTle hZlarge (by linarith only [hlogq]) (by norm_num only)
    have hsmallScaled :
      K * (Real.log q + 1) ≤ (4 * K) * (Real.log q + Real.log (T + 4) + 1) / T := by
      have hTpos : 0 < T := by linarith only [hT]
      apply (le_div_iff₀ hTpos).2
      calc
        K * (Real.log q + 1) * T = T * (K * (Real.log q + 1)) := by ring
        _ = K * (T * (Real.log q + 1)) := by ring
        _ ≤ K * (4 * (Real.log q + Real.log (T + 4) + 1)) :=
          mul_le_mul_of_nonneg_left hprod (le_of_lt hK)
        _ = (4 * K) * (Real.log q + Real.log (T + 4) + 1) := by ring
    have hcoeff : 4 * K ≤ C := by
      rw [show C = (192 + 1536 * Ar) + 4 * K from rfl]
      nlinarith only [show 0 ≤ 192 + 1536 * Ar by positivity]
    have hscaled :
      (4 * K) * (Real.log q + Real.log (T + 4) + 1) / T ≤
        C * (Real.log q + Real.log (T + 4) + 1) / T := by
      have hfactor : 0 ≤ (Real.log q + Real.log (T + 4) + 1) / T :=
        div_nonneg hZ (by linarith only [hT])
      calc
        (4 * K) * (Real.log q + Real.log (T + 4) + 1) / T =
            (4 * K) * ((Real.log q + Real.log (T + 4) + 1) / T) :=
          by ring
        _ ≤ C * ((Real.log q + Real.log (T + 4) + 1) / T) :=
          mul_le_mul_of_nonneg_right hcoeff hfactor
        _ = C * (Real.log q + Real.log (T + 4) + 1) / T := by ring
    calc
      (∑' ρ : ℂ, if T ≤ |ρ.im| then ‖completedLogHalfPhaseTerm χ v ρ‖ else 0) ≤
          K * (Real.log q + 1) :=
        hsmallTail
      _ ≤ (4 * K) * (Real.log q + Real.log (T + 4) + 1) / T := hsmallScaled
      _ ≤ C * (Real.log q + Real.log (T + 4) + 1) / T := hscaled

/-- Under individual Dirichlet GRH, the signed phase is bounded by its low-height
complement sum plus the conductor-uniform absolute tail. The low sum remains an absolutely
convergent series here; the next finite-ledger step identifies it with the finite zero set
inside the cutoff. -/
theorem exists_logarithmicHalfPhase_le_low_add_tail_bound {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (T v : ℝ) (hT : 2 ≤ T) :
    ∃ C : ℝ,
      0 < C ∧
        logarithmicHalfPhase χ v ≤
          -(∑' ρ : { ρ : ℂ // ρ ∈ (({((1 / 2 : ℝ) : ℂ)} : Finset ℂ) : Set ℂ)ᶜ },
                  if |ρ.val.im| < T then completedLogHalfPhaseTerm χ v ρ.val else 0).re +
            C * (Real.log N + Real.log (T + 4) + 1) / T := by
  obtain ⟨C, hC, hbound⟩ := exists_tsum_norm_completedLogHalfPhaseTerm_all_real_tail_bound
  refine ⟨C, hC, ?_⟩
  have hphase := logarithmicHalfPhase_le_complement_of_dirichletRH hN hRH hp hne hinv v
  have hsplit := tsum_completedLogHalfPhaseTerm_complement_eq_low_add_high hN hRH hp hne hinv v T
  rw [hsplit] at hphase
  simp only [Complex.add_re] at hphase
  let S : Set ℂ := (({((1 / 2 : ℝ) : ℂ)} : Finset ℂ) : Set ℂ)ᶜ
  let α := { ρ : ℂ // ρ ∈ S }
  let hi : α → ℂ := fun ρ => if T ≤ |ρ.val.im| then completedLogHalfPhaseTerm χ v ρ.val else 0
  obtain ⟨_, _, hnorm⟩ := exists_summable_norm_completedLogHalfPhaseTerm
  have hbase : Summable (fun ρ : α => ‖completedLogHalfPhaseTerm χ v ρ.val‖) := by
    exact (hnorm N hN χ hRH hp hne hinv v).subtype S
  have hhiNorm : Summable (fun ρ : α => ‖hi ρ‖) :=
    Summable.of_norm_bounded hbase
      (fun ρ => by
        dsimp only [hi]
        by_cases hr : T ≤ |ρ.val.im|
        · rw [ite_eq_left hr, norm_norm]
        · rw [ite_eq_right hr, norm_zero]
          simpa only [norm_zero] using norm_nonneg (completedLogHalfPhaseTerm χ v ρ.val))
  have hhi : Summable hi := hhiNorm.of_norm
  have hhiLe : ‖∑' ρ : α, hi ρ‖ ≤ ∑' ρ : α, ‖hi ρ‖ := norm_tsum_le_tsum_norm hhiNorm
  have hhighEq0 :
    (∑' ρ : α, if T ≤ |ρ.val.im| then ‖completedLogHalfPhaseTerm χ v ρ.val‖ else 0) =
      (∑' ρ : ℂ, if T ≤ |ρ.im| then ‖completedLogHalfPhaseTerm χ v ρ‖ else 0) := by
    exact
      tsum_subtype_eq_of_support_subset (s := S) (f := fun ρ : ℂ =>
        if T ≤ |ρ.im| then ‖completedLogHalfPhaseTerm χ v ρ‖ else 0)
        (by
          intro ρ hρ
          change (if T ≤ |ρ.im| then ‖completedLogHalfPhaseTerm χ v ρ‖ else 0) ≠ 0 at hρ
          by_contra hcenter
          have hEq : ρ = ((1 / 2 : ℝ) : ℂ) := by
            by_contra hneρ
            apply hcenter
            dsimp only [S]
            rw [Set.mem_compl_iff]
            simp only [Finset.mem_coe, Finset.mem_singleton]
            exact hneρ
          have hfalse : ¬T ≤ |(((1 / 2 : ℝ) : ℂ)).im| := by
            rw [Complex.ofReal_im, abs_zero]
            exact not_le.mpr (by linarith only [hT])
          rw [hEq] at hρ
          simp only [hfalse, ↓reduceIte, ne_eq, not_true_eq_false] at hρ)
  have hnormHi :
    (fun ρ : α => ‖hi ρ‖) =
      (fun ρ => if T ≤ |ρ.val.im| then ‖completedLogHalfPhaseTerm χ v ρ.val‖ else 0) := by
    funext ρ
    by_cases hr : T ≤ |ρ.val.im|
    · simp only [hi, ite_eq_left hr]
    · simp only [hi, ite_eq_right hr, norm_zero]
  have hhighEq :
    (∑' ρ : α, ‖hi ρ‖) =
      (∑' ρ : ℂ, if T ≤ |ρ.im| then ‖completedLogHalfPhaseTerm χ v ρ‖ else 0) := by
    rw [hnormHi]
    exact hhighEq0
  have htail := hbound N hN χ hRH hp hne hinv T hT v
  have hhighBound : ‖∑' ρ : α, hi ρ‖ ≤ C * (Real.log N + Real.log (T + 4) + 1) / T := by
    calc
      ‖∑' ρ : α, hi ρ‖ ≤ ∑' ρ : α, ‖hi ρ‖ := hhiLe
      _ = ∑' ρ : ℂ, if T ≤ |ρ.im| then ‖completedLogHalfPhaseTerm χ v ρ‖ else 0 := hhighEq
      _ ≤ _ := htail
  have hneg : -(∑' ρ : α, hi ρ).re ≤ C * (Real.log N + Real.log (T + 4) + 1) / T := by
    calc
      -(∑' ρ : α, hi ρ).re ≤ |(∑' ρ : α, hi ρ).re| := neg_le_abs _
      _ ≤ ‖∑' ρ : α, hi ρ‖ := Complex.abs_re_le_norm _
      _ ≤ _ := hhighBound
  linarith only [hphase, hneg]

/-- If the conductor logarithm is at most $L$, the power cutoff $T=L^\delta$ turns the
uniform tail into a bound of order $L^{1-\delta}$. The assumptions $0<\delta<1$ record the
proper power scale, while $T\ge2$ keeps the cutoff inside the range of the absolute-tail
theorem. -/
theorem exists_tsum_norm_completedLogHalfPhaseTerm_power_cutoff_bound {N : ℕ} [NeZero N]
    (hN : 2 ≤ N) {χ : DirichletCharacter ℂ N} (hRH : GRH.DirichletRiemannHypothesis χ)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (L δ : ℝ) (hL : 4 ≤ L)
    (hlogN : Real.log N ≤ L) (hδ : 0 < δ) (hδlt : δ < 1) (hcut : 2 ≤ L ^ δ) (v : ℝ) :
    ∃ C : ℝ,
      0 < C ∧
        0 < 1 - δ ∧
        1 - δ < 1 ∧
        (∑' ρ : ℂ, if L ^ δ ≤ |ρ.im| then ‖completedLogHalfPhaseTerm χ v ρ‖ else 0) ≤
          3 * C * L ^ (1 - δ) := by
  obtain ⟨C, hC, htail⟩ := exists_tsum_norm_completedLogHalfPhaseTerm_all_real_tail_bound
  refine ⟨C, hC, ?_, ?_, ?_⟩
  · linarith only [hδlt]
  · linarith only [hδ]
  · have hLpos : 0 < L := by linarith only [hL]
    have hLone : 1 ≤ L := by linarith only [hL]
    have hTleL : L ^ δ ≤ L := by
      calc
        L ^ δ ≤ L ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hLone (le_of_lt hδlt)
        _ = L := Real.rpow_one L
    have hlogArg : Real.log (L ^ δ + 4) ≤ L ^ δ + 3 := by
      calc
        Real.log (L ^ δ + 4) ≤ (L ^ δ + 4) - 1 := Real.log_le_sub_one_of_pos (by positivity)
        _ = L ^ δ + 3 := by ring
    have hnum : Real.log N + Real.log (L ^ δ + 4) + 1 ≤ 3 * L := by
      have hmid : L + (L ^ δ + 3) + 1 ≤ 3 * L := by nlinarith only [hL, hTleL]
      linarith only [hlogN, hlogArg, hmid]
    have hratio : (Real.log N + Real.log (L ^ δ + 4) + 1) / (L ^ δ) ≤ 3 * (L / L ^ δ) := by
      have hTpos : 0 < L ^ δ := lt_of_lt_of_le (by norm_num only) hcut
      calc
        (Real.log N + Real.log (L ^ δ + 4) + 1) / (L ^ δ) ≤ (3 * L) / (L ^ δ) :=
          div_le_div_of_nonneg_right hnum (le_of_lt hTpos)
        _ = 3 * (L / L ^ δ) := by ring
    have hpow : L / L ^ δ = L ^ (1 - δ) := by rw [Real.rpow_sub hLpos 1 δ, Real.rpow_one]
    have htail' := htail N hN χ hRH hp hne hinv (L ^ δ) hcut v
    calc
      (∑' ρ : ℂ, if L ^ δ ≤ |ρ.im| then ‖completedLogHalfPhaseTerm χ v ρ‖ else 0) ≤
          C * (Real.log N + Real.log (L ^ δ + 4) + 1) / (L ^ δ) :=
        htail'
      _ = C * ((Real.log N + Real.log (L ^ δ + 4) + 1) / (L ^ δ)) := by ring
      _ ≤ C * (3 * (L / L ^ δ)) := mul_le_mul_of_nonneg_left hratio (le_of_lt hC)
      _ = 3 * C * (L / L ^ δ) := by ring
      _ = 3 * C * L ^ (1 - δ) := by rw [hpow]

/-- Under individual GRH, primitive nonprincipal completed zeros with height below `T`
form a finite set. Translating each zero by minus one half places it in a compact disk,
and the shifted completed function has finite zero support there. This is the finite
low-height ledger needed to replace the low part of the global zero series by a finite sum. -/
theorem finite_completed_divisor_support_below_height {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hp : χ.IsPrimitive) (hne : χ ≠ 1)
    (hRH : GRH.DirichletRiemannHypothesis χ) (hinv : χ⁻¹ ≠ 1) (T : ℝ) :
    {ρ : ℂ | |ρ.im| < T ∧ MeromorphicOn.divisor χ.completedLFunction Set.univ ρ ≠ 0}.Finite := by
  let U : Set ℂ := Metric.closedBall 0 (T + 1)
  have hU : IsCompact U := isCompact_closedBall 0 (T + 1)
  have hf := finite_shifted_completed_zeros hp hne hU
  let f : ℂ → ℂ := fun z => z + ((1 / 2 : ℝ) : ℂ)
  apply Set.Finite.subset (hf.image f)
  intro ρ hρ
  have hz := dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero hne hρ.2
  have hr := completedLFunction_zero_re_eq_half_of_dirichletRH hRH hp hinv hz
  rw [Set.mem_image]
  refine ⟨ρ - ((1 / 2 : ℝ) : ℂ), ?_, ?_⟩
  · constructor
    · change ρ - ((1 / 2 : ℝ) : ℂ) ∈ Metric.closedBall (0 : ℂ) (T + 1)
      rw [Metric.mem_closedBall, dist_zero_right]
      have hnorm : ‖ρ - ((1 / 2 : ℝ) : ℂ)‖ = |ρ.im| := by
        rw [Complex.norm_def, Complex.normSq_apply, Complex.sub_re, Complex.ofReal_re, hr, sub_self,
          Complex.sub_im, Complex.ofReal_im, sub_zero]
        rw [show 0 * 0 + ρ.im * ρ.im = ρ.im ^ 2 by ring, Real.sqrt_sq_eq_abs]
      rw [hnorm]
      linarith only [hρ.1]
    · change χ.completedLFunction (ρ - ((1 / 2 : ℝ) : ℂ) + 1 / 2) = 0
      have heq : ρ - ((1 / 2 : ℝ) : ℂ) + 1 / 2 = ρ := by
        push_cast
        ring
      rw [heq]
      exact hz
  · change ρ - ((1 / 2 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) = ρ
    push_cast
    ring

/-- Under individual GRH, primitivity, and nonprincipality of the character and its inverse,
the completed half-phase terms below height `T` have finite support. A nonzero term must
have nonzero divisor multiplicity, so the compact zero ledger above contains its support. -/
theorem finite_completedLogHalfPhaseTerm_support_below_height {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hp : χ.IsPrimitive) (hne : χ ≠ 1)
    (hRH : GRH.DirichletRiemannHypothesis χ) (hinv : χ⁻¹ ≠ 1) (T v : ℝ) :
    {ρ : ℂ | |ρ.im| < T ∧ completedLogHalfPhaseTerm χ v ρ ≠ 0}.Finite := by
  apply (finite_completed_divisor_support_below_height hp hne hRH hinv T).subset
  intro ρ hρ
  refine ⟨hρ.1, ?_⟩
  by_contra hD
  apply hρ.2
  simp only [completedLogHalfPhaseTerm, hD, Int.cast_zero, zero_mul, zero_div]

/-- Under individual GRH and the same character hypotheses, the half-phase sum over
noncentral zeros below height `T` is a finite sum. The finite support is pulled back to
the subtype excluding the center and `tsum_eq_sum'` replaces the infinite sum by its
finite support ledger. -/
theorem exists_finite_center_complement_low_completedLogHalfPhaseTerm_sum {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hp : χ.IsPrimitive) (hne : χ ≠ 1)
    (hRH : GRH.DirichletRiemannHypothesis χ) (hinv : χ⁻¹ ≠ 1) (T v : ℝ) :
    ∃ S : Finset { ρ : ℂ // ρ ≠ ((1 / 2 : ℝ) : ℂ) },
      (∑' ρ : { ρ : ℂ // ρ ≠ ((1 / 2 : ℝ) : ℂ) },
          if |ρ.val.im| < T then completedLogHalfPhaseTerm χ v ρ.val else 0) =
        ∑ ρ ∈ S, if |ρ.val.im| < T then completedLogHalfPhaseTerm χ v ρ.val else 0 := by
  let A : Set ℂ := {ρ | |ρ.im| < T ∧ completedLogHalfPhaseTerm χ v ρ ≠ 0}
  have hA := finite_completedLogHalfPhaseTerm_support_below_height hp hne hRH hinv T v
  let α := { ρ : ℂ // ρ ≠ ((1 / 2 : ℝ) : ℂ) }
  let f : α → ℂ := fun ρ => if |ρ.val.im| < T then completedLogHalfPhaseTerm χ v ρ.val else 0
  have hs : {ρ : α | f ρ ≠ 0}.Finite := by
    apply (hA.preimage Subtype.val_injective.injOn).subset
    intro ρ hρ
    change ρ.val ∈ A
    change (if |ρ.val.im| < T then completedLogHalfPhaseTerm χ v ρ.val else 0) ≠ 0 at hρ
    by_cases hcut : |ρ.val.im| < T
    · rw [ite_eq_left hcut] at hρ
      exact ⟨hcut, hρ⟩
    · have hzero : (if |ρ.val.im| < T then completedLogHalfPhaseTerm χ v ρ.val else 0) = 0 := by
        rw [ite_eq_right hcut]
      exact False.elim (hρ hzero)
  refine ⟨hs.toFinset, ?_⟩
  exact
    tsum_eq_sum' (f := f) (s := hs.toFinset)
      (by
        intro ρ hρ
        exact
          (Set.Finite.mem_toFinset hs).2
            (by
              change f ρ ≠ 0
              exact hρ))

/-- Under individual GRH, the low-height complement in the logarithmic half-phase bound
can be taken as an explicit finite sum. The absolute tail estimate is unchanged; this
corollary packages the finite support ledger with the signed phase inequality. -/
theorem exists_logarithmicHalfPhase_le_finite_low_add_tail_bound {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (T v : ℝ) (hT : 2 ≤ T) :
    ∃ C : ℝ,
      0 < C ∧
        ∃ S : Finset { ρ : ℂ // ρ ∈ (({((1 / 2 : ℝ) : ℂ)} : Finset ℂ) : Set ℂ)ᶜ },
          logarithmicHalfPhase χ v ≤
            -(∑ ρ ∈ S, if |ρ.val.im| < T then completedLogHalfPhaseTerm χ v ρ.val else 0).re +
              C * (Real.log N + Real.log (T + 4) + 1) / T := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_logarithmicHalfPhase_le_low_add_tail_bound hN hRH hp hne hinv T v hT
  have hA := finite_completedLogHalfPhaseTerm_support_below_height hp hne hRH hinv T v
  let S : Set ℂ := (({((1 / 2 : ℝ) : ℂ)} : Finset ℂ) : Set ℂ)ᶜ
  let α := { ρ : ℂ // ρ ∈ S }
  let f : α → ℂ := fun ρ => if |ρ.val.im| < T then completedLogHalfPhaseTerm χ v ρ.val else 0
  have hs : {ρ : α | f ρ ≠ 0}.Finite := by
    apply (hA.preimage Subtype.val_injective.injOn).subset
    intro ρ hρ
    change ρ.val ∈ {z | |z.im| < T ∧ completedLogHalfPhaseTerm χ v z ≠ 0}
    change (if |ρ.val.im| < T then completedLogHalfPhaseTerm χ v ρ.val else 0) ≠ 0 at hρ
    by_cases hcut : |ρ.val.im| < T
    · rw [ite_eq_left hcut] at hρ
      exact ⟨hcut, hρ⟩
    · have hzero : (if |ρ.val.im| < T then completedLogHalfPhaseTerm χ v ρ.val else 0) = 0 := by
        rw [ite_eq_right hcut]
      exact False.elim (hρ hzero)
  have hsum : (∑' ρ : α, f ρ) = ∑ ρ ∈ hs.toFinset, f ρ :=
    tsum_eq_sum' (f := f) (s := hs.toFinset)
      (by
        intro ρ hρ
        exact
          (Set.Finite.mem_toFinset hs).2
            (by
              change f ρ ≠ 0
              exact hρ))
  refine ⟨C, hC, hs.toFinset, ?_⟩
  rw [← hsum]
  exact hbound

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
