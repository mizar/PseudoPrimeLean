/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.GeneralScaleHighPrime
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.HighPrimeIncidence

/-! # General-scale high-prime incidence with zero multiplicities -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity

/-- For a positive conductor cap and mesh density, a grid window of physical width at most
one has local conductor-height logarithm at most twice the global logarithm.
Bound the grid height by `T+1` and the local logarithm argument by the square of the
global argument. This controls multiplicity weights at general scales. -/
theorem expanded_grid_conductor_height_log_le {Q T M W : ℕ} (hQ : 0 < Q) (hM : 0 < M)
    (hwindow : (W + 1 : ℝ) / M ≤ 1) (q : Fin Q) (m : ℤ)
    (hm : m ∈ Finset.Icc (-(T * M : ℤ) - (W + 1 : ℤ)) ((T * M : ℤ) + (W + 1 : ℤ))) :
    Real.log (((q.val + 1 : ℕ) : ℝ) * (|((m : ℝ) / M)| + 3)) ≤
      2 * Real.log ((Q : ℝ) * ((T : ℝ) + 3)) := by
  have hq : ((q.val + 1 : ℕ) : ℝ) ≤ (Q : ℝ) := Nat.cast_le.mpr (Nat.succ_le_of_lt q.isLt)
  have hqpos : (0 : ℝ) < ((q.val + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos _)
  have hQreal : 1 ≤ (Q : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hQ)
  have hT : 0 ≤ (T : ℝ) := Nat.cast_nonneg T
  have hMreal : 0 < (M : ℝ) := Nat.cast_pos.mpr hM
  have hmInt : |m| ≤ (T * M : ℤ) + (W + 1 : ℤ) :=
    abs_le.mpr ⟨by linarith only [(Finset.mem_Icc.mp hm).1], (Finset.mem_Icc.mp hm).2⟩
  have hmReal : |(m : ℝ)| ≤ (T : ℝ) * M + (W + 1 : ℝ) := by exact_mod_cast hmInt
  have hheight : |(m : ℝ) / M| ≤ (T : ℝ) + 1 := by
    rw [abs_div, abs_of_pos hMreal]
    apply (div_le_iff₀ hMreal).mpr
    have hwidth := (div_le_iff₀ hMreal).mp hwindow
    nlinarith only [hmReal, hwidth]
  have harg : ((q.val + 1 : ℕ) : ℝ) * (|((m : ℝ) / M)| + 3) ≤ ((Q : ℝ) * ((T : ℝ) + 3)) ^ 2 := by
    have hheight' : |((m : ℝ) / M)| + 3 ≤ ((T : ℝ) + 3) ^ 2 := by nlinarith only [hheight, hT]
    have hQsq : (Q : ℝ) ≤ (Q : ℝ) ^ 2 := by nlinarith only [hQreal]
    calc
      _ ≤ (Q : ℝ) * (((T : ℝ) + 3) ^ 2) :=
        mul_le_mul hq hheight' (by linarith only [abs_nonneg ((m : ℝ) / M)])
          (by linarith only [hQreal])
      _ ≤ (Q : ℝ) ^ 2 * (((T : ℝ) + 3) ^ 2) := mul_le_mul_of_nonneg_right hQsq (sq_nonneg _)
      _ = _ := by ring
  have hargpos :=
    mul_pos hqpos (by linarith only [abs_nonneg ((m : ℝ) / M)] : 0 < |((m : ℝ) / M)| + 3)
  have hlog := Real.log_le_log hargpos harg
  simpa only [Real.log_pow, Nat.cast_ofNat] using hlog

/-- For a small positive shift and a narrow grid window, the local multiplicity ceiling is
bounded by one common ceiling linear in the scaled conductor-height logarithm.
Apply the expanded-grid logarithm comparison and ceiling monotonicity.
This preserves the scale dependence needed for general zero-density estimates. -/
theorem completedZeroLocalLogBoundCeil_le_general_scale_grid {Q T M W : ℕ} {η : ℝ} (hQ : 0 < Q)
    (hη : 0 < η) (hηsmall : η ≤ 1 / 1288) (hM : 0 < M) (hwindow : (W + 1 : ℝ) / M ≤ η / 8)
    (q : Fin Q) (m : ℤ)
    (hm : m ∈ Finset.Icc (-(T * M : ℤ) - (W + 1 : ℤ)) ((T * M : ℤ) + (W + 1 : ℤ))) :
    Nat.ceil
        (completedZeroLocalLogBoundConstant *
          (1 + 8 * η * Real.log (((q.val + 1 : ℕ) : ℝ) * (|((m : ℝ) / M)| + 3)))) ≤
      Nat.ceil
        (completedZeroLocalLogBoundConstant *
          (1 + 16 * η * Real.log ((Q : ℝ) * ((T : ℝ) + 3)))) := by
  have hwidth : (W + 1 : ℝ) / M ≤ 1 := by linarith only [hwindow, hηsmall]
  have hlog := expanded_grid_conductor_height_log_le hQ hM hwidth q m hm
  apply Nat.ceil_mono
  apply mul_le_mul_of_nonneg_left _ completedZeroLocalLogBoundConstant_pos.le
  nlinarith only [hlog, hη]

open Classical in
/-- Given a multiplicity-preserving occurrence detector, bound zero count times window
gain by the common logarithmic multiplicity weight times the family order-event sum.
Use the existing incidence estimate and compare its local weights on the expanded grid.
This replaces the fixed-scale restriction in the finite event-count interface. -/
theorem primitiveFamilyZeroOccurrence_mul_window_le_general_scale_order_events (Q : ℕ) (hQ : 0 < Q)
    {σ η : ℝ} (hσ1 : σ ≤ 1) (hσeta : 1 - σ ≤ η) (hη : 0 < η) (hηsmall : η ≤ 1 / 1288)
    (T nmax M W : ℕ) (hM : 0 < M) (hwindow : (W + 1 : ℝ) / M ≤ η / 8)
    (event : (q : Fin Q) → DirichletCharacter ℂ (q.val + 1) → ℕ → ℤ → Prop)
    [∀ q χ n, DecidablePred (event q χ n)]
    (hdetector :
      ∀
        {x :
          Σ q : Fin Q,
            Σ χ : DirichletCharacter ℂ (q.val + 1),
              Σ ρ : ℂ, Fin (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ)},
        x ∈ primitiveCharacterFamilyZeroOccurrenceLedger Q σ T →
          ∃ n ≤ nmax, ∀ j : ℤ, |x.2.2.1.im - (j : ℝ) / M| ≤ (W + 1 : ℝ) / M → event x.1 x.2.1 n j) :
    primitiveCharacterFamilyZeroOccurrenceCountAtNatHeight Q σ T * (2 * W + 1 : ℝ) ≤
      (Nat.ceil
            (completedZeroLocalLogBoundConstant *
              (1 + 16 * η * Real.log ((Q : ℝ) * ((T : ℝ) + 3)))) :
          ℝ) *
        (∑ q : Fin Q,
          ∑ χ : DirichletCharacter ℂ (q.val + 1),
            if _hχ : χ ≠ 1 then
              if _hprim : χ.IsPrimitive then
                ∑ m ∈ Finset.Icc (-(T * M : ℤ) - (W + 1 : ℤ)) ((T * M : ℤ) + (W + 1 : ℤ)),
                  ∑ n ∈ Finset.range (nmax + 1), if event q χ n m then (1 : ℝ) else 0
              else 0
            else 0) := by
  have hinc :=
    primitiveFamilyZeroOccurrence_mul_window_le_order_event_sum Q hσ1 hσeta hη hηsmall T nmax M W hM
      (show (W + 1 : ℝ) / M ≤ η by nlinarith only [hwindow, hη]) event hdetector
  apply hinc.trans
  simp only [Finset.mul_sum, mul_dite, mul_zero]
  apply Finset.sum_le_sum
  intro q hqmem
  apply Finset.sum_le_sum
  intro χ hχmem
  by_cases hχ : χ ≠ 1
  · by_cases hprim : χ.IsPrimitive
    · simp only [dite_eq_left hχ, dite_eq_left hprim]
      apply Finset.sum_le_sum
      intro m hm
      have hc :=
        completedZeroLocalLogBoundCeil_le_general_scale_grid hQ hη hηsmall hM hwindow q m hm
      have hcreal :
        (Nat.ceil
              (completedZeroLocalLogBoundConstant *
                (1 + 8 * η * Real.log (((q.val + 1 : ℕ) : ℝ) * (|((m : ℝ) / M)| + 3)))) :
            ℝ) ≤
          (Nat.ceil
              (completedZeroLocalLogBoundConstant *
                (1 + 16 * η * Real.log ((Q : ℝ) * ((T : ℝ) + 3)))) :
            ℝ) := by
        exact_mod_cast hc
      apply Finset.sum_le_sum
      intro n hn
      exact mul_le_mul_of_nonneg_right hcreal (by split <;> norm_num only)
    · simp only [dite_eq_left hχ, dite_eq_right hprim]
      exact le_rfl
  · simp only [dite_eq_right hχ]
    exact le_rfl

/-- For an actual high-prime occurrence detector on a shared mesh, bound zero count times
window gain by its high-prime event sum with a common logarithmic multiplicity weight.
Instantiate the general event bound and distribute the primitive-character filters.
This connects the common-support detector to normalized large-value counting. -/
theorem primitiveFamilyZeroOccurrence_mul_window_le_general_scale_prime_events (Q : ℕ) (hQ : 0 < Q)
    {σ η : ℝ} (hσ1 : σ ≤ 1) (hσeta : 1 - σ ≤ η) (hη : 0 < η) (hηsmall : η ≤ 1 / 1288)
    (T nmax M W R cutoff : ℕ) (hM : 0 < M) (hwindow : (W + 1 : ℝ) / M ≤ η / 8) (B : ℝ)
    (hdetector :
      ∀
        {x :
          Σ q : Fin Q,
            Σ χ : DirichletCharacter ℂ (q.val + 1),
              Σ ρ : ℂ, Fin (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ)},
        x ∈ primitiveCharacterFamilyZeroOccurrenceLedger Q σ T →
          ∃ n ≤ nmax,
            ∀ j : ℤ,
              |x.2.2.1.im - (j : ℝ) / M| ≤ (W + 1 : ℝ) / M →
                B ≤
                  (η ^ (n + 1) / (n.factorial : ℝ)) *
                    ‖primeLogPowerPolynomial (highPrimeEulerSupport R cutoff) n (1 + η)
                        (fun k ↦ x.2.1 (k : ZMod (x.1.val + 1))) ((j : ℝ) / M)‖) :
    primitiveCharacterFamilyZeroOccurrenceCountAtNatHeight Q σ T * (2 * W + 1 : ℝ) ≤
      (Nat.ceil
            (completedZeroLocalLogBoundConstant *
              (1 + 16 * η * Real.log ((Q : ℝ) * ((T : ℝ) + 3)))) :
          ℝ) *
        highPrimeFamilyGridEventSum Q T nmax M W R cutoff η B := by
  classical
  have hinc :=
    primitiveFamilyZeroOccurrence_mul_window_le_general_scale_order_events Q hQ hσ1 hσeta hη hηsmall
      T nmax M W hM hwindow
      (fun q χ n j ↦
        B ≤
          (η ^ (n + 1) / (n.factorial : ℝ)) *
            ‖primeLogPowerPolynomial (highPrimeEulerSupport R cutoff) n (1 + η)
                (fun k ↦ χ (k : ZMod (q.val + 1))) ((j : ℝ) / M)‖)
      hdetector
  apply hinc.trans_eq
  unfold highPrimeFamilyGridEventSum
  congr 1
  apply Finset.sum_congr rfl
  intro q hqmem
  apply Finset.sum_congr rfl
  intro χ hχmem
  by_cases hχ : χ ≠ 1
  · by_cases hp : χ.IsPrimitive
    · simp only [dite_eq_left hχ, dite_eq_left hp]
    · simp only [dite_eq_left hχ, dite_eq_right hp, Finset.sum_const_zero]
  · simp only [dite_eq_right hχ, Finset.sum_const_zero]

/-- For nonnegative shift and signal threshold, a shared occurrence detector bounds zero
count times window gain and squared signal by a logarithmically weighted normalized
family mean square. Apply incidence counting and the finite Markov estimate.
This supplies the general-scale multiplicity-preserving input to hybrid averaging. -/
theorem primitiveFamilyZeroOccurrence_general_scale_meanSquare_bound (Q : ℕ) (hQ : 0 < Q) {σ η : ℝ}
    (hσ1 : σ ≤ 1) (hσeta : 1 - σ ≤ η) (hη : 0 < η) (hηsmall : η ≤ 1 / 1288)
    (T nmax M W R cutoff : ℕ) (hM : 0 < M) (hwindow : (W + 1 : ℝ) / M ≤ η / 8) (B : ℝ) (hB : 0 ≤ B)
    (hdetector :
      ∀
        {x :
          Σ q : Fin Q,
            Σ χ : DirichletCharacter ℂ (q.val + 1),
              Σ ρ : ℂ, Fin (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ)},
        x ∈ primitiveCharacterFamilyZeroOccurrenceLedger Q σ T →
          ∃ n ≤ nmax,
            ∀ j : ℤ,
              |x.2.2.1.im - (j : ℝ) / M| ≤ (W + 1 : ℝ) / M →
                B ≤
                  (η ^ (n + 1) / (n.factorial : ℝ)) *
                    ‖primeLogPowerPolynomial (highPrimeEulerSupport R cutoff) n (1 + η)
                        (fun k ↦ x.2.1 (k : ZMod (x.1.val + 1))) ((j : ℝ) / M)‖) :
    primitiveCharacterFamilyZeroOccurrenceCountAtNatHeight Q σ T * (2 * W + 1 : ℝ) * B ^ 2 ≤
      (Nat.ceil
            (completedZeroLocalLogBoundConstant *
              (1 + 16 * η * Real.log ((Q : ℝ) * ((T : ℝ) + 3)))) :
          ℝ) *
        highPrimeFamilyGridMeanSquareSum Q T nmax M W R cutoff η := by
  have hinc :=
    mul_le_mul_of_nonneg_right
      (primitiveFamilyZeroOccurrence_mul_window_le_general_scale_prime_events Q hQ hσ1 hσeta hη
        hηsmall T nmax M W R cutoff hM hwindow B hdetector)
      (sq_nonneg B)
  have hmean :=
    mul_le_mul_of_nonneg_left
      (highPrimeFamilyGridEventSum_mul_sq_le_meanSquareSum Q T nmax M W R cutoff η B hη.le hB)
      (Nat.cast_nonneg
        (Nat.ceil
          (completedZeroLocalLogBoundConstant * (1 + 16 * η * Real.log ((Q : ℝ) * ((T : ℝ) + 3))))))
  nlinarith only [hinc, hmean]

/-- A primitive-family ledger occurrence supplies a nonprincipal primitive character,
a completed zero in the near-one strip, and the recorded height bound. Extract its
rectangle membership and retain its multiplicity index. This supplies the hypotheses
of the general-scale detector without a bound on the scaled conductor-height logarithm. -/
theorem primitiveFamilyOccurrence_general_scale_context {Q : ℕ} {σ η : ℝ} (hσ : σ ≤ 1)
    (hσeta : 1 - σ ≤ η) (T : ℕ)
    {x :
      Σ q : Fin Q,
        Σ χ : DirichletCharacter ℂ (q.val + 1),
          Σ ρ : ℂ, Fin (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ)}
    (hx : x ∈ primitiveCharacterFamilyZeroOccurrenceLedger Q σ T) :
    2 ≤ x.1.val + 1 ∧
      x.2.1 ≠ 1 ∧
      x.2.1.IsPrimitive ∧
      |x.2.2.1.re - 1| ≤ η ∧
      |x.2.2.1.im| ≤ (T : ℝ) ∧ DirichletCharacter.completedLFunction x.2.1 x.2.2.1 = 0 := by
  obtain ⟨q, χ, ρ, i, hχ, hxEq, hprim, hρ⟩ :=
    primitiveCharacterFamilyZeroOccurrenceLedger_mem_extract hx
  subst x
  have hbox := (mem_completedZerosInRectangle_iff.mp hρ).1
  rw [dirichletCompletedLFunctionRectangleBox, Rectangle.rectangleClosedBox,
    Complex.mem_reProdIm] at hbox
  have hreBox : ρ.re ∈ Set.uIcc σ 1 := by
    simpa only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, sub_zero, mul_zero, Complex.add_re, Complex.one_re,
      add_zero] using hbox.1
  have hre : σ ≤ ρ.re ∧ ρ.re ≤ 1 := by simpa only [Set.uIcc_of_le hσ, Set.mem_Icc] using hreBox
  have hρre : |ρ.re - 1| ≤ η := by
    rw [abs_le]
    exact ⟨by linarith only [hre.1, hσeta], by linarith only [hre.2, hσeta, hσ]⟩
  have hxocc :
    (⟨ρ, i⟩ : Σ z : ℂ, Fin (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) z)) ∈
      completedZeroMultiplicityOccurrences χ hχ ((σ : ℂ) - (T : ℝ) * Complex.I)
        ((1 : ℂ) + (T : ℝ) * Complex.I) := by
    simp only [completedZeroMultiplicityOccurrences, Finset.mem_sigma]
    exact ⟨hρ, Finset.mem_univ i⟩
  exact
    ⟨two_le_succ_modulus_of_nonprincipal q.val χ hχ, hχ, hprim, hρre,
      abs_le.mpr (completedZeroMultiplicityOccurrences_height_mem χ hχ σ T hxocc),
      (mem_completedZerosInRectangle_iff.mp hρ).2⟩

/-- Absolute cap and shift constants give, for every sufficiently large conductor
scale and every bounded height, one common support and mesh for the actual family
zero count. The cap is linear in the conductor-height scale; the physical incidence
gain and logarithmic support bound are explicit. Apply the actual zero-window
detector to every ledger occurrence and then the general-scale mean-square estimate.
This removes all detector and cap hypotheses before the hybrid bound is inserted. -/
theorem exists_uniform_general_scale_occurrence_meanSquare_bound :
    ∃ B η₀ : ℝ,
      0 < B ∧
        0 < η₀ ∧
        ∃ R₀ : ℕ,
          3 ≤ R₀ ∧
            ∀ (R T : ℕ) (σ η : ℝ) (Mmin : ℕ),
              R₀ ≤ R →
                T ≤ R →
                σ ≤ 1 →
                1 - σ ≤ η →
                0 < η →
                η ≤ η₀ →
                ∃ N cutoff M W : ℕ,
                  4 ≤ N ∧
                    (N : ℝ) ≤ B * (1 + η * Real.log ((R : ℝ) * ((R : ℝ) + 3))) ∧
                    R ^ 6 ≤ cutoff ∧
                    1 ≤ cutoff ∧
                    Mmin ≤ M ∧
                    0 < M ∧
                    (W + 1 : ℝ) / M ≤ η / 8 ∧
                    η * Real.exp (-(Real.log 414720 * N)) /
                        (16 * primeLogPowerVariationBound (4 * N)) ≤
                      (2 * W + 1 : ℝ) / M ∧
                    η * Real.log ((cutoff : ℝ) + 1) ≤
                      2 * ((4 * N : ℕ) + Real.log 414720 * N + Real.log (24 * (Real.log 4 + 4))) +
                        η * Real.log ((R ^ 6 : ℕ) : ℝ) +
                        η * Real.log 3 ∧
                    primitiveCharacterFamilyZeroOccurrenceCountAtNatHeight R σ T * (2 * W + 1 : ℝ) *
                        (Real.exp (-(Real.log 414720 * N)) / 16) ^ 2 ≤
                      (Nat.ceil
                            (completedZeroLocalLogBoundConstant *
                              (1 + 16 * η * Real.log ((R : ℝ) * ((T : ℝ) + 3)))) :
                          ℝ) *
                        highPrimeFamilyGridMeanSquareSum R T (4 * N) M W R cutoff η := by
  obtain ⟨B, η₀, hB, hη₀, hηsmall, R₀, hR₀, hzeros⟩ :=
    exists_uniform_completed_zero_general_scale_high_prime_window
  refine ⟨B, η₀, hB, hη₀, R₀, hR₀, ?_⟩
  intro R T σ η Mmin hR hT hσ hση hη hηbound
  obtain ⟨N, cutoff, hN, hNupper, hcutoff, hpos, hlog, hsignal⟩ := hzeros R hR η hη hηbound
  let δ := η * Real.exp (-(Real.log 414720 * N)) / (16 * primeLogPowerVariationBound (4 * N))
  have hD : 0 ≤ Real.log 414720 := Real.log_nonneg (by norm_num only)
  have hδ : 0 < δ :=
    div_pos (mul_pos hη (Real.exp_pos _))
      (mul_pos (by norm_num only) (primeLogPowerVariationBound_pos _))
  have hδsmall : δ ≤ η / 8 := by
    have h :=
      mul_le_mul_of_nonneg_left (uniform_high_prime_window_factor_le (Real.log 414720) N (4 * N) hD)
        hη.le
    simpa only [δ, ← mul_div_assoc, mul_one] using h
  obtain ⟨M, W, hMmin, hM, hwidth, hgain⟩ := exists_mesh_window_with_physical_radius δ Mmin hδ
  have hwidthsmall := hwidth.trans hδsmall
  refine ⟨N, cutoff, M, W, hN, hNupper, hcutoff, hpos, hMmin, hM, hwidthsmall, hgain, hlog, ?_⟩
  have hRpos : 0 < R := lt_of_lt_of_le (by decide : 0 < 3) (hR₀.trans hR)
  apply
    primitiveFamilyZeroOccurrence_general_scale_meanSquare_bound R hRpos hσ hση hη
      (hηbound.trans hηsmall) T (4 * N) M W R cutoff hM hwidthsmall
      (Real.exp (-(Real.log 414720 * N)) / 16) (div_nonneg (Real.exp_pos _).le (by norm_num only))
  intro x hx
  have hq : NeZero (x.1.val + 1) := ⟨Nat.succ_ne_zero _⟩
  obtain ⟨hmod, hχ, hp, hρre, hheight, hzero⟩ :=
    primitiveFamilyOccurrence_general_scale_context hσ hση T hx
  obtain ⟨n, hnlow, hnupper, hwindow⟩ :=
    @hsignal (x.1.val + 1) hq x.2.1 hmod (Nat.succ_le_of_lt x.1.isLt) hχ hp x.2.2.1
      (hheight.trans (Nat.cast_le.mpr hT)) hρre hzero
  refine ⟨n, (Nat.le_succ n).trans hnupper, ?_⟩
  intro j hj
  apply hwindow ((j : ℝ) / M)
  rw [abs_sub_comm]
  exact hj.trans hwidth

/-- When the scaled conductor logarithm is at least one, the physical incidence gain
absorbs mesh density and the hybrid logarithmic factor with the same loss as at the
boundary scale. Compare the shift with the reciprocal logarithm and reuse the
boundary sampling estimate. This prevents an additional grid factor at general scales. -/
theorem mesh_hybrid_sampling_loss_le_of_scaled_log_ge_one (η D : ℝ) (Kmax nmax R M W : ℕ)
    (hM : 0 < M) (hR : 2 ≤ R) (hscale : 1 ≤ η * Real.log (R : ℝ))
    (hgain :
      η * Real.exp (-(D * (Kmax : ℝ))) / (16 * primeLogPowerVariationBound nmax) ≤
        (2 * W + 1 : ℝ) / M) :
    2 * (M : ℝ) / ((2 * W + 1 : ℝ) * Real.log R) ≤
      32 * primeLogPowerVariationBound nmax * Real.exp (D * (Kmax : ℝ)) := by
  have hlog : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast hR)
  have hηlower : 1 / Real.log (R : ℝ) ≤ η := (div_le_iff₀ hlog).mpr hscale
  have hboundary : (1 / Real.log (R : ℝ)) * Real.log (R : ℝ) = 1 :=
    one_div_mul_cancel (ne_of_gt hlog)
  have hgain' :
    (1 / Real.log (R : ℝ)) * Real.exp (-(D * (Kmax : ℝ))) /
        (16 * primeLogPowerVariationBound nmax) ≤
      (2 * W + 1 : ℝ) / M :=
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hηlower (Real.exp_nonneg _))
          (mul_nonneg (by norm_num only) (primeLogPowerVariationBound_pos _).le)).trans
      hgain
  exact
    mesh_hybrid_sampling_loss_le_at_boundary_scale (1 / Real.log (R : ℝ)) D Kmax nmax R M W
      (div_pos zero_lt_one hlog) hM hboundary hgain'

/-- For an arbitrary nonnegative local multiplicity weight, a shared occurrence
mean-square bound and physical window yield an explicit zero-count bound whenever
the scaled conductor logarithm is at least one. Apply the normalized hybrid bound,
discard its decaying tail, and absorb the mesh density using the physical gain.
This leaves only order-dependent energy, variation, and exponential signal factors. -/
theorem highPrime_general_scale_count_le_of_meanSquare (N η D c₁ L : ℝ)
    (Kmax nmax R cutoff T M W : ℕ) (hR : 2 ≤ R) (hT : T ≤ R) (hM : 0 < M) (hη : 0 < η)
    (hηsmall : 2 * η ≤ 1) (hc₁ : 0 ≤ c₁) (hL : 0 ≤ L) (hwidth : ((W : ℝ) + 1) / M ≤ η / 8)
    (hscale : 1 ≤ η * Real.log (R : ℝ))
    (hgain :
      η * Real.exp (-(D * (Kmax : ℝ))) / (16 * primeLogPowerVariationBound nmax) ≤
        (2 * W + 1 : ℝ) / M)
    (hlogX : η * Real.log ((cutoff : ℝ) + 1) ≤ c₁ * Kmax)
    (hlarge : ((2 * nmax + 1 : ℕ) : ℝ) ≤ 6 * Real.log (R : ℝ))
    (hcount :
      N * (2 * W + 1 : ℝ) * (Real.exp (-(D * Kmax)) / 16) ^ 2 ≤
        L * highPrimeFamilyGridMeanSquareSum R T nmax M W R cutoff η) :
    N ≤
      (L * (4096 * (1 + (c₁ * Kmax / 8) ^ 2 / 2) * highPrimeOrderEnvelopeEnergy nmax) /
          (Real.exp (-(D * Kmax)) / 16) ^ 2) *
        (32 * primeLogPowerVariationBound nmax * Real.exp (D * Kmax)) := by
  have hlog : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast hR)
  have hH : 0 ≤ 4096 * (1 + (c₁ * Kmax / 8) ^ 2 / 2) * highPrimeOrderEnvelopeEnergy nmax :=
    mul_nonneg
      (mul_nonneg (by norm_num only)
        (add_nonneg zero_le_one (div_nonneg (sq_nonneg _) (by norm_num only))))
      (highPrimeOrderEnvelopeEnergy_nonneg nmax)
  have hhybrid :=
    highPrimeFamilyGridMeanSquareSum_hybrid_bound R cutoff nmax T M W hR hT η c₁ Kmax hM hη hηsmall
      hc₁ hwidth hlogX hlarge
  have hfactor : 0 ≤ (4096 : ℝ) / Real.log R * (1 + (c₁ * Kmax / 8) ^ 2 / 2) :=
    mul_nonneg (div_nonneg (by norm_num only) hlog.le)
      (add_nonneg zero_le_one (div_nonneg (sq_nonneg _) (by norm_num only)))
  have henergy :=
    mul_le_mul_of_nonneg_left
      (highPrime_grid_energy_sum_le nmax R η hη.le ((by decide : 1 ≤ 2).trans hR)) hfactor
  have hmean :
    highPrimeFamilyGridMeanSquareSum R T nmax M W R cutoff η * ((1 / (M : ℝ)) / 2) ≤
      (4096 * (1 + (c₁ * Kmax / 8) ^ 2 / 2) * highPrimeOrderEnvelopeEnergy nmax) / Real.log R := by
    convert hhybrid.trans henergy using 1
    ring
  have hraw :=
    count_le_sampling_loss_of_meanSquare N (2 * W + 1) (Real.exp (-(D * Kmax)) / 16) L
      (highPrimeFamilyGridMeanSquareSum R T nmax M W R cutoff η)
      (4096 * (1 + (c₁ * Kmax / 8) ^ 2 / 2) * highPrimeOrderEnvelopeEnergy nmax) M (Real.log R)
      (add_pos_of_nonneg_of_pos (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) (Nat.cast_nonneg W))
        zero_lt_one)
      (div_pos (Real.exp_pos _) (by norm_num only)) hL (Nat.cast_pos.mpr hM) hcount hmean
  exact
    hraw.trans
      (mul_le_mul_of_nonneg_left
        (mesh_hybrid_sampling_loss_le_of_scaled_log_ge_one η D Kmax nmax R M W hM hR hscale hgain)
        (div_nonneg (mul_nonneg hL hH) (sq_nonneg _)))

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity
