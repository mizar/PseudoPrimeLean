/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.RationalPoleKernel
public import PseudoPrime.LLS.PaperStatements.MellinKernelExplicitFormula
import PseudoPrime.LLS.PaperStatements.MellinKernelGammaBounds
import PseudoPrime.LLS.PaperStatements.TriangularConductorFormula
import PseudoPrime.LLS.PaperStatements.ReciprocalGapReflectedEuler
import PseudoPrime.LLS.PaperStatements.ResolventLaplaceWeights
import PseudoPrime.LLS.PaperStatements.ReciprocalGapReflectedDigamma
import PseudoPrime.LLS.PaperStatements.ReciprocalGapReflectedGamma
import PseudoPrime.AnalyticNumberTheory.General.WeightedDirichletIntegrals
import PseudoPrime.AnalyticNumberTheory.Arithmetic.CharacterAmbientTriviality
import PseudoPrime.AnalyticNumberTheory.Gamma.GammaNodeRationalCertificate
import PseudoPrime.Analysis.NumericalLogBounds
public import PseudoPrime.Analysis.ExponentialMomentTail
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticTripleCharacters
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Constants
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131PsiBounds
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Constants
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131PsiBounds

/-! # Mellin inversion for the K131 forward kernel -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private noncomputable def k131Pole (j : Fin 9) : LLS.PaperStatements.MellinKernel :=
  LLS.PaperStatements.rationalPoleMellinKernel (j.val + 2) (8 / 27) (9 / 8)
    (Nat.le_add_left 1 (j.val + 1)) (by norm_num only) (by norm_num only)

private noncomputable def k131PoleScale (j : Fin 9) : ℝ :=
  (gaussianK131Amplitude : ℝ) * (inverseCoeffs j : ℝ) * ((2 * j.val + 3).factorial : ℝ) *
    (16 / 27 : ℝ) ^ (2 * j.val + 3)

/-- The K131 transform is the positive linear combination of nine translated
reciprocal powers, with the pole at minus 27/16 and the support shift 9/4. -/
noncomputable def k131MellinFn (s : ℂ) : ℂ :=
  ∑ j : Fin 9, (k131PoleScale j : ℂ) * (k131Pole j).function s

private theorem k131_mellin_inversion {σ u : ℝ} (hσ : 0 < σ + (2 * (8 / 27 : ℝ))⁻¹) (hu : 0 < u) :
    Analysis.inverseMellin k131MellinFn σ u =
      ∑ j : Fin 9, (k131PoleScale j : ℂ) * (k131Pole j).transform u := by
  have he (j : Fin 9) :
    Analysis.inverseMellin (k131Pole j).function σ u = (k131Pole j).transform u := by
    change
      Analysis.inverseMellin (Analysis.rationalPoleFunction (j.val + 2) (8 / 27) (9 / 8)) σ u =
        Analysis.inverseMellin (Analysis.rationalPoleFunction (j.val + 2) (8 / 27) (9 / 8)) 0 u
    have hj : 1 ≤ j.val + 2 := Nat.le_add_left 1 (j.val + 1)
    rw [Analysis.inverseMellin_rationalPole hj (by norm_num only) hσ hu,
      Analysis.inverseMellin_rationalPole hj (by norm_num only) (by norm_num only) hu]
  simp only [← he]
  unfold Analysis.inverseMellin k131MellinFn
  simp only [Finset.sum_mul, mul_assoc]
  rw [MeasureTheory.integral_finsetSum]
  · simp only [MeasureTheory.integral_const_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  · intro j _
    exact
      (LLS.PaperStatements.integrable_inverseMellin_of_line hu
            (LLS.PaperStatements.integrable_rationalPole_line (Nat.le_add_left 1 (j.val + 1))
              (by norm_num only) hσ (9 / 8))).const_mul
        _

/-- The inverse Mellin profile of the K131 kernel, supported at positive
arguments up to the translated edge. -/
noncomputable def k131MellinProfile (u : ℝ) : ℝ :=
  if 0 < u ∧ Real.log u ≤ 9 / 4 then
    let v := 9 / 4 - Real.log u
    (gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * v) * gaussianK131Inverse v
  else 0

private theorem k131_pole_transform (j : Fin 9) {u : ℝ} (hu : 0 < u) :
    (k131Pole j).transform u =
      (Analysis.rationalPoleProfile (j.val + 2) (8 / 27) (9 / 8) u : ℂ) := by
  change Analysis.inverseMellin (Analysis.rationalPoleFunction (j.val + 2) (8 / 27) (9 / 8)) 0 u = _
  exact
    Analysis.inverseMellin_rationalPole (Nat.le_add_left 1 (j.val + 1)) (by norm_num only)
      (by norm_num only) hu _

private theorem k131_scaled_profile (j : Fin 9) {u : ℝ} (hu : 0 < u) (hlog : Real.log u ≤ 9 / 4) :
    k131PoleScale j * Analysis.rationalPoleProfile (j.val + 2) (8 / 27) (9 / 8) u =
      let v := 9 / 4 - Real.log u
      ((gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * v)) *
        ((inverseCoeffs j : ℝ) * v ^ (2 * j.val + 3)) := by
  unfold Analysis.rationalPoleProfile
  have h₂ : 2 * (9 / 8 : ℝ) = 9 / 4 := by norm_num only
  have h₃ : 2 * (8 / 27 : ℝ) = 16 / 27 := by norm_num only
  rw [h₂, h₃, ite_eq_left ⟨hu, hlog⟩]
  have hpow : 2 * (j.val + 2) - 1 = 2 * j.val + 3 := by
    rw [Nat.mul_add]
    rfl
  rw [hpow, div_pow]
  dsimp only [k131PoleScale]
  rw [show -((9 / 4 - Real.log u) / (16 / 27 : ℝ)) = -(27 / 16 : ℝ) * (9 / 4 - Real.log u) by ring]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (2 * j.val + 3))]

/-- Mellin inversion of the nine-pole combination gives exactly the
profile used by the principal Euler lower bound. -/
theorem k131_mellin_profile_eq {u : ℝ} (hu : 0 < u) :
    Analysis.inverseMellin k131MellinFn 0 u = (k131MellinProfile u : ℂ) := by
  rw [k131_mellin_inversion (by norm_num only) hu]
  simp only [k131_pole_transform _ hu, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
  apply congrArg Complex.ofReal
  unfold k131MellinProfile
  by_cases hl : Real.log u ≤ 9 / 4
  · rw [ite_eq_left ⟨hu, hl⟩]
    simp only [k131_scaled_profile _ hu hl, gaussianK131Inverse, Finset.mul_sum]
  · rw [ite_eq_right (fun h ↦ hl h.2)]
    have h₂ : 2 * (9 / 8 : ℝ) = 9 / 4 := by norm_num only
    simp only [Analysis.rationalPoleProfile, h₂, hu, hl, and_false, ite_false, mul_zero,
      Finset.sum_const_zero]

/-- On the forward support, the inverse Mellin profile divided by the
square root of the prime-power argument is the existing K131 Euler weight. -/
theorem k131_profile_forward_eq {y t : ℝ} (hy : 0 < y) (ht : 0 < t)
    (hu : t ≤ y ^ 2 * Real.exp (9 / 4)) :
    k131MellinProfile (t / y ^ 2) / Real.sqrt t = k131ForwardWeight y t := by
  have hpos := div_pos ht (pow_pos hy 2)
  have hlog :=
    (Real.log_le_iff_le_exp hpos).mpr
      ((div_le_iff₀ (pow_pos hy 2)).mpr (by simpa only [mul_comm] using hu))
  unfold k131MellinProfile k131ForwardWeight
  rw [ite_eq_left ⟨hpos, hlog⟩]
  dsimp only
  ring

private theorem k131_scale_nonneg (j : Fin 9) : 0 ≤ k131PoleScale j := by
  have hA : 0 ≤ (gaussianK131Amplitude : ℝ) := by
    rw [k131_amplitude_eq]
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
  have hB : ∀ i : Fin 9, 0 ≤ inverseCoeffs i := by decide +kernel
  exact
    mul_nonneg (mul_nonneg (mul_nonneg hA (Rat.cast_nonneg.mpr (hB j))) (Nat.cast_nonneg _))
      (pow_nonneg (by norm_num only) _)

private theorem k131_kernel_decay (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ s ∈ (k131Pole 0).region, η ≤ ‖s + 1 / 2‖ → ‖k131MellinFn s‖ ≤ C / (1 + ‖s‖ ^ 2) := by
  have h (j : Fin 9) := (k131Pole j).decay η hη
  choose C hC hbound using h
  let A := ∑ j : Fin 9, k131PoleScale j * C j
  have hA : 0 ≤ A := Finset.sum_nonneg (fun j _ ↦ mul_nonneg (k131_scale_nonneg j) (hC j).le)
  refine ⟨A + 1, add_pos_of_nonneg_of_pos hA zero_lt_one, fun s hs hηs ↦ ?_⟩
  have hd : 0 ≤ 1 + ‖s‖ ^ 2 := add_nonneg zero_le_one (sq_nonneg _)
  refine (norm_sum_le _ _).trans ?_
  have hsum :
    (∑ j : Fin 9, ‖(k131PoleScale j : ℂ) * (k131Pole j).function s‖) ≤
      ∑ j : Fin 9, (k131PoleScale j * C j) / (1 + ‖s‖ ^ 2) := by
    apply Finset.sum_le_sum
    intro j _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (k131_scale_nonneg j),
      mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (hbound j s hs hηs) (k131_scale_nonneg j)
  rw [← Finset.sum_div] at hsum
  exact hsum.trans (div_le_div_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hd)

private theorem differentiable_pole_sum {S : Set ℂ} (f : Fin 9 → ℂ → ℂ)
    (hf : ∀ j, DifferentiableOn ℂ (f j) S) (T : Finset (Fin 9)) :
    DifferentiableOn ℂ (fun s ↦ ∑ j ∈ T, (k131PoleScale j : ℂ) * f j s) S := by
  induction T using Finset.induction_on with
  | empty =>
    change DifferentiableOn ℂ (fun _ : ℂ ↦ (0 : ℂ)) S
    exact differentiableOn_const (0 : ℂ)
  | insert j T hj ih =>
    simp only [Finset.sum_insert hj]
    exact ((hf j).const_mul _).add ih

/-- The nine-pole K131 transform is an admissible Mellin kernel on
the common strip of its component kernels. -/
noncomputable def k131MellinKernel : LLS.PaperStatements.MellinKernel :=
  { k131Pole 0 with
    function := k131MellinFn
    holomorphic := by
      unfold k131MellinFn
      exact
        differentiable_pole_sum (fun j ↦ (k131Pole j).function) (fun j ↦ (k131Pole j).holomorphic) _
    regularized := fun s ↦ ∑ j : Fin 9, (k131PoleScale j : ℂ) * (k131Pole j).regularized s
    regularized_holomorphic := by
      exact
        differentiable_pole_sum (fun j ↦ (k131Pole j).regularized)
          (fun j ↦ (k131Pole j).regularized_holomorphic) _
    regularized_eq := by
      intro s hs hne
      unfold k131MellinFn
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [(k131Pole j).regularized_eq s hs hne]
      ring
    decay := k131_kernel_decay
    mellin_integrable := by
      intro σ u hσ hδ hu
      unfold k131MellinFn
      simp only [Finset.sum_mul, mul_assoc]
      exact
        MeasureTheory.integrable_finsetSum Finset.univ
          (fun j _ ↦ ((k131Pole j).mellin_integrable σ u hσ hδ hu).const_mul _)
    mellin_eq := by
      intro σ u hσ _ hu
      have hs : 0 < σ + (2 * (8 / 27 : ℝ))⁻¹ := by
        have he : (2 * (8 / 27 : ℝ))⁻¹ = 27 / 16 := by norm_num only
        rw [he]
        linarith only [hσ]
      rw [k131_mellin_inversion hs hu, k131_mellin_inversion (by norm_num only) hu]
    mellin_nonneg := by
      intro u hu
      rw [k131_mellin_profile_eq hu, Complex.ofReal_re]
      unfold k131MellinProfile
      split
      · rename_i h
        have hA : 0 ≤ (gaussianK131Amplitude : ℝ) := by
          rw [k131_amplitude_eq]
          norm_num only [Rat.cast_div, Rat.cast_ofNat]
        exact mul_nonneg (mul_nonneg hA (Real.exp_pos _).le) (inverse_nonneg (sub_nonneg.mpr h.2))
      · exact le_rfl
    mellin_nonzero := by
      let u := Real.exp (5 / 4)
      have hu : 0 < u := Real.exp_pos _
      refine ⟨u, hu, ?_⟩
      rw [k131_mellin_profile_eq hu, Complex.ofReal_re]
      have hl : Real.log u = 5 / 4 := Real.log_exp _
      have hB : 0 < gaussianK131Inverse 1 := by
        unfold gaussianK131Inverse
        simp only [one_pow, mul_one, ← Rat.cast_sum]
        exact Rat.cast_pos.mpr (by decide +kernel)
      have hA : 0 < (gaussianK131Amplitude : ℝ) := Rat.cast_pos.mpr (by decide +kernel)
      unfold k131MellinProfile
      rw [ite_eq_left
          ⟨hu, by
            rw [hl]; norm_num only⟩,
        hl, show (9 / 4 : ℝ) - 5 / 4 = 1 by norm_num only]
      exact (mul_pos (mul_pos hA (Real.exp_pos _)) hB).ne'
    mellin_real := by
      intro u hu
      rw [k131_mellin_profile_eq hu, Complex.ofReal_im] }

/-- The explicit-formula kernel summand is the supported Euler weight
times the character and the Mangoldt coefficient. -/
theorem k131_kernel_summand_eq {y : ℝ} (hy : 0 < y) {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) :
    k131MellinKernel.summand χ (y ^ 2) n =
      if (n : ℝ) ≤ y ^ 2 * Real.exp (9 / 4) then
        (k131ForwardWeight y n * ArithmeticFunction.vonMangoldt n : ℝ) * χ n
      else 0 := by
  unfold LLS.PaperStatements.MellinKernel.summand
  by_cases hn : n = 0
  · subst n
    simp only [ite_true, ArithmeticFunction.map_zero, mul_zero, Complex.ofReal_zero, zero_mul,
      ite_self]
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hp := div_pos hn' (pow_pos hy 2)
  rw [ite_eq_right hn]
  change _ * _ * Analysis.inverseMellin k131MellinFn 0 ((n : ℝ) / y ^ 2) = _
  rw [k131_mellin_profile_eq hp]
  by_cases h : (n : ℝ) ≤ y ^ 2 * Real.exp (9 / 4)
  · rw [ite_eq_left h, ← k131_profile_forward_eq hy hn' h]
    push_cast
    ring
  rw [ite_eq_right h]
  have hl : ¬Real.log ((n : ℝ) / y ^ 2) ≤ 9 / 4 := fun hl ↦
    h
      (by
        simpa only [mul_comm] using
          (div_le_iff₀ (pow_pos hy 2)).mp ((Real.log_le_iff_le_exp hp).mp hl))
  simp only [k131MellinProfile, hl, and_false, ite_false, Complex.ofReal_zero, mul_zero]

/-- Only indices inside the forward support contribute to the infinite
sum in the nonprincipal explicit formula. -/
theorem k131_kernel_tsum_eq {y : ℝ} (hy : 0 < y) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    (∑' n : ℕ, k131MellinKernel.summand χ (y ^ 2) n) =
      ∑ n ∈ Finset.Icc 0 ⌊y ^ 2 * Real.exp (9 / 4)⌋₊,
        (k131ForwardWeight y n * ArithmeticFunction.vonMangoldt n : ℝ) * χ n := by
  let u := y ^ 2 * Real.exp (9 / 4)
  have hu : 0 ≤ u := mul_nonneg (sq_nonneg y) (Real.exp_pos _).le
  rw [tsum_eq_sum (s := Finset.Icc 0 ⌊u⌋₊)]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [k131_kernel_summand_eq hy, ite_eq_left ((Nat.le_floor_iff hu).mp (Finset.mem_Icc.mp hn).2)]
  · intro n hn
    rw [k131_kernel_summand_eq hy, ite_eq_right]
    exact fun h ↦ hn (Finset.mem_Icc.mpr ⟨Nat.zero_le n, (Nat.le_floor_iff hu).mpr h⟩)

private theorem k131_zero_residue (F : ℂ → ℂ) (x : ℝ) :
    LLS.PaperStatements.MellinKernel.weightedResidue k131MellinKernel F x (-1 / 2) = 0 := by
  have h : k131MellinKernel.regularized (-1 / 2) = 0 := by
    change
      (∑ j : Fin 9,
          (k131PoleScale j : ℂ) * (((-1 / 2 : ℂ) + 1 / 2) * (k131Pole j).function (-1 / 2))) =
        0
    simp only [neg_div, neg_add_cancel, zero_mul, mul_zero, Finset.sum_const_zero]
  simp only [LLS.PaperStatements.MellinKernel.weightedResidue, h, zero_mul, mul_zero, ite_true]

private theorem k131_kernel_delta : k131MellinKernel.delta = 1 / 8 := by
  change min ((((2 * (8 / 27 : ℝ))⁻¹) - 1 / 2) / 4) (1 / 8) = 1 / 8
  rw [min_eq_right (by norm_num only)]

/-- The normalized left completed-L integral for K131. The line is in
the admissible strip and is left of all nontrivial zeros under GRH. -/
noncomputable def k131LeftIntegral {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  let s := fun t : ℝ ↦ (-9 / 16 : ℂ) + Complex.I * t
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ t : ℝ, -logDeriv χ.completedLFunction (s t + 1 / 2) * (k131MellinFn (s t) * (x : ℂ) ^ (s t))

/-- The normalized gamma integral for K131 on the central line. -/
noncomputable def k131GammaIntegral {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ t : ℝ,
      logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
        (k131MellinFn (Complex.I * t) * (x : ℂ) ^ (Complex.I * t))

/-- For primitive nonprincipal characters under GRH, the finite K131
Euler sum has the exact oscillatory-zero, left-line and gamma decomposition. -/
theorem k131_euler_explicit {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {y : ℝ} (hy : 1 ≤ y) :
    (∑ n ∈ Finset.Icc 0 ⌊y ^ 2 * Real.exp (9 / 4)⌋₊,
        (k131ForwardWeight y n * ArithmeticFunction.vonMangoldt n : ℝ) * χ n) =
      -(∑' ρ : ℂ, k131MellinKernel.oscillatingZeroTerm χ (y ^ 2) ρ) + k131LeftIntegral χ (y ^ 2) +
        k131GammaIntegral χ (y ^ 2) := by
  have hx : 1 ≤ y ^ 2 := by
    simpa only [one_pow] using pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 from zero_le_one) hy 2
  have ha : -1 / 2 - k131MellinKernel.delta < (-9 / 16 : ℝ) := by
    rw [k131_kernel_delta]
    norm_num only
  have hb : (9 / 16 : ℝ) ≤ 1 / 2 + k131MellinKernel.delta := by
    rw [k131_kernel_delta]
    norm_num only
  have he :=
    LLS.PaperStatements.MellinKernel.tsum_summand_eq_completed_residue_formula k131MellinKernel hq
      hGRH hp hne hinv (a := -9 / 16) (b := 9 / 16) (by norm_num only) ha hb (by norm_num only)
      (by norm_num only) hx (by norm_num only) (by norm_num only)
  dsimp only at he
  rw [k131_zero_residue, k131_kernel_tsum_eq (zero_lt_one.trans_le hy)] at he
  rw [LLS.PaperStatements.MellinKernel.gammaIntegral_eq_central k131MellinKernel χ (b := 9 / 16)
      (by norm_num only) hb (by norm_num only) hx] at he
  rw [show k131MellinKernel.function = k131MellinFn from rfl] at he
  simpa only [zero_sub, k131LeftIntegral, k131GammaIntegral, Complex.ofReal_div, Complex.ofReal_neg,
    Complex.ofReal_ofNat] using he

/-- The real trace summand has the same sign convention as the principal
Euler lower bound. This is the real form of the nonprincipal identity. -/
theorem k131_euler_real_explicit {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {y : ℝ} (hy : 1 ≤ y) :
    (∑ n ∈ Finset.Icc 0 ⌊y ^ 2 * Real.exp (9 / 4)⌋₊,
        (χ n).re * (k131ForwardWeight y n * ArithmeticFunction.vonMangoldt n)) =
      -(∑' ρ : ℂ, k131MellinKernel.oscillatingZeroTerm χ (y ^ 2) ρ).re +
        (k131LeftIntegral χ (y ^ 2)).re +
        (k131GammaIntegral χ (y ^ 2)).re := by
  have he := congrArg Complex.re (k131_euler_explicit hq hGRH hp hne hinv hy)
  simp only [Complex.re_sum, Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at he
  simpa only [mul_comm ((χ _).re)] using he

/-- The completed inverse-character integral on the reflected vertical
line, with the K131 weight on the original left line. -/
noncomputable def k131ReflectedIntegral {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) :
    ℂ :=
  let s := fun t : ℝ ↦ (-9 / 16 : ℂ) + Complex.I * t
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ t : ℝ,
      logDeriv χ⁻¹.completedLFunction (((17 / 16 : ℝ) : ℂ) - Complex.I * t) *
        (k131MellinFn (s t) * (x : ℂ) ^ (s t))

private theorem k131_left_weight_integral {x : ℝ} (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          k131MellinFn ((-9 / 16 : ℂ) + Complex.I * t) *
            (x : ℂ) ^ ((-9 / 16 : ℂ) + Complex.I * t)) =
      (k131MellinProfile x⁻¹ : ℂ) := by
  have h₁ := k131_mellin_inversion (σ := -9 / 16) (by norm_num only) (inv_pos.mpr hx)
  have h₂ := k131_mellin_inversion (σ := 0) (by norm_num only) (inv_pos.mpr hx)
  rw [← h₂, k131_mellin_profile_eq (inv_pos.mpr hx)] at h₁
  simpa only [Analysis.inverseMellin, Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg hx.le,
    Complex.cpow_neg, inv_inv, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat] using
    h₁

/-- Reflection of the completed logarithmic derivative extracts the
conductor term with its exact K131 inverse-transform coefficient. -/
theorem k131_left_eq_reflected {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) :
    k131LeftIntegral χ x =
      Complex.log q * (k131MellinProfile x⁻¹ : ℂ) + k131ReflectedIntegral χ x := by
  let s := fun t : ℝ ↦ (-9 / 16 : ℂ) + Complex.I * t
  let W := fun t : ℝ ↦ k131MellinFn (s t) * (x : ℂ) ^ (s t)
  let F := fun t : ℝ ↦ -logDeriv χ.completedLFunction (s t + 1 / 2) * W t
  let C := fun t : ℝ ↦ Complex.log q * W t
  let R := fun t : ℝ ↦ logDeriv χ⁻¹.completedLFunction (((17 / 16 : ℝ) : ℂ) - Complex.I * t) * W t
  have ha : -1 / 2 - k131MellinKernel.delta < (-9 / 16 : ℝ) := by
    rw [k131_kernel_delta]
    norm_num only
  have hb : (-9 / 16 : ℝ) ≤ 1 / 2 + k131MellinKernel.delta := by
    rw [k131_kernel_delta]
    norm_num only
  have he (t : ℝ) : F t = C t + R t := by
    unfold F C R s
    have h := LLS.PaperStatements.triangular18_completed_left_reflection hp hne hinv t
    simp only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat] at h
    simp only [Complex.ofReal_div, Complex.ofReal_ofNat]
    rw [h, add_mul]
  have hF : MeasureTheory.Integrable F := by
    have h :=
      LLS.PaperStatements.MellinKernel.integrable_completed_left_line k131MellinKernel hp hne hinv
        ha (by norm_num only) (by norm_num only) hx
    rw [show k131MellinKernel.function = k131MellinFn from rfl] at h
    simpa only [F, W, s, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat] using h
  have hW : MeasureTheory.Integrable W := by
    have h :=
      LLS.PaperStatements.MellinKernel.integrable_logWeighted_power_line k131MellinKernel (c :=
        -9 / 16) (F := fun _ : ℝ ↦ (1 : ℂ)) (A := 1) ha hb (by norm_num only) hx
        continuous_const.aestronglyMeasurable
        (fun t ↦ by
          simp only [norm_one, one_mul, le_add_iff_nonneg_left]
          exact Real.log_nonneg (by linarith only [abs_nonneg t]))
    rw [show k131MellinKernel.function = k131MellinFn from rfl] at h
    simpa only [W, s, one_mul, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat] using h
  have hC : MeasureTheory.Integrable C := hW.const_mul _
  have hR : MeasureTheory.Integrable R :=
    (hF.sub hC).congr
      (Filter.Eventually.of_forall (fun t ↦ by rw [Pi.sub_apply, he, add_sub_cancel_left]))
  have hsum : (∫ t : ℝ, F t) = (∫ t : ℝ, C t) + ∫ t : ℝ, R t := by
    rw [← MeasureTheory.integral_add hC hR]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall he)
  change ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, F t) = _
  rw [hsum, mul_add]
  have hi :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, C t) =
      Complex.log q * (k131MellinProfile x⁻¹ : ℂ) := by
    unfold C
    rw [MeasureTheory.integral_const_mul, mul_left_comm]
    congr 1
    exact k131_left_weight_integral hx
  rw [hi]
  rfl

/-- At the squared radius, the inverse-transform conductor coefficient
is the manuscript's decay factor times the inverse polynomial. -/
theorem k131_conductor_profile {y : ℝ} (hy : 1 ≤ y) :
    k131MellinProfile (y ^ 2)⁻¹ =
      ((gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * (9 / 4))) * y ^ (-(27 / 8 : ℝ)) *
        gaussianK131Inverse (9 / 4 + 2 * Real.log y) := by
  have hy0 := zero_lt_one.trans_le hy
  have h : Real.log ((y ^ 2)⁻¹) = -(2 * Real.log y) := by
    rw [Real.log_inv, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  unfold k131MellinProfile
  rw [ite_eq_left
      ⟨inv_pos.mpr (pow_pos hy0 2), by
        rw [h]; linarith only [Real.log_nonneg hy]⟩,
    h]
  dsimp only
  rw [sub_neg_eq_add, Real.rpow_def_of_pos hy0]
  have he :
    -(27 / 16 : ℝ) * (9 / 4 + 2 * Real.log y) =
      -(27 / 16 : ℝ) * (9 / 4) + Real.log y * -(27 / 8 : ℝ) := by
    ring
  rw [he, Real.exp_add]
  ring

/-- The nonprincipal finite Euler sum has the reflected decomposition
with the exact conductor coefficient. -/
theorem k131_euler_reflected {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {y : ℝ} (hy : 1 ≤ y) :
    (∑ n ∈ Finset.Icc 0 ⌊y ^ 2 * Real.exp (9 / 4)⌋₊,
        (χ n).re * (k131ForwardWeight y n * ArithmeticFunction.vonMangoldt n)) =
      -(∑' ρ : ℂ, k131MellinKernel.oscillatingZeroTerm χ (y ^ 2) ρ).re +
        (Complex.log q * (k131MellinProfile (y ^ 2)⁻¹ : ℂ)).re +
        (k131ReflectedIntegral χ (y ^ 2)).re +
        (k131GammaIntegral χ (y ^ 2)).re := by
  rw [k131_euler_real_explicit hq hGRH hp hne hinv hy,
    k131_left_eq_reflected hp hne hinv (pow_pos (zero_lt_one.trans_le hy) 2), Complex.add_re]
  ring

/-- The K131 kernel times the Mellin scale factor on its left contour. -/
noncomputable def k131LeftWeight (x t : ℝ) : ℂ :=
  let s := ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
  k131MellinFn s * (x : ℂ) ^ s

private theorem k131_left_weight_int {x : ℝ} (hx : 0 < x) :
    MeasureTheory.Integrable (k131LeftWeight x) := by
  have h :=
    LLS.PaperStatements.MellinKernel.integrable_inverse_in_strip k131MellinKernel (c := -9 / 16)
      (u := x⁻¹)
      (by
        rw [k131_kernel_delta]; norm_num only)
      (by
        rw [k131_kernel_delta]; norm_num only)
      (by norm_num only) (inv_pos.mpr hx)
  rw [show k131MellinKernel.function = k131MellinFn from rfl] at h
  unfold k131LeftWeight
  simpa only [Complex.ofReal_inv, Complex.cpow_neg, Complex.inv_cpow_ofReal_nonneg hx.le,
    inv_inv] using h

private theorem k131_dual_term_integral (f : ℕ → ℂ) {x : ℝ} (hx : 0 < x) (n : ℕ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          LSeries.term f (((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)) n * k131LeftWeight x t) =
      (f n / (n : ℂ) ^ (1 / 2 : ℂ)) * (k131MellinProfile (((n : ℝ) * x)⁻¹) : ℂ) := by
  by_cases hn : n = 0
  · subst n
    simp only [Nat.cast_zero]
    rw [show (0 : ℂ) ^ (1 / 2 : ℂ) = 0 from Complex.zero_cpow (by norm_num only)]
    simp only [LSeries.term_zero, zero_mul, MeasureTheory.integral_zero, mul_zero, div_zero]
  have he (t : ℝ) :
    LSeries.term f (((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)) n * k131LeftWeight x t =
      (f n / (n : ℂ) ^ (1 / 2 : ℂ)) * k131LeftWeight ((n : ℝ) * x) t := by
    let s : ℂ := ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    have hs : (((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)) = 1 / 2 - s := by
      unfold s
      push_cast
      ring
    change
      LSeries.term f _ n * (k131MellinFn s * (x : ℂ) ^ s) =
        (f n / (n : ℂ) ^ (1 / 2 : ℂ)) * (k131MellinFn s * (((n : ℝ) * x : ℝ) : ℂ) ^ s)
    rw [hs, ← mul_left_comm, LLS.PaperStatements.reflected_term_factor f hn hx]
    ring
  rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ he),
    MeasureTheory.integral_const_mul, mul_left_comm]
  have h := k131_left_weight_integral (mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) hx)
  simp only [Complex.ofReal_div] at h
  simp only [k131LeftWeight, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat]
  rw [h]

/-- The reflected Euler integral is the inverted K131 profile evaluated
at the inverse of each scale-times-index, with the exact Dirichlet coefficient. -/
theorem k131_dual_euler_eq {f : ℕ → ℂ} {x : ℝ} (hx : 0 < x)
    (hs : LSeriesSummable f (((17 / 16 : ℝ) : ℂ))) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ, LSeries f (((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)) * k131LeftWeight x t) =
      ∑' n : ℕ, (f n / (n : ℂ) ^ (1 / 2 : ℂ)) * (k131MellinProfile (((n : ℝ) * x)⁻¹) : ℂ) := by
  rw [AnalyticNumberTheory.General.integral_LSeries_mul_weight_eq_tsum hs (fun t : ℝ ↦ -t)
      (k131LeftWeight x) continuous_neg (k131_left_weight_int hx),
    ← tsum_mul_left]
  exact tsum_congr (k131_dual_term_integral f hx)

/-- Gamma contribution on the reflected line, oriented as the inverse
character in the completed functional equation. -/
noncomputable def k131ReflectedGamma {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ t : ℝ,
      logDeriv χ⁻¹.gammaFactor (((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)) * k131LeftWeight x t

/-- The reflected completed integral is the reflected Gamma term minus
the Euler series of the inverse character, with exact inverted weights. -/
theorem k131_reflected_eq_dual {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) :
    k131ReflectedIntegral χ x =
      k131ReflectedGamma χ x -
        ∑' n : ℕ,
          ((χ⁻¹ n) * (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ (1 / 2 : ℂ)) *
            (k131MellinProfile (((n : ℝ) * x)⁻¹) : ℂ) := by
  let f := (fun n : ℕ ↦ χ⁻¹ n) * (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ))
  let s := fun t : ℝ ↦ (((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ))
  let W := k131LeftWeight x
  let F := fun t ↦ logDeriv χ⁻¹.completedLFunction (s t) * W t
  let E := fun t ↦ LSeries f (s t) * W t
  let G := fun t ↦ logDeriv χ⁻¹.gammaFactor (s t) * W t
  have hs :=
    χ⁻¹.LSeriesSummable_twist_vonMangoldt
      (show 1 < (((17 / 16 : ℝ) : ℂ)).re by norm_num only [Complex.ofReal_re])
  have hW : MeasureTheory.Integrable W := k131_left_weight_int hx
  have hE : MeasureTheory.Integrable E := by
    have h :=
      Analysis.integrable_tsum_of_summable_integral_norm (fun n t ↦ LSeries.term f (s t) n * W t)
        (fun n ↦
          AnalyticNumberTheory.General.integrable_LSeries_term_mul_weight f (17 / 16) n
            (fun t : ℝ ↦ -t) continuous_neg W hW)
        (AnalyticNumberTheory.General.summable_integral_norm_LSeries_term_mul_weight hs
          (fun t : ℝ ↦ -t) W)
    exact
      h.congr
        (MeasureTheory.ae_of_all _
          (fun t ↦ by
            change (∑' n, LSeries.term f (s t) n * W t) = (∑' n, LSeries.term f (s t) n) * W t
            exact tsum_mul_right))
  have hF : MeasureTheory.Integrable F := by
    have ha : -1 / 2 - k131MellinKernel.delta < (-9 / 16 : ℝ) := by
      rw [k131_kernel_delta]
      norm_num only
    have h :=
      LLS.PaperStatements.MellinKernel.integrable_completed_left_line k131MellinKernel hp hne hinv
        ha (by norm_num only) (by norm_num only) hx
    rw [show k131MellinKernel.function = k131MellinFn from rfl] at h
    refine (h.sub (hW.const_mul (Complex.log q))).congr (MeasureTheory.ae_of_all _ ?_)
    intro t
    dsimp only [W, k131LeftWeight, F, s, Pi.sub_apply]
    rw [LLS.PaperStatements.triangular18_completed_left_reflection hp hne hinv, add_mul,
      add_sub_cancel_left]
    simp only [Complex.ofReal_neg, mul_neg, sub_eq_add_neg]
  have he (t : ℝ) : F t + E t = G t := by
    have ht : 1 < (s t).re := by
      unfold s
      norm_num only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
    have hd :=
      LLS.PaperStatements.MellinKernel.arithmetic_logDeriv_eq_completed_add_gamma hinv ht.le (W t)
    have hh : LSeries f (s t) = -logDeriv χ⁻¹.LFunction (s t) := by
      simpa only [f, Pi.mul_def, logDeriv, Pi.div_apply, neg_div] using
        AnalyticNumberTheory.DirichletLFunction.LSeries_mangoldt_eq_neg_logDeriv χ⁻¹ ht
    unfold F E G
    rw [hh]
    linear_combination hd
  have hG : MeasureTheory.Integrable G := (hF.add hE).congr (MeasureTheory.ae_of_all _ he)
  have hI : (∫ t : ℝ, F t) = (∫ t : ℝ, G t) - ∫ t : ℝ, E t := by
    rw [← MeasureTheory.integral_sub hG hE]
    exact
      MeasureTheory.integral_congr_ae
        (MeasureTheory.ae_of_all _
          (fun t ↦ by
            change F t = G t - E t
            rw [← he]
            ring))
  have hseries := k131_dual_euler_eq hx hs
  have hF' : k131ReflectedIntegral χ x = ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, F t := by
    unfold k131ReflectedIntegral F s W k131LeftWeight
    simp only [mul_neg, sub_eq_add_neg, Complex.ofReal_neg, Complex.ofReal_div,
      Complex.ofReal_ofNat]
  rw [hF', hI, mul_sub]
  change _ - (((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, LSeries f (s t) * k131LeftWeight x t) = _
  rw [hseries]
  rfl

/-- Each reflected Euler weight separates into the conductor decay,
the index power with exponent -35/16, and the shifted inverse polynomial. -/
theorem k131_dual_profile_eq {x t : ℝ} (hx : 1 ≤ x) (ht : 1 ≤ t) :
    let z := 9 / 4 + Real.log x
    k131MellinProfile (t * x)⁻¹ / Real.sqrt t =
      ((gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * z)) * t ^ (-(35 / 16 : ℝ)) *
        gaussianK131Inverse (z + Real.log t) := by
  intro z
  have hx0 := zero_lt_one.trans_le hx
  have ht0 := zero_lt_one.trans_le ht
  have htx := mul_pos ht0 hx0
  have hl : Real.log ((t * x)⁻¹) = -(Real.log t + Real.log x) := by
    rw [Real.log_inv, Real.log_mul ht0.ne' hx0.ne']
  unfold k131MellinProfile
  rw [ite_eq_left
      ⟨inv_pos.mpr htx, by
        rw [hl]
        linarith only [Real.log_nonneg hx, Real.log_nonneg ht]⟩,
    hl]
  dsimp only
  have hz : 9 / 4 - -(Real.log t + Real.log x) = z + Real.log t := by
    dsimp only [z]; ring
  rw [hz, mul_add, Real.exp_add, Real.sqrt_eq_rpow, Real.rpow_def_of_pos ht0,
    Real.rpow_def_of_pos ht0]
  have he :
    Real.exp (-(35 / 16 : ℝ) * Real.log t) =
      Real.exp (-(27 / 16 : ℝ) * Real.log t) / Real.exp (Real.log t * (1 / 2 : ℝ)) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [show Real.log t * -(35 / 16 : ℝ) = -(35 / 16 : ℝ) * Real.log t by ring, he]
  ring

private theorem inverse_coeff_nonneg_kernel (j : Fin 9) : 0 ≤ (inverseCoeffs j : ℝ) :=
  Rat.cast_nonneg.mpr ((show ∀ i : Fin 9, 0 ≤ inverseCoeffs i by decide +kernel) j)

/-- The inverse polynomial grows on nonnegative arguments, and for
coordinates at least 16 its translated value grows by at most degree 19. -/
theorem k131_inverse_shift_bounds {z v : ℝ} (hz : 16 ≤ z) (hv : 0 ≤ v) :
    gaussianK131Inverse z ≤ gaussianK131Inverse (z + v) ∧
      gaussianK131Inverse (z + v) ≤ (1 + v / 16) ^ 19 * gaussianK131Inverse z := by
  have hz0 : 0 < z := (by norm_num only : (0 : ℝ) < 16).trans_le hz
  unfold gaussianK131Inverse
  constructor
  · exact
      Finset.sum_le_sum
        (fun j _ ↦
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz0.le (le_add_of_nonneg_right hv) _)
            (inverse_coeff_nonneg_kernel j))
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  let n := 2 * j.val + 3
  have hn : n ≤ 19 := Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.le_of_lt_succ j.isLt)) 3
  have h₁ : 1 ≤ 1 + v / 16 := le_add_of_nonneg_right (div_nonneg hv (by norm_num only))
  have hbase : z + v ≤ z * (1 + v / 16) := by
    have hh := mul_le_mul_of_nonneg_right hz (div_nonneg hv (by norm_num only : (0 : ℝ) ≤ 16))
    linarith only [hh]
  have hpow : (z + v) ^ n ≤ z ^ n * (1 + v / 16) ^ 19 := by
    refine (pow_le_pow_left₀ (add_nonneg hz0.le hv) hbase n).trans ?_
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h₁ hn) (pow_nonneg hz0.le _)
  calc
    _ ≤ (inverseCoeffs j : ℝ) * (z ^ n * (1 + v / 16) ^ 19) :=
      mul_le_mul_of_nonneg_left hpow (inverse_coeff_nonneg_kernel j)
    _ = _ := by
      dsimp only [n]; ring

/-- Beyond log-height 14, the reflected polynomial envelope is
majorized by the exponential tangent at 14. -/
theorem k131_reflect_tangent {v : ℝ} (hv : 14 ≤ v) :
    (1 + v / 16) ^ 19 ≤ (30 / 16 : ℝ) ^ 19 * Real.exp ((19 / 30) * (v - 14)) := by
  have h := Real.add_one_le_exp ((v - 14) / 30)
  have he : 1 + v / 16 ≤ (30 / 16 : ℝ) * Real.exp ((v - 14) / 30) := by
    have h' := mul_le_mul_of_nonneg_left h (by norm_num only : (0 : ℝ) ≤ 30 / 16)
    linarith only [h']
  have he₀ : 0 ≤ 1 + v / 16 := by linarith only [hv]
  refine (pow_le_pow_left₀ he₀ he 19).trans_eq ?_
  rw [mul_pow, ← Real.exp_natCast_mul]
  norm_num only [Nat.cast_ofNat]
  congr 2
  ring

/-- For inverse coordinates at least 16 and indices beyond log-height 14,
the reflected kernel weight is bounded by a power with exponent -373/240. -/
theorem k131_dual_weight_tail {x t : ℝ} (hx : 1 ≤ x) (hz : 16 ≤ 9 / 4 + Real.log x) (ht : 1 ≤ t)
    (hl : 14 ≤ Real.log t) :
    let z := 9 / 4 + Real.log x
    k131MellinProfile (t * x)⁻¹ / Real.sqrt t ≤
      (gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * z) * gaussianK131Inverse z *
        ((30 / 16 : ℝ) ^ 19 * Real.exp (-(19 / 30 : ℝ) * 14)) *
        t ^ (-(373 / 240 : ℝ)) := by
  intro z
  have ht0 := zero_lt_one.trans_le ht
  have hA : 0 ≤ (gaussianK131Amplitude : ℝ) := Rat.cast_nonneg.mpr (by decide +kernel)
  have hB : 0 ≤ gaussianK131Inverse z := by
    unfold gaussianK131Inverse
    exact
      Finset.sum_nonneg
        (fun j _ ↦
          mul_nonneg (inverse_coeff_nonneg_kernel j)
            (pow_nonneg ((by norm_num only : (0 : ℝ) ≤ 16).trans hz) _))
  rw [k131_dual_profile_eq hx ht]
  have h :=
    (k131_inverse_shift_bounds hz (Real.log_nonneg ht)).2.trans
      (mul_le_mul_of_nonneg_right (k131_reflect_tangent hl) hB)
  refine
    (mul_le_mul_of_nonneg_left h
          (mul_nonneg (mul_nonneg hA (Real.exp_pos _).le) (Real.rpow_nonneg ht0.le _))).trans_eq
      ?_
  rw [Real.rpow_def_of_pos ht0, Real.rpow_def_of_pos ht0]
  have he :
    Real.exp (Real.log t * -(35 / 16 : ℝ)) * Real.exp ((19 / 30 : ℝ) * (Real.log t - 14)) =
      Real.exp (-(19 / 30 : ℝ) * 14) * Real.exp (Real.log t * -(373 / 240 : ℝ)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  linear_combination
    (gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * z) * gaussianK131Inverse z *
      (30 / 16 : ℝ) ^ 19 *
      he

/-- Above log-height 14, the Mangoldt logarithm is bounded by the
power envelope tangent to the logarithm at that height. -/
theorem k131_tail_log_le {t : ℝ} (ht : 0 < t) :
    Real.log t ≤ 14 * Real.exp (-1) * t ^ (1 / 14 : ℝ) := by
  have h := Real.add_one_le_exp (Real.log t / 14 - 1)
  rw [Real.rpow_def_of_pos ht, mul_assoc, ← Real.exp_add]
  rw [show (-1 : ℝ) + Real.log t * (1 / 14) = Real.log t / 14 - 1 by ring]
  linarith only [h]

/-- The Mangoldt-weighted reflected Euler tail has a summable power
majorant with exponent -2491/1680. -/
theorem k131_dual_mangoldt_tail {x : ℝ} {n : ℕ} (hx : 1 ≤ x) (hz : 16 ≤ 9 / 4 + Real.log x)
    (hn : 1 ≤ n) (hl : 14 ≤ Real.log (n : ℝ)) :
    let z := 9 / 4 + Real.log x
    ArithmeticFunction.vonMangoldt n * (k131MellinProfile ((n : ℝ) * x)⁻¹ / Real.sqrt n) ≤
      (gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * z) * gaussianK131Inverse z *
        ((30 / 16 : ℝ) ^ 19 * Real.exp (-(19 / 30 : ℝ) * 14)) *
        (14 * Real.exp (-1)) *
        (n : ℝ) ^ (-(2491 / 1680 : ℝ)) := by
  intro z
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos := zero_lt_one.trans_le hn'
  let C :=
    (gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * z) * gaussianK131Inverse z *
      ((30 / 16 : ℝ) ^ 19 * Real.exp (-(19 / 30 : ℝ) * 14))
  have hB : 0 ≤ gaussianK131Inverse z := by
    unfold gaussianK131Inverse
    exact
      Finset.sum_nonneg
        (fun j _ ↦
          mul_nonneg (inverse_coeff_nonneg_kernel j)
            (pow_nonneg ((by norm_num only : (0 : ℝ) ≤ 16).trans hz) _))
  have hA : 0 ≤ (gaussianK131Amplitude : ℝ) := Rat.cast_nonneg.mpr (by decide +kernel)
  have hC : 0 ≤ C := by
    dsimp only [C]; positivity
  have hlog := ArithmeticFunction.vonMangoldt_le_log.trans (k131_tail_log_le hpos)
  calc
    _ ≤ ArithmeticFunction.vonMangoldt n * (C * (n : ℝ) ^ (-(373 / 240 : ℝ))) :=
      mul_le_mul_of_nonneg_left (k131_dual_weight_tail hx hz hn' hl)
        ArithmeticFunction.vonMangoldt_nonneg
    _ ≤ (14 * Real.exp (-1) * (n : ℝ) ^ (1 / 14 : ℝ)) * (C * (n : ℝ) ^ (-(373 / 240 : ℝ))) :=
      mul_le_mul_of_nonneg_right hlog (mul_nonneg hC (Real.rpow_nonneg hpos.le _))
    _ = _ := by
      change _ = C * (14 * Real.exp (-1)) * _
      rw [show (-(2491 / 1680 : ℝ)) = 1 / 14 - 373 / 240 by norm_num only, sub_eq_add_neg,
        Real.rpow_add hpos]
      ring

/-- Integrating the decreasing power majorant bounds its entire discrete
tail after any positive integer cutoff. -/
theorem k131_tsum_tail_power {N : ℕ} (hN : 0 < N) :
    (∑' n : ℕ, ((n + N + 1 : ℕ) : ℝ) ^ (-(2491 / 1680 : ℝ))) ≤
      (N : ℝ) ^ (-(811 / 1680 : ℝ)) / (811 / 1680) := by
  have hp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have ha : (-(2491 / 1680 : ℝ)) < -1 := by norm_num only
  calc
    _ ≤ ∫ t : ℝ in Set.Ioi (N : ℝ), t ^ (-(2491 / 1680 : ℝ)) :=
      AntitoneOn.tsum_comp_add_le_integral N
        ((Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (ha.le.trans (by norm_num only))).mono
          (fun _ ht ↦ hp.trans_le ht))
        (integrableOn_Ioi_rpow_of_lt ha hp) (fun t ht ↦ Real.rpow_nonneg (hp.trans ht).le _)
    _ = _ := by
      rw [integral_Ioi_rpow_of_lt ha hp,
        show (-(2491 / 1680 : ℝ)) + 1 = -(811 / 1680) by norm_num only, div_neg, neg_div, neg_neg]

private theorem k131_reflect_tail_constant :
    (30 / 16 : ℝ) ^ 19 * (14 / (811 / 1680)) * Real.exp (-(133 / 8 : ℝ)) < 1 / 3 := by
  have h₁ : (2718 / 1000 : ℝ) ≤ Real.exp 1 := by linarith only [Real.exp_one_gt_d9]
  have h₂ : (13 / 8 : ℝ) ≤ Real.exp (5 / 8) := by linarith only [Real.add_one_le_exp (5 / 8)]
  have h₃ : (2718 / 1000 : ℝ) ^ 16 * (13 / 8) ≤ Real.exp (133 / 8) := by
    have h :=
      mul_le_mul (pow_le_pow_left₀ (by norm_num only) h₁ 16) h₂ (by norm_num only)
        (pow_nonneg (Real.exp_pos 1).le _)
    rw [← Real.exp_natCast_mul, ← Real.exp_add] at h
    convert h using 2
    norm_num only [Nat.cast_ofNat]
  rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_iff₀ (Real.exp_pos _)]
  exact
    (by norm_num only :
          (30 / 16 : ℝ) ^ 19 * (14 / (811 / 1680)) <
            1 / 3 * ((2718 / 1000 : ℝ) ^ 16 * (13 / 8))).trans_le
      (mul_le_mul_of_nonneg_left h₃ (by norm_num only))

/-- For an integer cutoff of log-height at least 14, the power series
majorant uses less than one third of the common reflected kernel factor. -/
theorem k131_reflect_tail_budget {N : ℕ} (hN : 0 < N) (hlog : 14 ≤ Real.log (N : ℝ)) :
    ((30 / 16 : ℝ) ^ 19 * Real.exp (-(19 / 30 : ℝ) * 14)) * (14 * Real.exp (-1)) *
        (∑' n : ℕ, ((n + N + 1 : ℕ) : ℝ) ^ (-(2491 / 1680 : ℝ))) <
      1 / 3 := by
  have h := k131_tsum_tail_power hN
  rw [Real.rpow_def_of_pos (Nat.cast_pos.mpr hN)] at h
  have he :=
    Real.exp_le_exp.mpr
      (show Real.log (N : ℝ) * -(811 / 1680 : ℝ) ≤ 14 * -(811 / 1680 : ℝ) by linarith only [hlog])
  have hu := h.trans (div_le_div_of_nonneg_right he (by norm_num only))
  refine (mul_le_mul_of_nonneg_left hu (by positivity)).trans_lt ?_
  convert k131_reflect_tail_constant using 1
  have hsum : -(19 / 30 : ℝ) * 14 + -1 + 14 * -(811 / 1680 : ℝ) = -(133 / 8) := by norm_num only
  rw [← hsum, Real.exp_add, Real.exp_add]
  ring

/-- The prime-two contribution of the three characters exceeds the
normalized tail budget. -/
theorem k131_reflect_two_gt : (1 / 3 : ℝ) < 3 * Real.log 2 * (2 : ℝ) ^ (-(35 / 16 : ℝ)) := by
  have hs : Real.sqrt 2 < 3 / 2 := by
    have h := Real.sq_sqrt (by norm_num only : (0 : ℝ) ≤ 2)
    nlinarith only [h, sq_nonneg (Real.sqrt 2 - 3 / 2)]
  have hp : (1 / 6 : ℝ) < (2 : ℝ) ^ (-(5 / 2 : ℝ)) := by
    rw [show (-(5 / 2 : ℝ)) = -(2 + 1 / 2) by norm_num only, Real.rpow_neg (by norm_num only),
      Real.rpow_add (by norm_num only), Real.rpow_ofNat, ← Real.sqrt_eq_rpow, inv_eq_one_div]
    rw [lt_div_iff₀ (by positivity)]
    nlinarith only [hs]
  have hpow :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num only : (1 : ℝ) ≤ 2)
      (by norm_num only : (-(5 / 2 : ℝ)) ≤ -(35 / 16))
  have hlog : (2 : ℝ) ≤ 3 * Real.log 2 := by linarith only [Real.log_two_gt_d9]
  exact
    (show (1 / 3 : ℝ) < 2 * (2 : ℝ) ^ (-(35 / 16 : ℝ)) by linarith only [hp.trans_le hpow]).trans_le
      (mul_le_mul_of_nonneg_right hlog (Real.rpow_nonneg (by norm_num only) _))

private theorem k131_inverse_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ gaussianK131Inverse z := by
  unfold gaussianK131Inverse
  exact Finset.sum_nonneg (fun j _ ↦ mul_nonneg (inverse_coeff_nonneg_kernel j) (pow_nonneg hz _))

/-- The reflected Euler series is nonnegative when its coefficient at two
is three, its prefix coefficients are nonnegative, and its tail is at least minus one. -/
theorem k131_reflected_main_nonneg {x : ℝ} {N : ℕ} (hx : 1 ≤ x) (hz : 16 ≤ 9 / 4 + Real.log x)
    (hN : 2 ≤ N) (hlog : 14 ≤ Real.log (N : ℝ)) (a : ℕ → ℝ) (h₂ : a 2 = 3)
    (hpre : ∀ n ≤ N, ArithmeticFunction.vonMangoldt n ≠ 0 → 0 ≤ a n) (htail : ∀ n > N, -1 ≤ a n)
    (hs :
      Summable
        (fun n : ℕ ↦
          a n *
            (ArithmeticFunction.vonMangoldt n *
              (k131MellinProfile ((n : ℝ) * x)⁻¹ / Real.sqrt n)))) :
    0 ≤
      ∑' n : ℕ,
        a n *
          (ArithmeticFunction.vonMangoldt n *
            (k131MellinProfile ((n : ℝ) * x)⁻¹ / Real.sqrt n)) := by
  let z := 9 / 4 + Real.log x
  let B := (gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * z) * gaussianK131Inverse z
  let K := ((30 / 16 : ℝ) ^ 19 * Real.exp (-(19 / 30 : ℝ) * 14)) * (14 * Real.exp (-1))
  let P := fun n : ℕ ↦ (n : ℝ) ^ (-(2491 / 1680 : ℝ))
  let w := fun n : ℕ ↦
    ArithmeticFunction.vonMangoldt n * (k131MellinProfile ((n : ℝ) * x)⁻¹ / Real.sqrt n)
  let f := fun n ↦ a n * w n
  have hz₀ : 0 ≤ z := (by norm_num only : (0 : ℝ) ≤ 16).trans hz
  have hA : 0 ≤ (gaussianK131Amplitude : ℝ) := Rat.cast_nonneg.mpr (by decide +kernel)
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg hA (Real.exp_pos _).le) (k131_inverse_nonneg hz₀)
  have hw (n : ℕ) : 0 ≤ w n := by
    cases n with
    | zero => simp only [w, ArithmeticFunction.vonMangoldt.map_zero, zero_mul, le_refl]
    | succ n =>
      have hn : (1 : ℝ) ≤ (n.succ : ℕ) := by exact_mod_cast Nat.succ_pos n
      dsimp only [w]
      rw [k131_dual_profile_eq hx hn]
      exact
        mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
          (mul_nonneg
            (mul_nonneg (mul_nonneg hA (Real.exp_pos _).le) (Real.rpow_nonneg (by positivity) _))
            (k131_inverse_nonneg (add_nonneg hz₀ (Real.log_nonneg hn))))
  have hmain : B * (1 / 3) ≤ f 2 := by
    have hlog₂ := Real.log_nonneg (by norm_num only : (1 : ℝ) ≤ 2)
    have hb := (k131_inverse_shift_bounds hz hlog₂).1
    have hp : 0 ≤ (2 : ℝ) ^ (-(35 / 16 : ℝ)) := by positivity
    have h :=
      mul_le_mul_of_nonneg_left hb
        (show
          0 ≤
            3 * Real.log 2 *
              ((gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * z) *
                (2 : ℝ) ^ (-(35 / 16 : ℝ)))
          by positivity)
    dsimp only [f, w]
    rw [h₂, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two, Nat.cast_ofNat,
      k131_dual_profile_eq hx (by norm_num only)]
    exact
      (mul_le_mul_of_nonneg_left k131_reflect_two_gt.le hB).trans
        (by
          convert h using 1
          · dsimp only [B, z]
            ring
          · dsimp only [z]
            ring)
  have hprefix : B * (1 / 3) ≤ ∑ n ∈ Finset.range (N + 1), f n := by
    apply hmain.trans
    refine Finset.single_le_sum (fun n hn ↦ ?_) (Finset.mem_range.mpr (Nat.lt_succ_of_le hN))
    by_cases hm : ArithmeticFunction.vonMangoldt n = 0
    · simp only [f, w, hm, zero_mul, mul_zero, le_refl]
    · exact mul_nonneg (hpre n (Nat.le_of_lt_succ (Finset.mem_range.mp hn)) hm) (hw n)
  have hterm (n : ℕ) : -(B * K * P (n + (N + 1))) ≤ f (n + (N + 1)) := by
    let m := n + (N + 1)
    have hm : N < m := (Nat.lt_succ_self N).trans_le (Nat.le_add_left (N + 1) n)
    have hml : 14 ≤ Real.log (m : ℝ) :=
      hlog.trans
        (Real.log_le_log (Nat.cast_pos.mpr ((by decide : 0 < 2).trans_le hN))
          (Nat.cast_le.mpr hm.le))
    have h := k131_dual_mangoldt_tail hx hz ((by decide : 1 ≤ 2).trans (hN.trans hm.le)) hml
    have hw' : w m ≤ B * K * P m := by
      convert h using 1
      dsimp only [B, K, P]
      ring
    exact
      (neg_le_neg hw').trans
        (by simpa only [neg_one_mul] using mul_le_mul_of_nonneg_right (htail m hm) (hw m))
  have hP : Summable P := Real.summable_nat_rpow.mpr (by norm_num only)
  have hseries := ((summable_nat_add_iff (N + 1)).2 hP).mul_left (-(B * K))
  have htailSum :=
    hseries.tsum_le_tsum
      (fun n ↦ by
        rw [neg_mul]
        exact hterm n)
      ((summable_nat_add_iff (N + 1)).2 hs)
  rw [tsum_mul_left] at htailSum
  have hbudget : B * (K * ∑' n : ℕ, P (n + (N + 1))) ≤ B * (1 / 3) := by
    apply mul_le_mul_of_nonneg_left _ hB
    simpa only [K, P, ← Nat.add_assoc] using
      (k131_reflect_tail_budget ((by decide : 0 < 2).trans_le hN) hlog).le
  change Summable f at hs
  rw [← hs.sum_add_tsum_nat_add (N + 1)]
  nlinarith only [hprefix, htailSum, hbudget]

/-- Absolute convergence of the reflected K131 Euler coefficients follows
from the summable integrals of the Dirichlet terms on the reflected line. -/
theorem k131_dual_euler_summable {f : ℕ → ℂ} {x : ℝ} (hx : 0 < x)
    (hs : LSeriesSummable f (((17 / 16 : ℝ) : ℂ))) :
    Summable
      (fun n : ℕ ↦ (f n / (n : ℂ) ^ (1 / 2 : ℂ)) * (k131MellinProfile (((n : ℝ) * x)⁻¹) : ℂ)) := by
  let F := fun n t ↦
    LSeries.term f (((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)) n * k131LeftWeight x t
  have h :=
    AnalyticNumberTheory.General.summable_integral_norm_LSeries_term_mul_weight hs (fun t : ℝ ↦ -t)
      (k131LeftWeight x)
  have h' : Summable (fun n ↦ ‖∫ t : ℝ, F n t‖) :=
    h.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
      (fun _ ↦ MeasureTheory.norm_integral_le_integral_norm _)
  exact (h'.of_norm.mul_left (((1 / (2 * Real.pi)) : ℝ) : ℂ)).congr (k131_dual_term_integral f hx)

/-- Taking the real part of a reflected Euler coefficient gives its
real character value times the common Mangoldt weight. -/
theorem k131_dual_char_term_re {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) (n : ℕ) :
    (((χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) / (n : ℂ) ^ (1 / 2 : ℂ)) *
          (k131MellinProfile (((n : ℝ) * x)⁻¹) : ℂ)).re =
      (χ n).re *
        (ArithmeticFunction.vonMangoldt n * (k131MellinProfile ((n : ℝ) * x)⁻¹ / Real.sqrt n)) := by
  have hp : (n : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt n : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (Nat.cast_nonneg n)]
    push_cast
    norm_num only
  rw [hp, mul_div_assoc, ← Complex.ofReal_div, mul_assoc, ← Complex.ofReal_mul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  ring

/-- The sum of the three reflected Euler series has nonnegative real part
when the inverse characters have the joint prefix and tail bounds. -/
theorem k131_three_dual_nonneg {p q r N : ℕ} {x : ℝ} (hx : 1 ≤ x) (hz : 16 ≤ 9 / 4 + Real.log x)
    (hN : 2 ≤ N) (hlog : 14 ≤ Real.log (N : ℝ)) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r)
    (h₂ : (a 2).re + (b 2).re + (c 2).re = 3)
    (hp : ∀ n ≤ N, ArithmeticFunction.vonMangoldt n ≠ 0 → 0 ≤ (a n).re + (b n).re + (c n).re)
    (ht : ∀ n > N, -1 ≤ (a n).re + (b n).re + (c n).re) :
    0 ≤
      (∑' n : ℕ,
          ((a n + b n + c n) * (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ (1 / 2 : ℂ)) *
            (k131MellinProfile (((n : ℝ) * x)⁻¹) : ℂ)).re := by
  let E := fun {m : ℕ} (χ : DirichletCharacter ℂ m) (n : ℕ) ↦
    (χ n * (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ (1 / 2 : ℂ)) *
      (k131MellinProfile (((n : ℝ) * x)⁻¹) : ℂ)
  have hs {m : ℕ} (χ : DirichletCharacter ℂ m) : Summable (E χ) :=
    k131_dual_euler_summable (zero_lt_one.trans_le hx)
      (χ.LSeriesSummable_twist_vonMangoldt (by norm_num only [Complex.ofReal_re]))
  have h := ((hs a).add (hs b)).add (hs c)
  have he (n : ℕ) :
    (E a n + E b n + E c n).re =
      ((a n).re + (b n).re + (c n).re) *
        (ArithmeticFunction.vonMangoldt n * (k131MellinProfile ((n : ℝ) * x)⁻¹ / Real.sqrt n)) := by
    rw [Complex.add_re, Complex.add_re]
    dsimp only [E]
    rw [k131_dual_char_term_re, k131_dual_char_term_re, k131_dual_char_term_re]
    ring
  have heq (n : ℕ) :
    ((a n + b n + c n) * (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ (1 / 2 : ℂ)) *
        (k131MellinProfile (((n : ℝ) * x)⁻¹) : ℂ) =
      E a n + E b n + E c n := by
    simp only [E, add_mul, add_div]
  rw [tsum_congr heq, Complex.re_tsum h, tsum_congr he]
  exact k131_reflected_main_nonneg hx hz hN hlog _ h₂ hp ht ((Complex.reCLM.summable h).congr he)

/-- The reflected integral of three primitive characters is bounded by
its Gamma contribution under the joint inverse-character sign conditions. -/
theorem k131_three_reflected_le_gamma {p q r N : ℕ} [NeZero p] [NeZero q] [NeZero r] {x : ℝ}
    (hx : 1 ≤ x) (hz : 16 ≤ 9 / 4 + Real.log x) (hN : 2 ≤ N) (hlog : 14 ≤ Real.log (N : ℝ))
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ r}
    (ha : a.IsPrimitive) (hb : b.IsPrimitive) (hc : c.IsPrimitive) (ha₁ : a ≠ 1) (hb₁ : b ≠ 1)
    (hc₁ : c ≠ 1) (h₂ : (a⁻¹ 2).re + (b⁻¹ 2).re + (c⁻¹ 2).re = 3)
    (hp : ∀ n ≤ N, ArithmeticFunction.vonMangoldt n ≠ 0 → 0 ≤ (a⁻¹ n).re + (b⁻¹ n).re + (c⁻¹ n).re)
    (ht : ∀ n > N, -1 ≤ (a⁻¹ n).re + (b⁻¹ n).re + (c⁻¹ n).re) :
    (k131ReflectedIntegral a x + k131ReflectedIntegral b x + k131ReflectedIntegral c x).re ≤
      (k131ReflectedGamma a x + k131ReflectedGamma b x + k131ReflectedGamma c x).re := by
  have hx₀ := zero_lt_one.trans_le hx
  have hi {m : ℕ} {χ : DirichletCharacter ℂ m} (h : χ ≠ 1) : χ⁻¹ ≠ 1 := by
    intro he
    apply h
    simpa only [inv_inv, inv_one] using congrArg Inv.inv he
  rw [k131_reflected_eq_dual ha ha₁ (hi ha₁) hx₀, k131_reflected_eq_dual hb hb₁ (hi hb₁) hx₀,
    k131_reflected_eq_dual hc hc₁ (hi hc₁) hx₀]
  have hs {m : ℕ} (χ : DirichletCharacter ℂ m) :
    Summable
      (fun n : ℕ ↦
        (χ n * (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ (1 / 2 : ℂ)) *
          (k131MellinProfile (((n : ℝ) * x)⁻¹) : ℂ)) :=
    k131_dual_euler_summable hx₀
      (χ.LSeriesSummable_twist_vonMangoldt (by norm_num only [Complex.ofReal_re]))
  have h := k131_three_dual_nonneg hx hz hN hlog a⁻¹ b⁻¹ c⁻¹ h₂ hp ht
  simp only [add_mul, add_div] at h
  rw [((hs a⁻¹).add (hs b⁻¹)).tsum_add (hs c⁻¹), (hs a⁻¹).tsum_add (hs b⁻¹)] at h
  simp only [Complex.add_re, Complex.sub_re] at h ⊢
  linarith only [h]

/-- At the three odd pair levels, triviality at all primes through an
integer cutoff makes the reflected Euler contribution nonpositive in the
completed integral. Quadraticity identifies each inverse character. -/
theorem k131_pair_reflected_le_gamma {p q r N : ℕ} [NeZero p] [NeZero q] [NeZero r] (hp : Odd p)
    (hq : Odd q) (hr : Odd r) {x : ℝ} (hx : 1 ≤ x) (hz : 16 ≤ 9 / 4 + Real.log x) (hN : 2 ≤ N)
    (hlog : 14 ≤ Real.log (N : ℝ)) :
    let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
    let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
    a.IsPrimitive →
      b.IsPrimitive →
      c.IsPrimitive →
      a ≠ 1 →
      b ≠ 1 →
      c ≠ 1 →
      (∀ l : ℕ, l.Prime → (l : ℝ) ≤ N → a l = 1 ∧ b l = 1 ∧ c l = 1) →
      (k131ReflectedIntegral a x + k131ReflectedIntegral b x + k131ReflectedIntegral c x).re ≤
        (k131ReflectedGamma a x + k131ReflectedGamma b x + k131ReflectedGamma c x).re := by
  intro a b c ha hb hc ha₁ hb₁ hc₁ hsmall
  have haI : a⁻¹ = a := (NumberTheory.complexJacobiNumeratorCharacter_isQuadratic _ _).inv
  have hbI : b⁻¹ = b := (NumberTheory.complexJacobiNumeratorCharacter_isQuadratic _ _).inv
  have hcI : c⁻¹ = c := (NumberTheory.complexJacobiNumeratorCharacter_isQuadratic _ _).inv
  have htwo : a 2 = 1 ∧ b 2 = 1 ∧ c 2 = 1 := by
    simpa only [Nat.cast_ofNat] using hsmall 2 Nat.prime_two (by exact_mod_cast hN)
  have he {m n : ℕ} (χ : DirichletCharacter ℂ m) (hχ : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ N → χ l = 1)
    (hn : n ≤ N) (hm : ArithmeticFunction.vonMangoldt n ≠ 0) : χ n = 1 :=
    AnalyticNumberTheory.Arithmetic.character_eq_one_of_ambient_mangoldt (N := 1) χ
      (fun l hl hle _ ↦ hχ l hl hle) (Nat.cast_le.mpr hn) (Nat.coprime_one_right _) hm
  apply k131_three_reflected_le_gamma hx hz hN hlog ha hb hc ha₁ hb₁ hc₁
  · rw [haI, hbI, hcI, htwo.1, htwo.2.1, htwo.2.2]
    norm_num only [Complex.one_re]
  · intro n hn hm
    rw [haI, hbI, hcI, he a (fun l hl hle ↦ (hsmall l hl hle).1) hn hm,
      he b (fun l hl hle ↦ (hsmall l hl hle).2.1) hn hm,
      he c (fun l hl hle ↦ (hsmall l hl hle).2.2) hn hm]
    norm_num only [Complex.one_re]
  · intro n _
    rw [haI, hbI, hcI]
    simpa only [a, b, c, Int.cast_natCast] using
      pair_character_sum_ge_neg_one (n : ℤ) p q r (hp.mul hq) (hp.mul hr) (hq.mul hr)

/-- Throughout the K131 cell, the fixed reflected-Euler cutoff lies
above exp(14) and below the square of the bridge radius. -/
theorem k131_reflect_cutoff {L : ℝ} (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000) :
    14 ≤ Real.log 1250000 ∧
      (1250000 : ℝ) ≤ gaussianBridgeScale L ^ 2 ∧
      16 ≤ 9 / 4 + Real.log (gaussianBridgeScale L ^ 2) := by
  have hy := (gaussian_bridge_scale_mem hL).1
  have hy₀ : 0 < gaussianBridgeScale L :=
    (by norm_num only : (0 : ℝ) < 465644807 / 400000).trans_le hy
  have he : Real.exp 14 ≤ (1250000 : ℝ) := by
    rw [show (14 : ℝ) = (14 : ℕ) * 1 by norm_num only, Real.exp_natCast_mul]
    exact
      (pow_le_pow_left₀ (Real.exp_pos 1).le
            (show Real.exp 1 ≤ (2719 / 1000 : ℝ) by linarith only [Real.exp_one_lt_d9]) 14).trans
        (by norm_num only)
  refine ⟨(Real.le_log_iff_exp_le (by norm_num only)).2 he, ?_, ?_⟩
  · exact
      (by norm_num only : (1250000 : ℝ) ≤ (465644807 / 400000) ^ 2).trans
        (pow_le_pow_left₀ (by norm_num only) hy 2)
  rw [Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  have hlog := (k131_radius_log_mem hL).1
  change 14 ≤ 2 * Real.log (gaussianBridgeScale L) at hlog
  linarith only [hlog]

/-- At the K131 radius, prime triviality up to the full squared radius
gives the upper Gamma bound for the reflected integral of the three pair characters. -/
theorem k131_bridge_reflected_le_gamma {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r] (hp : Odd p)
    (hq : Odd q) (hr : Odd r) {L : ℝ} (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000) :
    let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
    let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
    let x := gaussianBridgeScale L ^ 2
    a.IsPrimitive →
      b.IsPrimitive →
      c.IsPrimitive →
      a ≠ 1 →
      b ≠ 1 →
      c ≠ 1 →
      (∀ l : ℕ, l.Prime → (l : ℝ) ≤ x → a l = 1 ∧ b l = 1 ∧ c l = 1) →
      (k131ReflectedIntegral a x + k131ReflectedIntegral b x + k131ReflectedIntegral c x).re ≤
        (k131ReflectedGamma a x + k131ReflectedGamma b x + k131ReflectedGamma c x).re := by
  intro a b c x ha hb hc ha₁ hb₁ hc₁ hsmall
  obtain ⟨hlog, hcut, hz⟩ := k131_reflect_cutoff hL
  have hx := (by norm_num only : (1 : ℝ) ≤ 1250000).trans hcut
  exact
    k131_pair_reflected_le_gamma hp hq hr hx hz (N := 1250000) (by decide)
      (by simpa only [Nat.cast_ofNat] using hlog) ha hb hc ha₁ hb₁ hc₁
      (fun l hl hle ↦ hsmall l hl (hle.trans hcut))

private theorem k131_left_weight_shift {x : ℝ} (hx : 0 < x) (u t : ℝ) :
    Complex.exp (Complex.I * (t : ℂ) * (u : ℂ)) * k131LeftWeight x t =
      (Real.exp ((9 / 16 : ℝ) * u) : ℂ) * k131LeftWeight (x * Real.exp u) t := by
  let s : ℂ := ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
  have hy := mul_pos hx (Real.exp_pos u)
  change _ * (k131MellinFn s * (x : ℂ) ^ s) = _ * (k131MellinFn s * ((x * Real.exp u : ℝ) : ℂ) ^ s)
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne'), ← Complex.ofReal_log hx.le, ←
    Complex.ofReal_log hy.le, Real.log_mul hx.ne' (Real.exp_pos u).ne', Real.log_exp,
    Complex.ofReal_add, Complex.ofReal_exp]
  rw [show
      ((Real.log x : ℂ) + (u : ℂ)) * s =
        (Real.log x : ℂ) * s + (Complex.I * (t : ℂ) * (u : ℂ) - ((9 / 16 : ℝ) * u : ℝ))
      by
      dsimp only [s]
      push_cast
      ring,
    Complex.exp_add, Complex.exp_sub]
  field_simp [Complex.exp_ne_zero]

private theorem k131_left_weight_continuous {x : ℝ} (hx : 0 < x) :
    Continuous (k131LeftWeight x) := by
  unfold k131LeftWeight
  apply Continuous.mul
  · apply k131MellinKernel.holomorphic.continuousOn.comp_continuous (by fun_prop)
    intro t
    let s : ℂ := ((-9 / 16 : ℝ) : ℂ) + Complex.I * (t : ℝ)
    have hs : s.re = -9 / 16 := by
      simp only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
    refine ⟨k131MellinKernel.strip_subset ?_, ?_⟩
    · change -1 / 2 - k131MellinKernel.delta < s.re ∧ s.re ≤ 1 / 2 + k131MellinKernel.delta
      rw [hs, k131_kernel_delta]
      exact ⟨by norm_num only, by norm_num only⟩
    · intro he
      have h := congrArg Complex.re (show s = (-1 / 2 : ℂ) from Set.mem_singleton_iff.mp he)
      rw [hs] at h
      norm_num only [Complex.neg_re, Complex.div_ofNat_re, Complex.one_re] at h
  · simp only [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne')]
    fun_prop

/-- The reflected reciprocal factor becomes a real half-line integral
of the K131 profile at shifted inverse scales. -/
theorem k131_left_resolvent {x b : ℝ} (hx : 0 < x) (hb : 0 < b) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ, (1 / ((b : ℂ) - Complex.I * (t : ℂ) / 2)) * k131LeftWeight x t) =
      ∫ u : ℝ in Set.Ioi 0,
        (Real.exp ((9 / 32 - b) * u) : ℂ) * (k131MellinProfile (x * Real.exp (u / 2))⁻¹ : ℂ) := by
  let W := fun t : ℝ ↦ k131LeftWeight x (-t)
  have hW : Continuous W := (k131_left_weight_continuous hx).comp continuous_neg
  have hI :=
    MeasureTheory.integral_neg_eq_self
      (fun t : ℝ ↦ (1 / ((b : ℂ) - Complex.I * (t : ℂ) / 2)) * k131LeftWeight x t)
      MeasureTheory.volume
  simp only [Complex.ofReal_neg, mul_neg, neg_div, sub_neg_eq_add] at hI
  rw [← hI]
  change _ * (∫ t : ℝ, (1 / ((b : ℂ) + Complex.I * (t : ℂ) / 2)) * W t) = _
  rw [LLS.PaperStatements.resolvent_integral_eq_laplace_weight hb W hW
      ((k131_left_weight_int hx).comp_neg),
    ← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  refine MeasureTheory.ae_of_all _ (fun u ↦ ?_)
  have he :=
    MeasureTheory.integral_neg_eq_self
      (fun t : ℝ ↦ Complex.exp (-((b : ℂ) + Complex.I * (t : ℂ) / 2) * (u : ℂ)) * W t)
      MeasureTheory.volume
  simp only [W, neg_neg, Complex.ofReal_neg, mul_neg, neg_div, ← sub_eq_add_neg] at he
  dsimp only [W]
  rw [← he]
  have hf (t : ℝ) :
    Complex.exp (-((b : ℂ) - Complex.I * (t : ℂ) / 2) * (u : ℂ)) * k131LeftWeight x t =
      (Real.exp ((9 / 32 - b) * u) : ℂ) * k131LeftWeight (x * Real.exp (u / 2)) t := by
    rw [show
        -((b : ℂ) - Complex.I * (t : ℂ) / 2) * (u : ℂ) =
          -(b : ℂ) * (u : ℂ) + Complex.I * (t : ℂ) * ((u / 2 : ℝ) : ℂ)
        by
        push_cast; ring,
      Complex.exp_add, mul_assoc, k131_left_weight_shift hx]
    simp only [Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
    congr 3
    push_cast
    ring
  rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ hf),
    MeasureTheory.integral_const_mul, mul_left_comm]
  have h := k131_left_weight_integral (mul_pos hx (Real.exp_pos (u / 2)))
  exact
    congrArg (_ * ·)
      (by
        simpa only [k131LeftWeight, Complex.ofReal_div, Complex.ofReal_neg,
          Complex.ofReal_ofNat] using h)

private theorem k131_left_weight_quadratic {x : ℝ} (hx : 0 < x) :
    ∃ A : ℝ, ∀ t : ℝ, ‖k131LeftWeight x t‖ ≤ A / (1 + t ^ 2) := by
  obtain ⟨C, _, hC⟩ :=
    LLS.PaperStatements.MellinKernel.exists_norm_line_le_inverseSquare k131MellinKernel (c :=
      -9 / 16)
      (by
        rw [k131_kernel_delta]; norm_num only)
      (by
        rw [k131_kernel_delta]; norm_num only)
      (by norm_num only)
  refine ⟨C * x ^ (-9 / 16 : ℝ), fun t ↦ ?_⟩
  unfold k131LeftWeight
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero, add_zero]
  rw [mul_div_right_comm]
  exact mul_le_mul_of_nonneg_right (hC t) (Real.rpow_nonneg hx.le _)

private theorem k131_left_resolvent_diff {x b : ℝ} (hx : 0 < x) (hb : 0 < b) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ, (1 / (b : ℂ) - 1 / ((b : ℂ) - Complex.I * (t : ℂ) / 2)) * k131LeftWeight x t) =
      (k131MellinProfile x⁻¹ : ℂ) / (b : ℂ) -
        ∫ u : ℝ in Set.Ioi 0,
          (Real.exp ((9 / 32 - b) * u) : ℂ) * (k131MellinProfile (x * Real.exp (u / 2))⁻¹ : ℂ) := by
  let W := k131LeftWeight x
  obtain ⟨A, hA⟩ := k131_left_weight_quadratic hx
  have hD :=
    (LLS.PaperStatements.quadratic_resolvent_integral_bound hb (fun t ↦ W (-t))
        ((k131_left_weight_continuous hx).comp continuous_neg)
        (fun t ↦ by simpa only [neg_sq] using hA (-t))).1.comp_neg
  have hd :
    MeasureTheory.Integrable
      (fun t : ℝ ↦ (1 / (b : ℂ) - 1 / ((b : ℂ) - Complex.I * (t : ℂ) / 2)) * W t) := by
    simpa only [W, neg_neg, Complex.ofReal_neg, mul_neg, neg_div, mul_div_assoc,
      ← sub_eq_add_neg] using hD
  have hW := (k131_left_weight_int hx).const_mul (1 / (b : ℂ))
  have hr :
    MeasureTheory.Integrable (fun t : ℝ ↦ (1 / ((b : ℂ) - Complex.I * (t : ℂ) / 2)) * W t) :=
    (hW.sub hd).congr
      (MeasureTheory.ae_of_all _
        (fun t ↦ by
          dsimp only [Pi.sub_apply]
          ring))
  simp only [sub_mul]
  rw [MeasureTheory.integral_sub hW hr, mul_sub, k131_left_resolvent hx hb,
    MeasureTheory.integral_const_mul, mul_left_comm]
  have h :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, k131LeftWeight x t) =
      (k131MellinProfile x⁻¹ : ℂ) := by
    simpa only [k131LeftWeight, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat] using
      k131_left_weight_integral hx
  rw [h]
  simp only [sub_mul]
  ring

/-- The reflected digamma correction is the sum of explicit differences
between the profile at the original scale and a shifted profile integral. -/
theorem k131_reflected_digamma_series {x b : ℝ} (hx : 0 < x) (hb : 0 < b) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          (Complex.digamma ((b : ℂ) - Complex.I * (t / 2 : ℝ)) - Complex.digamma (b : ℂ)) *
            k131LeftWeight x t) =
      ∑' n : ℕ,
        ((k131MellinProfile x⁻¹ : ℂ) / ((b + n : ℝ) : ℂ) -
          ∫ u : ℝ in Set.Ioi 0,
            (Real.exp ((9 / 32 - (b + n)) * u) : ℂ) *
              (k131MellinProfile (x * Real.exp (u / 2))⁻¹ : ℂ)) := by
  obtain ⟨A, hA⟩ := k131_left_weight_quadratic hx
  simp only [Complex.ofReal_div, Complex.ofReal_ofNat]
  rw [LLS.PaperStatements.quadratic_reflected_digamma_eq_tsum hb _ (k131_left_weight_continuous hx)
      hA,
    ← tsum_mul_left]
  apply tsum_congr
  intro n
  simpa only [Complex.ofReal_div, Complex.ofReal_ofNat, mul_div_assoc] using
    k131_left_resolvent_diff hx (add_pos_of_pos_of_nonneg hb (Nat.cast_nonneg n))

private theorem k131_gamma_parity {q : ℕ} (χ : DirichletCharacter ℂ q) :
    ∃ κ : ℝ,
      0 ≤ κ ∧
        (χ.Even → κ = 0) ∧
        ∀ {s : ℂ},
          0 < s.re →
            logDeriv χ.gammaFactor s =
              (-Complex.log Real.pi + Complex.digamma (s / 2 + (κ : ℂ))) / 2 := by
  classical
  by_cases he : χ.Even
  · refine ⟨0, le_rfl, fun _ ↦ rfl, ?_⟩
    intro s hs
    have hh : 0 < (s / 2).re := by
      rw [Complex.div_ofNat_re]
      exact div_pos hs (by norm_num only)
    rw [AnalyticNumberTheory.DirichletLFunction.gammaLogDeriv_even_eq_digamma he
        (fun n ↦ AnalyticNumberTheory.Gamma.not_neg_nat_of_re_pos hh n)]
    simp only [Complex.ofReal_zero, add_zero]
    ring
  · obtain ⟨κ, hκ, _, hg⟩ := LLS.PaperStatements.gammaFactor_logDeriv_eq_affine_digamma χ
    exact ⟨κ, hκ, fun h ↦ False.elim (he h), hg⟩

/-- The reflected Gamma contribution splits into the digamma value on the
real axis and a convergent correction in shifted inverse-scale profiles. -/
theorem k131_reflected_gamma_series {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) :
    ∃ b : ℝ,
      0 < b ∧
        (χ⁻¹.Even → b = 17 / 32) ∧
        k131ReflectedGamma χ x =
          ((-Complex.log Real.pi + Complex.digamma (b : ℂ)) / 2) * (k131MellinProfile x⁻¹ : ℂ) +
            (1 / 2 : ℂ) *
              ∑' n : ℕ,
                ((k131MellinProfile x⁻¹ : ℂ) / ((b + n : ℝ) : ℂ) -
                  ∫ u : ℝ in Set.Ioi 0,
                    (Real.exp ((9 / 32 - (b + n)) * u) : ℂ) *
                      (k131MellinProfile (x * Real.exp (u / 2))⁻¹ : ℂ)) := by
  obtain ⟨κ, hκ, he, hγ⟩ := k131_gamma_parity χ⁻¹
  let b := 17 / 32 + κ
  have hb : 0 < b := by
    dsimp only [b]; linarith only [hκ]
  refine ⟨b, hb, fun h ↦ by rw [show b = 17 / 32 + κ from rfl, he h, add_zero], ?_⟩
  let W := k131LeftWeight x
  let C := (-Complex.log Real.pi + Complex.digamma (b : ℂ)) / 2
  let D := fun t : ℝ ↦ Complex.digamma ((b : ℂ) - Complex.I * (t / 2 : ℝ)) - Complex.digamma (b : ℂ)
  obtain ⟨A, hA⟩ := k131_left_weight_quadratic hx
  have hi : MeasureTheory.Integrable (fun t ↦ D t * W t) := by
    simpa only [D, W, Complex.ofReal_div, Complex.ofReal_ofNat] using
      LLS.PaperStatements.integrable_quadratic_reflected_digamma hb _
        (k131_left_weight_continuous hx) hA
  have hW : MeasureTheory.Integrable W := k131_left_weight_int hx
  have hterm (t : ℝ) :
    logDeriv χ⁻¹.gammaFactor (((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)) * W t =
      C * W t + (1 / 2 : ℂ) * (D t * W t) := by
    rw [hγ
        (by
          norm_num only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re,
            Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero])]
    rw [show
        (((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)) / 2 + (κ : ℂ) =
          (b : ℂ) - Complex.I * (t / 2 : ℝ)
        by
        dsimp only [b]; push_cast; ring]
    dsimp only [C, D]
    ring
  unfold k131ReflectedGamma
  rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ hterm),
    MeasureTheory.integral_add (hW.const_mul C) (hi.const_mul (1 / 2 : ℂ)), mul_add,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, mul_left_comm _ C,
    mul_left_comm _ (1 / 2 : ℂ)]
  have hw : ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, W t) = (k131MellinProfile x⁻¹ : ℂ) := by
    simpa only [W, k131LeftWeight, Complex.ofReal_div, Complex.ofReal_neg,
      Complex.ofReal_ofNat] using k131_left_weight_integral hx
  rw [hw, k131_reflected_digamma_series hx hb]

/-- K131 on the central line with the scale factor for the Gamma integral. -/
noncomputable def k131CentralWeight (x t : ℝ) : ℂ :=
  k131MellinFn (Complex.I * t) * (x : ℂ) ^ (Complex.I * t)

private theorem k131_central_weight_cont {x : ℝ} (hx : 0 < x) :
    Continuous (k131CentralWeight x) := by
  unfold k131CentralWeight
  apply Continuous.mul
  · apply k131MellinKernel.holomorphic.continuousOn.comp_continuous (by fun_prop)
    intro t
    have hs : (Complex.I * (t : ℂ)).re = 0 := by
      simp only [Complex.mul_re, Complex.I_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
    refine ⟨k131MellinKernel.strip_subset ?_, ?_⟩
    · change -1 / 2 - k131MellinKernel.delta < (Complex.I * (t : ℂ)).re ∧ _
      rw [hs, k131_kernel_delta]
      exact ⟨by norm_num only, by norm_num only⟩
    · intro he
      have h := congrArg Complex.re (Set.mem_singleton_iff.mp he)
      norm_num only [hs, Complex.neg_re, Complex.div_ofNat_re, Complex.one_re] at h
  · simp only [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne')]
    fun_prop

private theorem k131_central_weight_int {x : ℝ} (hx : 0 < x) :
    MeasureTheory.Integrable (k131CentralWeight x) := by
  have h :=
    LLS.PaperStatements.MellinKernel.integrable_inverse_in_strip k131MellinKernel (c := 0) (u :=
      x⁻¹)
      (by
        rw [k131_kernel_delta]; norm_num only)
      (by
        rw [k131_kernel_delta]; norm_num only)
      (by norm_num only) (inv_pos.mpr hx)
  rw [show k131MellinKernel.function = k131MellinFn from rfl] at h
  change MeasureTheory.Integrable (fun t : ℝ ↦ k131CentralWeight x t)
  simpa only [k131CentralWeight, Complex.ofReal_zero, zero_add, Complex.ofReal_inv,
    Complex.cpow_neg, Complex.inv_cpow_ofReal_nonneg hx.le, inv_inv] using h

private theorem k131_central_weight_integral {x : ℝ} (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, k131CentralWeight x t) =
      (k131MellinProfile x⁻¹ : ℂ) := by
  simpa only [Analysis.inverseMellin, k131CentralWeight, Complex.ofReal_zero, zero_add,
    Complex.ofReal_inv, Complex.cpow_neg, Complex.inv_cpow_ofReal_nonneg hx.le, inv_inv] using
    k131_mellin_profile_eq (inv_pos.mpr hx)

private theorem k131_central_weight_shift {x : ℝ} (hx : 0 < x) (u t : ℝ) :
    Complex.exp (Complex.I * (t : ℂ) * (u : ℂ)) * k131CentralWeight x t =
      k131CentralWeight (x * Real.exp u) t := by
  have hy := mul_pos hx (Real.exp_pos u)
  unfold k131CentralWeight
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne'), ← Complex.ofReal_log hx.le, ←
    Complex.ofReal_log hy.le, Real.log_mul hx.ne' (Real.exp_pos u).ne', Real.log_exp,
    Complex.ofReal_add, add_mul, Complex.exp_add]
  rw [show (u : ℂ) * (Complex.I * (t : ℂ)) = Complex.I * (t : ℂ) * u by ring]
  ring

/-- The central reciprocal factor gives a Laplace integral of the K131
profile in the scale direction opposite to the reflected factor. -/
theorem k131_central_resolvent {x b : ℝ} (hx : 0 < x) (hb : 0 < b) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ, (1 / ((b : ℂ) + Complex.I * (t : ℂ) / 2)) * k131CentralWeight x t) =
      ∫ u : ℝ in Set.Ioi 0,
        (Real.exp (-b * u) : ℂ) * (k131MellinProfile (x * Real.exp (-u / 2))⁻¹ : ℂ) := by
  rw [LLS.PaperStatements.resolvent_integral_eq_laplace_weight hb _ (k131_central_weight_cont hx)
      (k131_central_weight_int hx),
    ← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  refine MeasureTheory.ae_of_all _ (fun u ↦ ?_)
  have hf (t : ℝ) :
    Complex.exp (-((b : ℂ) + Complex.I * (t : ℂ) / 2) * (u : ℂ)) * k131CentralWeight x t =
      (Real.exp (-b * u) : ℂ) * k131CentralWeight (x * Real.exp (-u / 2)) t := by
    rw [show
        -((b : ℂ) + Complex.I * (t : ℂ) / 2) * (u : ℂ) =
          ((-b * u : ℝ) : ℂ) + Complex.I * (t : ℂ) * ((-u / 2 : ℝ) : ℂ)
        by
        push_cast; ring,
      Complex.exp_add, mul_assoc, k131_central_weight_shift hx, Complex.ofReal_exp]
  dsimp only
  rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ hf),
    MeasureTheory.integral_const_mul, mul_left_comm,
    k131_central_weight_integral (mul_pos hx (Real.exp_pos _))]

private theorem k131_central_weight_quadratic {x : ℝ} (hx : 0 < x) :
    ∃ A : ℝ, ∀ t : ℝ, ‖k131CentralWeight x t‖ ≤ A / (1 + t ^ 2) := by
  obtain ⟨C, _, hC⟩ :=
    LLS.PaperStatements.MellinKernel.exists_norm_line_le_inverseSquare k131MellinKernel (c := 0)
      (by
        rw [k131_kernel_delta]; norm_num only)
      (by
        rw [k131_kernel_delta]; norm_num only)
      (by norm_num only)
  refine ⟨C, fun t ↦ ?_⟩
  unfold k131CentralWeight
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.mul_re, Complex.I_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero,
    Real.rpow_zero, mul_one]
  simpa only [Complex.ofReal_zero, zero_add,
    show k131MellinKernel.function = k131MellinFn from rfl] using hC t

private theorem k131_central_resolvent_diff {x b : ℝ} (hx : 0 < x) (hb : 0 < b) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ, (1 / (b : ℂ) - 1 / ((b : ℂ) + Complex.I * (t : ℂ) / 2)) * k131CentralWeight x t) =
      (k131MellinProfile x⁻¹ : ℂ) / (b : ℂ) -
        ∫ u : ℝ in Set.Ioi 0,
          (Real.exp (-b * u) : ℂ) * (k131MellinProfile (x * Real.exp (-u / 2))⁻¹ : ℂ) := by
  let W := k131CentralWeight x
  obtain ⟨A, hA⟩ := k131_central_weight_quadratic hx
  have hd :=
    (LLS.PaperStatements.quadratic_resolvent_integral_bound hb W (k131_central_weight_cont hx) hA).1
  have hd' :
    MeasureTheory.Integrable
      (fun t : ℝ ↦ (1 / (b : ℂ) - 1 / ((b : ℂ) + Complex.I * (t : ℂ) / 2)) * W t) := by
    simpa only [mul_div_assoc] using hd
  have hW := (k131_central_weight_int hx).const_mul (1 / (b : ℂ))
  have hr :
    MeasureTheory.Integrable (fun t : ℝ ↦ (1 / ((b : ℂ) + Complex.I * (t : ℂ) / 2)) * W t) :=
    (hW.sub hd').congr
      (MeasureTheory.ae_of_all _
        (fun t ↦ by
          dsimp only [Pi.sub_apply]
          ring))
  simp only [sub_mul]
  rw [MeasureTheory.integral_sub hW hr, mul_sub, k131_central_resolvent hx hb,
    MeasureTheory.integral_const_mul, mul_left_comm]
  rw [k131_central_weight_integral hx]
  ring

/-- The central digamma correction is the sum of explicit differences
between the profile at the original scale and a shifted profile integral. -/
theorem k131_central_digamma_series {x b : ℝ} (hx : 0 < x) (hb : 0 < b) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          (Complex.digamma ((b : ℂ) + Complex.I * (t / 2 : ℝ)) - Complex.digamma (b : ℂ)) *
            k131CentralWeight x t) =
      ∑' n : ℕ,
        ((k131MellinProfile x⁻¹ : ℂ) / ((b + n : ℝ) : ℂ) -
          ∫ u : ℝ in Set.Ioi 0,
            (Real.exp (-(b + n) * u) : ℂ) * (k131MellinProfile (x * Real.exp (-u / 2))⁻¹ : ℂ)) := by
  obtain ⟨A, hA⟩ := k131_central_weight_quadratic hx
  simp only [Complex.ofReal_div, Complex.ofReal_ofNat]
  rw [LLS.PaperStatements.quadratic_digamma_integral_eq_tsum hb _ (k131_central_weight_cont hx) hA,
    ← tsum_mul_left]
  apply tsum_congr
  intro n
  simpa only [Complex.ofReal_div, Complex.ofReal_ofNat, mul_div_assoc] using
    k131_central_resolvent_diff hx (add_pos_of_pos_of_nonneg hb (Nat.cast_nonneg n))

/-- The central Gamma contribution splits into the digamma value on the
real axis and a convergent correction in shifted forward-scale profiles. -/
theorem k131_central_gamma_series {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) :
    ∃ b : ℝ,
      0 < b ∧
        (χ.Even → b = 1 / 4) ∧
        k131GammaIntegral χ x =
          ((-Complex.log Real.pi + Complex.digamma (b : ℂ)) / 2) * (k131MellinProfile x⁻¹ : ℂ) +
            (1 / 2 : ℂ) *
              ∑' n : ℕ,
                ((k131MellinProfile x⁻¹ : ℂ) / ((b + n : ℝ) : ℂ) -
                  ∫ u : ℝ in Set.Ioi 0,
                    (Real.exp (-(b + n) * u) : ℂ) *
                      (k131MellinProfile (x * Real.exp (-u / 2))⁻¹ : ℂ)) := by
  obtain ⟨κ, hκ, he, hγ⟩ := k131_gamma_parity χ
  let b := 1 / 4 + κ
  have hb : 0 < b := by
    dsimp only [b]; linarith only [hκ]
  refine ⟨b, hb, fun h ↦ by rw [show b = 1 / 4 + κ from rfl, he h, add_zero], ?_⟩
  let W := k131CentralWeight x
  let C := (-Complex.log Real.pi + Complex.digamma (b : ℂ)) / 2
  let D := fun t : ℝ ↦ Complex.digamma ((b : ℂ) + Complex.I * (t / 2 : ℝ)) - Complex.digamma (b : ℂ)
  obtain ⟨A, hA⟩ := k131_central_weight_quadratic hx
  have hd :=
    LLS.PaperStatements.integrable_quadratic_reflected_digamma hb (fun t ↦ W (-t))
      ((k131_central_weight_cont hx).comp continuous_neg)
      (fun t ↦ by simpa only [W, neg_sq] using hA (-t))
  have hi : MeasureTheory.Integrable (fun t ↦ D t * W t) := by
    simpa only [D, neg_neg, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_neg, neg_div,
      mul_neg, sub_neg_eq_add] using hd.comp_neg
  have hW : MeasureTheory.Integrable W := k131_central_weight_int hx
  have hterm (t : ℝ) :
    logDeriv χ.gammaFactor (Complex.I * (t : ℂ) + 1 / 2) * W t =
      C * W t + (1 / 2 : ℂ) * (D t * W t) := by
    rw [hγ
        (by
          norm_num only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.div_ofNat_re,
            Complex.one_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero])]
    rw [show (Complex.I * (t : ℂ) + 1 / 2) / 2 + (κ : ℂ) = (b : ℂ) + Complex.I * (t / 2 : ℝ) by
        dsimp only [b]; push_cast; ring]
    dsimp only [C, D]
    ring
  unfold k131GammaIntegral
  change
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ, logDeriv χ.gammaFactor (Complex.I * (t : ℂ) + 1 / 2) * W t) =
      _
  rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ hterm),
    MeasureTheory.integral_add (hW.const_mul C) (hi.const_mul (1 / 2 : ℂ)), mul_add,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, mul_left_comm _ C,
    mul_left_comm _ (1 / 2 : ℂ)]
  dsimp only [W, D]
  rw [k131_central_weight_integral hx, k131_central_digamma_series hx hb]

/-- For an even self-inverse character, the combined archimedean term
has fixed digamma bases and opposite profile shifts on the two lines. -/
theorem k131_even_gamma_pair_series {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (he : χ.Even)
    (hi : χ⁻¹ = χ) {x : ℝ} (hx : 0 < x) :
    k131GammaIntegral χ x + k131ReflectedGamma χ x =
      ((-2 * Complex.log Real.pi + Complex.digamma (1 / 4) + Complex.digamma (17 / 32)) / 2) *
          (k131MellinProfile x⁻¹ : ℂ) +
        (1 / 2 : ℂ) *
          (∑' n : ℕ,
            ((k131MellinProfile x⁻¹ : ℂ) / ((1 / 4 + n : ℝ) : ℂ) -
              ∫ u : ℝ in Set.Ioi 0,
                (Real.exp (-(1 / 4 + n) * u) : ℂ) *
                  (k131MellinProfile (x * Real.exp (-u / 2))⁻¹ : ℂ))) +
        (1 / 2 : ℂ) *
          (∑' n : ℕ,
            ((k131MellinProfile x⁻¹ : ℂ) / ((17 / 32 + n : ℝ) : ℂ) -
              ∫ u : ℝ in Set.Ioi 0,
                (Real.exp (-(1 / 4 + n) * u) : ℂ) *
                  (k131MellinProfile (x * Real.exp (u / 2))⁻¹ : ℂ))) := by
  obtain ⟨b, _, hb, hc⟩ := k131_central_gamma_series χ hx
  obtain ⟨d, _, hd, hr⟩ := k131_reflected_gamma_series χ hx
  have he' : χ⁻¹.Even := hi.symm ▸ he
  rw [hb he] at hc
  rw [hd he'] at hr
  rw [hc, hr]
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  have h (n : ℕ) : (9 / 32 : ℝ) - (17 / 32 + n) = -(1 / 4 + n) := by ring
  simp only [h]
  ring

/-- Moving the inverse Mellin scale by an exponential translates the
inverse polynomial argument. The profile vanishes after crossing its support edge. -/
theorem k131_shifted_profile {x : ℝ} (hx : 0 < x) (v : ℝ) :
    let z := 9 / 4 + Real.log x
    k131MellinProfile (x * Real.exp v)⁻¹ =
      if 0 ≤ z + v then
        (gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * (z + v)) *
          gaussianK131Inverse (z + v)
      else 0 := by
  intro z
  have hp := mul_pos hx (Real.exp_pos v)
  have hl : Real.log (x * Real.exp v)⁻¹ = -(Real.log x + v) := by
    rw [Real.log_inv, Real.log_mul hx.ne' (Real.exp_pos v).ne', Real.log_exp]
  have he : 9 / 4 - -(Real.log x + v) = z + v := by
    dsimp only [z]; ring
  unfold k131MellinProfile
  rw [hl, he]
  have hc : (0 < (x * Real.exp v)⁻¹ ∧ -(Real.log x + v) ≤ 9 / 4) ↔ 0 ≤ z + v := by
    rw [and_iff_right (inv_pos.mpr hp), ← he]
    exact sub_nonneg.symm
  simp only [hc]

/-- In the even central Gamma correction the shifted argument stays
in the support exactly up to twice the inverse polynomial coordinate. -/
theorem k131_central_gamma_density {x : ℝ} (hx : 0 < x) (n : ℕ) (u : ℝ) :
    let z := 9 / 4 + Real.log x
    Real.exp (-(1 / 4 + n) * u) * k131MellinProfile (x * Real.exp (-u / 2))⁻¹ =
      if u ≤ 2 * z then
        ((gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * z)) *
          Real.exp ((19 / 32 - n) * u) *
          gaussianK131Inverse (z - u / 2)
      else 0 := by
  intro z
  rw [k131_shifted_profile hx]
  change
    Real.exp (-(1 / 4 + n) * u) *
        (if 0 ≤ z + (-u / 2) then
          (gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * (z + (-u / 2))) *
            gaussianK131Inverse (z + (-u / 2))
        else 0) =
      _
  have hz : z + (-u / 2) = z - u / 2 := by ring
  have hcond : 0 ≤ z - u / 2 ↔ u ≤ 2 * z := by constructor <;> intro h <;> linarith only [h]
  simp only [hz, hcond]
  split
  · have he :
      -(1 / 4 + (n : ℝ)) * u + -(27 / 16 : ℝ) * (z - u / 2) =
        -(27 / 16 : ℝ) * z + (19 / 32 - n) * u := by
      ring
    have hE :
      Real.exp (-(1 / 4 + (n : ℝ)) * u) * Real.exp (-(27 / 16 : ℝ) * (z - u / 2)) =
        Real.exp (-(27 / 16 : ℝ) * z) * Real.exp ((19 / 32 - n) * u) := by
      rw [← Real.exp_add, he, Real.exp_add]
    linear_combination (gaussianK131Amplitude : ℝ) * gaussianK131Inverse (z - u / 2) * hE
  · exact mul_zero _

/-- The reflected Gamma density is an exponentially decaying translate
of the inverse polynomial on the positive half-line. -/
theorem k131_reflect_gamma_density {x : ℝ} (hx : 0 < x) (hz : 0 ≤ 9 / 4 + Real.log x) (n : ℕ)
    {u : ℝ} (hu : 0 ≤ u) :
    let z := 9 / 4 + Real.log x
    Real.exp (-(1 / 4 + n) * u) * k131MellinProfile (x * Real.exp (u / 2))⁻¹ =
      ((gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * z)) *
        Real.exp (-(35 / 32 + n) * u) *
        gaussianK131Inverse (z + u / 2) := by
  intro z
  rw [k131_shifted_profile hx, ite_eq_left (add_nonneg hz (div_nonneg hu (by norm_num only)))]
  have he :
    Real.exp (-(1 / 4 + (n : ℝ)) * u) * Real.exp (-(27 / 16 : ℝ) * (z + u / 2)) =
      Real.exp (-(27 / 16 : ℝ) * z) * Real.exp (-(35 / 32 + n) * u) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  change
    Real.exp (-(1 / 4 + (n : ℝ)) * u) *
        ((gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * (z + u / 2)) *
          gaussianK131Inverse (z + u / 2)) =
      _
  linear_combination (gaussianK131Amplitude : ℝ) * gaussianK131Inverse (z + u / 2) * he

private theorem k131_shift_pow_exp (z a u : ℝ) (m : ℕ) :
    Real.exp (-a * u) * (z + u / 2) ^ m =
      ∑ j ∈ Finset.range (m + 1),
        (z ^ (m - j) * (m.choose j : ℝ) / 2 ^ j) * (u ^ j * Real.exp (-a * u)) := by
  rw [add_comm z, add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [div_pow]
  ring

/-- The reflected Gamma moments of each monomial are explicit finite
binomial combinations of the exponential moments at zero. -/
theorem k131_reflect_monomial_moment {a : ℝ} (ha : 0 < a) (z : ℝ) (m : ℕ) :
    (∫ u : ℝ in Set.Ioi 0, Real.exp (-a * u) * (z + u / 2) ^ m) =
      ∑ j ∈ Finset.range (m + 1),
        (z ^ (m - j) * (m.choose j : ℝ) / 2 ^ j) * Analysis.logPowerTailPoly a j 0 := by
  simp only [k131_shift_pow_exp]
  rw [MeasureTheory.integral_finsetSum _
      (fun j _ ↦ (Analysis.exponential_moment_integrable ha j).const_mul _)]
  apply Finset.sum_congr rfl
  intro j _
  rw [MeasureTheory.integral_const_mul, Analysis.exponential_moment_tail ha (le_refl 0), mul_zero,
    Real.exp_zero, one_mul]

/-- The finite binomial expansion of the inverse polynomial's reflected
Gamma moment, at coordinate z and decay rate a. -/
noncomputable def k131ReflectMoment (a z : ℝ) : ℝ :=
  ∑ i : Fin 9,
    (inverseCoeffs i : ℝ) *
      (∑ j ∈ Finset.range (2 * i.val + 4),
        (z ^ (2 * i.val + 3 - j) * ((2 * i.val + 3).choose j : ℝ) / 2 ^ j) *
          Analysis.logPowerTailPoly a j 0)

/-- A polynomial in the reflected Gamma density integrates to a finite
sum of the monomial moment formulas. -/
theorem k131_reflect_inverse_moment {a : ℝ} (ha : 0 < a) (z : ℝ) :
    (∫ u : ℝ in Set.Ioi 0, Real.exp (-a * u) * gaussianK131Inverse (z + u / 2)) =
      k131ReflectMoment a z := by
  have hi (m : ℕ) :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ Real.exp (-a * u) * (z + u / 2) ^ m) (Set.Ioi 0) := by
    simp only [MeasureTheory.IntegrableOn, k131_shift_pow_exp]
    exact
      MeasureTheory.integrable_finsetSum _
        (fun j _ ↦ (Analysis.exponential_moment_integrable ha j).const_mul _)
  simp only [k131ReflectMoment, gaussianK131Inverse, Finset.mul_sum, mul_left_comm (Real.exp _)]
  rw [MeasureTheory.integral_finsetSum _ (fun i _ ↦ (hi (2 * i.val + 3)).const_mul _)]
  apply Finset.sum_congr rfl
  intro i _
  rw [MeasureTheory.integral_const_mul, k131_reflect_monomial_moment ha]
  rw [Finset.mul_sum]

/-- Each shifted inverse-scale integral in the even Gamma formula is
the common profile factor times an explicit finite polynomial moment. -/
theorem k131_reflect_gamma_moment {x : ℝ} (hx : 0 < x) (hz : 0 ≤ 9 / 4 + Real.log x) (n : ℕ) :
    (∫ u : ℝ in Set.Ioi 0,
        Real.exp (-(1 / 4 + n) * u) * k131MellinProfile (x * Real.exp (u / 2))⁻¹) =
      ((gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * (9 / 4 + Real.log x))) *
        k131ReflectMoment (35 / 32 + n) (9 / 4 + Real.log x) := by
  have ha : 0 < (35 / 32 : ℝ) + n := add_pos_of_pos_of_nonneg (by norm_num only) (Nat.cast_nonneg n)
  rw [← k131_reflect_inverse_moment ha, ← MeasureTheory.integral_const_mul]
  exact
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun u hu ↦ by
        have h := k131_reflect_gamma_density hx hz n (Set.mem_Ioi.mp hu).le
        exact h.trans (by ring))

/-- The central Gamma density integrates only up to the translated
support edge, leaving an exponential polynomial on a finite interval. -/
theorem k131_central_gamma_interval {x : ℝ} (hx : 0 < x) (n : ℕ) :
    let z := 9 / 4 + Real.log x
    (∫ u : ℝ in Set.Ioi 0,
        Real.exp (-(1 / 4 + n) * u) * k131MellinProfile (x * Real.exp (-u / 2))⁻¹) =
      ((gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * z)) *
        ∫ u : ℝ in Set.Ioc 0 (2 * z),
          Real.exp ((19 / 32 - n) * u) * gaussianK131Inverse (z - u / 2) := by
  intro z
  let F := fun u : ℝ ↦ Real.exp ((19 / 32 - n) * u) * gaussianK131Inverse (z - u / 2)
  let C := (gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * z)
  calc
    _ = ∫ u : ℝ in Set.Ioi 0, (Set.Iic (2 * z)).indicator (fun u ↦ C * F u) u := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro u _
      simpa only [Set.indicator, Set.mem_Iic, F, C, z, mul_assoc] using
        k131_central_gamma_density hx n u
    _ = _ := by
      rw [MeasureTheory.setIntegral_indicator measurableSet_Iic]
      rw [show Set.Ioi (0 : ℝ) ∩ Set.Iic (2 * z) = Set.Ioc 0 (2 * z) from rfl]
      exact MeasureTheory.integral_const_mul C F

private theorem k131_neg_shift_pow_exp (z a u : ℝ) (m : ℕ) :
    Real.exp (-a * u) * (z - u / 2) ^ m =
      ∑ j ∈ Finset.range (m + 1),
        (z ^ (m - j) * (m.choose j : ℝ) / (-2) ^ j) * (u ^ j * Real.exp (-a * u)) := by
  rw [show z - u / 2 = u / (-2) + z by ring, add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [div_pow]
  ring

private theorem k131_central_monomial {a z : ℝ} (ha : a ≠ 0) (hz : 0 ≤ z) (m : ℕ) :
    (∫ u : ℝ in Set.Ioc 0 (2 * z), Real.exp (-a * u) * (z - u / 2) ^ m) =
      ∑ j ∈ Finset.range (m + 1),
        (z ^ (m - j) * (m.choose j : ℝ) / (-2) ^ j) *
          (Analysis.logPowerTailPoly a j 0 -
            Real.exp (-a * (2 * z)) * Analysis.logPowerTailPoly a j (2 * z)) := by
  have hZ : 0 ≤ 2 * z := mul_nonneg (by norm_num only) hz
  have hi (j : ℕ) :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ u ^ j * Real.exp (-a * u)) (Set.Ioc 0 (2 * z)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hZ).mp
      ((by fun_prop : Continuous (fun u : ℝ ↦ u ^ j * Real.exp (-a * u))).intervalIntegrable _ _)
  simp only [k131_neg_shift_pow_exp]
  rw [MeasureTheory.integral_finsetSum _ (fun j _ ↦ (hi j).const_mul _)]
  apply Finset.sum_congr rfl
  intro j _
  rw [MeasureTheory.integral_const_mul, Analysis.exponential_moment_interval_ne ha hZ]

/-- The finite binomial formula for the central polynomial moment,
including the contribution from the support endpoint. -/
noncomputable def k131CentralMoment (a z : ℝ) : ℝ :=
  ∑ i : Fin 9,
    (inverseCoeffs i : ℝ) *
      (∑ j ∈ Finset.range (2 * i.val + 4),
        (z ^ (2 * i.val + 3 - j) * ((2 * i.val + 3).choose j : ℝ) / (-2) ^ j) *
          (Analysis.logPowerTailPoly a j 0 -
            Real.exp (-a * (2 * z)) * Analysis.logPowerTailPoly a j (2 * z)))

/-- Evaluate the central K131 polynomial moment at any nonzero decay
rate, including the growing exponential in the first digamma term. -/
theorem k131_central_inverse_moment {a z : ℝ} (ha : a ≠ 0) (hz : 0 ≤ z) :
    (∫ u : ℝ in Set.Ioc 0 (2 * z), Real.exp (-a * u) * gaussianK131Inverse (z - u / 2)) =
      k131CentralMoment a z := by
  have hi (m : ℕ) :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ Real.exp (-a * u) * (z - u / 2) ^ m)
      (Set.Ioc 0 (2 * z)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (mul_nonneg (by norm_num only) hz)).mp
      ((by fun_prop :
            Continuous (fun u : ℝ ↦ Real.exp (-a * u) * (z - u / 2) ^ m)).intervalIntegrable
        _ _)
  simp only [k131CentralMoment, gaussianK131Inverse, Finset.mul_sum, mul_left_comm (Real.exp _)]
  rw [MeasureTheory.integral_finsetSum _ (fun i _ ↦ (hi (2 * i.val + 3)).const_mul _)]
  apply Finset.sum_congr rfl
  intro i _
  rw [MeasureTheory.integral_const_mul, k131_central_monomial ha hz, Finset.mul_sum]

/-- The even central Gamma correction's shifted integral is the common
profile factor times the finite moment at the digamma index's rate. -/
theorem k131_central_gamma_moment {x : ℝ} (hx : 0 < x) (hz : 0 ≤ 9 / 4 + Real.log x) (n : ℕ) :
    let z := 9 / 4 + Real.log x
    (∫ u : ℝ in Set.Ioi 0,
        Real.exp (-(1 / 4 + n) * u) * k131MellinProfile (x * Real.exp (-u / 2))⁻¹) =
      ((gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * z)) *
        k131CentralMoment (n - 19 / 32) z := by
  have hn : (n : ℝ) - 19 / 32 ≠ 0 := by
    cases n with
    | zero => norm_num only [Nat.cast_zero]
    | succ n =>
      have h : (1 : ℝ) ≤ (n.succ : ℕ) := by exact_mod_cast Nat.succ_pos n
      exact ne_of_gt (by linarith only [h])
  rw [k131_central_gamma_interval hx]
  simp only [← k131_central_inverse_moment hn hz, neg_sub]

/-- The real combined Gamma term for an even self-inverse character,
expressed using only digamma values at fixed arguments and polynomial moments. -/
theorem k131_even_gamma_moments {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (he : χ.Even)
    (hi : χ⁻¹ = χ) {x : ℝ} (hx : 0 < x) (hz : 0 ≤ 9 / 4 + Real.log x) :
    let z := 9 / 4 + Real.log x
    let A := (gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * z)
    (k131GammaIntegral χ x + k131ReflectedGamma χ x).re =
      A *
          (((-2 * Complex.log Real.pi + Complex.digamma (1 / 4) + Complex.digamma (17 / 32)) /
                2).re *
            gaussianK131Inverse z) +
        (1 / 2 : ℝ) *
          (∑' n : ℕ,
            A * (gaussianK131Inverse z / (1 / 4 + n) - k131CentralMoment (n - 19 / 32) z)) +
        (1 / 2 : ℝ) *
          (∑' n : ℕ,
            A * (gaussianK131Inverse z / (17 / 32 + n) - k131ReflectMoment (35 / 32 + n) z)) := by
  intro z A
  have hP : k131MellinProfile x⁻¹ = A * gaussianK131Inverse z := by
    have h := k131_shifted_profile hx 0
    simpa only [Real.exp_zero, mul_one, add_zero, ite_eq_left hz, A, z] using h
  have hc (n : ℕ) :
    (∫ u : ℝ in Set.Ioi 0,
        (Real.exp (-(1 / 4 + n) * u) : ℂ) * (k131MellinProfile (x * Real.exp (-u / 2))⁻¹ : ℂ)) =
      ((A * k131CentralMoment (n - 19 / 32) z : ℝ) : ℂ) := by
    simp only [← Complex.ofReal_mul, integral_complex_ofReal, k131_central_gamma_moment hx hz, A, z]
  have hr (n : ℕ) :
    (∫ u : ℝ in Set.Ioi 0,
        (Real.exp (-(1 / 4 + n) * u) : ℂ) * (k131MellinProfile (x * Real.exp (u / 2))⁻¹ : ℂ)) =
      ((A * k131ReflectMoment (35 / 32 + n) z : ℝ) : ℂ) := by
    simp only [← Complex.ofReal_mul, integral_complex_ofReal, k131_reflect_gamma_moment hx hz, A, z]
  rw [k131_even_gamma_pair_series χ he hi hx]
  have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by
    push_cast; rfl
  simp only [hP, hc, hr, ← Complex.ofReal_div, ← Complex.ofReal_sub, ← Complex.ofReal_tsum, hhalf]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero]
  congr 1
  · congr 1
    · ring
    · congr 1
      apply tsum_congr
      intro n
      ring
  · congr 1
    apply tsum_congr
    intro n
    ring

/-- The constant term of the K131 Gamma coefficient expansion is at
most -13/5, by two short rational digamma enclosures and the log-pi bound. -/
theorem k131_gamma_constant_le :
    ((Complex.digamma (13 / 32) + Complex.digamma (35 / 32)).re / 2 - Real.log Real.pi) ≤
      -(13 / 5 : ℝ) := by
  have hx :=
    (AnalyticNumberTheory.Gamma.rationalDigammaIntervalCheck_sound (r := 45 / 32) (N := 4) (j := 2)
        (t := 20) (lo := -7 / 100) (hi := -1 / 20) (by decide +kernel)).2
  have hy :=
    (AnalyticNumberTheory.Gamma.rationalDigammaIntervalCheck_sound (r := 35 / 32) (N := 4) (j := 2)
        (t := 20) (lo := -45 / 100) (hi := -42 / 100) (by decide +kernel)).2
  have hcast : (((13 / 32 : ℝ) : ℂ)) = 13 / 32 := by
    norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat]
  have hpos : 0 < (13 / 32 : ℂ).re := by
    rw [← hcast, Complex.ofReal_re]
    norm_num only
  have hrec :=
    Complex.digamma_apply_add_one (13 / 32 : ℂ)
      (AnalyticNumberTheory.Gamma.not_neg_nat_of_re_pos hpos)
  have h := congrArg Complex.re hrec
  rw [show (13 / 32 + 1 : ℂ) = 45 / 32 by norm_num only] at h
  have hInv : ((13 / 32 : ℂ)⁻¹).re = 32 / 13 := by
    rw [show (13 / 32 : ℂ)⁻¹ = 32 / 13 by norm_num only, Complex.div_ofNat_re, ←
      Complex.ofReal_ofNat, Complex.ofReal_re]
  have hp := AnalyticNumberTheory.Gamma.gamma_log_pi_bounds.1
  rw [Complex.add_re, hInv] at h
  norm_num only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one,
    Complex.add_re] at hx hy hp ⊢
  linarith only [hx, hy, h, hp]

private theorem k131_inv_pow_summable {a : ℝ} (ha : 0 < a) {j : ℕ} (hj : 0 < j) :
    Summable (fun n : ℕ ↦ 1 / (a + n) ^ (j + 1)) := by
  have hs : (1 : ℝ) < ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_lt_succ hj
  refine ((Real.summable_one_div_nat_add_rpow a _).mpr hs).congr (fun n ↦ ?_)
  rw [abs_of_pos (add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) ha), Real.rpow_natCast, add_comm]

/-- The normalized positive-degree Gamma coefficient, represented by
the two shifted reciprocal-power sequences from the digamma expansion. -/
noncomputable def k131GammaHigher (j : ℕ) : ℝ :=
  (∑' n : ℕ, -(((-1 : ℝ) ^ j) * (1 / (13 / 32 + n) ^ (j + 1)) + 1 / (35 / 32 + n) ^ (j + 1))) /
    2 ^ (j + 1)

private theorem k131_gamma_higher_summable {j : ℕ} (hj : 0 < j) :
    Summable
      (fun n : ℕ ↦
        -(((-1 : ℝ) ^ j) * (1 / (13 / 32 + n) ^ (j + 1)) + 1 / (35 / 32 + n) ^ (j + 1))) := by
  have h₁ := k131_inv_pow_summable (by norm_num only : (0 : ℝ) < 13 / 32) hj
  have h₂ := k131_inv_pow_summable (by norm_num only : (0 : ℝ) < 35 / 32) hj
  exact ((h₁.mul_left ((-1 : ℝ) ^ j)).add h₂).neg

/-- Even Gamma coefficients are bounded above by any finite prefix:
every omitted term is nonpositive. -/
theorem k131_gamma_even_prefix {j : ℕ} (hj : 0 < j) (he : Even j) (N : ℕ) :
    k131GammaHigher j ≤
      (∑ n ∈ Finset.range N, -(1 / ((13 / 32 : ℝ) + n) ^ (j + 1) + 1 / (35 / 32 + n) ^ (j + 1))) /
        2 ^ (j + 1) := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hs := k131_gamma_higher_summable hj
  have hsign : (-1 : ℝ) ^ j = 1 := he.neg_one_pow
  have h :=
    hs.neg.sum_le_tsum (Finset.range N)
      (fun n _ ↦ by
        simp only [hsign, one_mul, neg_neg]
        positivity)
  simpa only [hsign, one_mul, neg_neg, Finset.sum_neg_distrib, tsum_neg] using neg_le_neg h

private theorem k131_pow_series_tail {N j : ℕ} (hN : 0 < N) (hj : 0 < j) :
    (∑' n : ℕ, 1 / (((n + (N + 1) : ℕ) : ℝ) ^ (j + 1))) ≤ (N : ℝ) ^ (-(j : ℝ)) / j := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hj' : (0 : ℝ) < j := Nat.cast_pos.mpr hj
  let a : ℝ := -((j : ℝ) + 1)
  have ha : a < -1 := by
    dsimp only [a]; linarith only [hj']
  have he (n : ℕ) :
    (1 : ℝ) / (((n + (N + 1) : ℕ) : ℝ) ^ (j + 1)) = (((n + N + 1 : ℕ) : ℝ) ^ a) := by
    rw [Nat.add_assoc, show a = -(((j + 1 : ℕ) : ℝ)) by simp only [a, Nat.cast_add, Nat.cast_one],
      Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_natCast, one_div]
  rw [tsum_congr he]
  calc
    _ ≤ ∫ t : ℝ in Set.Ioi (N : ℝ), t ^ a :=
      AntitoneOn.tsum_comp_add_le_integral N
        ((Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (ha.le.trans (by norm_num only))).mono
          (fun _ ht ↦ hN'.trans_le ht))
        (integrableOn_Ioi_rpow_of_lt ha hN') (fun _ ht ↦ Real.rpow_nonneg (hN'.trans ht).le _)
    _ = _ := by
      rw [integral_Ioi_rpow_of_lt ha hN',
        show a + 1 = -(j : ℝ) by
          dsimp only [a]; ring,
        div_neg, neg_div, neg_neg]

/-- Odd Gamma coefficients admit a finite prefix upper bound plus the
integral tail of the positive reciprocal powers. -/
theorem k131_gamma_odd_prefix {j N : ℕ} (hj : 0 < j) (ho : Odd j) (hN : 0 < N) :
    k131GammaHigher j ≤
      ((∑ n ∈ Finset.range (N + 1),
            (1 / ((13 / 32 : ℝ) + n) ^ (j + 1) - 1 / (35 / 32 + n) ^ (j + 1))) +
          (N : ℝ) ^ (-(j : ℝ)) / j) /
        2 ^ (j + 1) := by
  unfold k131GammaHigher
  apply div_le_div_of_nonneg_right _ (by positivity)
  let f := fun n : ℕ ↦
    -(((-1 : ℝ) ^ j) * (1 / (13 / 32 + n) ^ (j + 1)) + 1 / (35 / 32 + n) ^ (j + 1))
  have hs : Summable f := k131_gamma_higher_summable hj
  have he (n : ℕ) : f n = 1 / ((13 / 32 : ℝ) + n) ^ (j + 1) - 1 / (35 / 32 + n) ^ (j + 1) := by
    dsimp only [f]
    rw [ho.neg_one_pow, neg_one_mul]
    ring
  change (∑' n, f n) ≤ _
  rw [← hs.sum_add_tsum_nat_add (N + 1), Finset.sum_congr rfl (fun n _ ↦ he n)]
  apply add_le_add_right
  refine
    (Summable.tsum_le_tsum ?_ ((summable_nat_add_iff _).mpr hs)
          ((summable_nat_add_iff (N + 1)).mpr
            (Real.summable_one_div_nat_pow.mpr (Nat.succ_lt_succ hj)))).trans
      (k131_pow_series_tail hN hj)
  intro n
  let m := n + (N + 1)
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.add_pos_right _ (Nat.succ_pos _))
  rw [he]
  refine
    (sub_le_self _ (by positivity)).trans
      (div_le_div_of_nonneg_left (by norm_num only) (pow_pos hm _) (pow_le_pow_left₀ hm.le ?_ _))
  exact le_add_of_nonneg_left (by norm_num only)

/-- Rational upper bounds for the normalized Gamma coefficients. The
positive-degree entries use 32 terms and include an odd-degree tail. -/
def k131GammaUpper (j : ℕ) : ℚ :=
  if j = 0 then -13 / 5
  else
    ((∑ n ∈ Finset.range 32,
          -((-1 : ℚ) ^ j / (13 / 32 + n) ^ (j + 1) + 1 / (35 / 32 + n) ^ (j + 1))) +
        (if j % 2 = 0 then 0 else 1 / ((j : ℚ) * 31 ^ j))) /
      2 ^ (j + 1)

private def k131ShiftGammaCoeff (c : ℚ) (k : ℕ) : ℚ :=
  ∑ i : Fin 9,
    inverseCoeffs i *
      ∑ j ∈ Finset.range (2 * i.val + 4 - k),
        ((j.factorial : ℚ) * k131GammaUpper j + if j = 0 then c else 0) *
          ((2 * i.val + 3).choose j : ℚ) *
          ((2 * i.val + 3 - j).choose k : ℚ) *
          14 ^ (2 * i.val + 3 - j - k)

/-- The 32-term upper certificate shifted to coordinate 14 has strictly
negative coefficients after adding twice the inverse polynomial. -/
private theorem k131_gamma_shift_check : ∀ k : Fin 20, k131ShiftGammaCoeff 2 k < 0 := by
  decide +kernel

/-- The real high-degree coefficients are bounded by the rational
32-term certificate, with the integral remainder used at odd degrees. -/
theorem k131_gamma_high_le_upper {j : ℕ} (hj : 0 < j) :
    k131GammaHigher j ≤ (k131GammaUpper j : ℝ) := by
  unfold k131GammaUpper
  rw [ite_eq_right hj.ne']
  rcases Nat.even_or_odd j with he | ho
  · have hm : j % 2 = 0 := Nat.even_iff.mp he
    simpa only [ite_eq_left hm, add_zero, Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_add,
      Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat, Rat.cast_natCast, he.neg_one_pow] using
      k131_gamma_even_prefix hj he 32
  · have hm : j % 2 ≠ 0 := by
      rw [Nat.odd_iff.mp ho]
      decide
    have ht : (31 : ℝ) ^ (-(j : ℝ)) / j = 1 / ((j : ℝ) * 31 ^ j) := by
      rw [Real.rpow_neg (by norm_num only), Real.rpow_natCast, one_div, mul_inv]
      ring
    have h := k131_gamma_odd_prefix hj ho (N := 31) (by decide)
    norm_num only [Nat.cast_ofNat] at h
    rw [ht] at h
    simpa only [ite_eq_right hm, Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_add,
      Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat, Rat.cast_natCast, Rat.cast_mul, Rat.cast_inv,
      ho.neg_one_pow, div_eq_mul_inv, neg_one_mul, neg_add_rev, neg_neg, one_mul, sub_eq_add_neg,
      add_comm] using h

/-- The actual normalized coefficient in the K131 Gamma polynomial,
including the fixed real digamma baseline at degree zero. -/
noncomputable def k131GammaCoeff (j : ℕ) : ℝ :=
  if j = 0 then (Complex.digamma (13 / 32) + Complex.digamma (35 / 32)).re / 2 - Real.log Real.pi
  else (j.factorial : ℝ) * k131GammaHigher j

private theorem k131_gamma_coeff_le (j : ℕ) :
    k131GammaCoeff j ≤ (j.factorial : ℝ) * (k131GammaUpper j : ℝ) := by
  by_cases hj : j = 0
  · subst j
    simpa only [k131GammaCoeff, k131GammaUpper, ite_true, Rat.cast_div, Rat.cast_neg,
      Rat.cast_ofNat, neg_div, Nat.factorial_zero, Nat.cast_one, one_mul] using
      k131_gamma_constant_le
  · simpa only [k131GammaCoeff, ite_eq_right hj] using
      mul_le_mul_of_nonneg_left (k131_gamma_high_le_upper (Nat.pos_of_ne_zero hj))
        (Nat.cast_nonneg j.factorial)

/-- The value of the K131 Gamma expansion at the inverse coordinate z,
with the monomials differentiated using normalized binomial coefficients. -/
noncomputable def k131GammaPolyValue (z : ℝ) : ℝ :=
  ∑ i : Fin 9,
    (inverseCoeffs i : ℝ) *
      ∑ j ∈ Finset.range (2 * i.val + 4),
        k131GammaCoeff j * ((2 * i.val + 3).choose j : ℝ) * z ^ (2 * i.val + 3 - j)

private theorem k131_gamma_pad {m : ℕ} (hm : m + 1 ≤ 20) (f : ℕ → ℝ) :
    (∑ j ∈ Finset.range 20, f j * (m.choose j : ℝ)) =
      ∑ j ∈ Finset.range (m + 1), f j * (m.choose j : ℝ) := by
  symm
  apply Finset.sum_subset (Finset.range_mono hm)
  intro j _ hj
  have h : m < j := Nat.lt_of_succ_le (Nat.le_of_not_gt (fun h ↦ hj (Finset.mem_range.mpr h)))
  rw [Nat.choose_eq_zero_of_lt h, Nat.cast_zero, mul_zero]

private theorem k131_gamma_expand_pow {m : ℕ} (hm : m + 1 ≤ 20) (t : ℝ) :
    (14 + t) ^ m = ∑ k ∈ Finset.range 20, (m.choose k : ℝ) * 14 ^ (m - k) * t ^ k := by
  rw [add_comm, add_pow]
  have h := k131_gamma_pad hm (fun k ↦ t ^ k * 14 ^ (m - k))
  simpa only [mul_comm, mul_left_comm, mul_assoc] using h.symm

private theorem k131_gamma_shift_row {m k : ℕ} (G : ℕ → ℝ) :
    (∑ j ∈ Finset.range (m + 1),
        G j * (m.choose j : ℝ) * ((m - j).choose k : ℝ) * 14 ^ (m - j - k)) =
      ∑ j ∈ Finset.range (m + 1 - k),
        G j * (m.choose j : ℝ) * ((m - j).choose k : ℝ) * 14 ^ (m - j - k) := by
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.sub_le _ _))
  intro j hj hsub
  have hj' := Finset.mem_range.mp hj
  have hk := Nat.le_of_not_gt (fun h ↦ hsub (Finset.mem_range.mpr h))
  have hz : m - j < k := by omega
  rw [Nat.choose_eq_zero_of_lt hz, Nat.cast_zero, mul_zero, zero_mul]

private theorem k131_gamma_monomial_shift {m : ℕ} (hm : m + 1 ≤ 20) (G : ℕ → ℝ) (t : ℝ) :
    (∑ j ∈ Finset.range (m + 1), G j * (m.choose j : ℝ) * (14 + t) ^ (m - j)) =
      ∑ k ∈ Finset.range 20,
        (∑ j ∈ Finset.range (m + 1 - k),
            G j * (m.choose j : ℝ) * ((m - j).choose k : ℝ) * 14 ^ (m - j - k)) *
          t ^ k := by
  calc
    _ =
        ∑ j ∈ Finset.range (m + 1),
          ∑ k ∈ Finset.range 20,
            (G j * (m.choose j : ℝ) * ((m - j).choose k : ℝ) * 14 ^ (m - j - k)) * t ^ k :=
      by
      apply Finset.sum_congr rfl
      intro j _
      rw [k131_gamma_expand_pow ((Nat.add_le_add_right (Nat.sub_le m j) 1).trans hm),
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      simpa only [Finset.sum_mul] using
        congrArg (fun v : ℝ ↦ v * t ^ k) (k131_gamma_shift_row (m := m) (k := k) G)

private theorem k131_gamma_upper_eval (t : ℝ) :
    (∑ i : Fin 9,
        (inverseCoeffs i : ℝ) *
          ∑ j ∈ Finset.range (2 * i.val + 4),
            ((j.factorial : ℝ) * (k131GammaUpper j : ℝ) + if j = 0 then 2 else 0) *
              ((2 * i.val + 3).choose j : ℝ) *
              (14 + t) ^ (2 * i.val + 3 - j)) =
      ∑ k ∈ Finset.range 20, (k131ShiftGammaCoeff (2) k : ℝ) * t ^ k := by
  have h (i : Fin 9) :=
    k131_gamma_monomial_shift (m := 2 * i.val + 3)
      (show 2 * i.val + 3 + 1 ≤ 20 from
        Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.le_of_lt_succ i.isLt)) 4)
      (fun j ↦ (j.factorial : ℝ) * (k131GammaUpper j : ℝ) + if j = 0 then 2 else 0) t
  simp only [h, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  have hc (j : ℕ) : ((if j = 0 then (2 : ℚ) else 0 : ℚ) : ℝ) = (if j = 0 then 2 else 0) := by
    split <;> norm_num only [Rat.cast_ofNat, Rat.cast_zero]
  simp only [k131ShiftGammaCoeff, Rat.cast_sum, Rat.cast_mul, Rat.cast_add, Rat.cast_pow,
    Rat.cast_natCast, Rat.cast_ofNat, hc, Finset.sum_mul, Finset.mul_sum, mul_assoc]

private theorem k131_gamma_add_baseline (z c : ℝ) :
    (∑ i : Fin 9,
        (inverseCoeffs i : ℝ) *
          ∑ j ∈ Finset.range (2 * i.val + 4),
            (k131GammaCoeff j + if j = 0 then c else 0) * ((2 * i.val + 3).choose j : ℝ) *
              z ^ (2 * i.val + 3 - j)) =
      k131GammaPolyValue z + c * gaussianK131Inverse z := by
  have h (m : ℕ) :
    (∑ j ∈ Finset.range (m + 1), (if j = 0 then c else 0) * (m.choose j : ℝ) * z ^ (m - j)) =
      c * z ^ m := by
    rw [Finset.sum_eq_single 0]
    · simp only [ite_true, Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.sub_zero]
    · intro j _ hj
      simp only [ite_eq_right hj, zero_mul]
    · intro hmem
      exact (hmem (Finset.mem_range.mpr (Nat.succ_pos m))).elim
  simp only [add_mul, mul_add, Finset.sum_add_distrib, h, k131GammaPolyValue, gaussianK131Inverse,
    Finset.mul_sum, mul_left_comm c]

/-- For z at least 14, the polynomial part of the K131 Gamma expression
is at most minus twice the inverse polynomial. -/
theorem k131_gamma_poly_le {z : ℝ} (hz : 14 ≤ z) :
    k131GammaPolyValue z ≤ -(2 : ℝ) * gaussianK131Inverse z := by
  let t := z - 14
  have ht : 0 ≤ t := sub_nonneg.mpr hz
  have hz' : z = 14 + t := by
    dsimp only [t]; ring
  have h := k131_gamma_add_baseline z (2)
  have hu :
    k131GammaPolyValue z + (2 : ℝ) * gaussianK131Inverse z ≤
      ∑ k ∈ Finset.range 20, (k131ShiftGammaCoeff (2) k : ℝ) * t ^ k := by
    rw [← h, ← k131_gamma_upper_eval t]
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left _ (inverse_coeff_nonneg_kernel i)
    apply Finset.sum_le_sum
    intro j _
    conv_rhs => rw [← hz']
    exact
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (add_le_add_left (k131_gamma_coeff_le j) _) (Nat.cast_nonneg _))
        (pow_nonneg (by linarith only [hz]) _)
  have hnon : (∑ k ∈ Finset.range 20, (k131ShiftGammaCoeff (2) k : ℝ) * t ^ k) ≤ 0 :=
    Finset.sum_nonpos
      (fun k hk ↦
        mul_nonpos_of_nonpos_of_nonneg
          (Rat.cast_nonpos.mpr (k131_gamma_shift_check ⟨k, Finset.mem_range.mp hk⟩).le)
          (pow_nonneg ht _))
  linarith only [hu.trans hnon]

private theorem k131_neg_shift_monomial_int {a : ℝ} (ha : 0 < a) (z : ℝ) (m : ℕ) :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ Real.exp (-a * u) * (z - u / 2) ^ m) (Set.Ioi 0) := by
  simp only [MeasureTheory.IntegrableOn, k131_neg_shift_pow_exp]
  exact
    MeasureTheory.integrable_finsetSum _
      (fun j _ ↦ (Analysis.exponential_moment_integrable ha j).const_mul _)

private theorem k131_neg_shift_monomial {a : ℝ} (ha : 0 < a) (z : ℝ) (m : ℕ) :
    (∫ u : ℝ in Set.Ioi 0, Real.exp (-a * u) * (z - u / 2) ^ m) =
      ∑ j ∈ Finset.range (m + 1),
        (z ^ (m - j) * (m.choose j : ℝ) / (-2) ^ j) * Analysis.logPowerTailPoly a j 0 := by
  simp only [k131_neg_shift_pow_exp]
  rw [MeasureTheory.integral_finsetSum _
      (fun j _ ↦ (Analysis.exponential_moment_integrable ha j).const_mul _)]
  apply Finset.sum_congr rfl
  intro j _
  rw [MeasureTheory.integral_const_mul, Analysis.exponential_moment_tail ha (le_refl 0), mul_zero,
    Real.exp_zero, one_mul]

/-- The complete exponential moment of the central polynomial extended
past its support, defined by a finite binomial sum at positive decay. -/
noncomputable def k131UncutMoment (a z : ℝ) : ℝ :=
  ∑ i : Fin 9,
    (inverseCoeffs i : ℝ) *
      (∑ j ∈ Finset.range (2 * i.val + 4),
        (z ^ (2 * i.val + 3 - j) * ((2 * i.val + 3).choose j : ℝ) / (-2) ^ j) *
          Analysis.logPowerTailPoly a j 0)

private theorem k131_uncut_density_integrable {a : ℝ} (ha : 0 < a) (z : ℝ) :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ Real.exp (-a * u) * gaussianK131Inverse (z - u / 2))
      (Set.Ioi 0) := by
  simp only [gaussianK131Inverse, Finset.mul_sum, mul_left_comm (Real.exp _)]
  exact
    MeasureTheory.integrable_finsetSum _
      (fun i _ ↦ (k131_neg_shift_monomial_int ha z (2 * i.val + 3)).const_mul _)

/-- The complete central moment equals the integral of the extended
polynomial over the positive half-line. -/
theorem k131_uncut_moment_eq {a : ℝ} (ha : 0 < a) (z : ℝ) :
    (∫ u : ℝ in Set.Ioi 0, Real.exp (-a * u) * gaussianK131Inverse (z - u / 2)) =
      k131UncutMoment a z := by
  simp only [k131UncutMoment, gaussianK131Inverse, Finset.mul_sum, mul_left_comm (Real.exp _)]
  rw [MeasureTheory.integral_finsetSum _
      (fun i _ ↦ (k131_neg_shift_monomial_int ha z (2 * i.val + 3)).const_mul _)]
  apply Finset.sum_congr rfl
  intro i _
  rw [MeasureTheory.integral_const_mul, k131_neg_shift_monomial ha, Finset.mul_sum]

private theorem k131_inverse_nonpos {z : ℝ} (hz : z ≤ 0) : gaussianK131Inverse z ≤ 0 := by
  unfold gaussianK131Inverse
  apply Finset.sum_nonpos
  intro i _
  have he : Odd (2 * i.val + 3) := ⟨i.val + 1, by ring⟩
  exact mul_nonpos_of_nonneg_of_nonpos (inverse_coeff_nonneg_kernel i) ((he.pow_nonpos_iff).mpr hz)

/-- At positive decay the central support cutoff removes only nonpositive
values, so the finite central moment dominates the complete polynomial moment. -/
theorem k131_uncut_le_central {a z : ℝ} (ha : 0 < a) (hz : 0 ≤ z) :
    k131UncutMoment a z ≤ k131CentralMoment a z := by
  let F := fun u : ℝ ↦ Real.exp (-a * u) * gaussianK131Inverse (z - u / 2)
  have hF : MeasureTheory.IntegrableOn F (Set.Ioi 0) := k131_uncut_density_integrable ha z
  have hi := hF.indicator (measurableSet_Iic (a := 2 * z))
  have ht : (∫ u : ℝ in Set.Ioi 0, (Set.Iic (2 * z)).indicator F u) = k131CentralMoment a z := by
    rw [MeasureTheory.setIntegral_indicator measurableSet_Iic,
      show Set.Ioi (0 : ℝ) ∩ Set.Iic (2 * z) = Set.Ioc 0 (2 * z) from rfl]
    exact k131_central_inverse_moment ha.ne' hz
  rw [← k131_uncut_moment_eq ha z, ← ht]
  apply MeasureTheory.setIntegral_mono_on hF hi measurableSet_Ioi
  intro u _
  by_cases hu : u ∈ Set.Iic (2 * z)
  · rw [Set.indicator_of_mem hu]
  · rw [Set.indicator_of_notMem hu]
    have hneg : z - u / 2 ≤ 0 := by
      have h := le_of_not_ge (fun h ↦ hu (Set.mem_Iic.mpr h))
      linarith only [h]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (k131_inverse_nonpos hneg)

private theorem k131_reflect_density_int {a : ℝ} (ha : 0 < a) (z : ℝ) :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ Real.exp (-a * u) * gaussianK131Inverse (z + u / 2))
      (Set.Ioi 0) := by
  have hi (m : ℕ) :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ Real.exp (-a * u) * (z + u / 2) ^ m) (Set.Ioi 0) := by
    simp only [MeasureTheory.IntegrableOn, k131_shift_pow_exp]
    exact
      MeasureTheory.integrable_finsetSum _
        (fun j _ ↦ (Analysis.exponential_moment_integrable ha j).const_mul _)
  simp only [gaussianK131Inverse, Finset.mul_sum, mul_left_comm (Real.exp _)]
  exact MeasureTheory.integrable_finsetSum _ (fun i _ ↦ (hi (2 * i.val + 3)).const_mul _)

private theorem k131_reflect_tail_shift {a : ℝ} (ha : 0 < a) (z : ℝ) :
    (∫ u : ℝ in Set.Ioi (2 * z), Real.exp (-a * u) * gaussianK131Inverse (u / 2)) =
      Real.exp (-a * (2 * z)) * k131ReflectMoment a z := by
  let F := fun u : ℝ ↦ Real.exp (-a * u) * gaussianK131Inverse (u / 2)
  rw [← k131_reflect_inverse_moment ha, ← MeasureTheory.integral_const_mul]
  change (∫ u : ℝ in Set.Ioi (2 * z), F u) = _
  rw [← MeasureTheory.integral_indicator measurableSet_Ioi, ←
    MeasureTheory.integral_indicator measurableSet_Ioi]
  rw [← MeasureTheory.integral_add_right_eq_self ((Set.Ioi (2 * z)).indicator F) (2 * z)]
  apply MeasureTheory.integral_congr_ae
  refine MeasureTheory.ae_of_all _ (fun u ↦ ?_)
  have hm : u + 2 * z ∈ Set.Ioi (2 * z) ↔ u ∈ Set.Ioi (0 : ℝ) := by
    simp only [Set.mem_Ioi]
    constructor <;> intro h <;> linarith only [h]
  simp only [Set.indicator, hm]
  split
  · dsimp only [F]
    rw [mul_add, Real.exp_add, show (u + 2 * z) / 2 = z + u / 2 by ring]
    ring
  · rfl

private theorem k131_reverse_central {a z : ℝ} (hz : 0 ≤ z) :
    (∫ u : ℝ in Set.Ioc 0 (2 * z), Real.exp (a * u) * gaussianK131Inverse (z - u / 2)) =
      Real.exp (a * (2 * z)) *
        ∫ u : ℝ in Set.Ioc 0 (2 * z), Real.exp (-a * u) * gaussianK131Inverse (u / 2) := by
  have hZ : 0 ≤ 2 * z := mul_nonneg (by norm_num only) hz
  rw [← intervalIntegral.integral_of_le hZ, ← intervalIntegral.integral_of_le hZ, ←
    intervalIntegral.integral_const_mul]
  let F := fun u : ℝ ↦ Real.exp (a * (2 * z)) * (Real.exp (-a * u) * gaussianK131Inverse (u / 2))
  change _ = ∫ u in (0 : ℝ)..(2 * z), F u
  have h := intervalIntegral.integral_comp_sub_left F (a := (0 : ℝ)) (b := 2 * z) (2 * z)
  rw [sub_self, sub_zero] at h
  rw [← h]
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only [F]
  rw [← mul_assoc, ← Real.exp_add, show a * (2 * z) + -a * (2 * z - u) = a * u by ring,
    show (2 * z - u) / 2 = z - u / 2 by ring]

/-- At negative decay the first central Gamma moment consists of the
complete reflected moment at zero with its endpoint factor, less the shifted tail. -/
theorem k131_central_first_moment {a z : ℝ} (ha : 0 < a) (hz : 0 ≤ z) :
    k131CentralMoment (-a) z =
      Real.exp (a * (2 * z)) * k131ReflectMoment a 0 - k131ReflectMoment a z := by
  rw [← k131_central_inverse_moment (neg_ne_zero.mpr ha.ne') hz, neg_neg, k131_reverse_central hz]
  have hF :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ Real.exp (-a * u) * gaussianK131Inverse (u / 2))
      (Set.Ioi 0) := by
    simpa only [zero_add] using k131_reflect_density_int ha 0
  have h₁ : Set.Ioc (0 : ℝ) (2 * z) ⊆ Set.Ioi 0 := fun _ hu ↦ hu.1
  have h₂ : Set.Ioi (2 * z) ⊆ Set.Ioi 0 := fun _ hu ↦
    (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) hz).trans_lt hu
  have hd : Disjoint (Set.Ioc (0 : ℝ) (2 * z)) (Set.Ioi (2 * z)) :=
    Set.disjoint_left.mpr (fun _ hu hv ↦ (not_lt_of_ge hu.2) hv)
  have h := MeasureTheory.setIntegral_union hd measurableSet_Ioi (hF.mono_set h₁) (hF.mono_set h₂)
  rw [Set.Ioc_union_Ioi_eq_Ioi (mul_nonneg (by norm_num only) hz), k131_reflect_tail_shift ha] at h
  have hM := k131_reflect_inverse_moment ha 0
  simp only [zero_add] at hM
  rw [hM] at h
  rw [show
      (∫ u : ℝ in Set.Ioc 0 (2 * z), Real.exp (-a * u) * gaussianK131Inverse (u / 2)) =
        k131ReflectMoment a 0 - Real.exp (-a * (2 * z)) * k131ReflectMoment a z
      by linarith only [h],
    mul_sub, ← mul_assoc (Real.exp (a * (2 * z))), ← Real.exp_add]
  rw [show a * (2 * z) + -a * (2 * z) = 0 by ring, Real.exp_zero, one_mul]

/-- The first central Gamma term is bounded below by the negative
reflected moment because the contribution from its support endpoint is nonnegative. -/
theorem k131_first_moment_lower {a z : ℝ} (ha : 0 < a) (hz : 0 ≤ z) :
    -k131ReflectMoment a z ≤ k131CentralMoment (-a) z := by
  have hM : 0 ≤ k131ReflectMoment a 0 := by
    rw [← k131_reflect_inverse_moment ha]
    apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
    intro u hu
    have hv : 0 ≤ u / 2 := div_nonneg (Set.mem_Ioi.mp hu).le (by norm_num only)
    exact mul_nonneg (Real.exp_pos _).le (k131_inverse_nonneg (add_nonneg le_rfl hv))
  rw [k131_central_first_moment ha hz]
  linarith only [mul_nonneg (Real.exp_pos (a * (2 * z))).le hM]

private theorem k131_tail_poly_zero {a : ℝ} (ha : a ≠ 0) (j : ℕ) :
    Analysis.logPowerTailPoly a j 0 = (j.factorial : ℝ) / a ^ (j + 1) := by
  induction j with
  | zero =>
    simp only [Analysis.logPowerTailPoly, Nat.factorial_zero, Nat.cast_one, Nat.zero_add, pow_one]
  | succ j
    h =>
    rw [Analysis.logPowerTailPoly, zero_pow (Nat.succ_ne_zero j), zero_div, zero_add, h,
      Nat.factorial_succ, Nat.cast_mul, pow_succ]
    field_simp [ha]
    rw [pow_succ, pow_succ]
    ring

private theorem k131_resolvent_corr_summable {A b : ℝ} (hb : 0 < b) (W : ℝ → ℂ) (hc : Continuous W)
    (hW : ∀ t : ℝ, ‖W t‖ ≤ A / (1 + t ^ 2)) :
    Summable
      (fun n : ℕ ↦
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            (1 / ((b + n : ℝ) : ℂ) - 1 / (((b + n : ℝ) : ℂ) + Complex.I * (t / 2))) * W t)) := by
  let F := fun (n : ℕ) (t : ℝ) ↦
    (1 / ((b + n : ℝ) : ℂ) - 1 / (((b + n : ℝ) : ℂ) + Complex.I * (t / 2))) * W t
  have hs := LLS.PaperStatements.summable_quadratic_resolvent_norm hb W hc hW
  apply Summable.of_norm
  refine hs.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
  change ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, F n t)‖ ≤ (∫ t : ℝ, ‖F n t‖) / (2 * Real.pi)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), one_div,
    inv_mul_eq_div]
  exact div_le_div_of_nonneg_right (MeasureTheory.norm_integral_le_integral_norm _) (by positivity)

/-- The even central Gamma correction, after substituting the finite
polynomial moments, is an absolutely convergent real series. -/
theorem k131_central_corr_summable {x : ℝ} (hx : 0 < x) (hz : 0 ≤ 9 / 4 + Real.log x) :
    let z := 9 / 4 + Real.log x
    let A := (gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * z)
    Summable
      (fun n : ℕ ↦
        k131MellinProfile x⁻¹ / (1 / 4 + n) - A * k131CentralMoment (n - 19 / 32) z) := by
  intro z A
  obtain ⟨C, hC⟩ := k131_central_weight_quadratic hx
  have h :=
    k131_resolvent_corr_summable (by norm_num only : (0 : ℝ) < 1 / 4) (k131CentralWeight x)
      (k131_central_weight_cont hx) hC
  refine (Complex.reCLM.summable h).congr (fun n ↦ ?_)
  have hr := k131_central_resolvent_diff hx (show 0 < (1 / 4 : ℝ) + n by positivity)
  simp only [mul_div_assoc] at hr
  change (_ : ℂ).re = _
  rw [hr]
  simp only [← Complex.ofReal_mul, integral_complex_ofReal, k131_central_gamma_moment hx hz,
    ← Complex.ofReal_div, ← Complex.ofReal_sub, Complex.ofReal_re, A, z]

/-- The even reflected Gamma correction is absolutely convergent after
substituting the finite inverse polynomial moments. -/
theorem k131_reflect_corr_summable {x : ℝ} (hx : 0 < x) (hz : 0 ≤ 9 / 4 + Real.log x) :
    let z := 9 / 4 + Real.log x
    let A := (gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * z)
    Summable
      (fun n : ℕ ↦
        k131MellinProfile x⁻¹ / (17 / 32 + n) - A * k131ReflectMoment (35 / 32 + n) z) := by
  intro z A
  obtain ⟨C, hC⟩ := k131_left_weight_quadratic hx
  let W := fun t : ℝ ↦ k131LeftWeight x (-t)
  have h :=
    k131_resolvent_corr_summable (by norm_num only : (0 : ℝ) < 17 / 32) W
      ((k131_left_weight_continuous hx).comp continuous_neg)
      (fun t ↦ by simpa only [W, neg_sq] using hC (-t))
  refine (Complex.reCLM.summable h).congr (fun n ↦ ?_)
  let b : ℝ := 17 / 32 + n
  have hsubst :=
    MeasureTheory.integral_neg_eq_self
      (fun t : ℝ ↦ (1 / (b : ℂ) - 1 / ((b : ℂ) + Complex.I * ((t : ℂ) / 2))) * W t)
      MeasureTheory.volume
  simp only [W, neg_neg, Complex.ofReal_neg, neg_div, mul_neg, ← sub_eq_add_neg] at hsubst
  have hr :=
    k131_left_resolvent_diff hx
      (show 0 < b by
        dsimp only [b]; positivity)
  rw [show (9 / 32 - b : ℝ) = -(1 / 4 + n) by
      dsimp only [b]; ring] at hr
  change
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            (1 / (b : ℂ) - 1 / ((b : ℂ) + Complex.I * ((t : ℂ) / 2))) * k131LeftWeight x (-t))).re =
      _
  simp only [mul_div_assoc] at hr
  rw [← hsubst, hr]
  simp only [← Complex.ofReal_mul, integral_complex_ofReal, k131_reflect_gamma_moment hx hz,
    ← Complex.ofReal_div, ← Complex.ofReal_sub, Complex.ofReal_re, A, z, b]

private noncomputable def k131PowerWeight (d z : ℝ) (i : Fin 9) (j : ℕ) : ℝ :=
  (inverseCoeffs i : ℝ) * (z ^ (2 * i.val + 3 - j) * ((2 * i.val + 3).choose j : ℝ) / d ^ j) *
    (j.factorial : ℝ)

private theorem k131_moment_power_form {a : ℝ} (ha : a ≠ 0) (z : ℝ) :
    k131UncutMoment a z =
        ∑ i : Fin 9,
          ∑ j ∈ Finset.range (2 * i.val + 4), k131PowerWeight (-2) z i j * (1 / a ^ (j + 1)) ∧
      k131ReflectMoment a z =
        ∑ i : Fin 9,
          ∑ j ∈ Finset.range (2 * i.val + 4), k131PowerWeight 2 z i j * (1 / a ^ (j + 1)) := by
  constructor <;>
    simp only [k131UncutMoment, k131ReflectMoment, k131PowerWeight, k131_tail_poly_zero ha,
      Finset.mul_sum, div_eq_mul_inv, one_mul, mul_assoc]

private theorem k131_power_weight_zero (d z : ℝ) (i : Fin 9) :
    k131PowerWeight d z i 0 = (inverseCoeffs i : ℝ) * z ^ (2 * i.val + 3) := by
  simp only [k131PowerWeight, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, Nat.factorial_zero,
    pow_zero, div_one, mul_one]

private theorem k131_moment_split (d a z : ℝ) :
    (∑ i : Fin 9, ∑ j ∈ Finset.range (2 * i.val + 4), k131PowerWeight d z i j * (1 / a ^ (j + 1))) =
      gaussianK131Inverse z / a +
        ∑ i : Fin 9,
          ∑ j ∈ Finset.range (2 * i.val + 3),
            k131PowerWeight d z i (j + 1) * (1 / a ^ (j + 2)) := by
  rw [gaussianK131Inverse, div_eq_mul_inv, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change (∑ j ∈ Finset.range ((2 * i.val + 3) + 1), k131PowerWeight d z i j * (1 / a ^ (j + 1))) = _
  rw [Finset.sum_range_succ']
  rw [add_comm]
  simp only [k131_power_weight_zero, Nat.zero_add, pow_one, one_div]

/-- The positive-degree central moment after removing its leading
reciprocal, as a function of the digamma index, is summable. -/
theorem k131_uncut_remainder_summable {a : ℝ} (ha : 0 < a) (z : ℝ) :
    Summable (fun n : ℕ ↦ k131UncutMoment (a + n) z - gaussianK131Inverse z / (a + n)) := by
  have hs (n : ℕ) : a + n ≠ 0 := (add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg n)).ne'
  have he (n : ℕ) :
    k131UncutMoment (a + n) z - gaussianK131Inverse z / (a + n) =
      ∑ i : Fin 9,
        ∑ j ∈ Finset.range (2 * i.val + 3),
          k131PowerWeight (-2) z i (j + 1) * (1 / (a + n) ^ (j + 2)) := by
    rw [(k131_moment_power_form (hs n) z).1, k131_moment_split, add_sub_cancel_left]
  simp only [he]
  exact
    summable_sum
      (fun i _ ↦ summable_sum (fun j _ ↦ (k131_inv_pow_summable ha (Nat.succ_pos j)).mul_left _))

/-- Removing the leading reciprocal from the reflected moment leaves
a summable real sequence at every positive base. -/
theorem k131_reflect_remainder_summable {a : ℝ} (ha : 0 < a) (z : ℝ) :
    Summable (fun n : ℕ ↦ k131ReflectMoment (a + n) z - gaussianK131Inverse z / (a + n)) := by
  have hs (n : ℕ) : a + n ≠ 0 := (add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg n)).ne'
  have he (n : ℕ) :
    k131ReflectMoment (a + n) z - gaussianK131Inverse z / (a + n) =
      ∑ i : Fin 9,
        ∑ j ∈ Finset.range (2 * i.val + 3),
          k131PowerWeight 2 z i (j + 1) * (1 / (a + n) ^ (j + 2)) := by
    rw [(k131_moment_power_form (hs n) z).2, k131_moment_split, add_sub_cancel_left]
  simp only [he]
  exact
    summable_sum
      (fun i _ ↦ summable_sum (fun j _ ↦ (k131_inv_pow_summable ha (Nat.succ_pos j)).mul_left _))

private theorem k131_power_pair (z : ℝ) (i : Fin 9) (j n : ℕ) :
    let a : ℝ := 13 / 32 + n
    let b : ℝ := 35 / 32 + n
    (-1 / 2 : ℝ) *
        (k131PowerWeight (-2) z i j * (1 / a ^ (j + 1)) +
          k131PowerWeight 2 z i j * (1 / b ^ (j + 1))) =
      (inverseCoeffs i : ℝ) * ((2 * i.val + 3).choose j : ℝ) * z ^ (2 * i.val + 3 - j) *
        (j.factorial : ℝ) *
        (-((-1 : ℝ) ^ j * (1 / a ^ (j + 1)) + 1 / b ^ (j + 1)) / 2 ^ (j + 1)) := by
  intro a b
  unfold k131PowerWeight
  rw [show (-2 : ℝ) = (-1) * 2 by norm_num only, mul_pow, pow_succ]
  have h : ((-1 : ℝ) ^ j)⁻¹ = (-1 : ℝ) ^ j := by rw [← inv_pow, inv_neg, inv_one]
  simp only [div_eq_mul_inv, mul_inv, h]
  ring

/-- The positive-degree part of the Gamma polynomial is the combined
central and reflected reciprocal-power series after removing the zeroth terms. -/
theorem k131_gamma_high_series (z : ℝ) :
    (-1 / 2 : ℝ) *
        (∑' n : ℕ,
          ((k131UncutMoment (13 / 32 + n) z - gaussianK131Inverse z / (13 / 32 + n)) +
            (k131ReflectMoment (35 / 32 + n) z - gaussianK131Inverse z / (35 / 32 + n)))) =
      ∑ i : Fin 9,
        (gaussianK131InversePoly.coeff (2 * i.val + 3)) *
          ∑ j ∈ Finset.range (2 * i.val + 3),
            k131GammaCoeff (j + 1) * ((2 * i.val + 3).choose (j + 1) : ℝ) *
              z ^ (2 * i.val + 3 - (j + 1)) := by
  have hc (i : Fin 9) : gaussianK131InversePoly.coeff (2 * i.val + 3) = (inverseCoeffs i : ℝ) := by
    unfold gaussianK131InversePoly
    rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single i]
    · rw [Polynomial.coeff_monomial_same]
    · intro j _ hj
      have hn : 2 * j.val + 3 ≠ 2 * i.val + 3 := fun he ↦
        hj (Fin.ext (Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) (Nat.add_right_cancel he)))
      rw [Polynomial.coeff_monomial, Finsupp.single_eq_of_ne (Ne.symm hn)]
    · intro h
      exact (h (Finset.mem_univ i)).elim
  simp only [hc]
  rw [← tsum_mul_left]
  have he (n : ℕ) :
    (-1 / 2 : ℝ) *
        ((k131UncutMoment (13 / 32 + n) z - gaussianK131Inverse z / (13 / 32 + n)) +
          (k131ReflectMoment (35 / 32 + n) z - gaussianK131Inverse z / (35 / 32 + n))) =
      ∑ i : Fin 9,
        ∑ j ∈ Finset.range (2 * i.val + 3),
          (inverseCoeffs i : ℝ) * ((2 * i.val + 3).choose (j + 1) : ℝ) *
            z ^ (2 * i.val + 3 - (j + 1)) *
            ((j + 1).factorial : ℝ) *
            (-((-1 : ℝ) ^ (j + 1) * (1 / (13 / 32 + n) ^ (j + 2)) + 1 / (35 / 32 + n) ^ (j + 2)) /
              2 ^ (j + 2)) := by
    rw [(k131_moment_power_form (show (13 / 32 : ℝ) + n ≠ 0 by positivity) z).1,
      (k131_moment_power_form (show (35 / 32 : ℝ) + n ≠ 0 by positivity) z).2, k131_moment_split,
      k131_moment_split, add_sub_cancel_left, add_sub_cancel_left]
    simp only [← Finset.sum_add_distrib, Finset.mul_sum, k131_power_pair]
  rw [tsum_congr he]
  have hs (j : ℕ) := (k131_gamma_higher_summable (Nat.succ_pos j)).div_const (2 ^ (j + 2))
  rw [Summable.tsum_finsetSum (fun i _ ↦ summable_sum (fun j _ ↦ (hs j).mul_left _))]
  apply Finset.sum_congr rfl
  intro i _
  rw [Summable.tsum_finsetSum (fun j _ ↦ (hs j).mul_left _), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [tsum_mul_left, tsum_div_const]
  unfold k131GammaCoeff k131GammaHigher
  rw [ite_eq_right (Nat.succ_ne_zero j)]
  ring

private theorem k131_digamma_reciprocal {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Summable (fun n : ℕ ↦ 1 / (a + n) - 1 / (b + n)) ∧
      (∑' n : ℕ, (1 / (a + n) - 1 / (b + n))) =
        (Complex.digamma (b : ℂ)).re - (Complex.digamma (a : ℂ)).re := by
  have hs :=
    AnalyticNumberTheory.Gamma.summable_resolventDifference (s := (a : ℂ)) (t := (b : ℂ))
      (by simpa only [Complex.ofReal_re] using ha.le)
      (by simpa only [Complex.ofReal_re] using hb.le)
  have h :=
    AnalyticNumberTheory.Gamma.digamma_sub_eq_resolventSeries (s := (b : ℂ)) (t := (a : ℂ))
      (by simpa only [Complex.ofReal_re] using hb) (by simpa only [Complex.ofReal_re] using ha)
  have he (n : ℕ) : (1 / ((a : ℂ) + n) - 1 / ((b : ℂ) + n)).re = 1 / (a + n) - 1 / (b + n) := by
    simp only [← Complex.ofReal_natCast, ← Complex.ofReal_add, ← Complex.ofReal_one,
      ← Complex.ofReal_div, ← Complex.ofReal_sub, Complex.ofReal_re]
  refine ⟨(Complex.reCLM.summable hs).congr he, ?_⟩
  have hr := congrArg Complex.re h
  rw [Complex.sub_re, Complex.re_tsum hs, tsum_congr he] at hr
  exact hr.symm

private theorem k131_gamma_poly_split (z : ℝ) :
    k131GammaPolyValue z =
      k131GammaCoeff 0 * gaussianK131Inverse z -
        (1 / 2 : ℝ) *
          (∑' n : ℕ,
            ((k131UncutMoment (13 / 32 + n) z - gaussianK131Inverse z / (13 / 32 + n)) +
              (k131ReflectMoment (35 / 32 + n) z - gaussianK131Inverse z / (35 / 32 + n)))) := by
  have h := k131_gamma_high_series z
  have hc (i : Fin 9) : gaussianK131InversePoly.coeff (2 * i.val + 3) = (inverseCoeffs i : ℝ) := by
    unfold gaussianK131InversePoly
    rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single i]
    · rw [Polynomial.coeff_monomial_same]
    · intro j _ hj
      have hn : 2 * j.val + 3 ≠ 2 * i.val + 3 := fun he ↦
        hj (Fin.ext (Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) (Nat.add_right_cancel he)))
      rw [Polynomial.coeff_monomial, Finsupp.single_eq_of_ne (Ne.symm hn)]
    · intro h
      exact (h (Finset.mem_univ i)).elim
  simp only [hc, neg_div, neg_mul] at h
  rw [sub_eq_add_neg, h]
  unfold k131GammaPolyValue gaussianK131Inverse
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change
    (inverseCoeffs i : ℝ) *
        (∑ j ∈ Finset.range ((2 * i.val + 3) + 1),
          k131GammaCoeff j * ((2 * i.val + 3).choose j : ℝ) * z ^ (2 * i.val + 3 - j)) =
      _
  rw [Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.sub_zero, mul_add]
  ring

private theorem k131_reciprocal_baseline {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (B : ℝ) (M : ℕ → ℝ)
    (hs : Summable (fun n : ℕ ↦ M n - B / (b + n))) :
    Summable (fun n : ℕ ↦ B / (a + n) - M n) ∧
      (∑' n : ℕ, (B / (a + n) - M n)) =
        B * ((Complex.digamma (b : ℂ)).re - (Complex.digamma (a : ℂ)).re) -
          ∑' n : ℕ, (M n - B / (b + n)) := by
  obtain ⟨hD, hEq⟩ := k131_digamma_reciprocal ha hb
  have h := hD.mul_left B
  have he (n : ℕ) : B * (1 / (a + n) - 1 / (b + n)) - (M n - B / (b + n)) = B / (a + n) - M n := by
    ring
  refine ⟨(h.sub hs).congr he, ?_⟩
  rw [tsum_congr (fun n ↦ (he n).symm), h.tsum_sub hs, tsum_mul_left, hEq]

private theorem k131_digamma_quarter_shift :
    (Complex.digamma (5 / 4)).re = (Complex.digamma (1 / 4)).re + 4 := by
  have h : (0 : ℝ) < (1 / 4 : ℂ).re := by norm_num only [Complex.div_ofNat_re, Complex.one_re]
  have he :=
    Complex.digamma_apply_add_one (1 / 4) (AnalyticNumberTheory.Gamma.not_neg_nat_of_re_pos h)
  have he' := congrArg Complex.re he
  simpa only [show (1 / 4 + 1 : ℂ) = 5 / 4 by norm_num only, Complex.add_re,
    show (1 / 4 : ℂ)⁻¹ = 4 by norm_num only,
    show (4 : ℂ).re = 4 by rw [← Complex.ofReal_ofNat, Complex.ofReal_re]] using he'

/-- For an even self-inverse character in the K131 range, the combined
Gamma integral is bounded by minus twice the profile and the first endpoint mass. -/
theorem k131_even_gamma_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (he : χ.Even)
    (hi : χ⁻¹ = χ) {x : ℝ} (hx : 0 < x) (hz : 14 ≤ 9 / 4 + Real.log x) :
    let z := 9 / 4 + Real.log x
    (k131GammaIntegral χ x + k131ReflectedGamma χ x).re ≤
      -2 * k131MellinProfile x⁻¹ -
        ((gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * z)) *
            k131CentralMoment (-(19 / 32 : ℝ)) z /
          2 := by
  intro z
  let A := (gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * z)
  let B := gaussianK131Inverse z
  have hz₀ : 0 ≤ z := (by norm_num only : (0 : ℝ) ≤ 14).trans hz
  have hA : 0 ≤ A := mul_nonneg (Rat.cast_nonneg.mpr (by decide +kernel)) (Real.exp_pos _).le
  have hP : k131MellinProfile x⁻¹ = A * B := by
    simpa only [Real.exp_zero, mul_one, add_zero, ite_eq_left hz₀, A, B, z] using
      k131_shifted_profile hx 0
  have hu := k131_uncut_remainder_summable (by norm_num only : (0 : ℝ) < 13 / 32) z
  have hr := k131_reflect_remainder_summable (by norm_num only : (0 : ℝ) < 35 / 32) z
  obtain ⟨hcs, hc⟩ :=
    k131_reciprocal_baseline (by norm_num only : (0 : ℝ) < 5 / 4)
      (by norm_num only : (0 : ℝ) < 13 / 32) B (fun n ↦ k131UncutMoment (13 / 32 + n) z) hu
  obtain ⟨hrs, hrEq⟩ :=
    k131_reciprocal_baseline (by norm_num only : (0 : ℝ) < 17 / 32)
      (by norm_num only : (0 : ℝ) < 35 / 32) B (fun n ↦ k131ReflectMoment (35 / 32 + n) z) hr
  let C := fun n : ℕ ↦ A * (B / (1 / 4 + n) - k131CentralMoment (n - 19 / 32) z)
  have hC : Summable C := by
    have hs := k131_central_corr_summable hx hz₀
    rw [hP] at hs
    exact
      hs.congr
        (fun n ↦ by
          dsimp only [C, z, A, B]; ring)
  have htail :
    (∑' n : ℕ, C (n + 1)) ≤ ∑' n : ℕ, A * (B / (5 / 4 + n) - k131UncutMoment (13 / 32 + n) z) := by
    refine Summable.tsum_le_tsum (fun n ↦ ?_) ((summable_nat_add_iff 1).mpr hC) (hcs.mul_left A)
    have hn : 0 < (13 / 32 : ℝ) + n := by positivity
    have h := k131_uncut_le_central hn hz₀
    dsimp only [C]
    rw [Nat.cast_add, Nat.cast_one, show (1 / 4 : ℝ) + ((n : ℝ) + 1) = 5 / 4 + n by ring,
      show (n : ℝ) + 1 - 19 / 32 = 13 / 32 + n by ring]
    exact mul_le_mul_of_nonneg_left (sub_le_sub_left h _) hA
  simp only [tsum_mul_left, hc] at htail
  have h₀ : C 0 = A * (4 * B - k131CentralMoment (-(19 / 32 : ℝ)) z) := by
    dsimp only [C]
    rw [Nat.cast_zero, add_zero, zero_sub]
    ring
  have hpoly := k131_gamma_poly_split z
  rw [hu.tsum_add hr] at hpoly
  have hbound := mul_le_mul_of_nonneg_left (k131_gamma_poly_le hz) hA
  change A * k131GammaPolyValue z ≤ A * (-2 * B) at hbound
  have hgamma := k131_even_gamma_moments χ he hi hx hz₀
  change
    (k131GammaIntegral χ x + k131ReflectedGamma χ x).re =
      _ + (1 / 2 : ℝ) * (∑' n : ℕ, C n) +
        (1 / 2 : ℝ) *
          (∑' n : ℕ, A * (B / (17 / 32 + n) - k131ReflectMoment (35 / 32 + n) z)) at hgamma
  rw [← hC.sum_add_tsum_nat_add 1, Finset.sum_range_one, h₀] at hgamma
  simp only [tsum_mul_left, hrEq] at hgamma
  rw [hP]
  change _ ≤ -2 * (A * B) - A * k131CentralMoment (-(19 / 32 : ℝ)) z / 2
  unfold k131GammaCoeff at hpoly
  simp only [ite_true, Complex.add_re] at hpoly
  have hc₂ : (-2 : ℂ) = ((-2 : ℝ) : ℂ) := by
    norm_num only [Complex.ofReal_neg, Complex.ofReal_ofNat]
  rw [hc₂] at hgamma
  simp only [Complex.div_ofNat_re, Complex.add_re, Complex.mul_re, Complex.ofReal_im,
    Complex.ofReal_re, zero_mul, sub_zero, Complex.ofReal_div, Complex.ofReal_ofNat] at hgamma htail
  have hshift := k131_digamma_quarter_shift
  have hlog := Complex.log_ofReal_re Real.pi
  rw [hshift] at htail
  rw [hlog] at hgamma
  have hp := congrArg (fun v : ℝ ↦ A * v) hpoly
  simp only [A, B, z, Complex.add_re] at hgamma htail hp hbound ⊢
  nlinarith only [hgamma, htail, hp, hbound]

/-- The K131 pair-character Euler trace is bounded by its oscillatory
zero sums and conductor term, with the combined Gamma saving retained. -/
theorem k131_pair_euler_upper {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r] (hp : Odd p) (hq : Odd q)
    (hr : Odd r) (hpq : 2 ≤ p * q) (hpr : 2 ≤ p * r) (hqr : 2 ≤ q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L : ℝ}
    (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000) :
    let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
    let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
    let y := gaussianBridgeScale L
    let x := y ^ 2
    let z := 9 / 4 + Real.log x
    a.IsPrimitive →
      b.IsPrimitive →
      c.IsPrimitive →
      a ≠ 1 →
      b ≠ 1 →
      c ≠ 1 →
      a.Even →
      b.Even →
      c.Even →
      (∀ l : ℕ, l.Prime → (l : ℝ) ≤ x → a l = 1 ∧ b l = 1 ∧ c l = 1) →
      (∑ n ∈ Finset.Icc 0 ⌊x * Real.exp (9 / 4)⌋₊,
          ((a n).re + (b n).re + (c n).re) *
            (k131ForwardWeight y n * ArithmeticFunction.vonMangoldt n)) ≤
        -(∑' ρ : ℂ, k131MellinKernel.oscillatingZeroTerm a x ρ).re -
              (∑' ρ : ℂ, k131MellinKernel.oscillatingZeroTerm b x ρ).re -
              (∑' ρ : ℂ, k131MellinKernel.oscillatingZeroTerm c x ρ).re +
            (Real.log ((p * q : ℕ) : ℝ) + Real.log ((p * r : ℕ) : ℝ) + Real.log ((q * r : ℕ) : ℝ) -
                6) *
              k131MellinProfile x⁻¹ -
          3 *
            (((gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * z)) *
                k131CentralMoment (-(19 / 32 : ℝ)) z /
              2) := by
  intro a b c y x z ha hb hc ha₁ hb₁ hc₁ hea heb hec hsmall
  have hy : 1 ≤ y :=
    (by norm_num only : (1 : ℝ) ≤ 465644807 / 400000).trans (gaussian_bridge_scale_mem hL).1
  have hx : 0 < x := pow_pos (zero_lt_one.trans_le hy) 2
  have hz : 14 ≤ z := (by norm_num only : (14 : ℝ) ≤ 16).trans (k131_reflect_cutoff hL).2.2
  have hai : a⁻¹ = a := (NumberTheory.complexJacobiNumeratorCharacter_isQuadratic _ _).inv
  have hbi : b⁻¹ = b := (NumberTheory.complexJacobiNumeratorCharacter_isQuadratic _ _).inv
  have hci : c⁻¹ = c := (NumberTheory.complexJacobiNumeratorCharacter_isQuadratic _ _).inv
  have hA :=
    k131_euler_reflected hpq hGRH ha ha₁
      (by
        rw [hai]; exact ha₁)
      hy
  have hB :=
    k131_euler_reflected hpr hGRH hb hb₁
      (by
        rw [hbi]; exact hb₁)
      hy
  have hC :=
    k131_euler_reflected hqr hGRH hc hc₁
      (by
        rw [hci]; exact hc₁)
      hy
  have hR := k131_bridge_reflected_le_gamma hp hq hr hL ha hb hc ha₁ hb₁ hc₁ hsmall
  have hGa := k131_even_gamma_le a hea hai hx hz
  have hGb := k131_even_gamma_le b heb hbi hx hz
  have hGc := k131_even_gamma_le c hec hci hx hz
  have hlog (m : ℕ) :
    (Complex.log m * (k131MellinProfile x⁻¹ : ℂ)).re =
      Real.log (m : ℝ) * k131MellinProfile x⁻¹ := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      ← Complex.ofReal_natCast, Complex.log_ofReal_re]
  simp only [add_mul, Finset.sum_add_distrib]
  simp only [Complex.add_re] at hR hGa hGb hGc
  dsimp only [x, y, z] at hA hB hC hR hGa hGb hGc hlog ⊢
  rw [hA, hB, hC, hlog, hlog, hlog]
  linarith only [hR, hGa, hGb, hGc]

/-- The first central Gamma saving at radius y is the positive pole
term of order 1/y less a reflected polynomial moment of order y^(-27/8). -/
theorem k131_gamma_first_radius {y : ℝ} (hy : 1 ≤ y) :
    let z := 9 / 4 + 2 * Real.log y
    let A := (gaussianK131Amplitude : ℝ)
    A * Real.exp (-(27 / 16 : ℝ) * z) * k131CentralMoment (-(19 / 32 : ℝ)) z / 2 =
      A * Real.exp (-(9 / 8 : ℝ)) * k131ReflectMoment (19 / 32) 0 / (2 * y) -
        (A * Real.exp (-(27 / 16 : ℝ) * (9 / 4))) * y ^ (-(27 / 8 : ℝ)) *
            k131ReflectMoment (19 / 32) z /
          2 := by
  intro z A
  have hy₀ := zero_lt_one.trans_le hy
  have hz : 0 ≤ z := by
    dsimp only [z]; linarith only [Real.log_nonneg hy]
  rw [k131_central_first_moment (by norm_num only) hz]
  have h₁ :
    Real.exp (-(27 / 16 : ℝ) * z) * Real.exp ((19 / 32 : ℝ) * (2 * z)) =
      Real.exp (-(9 / 8 : ℝ)) / y := by
    rw [← Real.exp_add,
      show -(27 / 16 : ℝ) * z + (19 / 32 : ℝ) * (2 * z) = -(9 / 8 : ℝ) + -Real.log y by
        dsimp only [z]; ring,
      Real.exp_add, Real.exp_neg, Real.exp_neg, Real.exp_log hy₀]
    exact (div_eq_mul_inv _ _).symm
  have h₂ :
    Real.exp (-(27 / 16 : ℝ) * z) = Real.exp (-(27 / 16 : ℝ) * (9 / 4)) * y ^ (-(27 / 8 : ℝ)) := by
    rw [Real.rpow_def_of_pos hy₀, ← Real.exp_add]
    congr 1
    dsimp only [z]
    ring
  have hy₂ : 2 * y ≠ 0 := mul_ne_zero (by norm_num only) hy₀.ne'
  rw [mul_sub, sub_div, mul_assoc A, ← mul_assoc (Real.exp (-(27 / 16 : ℝ) * z)), h₁, h₂]
  field_simp [hy₀.ne', hy₂]

/-- The three Gamma profile savings absorb the logarithmic boundary
cost in the principal lower comparison, leaving at most 2L times the profile. -/
theorem k131_conductor_absorb {y L : ℝ} (hy : 1 ≤ y) :
    (2 * L - 6) * k131MellinProfile (y ^ 2)⁻¹ +
        3 * Real.log (2 * Real.pi) * k131MellinProfile (y ^ 2)⁻¹ ≤
      2 * L * k131MellinProfile (y ^ 2)⁻¹ := by
  have hR : 0 ≤ k131MellinProfile (y ^ 2)⁻¹ := by
    rw [k131_conductor_profile hy]
    have hz : 0 ≤ 9 / 4 + 2 * Real.log y := by linarith only [Real.log_nonneg hy]
    have hA : 0 ≤ (gaussianK131Amplitude : ℝ) := Rat.cast_nonneg.mpr (by decide +kernel)
    have hB := k131_inverse_nonneg hz
    positivity
  have hc : 3 * Real.log (2 * Real.pi) ≤ 6 := by linarith only [Analysis.log_two_mul_pi_lt]
  nlinarith only [mul_le_mul_of_nonneg_right hc hR]

/-- The degree-eight numerator whose square gives the full K131 kernel. -/
noncomputable def k131Numerator (s : ℂ) : ℂ :=
  s ^ 8 + (29 / 2 : ℂ) * s ^ 6 + 12 * s ^ 2 + 54

private theorem k131_pole_scaled (i : Fin 9) (s : ℂ) :
    (k131PoleScale i : ℂ) * (k131Pole i).function s =
      ((gaussianK131Amplitude : ℝ) : ℂ) * Complex.exp ((9 / 4 : ℂ) * s) *
        ((inverseCoeffs i : ℂ) * ((2 * i.val + 3).factorial : ℂ) /
          (s + 27 / 16) ^ (2 * i.val + 4)) := by
  change (k131PoleScale i : ℂ) * Analysis.rationalPoleFunction (i.val + 2) (8 / 27) (9 / 8) s = _
  have he : (1 : ℂ) + 2 * (8 / 27) * s = (16 / 27 : ℂ) * (s + 27 / 16) := by ring
  have hn : 2 * (i.val + 2) = 2 * i.val + 4 := by ring
  unfold k131PoleScale Analysis.rationalPoleFunction
  push_cast
  rw [he, hn, mul_pow, pow_succ' (16 / 27 : ℂ) (2 * i.val + 3)]
  have h₂ : (2 : ℂ) * (8 / 27) = 16 / 27 := by norm_num only
  have h₉ : (2 : ℂ) * (9 / 8) = 9 / 4 := by norm_num only
  rw [h₂, h₉]
  field_simp [pow_ne_zero _ (by norm_num only : (16 / 27 : ℂ) ≠ 0)]

private theorem k131_num_sum (s : ℂ) :
    (∑ i : Fin 9,
        (inverseCoeffs i : ℂ) * ((2 * i.val + 3).factorial : ℂ) * s ^ (20 - (2 * i.val + 4))) =
      k131Numerator s ^ 2 := by
  unfold k131Numerator
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ, inverseCoeffs,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Rat.cast_div, Rat.cast_ofNat, Rat.cast_one,
    Nat.factorial, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, Nat.cast_succ]
  ring

/-- Away from the pole, the nine rational terms combine into the
square of the manuscript numerator. -/
theorem k131_mellin_closed (s : ℂ) (hs : s + 27 / 16 ≠ 0) :
    k131MellinFn s =
      ((gaussianK131Amplitude : ℝ) : ℂ) * Complex.exp ((9 / 4 : ℂ) * s) *
        (k131Numerator (s + 27 / 16) ^ 2 / (s + 27 / 16) ^ 20) := by
  unfold k131MellinFn
  simp only [k131_pole_scaled, ← Finset.mul_sum]
  rw [← k131_num_sum, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hm : 2 * i.val + 4 ≤ 20 :=
    Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.le_of_lt_succ i.isLt)) 4
  let d : ℂ := s + 27 / 16
  have hd : d ≠ 0 := hs
  have hpow : d ^ 20 = d ^ (20 - (2 * i.val + 4)) * d ^ (2 * i.val + 4) := by
    rw [← pow_add, Nat.sub_add_cancel hm]
  change _ / d ^ (2 * i.val + 4) = _ * d ^ (20 - (2 * i.val + 4)) / d ^ 20
  rw [hpow]
  field_simp [pow_ne_zero _ hd]

/-- The modulus of K131 on the central line is a nonnegative rational
weight, given by the squared numerator modulus over the tenth power
of the sum of squares. -/
theorem k131_norm_central (t : ℝ) :
    ‖k131MellinFn (Complex.I * (t : ℂ))‖ =
      (gaussianK131Amplitude : ℝ) *
        (Complex.normSq (k131Numerator (Complex.I * (t : ℂ) + 27 / 16)) /
          (t ^ 2 + (27 / 16 : ℝ) ^ 2) ^ 10) := by
  let d : ℂ := Complex.I * (t : ℂ) + 27 / 16
  have hc : (27 / 16 : ℂ) = ((27 / 16 : ℝ) : ℂ) := by
    push_cast; rfl
  have hdre : d.re = 27 / 16 := by
    simp only [d, hc, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im, zero_mul,
      mul_zero, sub_zero, zero_add, Complex.ofReal_re]
  have hdim : d.im = t := by
    simp only [d, hc, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_im,
      Complex.ofReal_re, zero_mul, one_mul, zero_add, add_zero]
  have hd : d ≠ 0 := by
    intro he
    rw [he, Complex.zero_re] at hdre
    norm_num only at hdre
  have hpow : ‖d‖ ^ 20 = (t ^ 2 + (27 / 16 : ℝ) ^ 2) ^ 10 := by
    rw [show (20 : ℕ) = 2 * 10 by decide, pow_mul, Complex.sq_norm, Complex.normSq_apply, hdre,
      hdim]
    ring
  have he : ‖Complex.exp ((9 / 4 : ℂ) * (Complex.I * (t : ℂ)))‖ = 1 := by
    rw [Complex.norm_exp,
      show (9 / 4 : ℂ) = ((9 / 4 : ℝ) : ℂ) by
        push_cast; rfl]
    simp only [Complex.mul_re, Complex.I_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero,
      Real.exp_zero]
  rw [k131_mellin_closed _ hd, norm_mul, norm_mul, he, mul_one, norm_div, norm_pow, norm_pow]
  rw [Complex.sq_norm, hpow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Rat.cast_nonneg.mpr (by decide +kernel))]

/-- The holomorphic rational expression for the absolute K131 weight
on the central line, written in partial fractions for Fourier inversion. -/
noncomputable def k131MassFn (s : ℂ) : ℂ :=
  ((gaussianK131Amplitude : ℝ) : ℂ) *
    ∑ i : Fin 9, (gammaCoeffs i : ℂ) / (((27 / 16 : ℂ) ^ 2 - s ^ 2) ^ (10 - i.val))

private theorem k131_num_conj_prod (s : ℂ) :
    k131Numerator (27 / 16 + s) * k131Numerator (27 / 16 - s) =
      ∑ i : Fin 9, (gammaCoeffs i : ℂ) * ((27 / 16 : ℂ) ^ 2 - s ^ 2) ^ i.val := by
  unfold k131Numerator
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ, gammaCoeffs,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Rat.cast_div, Rat.cast_ofNat, Rat.cast_one,
    Rat.cast_neg]
  ring

private theorem k131_mass_denominator (s : ℂ) (hs : (27 / 16 : ℂ) ^ 2 - s ^ 2 ≠ 0) :
    k131MassFn s =
      ((gaussianK131Amplitude : ℝ) : ℂ) *
        (k131Numerator (27 / 16 + s) * k131Numerator (27 / 16 - s) /
          ((27 / 16 : ℂ) ^ 2 - s ^ 2) ^ 10) := by
  rw [k131MassFn, k131_num_conj_prod, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  let d : ℂ := (27 / 16 : ℂ) ^ 2 - s ^ 2
  have hd : d ≠ 0 := hs
  have he : 10 - i.val + i.val = 10 := Nat.sub_add_cancel (i.isLt.le.trans (by decide))
  have hp : d ^ 10 = d ^ (10 - i.val) * d ^ i.val := by rw [← pow_add, he]
  change _ / d ^ (10 - i.val) = _ * d ^ i.val / d ^ 10
  rw [hp]
  field_simp [pow_ne_zero _ hd]

/-- The partial-fraction kernel agrees with the absolute K131 weight
at each real ordinate, including ordinate zero. -/
theorem k131_mass_central (t : ℝ) :
    k131MassFn (Complex.I * (t : ℂ)) = (‖k131MellinFn (Complex.I * (t : ℂ))‖ : ℂ) := by
  have hden :
    (27 / 16 : ℂ) ^ 2 - (Complex.I * (t : ℂ)) ^ 2 = ((t ^ 2 + (27 / 16 : ℝ) ^ 2 : ℝ) : ℂ) := by
    push_cast
    rw [mul_pow, Complex.I_sq]
    ring
  have hp : 0 < t ^ 2 + (27 / 16 : ℝ) ^ 2 := by positivity
  have hd : (27 / 16 : ℂ) ^ 2 - (Complex.I * (t : ℂ)) ^ 2 ≠ 0 := by
    rw [hden]
    exact Complex.ofReal_ne_zero.mpr hp.ne'
  have hconj :
    (starRingEnd ℂ) (k131Numerator (Complex.I * (t : ℂ) + 27 / 16)) =
      k131Numerator (27 / 16 - Complex.I * (t : ℂ)) := by
    unfold k131Numerator
    simp only [map_add, map_mul, map_div₀, map_pow, map_ofNat, Complex.conj_I, Complex.conj_ofReal]
    rw [show -Complex.I * (t : ℂ) + 27 / 16 = 27 / 16 - Complex.I * (t : ℂ) by ring]
  rw [k131_mass_denominator _ hd, k131_norm_central, hden, add_comm (27 / 16 : ℂ), ← hconj,
    Complex.mul_conj]
  push_cast
  rfl

/-- The absolute zero weight is its nonnegative completed-L multiplicity
times the partial-fraction mass kernel at its ordinate. -/
theorem k131_zero_mass_term {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hne : χ ≠ 1) {x : ℝ}
    (hx : 0 < x) (ρ : ℂ) :
    ‖k131MellinKernel.oscillatingZeroTerm χ x ρ‖ =
      (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
        (k131MassFn (Complex.I * ρ.im)).re := by
  have ha : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := fun z _ ↦
    (DirichletCharacter.differentiable_completedLFunction hne).analyticAt z
  have hd : (0 : ℝ) ≤ (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) := by
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg ha ρ
  rw [LLS.PaperStatements.MellinKernel.norm_oscillatingZeroTerm _ χ hx,
    LLS.PaperStatements.MellinKernel.kernelZeroTerm, norm_mul, Complex.norm_intCast,
    abs_of_nonneg hd, k131_mass_central, Complex.ofReal_re]
  rfl

private theorem k131_mass_den_norm {s : ℂ} (hl : -(3 / 4 : ℝ) ≤ s.re) (hu : s.re ≤ 3 / 4) :
    1 + ‖s‖ ^ 2 ≤ ‖(27 / 16 : ℂ) ^ 2 - s ^ 2‖ := by
  let d := (27 / 16 : ℂ) ^ 2 - s ^ 2
  have h := Complex.re_le_norm d
  have hc : (27 / 16 : ℂ) = ((27 / 16 : ℝ) : ℂ) := by
    push_cast; rfl
  simp only [d, hc, Complex.sub_re, pow_two, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero] at h
  rw [← hc, ← pow_two (27 / 16 : ℂ), ← pow_two s] at h
  rw [Complex.sq_norm, Complex.normSq_apply]
  nlinarith only [h, sq_le_sq' hl hu]

/-- The two poles of the symmetric mass kernel are outside the
contour strip, so the mass kernel is holomorphic there. -/
theorem k131_mass_differentiable {s : ℂ} (hl : -(3 / 4 : ℝ) ≤ s.re) (hu : s.re ≤ 3 / 4) :
    DifferentiableAt ℂ k131MassFn s := by
  have h := k131_mass_den_norm hl hu
  have hd : (27 / 16 : ℂ) ^ 2 - s ^ 2 ≠ 0 := by
    intro he
    rw [he, norm_zero] at h
    linarith only [h, sq_nonneg ‖s‖]
  unfold k131MassFn
  fun_prop (disch := exact pow_ne_zero _ hd)

/-- Uniform inverse-square decay for the symmetric mass kernel
throughout the closed strip used for contour deformation. -/
theorem k131_mass_decay :
    ∃ C : ℝ,
      0 < C ∧ ∀ s : ℂ, -(3 / 4 : ℝ) ≤ s.re → s.re ≤ 3 / 4 → ‖k131MassFn s‖ ≤ C / (1 + ‖s‖ ^ 2) := by
  let A := ‖((gaussianK131Amplitude : ℝ) : ℂ)‖
  let B := ∑ i : Fin 9, ‖(gammaCoeffs i : ℂ)‖
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)
  refine
    ⟨A * B + 1, add_pos_of_nonneg_of_pos (mul_nonneg (norm_nonneg _) hB) zero_lt_one, fun s hl hu ↦
      ?_⟩
  let d : ℂ := (27 / 16 : ℂ) ^ 2 - s ^ 2
  have hd : 1 + ‖s‖ ^ 2 ≤ ‖d‖ := k131_mass_den_norm hl hu
  have hd₁ : 1 ≤ ‖d‖ := (le_add_of_nonneg_right (sq_nonneg _)).trans hd
  have hterm (i : Fin 9) :
    ‖(gammaCoeffs i : ℂ) / d ^ (10 - i.val)‖ ≤ ‖(gammaCoeffs i : ℂ)‖ / (1 + ‖s‖ ^ 2) := by
    have hm : 1 ≤ 10 - i.val :=
      Nat.le_sub_of_add_le
        (by simpa only [Nat.add_comm 1] using (Nat.succ_le_of_lt i.isLt).trans (by decide : 9 ≤ 10))
    rw [norm_div, norm_pow]
    apply div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
    exact hd.trans (by simpa only [pow_one] using pow_le_pow_right₀ hd₁ hm)
  unfold k131MassFn
  rw [norm_mul]
  calc
    _ ≤ A * ∑ i : Fin 9, ‖(gammaCoeffs i : ℂ) / d ^ (10 - i.val)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
    _ ≤ A * (B / (1 + ‖s‖ ^ 2)) := by
      dsimp only [B]
      rw [Finset.sum_div]
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ ↦ hterm i)) (norm_nonneg _)
    _ ≤ _ := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (by positivity)

/-- The K131 mass kernel is integrable on every vertical line within
the closed contour strip. -/
theorem k131_mass_line_int {c : ℝ} (hl : -(3 / 4 : ℝ) ≤ c) (hu : c ≤ 3 / 4) :
    MeasureTheory.Integrable (fun t : ℝ ↦ k131MassFn ((c : ℂ) + Complex.I * t)) := by
  let s := fun t : ℝ ↦ (c : ℂ) + Complex.I * t
  have hre (t : ℝ) : (s t).re = c := by
    simp only [s, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, zero_mul, mul_zero, sub_zero, add_zero]
  have him (t : ℝ) : (s t).im = t := by
    simp only [s, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add]
  have hc : Continuous (fun t ↦ k131MassFn (s t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have h :=
      k131_mass_differentiable (s := s t)
        (by
          rw [hre]; exact hl)
        (by
          rw [hre]; exact hu)
    apply h.continuousAt.comp
    dsimp only [s]
    fun_prop
  obtain ⟨C, hC, hb⟩ := k131_mass_decay
  refine (integrable_inv_one_add_sq.const_mul C).mono' hc.aestronglyMeasurable ?_
  apply MeasureTheory.ae_of_all _
  intro t
  have hd :=
    hb (s t)
      (by
        rw [hre]; exact hl)
      (by
        rw [hre]; exact hu)
  refine hd.trans ?_
  rw [Complex.sq_norm, Complex.normSq_apply, hre, him, ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_left hC.le (by positivity) (by nlinarith only [sq_nonneg c])

private noncomputable def k131MassHalf (a : ℝ) (j : ℕ) (u : ℝ) : ℂ :=
  (u : ℂ) ^ (a : ℂ) • Analysis.mellinLogPowerWeight j u

private theorem k131_mass_half_mellin (a : ℝ) (j : ℕ) {s : ℂ} (hs : 0 < (s + (a : ℂ)).re) :
    HasMellin (k131MassHalf a j) s ((j.factorial : ℂ) / (s + (a : ℂ)) ^ (j + 1)) := by
  have h := Analysis.hasMellin_logPowerWeight j hs
  refine ⟨MellinConvergent.cpow_smul.mpr h.1, ?_⟩
  change mellin (fun u : ℝ ↦ (u : ℂ) ^ (a : ℂ) • Analysis.mellinLogPowerWeight j u) s = _
  rw [mellin_cpow_smul, h.2]

private theorem k131_mass_half_below (a : ℝ) (j : ℕ) {u : ℝ} (hu : 0 < u) (h₁ : u ≤ 1) :
    k131MassHalf a j u = ((Real.exp (-a * |Real.log u|) * |Real.log u| ^ j : ℝ) : ℂ) := by
  have hi : u ∈ Set.Ioc (0 : ℝ) 1 := ⟨hu, h₁⟩
  have he : (u : ℂ) ^ (a : ℂ) = (Real.exp (Real.log u * a) : ℂ) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hu.ne'), ← Complex.ofReal_log hu.le,
      Complex.ofReal_exp, Complex.ofReal_mul]
  simp only [k131MassHalf, Analysis.logPowerWeight_eq_smul, Analysis.mellinWeightZero,
    Set.indicator_of_mem hi, Complex.real_smul, smul_eq_mul, mul_one, he,
    abs_of_nonpos (Real.log_nonpos hu.le h₁), show -a * -Real.log u = Real.log u * a by ring,
    Complex.ofReal_mul, Complex.ofReal_pow]

private theorem k131_mass_half_above (a : ℝ) (j : ℕ) {u : ℝ} (hu : 1 < u) :
    k131MassHalf a j u = 0 := by
  have hi : u ∉ Set.Ioc (0 : ℝ) 1 := fun h ↦ hu.not_ge h.2
  simp only [k131MassHalf, Analysis.logPowerWeight_eq_smul, Analysis.mellinWeightZero,
    Set.indicator_of_notMem hi, smul_zero]

/-- The two-sided exponential log monomial has the two reciprocal
Mellin poles, at a and -a. The value at one is the continuous representative. -/
theorem k131_bilateral_mellin {a : ℝ} (j : ℕ) {s : ℂ} (hl : -a < s.re) (hu : s.re < a) :
    HasMellin (fun u : ℝ ↦ ((Real.exp (-a * |Real.log u|) * |Real.log u| ^ j : ℝ) : ℂ)) s
      ((j.factorial : ℂ) / ((a : ℂ) + s) ^ (j + 1) +
        (j.factorial : ℂ) / ((a : ℂ) - s) ^ (j + 1)) := by
  let F := k131MassHalf a j
  have hp : 0 < (s + (a : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith only [hl]
  have hm : 0 < (-s + (a : ℂ)).re := by
    simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re]
    linarith only [hu]
  have h₁ := k131_mass_half_mellin a j hp
  have h₂ := k131_mass_half_mellin a j hm
  have hInv : MellinConvergent (fun u : ℝ ↦ F u⁻¹) s := by
    simpa only [Real.rpow_neg_one, Complex.ofReal_neg, Complex.ofReal_one, div_neg, div_one] using
      (MellinConvergent.comp_rpow (f := F) (s := s) (a := -1) (by norm_num only)).mpr
        (by simpa only [Complex.ofReal_neg, Complex.ofReal_one, div_neg, div_one] using h₂.1)
  have h := hasMellin_add h₁.1 hInv
  have he :
    (fun u : ℝ ↦ (u : ℂ) ^ (s - 1) • (F u + F u⁻¹)) =ᵐ[MeasureTheory.volume.restrict (Set.Ioi 0)]
      (fun u : ℝ ↦
        (u : ℂ) ^ (s - 1) • ((Real.exp (-a * |Real.log u|) * |Real.log u| ^ j : ℝ) : ℂ)) := by
    filter_upwards [MeasureTheory.Measure.ae_ne _ (1 : ℝ),
      MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hne hu₀
    have hpos := Set.mem_Ioi.mp hu₀
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · simp only [F, k131_mass_half_below a j hpos hlt.le,
        k131_mass_half_above a j ((one_lt_inv₀ hpos).mpr hlt), add_zero]
    · simp only [F, k131_mass_half_above a j hgt, zero_add,
        k131_mass_half_below a j (inv_pos.mpr hpos) ((inv_lt_one₀ hpos).mpr hgt).le, Real.log_inv,
        abs_neg]
  refine ⟨h.1.congr he, ?_⟩
  have hM := MeasureTheory.integral_congr_ae he
  change
    mellin (fun u ↦ F u + F u⁻¹) s =
      mellin (fun u : ℝ ↦ ((Real.exp (-a * |Real.log u|) * |Real.log u| ^ j : ℝ) : ℂ)) s at hM
  rw [← hM, h.2, mellin_comp_inv, h₁.2, h₂.2, add_comm s, sub_eq_neg_add]

/-- The continuous two-sided profile for a pair of symmetrized reciprocal
monomials. Lowering one power at a time implements partial fractions. -/
noncomputable def k131SymmetricProfile (a : ℝ) (m n : ℕ) (u : ℝ) : ℝ :=
  match m, n with
  | 0, 0 => 0
  | 0, k + 1 | k + 1, 0 => Real.exp (-a * |Real.log u|) * |Real.log u| ^ k / k.factorial
  | m + 1, n + 1 =>
    (k131SymmetricProfile a m (n + 1) u + k131SymmetricProfile a (m + 1) n u) / (2 * a)
termination_by m + n
decreasing_by
  · exact Nat.add_lt_add_right (Nat.lt_succ_self _) _
  · exact Nat.add_lt_add_left (Nat.lt_succ_self _) _

private theorem k131_mellin_add {f g : ℝ → ℂ} {s x y : ℂ} (hf : HasMellin f s x)
    (hg : HasMellin g s y) : HasMellin (fun u ↦ f u + g u) s (x + y) := by
  rw [← hf.2, ← hg.2]
  exact hasMellin_add hf.1 hg.1

private theorem k131_symmetric_init {a : ℝ} {s : ℂ} (hl : -a < s.re) (hu : s.re < a) (k : ℕ) :
    HasMellin
      (fun u : ℝ ↦ ((Real.exp (-a * |Real.log u|) * |Real.log u| ^ k / k.factorial : ℝ) : ℂ)) s
      (1 / ((a : ℂ) + s) ^ (k + 1) + 1 / ((a : ℂ) - s) ^ (k + 1)) := by
  have h := k131_bilateral_mellin k hl hu
  have hk : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h' := hasMellin_const_smul h.1 (k.factorial : ℂ)⁻¹
  rw [h.2] at h'
  convert h' using 1
  · funext u
    push_cast
    simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]
  · simp only [smul_eq_mul, mul_add, ← mul_div_assoc, inv_mul_cancel₀ hk]

/-- The symmetric profile transforms to the sum of the two reciprocal
products for every positive total degree on the strip between the poles. -/
theorem k131_symmetric_profile_mellin {a : ℝ} {s : ℂ} (hl : -a < s.re) (hu : s.re < a) (m n : ℕ)
    (hmn : 0 < m + n) :
    HasMellin (fun u : ℝ ↦ (k131SymmetricProfile a m n u : ℂ)) s
      (1 / (((a : ℂ) + s) ^ m * ((a : ℂ) - s) ^ n) +
        1 / (((a : ℂ) + s) ^ n * ((a : ℂ) - s) ^ m)) := by
  induction m, n using k131SymmetricProfile.induct with
  | case1 => exact (Nat.lt_irrefl 0 hmn).elim
  | case2 k =>
    simpa only [k131SymmetricProfile, pow_zero, one_mul, mul_one, add_comm] using
      k131_symmetric_init hl hu k
  | case3 k =>
    simpa only [k131SymmetricProfile, pow_zero, one_mul, mul_one] using k131_symmetric_init hl hu k
  | case4 m n hm hn =>
    have hm' := hm (Nat.add_pos_right _ (Nat.succ_pos n))
    have hn' := hn (Nat.add_pos_left (Nat.succ_pos m) _)
    have h := k131_mellin_add hm' hn'
    have H := hasMellin_const_smul h.1 ((2 * (a : ℂ))⁻¹)
    rw [h.2] at H
    have ha : 0 < a := by linarith only [hl, hu]
    have hp : (a : ℂ) + s ≠ 0 :=
      Complex.ne_zero_of_re_pos
        (by
          simp only [Complex.add_re, Complex.ofReal_re]
          linarith only [hl])
    have hm₀ : (a : ℂ) - s ≠ 0 :=
      Complex.ne_zero_of_re_pos
        (by
          simp only [Complex.sub_re, Complex.ofReal_re]
          linarith only [hu])
    convert H using 1
    · funext u
      rw [k131SymmetricProfile]
      push_cast
      simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]
    · simp only [smul_eq_mul, pow_succ]
      field_simp [hp, hm₀, Complex.ofReal_ne_zero.mpr ha.ne']
      ring

private theorem k131_mellin_finsum {ι : Type*} (I : Finset ι) (F : ι → ℝ → ℂ) (V : ι → ℂ) (s : ℂ)
    (h : ∀ i ∈ I, HasMellin (F i) s (V i)) :
    HasMellin (fun u ↦ ∑ i ∈ I, F i u) s (∑ i ∈ I, V i) := by
  classical
    induction I using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact
      ⟨by
        simp only [MellinConvergent, smul_zero]; exact MeasureTheory.integrable_zero _ _ _, by
        simp only [mellin, smul_zero, MeasureTheory.integral_zero]⟩
  | @insert i I hi ih =>
    simp only [Finset.sum_insert hi]
    exact
      k131_mellin_add (h i (Finset.mem_insert_self i I))
        (ih (fun j hj ↦ h j (Finset.mem_insert_of_mem hj)))

/-- The continuous inverse profile of the K131 mass kernel is the
signed sum of its nine two-sided reciprocal-power profiles. -/
noncomputable def k131MassProfile (u : ℝ) : ℝ :=
  (gaussianK131Amplitude : ℝ) *
    ∑ i : Fin 9,
      (gammaCoeffs i : ℝ) / 2 * k131SymmetricProfile (27 / 16) (10 - i.val) (10 - i.val) u

/-- The K131 mass profile transforms to the actual rational mass kernel
throughout the strip between its two poles. -/
theorem k131_mass_hasMellin {s : ℂ} (hl : -(27 / 16 : ℝ) < s.re) (hu : s.re < 27 / 16) :
    HasMellin (fun u : ℝ ↦ (k131MassProfile u : ℂ)) s (k131MassFn s) := by
  let a : ℝ := 27 / 16
  let m := fun i : Fin 9 ↦ 10 - i.val
  let F := fun (i : Fin 9) (u : ℝ) ↦
    ((gammaCoeffs i : ℂ) / 2) * (k131SymmetricProfile a (m i) (m i) u : ℂ)
  let V := fun i : Fin 9 ↦ (gammaCoeffs i : ℂ) / (((27 / 16 : ℂ) ^ 2 - s ^ 2) ^ m i)
  have h (i : Fin 9) : HasMellin (F i) s (V i) := by
    have hm : 0 < m i := Nat.sub_pos_of_lt (i.isLt.trans (by decide : 9 < 10))
    have h' := k131_symmetric_profile_mellin hl hu (m i) (m i) (Nat.add_pos_left hm _)
    have he := hasMellin_const_smul h'.1 ((gammaCoeffs i : ℂ) / 2)
    rw [h'.2] at he
    convert he using 1
    have hd : ((a : ℂ) + s) * ((a : ℂ) - s) = (27 / 16 : ℂ) ^ 2 - s ^ 2 := by
      dsimp only [a]
      push_cast
      ring
    dsimp only [V]
    rw [← hd, mul_pow]
    simp only [smul_eq_mul]
    ring
  have hs := k131_mellin_finsum Finset.univ F V s (fun i _ ↦ h i)
  have ha := hasMellin_const_smul hs.1 (((gaussianK131Amplitude : ℝ) : ℂ))
  rw [hs.2] at ha
  simpa only [F, V, a, m, k131MassProfile, k131MassFn, smul_eq_mul, Complex.ofReal_mul,
    Complex.ofReal_sum, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_ratCast] using ha

private theorem k131_symmetric_cont {u : ℝ} (hu : 0 < u) (a : ℝ) (m n : ℕ) :
    ContinuousAt (k131SymmetricProfile a m n) u := by
  induction m, n using k131SymmetricProfile.induct with
  | case1 =>
    change ContinuousAt (fun v : ℝ ↦ k131SymmetricProfile a 0 0 v) u
    simp only [k131SymmetricProfile]
    exact continuousAt_const
  | case2 k =>
    change ContinuousAt (fun v : ℝ ↦ k131SymmetricProfile a 0 (k + 1) v) u
    simp only [k131SymmetricProfile]
    have h := (Real.continuousAt_log hu.ne').abs
    exact ((Real.continuous_exp.continuousAt.comp (h.const_mul (-a))).mul (h.pow k)).div_const _
  | case3 k =>
    change ContinuousAt (fun v : ℝ ↦ k131SymmetricProfile a (k + 1) 0 v) u
    simp only [k131SymmetricProfile]
    have h := (Real.continuousAt_log hu.ne').abs
    exact ((Real.continuous_exp.continuousAt.comp (h.const_mul (-a))).mul (h.pow k)).div_const _
  | case4 m n hm
    hn =>
    change ContinuousAt (fun v : ℝ ↦ k131SymmetricProfile a (m + 1) (n + 1) v) u
    simp only [k131SymmetricProfile]
    exact (hm.add hn).div_const _

private theorem k131_mass_profile_cont {u : ℝ} (hu : 0 < u) : ContinuousAt k131MassProfile u := by
  unfold k131MassProfile
  apply ContinuousAt.const_mul
  have h (I : Finset (Fin 9)) :
    ContinuousAt
      (fun v ↦
        ∑ i ∈ I,
          (gammaCoeffs i : ℝ) / 2 * k131SymmetricProfile (27 / 16) (10 - i.val) (10 - i.val) v)
      u := by
    induction I using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact continuousAt_const
    | @insert i I hi ih =>
      simp only [Finset.sum_insert hi]
      exact ((k131_symmetric_cont hu _ _ _).const_mul _).add ih
  exact h Finset.univ

/-- On every contour line in the closed strip, Mellin inversion of
the symmetric mass kernel gives the continuous real K131 profile. -/
theorem k131_mass_inversion {c u : ℝ} (hl : -(3 / 4 : ℝ) ≤ c) (hu : c ≤ 3 / 4) (hx : 0 < u) :
    Analysis.inverseMellin k131MassFn c u = (k131MassProfile u : ℂ) := by
  let f := fun v : ℝ ↦ (k131MassProfile v : ℂ)
  have hre (t : ℝ) : ((c : ℂ) + t * Complex.I).re = c := by
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      zero_mul, mul_zero, sub_zero, add_zero]
  have h (t : ℝ) :
    HasMellin f ((c : ℂ) + t * Complex.I) (k131MassFn ((c : ℂ) + t * Complex.I)) := by
    apply k131_mass_hasMellin <;> rw [hre] <;> linarith only [hl, hu]
  have hv : Complex.VerticalIntegrable k131MassFn c := by
    simpa only [Complex.VerticalIntegrable, mul_comm Complex.I] using k131_mass_line_int hl hu
  have hi := hv.congr (Filter.Eventually.of_forall fun t ↦ (h t).2.symm)
  have h0 : MellinConvergent f (c : ℂ) := by
    simpa only [Complex.ofReal_zero, zero_mul, add_zero] using (h 0).1
  have hc : ContinuousAt f u :=
    Complex.continuous_ofReal.continuousAt.comp (k131_mass_profile_cont hx)
  change Analysis.inverseMellin k131MassFn c u = f u
  rw [Analysis.inverseMellin_eq_mellinInv, ← mellinInv_mellin_eq c f hx h0 hi hc]
  unfold mellinInv
  congr 1
  exact
    MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun t ↦
        congrArg (fun z : ℂ ↦ (u : ℂ) ^ (-((c : ℂ) + t * Complex.I)) • z) (h t).2.symm)

private def k131OnePoleCoeff (m n k : ℕ) : ℚ :=
  if k < m then
    ((m + n - k - 2).choose (n - 1) : ℚ) / ((k.factorial : ℚ) * (27 / 8 : ℚ) ^ (m + n - k - 1))
  else 0

private def k131SymCoeff (m n k : ℕ) : ℚ :=
  match m, n with
  | 0, 0 => 0
  | 0, j + 1 | j + 1, 0 => if k = j then 1 / (j.factorial : ℚ) else 0
  | m + 1, n + 1 => k131OnePoleCoeff (m + 1) (n + 1) k + k131OnePoleCoeff (n + 1) (m + 1) k

private theorem k131_sym_coeff_recur :
    ∀ (m n k : Fin 10),
      k131SymCoeff (m.val + 1) (n.val + 1) k =
        (k131SymCoeff m (n.val + 1) k + k131SymCoeff (m.val + 1) n k) / (27 / 8) := by
  decide +kernel

private theorem k131_sym_profile_coeff (m n : ℕ) (hm : m ≤ 10) (hn : n ≤ 10) (u : ℝ) :
    k131SymmetricProfile (27 / 16) m n u =
      Real.exp (-(27 / 16 : ℝ) * |Real.log u|) *
        ∑ k : Fin 10, (k131SymCoeff m n k : ℝ) * |Real.log u| ^ k.val := by
  let v := |Real.log u|
  let E := Real.exp (-(27 / 16 : ℝ) * v)
  have hbase (j : ℕ) (hj : j < 10) :
    E * v ^ j / j.factorial =
      E *
        ∑ k : Fin 10, ((if k.val = j then (1 / (j.factorial : ℚ)) else 0 : ℚ) : ℝ) * v ^ k.val := by
    rw [Finset.sum_eq_single ⟨j, hj⟩]
    · norm_num only [ite_true, Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
      ring
    · intro k _ hk
      have h : k.val ≠ j := fun he ↦ hk (Fin.ext he)
      simp only [ite_eq_right h, Rat.cast_zero, zero_mul]
    · intro h
      exact (h (Finset.mem_univ _)).elim
  induction m, n using k131SymmetricProfile.induct with
  | case1 =>
    simp only [k131SymmetricProfile, k131SymCoeff, Rat.cast_zero, zero_mul, Finset.sum_const_zero,
      mul_zero]
  | case2 j =>
    simpa only [k131SymmetricProfile, k131SymCoeff, E, v] using hbase j (Nat.lt_of_succ_le hn)
  | case3 j =>
    simpa only [k131SymmetricProfile, k131SymCoeff, E, v] using hbase j (Nat.lt_of_succ_le hm)
  | case4 m n ih ih' =>
    have hm' := Nat.lt_of_succ_le hm
    have hn' := Nat.lt_of_succ_le hn
    rw [k131SymmetricProfile, ih hm'.le hn, ih' hm hn'.le]
    have h (k : Fin 10) :
      (k131SymCoeff (m + 1) (n + 1) k : ℝ) =
        ((k131SymCoeff m (n + 1) k : ℝ) + (k131SymCoeff (m + 1) n k : ℝ)) / (27 / 8) := by
      simpa only [Rat.cast_div, Rat.cast_add, Rat.cast_ofNat] using
        congrArg (fun x : ℚ ↦ (x : ℝ)) (k131_sym_coeff_recur ⟨m, hm'⟩ ⟨n, hn'⟩ k)
    simp only [h, div_mul_eq_mul_div, ← Finset.sum_div, add_mul, Finset.sum_add_distrib]
    ring

private theorem k131_sym_diagonal_coeff :
    ∀ (i : Fin 9) (k : Fin 10),
      gammaCoeffs i / 2 * k131SymCoeff (10 - i.val) (10 - i.val) k =
        if k.val < 10 - i.val then fourierTerm i k / 2 else 0 := by
  unfold fourierTerm
  decide +kernel

private def k131FourierCoeff (k : ℕ) : ℚ :=
  ∑ i : Fin 9, if k < 10 - i.val then fourierTerm i k else 0

private theorem k131_fourier_coeff_nonneg : ∀ k : Fin 10, 0 ≤ k131FourierCoeff k := by
  unfold k131FourierCoeff fourierTerm
  decide +kernel

private theorem k131_fourier_eval (v : ℝ) :
    gaussianK131Fourier.eval v =
      (gaussianK131Amplitude : ℝ) * ∑ k : Fin 10, (k131FourierCoeff k : ℝ) * v ^ k.val := by
  simp only [gaussianK131Fourier, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial, k131FourierCoeff, Rat.cast_sum, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_eq_sum_range
      (fun k : ℕ ↦ ((if k < 10 - i.val then fourierTerm i k else 0 : ℚ) : ℝ) * v ^ k)]
  apply Finset.sum_subset_zero_on_sdiff (Finset.range_mono (Nat.sub_le 10 i.val))
  · intro k hk
    have h : ¬k < 10 - i.val := fun h ↦ (Finset.mem_sdiff.mp hk).2 (Finset.mem_range.mpr h)
    simp only [ite_eq_right h, Rat.cast_zero, zero_mul]
  · intro k hk
    simp only [ite_eq_left (Finset.mem_range.mp hk)]

/-- The inverse Mellin mass profile agrees with one half of the
manuscript Fourier polynomial times the logarithmic exponential. -/
theorem k131_mass_profile_fourier (u : ℝ) :
    k131MassProfile u =
      Real.exp (-(27 / 16 : ℝ) * |Real.log u|) * gaussianK131Fourier.eval |Real.log u| / 2 := by
  let v := |Real.log u|
  let E := Real.exp (-(27 / 16 : ℝ) * v)
  have h (i : Fin 9) (k : Fin 10) :
    ((gammaCoeffs i : ℝ) / 2) * (k131SymCoeff (10 - i.val) (10 - i.val) k : ℝ) =
      ((if k.val < 10 - i.val then fourierTerm i k else 0 : ℚ) : ℝ) / 2 := by
    have h' := congrArg (fun x : ℚ ↦ (x : ℝ)) (k131_sym_diagonal_coeff i k)
    by_cases hk : k.val < 10 - i.val
    · simpa only [ite_eq_left hk, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using h'
    · simpa only [ite_eq_right hk, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_zero,
        zero_div] using h'
  unfold k131MassProfile
  simp only [k131_sym_profile_coeff _ _ (Nat.sub_le _ _) (Nat.sub_le _ _), k131_fourier_eval]
  change
    _ *
        (∑ i : Fin 9,
          (gammaCoeffs i : ℝ) / 2 *
            (E * ∑ k : Fin 10, (k131SymCoeff (10 - i.val) (10 - i.val) k : ℝ) * v ^ k.val)) =
      _
  simp only [mul_left_comm _ E, ← mul_assoc, Finset.mul_sum, h]
  rw [Finset.sum_comm]
  simp only [k131FourierCoeff, Rat.cast_sum, Finset.sum_mul, Finset.mul_sum, div_eq_mul_inv]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [E, v]
  ring_nf

/-- The K131 mass profile is nonnegative, by the checked coefficients
of its Fourier polynomial. -/
theorem k131_mass_profile_nonneg (u : ℝ) : 0 ≤ k131MassProfile u := by
  rw [k131_mass_profile_fourier, k131_fourier_eval]
  have hA : 0 ≤ (gaussianK131Amplitude : ℝ) := Rat.cast_nonneg.mpr (by decide +kernel)
  have h :=
    Finset.sum_nonneg (s := (Finset.univ : Finset (Fin 10)))
      (fun k _ ↦
        mul_nonneg (Rat.cast_nonneg.mpr (k131_fourier_coeff_nonneg k))
          (pow_nonneg (abs_nonneg (Real.log u)) k.val))
  exact div_nonneg (mul_nonneg (Real.exp_pos _).le (mul_nonneg hA h)) (by norm_num only)

/-- The symmetric K131 mass test is admissible in the completed-L
contour formula. Its transform is the nonnegative Fourier profile. -/
noncomputable def k131MassKernel : LLS.PaperStatements.MellinKernel where
  function := k131MassFn
  delta := 1 / 8
  delta_pos := by norm_num only
  region := {z | z.re ∈ Set.Ioo (-(3 / 4 : ℝ)) (3 / 4)}
  region_open := isOpen_Ioo.preimage Complex.continuous_re
  strip_subset := by
    intro z hz
    change -1 / 2 - 1 / 8 < z.re ∧ z.re ≤ 1 / 2 + 1 / 8 at hz
    exact ⟨by linarith only [hz.1], by linarith only [hz.2]⟩
  holomorphic := fun z hz ↦ (k131_mass_differentiable hz.1.1.le hz.1.2.le).differentiableWithinAt
  regularized := fun z ↦ (z + 1 / 2) * k131MassFn z
  regularized_holomorphic := fun z hz ↦
    (((differentiableAt_id (𝕜 := ℂ) (x := z)).add_const _).mul
        (k131_mass_differentiable hz.1.le hz.2.le)).differentiableWithinAt
  regularized_eq := fun _ _ _ ↦ rfl
  decay := by
    intro η hη
    obtain ⟨C, hC, h⟩ := k131_mass_decay
    exact ⟨C, hC, fun s hs _ ↦ h s hs.1.le hs.2.le⟩
  mellin_integrable := fun _ _ hl hu hx ↦
    LLS.PaperStatements.integrable_inverseMellin_of_line hx
      (k131_mass_line_int (by linarith only [hl]) (by linarith only [hu]))
  mellin_eq := by
    intro c u hl hu hx
    rw [k131_mass_inversion (by linarith only [hl]) (by linarith only [hu]) hx,
      k131_mass_inversion (by norm_num only) (by norm_num only) hx]
  mellin_nonneg := by
    intro u hx
    rw [k131_mass_inversion (by norm_num only) (by norm_num only) hx, Complex.ofReal_re]
    exact k131_mass_profile_nonneg u
  mellin_nonzero := by
    refine ⟨1, zero_lt_one, ?_⟩
    rw [k131_mass_inversion (by norm_num only) (by norm_num only) zero_lt_one, Complex.ofReal_re,
      k131_mass_profile_fourier, Real.log_one, abs_zero, mul_zero, Real.exp_zero, one_mul,
      gaussian_k131_fourier_zero]
    norm_num only
  mellin_real := by
    intro u hx
    rw [k131_mass_inversion (by norm_num only) (by norm_num only) hx, Complex.ofReal_im]

/-- Above height six, the absolute K131 mass kernel is at most one
hundredth of the inverse critical-line squared norm. -/
theorem k131_mass_axis_cap {t : ℝ} (ht : 6 ≤ |t|) :
    ‖k131MassFn (Complex.I * (t : ℂ))‖ ≤ 1 / (100 * (t ^ 2 + 1 / 4)) := by
  let d := t ^ 2 + (27 / 16 : ℝ) ^ 2
  have ht₂ : (36 : ℝ) ≤ t ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 6) ht 2
    norm_num only [sq_abs] at h
    exact h
  have hd : 36 ≤ d := by
    dsimp only [d]; linarith only [ht₂]
  have hd₀ : 0 < d := (by norm_num only : (0 : ℝ) < 36).trans_le hd
  have hden : (27 / 16 : ℂ) ^ 2 - (Complex.I * (t : ℂ)) ^ 2 = (d : ℂ) := by
    dsimp only [d]
    push_cast
    rw [mul_pow, Complex.I_sq]
    ring
  have hA : 0 ≤ (gaussianK131Amplitude : ℝ) := Rat.cast_nonneg.mpr (by decide +kernel)
  let S := ∑ i : Fin 9, |(gammaCoeffs i : ℝ)| / (36 : ℝ) ^ (9 - i.val)
  have hc : (gaussianK131Amplitude : ℝ) * S ≤ 1 / 100 := by
    have h :
      gaussianK131Amplitude * (∑ i : Fin 9, |gammaCoeffs i| / (36 : ℚ) ^ (9 - i.val)) ≤
        1 / 100 := by
      decide +kernel
    simpa only [S, Rat.cast_mul, Rat.cast_sum, Rat.cast_abs, Rat.cast_pow, Rat.cast_div,
      Rat.cast_one, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr h
  have hterm (i : Fin 9) :
    ‖(gammaCoeffs i : ℂ) / (d : ℂ) ^ (10 - i.val)‖ ≤
      (|(gammaCoeffs i : ℝ)| / (36 : ℝ) ^ (9 - i.val)) / d := by
    have he : 10 - i.val = (9 - i.val) + 1 := by
      rw [show (10 : ℕ) = 1 + 9 by decide, Nat.add_sub_assoc i.isLt.le, add_comm]
    rw [norm_div, norm_pow, ← Complex.ofReal_ratCast, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hd₀.le, he, pow_succ, ← div_div]
    exact
      div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
          (pow_le_pow_left₀ (by norm_num only) hd _))
        hd₀.le
  unfold k131MassFn
  rw [hden, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hA]
  calc
    _ ≤ (gaussianK131Amplitude : ℝ) * (S / d) := by
      apply mul_le_mul_of_nonneg_left _ hA
      refine (norm_sum_le _ _).trans ?_
      dsimp only [S]
      rw [Finset.sum_div]
      exact Finset.sum_le_sum (fun i _ ↦ hterm i)
    _ ≤ (1 / 100 : ℝ) / d := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right hc hd₀.le
    _ ≤ _ := by
      rw [div_div]
      exact
        div_le_div_of_nonneg_left zero_le_one (by positivity)
          (mul_le_mul_of_nonneg_left
            (by
              dsimp only [d]; linarith only)
            (by norm_num only))

end PseudoPrime.PrimeTestBounds.MillerRabin
