/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Shift
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosineCore663
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Shift
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterForward656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAuxiliary656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosineSeries656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosineCore663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAuxSlope663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterThetaPoly663

/-! # Finite Gram comparison with the K197 coefficients -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Apply the linear and quadratic K197 frequency combination to a profile. -/
@[expose]
noncomputable def gaussianAuxMix197 (f : ℚ → ℝ) : ℝ :=
  (∑ i,
        ∑ j,
          (gaussianCoeff197 i : ℝ) * (gaussianCoeff197 j : ℝ) *
            f (quarterFreq663 i - quarterFreq663 j)) /
      2 -
    ∑ i, (gaussianCoeff197 i : ℝ) * f (quarterFreq663 i)

/-- Under GRH and prime agreement, the finite Gram inequality bounds the
main forward sum with the signed shifted remainders with the K197 coefficients. -/
theorem gaussian_single_forward_197 {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hn : χ ≠ 1)
    {r : ℝ} (hr : 328 ≤ r) (hpass : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ r ^ 2 → χ p = 1) :
    (∑' n, quarterKernel656.summand χ (r ^ 2) n).re + gaussianShiftedForward197 χ r ≤
      quarterCosineContour656 χ 0 + (contourRemainder656 χ (r ^ 2)).re +
        gaussianAuxMix197 (fun t ↦ quarterCosineContour656 χ |(t : ℝ)|) := by
  have hX : (1 : ℝ) ≤ r ^ 2 :=
    (by norm_num only : (1 : ℝ) ≤ 328 ^ 2).trans (pow_le_pow_left₀ (by norm_num only) hr 2)
  have hx := zero_lt_one.trans_le hX
  let Z := quarterKernel656.oscillatingZeroTerm χ (r ^ 2)
  have hZ :=
    LLS.PaperStatements.MellinKernel.summable_oscillatingZeroTerm quarterKernel656 hq hG hp hn
      (inv_ne_one.mpr hn) hx
  have h :=
    finite_frequency_weighted_le (fun ρ ↦ ‖Z ρ‖) (fun ρ ↦ (Z ρ).arg) Complex.im
      (fun ρ ↦ norm_nonneg (Z ρ)) hZ.norm (fun i ↦ (quarterFreq663 i : ℝ))
      (fun i ↦ (gaussianCoeff197 i : ℝ))
  dsimp only at h
  have hf : ∀ i, (21 / 8 : ℚ) ≤ quarterFreq663 i := by decide +kernel
  have hfR (i : Fin 6) : (21 / 8 : ℝ) ≤ (quarterFreq663 i : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (hf i)
  have hB (i : Fin 6) :=
    quarter_cosine_contour_656 hq hG hp hn hx ((by norm_num only : (0 : ℝ) ≤ 21 / 8).trans (hfR i))
  have hm := quarter_cosine_contour_656 hq hG hp hn hx (le_refl (0 : ℝ))
  simp only [zero_mul, Real.cos_zero, mul_one] at hm
  have ht (i : Fin 6) :
    (∑' ρ : ℂ, ‖Z ρ‖ * Real.cos ((Z ρ).arg - (quarterFreq663 i : ℝ) * ρ.im)) =
      (contourRemainder656 χ (r ^ 2 * Real.exp (-(quarterFreq663 i : ℝ)))).re -
        (∑' n,
            quarterKernel656.summand (1 : DirichletCharacter ℂ 1)
              (r ^ 2 * Real.exp (-(quarterFreq663 i : ℝ))) n).re := by
    dsimp only [Z]
    rw [shifted_phase_eq hq hG hp hn (inv_ne_one.mpr hn) hx,
      zero_re_eq_contour hq hG hp hn (quarter_aux_scale_ge_one_663 hr i),
      quarter_shifted_forward_656 χ hx (hfR i) hpass]
  have hz : (∑' ρ : ℂ, ‖Z ρ‖ * Real.cos (Z ρ).arg) = (∑' ρ : ℂ, Z ρ).re := by
    rw [Complex.re_tsum hZ]
    exact tsum_congr (fun ρ ↦ Complex.norm_mul_cos_arg (Z ρ))
  rw [hz] at h
  simp only [ht, Z, hB, quarter_cosine_abs_contour_656 hq hG hp hn hx, hm,
    zero_re_eq_contour hq hG hp hn hX, mul_add, Finset.sum_add_distrib] at h
  unfold gaussianShiftedForward197 gaussianAuxMix197
  simp only [Rat.cast_sub, abs_of_nonneg ((by norm_num only : (0 : ℝ) ≤ 21 / 8).trans (hfR _))]
  linarith only [h]

private theorem aux_mix_tsum {ι : Type*} (F : ℚ → ι → ℝ) (hf : ∀ s, Summable (F s)) :
    gaussianAuxMix197 (fun s ↦ ∑' n, F s n) = ∑' n, gaussianAuxMix197 (fun s ↦ F s n) := by
  let f := fun i ↦ F (quarterFreq663 i)
  let g := fun i j ↦ F (quarterFreq663 i - quarterFreq663 j)
  let c := fun i : Fin 6 ↦ (gaussianCoeff197 i : ℝ)
  have hp (i j : Fin 6) : Summable (fun n ↦ c i * c j * g i j n) := (hf _).mul_left _
  have hrow (i : Fin 6) : Summable (fun n ↦ ∑ j, c i * c j * g i j n) :=
    summable_sum (fun j _ ↦ hp i j)
  have hP : Summable (fun n ↦ ∑ i, ∑ j, c i * c j * g i j n) := summable_sum (fun i _ ↦ hrow i)
  have hS (i : Fin 6) : Summable (fun n ↦ c i * f i n) := (hf _).mul_left _
  have hSS : Summable (fun n ↦ ∑ i, c i * f i n) := summable_sum (fun i _ ↦ hS i)
  have h := Summable.tsum_sub (hP.div_const 2) hSS
  rw [tsum_div_const, Summable.tsum_finsetSum (fun i _ ↦ hrow i),
    Summable.tsum_finsetSum (fun i _ ↦ hS i)] at h
  simpa only [gaussianAuxMix197, f, g, c, Summable.tsum_finsetSum (fun j _ ↦ hp _ j),
    tsum_mul_left] using h.symm

private theorem aux_frequency_abs_le (i : Fin 6) : |(quarterFreq663 i : ℝ)| ≤ 10 := by
  have h : ∀ j, |quarterFreq663 j| ≤ 10 := by decide +kernel
  exact_mod_cast h i

private theorem aux_frequency_diff_le (i j : Fin 6) :
    |((quarterFreq663 i - quarterFreq663 j : ℚ) : ℝ)| ≤ 10 := by
  have h : ∀ k l, |quarterFreq663 k - quarterFreq663 l| ≤ 10 := by decide +kernel
  exact_mod_cast h i j

/-- Pairing reciprocal scales and summing all frequencies gives the auxiliary
Euler polynomial weighted by the trace deficit. -/
theorem gaussian_cosine_tail_eq_197 {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) {X : ℝ}
    (hX : (322 : ℝ) ^ 2 ≤ X) :
    gaussianAuxMix197 (fun s ↦ quarterCosineTail656 a b c X (s : ℝ)) =
      ∑' n : { n : ℕ // ⌊X⌋₊ < n },
        (3 - ((a n.val).re + (b n.val).re + (c n.val).re)) *
          (ArithmeticFunction.vonMangoldt n.val / (n.val : ℝ) ^ (8 / 5 : ℝ)) *
          (gaussianProfile197 (Real.log n.val) - quarterAuxProfile656 (Real.log n.val)) := by
  let N := { n : ℕ // ⌊X⌋₊ < n }
  let D := fun n : N ↦ 3 - ((a n.val).re + (b n.val).re + (c n.val).re)
  let F := fun s : ℚ ↦ fun n : N ↦
    D n *
      (ArithmeticFunction.vonMangoldt n.val / Real.sqrt n.val *
        (quarterSymmetricProfile656 (n.val / Real.exp |(s : ℝ)|) +
          quarterSymmetricProfile656 (n.val / (Real.exp |(s : ℝ)|)⁻¹)))
  have hF (s : ℚ) : Summable (F s) := by
    have hp := Real.exp_pos |s|
    have ha := (quarter_trace_tail_hasSum_656 a b c X hp).summable
    have hb := (quarter_trace_tail_hasSum_656 a b c X (inv_pos.mpr hp)).summable
    dsimp only at ha hb
    apply (ha.add hb).congr
    intro n
    simp only [F, D, mul_add]
  change gaussianAuxMix197 (fun s ↦ ∑' n, F s n) = _
  rw [aux_mix_tsum F hF]
  apply tsum_congr
  intro n
  have hX₀ := (by norm_num only : (0 : ℝ) < 322 ^ 2).trans_le hX
  have hn := (Nat.floor_lt hX₀.le).mp n.property
  have hn₀ := hX₀.trans hn
  have hlog : 10 ≤ Real.log n.val := by
    have he : Real.exp 10 ≤ (322 : ℝ) ^ 2 := by
      rw [show (10 : ℝ) = 1 * ((10 : ℕ) : ℝ) by norm_num only, Real.exp_mul_natCast]
      exact
        (pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le _).trans (by norm_num only)
    exact (Real.le_log_iff_exp_le hn₀).mpr (he.trans (hX.trans hn.le))
  have hscale :
    Real.exp (-(11 / 10) * Real.log n.val) / Real.sqrt n.val = ((n.val : ℝ) ^ (8 / 5 : ℝ))⁻¹ := by
    rw [mul_comm (-(11 / 10 : ℝ)), ← Real.rpow_def_of_pos hn₀, Real.sqrt_eq_rpow, ←
      Real.rpow_sub hn₀, show -(11 / 10 : ℝ) - 1 / 2 = -(8 / 5) by norm_num only,
      Real.rpow_neg hn₀.le]
  let K := D n * (ArithmeticFunction.vonMangoldt n.val / (n.val : ℝ) ^ (8 / 5 : ℝ))
  have he (s : ℚ) (hs : |(s : ℝ)| ≤ 10) : F s n = K * quarterAuxPair656 s (Real.log n.val) := by
    dsimp only [F, K]
    rw [quarter_cosine_profile_pair_656 hn₀ (hs.trans hlog)]
    linear_combination
      (D n * ArithmeticFunction.vonMangoldt n.val * quarterAuxPair656 s (Real.log n.val)) * hscale
  change
    gaussianAuxMix197 (fun s ↦ F s n) =
      K * (gaussianProfile197 (Real.log n.val) - quarterAuxProfile656 (Real.log n.val))
  unfold gaussianProfile197 gaussianAuxMix197
  have h₁ (i : Fin 6) :
    (gaussianCoeff197 i : ℝ) * F (quarterFreq663 i) n =
      K * ((gaussianCoeff197 i : ℝ) * quarterAuxPair656 (quarterFreq663 i) (Real.log n.val)) := by
    rw [he _ (aux_frequency_abs_le i), mul_left_comm]
  have h₂ (i j : Fin 6) :
    (gaussianCoeff197 i : ℝ) * (gaussianCoeff197 j : ℝ) *
        F (quarterFreq663 i - quarterFreq663 j) n =
      K *
        ((gaussianCoeff197 i : ℝ) * (gaussianCoeff197 j : ℝ) *
          quarterAuxPair656 ((quarterFreq663 i - quarterFreq663 j : ℚ) : ℝ) (Real.log n.val)) := by
    rw [he _ (aux_frequency_diff_le i j), mul_left_comm]
  simp only [h₁, h₂, ← Finset.mul_sum]
  ring

private theorem gaussian_mix_add (f g : ℚ → ℝ) :
    gaussianAuxMix197 (fun t ↦ f t + g t) = gaussianAuxMix197 f + gaussianAuxMix197 g := by
  unfold gaussianAuxMix197
  simp only [mul_add, Finset.sum_add_distrib]
  ring

/-- Sum the three K197 Gram inequalities and replace the mixed cosine
terms with their conductor core and paired signed Euler tail. -/
theorem gaussian_three_gram_197 {p q k : ℕ} [NeZero p] [NeZero q] [NeZero k]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ k}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hk : 2 ≤ k)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r : ℝ} (hr : 328 ≤ r)
    (hpa : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → a n = 1)
    (hpb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → b n = 1)
    (hpc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → c n = 1) :
    (∑' n, quarterKernel656.summand a (r ^ 2) n).re +
        (∑' n, quarterKernel656.summand b (r ^ 2) n).re +
        (∑' n, quarterKernel656.summand c (r ^ 2) n).re +
        (gaussianShiftedForward197 a r + gaussianShiftedForward197 b r +
          gaussianShiftedForward197 c r) ≤
      quarterCosineContour656 a 0 + quarterCosineContour656 b 0 + quarterCosineContour656 c 0 +
        ((contourRemainder656 a (r ^ 2)).re + (contourRemainder656 b (r ^ 2)).re +
          (contourRemainder656 c (r ^ 2)).re) +
        gaussianAuxMix197
          (fun t ↦ quarterCosineCore656 (Real.log p + Real.log q + Real.log k) (t : ℝ)) +
        ∑' n : { n : ℕ // ⌊r ^ 2⌋₊ < n },
          (3 - ((a n.val).re + (b n.val).re + (c n.val).re)) *
            (ArithmeticFunction.vonMangoldt n.val / (n.val : ℝ) ^ (8 / 5 : ℝ)) *
            (gaussianProfile197 (Real.log n.val) - quarterAuxProfile656 (Real.log n.val)) := by
  have hX := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 322) (by linarith only [hr] : 322 ≤ r) 2
  have he (t : ℚ) := quarter_three_cosine_split_656 ha hb hc (sq_nonneg r) (t : ℝ) hpa hpb hpc
  have h := congrArg gaussianAuxMix197 (funext he)
  rw [gaussian_mix_add, gaussian_mix_add, gaussian_mix_add,
    gaussian_cosine_tail_eq_197 a b c hX] at h
  linarith only [h, gaussian_single_forward_197 hp hG ha.1 ha.2.1 hr hpa,
    gaussian_single_forward_197 hq hG hb.1 hb.2.1 hr hpb,
    gaussian_single_forward_197 hk hG hc.1 hc.2.1 hr hpc]

private theorem gaussian_mix_linear (f g k : ℚ → ℝ) (a b c : ℝ) :
    gaussianAuxMix197 (fun s ↦ a * f s + b * g s + c * k s) =
      a * gaussianAuxMix197 f + b * gaussianAuxMix197 g + c * gaussianAuxMix197 k := by
  unfold gaussianAuxMix197
  simp only [mul_add, Finset.sum_add_distrib, mul_left_comm _ a, mul_left_comm _ b,
    mul_left_comm _ c]
  simp only [← Finset.mul_sum]
  ring

/-- Separate the K197 mixed core into its conductor coefficient, the
common xi contribution, and the symmetric half-point residues. -/
theorem gaussian_core_eq_197 (r : ℝ) :
    gaussianAuxMix197 (fun s ↦ quarterCosineCore656 (4 * r) (s : ℝ)) =
      3 * gaussianAuxMix197 (fun s ↦ quarterCosineXi656 |(s : ℝ)|) -
          (3 * ((11 / 10 : ℝ) ^ 5 / ((11 / 10 : ℝ) ^ 2 - 1 / 4) ^ 3)) *
            gaussianAuxMix197 (fun s ↦ quarterAuxResidue656 (s : ℝ)) +
        r * gaussianAuxMix197 quarterConductorProfile663 := by
  let M : ℝ := (11 / 10) ^ 5 / ((11 / 10 : ℝ) ^ 2 - 1 / 4) ^ 3
  have he (s : ℚ) :
    quarterCosineCore656 (4 * r) (s : ℝ) =
      3 * quarterCosineXi656 |(s : ℝ)| + (-3 * M) * quarterAuxResidue656 (s : ℝ) +
        r * quarterConductorProfile663 s := by
    have hp := quarter_cosine_pole_pair_656 |(s : ℝ)|
    dsimp only at hp
    unfold quarterCosineCore656 quarterAuxResidue656 M
    dsimp only
    rw [quarter_conductor_profile_eq_663, symmetric_profile_value (inv_pos.mpr (Real.exp_pos _)),
      symmetric_profile_value (inv_pos.mpr (Real.exp_pos _))]
    simp only [Real.log_inv, Real.log_exp, abs_neg, abs_abs]
    linear_combination -3 * hp
  rw [funext he, gaussian_mix_linear]
  dsimp only [M]
  ring

end PseudoPrime.PrimeTestBounds.MillerRabin
