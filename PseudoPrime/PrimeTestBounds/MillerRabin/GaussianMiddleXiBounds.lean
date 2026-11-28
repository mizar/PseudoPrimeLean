/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleMassXi
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleMassXi
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleWeights
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroConjugateSum
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterZetaLedger
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.SincTailAnchorRH
import PseudoPrime.LLS.PaperStatements.MellinKernelZetaContourLimits

/-! # Inverse-power bounds for the middle principal zero mass -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The positive coefficient majorant for a middle mass at ordinate `t`.
This discards the negative coefficients only for the principal zero estimate. -/
public noncomputable def middleMassHeightCap (Q : Polynomial ℚ) (a : ℚ) (d : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (d + 1),
    max 0 ((normSqPolynomial a Q).coeff j : ℝ) / ((a : ℝ) ^ 2 + t ^ 2) ^ (d + 2 - j)

/-- The height majorant is nonnegative. -/
public theorem middle_mass_height_nonneg (Q : Polynomial ℚ) (a : ℚ) (d : ℕ) (t : ℝ) :
    0 ≤ middleMassHeightCap Q a d t := by
  exact
    Finset.sum_nonneg fun j _ ↦
      div_nonneg (le_max_left _ _) (pow_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) _)

/-- The positive coefficient cap bounds the actual mass on the critical line. -/
public theorem middle_mass_extension_le_height (Q : Polynomial ℚ) {a : ℚ} {d : ℕ} (ha : 0 < (a : ℝ))
    (hd : 1 ≤ d) (hQ : Q.natDegree ≤ d) (t : ℝ) :
    (middleMassExtension Q a (d + 2) (Complex.I * (t : ℂ))).re ≤ middleMassHeightCap Q a d t := by
  rw [middle_mass_extension_line, Complex.ofReal_re]
  have hdeg := norm_sq_polynomial_degree a Q hd hQ
  rw [Polynomial.eval₂_eq_sum_range' _ (Nat.lt_succ_of_le hdeg), Finset.sum_div]
  apply Finset.sum_le_sum
  intro j hj
  let u : ℝ := (a : ℝ) ^ 2 + t ^ 2
  have hu : 0 < u := add_pos_of_pos_of_nonneg (pow_pos ha 2) (sq_nonneg _)
  have hj' := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hpow : u ^ (d + 2) = u ^ (d + 2 - j) * u ^ j := by
    rw [← pow_add, Nat.sub_add_cancel (hj'.trans (Nat.le_add_right _ _))]
  change ((normSqPolynomial a Q).coeff j : ℝ) * u ^ j / u ^ (d + 2) ≤ _
  rw [hpow, mul_div_mul_right _ _ (pow_ne_zero _ hu.ne')]
  exact div_le_div_of_nonneg_right (le_max_right _ _) (pow_nonneg hu.le _)

/-- Replacing a positive ordinate by a smaller positive lower bracket can
only enlarge the positive coefficient majorant. -/
public theorem middle_mass_height_antitone (Q : Polynomial ℚ) {a : ℚ} (d : ℕ) {s t : ℝ} (hs : 0 < s)
    (hst : s ≤ t) : middleMassHeightCap Q a d t ≤ middleMassHeightCap Q a d s := by
  apply Finset.sum_le_sum
  intro j _
  apply div_le_div_of_nonneg_left (le_max_left _ _)
  · exact pow_pos (add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos hs 2)) _
  · exact
      pow_le_pow_left₀ (add_nonneg (sq_nonneg ((a : ℝ))) (sq_nonneg s))
        (add_le_add le_rfl (pow_le_pow_left₀ hs.le hst 2)) _

/-- In the high-ordinate tail, reserve an inverse square for the zero summation
and bound the remaining reciprocal powers at the cutoff. -/
public noncomputable def middleMassHeightTail (Q : Polynomial ℚ) (a : ℚ) (d : ℕ) (T : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (d + 1), max 0 ((normSqPolynomial a Q).coeff j : ℝ) / T ^ (2 * (d + 1 - j))

/-- The tail coefficient multiplying the inverse-square mass is nonnegative. -/
public theorem middle_mass_tail_nonneg (Q : Polynomial ℚ) (a : ℚ) (d : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    0 ≤ middleMassHeightTail Q a d T :=
  Finset.sum_nonneg fun _ _ ↦ div_nonneg (le_max_left _ _) (pow_nonneg hT _)

/-- For `t` above a positive cutoff, the mass cap is at most the tail
coefficient divided by the square of the ordinate. -/
public theorem middle_mass_height_le_tail (Q : Polynomial ℚ) (a : ℚ) (d : ℕ) {T t : ℝ} (hT : 0 < T)
    (ht : T ≤ t) : middleMassHeightCap Q a d t ≤ middleMassHeightTail Q a d T / t ^ 2 := by
  unfold middleMassHeightTail
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro j hj
  rw [div_div]
  have hj' := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have he : d + 2 - j = (d + 1 - j) + 1 := by
    rw [← Nat.sub_add_comm (show j ≤ d + 1 from hj'.trans (Nat.le_succ d))]
  have ht₀ := hT.trans_le ht
  have hbase : t ^ 2 ≤ (a : ℝ) ^ 2 + t ^ 2 := le_add_of_nonneg_left (sq_nonneg _)
  have hpow : T ^ (2 * (d + 1 - j)) ≤ ((a : ℝ) ^ 2 + t ^ 2) ^ (d + 1 - j) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (sq_nonneg _) ((pow_le_pow_left₀ hT.le ht 2).trans hbase) _
  apply div_le_div_of_nonneg_left (le_max_left _ _)
  · exact mul_pos (pow_pos hT _) (pow_pos ht₀ _)
  · rw [he, pow_succ]
    exact
      mul_le_mul hpow hbase (sq_nonneg _) (pow_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) _)

/-- The principal head is controlled by the 29 certified lower brackets,
with the conjugate zeros contributing the same charge. -/
public theorem middle_mass_height_head (Q : Polynomial ℚ) (a : ℚ) (d : ℕ)
    (hRH : RiemannHypothesis) :
    (∑ ρ ∈ AnalyticNumberTheory.RiemannZeta.zerosUpTo 100,
        (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
          middleMassHeightCap Q a d |ρ.im|) ≤
      2 * ∑ i : Fin 29, middleMassHeightCap Q a d (middleZeroLower i) := by
  classical
  let m := AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity
  let w := fun ρ : ℂ ↦ (m ρ : ℝ) * middleMassHeightCap Q a d |ρ.im|
  have h100 : (0 : ℝ) ≤ 100 := by norm_num only
  have hconj (ρ : ℂ) (hρ : ρ ∈ AnalyticNumberTheory.RiemannZeta.zerosUpTo 100) :
    w ((starRingEnd ℂ) ρ) = w ρ := by
    have hz := (AnalyticNumberTheory.RiemannZeta.mem_zerosUpTo h100).mp hρ
    have hr :=
      AnalyticNumberTheory.RiemannZeta.zeta_zero_re_eq_half_of_riemannHypothesis hRH hz.1 hz.2.1
    have hne : ρ ≠ 1 := by
      intro he
      rw [he, Complex.one_re] at hr
      norm_num only at hr
    simp only [w, m, AnalyticNumberTheory.RiemannZeta.multiplicity_conj hne, Complex.conj_im,
      abs_neg]
  change (∑ ρ ∈ AnalyticNumberTheory.RiemannZeta.zerosUpTo 100, w ρ) ≤ _
  rw [AnalyticNumberTheory.RiemannZeta.zero_sum_eq_two_positive hRH h100 w hconj]
  apply mul_le_mul_of_nonneg_left _ (by norm_num only)
  obtain ⟨g, hm, hgp, _, _, hgl, _, hcover, hmult⟩ := quarter_low_zeros_complete hRH
  let Z := fun i : Fin 29 ↦ ((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I
  have hi (i : Fin 29) : (Z i).im = g i := by
    simp only [Z, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
  refine
    (Finset.sum_le_sum_of_subset_of_nonneg hcover
          (fun ρ _ _ ↦ mul_nonneg (Nat.cast_nonneg _) (middle_mass_height_nonneg _ _ _ _))).trans
      ?_
  change (∑ ρ ∈ Finset.univ.image Z, w ρ) ≤ _
  rw [Finset.sum_image
      (fun i _ j _ hij ↦ hm.injective (by simpa only [hi] using congrArg Complex.im hij))]
  apply Finset.sum_le_sum
  intro i _
  change (m (Z i) : ℝ) * middleMassHeightCap Q a d |(Z i).im| ≤ _
  rw [hi i, abs_of_nonneg (hgp i).le, show m (Z i) = 1 from hmult i, Nat.cast_one, one_mul]
  exact middle_mass_height_antitone Q d (middle_zero_lower_pos i) (middle_zero_lower_le g hgl i)

/-- The full Xi mass is bounded by the bracket sum below height 100 and the
coefficient tail times the inverse-square zero mass beyond height 100. -/
public theorem middle_xi_mass_le (Q : Polynomial ℚ) (a : ℚ) {d : ℕ} (ha : 2 ≤ (a : ℝ)) (hd : 1 ≤ d)
    (hQ : Q.natDegree ≤ d) (hRH : RiemannHypothesis) :
    (middleXiMass Q a d).re ≤
      2 * (∑ i : Fin 29, middleMassHeightCap Q a d (middleZeroLower i)) +
        middleMassHeightTail Q a d 100 * (13 / 1000) := by
  classical
  let B := fun j ↦ balancedPoleKernel a ha (d + 1 - j)
  let c := fun j ↦ ((normSqPolynomial a Q).coeff j : ℂ)
  let X := AnalyticNumberTheory.RiemannXi.Zero
  let M := AnalyticNumberTheory.RiemannXi.riemannXiZeroMultiplicity
  let f := fun ρ : X ↦ (M (ρ : ℂ) : ℂ) * middleMassExtension Q a (d + 2) (Complex.I * (ρ : ℂ).im)
  have ha₀ := (by norm_num only : (0 : ℝ) < 2).trans_le ha
  have hs : Summable f := by
    refine
      (summable_sum (s := Finset.range (d + 1)) fun j _ ↦
            ((B j).summable_zetaOscillatingZeroTerm hRH zero_lt_one).mul_left (c j)).congr
        ?_
    intro ρ
    have hre : (Complex.I * ((ρ : ℂ).im : ℂ)).re = 0 := by
      simp only [Complex.mul_re, Complex.I_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
    dsimp only [f]
    rw [middle_mass_balanced_sum Q a ha hd hQ
        (by
          rw [hre]; exact neg_lt_zero.mpr ha₀)
        (by
          rw [hre]; exact ha₀),
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [LLS.PaperStatements.MellinKernel.zetaOscillatingZeroTerm,
      LLS.PaperStatements.MellinKernel.zetaKernelZeroTerm, Complex.ofReal_one, Complex.one_cpow,
      mul_one, M]
    rw [mul_left_comm]
  change (∑' ρ, f ρ).re ≤ _
  apply le_of_tendsto (Complex.hasSum_re hs.hasSum)
  apply Filter.Eventually.of_forall
  intro S
  let e : X ↪ ℂ := ⟨Subtype.val, Subtype.val_injective⟩
  let Y := S.map e
  let p := fun ρ : ℂ ↦ |ρ.im| ≤ (100 : ℝ)
  let m := AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity
  let w := fun ρ : ℂ ↦ (m ρ : ℝ) * middleMassHeightCap Q a d |ρ.im|
  have hz (ρ : ℂ) (hρ : ρ ∈ Y) : AnalyticNumberTheory.RiemannXi.riemannXi ρ = 0 := by
    obtain ⟨r, _, rfl⟩ := Finset.mem_map.mp hρ
    exact r.property
  have hY : (∑ ρ ∈ S, (f ρ).re) ≤ ∑ ρ ∈ Y, w ρ := by
    rw [Finset.sum_map]
    apply Finset.sum_le_sum
    intro ρ _
    have hm :=
      AnalyticNumberTheory.RiemannXi.zeroMultiplicity_eq_zetaMultiplicity_of_zero ρ.property
    simp only [f, Complex.mul_re, ← Complex.ofReal_natCast, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, w, m, e, Function.Embedding.coeFn_mk, M, hm]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    have h := middle_mass_extension_le_height Q ha₀ hd hQ (ρ : ℂ).im
    simpa only [middleMassHeightCap, sq_abs] using h
  refine hY.trans ?_
  rw [← Finset.sum_filter_add_sum_filter_not Y p]
  have hhead : Y.filter p ⊆ AnalyticNumberTheory.RiemannZeta.zerosUpTo 100 := by
    intro ρ hρ
    obtain ⟨hY, hh⟩ := Finset.mem_filter.mp hρ
    exact
      (AnalyticNumberTheory.RiemannZeta.mem_zerosUpTo (by norm_num only)).mpr
        ⟨AnalyticNumberTheory.RiemannXi.riemannZeta_zero_of_riemannXi_zero (hz ρ hY),
          AnalyticNumberTheory.RiemannXi.riemannXi_zero_re_nonneg (hz ρ hY), hh⟩
  apply add_le_add
  · refine
      (Finset.sum_le_sum_of_subset_of_nonneg hhead
            (fun ρ _ _ ↦ mul_nonneg (Nat.cast_nonneg _) (middle_mass_height_nonneg Q a d _))).trans
        ?_
    exact middle_mass_height_head Q a d hRH
  · let T := middleMassHeightTail Q a d 100
    have hT : 0 ≤ T := middle_mass_tail_nonneg Q a d (by norm_num only)
    have hu (ρ : ℂ) (hρ : ρ ∈ Y.filter fun ρ ↦ ¬p ρ) : 100 < |ρ.im| :=
      lt_of_not_ge (Finset.mem_filter.mp hρ).2
    have ht :=
      (AnalyticNumberTheory.RiemannZeta.finite_ordinate_tail_le hRH (Y.filter fun ρ ↦ ¬p ρ) 100
            (fun ρ hρ ↦
              AnalyticNumberTheory.RiemannXi.riemannZeta_zero_of_riemannXi_zero
                (hz ρ (Finset.mem_filter.mp hρ).1))
            (fun ρ hρ ↦
              AnalyticNumberTheory.RiemannXi.riemannXi_zero_re_nonneg
                (hz ρ (Finset.mem_filter.mp hρ).1))
            hu).trans
        (AnalyticNumberTheory.RiemannZeta.ordinateTail_hundred_le hRH)
    have ht' := mul_le_mul_of_nonneg_left ht hT
    rw [Finset.mul_sum] at ht'
    simp only [sq_abs] at ht'
    refine (Finset.sum_le_sum (g := fun ρ : ℂ ↦ T * ((m ρ : ℝ) / ρ.im ^ 2)) fun ρ hρ ↦ ?_).trans ht'
    have hi := middle_mass_height_le_tail Q a d (by norm_num only) (hu ρ hρ).le
    simp only [sq_abs] at hi
    exact (mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg (m ρ))).trans_eq (by ring)

end PseudoPrime.PrimeTestBounds.MillerRabin
