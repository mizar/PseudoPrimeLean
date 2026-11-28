/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPrincipalMoments
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPrincipalZeroCancel
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.SincTailAnchorRH
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterZetaLedger
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroConjugateSum
import Mathlib.Tactic.LinearCombination

/-! # Inverse-height majorants for the middle principal zero series -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The weighted absolute coefficients of a translated profile.
Each term includes its monomial Laplace factorial and an inverse height power. -/
@[expose]
public noncomputable def middleSpectralMass (P : Polynomial ℝ) (b T : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (P.natDegree + 1), |principalMomentCoeff P b j| * (j.factorial : ℝ) / T ^ j

/-- A zero with ordinate magnitude at least `T` has an inverse-square bound
using the derivative at zero and the first reflected-derivative profile at the cutoff. -/
public theorem middle_spectral_term_le (B : Polynomial ℝ) (hRH : RiemannHypothesis) {κ d b X T : ℝ}
    {ρ : ℂ} (hκ : 0 ≤ κ) (hd : 0 < d) (hT : 0 < T) (ht : T ≤ |ρ.im|)
    (hz : riemannZeta ρ = 0 ∧ 0 ≤ ρ.re) (hB : B.eval 0 = 0) :
    let C := Polynomial.C d * B - B.derivative
    let e := Real.exp (-(d + 1 / 2) * b)
    (κ * e) * |principalCancelledTerm B d b X ρ| ≤
      (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
          (κ * middleSpectralMass B.derivative 0 T + 4 * κ * e * middleSpectralMass C b T) /
        |ρ.im| ^ 2 := by
  intro C e
  let s := (d : ℂ) + ρ
  let t := |ρ.im|
  let m := AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ
  have hxi := AnalyticNumberTheory.RiemannXi.xi_zero_of_zeta_zero_of_re_nonneg hz.1 hz.2
  have hρ := AnalyticNumberTheory.RiemannXi.xi_zero_re_eq_half_of_riemannHypothesis hRH hxi
  have hρ₀ : ρ ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hρ
    norm_num only at hρ
  have hs : s.re = d + 1 / 2 := by simp only [s, Complex.add_re, Complex.ofReal_re, hρ]
  have hs₀ : 0 < s.re := by
    rw [hs]; exact add_pos hd (by norm_num only)
  have hsne : s ≠ 0 := fun h ↦ hs₀.ne' (h ▸ Complex.zero_re)
  have htρ : t ≤ ‖ρ‖ := Complex.abs_im_le_norm _
  have hts : t ≤ ‖s‖ := by
    have h := Complex.abs_im_le_norm s
    simpa only [s, Complex.add_im, Complex.ofReal_im, zero_add] using h
  have hfull : complexLogPolyMoment B 0 s = complexLogPolyMoment B.derivative 0 s / s := by
    have h := complex_log_poly_moment_step B 0 hs₀
    rw [hB, Complex.ofReal_zero, sub_eq_zero] at h
    exact (eq_div_iff hsne).mpr ((mul_comm _ _).trans h)
  have hf := principal_moment_tail_le B.derivative 0 T t s s hT ht hts hts
  have hc := principal_moment_tail_le C b T t s ρ hT ht hts htρ
  change _ ≤ middleSpectralMass B.derivative 0 T / t ^ 2 at hf
  change _ ≤ middleSpectralMass C b T / t ^ 2 at hc
  have he : ‖(Real.exp b : ℂ) ^ s‖ = Real.exp ((d + 1 / 2) * b) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (Real.exp_pos _), Real.rpow_def_of_pos (Real.exp_pos _),
      Real.log_exp, hs, mul_comm]
  have hphase : ‖Complex.exp ((Real.log X : ℂ) * (ρ.im : ℂ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp, ← Complex.ofReal_mul]
    simp only [Complex.mul_re, Complex.I_re, Complex.ofReal_im, mul_zero, zero_mul, zero_sub,
      neg_zero, Real.exp_zero]
  have h0 := principal_cancelled_first B d b X hz hρ₀ hs₀
  change principalCancelledTerm B d b X ρ = _ at h0
  rw [h0]
  have h1 :=
    Complex.abs_re_le_norm
      (Complex.exp ((Real.log X : ℂ) * (ρ.im : ℂ) * Complex.I) *
        ((m : ℂ) *
          ((Real.exp b : ℂ) ^ s * complexLogPolyMoment B 0 s +
            4 * (complexLogPolyMoment C b s / ρ))))
  rw [norm_mul, hphase, one_mul, norm_mul, Complex.norm_natCast] at h1
  have h2 :=
    (norm_add_le ((Real.exp b : ℂ) ^ s * complexLogPolyMoment B 0 s)
          (4 * (complexLogPolyMoment C b s / ρ))).trans_eq
      (by rw [norm_mul, norm_mul, he, hfull, Complex.norm_ofNat])
  have hn : 0 ≤ κ * e := mul_nonneg hκ (Real.exp_nonneg _)
  have h3 :=
    mul_le_mul_of_nonneg_left
      ((h1.trans
        (mul_le_mul_of_nonneg_left
          (h2.trans
            (add_le_add (mul_le_mul_of_nonneg_left hf (Real.exp_nonneg _))
              (mul_le_mul_of_nonneg_left hc (by norm_num only))))
          (Nat.cast_nonneg m))))
      hn
  have hcancel : e * Real.exp ((d + 1 / 2) * b) = 1 := by
    dsimp only [e]
    rw [← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero]
  refine h3.trans_eq ?_
  rw [show
      κ * e *
          ((m : ℝ) *
            (Real.exp ((d + 1 / 2) * b) * (middleSpectralMass B.derivative 0 T / t ^ 2) +
              4 * (middleSpectralMass C b T / t ^ 2))) =
        (m : ℝ) *
            (κ * (e * Real.exp ((d + 1 / 2) * b)) * middleSpectralMass B.derivative 0 T +
              4 * κ * e * middleSpectralMass C b T) /
          t ^ 2
      by ring,
    hcancel, mul_one]

/-- The inverse-height coefficient charge is nonnegative at a positive height. -/
public theorem middle_spectral_mass_nonneg (P : Polynomial ℝ) (b : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    0 ≤ middleSpectralMass P b T := by
  exact
    Finset.sum_nonneg
      (fun j _ ↦ div_nonneg (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _)) (pow_nonneg hT j))

/-- Enlarging a positive lower bound for the height decreases the coefficient
majorant, since its summands have only nonnegative inverse powers. -/
public theorem middle_spectral_mass_antitone (P : Polynomial ℝ) (b : ℝ) {T U : ℝ} (hT : 0 < T)
    (hTU : T ≤ U) : middleSpectralMass P b U ≤ middleSpectralMass P b T := by
  apply Finset.sum_le_sum
  intro j hj
  exact
    div_le_div_of_nonneg_left (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _)) (pow_pos hT j)
      (pow_le_pow_left₀ hT.le hTU j)

/-- Separate the normalized zero series at height 100. The certified ordinate
tail supplies the total inverse-square mass on both signs of the ordinate. -/
public theorem middle_spectral_series_le (B : Polynomial ℝ) (hRH : RiemannHypothesis)
    {κ d b X H : ℝ} (hκ : 0 ≤ κ) (hd : 0 < d) (hb : 0 < b) (hX : 0 < X) (hB : B.eval 0 = 0)
    (hB' : B.derivative.eval 0 = 0)
    (hhead :
      (∑ ρ ∈ AnalyticNumberTheory.RiemannZeta.zerosUpTo 100,
          (κ * Real.exp (-(d + 1 / 2) * b)) * |principalCancelledTerm B d b X ρ|) ≤
        H) :
    let C := Polynomial.C d * B - B.derivative
    let e := Real.exp (-(d + 1 / 2) * b)
    |(κ * e) * ∑' ρ, principalCancelledTerm B d b X ρ| ≤
      H +
        (κ * middleSpectralMass B.derivative 0 100 + 4 * κ * e * middleSpectralMass C b 100) *
          (13 / 1000) := by
  classical
  intro C e
  let f := principalCancelledTerm B d b X
  let W := κ * middleSpectralMass B.derivative 0 100 + 4 * κ * e * middleSpectralMass C b 100
  have hw : 0 ≤ W :=
    add_nonneg (mul_nonneg hκ (middle_spectral_mass_nonneg _ _ (by norm_num only)))
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num only) hκ) (Real.exp_nonneg _))
        (middle_spectral_mass_nonneg _ _ (by norm_num only)))
  have hk : 0 ≤ κ * e := mul_nonneg hκ (Real.exp_nonneg _)
  have hs := (principal_cancelled_hasSum B hRH hd hb hX hB hB').summable.hasSum.mul_left (κ * e)
  apply le_of_tendsto hs.abs
  apply Filter.Eventually.of_forall
  intro S
  let p := fun ρ : ℂ ↦ riemannZeta ρ = 0 ∧ 0 ≤ ρ.re
  let q := fun ρ : ℂ ↦ |ρ.im| ≤ (100 : ℝ)
  let Z := S.filter p
  have hfilter : (∑ ρ ∈ S, κ * e * f ρ) = ∑ ρ ∈ Z, κ * e * f ρ := by
    rw [show Z = S.filter p from rfl, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ρ _
    by_cases h : p ρ
    · rw [ite_eq_left h]
    · simp only [f, principalCancelledTerm,
        ite_eq_right (show ¬(riemannZeta ρ = 0 ∧ 0 ≤ ρ.re) from h), mul_zero]
  have hz (ρ : ℂ) (hρ : ρ ∈ Z) : p ρ := (Finset.mem_filter.mp hρ).2
  have hsub : Z.filter q ⊆ AnalyticNumberTheory.RiemannZeta.zerosUpTo 100 := by
    intro ρ hρ
    have hm := Finset.mem_filter.mp hρ
    exact
      (AnalyticNumberTheory.RiemannZeta.mem_zerosUpTo (by norm_num only)).mpr
        ⟨(hz ρ hm.1).1, (hz ρ hm.1).2, hm.2⟩
  have hlo :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun ρ _ _ ↦ mul_nonneg hk (abs_nonneg (f ρ)))).trans
      hhead
  let S' := Z.filter fun ρ ↦ ¬q ρ
  have hu (ρ : ℂ) (hρ : ρ ∈ S') : 100 < |ρ.im| := lt_of_not_ge (Finset.mem_filter.mp hρ).2
  have ht :=
    (AnalyticNumberTheory.RiemannZeta.finite_ordinate_tail_le hRH S' 100
          (fun ρ hρ ↦ (hz ρ (Finset.mem_filter.mp hρ).1).1)
          (fun ρ hρ ↦ (hz ρ (Finset.mem_filter.mp hρ).1).2) hu).trans
      (AnalyticNumberTheory.RiemannZeta.ordinateTail_hundred_le hRH)
  have htail := mul_le_mul_of_nonneg_left ht hw
  rw [Finset.mul_sum] at htail
  change |∑ ρ ∈ S, κ * e * f ρ| ≤ _
  rw [hfilter]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  simp only [abs_mul, abs_of_nonneg hk]
  rw [← Finset.sum_filter_add_sum_filter_not Z q]
  refine add_le_add hlo (le_trans (Finset.sum_le_sum fun ρ hρ ↦ ?_) htail)
  have h :=
    middle_spectral_term_le B hRH (b := b) (X := X) hκ hd (by norm_num only : (0 : ℝ) < 100)
      (hu ρ hρ).le (hz ρ (Finset.mem_filter.mp hρ).1) hB
  dsimp only at h
  exact
    h.trans_eq
      (by
        dsimp only [W, C, e]; ring)

/-- A phase-free majorant may use the certified lower bracket of each
positive zero. The absolute ordinate and multiplicity give the same charge
on its conjugate. -/
public theorem middle_spectral_head_le (B : Polynomial ℝ) (hRH : RiemannHypothesis) {κ d b X : ℝ}
    (hκ : 0 ≤ κ) (hd : 0 < d) (T : Fin 29 → ℝ) (hT : ∀ i, 0 < T i)
    (hlo : ∀ g, AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g → ∀ i, T i ≤ g i)
    (hB : B.eval 0 = 0) :
    let C := Polynomial.C d * B - B.derivative
    let e := Real.exp (-(d + 1 / 2) * b)
    let W := fun t ↦ κ * middleSpectralMass B.derivative 0 t + 4 * κ * e * middleSpectralMass C b t
    (∑ ρ ∈ AnalyticNumberTheory.RiemannZeta.zerosUpTo 100,
        (κ * e) * |principalCancelledTerm B d b X ρ|) ≤
      2 * ∑ i, W (T i) / (T i) ^ 2 := by
  classical
  intro C e W
  let m := AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity
  let w := fun ρ : ℂ ↦ (m ρ : ℝ) * W |ρ.im| / |ρ.im| ^ 2
  have h100 : (0 : ℝ) ≤ 100 := by norm_num only
  have hw (t : ℝ) (ht : 0 ≤ t) : 0 ≤ W t :=
    add_nonneg (mul_nonneg hκ (middle_spectral_mass_nonneg _ _ ht))
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num only) hκ) (Real.exp_nonneg _))
        (middle_spectral_mass_nonneg _ _ ht))
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
  refine (Finset.sum_le_sum (g := w) (fun ρ hρ ↦ ?_)).trans ?_
  · have hz := (AnalyticNumberTheory.RiemannZeta.mem_zerosUpTo h100).mp hρ
    have hp :=
      (mul_pos (by norm_num only : (0 : ℝ) < 2) Real.pi_pos).trans
        (AnalyticNumberTheory.RiemannZeta.zero_height_gt_two_pi hRH hz.1 hz.2.1)
    exact middle_spectral_term_le B hRH hκ hd hp le_rfl ⟨hz.1, hz.2.1⟩ hB
  rw [AnalyticNumberTheory.RiemannZeta.zero_sum_eq_two_positive hRH h100 w hconj]
  apply mul_le_mul_of_nonneg_left _ (by norm_num only)
  obtain ⟨g, hm, hgp, _, _, hgl, _, hcover, hmult⟩ := quarter_low_zeros_complete hRH
  let Z := fun i : Fin 29 ↦ ((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I
  have hi (i : Fin 29) : (Z i).im = g i := by
    simp only [Z, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
  refine
    (Finset.sum_le_sum_of_subset_of_nonneg hcover
          (fun ρ _ _ ↦
            div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hw _ (abs_nonneg _))) (sq_nonneg _))).trans
      ?_
  change (∑ ρ ∈ Finset.univ.image Z, w ρ) ≤ _
  rw [Finset.sum_image
      (fun i _ j _ hij ↦ hm.injective (by simpa only [hi] using congrArg Complex.im hij))]
  apply Finset.sum_le_sum
  intro i _
  have htg : T i ≤ g i := hlo g hgl i
  have hmon : W (g i) ≤ W (T i) :=
    add_le_add (mul_le_mul_of_nonneg_left (middle_spectral_mass_antitone _ _ (hT i) htg) hκ)
      (mul_le_mul_of_nonneg_left (middle_spectral_mass_antitone _ _ (hT i) htg)
        (mul_nonneg (mul_nonneg (by norm_num only) hκ) (Real.exp_nonneg _)))
  change (m (Z i) : ℝ) * W |(Z i).im| / |(Z i).im| ^ 2 ≤ _
  rw [hi i, abs_of_nonneg (hgp i).le, show m (Z i) = 1 from hmult i, Nat.cast_one, one_mul]
  exact
    (div_le_div_of_nonneg_right hmon (sq_nonneg _)).trans
      (div_le_div_of_nonneg_left (hw _ (hT i).le) (pow_pos (hT i) 2)
        (pow_le_pow_left₀ (hT i).le htg 2))

/-- The full principal series is bounded by a sum of inverse-height weights
from the lower brackets and the certified height-100 inverse-square tail. -/
public theorem middle_spectral_of_lower (B : Polynomial ℝ) (hRH : RiemannHypothesis) {κ d b X : ℝ}
    (hκ : 0 ≤ κ) (hd : 0 < d) (hb : 0 < b) (hX : 0 < X) (T : Fin 29 → ℝ) (hT : ∀ i, 0 < T i)
    (hlo : ∀ g, AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g → ∀ i, T i ≤ g i)
    (hB : B.eval 0 = 0) (hB' : B.derivative.eval 0 = 0) :
    let C := Polynomial.C d * B - B.derivative
    let e := Real.exp (-(d + 1 / 2) * b)
    let W := fun t ↦ κ * middleSpectralMass B.derivative 0 t + 4 * κ * e * middleSpectralMass C b t
    |(κ * e) * ∑' ρ, principalCancelledTerm B d b X ρ| ≤
      2 * (∑ i, W (T i) / (T i) ^ 2) + W 100 * (13 / 1000) := by
  exact
    middle_spectral_series_le B hRH hκ hd hb hX hB hB'
      (middle_spectral_head_le B hRH hκ hd T hT hlo hB)

/-- The combined head and tail weight for one coefficient degree. It is shared
by the two middle kernels and every cutoff in either interval. -/
@[expose]
public noncomputable def middleSpectralWeight (T : Fin 29 → ℝ) (j : ℕ) : ℝ :=
  2 * (∑ i, (1 : ℝ) / (T i) ^ (j + 2)) + (13 / 1000 : ℝ) / 100 ^ j

/-- Interchange the two finite sums so that each inverse-height weight is
computed once per degree, independently of the profile. -/
public theorem middle_spectral_weighted_mass (P : Polynomial ℝ) (b : ℝ) (T : Fin 29 → ℝ) :
    2 * (∑ i, middleSpectralMass P b (T i) / (T i) ^ 2) + middleSpectralMass P b 100 * (13 / 1000) =
      ∑ j ∈ Finset.range (P.natDegree + 1),
        (|principalMomentCoeff P b j| * (j.factorial : ℝ)) * middleSpectralWeight T j := by
  let A := fun j : ℕ ↦ |principalMomentCoeff P b j| * (j.factorial : ℝ)
  change
    2 * (∑ i, (∑ j ∈ Finset.range (P.natDegree + 1), A j / (T i) ^ j) / (T i) ^ 2) +
        (∑ j ∈ Finset.range (P.natDegree + 1), A j / 100 ^ j) * (13 / 1000) =
      _
  simp only [Finset.sum_div]
  rw [Finset.sum_comm, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have he (i : Fin 29) : A j / (T i) ^ j / (T i) ^ (2 : ℕ) = A j * (1 / (T i) ^ (j + 2)) := by
    rw [pow_add, div_div, mul_one_div]
  simp_rw [he, ← Finset.mul_sum]
  dsimp only [middleSpectralWeight, A]
  ring

end PseudoPrime.PrimeTestBounds.MillerRabin
