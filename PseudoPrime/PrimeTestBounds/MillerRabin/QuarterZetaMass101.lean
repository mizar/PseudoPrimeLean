/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWeightedZeta
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalZeros
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100Bounds
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiSign100RH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCount100RH

/-! # Certified height-100 zeta mass for section 101 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private noncomputable def massWeight (t : ℝ) : ℝ :=
  (51 / 50 : ℝ) ^ 5 / ((51 / 50 : ℝ) ^ 2 + t ^ 2) ^ 3

private theorem massWeight_nonneg (t : ℝ) : 0 ≤ massWeight t := by
  unfold massWeight
  positivity

private theorem massWeight_antitone {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    massWeight t ≤ massWeight s := by
  unfold massWeight
  exact
    div_le_div_of_nonneg_left (by norm_num only)
      (pow_pos (add_pos_of_pos_of_nonneg (by norm_num only) (sq_nonneg s)) 3)
      (pow_le_pow_left₀ (add_nonneg (by norm_num only) (sq_nonneg s))
        (add_le_add_right (pow_le_pow_left₀ hs hst 2) ((51 / 50 : ℝ) ^ 2)) 3)

private theorem low_mass_arithmetic :
    (2 : ℚ) *
        (∑ i : Fin 29,
          (51 / 50 : ℚ) ^ 5 /
            ((51 / 50 : ℚ) ^ 2 + AnalyticNumberTheory.RiemannZeta.lowZero100Lower i ^ 2) ^ 3) ≤
      314 / 1000000000 := by
  decide +kernel

private theorem low_mass_bound {g : Fin 29 → ℝ}
    (hg : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g) :
    2 * (∑ i : Fin 29, massWeight (g i)) ≤ 314 / 1000000000 := by
  have hn : ∀ i : Fin 29, (0 : ℚ) ≤ AnalyticNumberTheory.RiemannZeta.lowZero100Lower i := by
    decide +kernel
  have h :=
    Finset.sum_le_sum (s := Finset.univ)
      (fun i _ ↦
        massWeight_antitone
          (show 0 ≤ (AnalyticNumberTheory.RiemannZeta.lowZero100Lower i : ℝ) by exact_mod_cast hn i)
          (hg i))
  have hc := mul_le_mul_of_nonneg_left h (by norm_num only : (0 : ℝ) ≤ 2)
  apply hc.trans
  unfold massWeight
  have hcast := Rat.cast_le (K := ℝ).mpr low_mass_arithmetic
  push_cast at hcast
  exact hcast

private theorem high_mass_weight {t : ℝ} (ht : 100 < |t|) :
    massWeight t ≤ ((51 / 50 : ℝ) ^ 5 / 100 ^ 4) * (t ^ 2)⁻¹ := by
  have hsq : (100 : ℝ) ^ 2 ≤ t ^ 2 := by
    rw [← sq_abs t]
    exact pow_le_pow_left₀ (by norm_num only) ht.le 2
  have hp : 0 < t ^ 2 := by linarith only [hsq]
  have h4 := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 100 ^ 2) hsq 2
  have h := mul_le_mul_of_nonneg_right h4 hp.le
  have hden : (100 : ℝ) ^ 4 * t ^ 2 ≤ ((51 / 50 : ℝ) ^ 2 + t ^ 2) ^ 3 := by
    calc
      _ ≤ (t ^ 2) ^ 3 := by nlinarith only [h]
      _ ≤ _ := pow_le_pow_left₀ hp.le (le_add_of_nonneg_left (sq_nonneg _)) 3
  unfold massWeight
  rw [← div_eq_mul_inv, div_div]
  exact div_le_div_of_nonneg_left (by norm_num only) (mul_pos (by norm_num only) hp) hden

private theorem finite_weighted_mass (hRH : RiemannHypothesis)
    (hc : AnalyticNumberTheory.RiemannZeta.zeroCount 100 = 58) (S : Finset ℂ)
    (hz : ∀ ρ ∈ S, riemannZeta ρ = 0) (hre : ∀ ρ ∈ S, 0 ≤ ρ.re) {g : Fin 29 → ℝ}
    (hg : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g) (hgmono : StrictMono g)
    (hgpos : ∀ i, 0 < g i)
    (hlo :
      ∀ ρ ∈ S,
        |ρ.im| ≤ 100 →
          AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ = 1 ∧
            (∃ i,
              ρ = (1 / 2 : ℂ) + (g i : ℂ) * Complex.I ∨
                ρ = (1 / 2 : ℂ) + ((-g i : ℝ) : ℂ) * Complex.I)) :
    (∑ ρ ∈ S,
        (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) * massWeight ρ.im) ≤
      1 / 3000000 := by
  classical
  let P := fun i : Fin 29 ↦ (1 / 2 : ℂ) + (g i : ℂ) * Complex.I
  let N := fun i : Fin 29 ↦ (1 / 2 : ℂ) + ((-g i : ℝ) : ℂ) * Complex.I
  let lo := S.filter (fun ρ ↦ |ρ.im| ≤ 100)
  let hi := S.filter (fun ρ ↦ 100 < |ρ.im|)
  let K := fun ρ : ℂ ↦ massWeight ρ.im
  let F := fun ρ : ℂ ↦ (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) * K ρ
  have hP (i : Fin 29) : (P i).im = g i := by
    simp only [P, Complex.add_im, Complex.mul_im, Complex.div_ofNat_im, Complex.one_im, zero_div,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero,
      zero_add]
  have hN (i : Fin 29) : (N i).im = -g i := by
    simp only [N, Complex.add_im, Complex.mul_im, Complex.div_ofNat_im, Complex.one_im, zero_div,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero,
      zero_add]
  have hPi : Function.Injective P := by
    intro i j h
    exact hgmono.injective ((hP i).symm.trans ((congrArg Complex.im h).trans (hP j)))
  have hNi : Function.Injective N := by
    intro i j h
    have he := (hN i).symm.trans ((congrArg Complex.im h).trans (hN j))
    exact hgmono.injective (neg_injective he)
  have hs : lo ⊆ Finset.univ.image P ∪ Finset.univ.image N := by
    intro ρ hρ
    have hp := Finset.mem_filter.mp hρ
    obtain ⟨i, hc⟩ := (hlo ρ hp.1 hp.2).2
    rcases hc with h | h
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h.symm⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h.symm⟩)
  have hdis : Disjoint (Finset.univ.image P) (Finset.univ.image N) := by
    apply Finset.disjoint_left.2
    intro ρ hp hn
    obtain ⟨i, _, hpi⟩ := Finset.mem_image.mp hp
    obtain ⟨j, _, hnj⟩ := Finset.mem_image.mp hn
    have h := congrArg Complex.im (hpi.trans hnj.symm)
    rw [hP, hN] at h
    linarith only [h, hgpos i, hgpos j]
  have hl : ∑ ρ ∈ lo, F ρ ≤ 314 / 1000000000 := by
    calc
      _ = ∑ ρ ∈ lo, K ρ := by
        apply Finset.sum_congr rfl
        intro ρ hρ
        have hp := Finset.mem_filter.mp hρ
        simp only [F, (hlo ρ hp.1 hp.2).1, Nat.cast_one, one_mul]
      _ ≤ ∑ ρ ∈ Finset.univ.image P ∪ Finset.univ.image N, K ρ :=
        Finset.sum_le_sum_of_subset_of_nonneg hs (fun ρ _ _ ↦ massWeight_nonneg ρ.im)
      _ = (∑ ρ ∈ Finset.univ.image P, K ρ) + ∑ ρ ∈ Finset.univ.image N, K ρ := Finset.sum_union hdis
      _ ≤ _ := by
        rw [Finset.sum_image (fun i _ j _ hij ↦ hPi hij),
          Finset.sum_image (fun i _ j _ hij ↦ hNi hij)]
        simp only [K, hP, hN, massWeight, neg_sq]
        have hh := low_mass_bound hg
        unfold massWeight at hh
        linarith only [hh]
  let A : ℝ := (51 / 50 : ℝ) ^ 5 / 100 ^ 4
  have hh : ∑ ρ ∈ hi, F ρ ≤ A * 0.0128 := by
    have hh :=
      AnalyticNumberTheory.RiemannZeta.finite_ordinate_tail_le hRH hi 100
        (fun ρ hρ ↦ hz ρ (Finset.mem_filter.mp hρ).1) (fun ρ hρ ↦ hre ρ (Finset.mem_filter.mp hρ).1)
        (fun ρ hρ ↦ (Finset.mem_filter.mp hρ).2)
    have hh' :=
      mul_le_mul_of_nonneg_left (hh.trans (section104_ordinate_tail_le hRH hc))
        (show 0 ≤ A by positivity)
    rw [Finset.mul_sum] at hh'
    apply (Finset.sum_le_sum (fun ρ hρ ↦ ?_)).trans hh'
    have hw := high_mass_weight (Finset.mem_filter.mp hρ).2
    dsimp only [F, K, A]
    rw [sq_abs]
    convert mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg _) using 1
    ring
  have he := Finset.sum_filter_add_sum_filter_not S (fun ρ ↦ |ρ.im| ≤ 100) F
  simp only [not_le] at he
  change (∑ ρ ∈ lo, F ρ) + (∑ ρ ∈ hi, F ρ) = ∑ ρ ∈ S, F ρ at he
  change (∑ ρ ∈ S, F ρ) ≤ _
  rw [← he]
  exact (add_le_add hl hh).trans (by norm_num only [A])

/-- Under RH the 29 certified positive zeros, their conjugates, and the
retained height-100 tail bound the absolute sixth-pole zeta mass by 1/3000000. -/
theorem section101_zeta_mass (hRH : RiemannHypothesis) :
    (∑' ρ, ‖quarterKernel570.zetaKernelZeroTerm ρ‖) ≤ 1 / 3000000 := by
  classical
  obtain ⟨g, hm, hp, ht, hζ, hg, _⟩ := AnalyticNumberTheory.RiemannZeta.low_zero_100_exists
  have hc := AnalyticNumberTheory.RiemannZeta.count_100_eq_58_of_RH hRH
  have hh := AnalyticNumberTheory.RiemannZeta.critical_zeros_complete_simple hRH hc.le g hm hp ht hζ
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at hh
  apply Real.tsum_le_of_sum_le (fun ρ ↦ norm_nonneg _)
  intro S
  let T := S.image (fun ρ : AnalyticNumberTheory.RiemannXi.Zero ↦ (ρ : ℂ))
  have hz (ρ : ℂ) (hρ : ρ ∈ T) : riemannZeta ρ = 0 := by
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hρ
    exact AnalyticNumberTheory.RiemannXi.riemannZeta_zero_of_riemannXi_zero w.property
  have hre (ρ : ℂ) (hρ : ρ ∈ T) : 0 ≤ ρ.re := by
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hρ
    exact AnalyticNumberTheory.RiemannXi.riemannXi_zero_re_nonneg w.property
  have h :=
    finite_weighted_mass hRH hc T hz hre hg hm hp
      (fun ρ hρ ht ↦ section104_low_pair_complete hRH hh.1 hh.2 (hz ρ hρ) (hre ρ hρ) ht)
  unfold T at h
  rw [Finset.sum_image (fun _ _ _ _ hij ↦ Subtype.ext hij)] at h
  apply le_trans (Finset.sum_le_sum (fun ρ _ ↦ ?_)) h
  rw [LLS.PaperStatements.MellinKernel.zetaKernelZeroTerm, norm_mul, Complex.norm_natCast,
    AnalyticNumberTheory.RiemannXi.zeroMultiplicity_eq_zetaMultiplicity_of_zero ρ.property,
    quarter_zero_norm_570]
  rfl

/-- The certified mass gives the explicit zeta budget for the section 107 phase. -/
theorem section107_zeta_lower (hRH : RiemannHypothesis) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    let u : ℝ := 11 / 25
    let v : ℝ := 91 / 200
    let Z := fun t : ℝ ↦ (∑' ρ, quarterKernel570.zetaOscillatingZeroTerm t ρ).re
    (-0.000002191 : ℝ) ≤
      3 *
        (u * (twoShiftXiContourValue (14 / 5) + Z x) - v * (twoShiftXiContourValue 3 + Z y) -
            ((u ^ 2 + v ^ 2) / 2) * twoShiftXiContourValue 0 +
          (u * v) * twoShiftXiContourValue (1 / 5)) := by
  intro u v Z
  have h := weighted_zeta_total_lower hRH hx hy (section101_zeta_mass hRH)
  dsimp only [u, v, Z] at h ⊢
  linarith only [h]

end PseudoPrime.PrimeTestBounds.MillerRabin
