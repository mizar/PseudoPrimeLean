/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK137Later
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197PowerBounds
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Abel1000
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Boundary143
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPowerGain663
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterReflectBox663
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197NinthNumerics
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK137Boundary
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Boundary33
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Boundary36
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Boundary45
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Boundary56
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Boundary65
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Boundary76
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Boundary88
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Boundary99
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Boundary106
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Main522
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Main572
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Main672
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Main1000
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Boundary114
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt1423toMillion
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Main472
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Power472
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Main426
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Power426
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Main395
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Power395
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Main370
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Power370
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Main354
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Power354
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197ReflectCredit
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197LocalNumerics
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197PowerGrowth346
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Shift
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197ReflectionEarly
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Conductor

/-! # Early K197 Gaussian witness cells -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem first_radius_mem {L : ℝ} (hL : L ∈ Set.Icc (2657 / 4) (2659 / 4)) :
    (500186760939 / 500000000000 : ℝ) * L / 2 ∈ Set.Icc 332.249 332.5 := by
  exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩

private theorem first_linear_lower {L : ℝ} (hL : L ∈ Set.Icc (2657 / 4) (2659 / 4)) :
    let r := (500186760939 / 500000000000 : ℝ) * L / 2
    (-10.557449 : ℝ) ≤
      (0.71780481 - gaussianHalfCoeff197) * r -
        (3 / 4 + gaussianAuxMix197 quarterConductorProfile663) * (L / 2) := by
  intro r
  have hr : 0 ≤ r := (by norm_num only : (0 : ℝ) ≤ 332.249).trans (first_radius_mem hL).1
  have hL₀ : 0 ≤ L / 2 := by linarith only [hL.1]
  have h₁ := mul_le_mul_of_nonneg_right gaussian_half_upper_197 hr
  have h₂ := mul_le_mul_of_nonneg_right gaussian_conductor_upper_197 hL₀
  have h₃ : (-10.557449 : ℝ) ≤ (0.71780481 + 0.00692794) * r - (3 / 4 + 0.00676712) * (L / 2) := by
    dsimp only [r]
    linarith only [hL.2]
  linarith only [h₁, h₂, h₃]

private theorem early_pair_false {p q k : ℕ} [NeZero p] [NeZero q] [NeZero k]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ k}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even)
    (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even)
    (hp : 2 ≤ p) (hq : 2 ≤ q) (hk : 2 ≤ k)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r t B G M C : ℝ}
    (hr : r ∈ Set.Icc 332.15 336.9)
    (hcond_bound : 4 * r * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ C) (ht₀ : t ≤ r)
    (hlev : Real.log p + Real.log q + Real.log k = 4 * t)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3) :
    (∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1) →
    (∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1) →
    (∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) →
    (let x := r ^ 2
     let W := fun n ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) x n).re
     (0.71780481 : ℝ) * r + B <
       4 * (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, W n) - (∑' n, W n) -
         3 * (centralGammaPair656 (1 : DirichletCharacter ℂ 1) x).re) →
    (G ≤ (gaussianShiftedForward197 a r + gaussianShiftedForward197 b r +
      gaussianShiftedForward197 c r) + gaussianHalfCoeff197 * r) →
    (M ≤ (0.71780481 - gaussianHalfCoeff197) * r -
      (3 / 4 + gaussianAuxMix197 quarterConductorProfile663) * t) →
    (0 ≤ (15.0472769 : ℝ) + 0.143227796 + B + G + M - 4 * 0.006305 - C -
      0.000251 + 0.00914) →
    False := by
  intro hpa hpb hpc hmain hs hlin hmargin
  have h := gaussian_fixed_power_comparison_197 ha hb hc hp hq hk hG hr hlev ht hpa hpb hpc
  have htail := gaussian_abel_tail_early_197 hr
  have hr₃ : (328 : ℝ) ≤ r := (by norm_num only : (328 : ℝ) ≤ 332.15).trans hr.1
  have hr₂ : (322 : ℝ) ≤ r := (by norm_num only : (322 : ℝ) ≤ 328).trans hr₃
  have hB : (103684 : ℝ) ≤ r ^ 2 :=
    (by norm_num only : (103684 : ℝ) ≤ 322 ^ 2).trans
      (pow_le_pow_left₀ (by norm_num only) hr₂ 2)
  have hreflect := (quarter_main_reflect_cap_656 a b c hG.riemann hr₂ (B := 103684)
    (by norm_num only) (by norm_num only) (by exact_mod_cast hB) ht hpa hpb hpc).trans
    (k197_main_reflect_box ⟨hr₃, hr.2⟩)
  have hpos := gaussian_k197_reflect_credit ⟨hr₃, hr.2.trans (by norm_num only)⟩
  let R := (quarterKernel656.transform (r ^ 2)⁻¹).re
  have hcond : 4 * t * R ≤ C := by
    have hR : 0 ≤ R := quarterKernel656.mellin_nonneg _ (by positivity)
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht₀
      (by norm_num only : (0 : ℝ) ≤ 4)) hR).trans hcond_bound
  dsimp only at h hmain htail
  dsimp only [R] at hcond
  ring_nf at h hs hmain hlin htail hreflect hpos hcond
  linarith only [h, hs, hmain, hlin, htail, hreflect, hpos, hcond, hmargin]

private theorem first_pair_false {p q k : ℕ} [NeZero p] [NeZero q] [NeZero k]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ k}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hk : 2 ≤ k)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L : ℝ}
    (hL : L ∈ Set.Icc (2657 / 4) (2659 / 4)) (hlev : Real.log p + Real.log q + Real.log k = 2 * L)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3) :
    let r := (500186760939 / 500000000000 : ℝ) * L / 2
    (∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1) →
      (∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1) →
      (∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) → False := by
  intro r hpa hpb hpc
  have hr : r ∈ Set.Icc 332.249 332.5 := first_radius_mem hL
  have hw : r ∈ Set.Icc 332.15 334 :=
    ⟨(by norm_num only : (332.15 : ℝ) ≤ 332.249).trans hr.1, hr.2.trans (by norm_num only)⟩
  have hlevel : Real.log p + Real.log q + Real.log k = 4 * (L / 2) := by linarith only [hlev]
  have hscale : 4 * r / (500186760939 / 500000000000) = 2 * L := by
    dsimp only [r]
    ring
  have hs :=
    gaussian_shift_forward_first_197 ha hb hc hG.riemann hr (hlev.trans hscale.symm) ht hpa hpb hpc
  have htr : L / 2 ≤ r := by
    dsimp only [r]; linarith only [hL.1]
  apply
    early_pair_false ha hb hc hp hq hk hG ⟨hw.1, hw.2.trans (by norm_num only)⟩
      (quarter_main_conductor_k197 hw.1) htr hlevel ht hpa hpb hpc
      (gaussian_k197_first_principal hG.riemann hL) hs (first_linear_lower hL)
  norm_num only

private theorem second_linear_lower {L : ℝ} (hL : L ∈ Set.Icc (2659 / 4) (2661 / 4)) :
    let r := (12505045329 / 12500000000 : ℝ) * L / 2
    (-10.558133 : ℝ) ≤
      (0.71780481 - gaussianHalfCoeff197) * r -
        (3 / 4 + gaussianAuxMix197 quarterConductorProfile663) * (L / 2) := by
  intro r
  have hr : 0 ≤ r := by
    dsimp only [r]; linarith only [hL.1]
  have hL₀ : 0 ≤ L / 2 := by linarith only [hL.1]
  have h₁ := mul_le_mul_of_nonneg_right gaussian_half_upper_197 hr
  have h₂ := mul_le_mul_of_nonneg_right gaussian_conductor_upper_197 hL₀
  have h₃ : (-10.558133 : ℝ) ≤ (0.71780481 + 0.00692794) * r - (3 / 4 + 0.00676712) * (L / 2) := by
    dsimp only [r]
    linarith only [hL.2]
  linarith only [h₁, h₂, h₃]

private theorem second_pair_false {p q k : ℕ} [NeZero p] [NeZero q] [NeZero k]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ k}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hk : 2 ≤ k)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L : ℝ}
    (hL : L ∈ Set.Icc (2659 / 4) (2661 / 4)) (hlev : Real.log p + Real.log q + Real.log k = 2 * L)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3) :
    let r := (12505045329 / 12500000000 : ℝ) * L / 2
    (∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1) →
      (∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1) →
      (∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) → False := by
  intro r hpa hpb hpc
  have hw : r ∈ Set.Icc 332.15 334 :=
    ⟨by
      dsimp only [r]; linarith only [hL.1], by
      dsimp only [r]; linarith only [hL.2]⟩
  have hlevel : Real.log p + Real.log q + Real.log k = 4 * (L / 2) := by linarith only [hlev]
  have hscale : 4 * r / (12505045329 / 12500000000) = 2 * L := by
    dsimp only [r]
    ring
  have hs :=
    gaussian_shift_forward_early_197 ha hb hc hG.riemann (s := 12505045329 / 12500000000) hw
      (by norm_num only) (hlev.trans hscale.symm) ht hpa hpb hpc
  have htr : L / 2 ≤ r := by
    dsimp only [r]; linarith only [hL.1]
  apply
    early_pair_false ha hb hc hp hq hk hG ⟨hw.1, hw.2.trans (by norm_num only)⟩
      (quarter_main_conductor_k197 hw.1) htr hlevel ht hpa hpb hpc
      (gaussian_k197_second_principal hG.riemann hL) hs (second_linear_lower hL)
  norm_num only

/-- Under GRH, an odd uniform Korselt triple in the first K197 cell has a
prime Miller–Rabin witness below that cell's squared Gaussian radius. -/
theorem gaussian_k197_first_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (2657 / 4) (2659 / 4)) :
    let r := (500186760939 / 500000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  intro r
  apply uniform_witness_of_pair_false hn ho hu (X := r ^ 2)
  intro p q k _ _ _ a b c ha hb hc hp hq hk hlev ht hsmall
  exact
    first_pair_false ha hb hc hp hq hk hG hL hlev ht (fun l hl hX ↦ (hsmall l hl hX).1)
      (fun l hl hX ↦ (hsmall l hl hX).2.1) (fun l hl hX ↦ (hsmall l hl hX).2.2)

/-- Under GRH, an odd uniform Korselt triple in the second K197 cell has a
prime Miller–Rabin witness below that cell's squared Gaussian radius. -/
theorem gaussian_k197_second_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (2659 / 4) (2661 / 4)) :
    let r := (12505045329 / 12500000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  intro r
  apply uniform_witness_of_pair_false hn ho hu (X := r ^ 2)
  intro p q k _ _ _ a b c ha hb hc hp hq hk hlev ht hsmall
  exact
    second_pair_false ha hb hc hp hq hk hG hL hlev ht (fun l hl hX ↦ (hsmall l hl hX).1)
      (fun l hl hX ↦ (hsmall l hl hX).2.1) (fun l hl hX ↦ (hsmall l hl hX).2.2)

private theorem third_linear_lower {L : ℝ} (hL : L ∈ Set.Icc (2661 / 4) (2665 / 4)) :
    let r := (1000433684769 / 1000000000000 : ℝ) * L / 2
    (-10.566747 : ℝ) ≤
      (0.71780481 - gaussianHalfCoeff197) * r -
        (3 / 4 + gaussianAuxMix197 quarterConductorProfile663) * (L / 2) := by
  intro r
  have hr : 0 ≤ r := by
    dsimp only [r]; linarith only [hL.1]
  have hL₀ : 0 ≤ L / 2 := by linarith only [hL.1]
  have h₁ := mul_le_mul_of_nonneg_right gaussian_half_upper_197 hr
  have h₂ := mul_le_mul_of_nonneg_right gaussian_conductor_upper_197 hL₀
  have h₃ : (-10.566747 : ℝ) ≤ (0.71780481 + 0.00692794) * r - (3 / 4 + 0.00676712) * (L / 2) := by
    dsimp only [r]
    linarith only [hL.2]
  linarith only [h₁, h₂, h₃]

private theorem third_pair_false {p q k : ℕ} [NeZero p] [NeZero q] [NeZero k]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ k}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hk : 2 ≤ k)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L : ℝ}
    (hL : L ∈ Set.Icc (2661 / 4) (2665 / 4)) (hlev : Real.log p + Real.log q + Real.log k = 2 * L)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3) :
    let r := (1000433684769 / 1000000000000 : ℝ) * L / 2
    (∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1) →
      (∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1) →
      (∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) → False := by
  intro r hpa hpb hpc
  have hw : r ∈ Set.Icc 332.15 334 :=
    ⟨by
      dsimp only [r]; linarith only [hL.1], by
      dsimp only [r]; linarith only [hL.2]⟩
  have hlevel : Real.log p + Real.log q + Real.log k = 4 * (L / 2) := by linarith only [hlev]
  have hscale : 4 * r / (1000433684769 / 1000000000000) = 2 * L := by
    dsimp only [r]
    ring
  have hs :=
    gaussian_shift_forward_early_197 ha hb hc hG.riemann (s := 1000433684769 / 1000000000000) hw
      (by norm_num only) (hlev.trans hscale.symm) ht hpa hpb hpc
  have htr : L / 2 ≤ r := by
    dsimp only [r]; linarith only [hL.1]
  apply
    early_pair_false ha hb hc hp hq hk hG ⟨hw.1, hw.2.trans (by norm_num only)⟩
      (quarter_main_conductor_k197 hw.1) htr hlevel ht hpa hpb hpc
      (gaussian_k197_third_principal hG.riemann hL) hs (third_linear_lower hL)
  norm_num only

/-- Under GRH, an odd uniform Korselt triple in the third K197 cell has a
prime Miller–Rabin witness below that cell's squared Gaussian radius. -/
theorem gaussian_k197_third_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (2661 / 4) (2665 / 4)) :
    let r := (1000433684769 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  intro r
  apply uniform_witness_of_pair_false hn ho hu (X := r ^ 2)
  intro p q k _ _ _ a b c ha hb hc hp hq hk hlev ht hsmall
  exact
    third_pair_false ha hb hc hp hq hk hG hL hlev ht (fun l hl hX ↦ (hsmall l hl hX).1)
      (fun l hl hX ↦ (hsmall l hl hX).2.1) (fun l hl hX ↦ (hsmall l hl hX).2.2)

private theorem fourth_linear_lower {L : ℝ} (hL : L ∈ Set.Icc (2665 / 4) (2669 / 4)) :
    let r := (500246832053 / 500000000000 : ℝ) * L / 2
    (-10.568105 : ℝ) ≤
      (0.71780481 - gaussianHalfCoeff197) * r -
        (3 / 4 + gaussianAuxMix197 quarterConductorProfile663) * (L / 2) := by
  intro r
  have hr : 0 ≤ r := by
    dsimp only [r]; linarith only [hL.1]
  have hL₀ : 0 ≤ L / 2 := by linarith only [hL.1]
  have h₁ := mul_le_mul_of_nonneg_right gaussian_half_upper_197 hr
  have h₂ := mul_le_mul_of_nonneg_right gaussian_conductor_upper_197 hL₀
  have h₃ : (-10.568105 : ℝ) ≤ (0.71780481 + 0.00692794) * r - (3 / 4 + 0.00676712) * (L / 2) := by
    dsimp only [r]
    linarith only [hL.2]
  linarith only [h₁, h₂, h₃]

private theorem fourth_pair_false {p q k : ℕ} [NeZero p] [NeZero q] [NeZero k]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ k}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hk : 2 ≤ k)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L : ℝ}
    (hL : L ∈ Set.Icc (2665 / 4) (2669 / 4)) (hlev : Real.log p + Real.log q + Real.log k = 2 * L)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3) :
    let r := (500246832053 / 500000000000 : ℝ) * L / 2
    (∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1) →
      (∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1) →
      (∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) → False := by
  intro r hpa hpb hpc
  have hw : r ∈ Set.Icc 332.15 334 :=
    ⟨by
      dsimp only [r]; linarith only [hL.1], by
      dsimp only [r]; linarith only [hL.2]⟩
  have hlevel : Real.log p + Real.log q + Real.log k = 4 * (L / 2) := by linarith only [hlev]
  have hscale : 4 * r / (500246832053 / 500000000000) = 2 * L := by
    dsimp only [r]
    ring
  have hs :=
    gaussian_shift_forward_early_197 ha hb hc hG.riemann (s := 500246832053 / 500000000000) hw
      (by norm_num only) (hlev.trans hscale.symm) ht hpa hpb hpc
  have htr : L / 2 ≤ r := by
    dsimp only [r]; linarith only [hL.1]
  apply
    early_pair_false ha hb hc hp hq hk hG ⟨hw.1, hw.2.trans (by norm_num only)⟩
      (quarter_main_conductor_k197 hw.1) htr hlevel ht hpa hpb hpc
      (gaussian_k197_fourth_principal hG.riemann hL) hs (fourth_linear_lower hL)
  norm_num only

/-- Under GRH, an odd uniform Korselt triple in the fourth K197 cell has a
prime Miller–Rabin witness below that cell's squared Gaussian radius. -/
theorem gaussian_k197_fourth_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (2665 / 4) (2669 / 4)) :
    let r := (500246832053 / 500000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  intro r
  apply uniform_witness_of_pair_false hn ho hu (X := r ^ 2)
  intro p q k _ _ _ a b c ha hb hc hp hq hk hlev ht hsmall
  exact
    fourth_pair_false ha hb hc hp hq hk hG hL hlev ht (fun l hl hX ↦ (hsmall l hl hX).1)
      (fun l hl hX ↦ (hsmall l hl hX).2.1) (fun l hl hX ↦ (hsmall l hl hX).2.2)

private noncomputable def k197Slope (s : ℝ) : ℝ :=
  (0.71780481 + 0.00692794) * s - (3 / 4 + 0.00676712)

private theorem wide_linear_lower {L U s : ℝ} (hL₀ : 0 ≤ L) (hL : L ≤ U) (hs : 1 ≤ s)
    (hm : k197Slope s ≤ 0) :
    k197Slope s * (U / 2) ≤
      (0.71780481 - gaussianHalfCoeff197) * (s * L / 2) -
        (3 / 4 + gaussianAuxMix197 quarterConductorProfile663) * (L / 2) := by
  have h₀ : 0 ≤ s * L / 2 := div_nonneg (mul_nonneg (zero_le_one.trans hs) hL₀) (by norm_num only)
  have h₁ := mul_le_mul_of_nonneg_right gaussian_half_upper_197 h₀
  have h₂ :=
    mul_le_mul_of_nonneg_right gaussian_conductor_upper_197
      (div_nonneg hL₀ (by norm_num only : (0 : ℝ) ≤ 2))
  have h₃ :=
    mul_le_mul_of_nonpos_left (div_le_div_of_nonneg_right hL (by norm_num only : (0 : ℝ) ≤ 2)) hm
  unfold k197Slope at h₃ ⊢
  linarith only [h₁, h₂, h₃]

/-- Convert a certified signed boundary and scalar margin to a rejecting
prime throughout the K197 window from radius 333.8 through 336. -/
private theorem wide_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {U s B : ℝ} (tight : Bool)
    (hL : Real.log n ≤ U) (hs : 1 ≤ s) (hm : k197Slope s ≤ 0)
    (hmargin :
      0 ≤
        (15.0472769 : ℝ) + 0.143227796 + (0.045488 - B) + (if tight then -2.878559 else -2.887559) +
              k197Slope s * (U / 2) -
            4 * 0.006305 -
            (if tight then 1.64042 else 1.64886) -
            0.000251 +
          0.00914) :
    let r := s * Real.log n / 2
    r ∈ Set.Icc (if tight then 1678 / 5 else 333.8) 336.9 →
      (-4 * (Chebyshev.psi (r ^ 2) - r ^ 2) * quarterWeight656 (r ^ 2) (r ^ 2) ≤ B) →
      ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  intro r hr hb
  apply uniform_witness_of_pair_false hn ho hu (X := r ^ 2)
  intro p q k _ _ _ a b c ha hb' hc hp hq hk hlev ht hsmall
  have hL₀ := Real.log_natCast_nonneg n
  have hscale : 4 * r / s = 2 * Real.log n := by
    dsimp only [r]
    apply (div_eq_iff (zero_lt_one.trans_le hs).ne').mpr
    ring
  have ht₀ : Real.log n / 2 ≤ r := by
    dsimp only [r]
    linarith only [mul_le_mul_of_nonneg_right hs hL₀]
  have hlevel : Real.log p + Real.log q + Real.log k = 4 * (Real.log n / 2) := by
    linarith only [hlev]
  have hpa l hl hcut := (hsmall l hl hcut).1
  have hpb l hl hcut := (hsmall l hl hcut).2.1
  have hpc l hl hcut := (hsmall l hl hcut).2.2
  have hr₃ : 333.8 ≤ r := by
    cases tight
    · exact hr.1
    · exact (by norm_num only : (333.8 : ℝ) ≤ 1678 / 5).trans hr.1
  have hshift :
    (if tight then -2.878559 else -2.887559 : ℝ) ≤
      (gaussianShiftedForward197 a r + gaussianShiftedForward197 b r +
          gaussianShiftedForward197 c r) +
        gaussianHalfCoeff197 * r := by
    cases tight
    · exact
        gaussian_shift_forward_from3338_197 ha hb' hc hG.riemann ⟨hr₃, hr.2⟩ hs
          (hlev.trans hscale.symm) ht hpa hpb hpc
    · exact
        gaussian_shift_forward_from3356 ha hb' hc hG.riemann hr hs (hlev.trans hscale.symm) ht hpa
          hpb hpc
  have hcond :
    4 * r * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤
      (if tight then 1.64042 else 1.64886 : ℝ) := by
    cases tight
    · exact quarter_main_conductor_k197 ((by norm_num only : (332.15 : ℝ) ≤ 333.8).trans hr₃)
    · exact quarter_main_conductor_from3356 hr.1
  have hmain :=
    gaussian_k197_wide_principal hG.riemann
      ⟨(by norm_num only : (663 / 2 : ℝ) ≤ 333.8).trans hr₃, hr.2⟩ hb
  refine
    early_pair_false ha hb' hc hp hq hk hG (B := 0.045488 - B)
      ⟨(by norm_num only : (332.15 : ℝ) ≤ 333.8).trans hr₃, hr.2⟩ hcond ht₀ hlevel ht hpa hpb hpc ?_
      hshift (wide_linear_lower hL₀ hL hs hm) ?_
  · simpa only [sub_eq_add_neg, add_assoc] using hmain
  · linarith only [hmargin]

/-- Under GRH, a uniform Korselt triple on compressed K197 cell 5 has
a prime rejecting base within its squared certified radius. -/
theorem gaussian_k197_cell5_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (2669 / 4) (2671 / 4)) :
    let r := (1000553460733 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    wide_witness hn ho hu hG (B := 0.095) false hL.2 (by norm_num only)
      (by norm_num only [k197Slope]) (by norm_num only [k197Slope, Bool.false_eq_true, ite_false])
  · exact
      ⟨by
        simp only [Bool.false_eq_true, ite_false]; linarith only [hL.1], by linarith only [hL.2]⟩
  · exact gaussian_k197_cell5_boundary_le hL

/-- Under GRH, a uniform Korselt triple on compressed K197 cell 6 has
a prime rejecting base within its squared certified radius. -/
theorem gaussian_k197_cell6_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (2671 / 4) (2675 / 4)) :
    let r := (1000583290791 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    wide_witness hn ho hu hG (B := 0.096) false hL.2 (by norm_num only)
      (by norm_num only [k197Slope]) (by norm_num only [k197Slope, Bool.false_eq_true, ite_false])
  · exact
      ⟨by
        simp only [Bool.false_eq_true, ite_false]; linarith only [hL.1], by linarith only [hL.2]⟩
  · exact gaussian_k197_cell6_boundary_le hL

/-- Under GRH, a uniform Korselt triple on compressed K197 cell 7 has
a prime rejecting base within its squared certified radius. -/
theorem gaussian_k197_cell7_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (2675 / 4) (2679 / 4)) :
    let r := (1000642814919 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    wide_witness hn ho hu hG (B := 0.087) false hL.2 (by norm_num only)
      (by norm_num only [k197Slope]) (by norm_num only [k197Slope, Bool.false_eq_true, ite_false])
  · exact
      ⟨by
        simp only [Bool.false_eq_true, ite_false]; linarith only [hL.1], by linarith only [hL.2]⟩
  · exact gaussian_k197_cell7_boundary_le hL

/-- Under GRH, a uniform Korselt triple on compressed K197 cell 8 has
a prime rejecting base within its squared certified radius. -/
theorem gaussian_k197_cell8_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (2679 / 4) (2683 / 4)) :
    let r := (1000702158417 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    wide_witness hn ho hu hG (B := 0.085) false hL.2 (by norm_num only)
      (by norm_num only [k197Slope]) (by norm_num only [k197Slope, Bool.false_eq_true, ite_false])
  · exact
      ⟨by
        simp only [Bool.false_eq_true, ite_false]; linarith only [hL.1], by linarith only [hL.2]⟩
  · exact gaussian_k197_cell8_boundary_le hL

/-- Under GRH, a uniform Korselt triple on compressed K197 cell 9 has
a prime rejecting base within its squared certified radius. -/
theorem gaussian_k197_cell9_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (2683 / 4) (2685 / 4)) :
    let r := (1000761322111 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    wide_witness hn ho hu hG (B := 0.111) true hL.2 (by norm_num only)
      (by norm_num only [k197Slope]) (by norm_num only [k197Slope, ite_true])
  · exact
      ⟨by
        simp only [ite_true]; linarith only [hL.1], by linarith only [hL.2]⟩
  · exact gaussian_k197_cell9_boundary_le hL

/-- Under GRH, a uniform Korselt triple on compressed K197 cell 10 has
a prime rejecting base within its squared certified radius. -/
theorem gaussian_k197_cell10_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (2685 / 4) (2686 / 4)) :
    let r := (1000790836787 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  intro r
  apply uniform_witness_of_pair_false hn ho hu (X := r ^ 2)
  intro p q k _ _ _ a b c ha hb hc hp hq hk hlev ht hsmall
  have hr : r ∈ Set.Icc (8397 / 25) 336.02 :=
    ⟨by
      dsimp only [r]; linarith only [hL.1], by
      dsimp only [r]; linarith only [hL.2]⟩
  have ht₀ : Real.log n / 2 ≤ r := by
    dsimp only [r]; linarith only [hL.1]
  have hscale : 4 * r / (1000790836787 / 1000000000000) = 2 * Real.log n := by
    dsimp only [r]
    ring
  have hlevel : Real.log p + Real.log q + Real.log k = 4 * (Real.log n / 2) := by
    linarith only [hlev]
  have hpa l hl hcut := (hsmall l hl hcut).1
  have hpb l hl hcut := (hsmall l hl hcut).2.1
  have hpc l hl hcut := (hsmall l hl hcut).2.2
  have hshift :=
    gaussian_shift_forward_cell10 ha hb hc hG.riemann hr (hlev.trans hscale.symm) ht hpa hpb hpc
  have hmain :=
    gaussian_k197_wide_principal hG.riemann
      ⟨(by norm_num only : (663 / 2 : ℝ) ≤ 8397 / 25).trans hr.1, hr.2.trans (by norm_num only)⟩
      (gaussian_k197_cell10_boundary_le hL)
  have hlin :=
    wide_linear_lower (s := 1000790836787 / 1000000000000) (Real.log_natCast_nonneg n) hL.2
      (by norm_num only) (by norm_num only [k197Slope])
  refine
    early_pair_false ha hb hc hp hq hk hG (B := 0.045488 - 0.142)
      ⟨(by norm_num only : (332.15 : ℝ) ≤ 8397 / 25).trans hr.1, hr.2.trans (by norm_num only)⟩
      (quarter_main_conductor_from33588 hr.1) ht₀ hlevel ht hpa hpb hpc ?_ hshift hlin ?_
  · simpa only [sub_eq_add_neg, add_assoc] using hmain
  · norm_num only [k197Slope]

/-- Under GRH, a uniform Korselt triple on compressed K197 cell 11 has
a prime rejecting base within its squared certified radius. -/
theorem gaussian_k197_cell11_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (1343 / 2) 672) :
    let r := (1000805577377 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    wide_witness hn ho hu hG (B := 0.130) true hL.2 (by norm_num only)
      (by norm_num only [k197Slope]) (by norm_num only [k197Slope, ite_true])
  · exact
      ⟨by
        simp only [ite_true]; linarith only [hL.1], by linarith only [hL.2]⟩
  · exact gaussian_k197_cell11_boundary_le hL

/-- Under GRH, a uniform Korselt triple on compressed K197 cell 12 has
a prime rejecting base within its squared certified radius. -/
theorem gaussian_k197_cell12_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc 672 673) :
    let r := (8006680201 / 8000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    wide_witness hn ho hu hG (B := 0.066) true hL.2 (by norm_num only)
      (by norm_num only [k197Slope]) (by norm_num only [k197Slope, ite_true])
  · exact
      ⟨by
        simp only [ite_true]; linarith only [hL.1], by linarith only [hL.2]⟩
  · exact gaussian_k197_cell12_boundary_le hL

private theorem mid_pair_false_with_abel {p q k : ℕ} [NeZero p] [NeZero q] [NeZero k]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ k}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r t B G M C P R₀ R₁ A : ℝ}
    (hr : 336.8 ≤ r)
    (htail : (∫ z in Set.Ioi (r ^ 2), gaussianDensity197 z) -
      (Chebyshev.psi (r ^ 2) - r ^ 2) * gaussianDensity197 (r ^ 2) +
      gaussianAbelError197 (r ^ 2) ≤ A)
    (hcond : 4 * t * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ C)
    (hcap : quarterAuxReflectCap656 r (-(21 / 8)) 103684 ≤ R₀)
    (hpos : R₁ ≤ 3 * quarterMainEuler656 (1 : DirichletCharacter ℂ 1) (r ^ 2))
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3) :
    (∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1) →
    (∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1) →
    (∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) →
    (let x := r ^ 2
    let W := fun n ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) x n).re
    let R := (quarterKernel656.transform x⁻¹).re
    let T := (∫ z in Set.Ioi x, gaussianDensity197 z) -
      (Chebyshev.psi x - x) * gaussianDensity197 x + gaussianAbelError197 x
    4 * (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, W n) - (∑' n, W n) +
      P +
      (gaussianShiftedForward197 a r + gaussianShiftedForward197 b r +
        gaussianShiftedForward197 c r)
      + (15.0472769 - 4 * T) ≤
      (3 / 4 + gaussianAuxMix197 quarterConductorProfile663) * t + 4 * t * R +
        3 * (centralGammaPair656 (1 : DirichletCharacter ℂ 1) x).re -
        (quarterMainEuler656 a x + quarterMainEuler656 b x + quarterMainEuler656 c x)) →
    (let x := r ^ 2
     let W := fun n ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) x n).re
     (0.71780481 : ℝ) * r + B <
       4 * (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, W n) - (∑' n, W n) -
         3 * (centralGammaPair656 (1 : DirichletCharacter ℂ 1) x).re) →
    (G ≤ (gaussianShiftedForward197 a r + gaussianShiftedForward197 b r +
      gaussianShiftedForward197 c r) + gaussianHalfCoeff197 * r) →
    (M ≤ (0.71780481 - gaussianHalfCoeff197) * r -
      (3 / 4 + gaussianAuxMix197 quarterConductorProfile663) * t) →
    (0 ≤ (15.0472769 : ℝ) + P + B + G + M - 4 * A - C -
      R₀ + R₁) →
    False := by
  intro hpa hpb hpc h hmain hs hlin hmargin
  have hr₃ : (328 : ℝ) ≤ r := (by norm_num only : (328 : ℝ) ≤ 336.8).trans hr
  have hr₂ : (322 : ℝ) ≤ r := (by norm_num only : (322 : ℝ) ≤ 328).trans hr₃
  have hB : (103684 : ℝ) ≤ r ^ 2 :=
    (by norm_num only : (103684 : ℝ) ≤ 322 ^ 2).trans
      (pow_le_pow_left₀ (by norm_num only) hr₂ 2)
  have hreflect := (quarter_main_reflect_cap_656 a b c hG.riemann hr₂ (B := 103684)
    (by norm_num only) (by norm_num only) (by exact_mod_cast hB) ht hpa hpb hpc).trans
    hcap
  dsimp only at h hmain htail
  ring_nf at h hs hmain hlin htail hreflect hpos hcond
  linarith only [h, hs, hmain, hlin, htail, hreflect, hpos, hcond, hmargin]

private theorem mid_pair_false {p q k : ℕ} [NeZero p] [NeZero q] [NeZero k]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ k}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r t B G M C P R₀ R₁ : ℝ}
    (hr : r ∈ Set.Icc 336.8 788)
    (hcond : 4 * t * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ C)
    (hcap : quarterAuxReflectCap656 r (-(21 / 8)) 103684 ≤ R₀)
    (hpos : R₁ ≤ 3 * quarterMainEuler656 (1 : DirichletCharacter ℂ 1) (r ^ 2))
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3) :
    (∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1) →
    (∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1) →
    (∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) →
    (let x := r ^ 2
    let W := fun n ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) x n).re
    let R := (quarterKernel656.transform x⁻¹).re
    let T := (∫ z in Set.Ioi x, gaussianDensity197 z) -
      (Chebyshev.psi x - x) * gaussianDensity197 x + gaussianAbelError197 x
    4 * (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, W n) - (∑' n, W n) +
      P +
      (gaussianShiftedForward197 a r + gaussianShiftedForward197 b r +
        gaussianShiftedForward197 c r)
      + (15.0472769 - 4 * T) ≤
      (3 / 4 + gaussianAuxMix197 quarterConductorProfile663) * t + 4 * t * R +
        3 * (centralGammaPair656 (1 : DirichletCharacter ℂ 1) x).re -
        (quarterMainEuler656 a x + quarterMainEuler656 b x + quarterMainEuler656 c x)) →
    (let x := r ^ 2
     let W := fun n ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) x n).re
     (0.71780481 : ℝ) * r + B <
       4 * (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, W n) - (∑' n, W n) -
         3 * (centralGammaPair656 (1 : DirichletCharacter ℂ 1) x).re) →
    (G ≤ (gaussianShiftedForward197 a r + gaussianShiftedForward197 b r +
      gaussianShiftedForward197 c r) + gaussianHalfCoeff197 * r) →
    (M ≤ (0.71780481 - gaussianHalfCoeff197) * r -
      (3 / 4 + gaussianAuxMix197 quarterConductorProfile663) * t) →
    (0 ≤ (15.0472769 : ℝ) + P + B + G + M - 4 * 0.006305 - C -
      R₀ + R₁) →
    False := by
  exact mid_pair_false_with_abel hG hr.1 (gaussian_abel_tail_through788 hr) hcond hcap hpos ht

/-- Convert a certified signed boundary and scalar margin to a rejecting
prime throughout the K197 window from radius 336.8 through 342.9. -/
private theorem mid_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {U s B : ℝ} (tight : Bool)
    (hL : Real.log n ≤ U) (hs : (if tight then 1.001 else 1) ≤ s) (hm : k197Slope s ≤ 0)
    (hmargin :
      0 ≤
        (15.0472769 : ℝ) + 0.136227796 + (0.044128 - B) + (if tight then -2.865764 else -2.873664) +
              k197Slope s * (U / 2) -
            4 * 0.006305 -
            1.64042 -
            0.000255 +
          0.00878) :
    let r := s * Real.log n / 2
    r ∈ Set.Icc (if tight then 338 else 336.8) 342.9 →
      (-4 * (Chebyshev.psi (r ^ 2) - r ^ 2) * quarterWeight656 (r ^ 2) (r ^ 2) ≤ B) →
      ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  intro r hr hb
  have hs₁ : 1 ≤ s := by
    cases tight
    · exact hs
    · exact (by norm_num only : (1 : ℝ) ≤ 1.001).trans hs
  have hrw : r ∈ Set.Icc 336.8 342.9 := by
    cases tight
    · exact hr
    · exact ⟨(by norm_num only : (336.8 : ℝ) ≤ 338).trans hr.1, hr.2⟩
  apply uniform_witness_of_pair_false hn ho hu (X := r ^ 2)
  intro p q k _ _ _ a b c ha hb' hc hp hq hk hlev ht hsmall
  have hL₀ := Real.log_natCast_nonneg n
  have hscale : 4 * r / s = 2 * Real.log n := by
    dsimp only [r]
    apply (div_eq_iff (zero_lt_one.trans_le hs₁).ne').mpr
    ring
  have ht₀ : Real.log n / 2 ≤ r := by
    dsimp only [r]
    linarith only [mul_le_mul_of_nonneg_right hs₁ hL₀]
  have hlevel : Real.log p + Real.log q + Real.log k = 4 * (Real.log n / 2) := by
    linarith only [hlev]
  have hpa l hl hcut := (hsmall l hl hcut).1
  have hpb l hl hcut := (hsmall l hl hcut).2.1
  have hpc l hl hcut := (hsmall l hl hcut).2.2
  have hshift :
    (if tight then -2.865764 else -2.873664 : ℝ) ≤
      (gaussianShiftedForward197 a r + gaussianShiftedForward197 b r +
          gaussianShiftedForward197 c r) +
        gaussianHalfCoeff197 * r := by
    cases tight
    · exact
        gaussian_shift_forward_mid_197 ha hb' hc hG.riemann hrw hs₁ (hlev.trans hscale.symm) ht hpa
          hpb hpc
    · exact
        gaussian_shift_forward_from338_197 ha hb' hc hG.riemann hr hs (hlev.trans hscale.symm) ht
          hpa hpb hpc
  have hcond :=
    quarter_main_conductor_from3356 ((by norm_num only : (1678 / 5 : ℝ) ≤ 336.8).trans hrw.1)
  have hmain :=
    gaussian_k197_mid_principal hG.riemann
      ⟨(by norm_num only : (663 / 2 : ℝ) ≤ 336.8).trans hrw.1, hrw.2⟩ hb
  have hR : 0 ≤ (quarterKernel656.transform (r ^ 2)⁻¹).re :=
    quarterKernel656.mellin_nonneg _
      (inv_pos.mpr (sq_pos_of_pos ((by norm_num only : (0 : ℝ) < 336.8).trans_le hrw.1)))
  have hc' :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht₀ (by norm_num only : (0 : ℝ) ≤ 4))
          hR).trans
      hcond
  have hcompare := gaussian_erased_comparison_197 ha hb' hc hp hq hk hG hrw hlevel ht hpa hpb hpc
  have hrf : r ∈ Set.Icc 328 342.9 := ⟨(by norm_num only : (328 : ℝ) ≤ 336.8).trans hrw.1, hrw.2⟩
  refine
    mid_pair_false (a := a) (b := b) (c := c) hG (B := 0.044128 - B)
      ⟨hrw.1, hrw.2.trans (by norm_num only)⟩ hc' (k197_mid_main_reflect_box hrf)
      (gaussian_k197_mid_reflect_credit hrf) ht hpa hpb hpc hcompare ?_ hshift
      (wide_linear_lower hL₀ hL hs₁ hm) ?_
  · simpa only [sub_eq_add_neg, add_assoc] using hmain
  · linarith only [hmargin]

/-- Under GRH, a uniform Korselt triple on compressed K197 cell 13 has
a prime rejecting base within its squared certified radius. -/
theorem gaussian_k197_cell13_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc 673 (1347 / 2)) :
    let r := (500446893623 / 500000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    mid_witness hn ho hu hG (B := 0.049) false hL.2
      (by norm_num only [Bool.false_eq_true, ite_false]) (by norm_num only [k197Slope])
      (by norm_num only [k197Slope, Bool.false_eq_true, ite_false])
  · exact
      ⟨by
        simp only [Bool.false_eq_true, ite_false]; linarith only [hL.1], by linarith only [hL.2]⟩
  · exact gaussian_k197_cell13_boundary_le hL

/-- Under GRH, a uniform Korselt triple on compressed K197 cell 14 has
a prime rejecting base within its squared certified radius. -/
theorem gaussian_k197_cell14_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (1347 / 2) 674) :
    let r := (50046155091 / 50000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    mid_witness hn ho hu hG (B := 0.111) false hL.2
      (by norm_num only [Bool.false_eq_true, ite_false]) (by norm_num only [k197Slope])
      (by norm_num only [k197Slope, Bool.false_eq_true, ite_false])
  · exact
      ⟨by
        simp only [Bool.false_eq_true, ite_false]; linarith only [hL.1], by linarith only [hL.2]⟩
  · exact gaussian_k197_cell14_boundary_le hL

/-- Under GRH, a uniform Korselt triple on compressed K197 cell 15 has
a prime rejecting base within its squared certified radius. -/
theorem gaussian_k197_cell15_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc 674 (1349 / 2)) :
    let r := (50046155091 / 50000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    mid_witness hn ho hu hG (B := 0.111) false hL.2
      (by norm_num only [Bool.false_eq_true, ite_false]) (by norm_num only [k197Slope])
      (by norm_num only [k197Slope, Bool.false_eq_true, ite_false])
  · exact
      ⟨by
        simp only [Bool.false_eq_true, ite_false]; linarith only [hL.1], by linarith only [hL.2]⟩
  · exact gaussian_k197_cell15_boundary_le hL

/-- Under GRH, a uniform Korselt triple on compressed K197 cell 16 has
a prime rejecting base within its squared certified radius. -/
theorem gaussian_k197_cell16_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (1349 / 2) (1351 / 2)) :
    let r := (1000981598501 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    mid_witness hn ho hu hG (B := 0.096) false hL.2
      (by norm_num only [Bool.false_eq_true, ite_false]) (by norm_num only [k197Slope])
      (by norm_num only [k197Slope, Bool.false_eq_true, ite_false])
  · exact
      ⟨by
        simp only [Bool.false_eq_true, ite_false]; linarith only [hL.1], by linarith only [hL.2]⟩
  · exact gaussian_k197_cell16_boundary_le hL

/-- Under GRH, a uniform Korselt triple on compressed K197 cell 17 has
a prime rejecting base within its squared certified radius. -/
theorem gaussian_k197_cell17_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (1351 / 2) 676) :
    let r := (125129989903 / 125000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    mid_witness hn ho hu hG (B := 0.130) true hL.2 (by norm_num only [ite_true])
      (by norm_num only [k197Slope]) (by norm_num only [k197Slope, ite_true])
  · exact
      ⟨by
        simp only [ite_true]; linarith only [hL.1], by linarith only [hL.2]⟩
  · exact gaussian_k197_cell17_boundary_le hL

private theorem local_boundary {r a A B E D : ℝ} (ha : 0 < a) (hr : a ≤ r) (hlo : A ≤ r ^ 2)
    (hhi : r ^ 2 ≤ B) (he : 0 ≤ E) (hψ : ∀ x : ℝ, A ≤ x → x ≤ B → -E ≤ Chebyshev.psi x - x)
    (hD : 4 * E * 0.09319732 / a ≤ D) :
    (-4 : ℝ) * (Chebyshev.psi (r ^ 2) - r ^ 2) * quarterWeight656 (r ^ 2) (r ^ 2) ≤ D := by
  have h := quarter_bridge_boundary_lower ha hr he (hψ (r ^ 2) hlo hhi)
  linarith only [h, hD]

private theorem local_growth_credit {r : ℝ} (hr : r ∈ Set.Icc 338 342.9) :
    (0.1414 : ℝ) ≤
      ∑ n ∈ fixedPowers663.erase (337 ^ 2),
        4 * (ArithmeticFunction.vonMangoldt n * quarterWeight656 (r ^ 2) n) :=
  erased_growth_at_radius hr (by norm_num only) (by linarith only [log_radius_gain hr.1])
    (gaussian_growth_from338 hr.1) (by norm_num only)

private theorem late_growth_credit {r : ℝ} (ha : (339916 / 1000 : ℝ) ≤ r) (hb : r ≤ 342.9) :
    (0.1426 : ℝ) ≤
      ∑ n ∈ fixedPowers663.erase (337 ^ 2),
        4 * (ArithmeticFunction.vonMangoldt n * quarterWeight656 (r ^ 2) n) := by
  have hr := (by norm_num only : (338 : ℝ) ≤ 339916 / 1000).trans ha
  exact
    erased_growth_at_radius ⟨hr, hb⟩ (by norm_num only) (by linarith only [log_radius_gain hr])
      (gaussian_growth_from339916 ha) (by norm_num only)

private theorem local_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {U s B a T P C F u D : ℝ}
    (hL : Real.log n ≤ U) (hs : 1.00106 ≤ s) (hm : k197Slope s ≤ 0) (ha₀ : (8459 / 25 : ℝ) ≤ a)
    (hD : 0 ≤ D) (hDu : D * u ≤ 20.74) (huR : u ≤ 342.9)
    (hT : ∀ r : ℝ, a ≤ r → T ≤ gaussianTheta197 r) (hneg : T ≤ 0)
    (hP : P ≤ T / 1.00106 + D - 0.000069)
    (hC : ∀ r : ℝ, a ≤ r → 4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ C)
    (hgain :
      ∀ r : ℝ,
        r ∈ Set.Icc a u →
          F ≤
            ∑ n ∈ fixedPowers663.erase (337 ^ 2),
              4 * (ArithmeticFunction.vonMangoldt n * quarterWeight656 (r ^ 2) n))
    (hmargin :
      0 ≤
        (15.0472769 : ℝ) + F + (0.044128 - B) + P + k197Slope s * (U / 2) - 4 * 0.006305 - C -
            0.000255 +
          0.00878) :
    let r := s * Real.log n / 2
    r ∈ Set.Icc a u →
      (-4 * (Chebyshev.psi (r ^ 2) - r ^ 2) * quarterWeight656 (r ^ 2) (r ^ 2) ≤ B) →
      ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  intro r hr₀ hb
  have hr : r ∈ Set.Icc (8459 / 25) u := ⟨ha₀.trans hr₀.1, hr₀.2⟩
  apply uniform_witness_of_pair_false hn ho hu (X := r ^ 2)
  intro p q k _ _ _ a b c ha hb' hc hp hq hk hlev ht hsmall
  have hs₁ : 1 ≤ s := (by norm_num only : (1 : ℝ) ≤ 1.00106).trans hs
  have hscale : r / s = Real.log n / 2 := by
    dsimp only [r]
    apply (div_eq_iff (zero_lt_one.trans_le hs₁).ne').mpr
    ring
  have hlevel : Real.log p + Real.log q + Real.log k = 4 * (Real.log n / 2) := by
    linarith only [hlev]
  have hrw : r ∈ Set.Icc 338 342.9 :=
    ⟨(by norm_num only : (338 : ℝ) ≤ 8459 / 25).trans hr.1, hr.2.trans huR⟩
  have hpa l hl hcut := (hsmall l hl hcut).1
  have hpb l hl hcut := (hsmall l hl hcut).2.1
  have hpc l hl hcut := (hsmall l hl hcut).2.2
  have hshift :=
    gaussian_shift_forward_local_197 ha hb' hc hG.riemann hr hD hDu (huR.trans (by norm_num only))
      hs (hT r hr₀.1)
      (by
        intro t ht
        exact
          (mul_le_mul_of_nonpos_left ht
                (div_nonpos_of_nonpos_of_nonneg hneg (by norm_num only))).trans_eq
            (by ring))
      hP
      (by
        rw [mul_div_assoc, hscale]; exact hlevel)
      ht hpa hpb hpc
  have hcond := hC r hr₀.1
  rw [hscale] at hcond
  have hmain :=
    gaussian_k197_mid_principal hG.riemann
      ⟨(by norm_num only : (663 / 2 : ℝ) ≤ 338).trans hrw.1, hrw.2⟩ hb
  have hcompare :=
    erased_comparison_of_gain ha hb' hc hp hq hk hG
      ⟨(by norm_num only : (336.8 : ℝ) ≤ 338).trans hrw.1, hrw.2⟩ hlevel ht hpa hpb hpc
      (hgain r hr₀)
  have hrB : r ∈ Set.Icc 336.8 788 :=
    ⟨(by norm_num only : (336.8 : ℝ) ≤ 338).trans hrw.1, hrw.2.trans (by norm_num only)⟩
  have hrF : r ∈ Set.Icc 328 342.9 := ⟨(by norm_num only : (328 : ℝ) ≤ 338).trans hrw.1, hrw.2⟩
  refine
    mid_pair_false (a := a) (b := b) (c := c) hG (B := 0.044128 - B) hrB hcond
      (k197_mid_main_reflect_box hrF) (gaussian_k197_mid_reflect_credit hrF) ht hpa hpb hpc hcompare
      ?_ hshift (wide_linear_lower (Real.log_natCast_nonneg n) hL hs₁ hm) ?_
  · simpa only [sub_eq_add_neg, add_assoc] using hmain
  · linarith only [hmargin]

private theorem late_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {U s B a T P C F v : ℝ}
    (hL : Real.log n ≤ U) (hs : 1.00106 ≤ s) (hm : k197Slope s ≤ 0) (ha₀ : (340 : ℝ) ≤ a)
    (hT : ∀ r : ℝ, a ≤ r → T ≤ gaussianTheta197 r) (hv : 0 < v) (hvs : v ≤ s) (hneg : T ≤ 0)
    (hP : P ≤ T / v + 0.05992 - 0.000069)
    (hC : ∀ r : ℝ, a ≤ r → 4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ C)
    (hF :
      ∀ r : ℝ,
        r ∈ Set.Icc a 346.1 →
          F ≤
            ∑ n ∈ (fixedPowers663.erase (337 ^ 2)).erase (7 ^ 6),
              4 * (ArithmeticFunction.vonMangoldt n * quarterWeight656 (r ^ 2) n))
    (hmargin :
      0 ≤
        (15.0472769 : ℝ) + F + (0.043358 - B) + P + k197Slope s * (U / 2) - 4 * 0.006305 - C -
            0.00027 +
          0.0086) :
    let r := s * Real.log n / 2
    r ∈ Set.Icc a 346.1 →
      (-4 * (Chebyshev.psi (r ^ 2) - r ^ 2) * quarterWeight656 (r ^ 2) (r ^ 2) ≤ B) →
      ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  intro r hra hb
  have hr₀ : r ∈ Set.Icc 340 346.1 := ⟨ha₀.trans hra.1, hra.2⟩
  apply uniform_witness_of_pair_false hn ho hu (X := r ^ 2)
  intro p q k _ _ _ a b c ha hb' hc hp hq hk hlev ht hsmall
  have hs₁ : 1 ≤ s := (by norm_num only : (1 : ℝ) ≤ 1.00106).trans hs
  have hscale : r / s = Real.log n / 2 := by
    dsimp only [r]
    apply (div_eq_iff (zero_lt_one.trans_le hs₁).ne').mpr
    ring
  have hlevel : Real.log p + Real.log q + Real.log k = 4 * (Real.log n / 2) := by
    linarith only [hlev]
  have hpa l hl hcut := (hsmall l hl hcut).1
  have hpb l hl hcut := (hsmall l hl hcut).2.1
  have hpc l hl hcut := (hsmall l hl hcut).2.2
  have hspos : 0 < s := hv.trans_le hvs
  have hθ : T / v ≤ gaussianTheta197 r / s := by
    apply (le_div_iff₀ hspos).mpr
    refine (mul_le_mul_of_nonpos_left hvs (div_nonpos_of_nonpos_of_nonneg hneg hv.le)).trans ?_
    rw [div_mul_cancel₀ _ hv.ne']
    exact hT r hra.1
  have hpole : (0.05992 : ℝ) ≤ gaussianNegPole197 / r := by
    apply (le_div_iff₀ ((by norm_num only : (0 : ℝ) < 340).trans_le hr₀.1)).mpr
    linarith only [hr₀.2, gaussian_neg_pole_lower_197]
  have hcost : P + 0.000069 ≤ gaussianTheta197 r / s + gaussianNegPole197 / r := by
    linarith only [hP, hθ, hpole]
  have hshift₀ :=
    shift_forward_of_refl ha hb' hc hG.riemann ((by norm_num only : (328 : ℝ) ≤ 340).trans hr₀.1)
      (by
        rw [mul_div_assoc, hscale]; exact hlevel)
      ht hpa hpb hpc hcost
      (gaussian_joint_to34610 hG.riemann
        ⟨(by norm_num only : (332.15 : ℝ) ≤ 340).trans hr₀.1, hr₀.2⟩)
  have hshift :
    P ≤
      (gaussianShiftedForward197 a r + gaussianShiftedForward197 b r +
          gaussianShiftedForward197 c r) +
        gaussianHalfCoeff197 * r := by
    linarith only [hshift₀]
  have hcond := hC r hra.1
  rw [hscale] at hcond
  have hmain :=
    gaussian_k197_principal_to34610 hG.riemann
      ⟨(by norm_num only : (663 / 2 : ℝ) ≤ 340).trans hr₀.1, hr₀.2⟩ hb
  have hcompare :=
    retained_comparison_of_gain ha hb' hc hp hq hk hG
      ((by norm_num only : (336.8 : ℝ) ≤ 340).trans hr₀.1)
      ((fixedPowers663.erase (337 ^ 2)).erase (7 ^ 6)) (fun _ hn ↦ Finset.mem_of_mem_erase hn)
      (fun _ hn ↦ retained_without343_cut hr₀ hn) hlevel ht hpa hpb hpc (hF r hra)
  have hrF : r ∈ Set.Icc 328 346.1 := ⟨(by norm_num only : (328 : ℝ) ≤ 340).trans hr₀.1, hr₀.2⟩
  refine
    mid_pair_false (a := a) (b := b) (c := c) hG (B := 0.043358 - B)
      ⟨(by norm_num only : (336.8 : ℝ) ≤ 340).trans hr₀.1, hr₀.2.trans (by norm_num only)⟩ hcond
      (k197_main_reflect_to34610 hrF) (gaussian_k197_reflect_credit_to34610 hrF) ht hpa hpb hpc
      hcompare ?_ hshift (wide_linear_lower (Real.log_natCast_nonneg n) hL hs₁ hm) ?_
  · simpa only [sub_eq_add_neg, add_assoc] using hmain
  · linarith only [hmargin]

private theorem local_boundary_of_cell {L l u s a A B E D : ℝ} (ha : 0 < a) (hL : L ∈ Set.Icc l u)
    (hs : 1.00106 ≤ s) (hl : 0 ≤ l) (hR : a ≤ s * l / 2) (hA : A ≤ (s * l / 2) ^ 2)
    (hB : (s * u / 2) ^ 2 ≤ B) (he : 0 ≤ E) (hψ : ∀ x : ℝ, A ≤ x → x ≤ B → -E ≤ Chebyshev.psi x - x)
    (hD : 4 * E * 0.09319732 / a ≤ D) :
    let r := s * L / 2
    (-4 : ℝ) * (Chebyshev.psi (r ^ 2) - r ^ 2) * quarterWeight656 (r ^ 2) (r ^ 2) ≤ D := by
  intro r
  have hs₀ : 0 ≤ s := (by norm_num only : (0 : ℝ) ≤ 1.00106).trans hs
  have hlo : s * l / 2 ≤ r :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hL.1 hs₀) (by norm_num only)
  have hhi : r ≤ s * u / 2 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hL.2 hs₀) (by norm_num only)
  have hp : 0 ≤ s * l / 2 := div_nonneg (mul_nonneg hs₀ hl) (by norm_num only)
  exact
    local_boundary ha (hR.trans hlo) (hA.trans (pow_le_pow_left₀ hp hlo 2))
      ((pow_le_pow_left₀ (hp.trans hlo) hhi 2).trans hB) he hψ hD

/-- Under GRH, a uniform Korselt triple on compressed K197 cell 18 has
a prime rejecting base within its squared certified radius. -/
theorem gaussian_k197_cell18_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc 676 (2705 / 4)) :
    let r := (1001069013851 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    local_witness hn ho hu hG (B := 0.15095) (a := 8459 / 25) (P := -2.86259) (u := 340.05) (D :=
      0.06099) hL.2 (by norm_num only) (by norm_num only [k197Slope]) le_rfl (by norm_num only)
      (by norm_num only) (by norm_num only) (fun _ hr ↦ theta_from33836 hr) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ gaussian_main_conductor_local_197 hr (by norm_num only)) (F :=
      0.1414)
      (fun _ hr ↦
        local_growth_credit
          ⟨(by norm_num only : (338 : ℝ) ≤ _).trans hr.1, hr.2.trans (by norm_num only)⟩)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 114488) (B := 114574) (E := 137) (a := 8459 / 25)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell18 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple on compressed K197 cell 19 has
a prime rejecting base within its squared certified radius. -/
theorem gaussian_k197_cell19_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (2705 / 4) (1353 / 2)) :
    let r := (1001083544773 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    local_witness hn ho hu hG (B := 0.14985) (a := 8459 / 25) (P := -2.86259) (u := 340.05) (D :=
      0.06099) hL.2 (by norm_num only) (by norm_num only [k197Slope]) le_rfl (by norm_num only)
      (by norm_num only) (by norm_num only) (fun _ hr ↦ theta_from33836 hr) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ gaussian_main_conductor_local_197 hr (by norm_num only)) (F :=
      0.1414)
      (fun _ hr ↦
        local_growth_credit
          ⟨(by norm_num only : (338 : ℝ) ≤ _).trans hr.1, hr.2.trans (by norm_num only)⟩)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 114576) (B := 114662) (E := 136) (a := 8459 / 25)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell19 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple on compressed K197 cell 20 has
a prime rejecting base within its squared certified radius. -/
theorem gaussian_k197_cell20_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (1353 / 2) 677) :
    let r := (200219612957 / 200000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    local_witness hn ho hu hG (B := 0.12230) (a := 8459 / 25) (P := -2.86259) (u := 340.05) (D :=
      0.06099) hL.2 (by norm_num only) (by norm_num only [k197Slope]) le_rfl (by norm_num only)
      (by norm_num only) (by norm_num only) (fun _ hr ↦ theta_from33836 hr) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ gaussian_main_conductor_local_197 hr (by norm_num only)) (F :=
      0.1414)
      (fun _ hr ↦
        local_growth_credit
          ⟨(by norm_num only : (338 : ℝ) ≤ _).trans hr.1, hr.2.trans (by norm_num only)⟩)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 114664) (B := 114835) (E := 111) (a := 8459 / 25)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell20 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple on compressed K197 cell 21 has
a prime rejecting base within its squared certified radius. -/
theorem gaussian_k197_cell21_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc 677 (1355 / 2)) :
    let r := (7821305251 / 7812500000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    local_witness hn ho hu hG (B := 0.135) (a := 8459 / 25) (P := -2.86259) (u := 340.05) (D :=
      0.06099) hL.2 (by norm_num only) (by norm_num only [k197Slope]) le_rfl (by norm_num only)
      (by norm_num only) (by norm_num only) (fun _ hr ↦ theta_from33836 hr) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ gaussian_main_conductor_local_197 hr (by norm_num only)) (F :=
      0.1414)
      (fun _ hr ↦
        local_growth_credit
          ⟨(by norm_num only : (338 : ℝ) ≤ _).trans hr.1, hr.2.trans (by norm_num only)⟩)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact gaussian_k197_cell21_boundary_le hL

/-- Under GRH, a uniform Korselt triple on compressed K197 cell 22 has
a prime rejecting base within its squared certified radius. -/
theorem gaussian_k197_cell22_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (1355 / 2) 678) :
    let r := (125144504497 / 125000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    local_witness hn ho hu hG (B := 0.140) (a := 8459 / 25) (P := -2.86259) (u := 340.05) (D :=
      0.06099) hL.2 (by norm_num only) (by norm_num only [k197Slope]) le_rfl (by norm_num only)
      (by norm_num only) (by norm_num only) (fun _ hr ↦ theta_from33836 hr) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ gaussian_main_conductor_local_197 hr (by norm_num only)) (F :=
      0.1414)
      (fun _ hr ↦
        local_growth_credit
          ⟨(by norm_num only : (338 : ℝ) ≤ _).trans hr.1, hr.2.trans (by norm_num only)⟩)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact gaussian_k197_cell22_boundary_le hL

/-- Under GRH, a uniform Korselt triple on compressed K197 cell 23 has
a prime rejecting base within its squared certified radius. -/
theorem gaussian_k197_cell23_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc 678 (1357 / 2)) :
    let r := (1001184956427 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    local_witness hn ho hu hG (B := 0.150) (a := 1697 / 5) (P := -2.85754) (u := 340.05) (D :=
      0.06099) hL.2 (by norm_num only) (by norm_num only [k197Slope]) (by norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only) (fun _ hr ↦ theta_from3394 hr)
      (by norm_num only) (by norm_num only)
      (fun _ hr ↦
        gaussian_main_conductor_local_197 ((by norm_num only : (8459 / 25 : ℝ) ≤ 1697 / 5).trans hr)
          (by norm_num only))
      (F := 0.1414)
      (fun _ hr ↦
        local_growth_credit
          ⟨(by norm_num only : (338 : ℝ) ≤ _).trans hr.1, hr.2.trans (by norm_num only)⟩)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact gaussian_k197_cell23_boundary_le hL

/-- Under GRH, a uniform Korselt triple on compressed K197 cell 24 has
a prime rejecting base within its squared certified radius. -/
theorem gaussian_k197_cell24_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (1357 / 2) (2715 / 4)) :
    let r := (1001213833581 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    local_witness hn ho hu hG (B := 0.141) (a := 1697 / 5) (P := -2.85754) (u := 340.05) (D :=
      0.06099) hL.2 (by norm_num only) (by norm_num only [k197Slope]) (by norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only) (fun _ hr ↦ theta_from3394 hr)
      (by norm_num only) (by norm_num only)
      (fun _ hr ↦
        gaussian_main_conductor_local_197 ((by norm_num only : (8459 / 25 : ℝ) ≤ 1697 / 5).trans hr)
          (by norm_num only))
      (F := 0.1414)
      (fun _ hr ↦
        local_growth_credit
          ⟨(by norm_num only : (338 : ℝ) ≤ _).trans hr.1, hr.2.trans (by norm_num only)⟩)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact gaussian_k197_cell24_boundary_le hL

/-- Under GRH, a uniform Korselt triple on compressed K197 cell 25 has
a prime rejecting base within its squared certified radius. -/
theorem gaussian_k197_cell25_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (2715 / 4) 679) :
    let r := (1001228255951 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    local_witness hn ho hu hG (B := 0.15756) (a := 33979 / 100) (P := -2.85571) (u := 340.05) (D :=
      0.06099) hL.2 (by norm_num only) (by norm_num only [k197Slope]) (by norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only) (fun _ hr ↦ theta_from33979 hr)
      (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from33979 hr (by norm_num only)) (F := 0.1414)
      (fun _ hr ↦
        local_growth_credit
          ⟨(by norm_num only : (338 : ℝ) ≤ _).trans hr.1, hr.2.trans (by norm_num only)⟩)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 115458) (B := 115544) (E := 143) (a := 8459 / 25)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell25 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in this K197 range has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell26_left_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc 679 679.011) :
    let r := (1001228255951 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    local_witness hn ho hu hG (B := 0.16013) (a := 339916 / 1000) (P := -2.85513) (u := 340.05)
      (D := 0.06099) hL.2 (by norm_num only) (by norm_num only [k197Slope]) (by norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only) (fun _ hr ↦ theta_from339916 hr)
      (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from339916 hr (by norm_num only)) (F := 0.1426)
      (fun _ hr ↦ late_growth_credit hr.1 (hr.2.trans (by norm_num only)))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 115543) (B := 115587) (E := 146) (a := 339916 / 1000)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell26 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in this K197 range has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell26_right_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc 679.011 (5433 / 8)) :
    let r := (1001228255951 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    local_witness hn ho hu hG (B := 0.15464) (a := 339916 / 1000) (P := -2.85513) (u := 340.05)
      (D := 0.06099) hL.2 (by norm_num only) (by norm_num only [k197Slope]) (by norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only) (fun _ hr ↦ theta_from339916 hr)
      (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from339916 hr (by norm_num only)) (F := 0.1426)
      (fun _ hr ↦ late_growth_credit hr.1 (hr.2.trans (by norm_num only)))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 115547) (B := 115587) (E := 141) (a := 339916 / 1000)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦
          AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell26_right hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in this K197 range has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell27_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (5433 / 8) (2717 / 4)) :
    let r := (1001228255951 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    local_witness hn ho hu hG (B := 0.15464) (a := 339916 / 1000) (P := -2.85513) (u := 340.05)
      (D := 0.06099) hL.2 (by norm_num only) (by norm_num only [k197Slope]) (by norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only) (fun _ hr ↦ theta_from339916 hr)
      (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from339916 hr (by norm_num only)) (F := 0.1426)
      (fun _ hr ↦ late_growth_credit hr.1 (hr.2.trans (by norm_num only)))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 115586) (B := 115629) (E := 141) (a := 339916 / 1000)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell27 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple on K197 cell 28 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell28_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (2717 / 4) (1359 / 2)) :
    let r := (50062853417 / 50000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    local_witness hn ho hu hG (B := 0.15903) (a := 339916 / 1000) (P := -2.85550) (u := 341.61)
      (D := 0.06071) hL.2 (by norm_num only) (by norm_num only [k197Slope]) (by norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only) (fun _ hr ↦ theta_from339916 hr)
      (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from339916 hr (by norm_num only)) (F := 0.1426)
      (fun _ hr ↦ late_growth_credit hr.1 (hr.2.trans (by norm_num only)))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 115635) (B := 115721) (E := 145) (a := 339916 / 1000)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell28 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple on the left part of K197 cell 29
has a prime rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell29_left_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (1359 / 2) 679.52) :
    let r := (50062853417 / 50000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    local_witness hn ho hu hG (B := 0.16561) (a := 340) (P := -2.85514) (u := 340.25) (D := 0.06095)
      hL.2 (by norm_num only) (by norm_num only [k197Slope]) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only)
      (fun _ hr ↦ theta_from339916 ((by norm_num only : (339916 / 1000 : ℝ) ≤ 340).trans hr))
      (by norm_num only) (by norm_num only)
      (fun _ hr ↦
        gaussian_main_conductor_from339916 ((by norm_num only : (339916 / 1000 : ℝ) ≤ 340).trans hr)
          (by norm_num only))
      (F := 0.14908) (fun _ hr ↦ retained_gain_from340 ⟨hr.1, hr.2.trans (by norm_num only)⟩)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 115720) (B := 115764) (E := 151) (a := 340) (by norm_num only) hL
        (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell29 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple on the right part of K197 cell 29
has a prime rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell29_right_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc 679.52 (5437 / 8)) :
    let r := (50062853417 / 50000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    local_witness hn ho hu hG (B := 0.15903) (a := 340) (P := -2.85514) (u := 340.25) (D := 0.06095)
      hL.2 (by norm_num only) (by norm_num only [k197Slope]) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only)
      (fun _ hr ↦ theta_from339916 ((by norm_num only : (339916 / 1000 : ℝ) ≤ 340).trans hr))
      (by norm_num only) (by norm_num only)
      (fun _ hr ↦
        gaussian_main_conductor_from339916 ((by norm_num only : (339916 / 1000 : ℝ) ≤ 340).trans hr)
          (by norm_num only))
      (F := 0.14908) (fun _ hr ↦ retained_gain_from340 ⟨hr.1, hr.2.trans (by norm_num only)⟩)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 115727) (B := 115764) (E := 145) (a := 340) (by norm_num only) hL
        (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦
          AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell29_right hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple on K197 cell 30 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell30_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (5437 / 8) (2719 / 4)) :
    let r := (50062853417 / 50000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    local_witness hn ho hu hG (B := 0.139) (a := 339916 / 1000) (P := -2.85550) (u := 341.61) (D :=
      0.06071) hL.2 (by norm_num only) (by norm_num only [k197Slope]) (by norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only) (fun _ hr ↦ theta_from339916 hr)
      (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from339916 hr (by norm_num only)) (F := 0.1426)
      (fun _ hr ↦ late_growth_credit hr.1 (hr.2.trans (by norm_num only)))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact gaussian_k197_cell30_boundary_le hL

/-- Under GRH, a uniform Korselt triple on K197 cell 31 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell31_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (2719 / 4) (2723 / 4)) :
    let r := (500642918837 / 500000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    local_witness hn ho hu hG (B := 0.095) (a := 339916 / 1000) (P := -2.85550) (u := 341.61) (D :=
      0.06071) hL.2 (by norm_num only) (by norm_num only [k197Slope]) (by norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only) (fun _ hr ↦ theta_from339916 hr)
      (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from339916 hr (by norm_num only)) (F := 0.1426)
      (fun _ hr ↦ late_growth_credit hr.1 (hr.2.trans (by norm_num only)))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact gaussian_k197_cell31_boundary_le hL

/-- Under GRH, a uniform Korselt triple on K197 cell 32 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell32_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (2723 / 4) (2727 / 4)) :
    let r := (250335811891 / 250000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    local_witness hn ho hu hG (B := 0.090) (a := 339916 / 1000) (P := -2.85550) (u := 341.61) (D :=
      0.06071) hL.2 (by norm_num only) (by norm_num only [k197Slope]) (by norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only) (fun _ hr ↦ theta_from339916 hr)
      (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from339916 hr (by norm_num only)) (F := 0.1426)
      (fun _ hr ↦ late_growth_credit hr.1 (hr.2.trans (by norm_num only)))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact gaussian_k197_cell32_boundary_le hL

/-- Under GRH, a uniform Korselt triple on K197 cell 33 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell33_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (2727 / 4) (2729 / 4)) :
    let r := (1001400486393 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    local_witness hn ho hu hG (B := 0.129) (a := 339916 / 1000) (P := -2.85550) (u := 341.61) (D :=
      0.06071) hL.2 (by norm_num only) (by norm_num only [k197Slope]) (by norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only) (fun _ hr ↦ theta_from339916 hr)
      (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from339916 hr (by norm_num only)) (F := 0.1426)
      (fun _ hr ↦ late_growth_credit hr.1 (hr.2.trans (by norm_num only)))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact gaussian_k197_cell33_boundary_le hL

/-- Under GRH, a uniform Korselt triple on K197 cell 34 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell34_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (2729 / 4) (2731 / 4)) :
    let r := (1001400486393 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    local_witness hn ho hu hG (B := 0.141) (a := 340) (P := -2.85565) (u := 342.9) (D := 0.06048)
      hL.2 (by norm_num only) (by norm_num only [k197Slope]) (by norm_num only) (by norm_num only)
      (by norm_num only) le_rfl
      (fun _ hr ↦ theta_from339916 ((by norm_num only : (339916 / 1000 : ℝ) ≤ 340).trans hr))
      (by norm_num only) (by norm_num only)
      (fun _ hr ↦
        gaussian_main_conductor_from339916 ((by norm_num only : (339916 / 1000 : ℝ) ≤ 340).trans hr)
          (by norm_num only))
      (F := 0.14908) (fun _ hr ↦ retained_gain_from340 hr) (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 116692) (B := 116864) (E := 128) (a := 340) (by norm_num only) hL
        (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell34 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple on K197 cell 35 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell35_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (2731 / 4) (2735 / 4)) :
    let r := (500728777463 / 500000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    local_witness hn ho hu hG (B := 0.141) (a := 340) (P := -2.85565) (u := 342.9) (D := 0.06048)
      hL.2 (by norm_num only) (by norm_num only [k197Slope]) (by norm_num only) (by norm_num only)
      (by norm_num only) le_rfl
      (fun _ hr ↦ theta_from339916 ((by norm_num only : (339916 / 1000 : ℝ) ≤ 340).trans hr))
      (by norm_num only) (by norm_num only)
      (fun _ hr ↦
        gaussian_main_conductor_from339916 ((by norm_num only : (339916 / 1000 : ℝ) ≤ 340).trans hr)
          (by norm_num only))
      (F := 0.14908) (fun _ hr ↦ retained_gain_from340 hr) (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 116876) (B := 117220) (E := 126) (a := 340) (by norm_num only) hL
        (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell35 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple on K197 cell 36 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell36_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (2735 / 4) (2739 / 4)) :
    let r := (40060578157 / 40000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    local_witness hn ho hu hG (B := 0.141) (a := 340) (P := -2.85565) (u := 342.9) (D := 0.06048)
      hL.2 (by norm_num only) (by norm_num only [k197Slope]) (by norm_num only) (by norm_num only)
      (by norm_num only) le_rfl
      (fun _ hr ↦ theta_from339916 ((by norm_num only : (339916 / 1000 : ℝ) ≤ 340).trans hr))
      (by norm_num only) (by norm_num only)
      (fun _ hr ↦
        gaussian_main_conductor_from339916 ((by norm_num only : (339916 / 1000 : ℝ) ≤ 340).trans hr)
          (by norm_num only))
      (F := 0.14908) (fun _ hr ↦ retained_gain_from340 hr) (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 117232) (B := 117576) (E := 124) (a := 340) (by norm_num only) hL
        (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell36 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 37 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell37_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (2739 / 4) (2743 / 4)) :
    let r := (1001571184149 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    late_witness hn ho hu hG (B := 0.134) (a := 340) (P := -2.85617) hL.2 (by norm_num only)
      (by norm_num only [k197Slope]) le_rfl
      (fun _ hr ↦ theta_from339916 ((by norm_num only : (339916 / 1000 : ℝ) ≤ 340).trans hr)) (v :=
      1.00106) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦
        gaussian_main_conductor_from339916 ((by norm_num only : (339916 / 1000 : ℝ) ≤ 340).trans hr)
          (by norm_num only))
      (F := 0.147)
      (fun _ hr ↦ retained_gain_without343 ⟨(by norm_num only : (340 : ℝ) ≤ _).trans hr.1, hr.2⟩)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 117589) (B := 117933) (E := 122) (a := 340) (by norm_num only) hL
        (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell37 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 38 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell38_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (2743 / 4) (2747 / 4)) :
    let r := (1001627746349 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    late_witness hn ho hu hG (B := 0.087) (a := 340) (P := -2.85617) hL.2 (by norm_num only)
      (by norm_num only [k197Slope]) le_rfl
      (fun _ hr ↦ theta_from339916 ((by norm_num only : (339916 / 1000 : ℝ) ≤ 340).trans hr)) (v :=
      1.00106) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦
        gaussian_main_conductor_from339916 ((by norm_num only : (339916 / 1000 : ℝ) ≤ 340).trans hr)
          (by norm_num only))
      (F := 0.147)
      (fun _ hr ↦ retained_gain_without343 ⟨(by norm_num only : (340 : ℝ) ≤ _).trans hr.1, hr.2⟩)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 117946) (B := 118291) (E := 79) (a := 340) (by norm_num only) hL
        (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell38 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 39 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell39_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (2747 / 4) (2751 / 4)) :
    let r := (40067365651 / 40000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    late_witness hn ho hu hG (B := 0.124) (a := 340) (P := -2.85617) hL.2 (by norm_num only)
      (by norm_num only [k197Slope]) le_rfl
      (fun _ hr ↦ theta_from339916 ((by norm_num only : (339916 / 1000 : ℝ) ≤ 340).trans hr)) (v :=
      1.00106) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦
        gaussian_main_conductor_from339916 ((by norm_num only : (339916 / 1000 : ℝ) ≤ 340).trans hr)
          (by norm_num only))
      (F := 0.147)
      (fun _ hr ↦ retained_gain_without343 ⟨(by norm_num only : (340 : ℝ) ≤ _).trans hr.1, hr.2⟩)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 118303) (B := 118649) (E := 113) (a := 340) (by norm_num only) hL
        (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell39 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 40 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell40_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (2751 / 4) (2755 / 4)) :
    let r := (1001740369669 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    late_witness hn ho hu hG (B := 0.128) (a := 340) (P := -2.85617) hL.2 (by norm_num only)
      (by norm_num only [k197Slope]) le_rfl
      (fun _ hr ↦ theta_from339916 ((by norm_num only : (339916 / 1000 : ℝ) ≤ 340).trans hr)) (v :=
      1.00106) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦
        gaussian_main_conductor_from339916 ((by norm_num only : (339916 / 1000 : ℝ) ≤ 340).trans hr)
          (by norm_num only))
      (F := 0.147)
      (fun _ hr ↦ retained_gain_without343 ⟨(by norm_num only : (340 : ℝ) ≤ _).trans hr.1, hr.2⟩)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 118661) (B := 119008) (E := 116) (a := 340) (by norm_num only) hL
        (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell40 hx hy)
        (by norm_num only)

/-- Under GRH, the left part of K197 cell 41 has a prime rejecting
base within the squared certified radius for a uniform Korselt triple. -/
theorem gaussian_k197_cell41_left_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (2755 / 4) 688.804) :
    let r := (62612277017 / 62500000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    late_witness hn ho hu hG (B := 0.149) (a := 340) (P := -2.85617) hL.2 (by norm_num only)
      (by norm_num only [k197Slope]) le_rfl
      (fun _ hr ↦ theta_from339916 ((by norm_num only : (339916 / 1000 : ℝ) ≤ 340).trans hr)) (v :=
      1.00106) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦
        gaussian_main_conductor_from339916 ((by norm_num only : (339916 / 1000 : ℝ) ≤ 340).trans hr)
          (by norm_num only))
      (F := 0.147)
      (fun _ hr ↦ retained_gain_without343 ⟨(by norm_num only : (340 : ℝ) ≤ _).trans hr.1, hr.2⟩)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 119020) (B := 119367) (E := 135) (a := 340) (by norm_num only) hL
        (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell41 hx hy)
        (by norm_num only)

/-- Under GRH, the right part of K197 cell 41 has a prime rejecting
base within the squared certified radius for a uniform Korselt triple. -/
theorem gaussian_k197_cell41_right_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc 688.804 (2759 / 4)) :
    let r := (62612277017 / 62500000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    late_witness hn ho hu hG (B := 0.135) (a := 340) (P := -2.85617) hL.2 (by norm_num only)
      (by norm_num only [k197Slope]) le_rfl
      (fun _ hr ↦ theta_from339916 ((by norm_num only : (339916 / 1000 : ℝ) ≤ 340).trans hr)) (v :=
      1.00106) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦
        gaussian_main_conductor_from339916 ((by norm_num only : (339916 / 1000 : ℝ) ≤ 340).trans hr)
          (by norm_num only))
      (F := 0.147)
      (fun _ hr ↦ retained_gain_without343 ⟨(by norm_num only : (340 : ℝ) ≤ _).trans hr.1, hr.2⟩)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 119039) (B := 119367) (E := 123) (a := 340) (by norm_num only) hL
        (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦
          AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell41_right hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in this K197 interval has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell42_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (2759 / 4) 690) :
    let r := (500926164909 / 500000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    late_witness hn ho hu hG (B := 0.155) (a := 34549 / 100) (P := -2.83018) hL.2 (by norm_num only)
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from34549 hr) (v :=
      1.00106) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from34549 hr (by norm_num only)) (F := 0.147)
      (fun _ hr ↦ retained_gain_without343 ⟨(by norm_num only : (340 : ℝ) ≤ _).trans hr.1, hr.2⟩)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 119379) (B := 119467) (E := 143) (a := 34549 / 100)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell42 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in this K197 interval has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell43_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc 690 (5521 / 8)) :
    let r := (500926164909 / 500000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    late_witness hn ho hu hG (B := 0.181) (a := 34549 / 100) (P := -2.83018) hL.2 (by norm_num only)
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from34549 hr) (v :=
      1.00106) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from34549 hr (by norm_num only)) (F := 0.147)
      (fun _ hr ↦ retained_gain_without343 ⟨(by norm_num only : (340 : ℝ) ≤ _).trans hr.1, hr.2⟩)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 119466) (B := 119510) (E := 167) (a := 34549 / 100)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell43 hx hy)
        (by norm_num only)

/-- Under GRH, K197 cell 44 has a prime rejecting base within the squared
certified radius for every uniform Korselt triple. -/
theorem gaussian_k197_cell44_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (5521 / 8) (2761 / 4)) :
    let r := (500926164909 / 500000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    late_witness hn ho hu hG (B := 0.19088) (a := 3457 / 10) (P := -2.82694) hL.2 (by norm_num only)
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from3457 hr) (v :=
      1.00185) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from3457 hr (by norm_num only)) (F := 0.1509)
      (fun _ hr ↦ grown_without343 ⟨by linarith only [hr.1], hr.2⟩) (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 119509) (B := 119553) (E := 177) (a := 3457 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell44 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in this K197 interval has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell45_left_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (2761 / 4) 690.399) :
    let r := (250470054231 / 250000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    late_witness hn ho hu hG (B := 0.184) (a := 34549 / 100) (P := -2.83018) hL.2 (by norm_num only)
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from34549 hr) (v :=
      1.00106) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from34549 hr (by norm_num only)) (F := 0.147)
      (fun _ hr ↦ retained_gain_without343 ⟨(by norm_num only : (340 : ℝ) ≤ _).trans hr.1, hr.2⟩)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 119559) (B := 119733) (E := 170) (a := 34549 / 100)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell45 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in this K197 interval has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell45_right_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc 690.399 (2763 / 4)) :
    let r := (250470054231 / 250000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    late_witness hn ho hu hG (B := 0.177) (a := 34549 / 100) (P := -2.83018) hL.2 (by norm_num only)
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from34549 hr) (v :=
      1.00106) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from34549 hr (by norm_num only)) (F := 0.147)
      (fun _ hr ↦ retained_gain_without343 ⟨(by norm_num only : (340 : ℝ) ≤ _).trans hr.1, hr.2⟩)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 119611) (B := 119733) (E := 164) (a := 34549 / 100)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦
          AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell45_right hx hy)
        (by norm_num only)

private theorem witness_below354 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {U s B a T P C : ℝ}
    (hL : Real.log n ≤ U) (hm : k197Slope s ≤ 0) (ha₀ : (340 : ℝ) ≤ a)
    (hT : ∀ r : ℝ, a ≤ r → T ≤ gaussianTheta197 r) (hvs : 1.0019 ≤ s) (hneg : T ≤ 0)
    (hP : P ≤ T / 1.0019 + 0.05858 - 0.000084)
    (hC : ∀ r : ℝ, a ≤ r → 4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ C)
    (hmargin :
      0 ≤
        (15.0472769 : ℝ) + 0.12911 + (0.041518 - B) + P + k197Slope s * (U / 2) - 4 * 0.006305 - C -
            0.0003 +
          0.00818) :
    let r := s * Real.log n / 2
    r ∈ Set.Ico a 354 →
      (-4 * (Chebyshev.psi (r ^ 2) - r ^ 2) * quarterWeight656 (r ^ 2) (r ^ 2) ≤ B) →
      ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  intro r hra hb
  have hr₀ : r ∈ Set.Ico 340 354 := ⟨ha₀.trans hra.1, hra.2⟩
  apply uniform_witness_of_pair_false hn ho hu (X := r ^ 2)
  intro p q k _ _ _ a b c ha hb' hc hp hq hk hlev ht hsmall
  have hs₁ : 1 ≤ s := (by norm_num only : (1 : ℝ) ≤ 1.0019).trans hvs
  have hscale : r / s = Real.log n / 2 := by
    dsimp only [r]
    apply (div_eq_iff (zero_lt_one.trans_le hs₁).ne').mpr
    ring
  have hlevel : Real.log p + Real.log q + Real.log k = 4 * (Real.log n / 2) := by
    linarith only [hlev]
  have hpa l hl hcut := (hsmall l hl hcut).1
  have hpb l hl hcut := (hsmall l hl hcut).2.1
  have hpc l hl hcut := (hsmall l hl hcut).2.2
  have hspos : 0 < s := (by norm_num only : (0 : ℝ) < 1.0019).trans_le hvs
  have hθ : T / 1.0019 ≤ gaussianTheta197 r / s := by
    apply (le_div_iff₀ hspos).mpr
    have hdiv : T / 1.0019 ≤ 0 := div_nonpos_of_nonpos_of_nonneg hneg (by norm_num only)
    refine (mul_le_mul_of_nonpos_left hvs hdiv).trans ?_
    rw [div_mul_cancel₀ _ (by norm_num only)]
    exact hT r hra.1
  have hpole : (0.05858 : ℝ) ≤ gaussianNegPole197 / r := by
    apply (le_div_iff₀ ((by norm_num only : (0 : ℝ) < 340).trans_le hr₀.1)).mpr
    linarith only [hr₀.2.le, gaussian_neg_pole_lower_197]
  have hcost : P + 0.000084 ≤ gaussianTheta197 r / s + gaussianNegPole197 / r := by
    linarith only [hP, hθ, hpole]
  have hshift₀ :=
    shift_forward_of_refl ha hb' hc hG.riemann ((by norm_num only : (328 : ℝ) ≤ 340).trans hr₀.1)
      (by
        rw [mul_div_assoc, hscale]; exact hlevel)
      ht hpa hpb hpc hcost
      (gaussian_joint_to354 hG.riemann
        ⟨(by norm_num only : (332.15 : ℝ) ≤ 340).trans hr₀.1, hr₀.2.le⟩)
  have hshift :
    P ≤
      (gaussianShiftedForward197 a r + gaussianShiftedForward197 b r +
          gaussianShiftedForward197 c r) +
        gaussianHalfCoeff197 * r := by
    linarith only [hshift₀]
  have hcond := hC r hra.1
  rw [hscale] at hcond
  have hmain :=
    gaussian_k197_principal_to354 hG.riemann
      ⟨(by norm_num only : (663 / 2 : ℝ) ≤ 340).trans hr₀.1, hr₀.2.le⟩ hb
  have hcompare := gaussian_comparison_below354 ha hb' hc hp hq hk hG hr₀ hlevel ht hpa hpb hpc
  have hrF : r ∈ Set.Icc 328 354 := ⟨(by norm_num only : (328 : ℝ) ≤ 340).trans hr₀.1, hr₀.2.le⟩
  refine
    mid_pair_false (a := a) (b := b) (c := c) hG (B := 0.041518 - B)
      ⟨(by norm_num only : (336.8 : ℝ) ≤ 340).trans hr₀.1, hr₀.2.le.trans (by norm_num only)⟩ hcond
      (k197_main_reflect_to354 hrF) (gaussian_k197_reflect_credit_to354 hrF) ht hpa hpb hpc hcompare
      ?_ hshift (wide_linear_lower (Real.log_natCast_nonneg n) hL hs₁ hm) ?_
  · simpa only [sub_eq_add_neg, add_assoc] using hmain
  · linarith only [hmargin]

/-- Under GRH, a uniform Korselt triple in K197 cell 46 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell46_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (2763 / 4) (2767 / 4)) :
    let r := (1001908063039 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below354 hn ho hu hG (B := 0.14007) (a := 346) (P := -2.82676) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from346 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from346 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 119739) (B := 120087) (E := 130) (a := 346) (by norm_num only) hL
        (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell46 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 47 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell47_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (2767 / 4) (2771 / 4)) :
    let r := (1001963632661 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below354 hn ho hu hG (B := 0.13145) (a := 346) (P := -2.82676) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from346 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from346 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 120099) (B := 120448) (E := 122) (a := 346) (by norm_num only) hL
        (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell47 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 48 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell48_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (2771 / 4) (2773 / 4)) :
    let r := (501009519703 / 500000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below354 hn ho hu hG (B := 0.16649) (a := 34707 / 100) (P := -2.82183) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from34707 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from34707 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 120460) (B := 120635) (E := 155) (a := 34707 / 100)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell48 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 49 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell49_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (2773 / 4) (2775 / 4)) :
    let r := (501009519703 / 500000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below354 hn ho hu hG (B := 0.15038) (a := 34707 / 100) (P := -2.82183) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from34707 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from34707 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 120634) (B := 120809) (E := 140) (a := 34707 / 100)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell49 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 50 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell50_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (2775 / 4) (2779 / 4)) :
    let r := (1002074283993 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below354 hn ho hu hG (B := 0.12030) (a := 34707 / 100) (P := -2.82183) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from34707 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from34707 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 120821) (B := 121171) (E := 112) (a := 34707 / 100)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell50 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 51 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell51_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (2779 / 4) (2783 / 4)) :
    let r := (1002074283993 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below354 hn ho hu hG (B := 0.09775) (a := 34707 / 100) (P := -2.82183) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from34707 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from34707 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 121170) (B := 121520) (E := 91) (a := 34707 / 100)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell51 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 52 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell52_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (2783 / 4) (2791 / 4)) :
    let r := (1002184289539 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below354 hn ho hu hG (B := 0.07304) (a := 34707 / 100) (P := -2.82183) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from34707 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from34707 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 121546) (B := 122247) (E := 68) (a := 34707 / 100)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell52 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 53 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell53_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (2791 / 4) (2799 / 4)) :
    let r := (1002293654961 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below354 hn ho hu hG (B := 0.03115) (a := 34707 / 100) (P := -2.82183) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from34707 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from34707 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 122272) (B := 122975) (E := 29) (a := 34707 / 100)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell53 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 54 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell54_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (2799 / 4) (2807 / 4)) :
    let r := (250600596463 / 250000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below354 hn ho hu hG (B := 0.07197) (a := 34707 / 100) (P := -2.82183) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from34707 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from34707 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 123001) (B := 123706) (E := 67) (a := 34707 / 100)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell54 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 55 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell55_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (2807 / 4) (2815 / 4)) :
    let r := (501255243871 / 500000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below354 hn ho hu hG (B := 0.04404) (a := 34707 / 100) (P := -2.82183) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from34707 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from34707 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 123732) (B := 124439) (E := 41) (a := 34707 / 100)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell55 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 56 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell56_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (2815 / 4) (2823 / 4)) :
    let r := (501255243871 / 500000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below354 hn ho hu hG (B := 0.03652) (a := 34707 / 100) (P := -2.82183) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from34707 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from34707 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 124438) (B := 125147) (E := 34) (a := 34707 / 100)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell56 hx hy)
        (by norm_num only)

private theorem witness_below370 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {U s B a T P C : ℝ}
    (hL : Real.log n ≤ U) (hm : k197Slope s ≤ 0) (ha₀ : (340 : ℝ) ≤ a)
    (hT : ∀ r : ℝ, a ≤ r → T ≤ gaussianTheta197 r) (hvs : 1.0027 ≤ s) (hneg : T ≤ 0)
    (hP : P ≤ T / 1.0027 + 0.05605 - 0.000099)
    (hC : ∀ r : ℝ, a ≤ r → 4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ C)
    (hmargin :
      0 ≤
        (15.0472769 : ℝ) + 0.11489 + (0.038438 - B) + P + k197Slope s * (U / 2) - 4 * 0.006305 - C -
            0.00034 +
          0.0074) :
    let r := s * Real.log n / 2
    r ∈ Set.Ico a 370 →
      (-4 * (Chebyshev.psi (r ^ 2) - r ^ 2) * quarterWeight656 (r ^ 2) (r ^ 2) ≤ B) →
      ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  intro r hra hb
  have hr₀ : r ∈ Set.Ico 340 370 := ⟨ha₀.trans hra.1, hra.2⟩
  apply uniform_witness_of_pair_false hn ho hu (X := r ^ 2)
  intro p q k _ _ _ a b c ha hb' hc hp hq hk hlev ht hsmall
  have hs₁ : 1 ≤ s := (by norm_num only : (1 : ℝ) ≤ 1.0027).trans hvs
  have hscale : r / s = Real.log n / 2 := by
    dsimp only [r]
    apply (div_eq_iff (zero_lt_one.trans_le hs₁).ne').mpr
    ring
  have hlevel : Real.log p + Real.log q + Real.log k = 4 * (Real.log n / 2) := by
    linarith only [hlev]
  have hpa l hl hcut := (hsmall l hl hcut).1
  have hpb l hl hcut := (hsmall l hl hcut).2.1
  have hpc l hl hcut := (hsmall l hl hcut).2.2
  have hspos : 0 < s := (by norm_num only : (0 : ℝ) < 1.0027).trans_le hvs
  have hθ : T / 1.0027 ≤ gaussianTheta197 r / s := by
    apply (le_div_iff₀ hspos).mpr
    have hdiv : T / 1.0027 ≤ 0 := div_nonpos_of_nonpos_of_nonneg hneg (by norm_num only)
    refine (mul_le_mul_of_nonpos_left hvs hdiv).trans ?_
    rw [div_mul_cancel₀ _ (by norm_num only)]
    exact hT r hra.1
  have hpole : (0.05605 : ℝ) ≤ gaussianNegPole197 / r := by
    apply (le_div_iff₀ ((by norm_num only : (0 : ℝ) < 340).trans_le hr₀.1)).mpr
    linarith only [hr₀.2.le, gaussian_neg_pole_lower_197]
  have hcost : P + 0.000099 ≤ gaussianTheta197 r / s + gaussianNegPole197 / r := by
    linarith only [hP, hθ, hpole]
  have hshift₀ :=
    shift_forward_of_refl ha hb' hc hG.riemann ((by norm_num only : (328 : ℝ) ≤ 340).trans hr₀.1)
      (by
        rw [mul_div_assoc, hscale]; exact hlevel)
      ht hpa hpb hpc hcost
      (gaussian_joint_to370 hG.riemann
        ⟨(by norm_num only : (332.15 : ℝ) ≤ 340).trans hr₀.1, hr₀.2.le⟩)
  have hshift :
    P ≤
      (gaussianShiftedForward197 a r + gaussianShiftedForward197 b r +
          gaussianShiftedForward197 c r) +
        gaussianHalfCoeff197 * r := by
    linarith only [hshift₀]
  have hcond := hC r hra.1
  rw [hscale] at hcond
  have hmain :=
    gaussian_k197_principal_to370 hG.riemann
      ⟨(by norm_num only : (663 / 2 : ℝ) ≤ 340).trans hr₀.1, hr₀.2.le⟩ hb
  have hcompare := gaussian_comparison_below370 ha hb' hc hp hq hk hG hr₀ hlevel ht hpa hpb hpc
  have hrF : r ∈ Set.Icc 328 370 := ⟨(by norm_num only : (328 : ℝ) ≤ 340).trans hr₀.1, hr₀.2.le⟩
  refine
    mid_pair_false (a := a) (b := b) (c := c) hG (B := 0.038438 - B)
      ⟨(by norm_num only : (336.8 : ℝ) ≤ 340).trans hr₀.1, hr₀.2.le.trans (by norm_num only)⟩ hcond
      (k197_main_reflect_to370 hrF) (gaussian_k197_reflect_credit_to370 hrF) ht hpa hpb hpc hcompare
      ?_ hshift (wide_linear_lower (Real.log_natCast_nonneg n) hL hs₁ hm) ?_
  · simpa only [sub_eq_add_neg, add_assoc] using hmain
  · linarith only [hmargin]

/-- Under GRH, a uniform Korselt triple in K197 cell 57 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell57_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (2823 / 4) (2839 / 4)) :
    let r := (1002724826311 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below370 hn ho hu hG (B := 0.04321) (a := 1769 / 5) (P := -2.79144) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from3538 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from3538 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 125200) (B := 126624) (E := 41) (a := 1769 / 5)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell57 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 58 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell58_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (2839 / 4) (2847 / 4)) :
    let r := (1002936713637 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below370 hn ho hu hG (B := 0.09694) (a := 1769 / 5) (P := -2.79144) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from3538 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from3538 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 126677) (B := 127392) (E := 92) (a := 1769 / 5)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell58 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 59 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell59_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (2847 / 4) (2855 / 4)) :
    let r := (501520875621 / 500000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below370 hn ho hu hG (B := 0.11802) (a := 1769 / 5) (P := -2.79144) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from3538 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from3538 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 127418) (B := 128136) (E := 112) (a := 1769 / 5)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell59 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 60 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell60_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (2855 / 4) (2863 / 4)) :
    let r := (125393273963 / 125000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below370 hn ho hu hG (B := 0.07903) (a := 1769 / 5) (P := -2.79144) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from3538 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from3538 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 128162) (B := 128882) (E := 75) (a := 1769 / 5)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell60 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 61 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell61_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (2863 / 4) (2879 / 4)) :
    let r := (8026000321 / 8000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below370 hn ho hu hG (B := 0.03267) (a := 1769 / 5) (P := -2.79144) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from3538 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from3538 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 128908) (B := 130354) (E := 31) (a := 1769 / 5)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell61 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 62 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell62_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (2879 / 4) (2895 / 4)) :
    let r := (1003455980947 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below370 hn ho hu hG (B := 0.04847) (a := 1769 / 5) (P := -2.79144) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from3538 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from3538 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 130406) (B := 131861) (E := 46) (a := 1769 / 5)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell62 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 63 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell63_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (2895 / 4) (2911 / 4)) :
    let r := (12545745167 / 12500000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below370 hn ho hu hG (B := 0.06778) (a := 363) (P := -2.75051) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from363 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from363 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 131913) (B := 133376) (E := 66) (a := 363) (by norm_num only) hL
        (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell63 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 64 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell64_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (2911 / 4) (2927 / 4)) :
    let r := (501930488063 / 500000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below370 hn ho hu hG (B := 0.08627) (a := 363) (P := -2.75051) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from363 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from363 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 133429) (B := 134901) (E := 84) (a := 363) (by norm_num only) hL
        (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell64 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 65 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell65_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (2927 / 4) (2943 / 4)) :
    let r := (125507513393 / 125000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below370 hn ho hu hG (B := 0.09141) (a := 363) (P := -2.75051) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from363 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from363 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 134953) (B := 136434) (E := 89) (a := 363) (by norm_num only) hL
        (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell65 hx hy)
        (by norm_num only)

private theorem witness_below395 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {U s B a T P C : ℝ}
    (hL : Real.log n ≤ U) (hm : k197Slope s ≤ 0) (ha₀ : (340 : ℝ) ≤ a)
    (hT : ∀ r : ℝ, a ≤ r → T ≤ gaussianTheta197 r) (hvs : 1.0042 ≤ s) (hneg : T ≤ 0)
    (hP : P ≤ T / 1.0042 + 0.0525 - 0.000119)
    (hC : ∀ r : ℝ, a ≤ r → 4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ C)
    (hmargin :
      0 ≤
        (15.0472769 : ℝ) + 0.09284 + (0.034118 - B) + P + k197Slope s * (U / 2) - 4 * 0.006305 - C -
            0.0004 +
          0.00639) :
    let r := s * Real.log n / 2
    r ∈ Set.Ico a 395 →
      (-4 * (Chebyshev.psi (r ^ 2) - r ^ 2) * quarterWeight656 (r ^ 2) (r ^ 2) ≤ B) →
      ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  intro r hra hb
  have hr₀ : r ∈ Set.Ico 340 395 := ⟨ha₀.trans hra.1, hra.2⟩
  apply uniform_witness_of_pair_false hn ho hu (X := r ^ 2)
  intro p q k _ _ _ a b c ha hb' hc hp hq hk hlev ht hsmall
  have hs₁ : 1 ≤ s := (by norm_num only : (1 : ℝ) ≤ 1.0042).trans hvs
  have hscale : r / s = Real.log n / 2 := by
    dsimp only [r]
    apply (div_eq_iff (zero_lt_one.trans_le hs₁).ne').mpr
    ring
  have hlevel : Real.log p + Real.log q + Real.log k = 4 * (Real.log n / 2) := by
    linarith only [hlev]
  have hpa l hl hcut := (hsmall l hl hcut).1
  have hpb l hl hcut := (hsmall l hl hcut).2.1
  have hpc l hl hcut := (hsmall l hl hcut).2.2
  have hspos : 0 < s := (by norm_num only : (0 : ℝ) < 1.0042).trans_le hvs
  have hθ : T / 1.0042 ≤ gaussianTheta197 r / s := by
    apply (le_div_iff₀ hspos).mpr
    have hdiv : T / 1.0042 ≤ 0 := div_nonpos_of_nonpos_of_nonneg hneg (by norm_num only)
    refine (mul_le_mul_of_nonpos_left hvs hdiv).trans ?_
    rw [div_mul_cancel₀ _ (by norm_num only)]
    exact hT r hra.1
  have hpole : (0.0525 : ℝ) ≤ gaussianNegPole197 / r := by
    apply (le_div_iff₀ ((by norm_num only : (0 : ℝ) < 340).trans_le hr₀.1)).mpr
    linarith only [hr₀.2.le, gaussian_neg_pole_lower_197]
  have hcost : P + 0.000119 ≤ gaussianTheta197 r / s + gaussianNegPole197 / r := by
    linarith only [hP, hθ, hpole]
  have hshift₀ :=
    shift_forward_of_refl ha hb' hc hG.riemann ((by norm_num only : (328 : ℝ) ≤ 340).trans hr₀.1)
      (by
        rw [mul_div_assoc, hscale]; exact hlevel)
      ht hpa hpb hpc hcost
      (gaussian_joint_to395 hG.riemann
        ⟨(by norm_num only : (332.15 : ℝ) ≤ 340).trans hr₀.1, hr₀.2.le⟩)
  have hshift :
    P ≤
      (gaussianShiftedForward197 a r + gaussianShiftedForward197 b r +
          gaussianShiftedForward197 c r) +
        gaussianHalfCoeff197 * r := by
    linarith only [hshift₀]
  have hcond := hC r hra.1
  rw [hscale] at hcond
  have hmain :=
    gaussian_k197_principal_to395 hG.riemann
      ⟨(by norm_num only : (663 / 2 : ℝ) ≤ 340).trans hr₀.1, hr₀.2.le⟩ hb
  have hcompare := gaussian_comparison_below395 ha hb' hc hp hq hk hG hr₀ hlevel ht hpa hpb hpc
  have hrF : r ∈ Set.Icc 328 395 := ⟨(by norm_num only : (328 : ℝ) ≤ 340).trans hr₀.1, hr₀.2.le⟩
  refine
    mid_pair_false (a := a) (b := b) (c := c) hG (B := 0.034118 - B)
      ⟨(by norm_num only : (336.8 : ℝ) ≤ 340).trans hr₀.1, hr₀.2.le.trans (by norm_num only)⟩ hcond
      (k197_main_reflect_to395 hrF) (gaussian_k197_reflect_credit_to395 hrF) ht hpa hpb hpc hcompare
      ?_ hshift (wide_linear_lower (Real.log_natCast_nonneg n) hL hs₁ hm) ?_
  · simpa only [sub_eq_add_neg, add_assoc] using hmain
  · linarith only [hmargin]

/-- Under GRH, a uniform Korselt triple in K197 cell 66 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell66_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (2943 / 4) (2959 / 4)) :
    let r := (251064260869 / 250000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below395 hn ho hu hG (B := 0.00000) (a := 3693 / 10) (P := -2.72255) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from3693 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from3693 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 136486) (B := 137975) (E := 0) (a := 3693 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ by
          simpa only [neg_zero] using
            AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell66 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 67 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell67_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (2959 / 4) (2975 / 4)) :
    let r := (200890364273 / 200000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below395 hn ho hu hG (B := 0.01414) (a := 3693 / 10) (P := -2.72255) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from3693 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from3693 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 138028) (B := 139526) (E := 14) (a := 3693 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell67 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 68 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell68_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (2975 / 4) (2991 / 4)) :
    let r := (50232223813 / 50000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below395 hn ho hu hG (B := 0.00000) (a := 3693 / 10) (P := -2.72255) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from3693 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from3693 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 139578) (B := 141084) (E := 0) (a := 3693 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ by
          simpa only [neg_zero] using
            AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell68 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 69 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell69_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (2991 / 4) (3007 / 4)) :
    let r := (25120876071 / 25000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below395 hn ho hu hG (B := 0.00000) (a := 3693 / 10) (P := -2.72255) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from3693 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from3693 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 141137) (B := 142652) (E := 0) (a := 3693 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ by
          simpa only [neg_zero] using
            AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell69 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 70 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell70_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (3007 / 4) (3023 / 4)) :
    let r := (100502355503 / 100000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below395 hn ho hu hG (B := 0.03937) (a := 3693 / 10) (P := -2.72255) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from3693 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from3693 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 142705) (B := 144228) (E := 39) (a := 3693 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell70 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 71 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell71_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (3023 / 4) (3039 / 4)) :
    let r := (40208401841 / 40000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below395 hn ho hu hG (B := 0.09489) (a := 3693 / 10) (P := -2.72255) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from3693 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from3693 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 144281) (B := 145813) (E := 94) (a := 3693 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell71 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 72 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell72_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (3039 / 4) (3055 / 4)) :
    let r := (1005394548309 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below395 hn ho hu hG (B := 0.05048) (a := 3693 / 10) (P := -2.72255) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from3693 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from3693 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 145866) (B := 147407) (E := 50) (a := 3693 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell72 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 73 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell73_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (3055 / 4) (3071 / 4)) :
    let r := (125697136709 / 125000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below395 hn ho hu hG (B := 0.08682) (a := 3693 / 10) (P := -2.72255) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from3693 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from3693 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 147459) (B := 149009) (E := 86) (a := 3693 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell73 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 74 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell74_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (3071 / 4) (3087 / 4)) :
    let r := (62859857077 / 62500000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below395 hn ho hu hG (B := 0.02423) (a := 3693 / 10) (P := -2.72255) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from3693 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from3693 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 149061) (B := 150620) (E := 24) (a := 3693 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell74 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 75 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell75_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (3087 / 4) (3103 / 4)) :
    let r := (62859857077 / 62500000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below395 hn ho hu hG (B := 0.00000) (a := 3693 / 10) (P := -2.72255) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from3693 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from3693 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 150619) (B := 152185) (E := 0) (a := 3693 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ by
          simpa only [neg_zero] using
            AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell75 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 76 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell76_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (3103 / 4) (3135 / 4)) :
    let r := (1006113296139 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below395 hn ho hu hG (B := 0.00000) (a := 3693 / 10) (P := -2.72255) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from3693 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from3693 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 152292) (B := 155450) (E := 0) (a := 3693 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ by
          simpa only [neg_zero] using
            AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell76 hx hy)
        (by norm_num only)

private theorem witness_below426 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {U s B a T P C : ℝ}
    (hL : Real.log n ≤ U) (hm : k197Slope s ≤ 0) (ha₀ : (340 : ℝ) ≤ a)
    (hT : ∀ r : ℝ, a ≤ r → T ≤ gaussianTheta197 r) (hvs : 1.0064 ≤ s) (hneg : T ≤ 0)
    (hP : P ≤ T / 1.0064 + 0.04868 - 0.00015)
    (hC : ∀ r : ℝ, a ≤ r → 4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ C)
    (hmargin :
      0 ≤
        (15.0472769 : ℝ) + 0.07131 + (0.029188 - B) + P + k197Slope s * (U / 2) - 4 * 0.006305 - C -
            0.00044 +
          0.0054) :
    let r := s * Real.log n / 2
    r ∈ Set.Ico a 426 →
      (-4 * (Chebyshev.psi (r ^ 2) - r ^ 2) * quarterWeight656 (r ^ 2) (r ^ 2) ≤ B) →
      ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  intro r hra hb
  have hr₀ : r ∈ Set.Ico 340 426 := ⟨ha₀.trans hra.1, hra.2⟩
  apply uniform_witness_of_pair_false hn ho hu (X := r ^ 2)
  intro p q k _ _ _ a b c ha hb' hc hp hq hk hlev ht hsmall
  have hs₁ : 1 ≤ s := (by norm_num only : (1 : ℝ) ≤ 1.0064).trans hvs
  have hscale : r / s = Real.log n / 2 := by
    dsimp only [r]
    apply (div_eq_iff (zero_lt_one.trans_le hs₁).ne').mpr
    ring
  have hlevel : Real.log p + Real.log q + Real.log k = 4 * (Real.log n / 2) := by
    linarith only [hlev]
  have hpa l hl hcut := (hsmall l hl hcut).1
  have hpb l hl hcut := (hsmall l hl hcut).2.1
  have hpc l hl hcut := (hsmall l hl hcut).2.2
  have hspos : 0 < s := (by norm_num only : (0 : ℝ) < 1.0064).trans_le hvs
  have hθ : T / 1.0064 ≤ gaussianTheta197 r / s := by
    apply (le_div_iff₀ hspos).mpr
    have hdiv : T / 1.0064 ≤ 0 := div_nonpos_of_nonpos_of_nonneg hneg (by norm_num only)
    refine (mul_le_mul_of_nonpos_left hvs hdiv).trans ?_
    rw [div_mul_cancel₀ _ (by norm_num only)]
    exact hT r hra.1
  have hpole : (0.04868 : ℝ) ≤ gaussianNegPole197 / r := by
    apply (le_div_iff₀ ((by norm_num only : (0 : ℝ) < 340).trans_le hr₀.1)).mpr
    linarith only [hr₀.2.le, gaussian_neg_pole_lower_197]
  have hcost : P + 0.00015 ≤ gaussianTheta197 r / s + gaussianNegPole197 / r := by
    linarith only [hP, hθ, hpole]
  have hshift₀ :=
    shift_forward_of_refl ha hb' hc hG.riemann ((by norm_num only : (328 : ℝ) ≤ 340).trans hr₀.1)
      (by
        rw [mul_div_assoc, hscale]; exact hlevel)
      ht hpa hpb hpc hcost
      (gaussian_joint_to426 hG.riemann
        ⟨(by norm_num only : (332.15 : ℝ) ≤ 340).trans hr₀.1, hr₀.2.le⟩)
  have hshift :
    P ≤
      (gaussianShiftedForward197 a r + gaussianShiftedForward197 b r +
          gaussianShiftedForward197 c r) +
        gaussianHalfCoeff197 * r := by
    linarith only [hshift₀]
  have hcond := hC r hra.1
  rw [hscale] at hcond
  have hmain :=
    gaussian_k197_principal_to426 hG.riemann
      ⟨(by norm_num only : (663 / 2 : ℝ) ≤ 340).trans hr₀.1, hr₀.2.le⟩ hb
  have hcompare := gaussian_comparison_below426 ha hb' hc hp hq hk hG hr₀ hlevel ht hpa hpb hpc
  have hrF : r ∈ Set.Icc 328 426 := ⟨(by norm_num only : (328 : ℝ) ≤ 340).trans hr₀.1, hr₀.2.le⟩
  refine
    mid_pair_false (a := a) (b := b) (c := c) hG (B := 0.029188 - B)
      ⟨(by norm_num only : (336.8 : ℝ) ≤ 340).trans hr₀.1, hr₀.2.le.trans (by norm_num only)⟩ hcond
      (k197_main_reflect_to426 hrF) (gaussian_k197_reflect_credit_to426 hrF) ht hpa hpb hpc hcompare
      ?_ hshift (wide_linear_lower (Real.log_natCast_nonneg n) hL hs₁ hm) ?_
  · simpa only [sub_eq_add_neg, add_assoc] using hmain
  · linarith only [hmargin]

/-- Under GRH, a uniform Korselt triple in K197 cell 77 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell77_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (3135 / 4) (3167 / 4)) :
    let r := (1006461533141 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below426 hn ho hu hG (B := 0.00000) (a := 3943 / 10) (P := -2.61682) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from3943 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from3943 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 155556) (B := 158749) (E := 0) (a := 3943 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ by
          simpa only [neg_zero] using
            AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell77 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 78 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell78_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (3167 / 4) (3199 / 4)) :
    let r := (503401325321 / 500000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below426 hn ho hu hG (B := 0.02931) (a := 3943 / 10) (P := -2.61682) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from3943 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from3943 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 158856) (B := 162083) (E := 31) (a := 3943 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell78 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 79 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell79_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (3199 / 4) (3231 / 4)) :
    let r := (1007136865833 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below426 hn ho hu hG (B := 0.08888) (a := 3943 / 10) (P := -2.61682) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from3943 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from3943 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 162190) (B := 165452) (E := 94) (a := 3943 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell79 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 80 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell80_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (3231 / 4) (3247 / 4)) :
    let r := (1007464387157 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below426 hn ho hu hG (B := 0.15695) (a := 3943 / 10) (P := -2.61682) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from3943 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from3943 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 165559) (B := 167203) (E := 166) (a := 3943 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell80 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 81 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell81_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (3247 / 4) (3263 / 4)) :
    let r := (503812850237 / 500000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below426 hn ho hu hG (B := 0.19419) (a := 4089 / 10) (P := -2.55977) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from4089 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from4089 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 167256) (B := 168909) (E := 213) (a := 4089 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell81 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 82 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell82_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (3263 / 4) (3279 / 4)) :
    let r := (503892707373 / 500000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below426 hn ho hu hG (B := 0.21060) (a := 4089 / 10) (P := -2.55977) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from4089 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from4089 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 168962) (B := 170624) (E := 231) (a := 4089 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell82 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 83 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell83_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (3279 / 4) (3295 / 4)) :
    let r := (6299647211 / 6250000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below426 hn ho hu hG (B := 0.16320) (a := 4089 / 10) (P := -2.55977) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from4089 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from4089 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 170677) (B := 172347) (E := 179) (a := 4089 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell83 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 84 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell84_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (3295 / 4) (3311 / 4)) :
    let r := (6299647211 / 6250000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below426 hn ho hu hG (B := 0.16137) (a := 4089 / 10) (P := -2.55977) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from4089 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from4089 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 172346) (B := 174025) (E := 177) (a := 4089 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell84 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 85 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell85_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (3311 / 4) (3327 / 4)) :
    let r := (504127599407 / 500000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below426 hn ho hu hG (B := 0.23887) (a := 4089 / 10) (P := -2.55977) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from4089 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from4089 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 174132) (B := 175820) (E := 262) (a := 4089 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell85 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 86 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell86_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (3327 / 4) (3343 / 4)) :
    let r := (504204375061 / 500000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below426 hn ho hu hG (B := 0.22063) (a := 4089 / 10) (P := -2.55977) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from4089 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from4089 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 175872) (B := 177569) (E := 242) (a := 4089 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell86 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 87 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell87_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (3343 / 4) (3359 / 4)) :
    let r := (100856081673 / 100000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below426 hn ho hu hG (B := 0.19055) (a := 4089 / 10) (P := -2.55977) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from4089 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from4089 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 177622) (B := 179327) (E := 209) (a := 4089 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell87 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 88 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell88_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (3359 / 4) (3375 / 4)) :
    let r := (100856081673 / 100000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below426 hn ho hu hG (B := 0.09573) (a := 4089 / 10) (P := -2.55977) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from4089 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from4089 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 179326) (B := 181039) (E := 105) (a := 4089 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell88 hx hy)
        (by norm_num only)

private theorem witness_below472 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {U s B a T P C : ℝ}
    (hL : Real.log n ≤ U) (hm : k197Slope s ≤ 0) (ha₀ : (340 : ℝ) ≤ a)
    (hT : ∀ r : ℝ, a ≤ r → T ≤ gaussianTheta197 r) (hvs : 1.0088 ≤ s) (hneg : T ≤ 0)
    (hP : P ≤ T / 1.0088 + 0.04394 - 0.0002)
    (hC : ∀ r : ℝ, a ≤ r → 4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ C)
    (hmargin :
      0 ≤
        (15.0472769 : ℝ) + 0.04382 + (0.023628 - B) + P + k197Slope s * (U / 2) - 4 * 0.006305 - C -
            0.0005 +
          0.0043) :
    let r := s * Real.log n / 2
    r ∈ Set.Ico a 472 →
      (-4 * (Chebyshev.psi (r ^ 2) - r ^ 2) * quarterWeight656 (r ^ 2) (r ^ 2) ≤ B) →
      ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  intro r hra hb
  have hr₀ : r ∈ Set.Ico 340 472 := ⟨ha₀.trans hra.1, hra.2⟩
  apply uniform_witness_of_pair_false hn ho hu (X := r ^ 2)
  intro p q k _ _ _ a b c ha hb' hc hp hq hk hlev ht hsmall
  have hs₁ : 1 ≤ s := (by norm_num only : (1 : ℝ) ≤ 1.0088).trans hvs
  have hscale : r / s = Real.log n / 2 := by
    dsimp only [r]
    apply (div_eq_iff (zero_lt_one.trans_le hs₁).ne').mpr
    ring
  have hlevel : Real.log p + Real.log q + Real.log k = 4 * (Real.log n / 2) := by
    linarith only [hlev]
  have hpa l hl hcut := (hsmall l hl hcut).1
  have hpb l hl hcut := (hsmall l hl hcut).2.1
  have hpc l hl hcut := (hsmall l hl hcut).2.2
  have hspos : 0 < s := (by norm_num only : (0 : ℝ) < 1.0088).trans_le hvs
  have hθ : T / 1.0088 ≤ gaussianTheta197 r / s := by
    apply (le_div_iff₀ hspos).mpr
    have hdiv : T / 1.0088 ≤ 0 := div_nonpos_of_nonpos_of_nonneg hneg (by norm_num only)
    refine (mul_le_mul_of_nonpos_left hvs hdiv).trans ?_
    rw [div_mul_cancel₀ _ (by norm_num only)]
    exact hT r hra.1
  have hpole : (0.04394 : ℝ) ≤ gaussianNegPole197 / r := by
    apply (le_div_iff₀ ((by norm_num only : (0 : ℝ) < 340).trans_le hr₀.1)).mpr
    linarith only [hr₀.2.le, gaussian_neg_pole_lower_197]
  have hcost : P + 0.0002 ≤ gaussianTheta197 r / s + gaussianNegPole197 / r := by
    linarith only [hP, hθ, hpole]
  have hshift₀ :=
    shift_forward_of_refl ha hb' hc hG.riemann ((by norm_num only : (328 : ℝ) ≤ 340).trans hr₀.1)
      (by
        rw [mul_div_assoc, hscale]; exact hlevel)
      ht hpa hpb hpc hcost
      (gaussian_joint_to472 hG.riemann
        ⟨(by norm_num only : (332.15 : ℝ) ≤ 340).trans hr₀.1, hr₀.2.le⟩)
  have hshift :
    P ≤
      (gaussianShiftedForward197 a r + gaussianShiftedForward197 b r +
          gaussianShiftedForward197 c r) +
        gaussianHalfCoeff197 * r := by
    linarith only [hshift₀]
  have hcond := hC r hra.1
  rw [hscale] at hcond
  have hmain :=
    gaussian_k197_principal_to472 hG.riemann
      ⟨(by norm_num only : (663 / 2 : ℝ) ≤ 340).trans hr₀.1, hr₀.2.le⟩ hb
  have hcompare := gaussian_comparison_below472 ha hb' hc hp hq hk hG hr₀ hlevel ht hpa hpb hpc
  have hrF : r ∈ Set.Icc 328 472 := ⟨(by norm_num only : (328 : ℝ) ≤ 340).trans hr₀.1, hr₀.2.le⟩
  refine
    mid_pair_false (a := a) (b := b) (c := c) hG (B := 0.023628 - B)
      ⟨(by norm_num only : (336.8 : ℝ) ≤ 340).trans hr₀.1, hr₀.2.le.trans (by norm_num only)⟩ hcond
      (k197_main_reflect_to472 hrF) (gaussian_k197_reflect_credit_to472 hrF) ht hpa hpb hpc hcompare
      ?_ hshift (wide_linear_lower (Real.log_natCast_nonneg n) hL hs₁ hm) ?_
  · simpa only [sub_eq_add_neg, add_assoc] using hmain
  · linarith only [hmargin]

/-- Under GRH, a uniform Korselt triple in K197 cell 89 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell89_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (3375 / 4) (3407 / 4)) :
    let r := (126107572703 / 125000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below472 hn ho hu hG (B := 0.16647) (a := 4255 / 10) (P := -2.49645) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from4255 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from4255 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 181146) (B := 184598) (E := 190) (a := 4255 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell89 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 90 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell90_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (3407 / 4) (3439 / 4)) :
    let r := (1009154660969 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below472 hn ho hu hG (B := 0.09375) (a := 4255 / 10) (P := -2.49645) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from4255 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from4255 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 184705) (B := 188192) (E := 107) (a := 4255 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell90 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 91 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell91_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (3439 / 4) (3471 / 4)) :
    let r := (201888643181 / 200000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below472 hn ho hu hG (B := 0.06747) (a := 4255 / 10) (P := -2.49645) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from4255 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from4255 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 188299) (B := 191820) (E := 77) (a := 4255 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell91 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 92 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell92_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (3471 / 4) (3503 / 4)) :
    let r := (50486320077 / 50000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below472 hn ho hu hG (B := 0.03505) (a := 4255 / 10) (P := -2.49645) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from4255 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from4255 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 191927) (B := 195483) (E := 40) (a := 4255 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell92 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 93 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell93_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (3503 / 4) (3535 / 4)) :
    let r := (505002183613 / 500000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below472 hn ho hu hG (B := 0.03288) (a := 4422 / 10) (P := -2.43707) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from4422 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from4422 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 195590) (B := 199180) (E := 39) (a := 4422 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell93 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 94 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell94_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (3535 / 4) (3567 / 4)) :
    let r := (126284657103 / 125000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below472 hn ho hu hG (B := 0.08178) (a := 4422 / 10) (P := -2.43707) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from4422 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from4422 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 199287) (B := 202912) (E := 97) (a := 4422 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell94 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 95 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell95_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (3567 / 4) (3599 / 4)) :
    let r := (505272604479 / 500000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below472 hn ho hu hG (B := 0.12140) (a := 4422 / 10) (P := -2.43707) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from4422 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from4422 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 203019) (B := 206679) (E := 144) (a := 4422 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell95 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 96 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell96_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (3599 / 4) (3631 / 4)) :
    let r := (1010808357247 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below472 hn ho hu hG (B := 0.09190) (a := 4422 / 10) (P := -2.43707) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from4422 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from4422 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 206786) (B := 210480) (E := 109) (a := 4422 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell96 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 97 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell97_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (3631 / 4) (3663 / 4)) :
    let r := (101106683053 / 100000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below472 hn ho hu hG (B := 0.00000) (a := 4422 / 10) (P := -2.43707) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from4422 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from4422 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 210587) (B := 214316) (E := 0) (a := 4422 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ by
          simpa only [neg_zero] using
            AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell97 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 98 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell98_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (3663 / 4) (3695 / 4)) :
    let r := (505660376539 / 500000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below472 hn ho hu hG (B := 0.08852) (a := 4422 / 10) (P := -2.43707) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from4422 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from4422 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 214423) (B := 218186) (E := 105) (a := 4422 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell98 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 99 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell99_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (3695 / 4) (3727 / 4)) :
    let r := (252892561199 / 250000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below472 hn ho hu hG (B := 0.11887) (a := 4422 / 10) (P := -2.43707) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from4422 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from4422 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 218293) (B := 222091) (E := 141) (a := 4422 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell99 hx hy)
        (by norm_num only)

private theorem witness_below522 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {U s B a T P C : ℝ}
    (hL : Real.log n ≤ U) (hm : k197Slope s ≤ 0) (ha₀ : (340 : ℝ) ≤ a)
    (hT : ∀ r : ℝ, a ≤ r → T ≤ gaussianTheta197 r) (hvs : 1.0118 ≤ s) (hneg : T ≤ 0)
    (hP : P ≤ T / 1.0118 + 0.03973 - 0.00026)
    (hC : ∀ r : ℝ, a ≤ r → 4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ C)
    (hmargin :
      0 ≤
        (15.0472769 : ℝ) + (0.018398 - B) + P + k197Slope s * (U / 2) - 4 * 0.006305 - C - 0.0006 +
          0.00345) :
    let r := s * Real.log n / 2
    r ∈ Set.Ico a 522 →
      (-4 * (Chebyshev.psi (r ^ 2) - r ^ 2) * quarterWeight656 (r ^ 2) (r ^ 2) ≤ B) →
      ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  intro r hra hb
  have hr₀ : r ∈ Set.Ico 340 522 := ⟨ha₀.trans hra.1, hra.2⟩
  apply uniform_witness_of_pair_false hn ho hu (X := r ^ 2)
  intro p q k _ _ _ a b c ha hb' hc hp hq hk hlev ht hsmall
  have hs₁ : 1 ≤ s := (by norm_num only : (1 : ℝ) ≤ 1.0118).trans hvs
  have hscale : r / s = Real.log n / 2 := by
    dsimp only [r]
    apply (div_eq_iff (zero_lt_one.trans_le hs₁).ne').mpr
    ring
  have hlevel : Real.log p + Real.log q + Real.log k = 4 * (Real.log n / 2) := by
    linarith only [hlev]
  have hpa l hl hcut := (hsmall l hl hcut).1
  have hpb l hl hcut := (hsmall l hl hcut).2.1
  have hpc l hl hcut := (hsmall l hl hcut).2.2
  have hspos : 0 < s := (by norm_num only : (0 : ℝ) < 1.0118).trans_le hvs
  have hθ : T / 1.0118 ≤ gaussianTheta197 r / s := by
    apply (le_div_iff₀ hspos).mpr
    have hdiv : T / 1.0118 ≤ 0 := div_nonpos_of_nonpos_of_nonneg hneg (by norm_num only)
    refine (mul_le_mul_of_nonpos_left hvs hdiv).trans ?_
    rw [div_mul_cancel₀ _ (by norm_num only)]
    exact hT r hra.1
  have hpole : (0.03973 : ℝ) ≤ gaussianNegPole197 / r := by
    apply (le_div_iff₀ ((by norm_num only : (0 : ℝ) < 340).trans_le hr₀.1)).mpr
    linarith only [hr₀.2.le, gaussian_neg_pole_lower_197]
  have hcost : P + 0.00026 ≤ gaussianTheta197 r / s + gaussianNegPole197 / r := by
    linarith only [hP, hθ, hpole]
  have hshift₀ :=
    shift_forward_of_refl ha hb' hc hG.riemann ((by norm_num only : (328 : ℝ) ≤ 340).trans hr₀.1)
      (by
        rw [mul_div_assoc, hscale]; exact hlevel)
      ht hpa hpb hpc hcost
      (gaussian_joint_to522 hG.riemann
        ⟨(by norm_num only : (332.15 : ℝ) ≤ 340).trans hr₀.1, hr₀.2.le⟩)
  have hshift :
    P ≤
      (gaussianShiftedForward197 a r + gaussianShiftedForward197 b r +
          gaussianShiftedForward197 c r) +
        gaussianHalfCoeff197 * r := by
    linarith only [hshift₀]
  have hcond := hC r hra.1
  rw [hscale] at hcond
  have hmain :=
    gaussian_k197_principal_to522 hG.riemann
      ⟨(by norm_num only : (663 / 2 : ℝ) ≤ 340).trans hr₀.1, hr₀.2.le⟩ hb
  have hcompare :=
    retained_comparison_of_gain ha hb' hc hp hq hk hG (C := 0)
      ((by norm_num only : (336.8 : ℝ) ≤ 340).trans hr₀.1) ∅ (Finset.empty_subset _)
      (fun n hn ↦ (Finset.notMem_empty n hn).elim) hlevel ht hpa hpb hpc (by rw [Finset.sum_empty])
  have hrF : r ∈ Set.Icc 328 522 := ⟨(by norm_num only : (328 : ℝ) ≤ 340).trans hr₀.1, hr₀.2.le⟩
  refine
    mid_pair_false (a := a) (b := b) (c := c) hG (B := 0.018398 - B)
      ⟨(by norm_num only : (336.8 : ℝ) ≤ 340).trans hr₀.1, hr₀.2.le.trans (by norm_num only)⟩ hcond
      (k197_main_reflect_to522 hrF) (gaussian_k197_reflect_credit_to522 hrF) ht hpa hpb hpc hcompare
      ?_ hshift (wide_linear_lower (Real.log_natCast_nonneg n) hL hs₁ hm) ?_
  · simpa only [sub_eq_add_neg, add_assoc] using hmain
  · linarith only [hmargin]

/-- Under GRH, a uniform Korselt triple in K197 cell 100 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell100_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (3727 / 4) (3791 / 4)) :
    let r := (1011815421411 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below522 hn ho hu hG (B := 0.04037) (a := 471) (P := -2.33811) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from471 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from471 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 222198) (B := 229896) (E := 51) (a := 471) (by norm_num only) hL
        (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell100 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 101 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell101_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (3791 / 4) (3823 / 4)) :
    let r := (1012293272431 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below522 hn ho hu hG (B := 0.01267) (a := 471) (P := -2.33811) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from471 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from471 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 230112) (B := 234014) (E := 16) (a := 471) (by norm_num only) hL
        (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell101 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 102 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell102_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (3823 / 4) (3855 / 4)) :
    let r := (1012526158983 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below522 hn ho hu hG (B := 0.15672) (a := 471) (P := -2.33811) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from471 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from471 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 234121) (B := 238058) (E := 198) (a := 471) (by norm_num only) hL
        (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell102 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 103 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell103_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (3855 / 4) (3919 / 4)) :
    let r := (506377577521 / 500000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below522 hn ho hu hG (B := 0.11077) (a := 488) (P := -2.28497) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from488 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from488 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 238164) (B := 246139) (E := 145) (a := 488) (by norm_num only) hL
        (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell103 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 104 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell104_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (3919 / 4) (3983 / 4)) :
    let r := (506600930973 / 500000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below522 hn ho hu hG (B := 0.06417) (a := 488) (P := -2.28497) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from488 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from488 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 246355) (B := 254468) (E := 84) (a := 488) (by norm_num only) hL
        (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell104 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 105 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell105_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (3983 / 4) (4047 / 4)) :
    let r := (1013634134211 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below522 hn ho hu hG (B := 0.11994) (a := 488) (P := -2.28497) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from488 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from488 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 254684) (B := 262936) (E := 157) (a := 488) (by norm_num only) hL
        (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell105 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 106 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell106_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (4047 / 4) (4111 / 4)) :
    let r := (126756583177 / 125000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below522 hn ho hu hG (B := 0.13369) (a := 488) (P := -2.28497) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from488 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from488 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 263152) (B := 271542) (E := 175) (a := 488) (by norm_num only) hL
        (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell106 hx hy)
        (by norm_num only)

private theorem sqrt_boundary_bound {r : ℝ} (hr : r ∈ Set.Ico 521 1000) :
    (-4 : ℝ) * (Chebyshev.psi (r ^ 2) - r ^ 2) * quarterWeight656 (r ^ 2) (r ^ 2) ≤ 0.29824 := by
  have hp : 0 < r := (by norm_num only : (0 : ℝ) < 521).trans_le hr.1
  have hl : (1423 : ℝ) ≤ r ^ 2 :=
    (by norm_num only : (1423 : ℝ) ≤ 521 ^ 2).trans (pow_le_pow_left₀ (by norm_num only) hr.1 2)
  have hu : r ^ 2 ≤ (1000000 : ℝ) := (pow_le_pow_left₀ hp.le hr.2.le 2).trans (by norm_num only)
  have hψ := AnalyticNumberTheory.Arithmetic.psi_four_fifths_1423_million hl hu
  rw [Real.sqrt_sq hp.le] at hψ
  rw [quarter_cutoff_weight_656 (sq_pos_of_pos hp), Real.sqrt_sq hp.le]
  let W := (quarterKernel656.transform 1).re
  have hw : 0 ≤ W := by linarith only [quarter_unit_weight_656.1]
  have hm := mul_le_mul_of_nonneg_right (abs_le.mp hψ).1 (div_nonneg hw hp.le)
  have hc : -(4 / 5 * r) * (W / r) = -(4 / 5 * W) := by
    rw [show -(4 / 5 * r) * (W / r) = (-(4 / 5 * W) * r) / r by ring,
      mul_div_cancel_right₀ _ hp.ne']
  rw [hc] at hm
  change (-4 : ℝ) * (Chebyshev.psi (r ^ 2) - r ^ 2) * (W / r) ≤ 0.29824
  linarith only [hm, quarter_unit_weight_656.2]

private theorem witness_below572 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {U s a T P C : ℝ}
    (hL : Real.log n ≤ U) (hm : k197Slope s ≤ 0) (ha₀ : (521 : ℝ) ≤ a)
    (hT : ∀ r : ℝ, a ≤ r → T ≤ gaussianTheta197 r) (hvs : 1.0144 ≤ s) (hneg : T ≤ 0)
    (hP : P ≤ T / 1.0144 + 0.03625 - 0.0003)
    (hC : ∀ r : ℝ, a ≤ r → 4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ C)
    (hmargin :
      0 ≤
        (15.0472769 : ℝ) + (0.014378 - 0.29824) + P + k197Slope s * (U / 2) - 4 * 0.006305 - C -
            0.0007 +
          0.0028) :
    let r := s * Real.log n / 2
    r ∈ Set.Ico a 572 →
      ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  intro r hra
  have hr₀ : r ∈ Set.Ico 521 572 := ⟨ha₀.trans hra.1, hra.2⟩
  apply uniform_witness_of_pair_false hn ho hu (X := r ^ 2)
  intro p q k _ _ _ a b c ha hb' hc hp hq hk hlev ht hsmall
  have hs₁ : 1 ≤ s := (by norm_num only : (1 : ℝ) ≤ 1.0144).trans hvs
  have hscale : r / s = Real.log n / 2 := by
    dsimp only [r]
    apply (div_eq_iff (zero_lt_one.trans_le hs₁).ne').mpr
    ring
  have hlevel : Real.log p + Real.log q + Real.log k = 4 * (Real.log n / 2) := by
    linarith only [hlev]
  have hpa l hl hcut := (hsmall l hl hcut).1
  have hpb l hl hcut := (hsmall l hl hcut).2.1
  have hpc l hl hcut := (hsmall l hl hcut).2.2
  have hspos : 0 < s := (by norm_num only : (0 : ℝ) < 1.0144).trans_le hvs
  have hθ : T / 1.0144 ≤ gaussianTheta197 r / s := by
    apply (le_div_iff₀ hspos).mpr
    have hdiv : T / 1.0144 ≤ 0 := div_nonpos_of_nonpos_of_nonneg hneg (by norm_num only)
    refine (mul_le_mul_of_nonpos_left hvs hdiv).trans ?_
    rw [div_mul_cancel₀ _ (by norm_num only)]
    exact hT r hra.1
  have hpole : (0.03625 : ℝ) ≤ gaussianNegPole197 / r := by
    apply (le_div_iff₀ ((by norm_num only : (0 : ℝ) < 521).trans_le hr₀.1)).mpr
    linarith only [hr₀.2.le, gaussian_neg_pole_lower_197]
  have hcost : P + 0.0003 ≤ gaussianTheta197 r / s + gaussianNegPole197 / r := by
    linarith only [hP, hθ, hpole]
  have hshift₀ :=
    shift_forward_of_refl ha hb' hc hG.riemann ((by norm_num only : (328 : ℝ) ≤ 521).trans hr₀.1)
      (by
        rw [mul_div_assoc, hscale]; exact hlevel)
      ht hpa hpb hpc hcost
      (gaussian_joint_to572 hG.riemann
        ⟨(by norm_num only : (332.15 : ℝ) ≤ 521).trans hr₀.1, hr₀.2.le⟩)
  have hshift :
    P ≤
      (gaussianShiftedForward197 a r + gaussianShiftedForward197 b r +
          gaussianShiftedForward197 c r) +
        gaussianHalfCoeff197 * r := by
    linarith only [hshift₀]
  have hcond := hC r hra.1
  rw [hscale] at hcond
  have hmain :=
    gaussian_k197_principal_to572 hG.riemann
      ⟨(by norm_num only : (663 / 2 : ℝ) ≤ 521).trans hr₀.1, hr₀.2.le⟩
      (sqrt_boundary_bound ⟨hr₀.1, hr₀.2.trans (by norm_num only)⟩)
  have hcompare :=
    retained_comparison_of_gain ha hb' hc hp hq hk hG (C := 0)
      ((by norm_num only : (336.8 : ℝ) ≤ 521).trans hr₀.1) ∅ (Finset.empty_subset _)
      (fun n hn ↦ (Finset.notMem_empty n hn).elim) hlevel ht hpa hpb hpc (by rw [Finset.sum_empty])
  have hrF : r ∈ Set.Icc 328 572 := ⟨(by norm_num only : (328 : ℝ) ≤ 521).trans hr₀.1, hr₀.2.le⟩
  refine
    mid_pair_false (a := a) (b := b) (c := c) hG (B := 0.014378 - 0.29824)
      ⟨(by norm_num only : (336.8 : ℝ) ≤ 521).trans hr₀.1, hr₀.2.le.trans (by norm_num only)⟩ hcond
      (k197_main_reflect_to572 hrF) (gaussian_k197_reflect_credit_to572 hrF) ht hpa hpb hpc hcompare
      ?_ hshift (wide_linear_lower (Real.log_natCast_nonneg n) hL hs₁ hm) ?_
  · simpa only [sub_eq_add_neg, add_assoc] using hmain
  · linarith only [hmargin]

/-- Under GRH, a uniform Korselt triple in K197 cell 107 has a prime
rejecting base within the squared certified radius by the square-root envelope. -/
theorem gaussian_k197_cell107_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (4111 / 4) (4175 / 4)) :
    let r := (1014458105391 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below572 hn ho hu hG (a := 2085 / 4) (P := -2.18552) hL.2 (by norm_num only [k197Slope])
      (by norm_num only) (fun _ hr ↦ theta_from52125 hr) (by norm_num only) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ gaussian_main_conductor_from52125 hr (by norm_num only))
      (by norm_num only [k197Slope])
  exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩

/-- Under GRH, a uniform Korselt triple in K197 cell 108 has a prime
rejecting base within the squared certified radius by the square-root envelope. -/
theorem gaussian_k197_cell108_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (4175 / 4) (4239 / 4)) :
    let r := (15857047869 / 15625000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below572 hn ho hu hG (a := 2648 / 5) (P := -2.16244) hL.2 (by norm_num only [k197Slope])
      (by norm_num only) (fun _ hr ↦ theta_from5296 hr) (by norm_num only) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ gaussian_main_conductor_from5296 hr (by norm_num only))
      (by norm_num only [k197Slope])
  exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩

/-- Under GRH, a uniform Korselt triple in K197 cell 109 has a prime
rejecting base within the squared certified radius by the square-root envelope. -/
theorem gaussian_k197_cell109_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (4239 / 4) (4303 / 4)) :
    let r := (1015232112301 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below572 hn ho hu hG (a := 5379 / 10) (P := -2.14000) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from5379 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from5379 hr (by norm_num only))
      (by norm_num only [k197Slope])
  exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩

/-- Under GRH, a uniform Korselt triple in K197 cell 110 has a prime
rejecting base within the squared certified radius by the square-root envelope. -/
theorem gaussian_k197_cell110_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (4303 / 4) (4367 / 4)) :
    let r := (253900447299 / 250000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below572 hn ho hu hG (a := 2731 / 5) (P := -2.11801) hL.2 (by norm_num only [k197Slope])
      (by norm_num only) (fun _ hr ↦ theta_from5462 hr) (by norm_num only) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ gaussian_main_conductor_from5462 hr (by norm_num only))
      (by norm_num only [k197Slope])
  exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩

/-- Under GRH, a uniform Korselt triple in K197 cell 111 has a prime
rejecting base within the squared certified radius by the square-root envelope. -/
theorem gaussian_k197_cell111_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (4367 / 4) (4431 / 4)) :
    let r := (1015960600149 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below572 hn ho hu hG (a := 2731 / 5) (P := -2.11801) hL.2 (by norm_num only [k197Slope])
      (by norm_num only) (fun _ hr ↦ theta_from5462 hr) (by norm_num only) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ gaussian_main_conductor_from5462 hr (by norm_num only))
      (by norm_num only [k197Slope])
  exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩

/-- Under GRH, a uniform Korselt triple in K197 cell 112 has a prime
rejecting base within the squared certified radius by the square-root envelope. -/
theorem gaussian_k197_cell112_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (4431 / 4) (4495 / 4)) :
    let r := (101630902143 / 100000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below572 hn ho hu hG (a := 2731 / 5) (P := -2.11801) hL.2 (by norm_num only [k197Slope])
      (by norm_num only) (fun _ hr ↦ theta_from5462 hr) (by norm_num only) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ gaussian_main_conductor_from5462 hr (by norm_num only))
      (by norm_num only [k197Slope])
  exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩

private theorem witness_below672 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {U s B a T P C : ℝ}
    (hL : Real.log n ≤ U) (hm : k197Slope s ≤ 0) (ha₀ : (340 : ℝ) ≤ a)
    (hT : ∀ r : ℝ, a ≤ r → T ≤ gaussianTheta197 r) (hvs : 1.0166 ≤ s) (hneg : T ≤ 0)
    (hP : P ≤ T / 1.0166 + 0.03086 - 0.0005)
    (hC : ∀ r : ℝ, a ≤ r → 4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ C)
    (hmargin :
      0 ≤
        (15.0472769 : ℝ) + (0.007898 - B) + P + k197Slope s * (U / 2) - 4 * 0.006305 - C - 0.0008 +
          0.00197) :
    let r := s * Real.log n / 2
    r ∈ Set.Ico a 672 →
      (-4 * (Chebyshev.psi (r ^ 2) - r ^ 2) * quarterWeight656 (r ^ 2) (r ^ 2) ≤ B) →
      ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  intro r hra hb
  have hr₀ : r ∈ Set.Ico 340 672 := ⟨ha₀.trans hra.1, hra.2⟩
  apply uniform_witness_of_pair_false hn ho hu (X := r ^ 2)
  intro p q k _ _ _ a b c ha hb' hc hp hq hk hlev ht hsmall
  have hs₁ : 1 ≤ s := (by norm_num only : (1 : ℝ) ≤ 1.0166).trans hvs
  have hscale : r / s = Real.log n / 2 := by
    dsimp only [r]
    apply (div_eq_iff (zero_lt_one.trans_le hs₁).ne').mpr
    ring
  have hlevel : Real.log p + Real.log q + Real.log k = 4 * (Real.log n / 2) := by
    linarith only [hlev]
  have hpa l hl hcut := (hsmall l hl hcut).1
  have hpb l hl hcut := (hsmall l hl hcut).2.1
  have hpc l hl hcut := (hsmall l hl hcut).2.2
  have hspos : 0 < s := (by norm_num only : (0 : ℝ) < 1.0166).trans_le hvs
  have hθ : T / 1.0166 ≤ gaussianTheta197 r / s := by
    apply (le_div_iff₀ hspos).mpr
    have hdiv : T / 1.0166 ≤ 0 := div_nonpos_of_nonpos_of_nonneg hneg (by norm_num only)
    refine (mul_le_mul_of_nonpos_left hvs hdiv).trans ?_
    rw [div_mul_cancel₀ _ (by norm_num only)]
    exact hT r hra.1
  have hpole : (0.03086 : ℝ) ≤ gaussianNegPole197 / r := by
    apply (le_div_iff₀ ((by norm_num only : (0 : ℝ) < 340).trans_le hr₀.1)).mpr
    linarith only [hr₀.2.le, gaussian_neg_pole_lower_197]
  have hcost : P + 0.0005 ≤ gaussianTheta197 r / s + gaussianNegPole197 / r := by
    linarith only [hP, hθ, hpole]
  have hshift₀ :=
    shift_forward_of_refl ha hb' hc hG.riemann ((by norm_num only : (328 : ℝ) ≤ 340).trans hr₀.1)
      (by
        rw [mul_div_assoc, hscale]; exact hlevel)
      ht hpa hpb hpc hcost
      (gaussian_joint_to672 hG.riemann
        ⟨(by norm_num only : (332.15 : ℝ) ≤ 340).trans hr₀.1, hr₀.2.le⟩)
  have hshift :
    P ≤
      (gaussianShiftedForward197 a r + gaussianShiftedForward197 b r +
          gaussianShiftedForward197 c r) +
        gaussianHalfCoeff197 * r := by
    linarith only [hshift₀]
  have hcond := hC r hra.1
  rw [hscale] at hcond
  have hmain :=
    gaussian_k197_principal_to672 hG.riemann
      ⟨(by norm_num only : (663 / 2 : ℝ) ≤ 340).trans hr₀.1, hr₀.2.le⟩ hb
  have hcompare :=
    retained_comparison_of_gain ha hb' hc hp hq hk hG (C := 0)
      ((by norm_num only : (336.8 : ℝ) ≤ 340).trans hr₀.1) ∅ (Finset.empty_subset _)
      (fun n hn ↦ (Finset.notMem_empty n hn).elim) hlevel ht hpa hpb hpc (by rw [Finset.sum_empty])
  have hrF : r ∈ Set.Icc 328 672 := ⟨(by norm_num only : (328 : ℝ) ≤ 340).trans hr₀.1, hr₀.2.le⟩
  refine
    mid_pair_false (a := a) (b := b) (c := c) hG (B := 0.007898 - B)
      ⟨(by norm_num only : (336.8 : ℝ) ≤ 340).trans hr₀.1, hr₀.2.le.trans (by norm_num only)⟩ hcond
      (k197_main_reflect_to672 hrF) (gaussian_k197_reflect_credit_to672 hrF) ht hpa hpb hpc hcompare
      ?_ hshift (wide_linear_lower (Real.log_natCast_nonneg n) hL hs₁ hm) ?_
  · simpa only [sub_eq_add_neg, add_assoc] using hmain
  · linarith only [hmargin]

/-- Under GRH, a uniform Korselt triple in K197 cell 113 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell113_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (4495 / 4) (4623 / 4)) :
    let r := (254161875467 / 250000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below672 hn ho hu hG (B := 0) (a := 571) (P := -2.05603) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from571 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from571 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 326302) (B := 345151) (E := 0) (a := 571) (by norm_num only) hL
        (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ by
          simpa only [neg_zero] using
            AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell113 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 114 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell114_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (4623 / 4) (4751 / 4)) :
    let r := (1017296309847 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below672 hn ho hu hG (B := 0.00849) (a := 571) (P := -2.05603) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from571 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from571 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 345591) (B := 364994) (E := 13) (a := 571) (by norm_num only) hL
        (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell114 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple in K197 cell 115 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell115_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (4751 / 4) (4815 / 4)) :
    let r := (1017910135939 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below672 hn ho hu hG (B := 0.29824) (a := 604) (P := -1.97801) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from604 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from604 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · apply sqrt_boundary_bound
    exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩

/-- Under GRH, a uniform Korselt triple in K197 cell 116 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell116_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (4815 / 4) (4879 / 4)) :
    let r := (254551202941 / 250000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below672 hn ho hu hG (B := 0.29824) (a := 604) (P := -1.97801) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from604 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from604 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · apply sqrt_boundary_bound
    exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩

/-- Under GRH, a uniform Korselt triple in K197 cell 117 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell117_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (4879 / 4) (4943 / 4)) :
    let r := (509245880961 / 500000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below672 hn ho hu hG (B := 0.29824) (a := 604) (P := -1.97801) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from604 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from604 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · apply sqrt_boundary_bound
    exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩

/-- Under GRH, a uniform Korselt triple in K197 cell 118 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell118_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (4943 / 4) (5007 / 4)) :
    let r := (63673205597 / 62500000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below672 hn ho hu hG (B := 0.29824) (a := 604) (P := -1.97801) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from604 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from604 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · apply sqrt_boundary_bound
    exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩

/-- Under GRH, a uniform Korselt triple in K197 cell 119 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell119_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (5007 / 4) (5071 / 4)) :
    let r := (1019043682131 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below672 hn ho hu hG (B := 0.29824) (a := 604) (P := -1.97801) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from604 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from604 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · apply sqrt_boundary_bound
    exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩

/-- Under GRH, a uniform Korselt triple in K197 cell 120 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell120_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (5071 / 4) (5135 / 4)) :
    let r := (509654606237 / 500000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below672 hn ho hu hG (B := 0.29824) (a := 636) (P := -1.90791) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from636 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from636 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · apply sqrt_boundary_bound
    exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩

/-- Under GRH, a uniform Korselt triple in K197 cell 121 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell121_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (5135 / 4) (5199 / 4)) :
    let r := (127446017457 / 125000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below672 hn ho hu hG (B := 0.29824) (a := 636) (P := -1.90791) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from636 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from636 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · apply sqrt_boundary_bound
    exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩

/-- Under GRH, a uniform Korselt triple in K197 cell 122 has a prime
rejecting base within the squared certified radius. -/
theorem gaussian_k197_cell122_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (5199 / 4) (5263 / 4)) :
    let r := (127477588733 / 125000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below672 hn ho hu hG (B := 0.29824) (a := 636) (P := -1.90791) hL.2
      (by norm_num only [k197Slope]) (by norm_num only) (fun _ hr ↦ theta_from636 hr)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ gaussian_main_conductor_from636 hr (by norm_num only))
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · apply sqrt_boundary_bound
    exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩

private theorem witness_below788 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {U s a T P C : ℝ}
    (hL : Real.log n ≤ U) (hm : k197Slope s ≤ 0) (ha₀ : (671 : ℝ) ≤ a)
    (hT : ∀ r : ℝ, a ≤ r → T ≤ gaussianTheta197 r) (hvs : 1.02 ≤ s) (hneg : T ≤ 0)
    (hP : P ≤ T / 1.02 + 0.02631 - 0.0008)
    (hC : ∀ r : ℝ, a ≤ r → 4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ C)
    (hmargin :
      0 ≤
        (15.0472769 : ℝ) + (0.002648 - 0.29824) + P + k197Slope s * (U / 2) - 4 * 0.006305 - C -
            0.001 +
          0.00137) :
    let r := s * Real.log n / 2
    r ∈ Set.Ico a 788 →
      ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  intro r hra
  have hr₀ : r ∈ Set.Ico 671 788 := ⟨ha₀.trans hra.1, hra.2⟩
  apply uniform_witness_of_pair_false hn ho hu (X := r ^ 2)
  intro p q k _ _ _ a b c ha hb' hc hp hq hk hlev ht hsmall
  have hs₁ : 1 ≤ s := (by norm_num only : (1 : ℝ) ≤ 1.02).trans hvs
  have hscale : r / s = Real.log n / 2 := by
    dsimp only [r]
    apply (div_eq_iff (zero_lt_one.trans_le hs₁).ne').mpr
    ring
  have hlevel : Real.log p + Real.log q + Real.log k = 4 * (Real.log n / 2) := by
    linarith only [hlev]
  have hpa l hl hcut := (hsmall l hl hcut).1
  have hpb l hl hcut := (hsmall l hl hcut).2.1
  have hpc l hl hcut := (hsmall l hl hcut).2.2
  have hspos : 0 < s := (by norm_num only : (0 : ℝ) < 1.02).trans_le hvs
  have hθ : T / 1.02 ≤ gaussianTheta197 r / s := by
    apply (le_div_iff₀ hspos).mpr
    have hdiv : T / 1.02 ≤ 0 := div_nonpos_of_nonpos_of_nonneg hneg (by norm_num only)
    refine (mul_le_mul_of_nonpos_left hvs hdiv).trans ?_
    rw [div_mul_cancel₀ _ (by norm_num only)]
    exact hT r hra.1
  have hpole : (0.02631 : ℝ) ≤ gaussianNegPole197 / r := by
    apply (le_div_iff₀ ((by norm_num only : (0 : ℝ) < 671).trans_le hr₀.1)).mpr
    linarith only [hr₀.2.le, gaussian_neg_pole_lower_197]
  have hcost : P + 0.0008 ≤ gaussianTheta197 r / s + gaussianNegPole197 / r := by
    linarith only [hP, hθ, hpole]
  have hshift₀ :=
    shift_forward_of_refl ha hb' hc hG.riemann ((by norm_num only : (328 : ℝ) ≤ 671).trans hr₀.1)
      (by
        rw [mul_div_assoc, hscale]; exact hlevel)
      ht hpa hpb hpc hcost
      (gaussian_joint_to788 hG.riemann
        ⟨(by norm_num only : (332.15 : ℝ) ≤ 671).trans hr₀.1, hr₀.2.le⟩)
  have hshift :
    P ≤
      (gaussianShiftedForward197 a r + gaussianShiftedForward197 b r +
          gaussianShiftedForward197 c r) +
        gaussianHalfCoeff197 * r := by
    linarith only [hshift₀]
  have hcond := hC r hra.1
  rw [hscale] at hcond
  have hmain :=
    gaussian_k197_principal_to788 hG.riemann
      ⟨(by norm_num only : (663 / 2 : ℝ) ≤ 671).trans hr₀.1, hr₀.2.le⟩
      (sqrt_boundary_bound
        ⟨(by norm_num only : (521 : ℝ) ≤ 671).trans hr₀.1, hr₀.2.trans (by norm_num only)⟩)
  have hcompare :=
    retained_comparison_of_gain ha hb' hc hp hq hk hG (C := 0)
      ((by norm_num only : (336.8 : ℝ) ≤ 671).trans hr₀.1) ∅ (Finset.empty_subset _)
      (fun n hn ↦ (Finset.notMem_empty n hn).elim) hlevel ht hpa hpb hpc (by rw [Finset.sum_empty])
  have hrF : r ∈ Set.Icc 328 788 := ⟨(by norm_num only : (328 : ℝ) ≤ 671).trans hr₀.1, hr₀.2.le⟩
  refine
    mid_pair_false (a := a) (b := b) (c := c) hG (B := 0.002648 - 0.29824)
      ⟨(by norm_num only : (336.8 : ℝ) ≤ 671).trans hr₀.1, hr₀.2.le⟩ hcond
      (k197_main_reflect_to788 hrF) (gaussian_k197_reflect_credit_to788 hrF) ht hpa hpb hpc hcompare
      ?_ hshift (wide_linear_lower (Real.log_natCast_nonneg n) hL hs₁ hm) ?_
  · simpa only [sub_eq_add_neg, add_assoc] using hmain
  · linarith only [hmargin]

/-- Under GRH, a uniform Korselt triple in K197 cell 123 has a prime
rejecting base within the squared certified radius by the square-root envelope. -/
theorem gaussian_k197_cell123_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (5263 / 4) (5327 / 4)) :
    let r := (204013431439 / 200000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below788 hn ho hu hG (s := 204013431439 / 200000000000) (a := 6710 / 10) (P :=
      -1.835466) hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from6710 (s := 204013431439 / 200000000000) hr (by norm_num only)).1)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ (conductors_from6710 hr (by norm_num only)).2) (by norm_num only [k197Slope])
  exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩

/-- Under GRH, a uniform Korselt triple in K197 cell 124 has a prime
rejecting base within the squared certified radius by the square-root envelope. -/
theorem gaussian_k197_cell124_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (5327 / 4) (5391 / 4)) :
    let r := (1020307704381 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below788 hn ho hu hG (s := 1020307704381 / 1000000000000) (a := 6793 / 10) (P :=
      -1.819468) hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦
        (conductors_from6793 (s := 1020307704381 / 1000000000000) hr (by norm_num only)).1)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ (conductors_from6793 hr (by norm_num only)).2) (by norm_num only [k197Slope])
  exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩

private theorem cell125_left {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (5391 / 4) (5455 / 4)) :
    let r := (510271281739 / 500000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below788 hn ho hu hG (s := 510271281739 / 500000000000) (a := 6877 / 10) (P :=
      -1.803559) hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from6877 (s := 510271281739 / 500000000000) hr (by norm_num only)).1)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ (conductors_from6877 hr (by norm_num only)).2) (by norm_num only [k197Slope])
  exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩

private theorem cell125_right {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (5455 / 4) (5519 / 4)) :
    let r := (510271281739 / 500000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below788 hn ho hu hG (s := 510271281739 / 500000000000) (a := 6958 / 10) (P :=
      -1.788493) hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from6958 (s := 510271281739 / 500000000000) hr (by norm_num only)).1)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ (conductors_from6958 hr (by norm_num only)).2) (by norm_num only [k197Slope])
  exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩

private theorem cell126_left {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (5519 / 4) (5583 / 4)) :
    let r := (255249003993 / 250000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below788 hn ho hu hG (s := 255249003993 / 250000000000) (a := 7043 / 10) (P :=
      -1.772953) hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from7043 (s := 255249003993 / 250000000000) hr (by norm_num only)).1)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ (conductors_from7043 hr (by norm_num only)).2) (by norm_num only [k197Slope])
  exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩

private theorem cell126_right {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (5583 / 4) (5647 / 4)) :
    let r := (255249003993 / 250000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below788 hn ho hu hG (s := 255249003993 / 250000000000) (a := 7125 / 10) (P :=
      -1.758223) hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from7125 (s := 255249003993 / 250000000000) hr (by norm_num only)).1)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ (conductors_from7125 hr (by norm_num only)).2) (by norm_num only [k197Slope])
  exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩

private theorem cell127_left {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (5647 / 4) (5711 / 4)) :
    let r := (102142902047 / 100000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below788 hn ho hu hG (s := 102142902047 / 100000000000) (a := 7210 / 10) (P :=
      -1.743223) hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from7210 (s := 102142902047 / 100000000000) hr (by norm_num only)).1)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ (conductors_from7210 hr (by norm_num only)).2) (by norm_num only [k197Slope])
  exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩

private theorem cell127_right {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (5711 / 4) (5775 / 4)) :
    let r := (102142902047 / 100000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below788 hn ho hu hG (s := 102142902047 / 100000000000) (a := 7291 / 10) (P := -1.72918)
      hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from7291 (s := 102142902047 / 100000000000) hr (by norm_num only)).1)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ (conductors_from7291 hr (by norm_num only)).2) (by norm_num only [k197Slope])
  exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩

private theorem cell128_left {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (5775 / 4) (5839 / 4)) :
    let r := (510921474027 / 500000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below788 hn ho hu hG (s := 510921474027 / 500000000000) (a := 7376 / 10) (P := -1.71468)
      hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from7376 (s := 510921474027 / 500000000000) hr (by norm_num only)).1)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ (conductors_from7376 hr (by norm_num only)).2) (by norm_num only [k197Slope])
  exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩

private theorem cell128_right {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (5839 / 4) (5903 / 4)) :
    let r := (510921474027 / 500000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below788 hn ho hu hG (s := 510921474027 / 500000000000) (a := 7458 / 10) (P :=
      -1.700933) hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from7458 (s := 510921474027 / 500000000000) hr (by norm_num only)).1)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ (conductors_from7458 hr (by norm_num only)).2) (by norm_num only [k197Slope])
  exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩

private theorem cell129_left {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (5903 / 4) (5967 / 4)) :
    let r := (1022239049827 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below788 hn ho hu hG (s := 1022239049827 / 1000000000000) (a := 7542 / 10) (P :=
      -1.68708) hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦
        (conductors_from7542 (s := 1022239049827 / 1000000000000) hr (by norm_num only)).1)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ (conductors_from7542 hr (by norm_num only)).2) (by norm_num only [k197Slope])
  exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩

private theorem cell129_right {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (5967 / 4) (6031 / 4)) :
    let r := (1022239049827 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below788 hn ho hu hG (s := 1022239049827 / 1000000000000) (a := 7624 / 10) (P :=
      -1.673791) hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦
        (conductors_from7624 (s := 1022239049827 / 1000000000000) hr (by norm_num only)).1)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ (conductors_from7624 hr (by norm_num only)).2) (by norm_num only [k197Slope])
  exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩

private theorem cell130_left {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (6031 / 4) (6095 / 4)) :
    let r := (1597841359 / 1562500000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below788 hn ho hu hG (s := 1597841359 / 1562500000) (a := 7709 / 10) (P := -1.660233)
      hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from7709 (s := 1597841359 / 1562500000) hr (by norm_num only)).1)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ (conductors_from7709 hr (by norm_num only)).2) (by norm_num only [k197Slope])
  exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩

private theorem cell130_right {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (6095 / 4) (6159 / 4)) :
    let r := (1597841359 / 1562500000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    witness_below788 hn ho hu hG (s := 1597841359 / 1562500000) (a := 7791 / 10) (P := -1.647369)
      hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from7791 (s := 1597841359 / 1562500000) hr (by norm_num only)).1)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (fun _ hr ↦ (conductors_from7791 hr (by norm_num only)).2) (by norm_num only [k197Slope])
  exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩

/-- Under GRH, a uniform Korselt triple in K197 cell 125 has a prime
rejecting base within the squared certified radius, using a midpoint conductor bound. -/
theorem gaussian_k197_cell125_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (5391 / 4) (5519 / 4)) :
    let r := (510271281739 / 500000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  by_cases hm : Real.log n ≤ 5455 / 4
  · exact cell125_left hn ho hu hG ⟨hL.1, hm⟩
  exact cell125_right hn ho hu hG ⟨le_of_not_ge hm, hL.2⟩

/-- Under GRH, a uniform Korselt triple in K197 cell 126 has a prime
rejecting base within the squared certified radius, using a midpoint conductor bound. -/
theorem gaussian_k197_cell126_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (5519 / 4) (5647 / 4)) :
    let r := (255249003993 / 250000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  by_cases hm : Real.log n ≤ 5583 / 4
  · exact cell126_left hn ho hu hG ⟨hL.1, hm⟩
  exact cell126_right hn ho hu hG ⟨le_of_not_ge hm, hL.2⟩

/-- Under GRH, a uniform Korselt triple in K197 cell 127 has a prime
rejecting base within the squared certified radius, using a midpoint conductor bound. -/
theorem gaussian_k197_cell127_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (5647 / 4) (5775 / 4)) :
    let r := (102142902047 / 100000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  by_cases hm : Real.log n ≤ 5711 / 4
  · exact cell127_left hn ho hu hG ⟨hL.1, hm⟩
  exact cell127_right hn ho hu hG ⟨le_of_not_ge hm, hL.2⟩

/-- Under GRH, a uniform Korselt triple in K197 cell 128 has a prime
rejecting base within the squared certified radius, using a midpoint conductor bound. -/
theorem gaussian_k197_cell128_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (5775 / 4) (5903 / 4)) :
    let r := (510921474027 / 500000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  by_cases hm : Real.log n ≤ 5839 / 4
  · exact cell128_left hn ho hu hG ⟨hL.1, hm⟩
  exact cell128_right hn ho hu hG ⟨le_of_not_ge hm, hL.2⟩

/-- Under GRH, a uniform Korselt triple in K197 cell 129 has a prime
rejecting base within the squared certified radius, using a midpoint conductor bound. -/
theorem gaussian_k197_cell129_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (5903 / 4) (6031 / 4)) :
    let r := (1022239049827 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  by_cases hm : Real.log n ≤ 5967 / 4
  · exact cell129_left hn ho hu hG ⟨hL.1, hm⟩
  exact cell129_right hn ho hu hG ⟨le_of_not_ge hm, hL.2⟩

/-- Under GRH, a uniform Korselt triple in K197 cell 130 has a prime
rejecting base within the squared certified radius, using a midpoint conductor bound. -/
theorem gaussian_k197_cell130_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (6031 / 4) (6159 / 4)) :
    let r := (1597841359 / 1562500000 : ℝ) * Real.log n / 2
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  by_cases hm : Real.log n ≤ 6095 / 4
  · exact cell130_left hn ho hu hG ⟨hL.1, hm⟩
  exact cell130_right hn ho hu hG ⟨le_of_not_ge hm, hL.2⟩

private theorem witness_below1000_of_boundary {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {U s a T P C B : ℝ} (hL : Real.log n ≤ U) (hm : k197Slope s ≤ 0) (ha₀ : (787 : ℝ) ≤ a)
    (hT : ∀ r : ℝ, a ≤ r → T ≤ gaussianTheta197 r) (hvs : 1.02 ≤ s)
    (hP : P ≤ T / s + 0.02074 - 0.00111)
    (hC : ∀ r : ℝ, a ≤ r → 4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ C)
    (hmargin :
      0 ≤
        (15.0472769 : ℝ) + (-0.004 - B) + P + k197Slope s * (U / 2) - 4 * 0.00683 - C - 0.0012 +
          0.00082) :
    let r := s * Real.log n / 2
    r ∈ Set.Ico a 1000 →
      (-4 * (Chebyshev.psi (r ^ 2) - r ^ 2) * quarterWeight656 (r ^ 2) (r ^ 2) ≤ B) →
      ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  intro r hra hb
  have hr₀ : r ∈ Set.Ico 787 1000 := ⟨ha₀.trans hra.1, hra.2⟩
  apply uniform_witness_of_pair_false hn ho hu (X := r ^ 2)
  intro p q k _ _ _ a b c ha hb' hc hp hq hk hlev ht hsmall
  have hs₁ : 1 ≤ s := (by norm_num only : (1 : ℝ) ≤ 1.02).trans hvs
  have hscale : r / s = Real.log n / 2 := by
    dsimp only [r]
    apply (div_eq_iff (zero_lt_one.trans_le hs₁).ne').mpr
    ring
  have hlevel : Real.log p + Real.log q + Real.log k = 4 * (Real.log n / 2) := by
    linarith only [hlev]
  have hpa l hl hcut := (hsmall l hl hcut).1
  have hpb l hl hcut := (hsmall l hl hcut).2.1
  have hpc l hl hcut := (hsmall l hl hcut).2.2
  have hspos : 0 < s := (by norm_num only : (0 : ℝ) < 1.02).trans_le hvs
  have hθ := div_le_div_of_nonneg_right (hT r hra.1) hspos.le
  have hpole : (0.02074 : ℝ) ≤ gaussianNegPole197 / r := by
    apply (le_div_iff₀ ((by norm_num only : (0 : ℝ) < 787).trans_le hr₀.1)).mpr
    linarith only [hr₀.2.le, gaussian_neg_pole_lower_197]
  have hcost : P + 0.00111 ≤ gaussianTheta197 r / s + gaussianNegPole197 / r := by
    linarith only [hP, hθ, hpole]
  have hshift₀ :=
    shift_forward_of_refl ha hb' hc hG.riemann ((by norm_num only : (328 : ℝ) ≤ 787).trans hr₀.1)
      (by
        rw [mul_div_assoc, hscale]; exact hlevel)
      ht hpa hpb hpc hcost
      (gaussian_joint_to1000 hG.riemann
        ⟨(by norm_num only : (332.15 : ℝ) ≤ 787).trans hr₀.1, hr₀.2.le⟩)
  have hshift :
    P ≤
      (gaussianShiftedForward197 a r + gaussianShiftedForward197 b r +
          gaussianShiftedForward197 c r) +
        gaussianHalfCoeff197 * r := by
    linarith only [hshift₀]
  have hcond := hC r hra.1
  rw [hscale] at hcond
  have hmain :=
    gaussian_k197_principal_to1000 hG.riemann
      ⟨(by norm_num only : (663 / 2 : ℝ) ≤ 787).trans hr₀.1, hr₀.2.le⟩ hb
  have hcompare :=
    retained_comparison_of_gain ha hb' hc hp hq hk hG (C := 0)
      ((by norm_num only : (336.8 : ℝ) ≤ 787).trans hr₀.1) ∅ (Finset.empty_subset _)
      (fun n hn ↦ (Finset.notMem_empty n hn).elim) hlevel ht hpa hpb hpc (by rw [Finset.sum_empty])
  have hrF : r ∈ Set.Icc 328 1000 := ⟨(by norm_num only : (328 : ℝ) ≤ 787).trans hr₀.1, hr₀.2.le⟩
  refine
    mid_pair_false_with_abel (a := a) (b := b) (c := c) hG (B := -0.004 - B)
      ((by norm_num only : (336.8 : ℝ) ≤ 787).trans hr₀.1)
      (gaussian_abel_tail_through1000
        ⟨(by norm_num only : (336.8 : ℝ) ≤ 787).trans hr₀.1, hr₀.2.le⟩)
      hcond (k197_main_reflect_to1000 hrF) (gaussian_k197_reflect_credit_to1000 hrF) ht hpa hpb hpc
      hcompare ?_ hshift (wide_linear_lower (Real.log_natCast_nonneg n) hL hs₁ hm) ?_
  · simpa only [sub_eq_add_neg, add_assoc] using hmain
  · linarith only [hmargin]

private theorem witness_below1000 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {U s a T P C : ℝ}
    (hL : Real.log n ≤ U) (hm : k197Slope s ≤ 0) (ha₀ : (787 : ℝ) ≤ a)
    (hT : ∀ r : ℝ, a ≤ r → T ≤ gaussianTheta197 r) (hvs : 1.02 ≤ s)
    (hP : P ≤ T / s + 0.02074 - 0.00111)
    (hC : ∀ r : ℝ, a ≤ r → 4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ C)
    (hmargin :
      0 ≤
        (15.0472769 : ℝ) + (-0.004 - 0.29824) + P + k197Slope s * (U / 2) - 4 * 0.00683 - C -
            0.0012 +
          0.00082) :
    let r := s * Real.log n / 2
    r ∈ Set.Ico a 1000 →
      ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  intro r hr
  exact
    witness_below1000_of_boundary hn ho hu hG hL hm ha₀ hT hvs hP hC hmargin hr
      (sqrt_boundary_bound ⟨(by norm_num only : (521 : ℝ) ≤ 787).trans (ha₀.trans hr.1), hr.2⟩)

private theorem cell131_part0 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (6159 / 4) (6191 / 4)) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ ((127872781989 / 125000000000 : ℝ) * Real.log n / 2) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    witness_below1000 hn ho hu hG (s := 127872781989 / 125000000000) (a := 7875 / 10) (P :=
      -1.635453) hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from7875 (s := 1.02) hr le_rfl).1) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ (conductors_from7875 hr (by norm_num only)).2)
      (by norm_num only [k197Slope])
  exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩

private theorem cell131_part1 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (6191 / 4) (6223 / 4)) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ ((127872781989 / 125000000000 : ℝ) * Real.log n / 2) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    witness_below1000 hn ho hu hG (s := 127872781989 / 125000000000) (a := 7916 / 10) (P :=
      -1.629220) hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from7916 (s := 1.02) hr le_rfl).1) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ (conductors_from7916 hr (by norm_num only)).2)
      (by norm_num only [k197Slope])
  exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩

private theorem cell131_part2 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (6223 / 4) (6255 / 4)) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ ((127872781989 / 125000000000 : ℝ) * Real.log n / 2) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    witness_below1000 hn ho hu hG (s := 127872781989 / 125000000000) (a := 7957 / 10) (P :=
      -1.623040) hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from7957 (s := 1.02) hr le_rfl).1) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ (conductors_from7957 hr (by norm_num only)).2)
      (by norm_num only [k197Slope])
  exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩

private theorem cell131_part3 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (6255 / 4) (6287 / 4)) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ ((127872781989 / 125000000000 : ℝ) * Real.log n / 2) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    witness_below1000 hn ho hu hG (s := 127872781989 / 125000000000) (a := 7998 / 10) (P :=
      -1.616904) hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from7998 (s := 1.02) hr le_rfl).1) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ (conductors_from7998 hr (by norm_num only)).2)
      (by norm_num only [k197Slope])
  exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩

/-- Under GRH, an odd uniform Korselt triple in K197 cell 131 has a prime rejecting
base within the squared certified radius, using the square-root boundary bound. -/
theorem gaussian_k197_cell131_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (6159 / 4) (6287 / 4)) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ ((127872781989 / 125000000000 : ℝ) * Real.log n / 2) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases h0 : Real.log n ≤ 6191 / 4
  · exact cell131_part0 hn ho hu hG ⟨hL.1, h0⟩
  by_cases h1 : Real.log n ≤ 6223 / 4
  · exact cell131_part1 hn ho hu hG ⟨le_of_not_ge h0, h1⟩
  by_cases h2 : Real.log n ≤ 6255 / 4
  · exact cell131_part2 hn ho hu hG ⟨le_of_not_ge h1, h2⟩
  exact cell131_part3 hn ho hu hG ⟨le_of_not_ge h2, hL.2⟩

private theorem cell132_part0 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (6287 / 4) (6303 / 4)) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ ((25583284257 / 25000000000 : ℝ) * Real.log n / 2) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    witness_below1000 hn ho hu hG (s := 25583284257 / 25000000000) (a := 8042 / 10) (P := -1.609813)
      hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from8042 (s := 1.02) hr le_rfl).1) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ (conductors_from8042 hr (by norm_num only)).2)
      (by norm_num only [k197Slope])
  exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩

private theorem cell132_part1 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (6303 / 4) (6319 / 4)) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ ((25583284257 / 25000000000 : ℝ) * Real.log n / 2) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    witness_below1000 hn ho hu hG (s := 25583284257 / 25000000000) (a := 8062 / 10) (P := -1.606869)
      hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from8062 (s := 1.02) hr le_rfl).1) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ (conductors_from8062 hr (by norm_num only)).2)
      (by norm_num only [k197Slope])
  exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩

private theorem cell132_part2 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (6319 / 4) (6335 / 4)) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ ((25583284257 / 25000000000 : ℝ) * Real.log n / 2) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    witness_below1000 hn ho hu hG (s := 25583284257 / 25000000000) (a := 8083 / 10) (P := -1.603782)
      hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from8083 (s := 1.02) hr le_rfl).1) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ (conductors_from8083 hr (by norm_num only)).2)
      (by norm_num only [k197Slope])
  exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩

private theorem cell132_part3 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (6335 / 4) (6351 / 4)) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ ((25583284257 / 25000000000 : ℝ) * Real.log n / 2) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    witness_below1000 hn ho hu hG (s := 25583284257 / 25000000000) (a := 8103 / 10) (P := -1.600856)
      hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from8103 (s := 1.02) hr le_rfl).1) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ (conductors_from8103 hr (by norm_num only)).2)
      (by norm_num only [k197Slope])
  exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩

private theorem cell132_part4 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (6351 / 4) (6367 / 4)) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ ((25583284257 / 25000000000 : ℝ) * Real.log n / 2) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    witness_below1000 hn ho hu hG (s := 25583284257 / 25000000000) (a := 8123 / 10) (P := -1.597937)
      hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from8123 (s := 1.02) hr le_rfl).1) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ (conductors_from8123 hr (by norm_num only)).2)
      (by norm_num only [k197Slope])
  exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩

private theorem cell132_part5 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (6367 / 4) (6383 / 4)) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ ((25583284257 / 25000000000 : ℝ) * Real.log n / 2) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    witness_below1000 hn ho hu hG (s := 25583284257 / 25000000000) (a := 8144 / 10) (P := -1.594895)
      hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from8144 (s := 1.02) hr le_rfl).1) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ (conductors_from8144 hr (by norm_num only)).2)
      (by norm_num only [k197Slope])
  exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩

private theorem cell132_part6 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (6383 / 4) (6399 / 4)) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ ((25583284257 / 25000000000 : ℝ) * Real.log n / 2) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    witness_below1000 hn ho hu hG (s := 25583284257 / 25000000000) (a := 8164 / 10) (P := -1.591999)
      hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from8164 (s := 1.02) hr le_rfl).1) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ (conductors_from8164 hr (by norm_num only)).2)
      (by norm_num only [k197Slope])
  exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩

private theorem cell132_part7 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (6399 / 4) (6415 / 4)) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ ((25583284257 / 25000000000 : ℝ) * Real.log n / 2) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    witness_below1000 hn ho hu hG (s := 25583284257 / 25000000000) (a := 8185 / 10) (P := -1.588976)
      hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from8185 (s := 1.02) hr le_rfl).1) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ (conductors_from8185 hr (by norm_num only)).2)
      (by norm_num only [k197Slope])
  exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩

/-- Under GRH, an odd uniform Korselt triple in K197 cell 132 has a prime rejecting
base within the squared certified radius, using the square-root boundary bound. -/
theorem gaussian_k197_cell132_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (6287 / 4) (6415 / 4)) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ ((25583284257 / 25000000000 : ℝ) * Real.log n / 2) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases h0 : Real.log n ≤ 6303 / 4
  · exact cell132_part0 hn ho hu hG ⟨hL.1, h0⟩
  by_cases h1 : Real.log n ≤ 6319 / 4
  · exact cell132_part1 hn ho hu hG ⟨le_of_not_ge h0, h1⟩
  by_cases h2 : Real.log n ≤ 6335 / 4
  · exact cell132_part2 hn ho hu hG ⟨le_of_not_ge h1, h2⟩
  by_cases h3 : Real.log n ≤ 6351 / 4
  · exact cell132_part3 hn ho hu hG ⟨le_of_not_ge h2, h3⟩
  by_cases h4 : Real.log n ≤ 6367 / 4
  · exact cell132_part4 hn ho hu hG ⟨le_of_not_ge h3, h4⟩
  by_cases h5 : Real.log n ≤ 6383 / 4
  · exact cell132_part5 hn ho hu hG ⟨le_of_not_ge h4, h5⟩
  by_cases h6 : Real.log n ≤ 6399 / 4
  · exact cell132_part6 hn ho hu hG ⟨le_of_not_ge h5, h6⟩
  exact cell132_part7 hn ho hu hG ⟨le_of_not_ge h6, hL.2⟩

/-- Under GRH, a uniform Korselt triple with logarithm in compressed cell 133 has
a prime rejecting base within the squared certified radius by the signed boundary bound. -/
theorem gaussian_k197_cell133_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (6415 / 4) (6543 / 4)) :
    let r := (255916674363 / 250000000000 : ℝ) * Real.log n / 2
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    witness_below1000_of_boundary hn ho hu hG (s := 255916674363 / 250000000000) (B := 0.17214)
      (a := 8208 / 10) (P := -1.585144) hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from8208 (s := 1.02) hr le_rfl).1) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ (conductors_from8208 hr (by norm_num only)).2)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 673799) (B := 700957) (E := 379) (a := 8208 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell133 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple with logarithm in compressed cell 134 has
a prime rejecting base within the squared certified radius by the signed boundary bound. -/
theorem gaussian_k197_cell134_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (6543 / 4) (6671 / 4)) :
    let r := (511994526119 / 500000000000 : ℝ) * Real.log n / 2
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    witness_below1000_of_boundary hn ho hu hG (s := 511994526119 / 500000000000) (B := 0.12065)
      (a := 8374 / 10) (P := -1.561259) hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from8374 (s := 1.02) hr le_rfl).1) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ (conductors_from8374 hr (by norm_num only)).2)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 701397) (B := 729110) (E := 271) (a := 8374 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell134 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple with logarithm in compressed cell 135 has
a prime rejecting base within the squared certified radius by the signed boundary bound. -/
theorem gaussian_k197_cell135_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (6671 / 4) (6799 / 4)) :
    let r := (51214959321 / 50000000000 : ℝ) * Real.log n / 2
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    witness_below1000_of_boundary hn ho hu hG (s := 51214959321 / 50000000000) (B := 0.17983) (a :=
      8541 / 10) (P := -1.537971) hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from8541 (s := 1.02) hr le_rfl).1) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ (conductors_from8541 hr (by norm_num only)).2)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 729550) (B := 757816) (E := 412) (a := 8541 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell135 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple with logarithm in compressed cell 136 has
a prime rejecting base within the squared certified radius by the signed boundary bound. -/
theorem gaussian_k197_cell136_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (6799 / 4) (6927 / 4)) :
    let r := (512298897363 / 500000000000 : ℝ) * Real.log n / 2
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    witness_below1000_of_boundary hn ho hu hG (s := 512298897363 / 500000000000) (B := 0.16955)
      (a := 8707 / 10) (P := -1.515532) hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from8707 (s := 1.02) hr le_rfl).1) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ (conductors_from8707 hr (by norm_num only)).2)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 758257) (B := 787078) (E := 396) (a := 8707 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell136 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple with logarithm in compressed cell 137 has
a prime rejecting base within the squared certified radius by the signed boundary bound. -/
theorem gaussian_k197_cell137_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (6927 / 4) (7055 / 4)) :
    let r := (512442760071 / 500000000000 : ℝ) * Real.log n / 2
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    witness_below1000_of_boundary hn ho hu hG (s := 512442760071 / 500000000000) (B := 0.04327)
      (a := 8874 / 10) (P := -1.493643) hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from8874 (s := 1.02) hr le_rfl).1) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ (conductors_from8874 hr (by norm_num only)).2)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 787519) (B := 816893) (E := 103) (a := 8874 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell137 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple with logarithm in compressed cell 138 has
a prime rejecting base within the squared certified radius by the signed boundary bound. -/
theorem gaussian_k197_cell138_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (7055 / 4) (7183 / 4)) :
    let r := (256290739661 / 250000000000 : ℝ) * Real.log n / 2
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    witness_below1000_of_boundary hn ho hu hG (s := 256290739661 / 250000000000) (B := 0.06351)
      (a := 9040 / 10) (P := -1.472525) hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from9040 (s := 1.02) hr le_rfl).1) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ (conductors_from9040 hr (by norm_num only)).2)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 817334) (B := 847262) (E := 154) (a := 9040 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell138 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple with logarithm in compressed cell 139 has
a prime rejecting base within the squared certified radius by the signed boundary bound. -/
theorem gaussian_k197_cell139_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (7183 / 4) (7311 / 4)) :
    let r := (1025430663409 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    witness_below1000_of_boundary hn ho hu hG (s := 1025430663409 / 1000000000000) (B := 0.05629)
      (a := 9207 / 10) (P := -1.451908) hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from9207 (s := 1.02) hr le_rfl).1) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ (conductors_from9207 hr (by norm_num only)).2)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 847704) (B := 878186) (E := 139) (a := 9207 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell139 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple with logarithm in compressed cell 140 has
a prime rejecting base within the squared certified radius by the signed boundary bound. -/
theorem gaussian_k197_cell140_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (7311 / 4) (7439 / 4)) :
    let r := (256422287149 / 250000000000 : ℝ) * Real.log n / 2
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    witness_below1000_of_boundary hn ho hu hG (s := 256422287149 / 250000000000) (B := 0.04733)
      (a := 9373 / 10) (P := -1.431996) hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from9373 (s := 1.02) hr le_rfl).1) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ (conductors_from9373 hr (by norm_num only)).2)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 878628) (B := 909664) (E := 119) (a := 9373 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell140 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple with logarithm in compressed cell 141 has
a prime rejecting base within the squared certified radius by the signed boundary bound. -/
theorem gaussian_k197_cell141_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (7439 / 4) (7567 / 4)) :
    let r := (1025938892721 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    witness_below1000_of_boundary hn ho hu hG (s := 1025938892721 / 1000000000000) (B := 0) (a :=
      9539 / 10) (P := -1.412647) hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from9539 (s := 1.02) hr le_rfl).1) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ (conductors_from9539 hr (by norm_num only)).2)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 910106) (B := 941696) (E := 0) (a := 9539 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ by
          simpa only [neg_zero] using
            AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell141 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple with logarithm in compressed cell 142 has
a prime rejecting base within the squared certified radius by the signed boundary bound. -/
theorem gaussian_k197_cell142_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (7567 / 4) (7695 / 4)) :
    let r := (513090170847 / 500000000000 : ℝ) * Real.log n / 2
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    witness_below1000_of_boundary hn ho hu hG (s := 513090170847 / 500000000000) (B := 0.10448)
      (a := 9706 / 10) (P := -1.393731) hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from9706 (s := 1.02) hr le_rfl).1) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ (conductors_from9706 hr (by norm_num only)).2)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 942138) (B := 974282) (E := 272) (a := 9706 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell142 hx hy)
        (by norm_num only)

/-- Under GRH, a uniform Korselt triple with logarithm in compressed cell 143 has
a prime rejecting base within the squared certified radius by the signed boundary bound. -/
theorem gaussian_k197_cell143_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (7695 / 4) (7759 / 4)) :
    let r := (1026413911551 / 1000000000000 : ℝ) * Real.log n / 2
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    witness_below1000_of_boundary hn ho hu hG (s := 1026413911551 / 1000000000000) (B := 0.1824)
      (a := 9872 / 10) (P := -1.375441) hL.2 (by norm_num only [k197Slope]) (by norm_num only)
      (fun _ hr ↦ (conductors_from9872 (s := 1.02) hr le_rfl).1) (by norm_num only)
      (by norm_num only) (fun _ hr ↦ (conductors_from9872 hr (by norm_num only)).2)
      (by norm_num only [k197Slope])
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact
      local_boundary_of_cell (A := 974725) (B := 991007) (E := 483) (a := 9872 / 10)
        (by norm_num only) hL (by norm_num only) (by norm_num only) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
        (fun _ hx hy ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell143 hx hy)
        (by norm_num only)

end PseudoPrime.PrimeTestBounds.MillerRabin
