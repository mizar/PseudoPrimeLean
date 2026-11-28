/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Forward
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Kernel
import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticTripleConductors
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Forward
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131PsiBounds

/-! # The raw K131 comparison beyond the affine bridge -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Lee--Nosal bounds the lower principal boundary at every radius
whose square is at least 101. -/
theorem k131_raw_boundary_lower (hRH : RiemannHypothesis) {y : ℝ} (hy : 0 < y)
    (hx : (101 : ℝ) ≤ y ^ 2) :
    k131PrincipalError gaussianK131RhCoeff y ≤
      4 * (gaussianK131UnitWeight / y) * (Chebyshev.psi (y ^ 2) - y ^ 2) := by
  have h := AnalyticNumberTheory.Arithmetic.psi_lee_nosal_of_RH hRH hx
  rw [Real.sqrt_sq hy.le, Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  let N := (2 * Real.log y) * (2 * Real.log y - Real.log (2 * Real.log y))
  change |Chebyshev.psi (y ^ 2) - y ^ 2| / y ≤ N / (8 * Real.pi) at h
  have hN : 0 ≤ N := by
    have hw := (div_nonneg (abs_nonneg _) hy.le).trans h
    simpa only [zero_mul] using (le_div_iff₀ (mul_pos (by norm_num only) Real.pi_pos)).mp hw
  have hp : (314159 / 100000 : ℝ) ≤ Real.pi := by linarith only [Real.pi_gt_d20]
  have hb :=
    h.trans
      (div_le_div_of_nonneg_left hN (by norm_num only)
        (mul_le_mul_of_nonneg_left hp (by norm_num only)))
  have hlow : -(N / (8 * (314159 / 100000 : ℝ))) ≤ (Chebyshev.psi (y ^ 2) - y ^ 2) / y := by
    have h₁ := div_le_div_of_nonneg_right (neg_abs_le (Chebyshev.psi (y ^ 2) - y ^ 2)) hy.le
    rw [neg_div] at h₁
    exact (neg_le_neg hb).trans h₁
  have hm :=
    mul_le_mul_of_nonneg_left hlow (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4) unit_weight_nonneg)
  unfold k131PrincipalError gaussianK131RhCoeff
  change -(gaussianK131UnitWeight / (2 * (314159 / 100000))) * N ≤ _
  refine (le_of_eq ?_).trans (hm.trans_eq ?_)
  · ring
  · ring

/-- The three-character trace dominates the raw principal combination at
any positive radius, using only prime triviality on the tested prefix. -/
theorem k131_raw_trace_lower {y : ℝ} (hy : 0 < y) {p q r : ℕ} (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (ha : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ y ^ 2 → a l = 1)
    (hb : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ y ^ 2 → b l = 1)
    (hc : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ y ^ 2 → c l = 1) :
    let x := ⌊y ^ 2⌋₊
    let u := ⌊y ^ 2 * Real.exp (9 / 4)⌋₊
    let w := fun n : ℕ ↦ k131ForwardWeight y n * ArithmeticFunction.vonMangoldt n
    4 * (∑ n ∈ Finset.Icc 0 x, w n) - (∑ n ∈ Finset.Icc 0 u, w n) ≤
      ∑ n ∈ Finset.Icc 0 u, ((a n).re + (b n).re + (c n).re) * w n := by
  intro x u w
  have hxu : x ≤ u :=
    Nat.floor_mono (le_mul_of_one_le_right (sq_nonneg y) (Real.one_le_exp (by norm_num only)))
  have hpre :
    (∑ n ∈ Finset.Icc 0 x, ((a n).re + (b n).re + (c n).re) * w n) =
      3 * ∑ n ∈ Finset.Icc 0 x, w n := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
    · simp only [w, hΛ, mul_zero]
    have hn' := (Nat.le_floor_iff (sq_nonneg y)).mp (Finset.mem_Icc.mp hn).2
    rw [prefix_char_one a hn' hΛ ha, prefix_char_one b hn' hΛ hb, prefix_char_one c hn' hΛ hc,
      Complex.one_re]
    norm_num only
  have htail :
    -(∑ n ∈ Finset.Ioc x u, w n) ≤
      ∑ n ∈ Finset.Ioc x u, ((a n).re + (b n).re + (c n).re) * w n := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro n hn
    have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.zero_le x |>.trans_lt (Finset.mem_Ioc.mp hn).1)
    have hn₁ :=
      (Nat.le_floor_iff (mul_nonneg (sq_nonneg y) (Real.exp_pos _).le)).mp (Finset.mem_Ioc.mp hn).2
    simpa only [neg_one_mul] using
      mul_le_mul_of_nonneg_right (ht n)
        (mul_nonneg (forward_weight_nonneg hy hn₀ hn₁) ArithmeticFunction.vonMangoldt_nonneg)
  rw [sum_prefix_tail hxu w, sum_prefix_tail hxu, hpre]
  linarith only [htail]

/-- The raw K131 trace lower bound under RH uses the principal remainder
and holds throughout the range where the squared radius is at least 101. -/
theorem k131_raw_formula_lower (hRH : RiemannHypothesis) {y : ℝ} (hy : 1 < y) (hx : 101 ≤ y ^ 2)
    {p q r : ℕ} (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q)
    (c : DirichletCharacter ℂ r) (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (ha : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ y ^ 2 → a l = 1)
    (hb : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ y ^ 2 → b l = 1)
    (hc : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ y ^ 2 → c l = 1) :
    let z := 9 / 4 + 2 * Real.log y
    let P :=
      ((gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * (9 / 4))) * y ^ (-(27 / 8 : ℝ))
    let c₀ := Real.log (2 * Real.pi)
    k131PrincipalDelta * y + k131PrincipalError gaussianK131RhCoeff y +
          4 * (gaussianK131UnitWeight / y) * c₀ -
        3 * c₀ * P * gaussianK131InversePoly.eval z -
        25329 / 1000000 -
        k131PrincipalRem y ≤
      ∑ n ∈ Finset.Icc 0 ⌊y ^ 2 * Real.exp (9 / 4)⌋₊,
        ((a n).re + (b n).re + (c n).re) *
          (k131ForwardWeight y n * ArithmeticFunction.vonMangoldt n) := by
  intro z P c₀
  have hy₀ := zero_lt_one.trans hy
  have hp := k131_principal_formula_lower hRH hy
  have hψ := k131_raw_boundary_lower hRH hy₀ hx
  have htrace := k131_raw_trace_lower hy₀ a b c ht ha hb hc
  dsimp only at hp htrace
  dsimp only [z, P, c₀]
  linarith only [hp, hψ, htrace]

/-- At any radius meeting the reflected-tail support conditions, the raw
K131 Euler trace has the same upper comparison with zeros and Gamma. -/
theorem k131_raw_pair_euler_upper {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r] (hp : Odd p)
    (hq : Odd q) (hr : Odd r) (hpq : 2 ≤ p * q) (hpr : 2 ≤ p * r) (hqr : 2 ≤ q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 1 ≤ y)
    (hcut : (1250000 : ℝ) ≤ y ^ 2) (hz₀ : 16 ≤ 9 / 4 + Real.log (y ^ 2)) :
    let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
    let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
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
  intro a b c x z ha hb hc ha₁ hb₁ hc₁ hea heb hec hsmall
  have hx : 0 < x := pow_pos (zero_lt_one.trans_le hy) 2
  have hz : 14 ≤ z := (by norm_num only : (14 : ℝ) ≤ 16).trans hz₀
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
  have hlogN : 14 ≤ Real.log (1250000 : ℝ) := by
    apply (Real.le_log_iff_exp_le (by norm_num only)).2
    rw [show (14 : ℝ) = (14 : ℕ) * 1 by norm_num only, Real.exp_natCast_mul]
    exact
      (pow_le_pow_left₀ (Real.exp_pos 1).le
            (show Real.exp 1 ≤ (2719 / 1000 : ℝ) by linarith only [Real.exp_one_lt_d9]) 14).trans
        (by norm_num only)
  have hx₁ : 1 ≤ y ^ 2 := (by norm_num only : (1 : ℝ) ≤ 1250000).trans hcut
  have hR :=
    k131_pair_reflected_le_gamma hp hq hr hx₁ hz₀ (N := 1250000) (by decide)
      (by simpa only [Nat.cast_ofNat] using hlogN) ha hb hc ha₁ hb₁ hc₁
      (fun l hl hle ↦ hsmall l hl (hle.trans (by simpa only [Nat.cast_ofNat] using hcut)))
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
  dsimp only [x, z] at hA hB hC hR hGa hGb hGc hlog ⊢
  rw [hA, hB, hC, hlog, hlog, hlog]
  linarith only [hR, hGa, hGb, hGc]

/-- Prime triviality forces the three K131 pair-character zero sums to
dominate the raw principal comparison, with the exact conductor correction. -/
theorem k131_raw_pair_zero_lower {n p q r : ℕ} [NeZero p] [NeZero q] [NeZero r] (hn : n = p * q * r)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpq : 2 ≤ p * q) (hpr : 2 ≤ p * r) (hqr : 2 ≤ q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 1 < y)
    (hcut : (1250000 : ℝ) ≤ y ^ 2) (hz₀ : 16 ≤ 9 / 4 + Real.log (y ^ 2)) :
    let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
    let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
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
      k131PrincipalDelta * y + k131PrincipalError gaussianK131RhCoeff y +
                4 * (gaussianK131UnitWeight / y) * Real.log (2 * Real.pi) -
              25329 / 1000000 -
              k131PrincipalRem y +
            3 *
              (((gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * z)) *
                  k131CentralMoment (-(19 / 32 : ℝ)) z /
                2) -
          (2 * Real.log n - 6 + 3 * Real.log (2 * Real.pi)) * k131MellinProfile x⁻¹ ≤
        -(∑' ρ : ℂ, k131MellinKernel.oscillatingZeroTerm a x ρ).re -
          (∑' ρ : ℂ, k131MellinKernel.oscillatingZeroTerm b x ρ).re -
          (∑' ρ : ℂ, k131MellinKernel.oscillatingZeroTerm c x ρ).re := by
  intro a b c x z ha hb hc ha₁ hb₁ hc₁ hea heb hec hsmall
  have ht (k : ℕ) : -1 ≤ (a k).re + (b k).re + (c k).re := by
    simpa only [a, b, c, Int.cast_natCast] using
      pair_character_sum_ge_neg_one (k : ℤ) p q r (hp.mul hq) (hp.mul hr) (hq.mul hr)
  have h101 : (101 : ℝ) ≤ y ^ 2 := (by norm_num only : (101 : ℝ) ≤ 1250000).trans hcut
  have hlow :=
    k131_raw_formula_lower hGRH.riemann hy h101 a b c ht (fun l hl hle ↦ (hsmall l hl hle).1)
      (fun l hl hle ↦ (hsmall l hl hle).2.1) (fun l hl hle ↦ (hsmall l hl hle).2.2)
  have hhigh :=
    k131_raw_pair_euler_upper hp hq hr hpq hpr hqr hGRH hy.le hcut hz₀ ha hb hc ha₁ hb₁ hc₁ hea heb
      hec hsmall
  have hR := k131_conductor_profile hy.le
  have hlog := pair_level_log_sum hn
  rw [hlog] at hhigh
  simp only [gaussian_k131_inverse_eval] at hlow
  have hR' := congrArg (fun t : ℝ ↦ 3 * Real.log (2 * Real.pi) * t) hR
  dsimp only [x, z] at hhigh ⊢
  have h := hlow.trans hhigh
  dsimp only [a, b, c] at h ⊢
  nlinarith only [h, hR']

end PseudoPrime.PrimeTestBounds.MillerRabin
