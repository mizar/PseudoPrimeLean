/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Core
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Euler
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterShift663
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Euler
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerTail663

/-! # K197 comparison after recovery of known passing prime powers -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The signed Euler series splits into the common forward-minus-quadratic
part and the additional mixed cosine tail. All three series converge. -/
theorem gaussian_euler_split_197 {r : ℝ} (hr : 332.15 ≤ r) (d : ℕ → ℝ)
    (hd : ∀ n, d n ∈ Set.Icc 0 4) :
    let N := { n : ℕ // ⌊r ^ 2⌋₊ < n }
    let f := fun n : ℕ ↦
      if Real.log ((n : ℝ) / r ^ 2) ≤ 21 / 8 then quarterWeight656 (r ^ 2) n else 0
    let q := fun n : ℕ ↦ (n : ℝ) ^ (-(8 / 5) : ℝ) * quarterAuxProfile656 (Real.log n)
    (∑' n : N,
        ArithmeticFunction.vonMangoldt n.val *
          ((4 - d n.val) * f n.val - d n.val * gaussianDensity197 n.val)) =
      (∑' n : N,
          ArithmeticFunction.vonMangoldt n.val * ((4 - d n.val) * f n.val - d n.val * q n.val)) -
        (∑' n : N,
          d n.val * (ArithmeticFunction.vonMangoldt n.val / (n.val : ℝ) ^ (8 / 5 : ℝ)) *
            (gaussianProfile197 (Real.log n.val) - quarterAuxProfile656 (Real.log n.val))) := by
  intro N f q
  let g := fun n : ℕ ↦
    ArithmeticFunction.vonMangoldt n * ((4 - d n) * f n - d n * gaussianDensity197 n)
  let k := fun n : ℕ ↦ d n * (ArithmeticFunction.vonMangoldt n * (gaussianDensity197 n - q n))
  have hg : Summable g := common_tail_summable hr d hd
  have hb :
    Summable (fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * (gaussianDensity197 n - q n)) := by
    simpa only [mul_sub] using gaussian_profile_summable_197.sub q_summable
  have hk : Summable k := by
    apply Summable.of_norm_bounded (hb.norm.mul_left 4)
    intro n
    simp only [k, norm_mul, Real.norm_of_nonneg (hd n).1]
    exact mul_le_mul_of_nonneg_right (hd n).2 (by positivity)
  have hs := (hg.subtype (fun n ↦ ⌊r ^ 2⌋₊ < n)).tsum_add (hk.subtype (fun n ↦ ⌊r ^ 2⌋₊ < n))
  change (∑' n : N, (g n.val + k n.val)) = (∑' n : N, g n.val) + (∑' n : N, k n.val) at hs
  have h₁ (n : N) :
    g n.val + k n.val =
      ArithmeticFunction.vonMangoldt n.val * ((4 - d n.val) * f n.val - d n.val * q n.val) := by
    dsimp only [g, k]
    ring
  have h₂ (n : N) :
    k n.val =
      d n.val * (ArithmeticFunction.vonMangoldt n.val / (n.val : ℝ) ^ (8 / 5 : ℝ)) *
        (gaussianProfile197 (Real.log n.val) - quarterAuxProfile656 (Real.log n.val)) := by
    simp only [k, q, gaussianDensity197, Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv]
    ring
  simp only [h₁] at hs
  simp only [h₂] at hs
  change (∑' n : N, g n.val) = _
  linarith only [hs]

/-- Join the K197 forward Gram inequality to the retained arithmetic
terms and cancel the common mixed Euler tail. -/
theorem gaussian_recovered_prefix_197 {p q k : ℕ} [NeZero p] [NeZero q] [NeZero k]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ k}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hk : 2 ≤ k)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r t : ℝ} (hr : 332.15 ≤ r)
    (hL : Real.log p + Real.log q + Real.log k = 4 * t)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hpa : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → a n = 1)
    (hpb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → b n = 1)
    (hpc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → c n = 1) (K : Finset ℕ)
    (hK : ∀ n ∈ K, r ^ 2 < (n : ℝ)) (hU : ∀ n ∈ K, Real.log ((n : ℝ) / r ^ 2) ≤ 21 / 8)
    (hpass : ∀ n ∈ K, 3 - ((a n).re + (b n).re + (c n).re) = 0) :
    let d := fun n : ℕ ↦ 3 - ((a n).re + (b n).re + (c n).re)
    let W := fun n ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) n).re
    let Q := fun n : ℕ ↦ (n : ℝ) ^ (-(8 / 5) : ℝ) * quarterAuxProfile656 (Real.log n)
    let T :=
      (∫ x in Set.Ioi (r ^ 2), gaussianDensity197 x) -
          (Chebyshev.psi (r ^ 2) - r ^ 2) * gaussianDensity197 (r ^ 2) +
        gaussianAbelError197 (r ^ 2)
    4 * (∑ n ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊, W n) +
            (gaussianShiftedForward197 a r + gaussianShiftedForward197 b r +
              gaussianShiftedForward197 c r) +
            (4.125607 - 4 * T) +
            (∑ n ∈ K, 4 * (ArithmeticFunction.vonMangoldt n * quarterWeight656 (r ^ 2) n)) -
          (∑ n ∈ K, 8 * (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(8 / 5) : ℝ))) +
        (∑' n : { n : ℕ // ⌊r ^ 2⌋₊ < n },
          d n.val * (ArithmeticFunction.vonMangoldt n.val * Q n.val)) ≤
      quarterCosineContour656 a 0 + quarterCosineContour656 b 0 + quarterCosineContour656 c 0 +
        ((contourRemainder656 a (r ^ 2)).re + (contourRemainder656 b (r ^ 2)).re +
          (contourRemainder656 c (r ^ 2)).re) +
        gaussianAuxMix197 quarterConductorProfile663 * t +
        (∑' n, W n) := by
  intro d W Q T
  have hr' : (328 : ℝ) ≤ r := (by norm_num only : (328 : ℝ) ≤ 332.15).trans hr
  have hx : 0 < r ^ 2 := sq_pos_of_pos ((by norm_num only : (0 : ℝ) < 328).trans_le hr')
  have hd (n : ℕ) : d n ∈ Set.Icc 0 4 :=
    ⟨sub_nonneg.mpr (ht n).2, by
      dsimp only [d]; linarith only [(ht n).1]⟩
  have he := gaussian_euler_abel_197 hG.riemann hr d hd K hK hpass
  dsimp only at he
  have hf (n : ℕ) (hn : n ∈ K) :
    (if Real.log ((n : ℝ) / r ^ 2) ≤ 21 / 8 then quarterWeight656 (r ^ 2) n else 0) =
      quarterWeight656 (r ^ 2) n :=
    ite_eq_left (hU n hn)
  have hsum :
    (∑ n ∈ K,
        4 *
          (ArithmeticFunction.vonMangoldt n *
            (if Real.log ((n : ℝ) / r ^ 2) ≤ 21 / 8 then quarterWeight656 (r ^ 2) n else 0))) =
      ∑ n ∈ K, 4 * (ArithmeticFunction.vonMangoldt n * quarterWeight656 (r ^ 2) n) :=
    Finset.sum_congr rfl (fun n hn ↦ by rw [hf n hn])
  rw [hsum, ←
    tsum_above_eq (common_tail_summable hr d hd)
      (by simp only [ArithmeticFunction.map_zero, zero_mul])] at he
  rw [gaussian_euler_split_197 hr d hd, quarter_forward_quadratic_split_663 hx d hd] at he
  have hprefix := quarter_forward_prefix_663 a b c hx ht hpa hpb hpc
  have hgram := gaussian_scaled_forward_197 ha hb hc hp hq hk hG hr' hL hpa hpb hpc
  dsimp only [d, W, Q, T] at he hprefix ⊢
  linarith only [he, hprefix, hgram]

/-- Expand the principal contours after Euler cancellation and retain
the explicit K197 tail and prime-power charges. -/
theorem gaussian_comparison_upper_197 {p q k : ℕ} [NeZero p] [NeZero q] [NeZero k]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ k}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hk : 2 ≤ k)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r t : ℝ} (hr : 332.15 ≤ r)
    (hL : Real.log p + Real.log q + Real.log k = 4 * t)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hpa : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → a n = 1)
    (hpb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → b n = 1)
    (hpc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → c n = 1) (K : Finset ℕ)
    (hK : ∀ n ∈ K, r ^ 2 < (n : ℝ)) (hU : ∀ n ∈ K, Real.log ((n : ℝ) / r ^ 2) ≤ 21 / 8)
    (hpass : ∀ n ∈ K, 3 - ((a n).re + (b n).re + (c n).re) = 0) :
    let x := r ^ 2
    let W := fun n ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) x n).re
    let R := (quarterKernel656.transform x⁻¹).re
    let T :=
      (∫ z in Set.Ioi x, gaussianDensity197 z) - (Chebyshev.psi x - x) * gaussianDensity197 x +
        gaussianAbelError197 x
    4 * (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, W n) - (∑' n, W n) +
          (∑ n ∈ K, 4 * (ArithmeticFunction.vonMangoldt n * quarterWeight656 x n)) +
          (gaussianShiftedForward197 a r + gaussianShiftedForward197 b r +
            gaussianShiftedForward197 c r) +
          (15.0475739 - 4 * T) -
        (∑ n ∈ K, 8 * (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(8 / 5) : ℝ))) ≤
      (3 / 4 + gaussianAuxMix197 quarterConductorProfile663) * t + 4 * t * R +
          3 * (centralGammaPair656 (1 : DirichletCharacter ℂ 1) x).re -
        (quarterMainEuler656 a x + quarterMainEuler656 b x + quarterMainEuler656 c x) := by
  intro x W R T
  have hr₁ : (1 : ℝ) ≤ r := (by norm_num only : (1 : ℝ) ≤ 332.15).trans hr
  have hx : 1 ≤ x := one_le_pow₀ hr₁
  have hx₀ := zero_lt_one.trans_le hx
  have he := quarter_three_cosine_split_656 ha hb hc (sq_nonneg r) 0 hpa hpb hpc
  rw [hL, quarter_cosine_zero_tail_663 a b c hx, abs_zero] at he
  have h := gaussian_recovered_prefix_197 ha hb hc hp hq hk hG hr hL ht hpa hpb hpc K hK hU hpass
  have hm := quarter_cosine_zero_cap_663 hG.riemann t
  have hR : Analysis.rationalPoleProfile 3 (5 / 11) (21 / 16) x⁻¹ = R := by
    dsimp only [R]
    rw [quarterKernel656, LLS.PaperStatements.rationalPole_transform _ _ _ _ (inv_pos.mpr hx₀),
      Complex.ofReal_re]
  have hCa := quarter_main_arch_split_656 ha.1 ha.2.1 ha.2.2.1 hx₀
  have hCb := quarter_main_arch_split_656 hb.1 hb.2.1 hb.2.2.1 hx₀
  have hCc := quarter_main_arch_split_656 hc.1 hc.2.1 hc.2.2.1 hx₀
  rw [hR, quarter_even_level_gamma_656 a ha.2.1 ha.2.2.2, quarter_level_gamma_central_656 hx] at hCa
  rw [hR, quarter_even_level_gamma_656 b hb.2.1 hb.2.2.2, quarter_level_gamma_central_656 hx] at hCb
  rw [hR, quarter_even_level_gamma_656 c hc.2.1 hc.2.2.2, quarter_level_gamma_central_656 hx] at hCc
  have hcond := congrArg (fun u : ℝ ↦ u * R) hL
  ring_nf at hcond
  dsimp only [x, W, R, T] at h he hCa hCb hCc hcond ⊢
  linarith only [h, he, hm, hCa, hCb, hCc, hcond, quarter_mass_constant_656]

/-- Join the K197 forward Gram inequality to the retained arithmetic
terms and cancel the common mixed Euler tail. -/
theorem gaussian_signed_prefix_197 {p q k : ℕ} [NeZero p] [NeZero q] [NeZero k]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ k}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hk : 2 ≤ k)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r t : ℝ} (hr : 332.15 ≤ r)
    (hL : Real.log p + Real.log q + Real.log k = 4 * t)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hpa : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → a n = 1)
    (hpb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → b n = 1)
    (hpc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → c n = 1) (K : Finset ℕ)
    (hK : ∀ n ∈ K, r ^ 2 < (n : ℝ)) (hpass : ∀ n ∈ K, 3 - ((a n).re + (b n).re + (c n).re) = 0) :
    let d := fun n : ℕ ↦ 3 - ((a n).re + (b n).re + (c n).re)
    let W := fun n ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) n).re
    let Q := fun n : ℕ ↦ (n : ℝ) ^ (-(8 / 5) : ℝ) * quarterAuxProfile656 (Real.log n)
    let F := fun n : ℕ ↦
      if Real.log ((n : ℝ) / r ^ 2) ≤ 21 / 8 then quarterWeight656 (r ^ 2) n else 0
    let T :=
      (∫ x in Set.Ioi (r ^ 2), gaussianDensity197 x) -
          (Chebyshev.psi (r ^ 2) - r ^ 2) * gaussianDensity197 (r ^ 2) +
        gaussianAbelError197 (r ^ 2)
    4 * (∑ n ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊, W n) +
        (gaussianShiftedForward197 a r + gaussianShiftedForward197 b r +
          gaussianShiftedForward197 c r) +
        (4.125607 - 4 * T) +
        (∑ n ∈ K, 4 * (ArithmeticFunction.vonMangoldt n * (F n + gaussianDensity197 n))) +
        (∑' n : { n : ℕ // ⌊r ^ 2⌋₊ < n },
          d n.val * (ArithmeticFunction.vonMangoldt n.val * Q n.val)) ≤
      quarterCosineContour656 a 0 + quarterCosineContour656 b 0 + quarterCosineContour656 c 0 +
        ((contourRemainder656 a (r ^ 2)).re + (contourRemainder656 b (r ^ 2)).re +
          (contourRemainder656 c (r ^ 2)).re) +
        gaussianAuxMix197 quarterConductorProfile663 * t +
        (∑' n, W n) := by
  intro d W Q F T
  have hr' : (328 : ℝ) ≤ r := (by norm_num only : (328 : ℝ) ≤ 332.15).trans hr
  have hx : 0 < r ^ 2 := sq_pos_of_pos ((by norm_num only : (0 : ℝ) < 328).trans_le hr')
  have hd (n : ℕ) : d n ∈ Set.Icc 0 4 :=
    ⟨sub_nonneg.mpr (ht n).2, by
      dsimp only [d]; linarith only [(ht n).1]⟩
  have he := gaussian_euler_abel_signed_197 hG.riemann hr d hd K hK hpass
  dsimp only at he
  rw [←
    tsum_above_eq (common_tail_summable hr d hd)
      (by simp only [ArithmeticFunction.map_zero, zero_mul])] at he
  rw [gaussian_euler_split_197 hr d hd, quarter_forward_quadratic_split_663 hx d hd] at he
  have hprefix := quarter_forward_prefix_663 a b c hx ht hpa hpb hpc
  have hgram := gaussian_scaled_forward_197 ha hb hc hp hq hk hG hr' hL hpa hpb hpc
  dsimp only [d, W, Q, F, T] at he hprefix ⊢
  linarith only [he, hprefix, hgram]

/-- Expand the principal contours after Euler cancellation and retain
the full signed contribution of the passing K197 atoms. -/
theorem gaussian_comparison_signed_197 {p q k : ℕ} [NeZero p] [NeZero q] [NeZero k]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ k}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hk : 2 ≤ k)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r t : ℝ} (hr : 332.15 ≤ r)
    (hL : Real.log p + Real.log q + Real.log k = 4 * t)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hpa : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → a n = 1)
    (hpb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → b n = 1)
    (hpc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → c n = 1) (K : Finset ℕ)
    (hK : ∀ n ∈ K, r ^ 2 < (n : ℝ)) (hpass : ∀ n ∈ K, 3 - ((a n).re + (b n).re + (c n).re) = 0) :
    let x := r ^ 2
    let W := fun n ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) x n).re
    let R := (quarterKernel656.transform x⁻¹).re
    let F := fun n : ℕ ↦
      if Real.log ((n : ℝ) / r ^ 2) ≤ 21 / 8 then quarterWeight656 (r ^ 2) n else 0
    let T :=
      (∫ z in Set.Ioi x, gaussianDensity197 z) - (Chebyshev.psi x - x) * gaussianDensity197 x +
        gaussianAbelError197 x
    4 * (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, W n) - (∑' n, W n) +
        (∑ n ∈ K, 4 * (ArithmeticFunction.vonMangoldt n * (F n + gaussianDensity197 n))) +
        (gaussianShiftedForward197 a r + gaussianShiftedForward197 b r +
          gaussianShiftedForward197 c r) +
        (15.0475739 - 4 * T) ≤
      (3 / 4 + gaussianAuxMix197 quarterConductorProfile663) * t + 4 * t * R +
          3 * (centralGammaPair656 (1 : DirichletCharacter ℂ 1) x).re -
        (quarterMainEuler656 a x + quarterMainEuler656 b x + quarterMainEuler656 c x) := by
  intro x W R F T
  have hr₁ : (1 : ℝ) ≤ r := (by norm_num only : (1 : ℝ) ≤ 332.15).trans hr
  have hx : 1 ≤ x := one_le_pow₀ hr₁
  have hx₀ := zero_lt_one.trans_le hx
  have he := quarter_three_cosine_split_656 ha hb hc (sq_nonneg r) 0 hpa hpb hpc
  rw [hL, quarter_cosine_zero_tail_663 a b c hx, abs_zero] at he
  have h := gaussian_signed_prefix_197 ha hb hc hp hq hk hG hr hL ht hpa hpb hpc K hK hpass
  have hm := quarter_cosine_zero_cap_663 hG.riemann t
  have hR : Analysis.rationalPoleProfile 3 (5 / 11) (21 / 16) x⁻¹ = R := by
    dsimp only [R]
    rw [quarterKernel656, LLS.PaperStatements.rationalPole_transform _ _ _ _ (inv_pos.mpr hx₀),
      Complex.ofReal_re]
  have hCa := quarter_main_arch_split_656 ha.1 ha.2.1 ha.2.2.1 hx₀
  have hCb := quarter_main_arch_split_656 hb.1 hb.2.1 hb.2.2.1 hx₀
  have hCc := quarter_main_arch_split_656 hc.1 hc.2.1 hc.2.2.1 hx₀
  rw [hR, quarter_even_level_gamma_656 a ha.2.1 ha.2.2.2, quarter_level_gamma_central_656 hx] at hCa
  rw [hR, quarter_even_level_gamma_656 b hb.2.1 hb.2.2.2, quarter_level_gamma_central_656 hx] at hCb
  rw [hR, quarter_even_level_gamma_656 c hc.2.1 hc.2.2.2, quarter_level_gamma_central_656 hx] at hCc
  have hcond := congrArg (fun u : ℝ ↦ u * R) hL
  ring_nf at hcond
  dsimp only [x, W, R, F, T] at h he hCa hCb hCc hcond ⊢
  linarith only [h, he, hm, hCa, hCb, hCc, hcond, quarter_mass_constant_656]

/-- For retained prime powers on the early radius window, charge at
most 0.000297 for their reflected part in the K197 comparison. -/
theorem gaussian_power_comparison_197 {p q k : ℕ} [NeZero p] [NeZero q] [NeZero k]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ k}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hk : 2 ≤ k)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r t : ℝ}
    (hr : r ∈ Set.Icc 332.15 337) (hL : Real.log p + Real.log q + Real.log k = 4 * t)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hpa : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → a n = 1)
    (hpb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → b n = 1)
    (hpc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → c n = 1) (K : Finset ℕ)
    (hK : ∀ n ∈ K, r ^ 2 < (n : ℝ)) (hU : ∀ n ∈ K, Real.log ((n : ℝ) / r ^ 2) ≤ 21 / 8)
    (hpow : ∀ n ∈ K, ∃ l j : ℕ, l.Prime ∧ 2 ≤ j ∧ n = l ^ j) :
    let x := r ^ 2
    let W := fun n ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) x n).re
    let R := (quarterKernel656.transform x⁻¹).re
    let T :=
      (∫ z in Set.Ioi x, gaussianDensity197 z) - (Chebyshev.psi x - x) * gaussianDensity197 x +
        gaussianAbelError197 x
    4 * (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, W n) - (∑' n, W n) +
        (∑ n ∈ K, 4 * (ArithmeticFunction.vonMangoldt n * quarterWeight656 x n)) +
        (gaussianShiftedForward197 a r + gaussianShiftedForward197 b r +
          gaussianShiftedForward197 c r) +
        (15.0472769 - 4 * T) ≤
      (3 / 4 + gaussianAuxMix197 quarterConductorProfile663) * t + 4 * t * R +
          3 * (centralGammaPair656 (1 : DirichletCharacter ℂ 1) x).re -
        (quarterMainEuler656 a x + quarterMainEuler656 b x + quarterMainEuler656 c x) := by
  have hr' : r ∈ Set.Icc 328 337 := ⟨(by norm_num only : (328 : ℝ) ≤ 332.15).trans hr.1, hr.2⟩
  obtain ⟨hpass, hcost⟩ := quarter_retained_window_663 a b c hr' hpa hpb hpc K hK hU hpow
  have h := gaussian_comparison_upper_197 ha hb hc hp hq hk hG hr.1 hL ht hpa hpb hpc K hK hU hpass
  have hcost' :
    (∑ n ∈ K, 8 * (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(8 / 5) : ℝ))) ≤ 0.000297 := by
    rw [← Finset.mul_sum] at hcost ⊢
    linarith only [hcost]
  dsimp only at h ⊢
  linarith only [h, hcost']

/-- Evaluate the signed comparison on retained powers whose prime bases are
within the witness cutoff. The powers themselves may exceed the forward support. -/
theorem gaussian_prime_power_signed_197 {p q k : ℕ} [NeZero p] [NeZero q] [NeZero k]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ k}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hk : 2 ≤ k)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r t : ℝ} (hr : 332.15 ≤ r)
    (hL : Real.log p + Real.log q + Real.log k = 4 * t)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hpa : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → a n = 1)
    (hpb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → b n = 1)
    (hpc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → c n = 1) (K : Finset ℕ)
    (hK : ∀ n ∈ K, r ^ 2 < (n : ℝ))
    (hpow : ∀ n ∈ K, ∃ l j : ℕ, l.Prime ∧ (l : ℝ) ≤ r ^ 2 ∧ n = l ^ j) :
    let x := r ^ 2
    let W := fun n ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) x n).re
    let R := (quarterKernel656.transform x⁻¹).re
    let F := fun n : ℕ ↦
      if Real.log ((n : ℝ) / r ^ 2) ≤ 21 / 8 then quarterWeight656 (r ^ 2) n else 0
    let T :=
      (∫ z in Set.Ioi x, gaussianDensity197 z) - (Chebyshev.psi x - x) * gaussianDensity197 x +
        gaussianAbelError197 x
    4 * (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, W n) - (∑' n, W n) +
        (∑ n ∈ K, 4 * (ArithmeticFunction.vonMangoldt n * (F n + gaussianDensity197 n))) +
        (gaussianShiftedForward197 a r + gaussianShiftedForward197 b r +
          gaussianShiftedForward197 c r) +
        (15.0475739 - 4 * T) ≤
      (3 / 4 + gaussianAuxMix197 quarterConductorProfile663) * t + 4 * t * R +
          3 * (centralGammaPair656 (1 : DirichletCharacter ℂ 1) x).re -
        (quarterMainEuler656 a x + quarterMainEuler656 b x + quarterMainEuler656 c x) := by
  apply gaussian_comparison_signed_197 ha hb hc hp hq hk hG hr hL ht hpa hpb hpc K hK
  intro n hn
  obtain ⟨l, j, hl, hcut, rfl⟩ := hpow n hn
  have hpowers {m : ℕ} (χ : DirichletCharacter ℂ m) (hχ : χ l = 1) : χ (↑(l ^ j) : ZMod m) = 1 := by
    rw [Nat.cast_pow, map_pow, hχ, one_pow]
  rw [hpowers a (hpa l hl hcut), hpowers b (hpb l hl hcut), hpowers c (hpc l hl hcut),
    Complex.one_re]
  norm_num only

end PseudoPrime.PrimeTestBounds.MillerRabin
