/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterGammaCentral656

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerTail663
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterReflectBox663
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMainXi656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterThetaPoly663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterForward663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterProfile663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAuxSlope663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosineSeries656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAuxEuler656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosineSplit656

/-! # Shifted contour expansion at the six section 137 frequencies -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The signed zeta zero contribution at the six shifted scales. -/
noncomputable def quarterMainXiMix663 (r : ℝ) : ℝ :=
  ∑ i,
    (quarterCoeff663 i : ℝ) *
      (∑' ρ,
          quarterKernel656.zetaOscillatingZeroTerm (r ^ 2 * Real.exp (-(quarterFreq663 i : ℝ)))
            ρ).re

/-- Under RH, expand the six shifted remainders at radius `r` and total
log conductor `4 * r / scale`. Only the conductor term is divided by the scale. -/
theorem quarter_scaled_shift_mix_663 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ s}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hRH : RiemannHypothesis) {r scale : ℝ}
    (hr : 328 ≤ r) (hL : Real.log p + Real.log q + Real.log s = 4 * r / scale) :
    (quarterShiftedForward663 a r + quarterShiftedForward663 b r + quarterShiftedForward663 c r) +
        quarterAuxHalfCoeff663 * r =
      quarterAuxTheta663 r / scale + quarterAuxNegPole663 / r + 3 * quarterMainXiMix663 r +
        ∑ i,
          (quarterCoeff663 i : ℝ) *
            quarterAuxReflection656 (fun n ↦ 3 - ((a n).re + (b n).re + (c n).re)) r
              (quarterShift663 i : ℝ) := by
  let x := fun i ↦ r ^ 2 * Real.exp (-((quarterFreq663 i : ℝ)))
  let P := fun (t : ℝ) (i : Fin 6) ↦ (quarterKernel656.function (t : ℂ) * (x i : ℂ) ^ (t : ℂ)).re
  let Z := fun i ↦ (∑' ρ, quarterKernel656.zetaOscillatingZeroTerm (x i) ρ).re
  let T := fun i ↦
    quarterAuxReflection656 (fun n ↦ 3 - ((a n).re + (b n).re + (c n).re)) r (quarterShift663 i : ℝ)
  let A := fun i ↦ (4 * r * (quarterKernel656.transform (x i)⁻¹).re) / scale - 3 * P (-1 / 2) i
  let S := fun (i : Fin 6) ↦
    (∑' n, quarterKernel656.summand (1 : DirichletCharacter ℂ 1) (x i) n).re
  have hr₀ := (by norm_num only : (0 : ℝ) < 328).trans_le hr
  have hx (i : Fin 6) : 1 ≤ x i := quarter_aux_scale_ge_one_663 hr i
  have hs (i : Fin 6) :
    (contourRemainder656 a (x i)).re - S i + P (1 / 2) i +
        ((contourRemainder656 b (x i)).re - S i + P (1 / 2) i) +
        ((contourRemainder656 c (x i)).re - S i + P (1 / 2) i) =
      A i + 3 * Z i + T i := by
    have he : 21 / 8 + (quarterShift663 i : ℝ) = (quarterFreq663 i : ℝ) := by
      simp only [quarterShift663, Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat]
      ring
    have h :=
      quarter_shifted_forward_diff_656 ha hb hc hRH hr₀ (h := (quarterShift663 i : ℝ))
        (by simpa only [he, x] using hx i)
    simp only [he] at h
    have hp :
      (quarterKernel656.transform (x i)⁻¹).re =
        Analysis.rationalPoleProfile 3 (5 / 11) (21 / 16) (x i)⁻¹ := by
      rw [quarterKernel656,
        LLS.PaperStatements.rationalPole_transform _ _ _ _
          (inv_pos.mpr (zero_lt_one.trans_le (hx i))),
        Complex.ofReal_re]
    simp only [hL, Complex.sub_re] at h
    dsimp only [A, P, Z, S, T, x] at h hp ⊢
    rw [hp]
    linear_combination h
  have hA :
    (∑ i, (quarterCoeff663 i : ℝ) * A i) =
      quarterAuxTheta663 r / scale + quarterAuxNegPole663 / r := by
    have ht := quarter_aux_theta_sum_663 hr
    have hp := quarter_aux_neg_pole_sum_663 hr₀
    dsimp only [A, P, x]
    simp only [mul_sub, Finset.sum_sub_distrib, ← mul_div_assoc,
      mul_left_comm (quarterCoeff663 _ : ℝ) 3, ← Finset.mul_sum]
    rw [← Finset.sum_div, ht]
    linarith only [hp]
  rw [← hA]
  rw [← quarter_aux_half_pole_sum_663 hr₀]
  unfold quarterShiftedForward663 quarterMainXiMix663
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hp : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by
    norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  rw [← hp]
  change
    (quarterCoeff663 i : ℝ) * ((contourRemainder656 a (x i)).re - S i) +
        (quarterCoeff663 i : ℝ) * ((contourRemainder656 b (x i)).re - S i) +
        (quarterCoeff663 i : ℝ) * ((contourRemainder656 c (x i)).re - S i) +
        3 * ((quarterCoeff663 i : ℝ) * P (1 / 2) i) =
      (quarterCoeff663 i : ℝ) * A i + 3 * ((quarterCoeff663 i : ℝ) * Z i) +
        (quarterCoeff663 i : ℝ) * T i
  linear_combination (quarterCoeff663 i : ℝ) * hs i

/-- At scale one, the shifted expansion uses total log conductor four
times the radius, as in the quarter-square comparison. -/
theorem quarter_shift_mix_663 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ s}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hRH : RiemannHypothesis) {r : ℝ} (hr : 328 ≤ r)
    (hL : Real.log p + Real.log q + Real.log s = 4 * r) :
    (quarterShiftedForward663 a r + quarterShiftedForward663 b r + quarterShiftedForward663 c r) +
        quarterAuxHalfCoeff663 * r =
      quarterAuxTheta663 r + quarterAuxNegPole663 / r + 3 * quarterMainXiMix663 r +
        ∑ i,
          (quarterCoeff663 i : ℝ) *
            quarterAuxReflection656 (fun n ↦ 3 - ((a n).re + (b n).re + (c n).re)) r
              (quarterShift663 i : ℝ) := by
  simpa only [div_one] using
    quarter_scaled_shift_mix_663 ha hb hc hRH hr (scale := 1) (by simpa only [div_one] using hL)

/-- The shifted zeta zero terms cost at most nine millionths after
summing the six terms for three characters. -/
theorem quarter_shift_xi_cap_663 (hRH : RiemannHypothesis) {r : ℝ} (hr : 328 ≤ r) :
    |3 * quarterMainXiMix663 r| ≤ 0.000009 := by
  let f := fun i : Fin 6 ↦
    (∑' ρ,
        quarterKernel656.zetaOscillatingZeroTerm (r ^ 2 * Real.exp (-(quarterFreq663 i : ℝ))) ρ).re
  have hf (i : Fin 6) := quarter_main_zero_abs_656 hRH (quarter_aux_scale_ge_one_663 hr i)
  have h :=
    sum_six_error (fun i ↦ (quarterCoeff663 i : ℝ) * f i) (fun _ ↦ 0)
      (fun i ↦ by
        simpa only [mul_zero] using
          weighted_error i (b := 0) (by simpa only [f, sub_zero] using hf i))
  simp only [Finset.sum_const_zero, sub_zero] at h
  rw [abs_mul, abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 3)]
  unfold quarterMainXiMix663
  linarith only [h]

/-- At the section 137 radii, the shifted comparison including the
linear deficit and the zeta zero contribution has a fixed lower bound. -/
theorem quarter_shift_forward_lower_663 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ s}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hRH : RiemannHypothesis) {r : ℝ}
    (hr : r ∈ Set.Icc 328 (663 / 2)) (hL : Real.log p + Real.log q + Real.log s = 4 * r)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hpa : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → a n = 1)
    (hpb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → b n = 1)
    (hpc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → c n = 1) :
    -13.054763 + 0.0219746789 * (663 / 2 - r) ≤
      -(3 / 4 - 0.71780481) * r - quarterAuxMix663 quarterConductorProfile663 * r +
        (quarterShiftedForward663 a r + quarterShiftedForward663 b r +
          quarterShiftedForward663 c r) := by
  let d := fun n : ℕ ↦ 3 - ((a n).re + (b n).re + (c n).re)
  have hd (n : ℕ) : 0 ≤ d n ∧ d n ≤ 4 :=
    ⟨sub_nonneg.mpr (ht n).2, by
      dsimp only [d]; linarith only [(ht n).1]⟩
  have hp (n : ℕ) (hn : n ∈ Finset.Ioc 0 103684) (hΛ : ArithmeticFunction.vonMangoldt n ≠ 0) :
    d n = 0 := by
    have hn' : (n : ℝ) ≤ 103684 := by exact_mod_cast (Finset.mem_Ioc.mp hn).2
    have hx :=
      hn'.trans
        ((by norm_num only : (103684 : ℝ) ≤ 328 ^ 2).trans
          (pow_le_pow_left₀ (by norm_num only) hr.1 2))
    simp only [d,
      AnalyticNumberTheory.Arithmetic.character_apply_one_of_mangoldt_ne_zero a hpa hx hΛ,
      AnalyticNumberTheory.Arithmetic.character_apply_one_of_mangoldt_ne_zero b hpb hx hΛ,
      AnalyticNumberTheory.Arithmetic.character_apply_one_of_mangoldt_ne_zero c hpc hx hΛ,
      Complex.one_re]
    norm_num only
  have h := quarter_shift_comparison_lower_663 hRH d hd hp hr
  dsimp only [d] at h
  linarith only [h, quarter_shift_mix_663 ha hb hc hRH hr.1 hL,
    (abs_le.mp (quarter_shift_xi_cap_663 hRH hr.1)).1]

/-- The three-character comparison retains both the tested prefix and
the recovered prime powers after absorbing the shifted contour terms. -/
theorem quarter_main_comparison_663 {p q k : ℕ} [NeZero p] [NeZero q] [NeZero k]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ k}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hk : 2 ≤ k)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r : ℝ}
    (hr : r ∈ Set.Icc 328 (663 / 2)) (hL : Real.log p + Real.log q + Real.log k = 4 * r)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hpa : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → a n = 1)
    (hpb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → b n = 1)
    (hpc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → c n = 1) (K : Finset ℕ)
    (hK : ∀ n ∈ K, r ^ 2 < (n : ℝ)) (hU : ∀ n ∈ K, Real.log ((n : ℝ) / r ^ 2) ≤ 21 / 8)
    (hpow : ∀ n ∈ K, ∃ p k : ℕ, p.Prime ∧ 2 ≤ k ∧ n = p ^ k) :
    let d := fun n : ℕ ↦ 3 - ((a n).re + (b n).re + (c n).re)
    let W := fun n ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) n).re
    let Q := fun n : ℕ ↦ (n : ℝ) ^ (-(8 / 5) : ℝ) * quarterAuxProfile656 (Real.log n)
    4 * (∑ n ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊, W n) +
        (∑ n ∈ K, 4 * (ArithmeticFunction.vonMangoldt n * quarterWeight656 (r ^ 2) n)) +
        (∑' n : { n : ℕ // ⌊r ^ 2⌋₊ < n },
          d n.val * (ArithmeticFunction.vonMangoldt n.val * Q n.val)) ≤
      quarterCosineContour656 a 0 + quarterCosineContour656 b 0 + quarterCosineContour656 c 0 +
              ((contourRemainder656 a (r ^ 2)).re + (contourRemainder656 b (r ^ 2)).re +
                (contourRemainder656 c (r ^ 2)).re) +
              (∑' n, W n) -
            (3 / 4 - 0.71780481) * r +
          9.42802707 -
        0.0219746789 * (663 / 2 - r) := by
  intro d W Q
  have h := quarter_recovered_prefix_663 ha hb hc hp hq hk hG hr hL ht hpa hpb hpc K hK hU hpow
  have hs := quarter_shift_forward_lower_663 ha hb hc hG.riemann hr hL ht hpa hpb hpc
  dsimp only at h
  dsimp only [d, W, Q]
  linarith only [h, hs]

/-- At frequency zero, the cosine Euler tail is the reflected quadratic
weighted by the common trace deficit. -/
theorem quarter_cosine_zero_tail_663 {p q k : ℕ} (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ k) {x : ℝ} (hx : 1 ≤ x) :
    quarterCosineTail656 a b c x 0 =
      ∑' n : { n : ℕ // ⌊x⌋₊ < n },
        (3 - ((a n.val).re + (b n.val).re + (c n.val).re)) *
          (ArithmeticFunction.vonMangoldt n.val *
            ((n.val : ℝ) ^ (-(8 / 5) : ℝ) * quarterAuxProfile656 (Real.log n.val))) := by
  unfold quarterCosineTail656
  apply tsum_congr
  intro n
  have hn := (Nat.floor_lt (zero_le_one.trans hx)).mp n.property
  have hp := (zero_lt_one.trans_le hx).trans hn
  have h :=
    quarter_cosine_profile_pair_656 hp (s := 0)
      (by simpa only [abs_zero] using Real.log_nonneg (hx.trans hn.le))
  rw [h]
  have hs :
    Real.exp (-(11 / 10) * Real.log n.val) / Real.sqrt n.val = (n.val : ℝ) ^ (-(8 / 5) : ℝ) := by
    rw [mul_comm (-(11 / 10 : ℝ)), ← Real.rpow_def_of_pos hp, Real.sqrt_eq_rpow, ← Real.rpow_sub hp,
      show -(11 / 10 : ℝ) - 1 / 2 = -(8 / 5) by norm_num only]
  simp only [quarterAuxPair656, abs_zero, mul_zero, Real.exp_zero, sub_zero, add_zero, one_mul,
    add_self_div_two]
  linear_combination
    (3 - ((a n.val).re + (b n.val).re + (c n.val).re)) * ArithmeticFunction.vonMangoldt n.val *
      quarterAuxProfile656 (Real.log n.val) *
      hs

/-- The unshifted cosine core includes the linear conductor contribution
and the two half-point residues, with an upper error from the zeta zeros. -/
theorem quarter_cosine_zero_cap_663 (hRH : RiemannHypothesis) (r : ℝ) :
    quarterCosineCore656 (4 * r) 0 ≤
      3 / 4 * r + 0.000003 - 6 * ((11 / 10 : ℝ) ^ 5 / ((11 / 10 : ℝ) ^ 2 - 1 / 4) ^ 3) := by
  have hp := quarter_cosine_pole_pair_656 (0 : ℝ)
  dsimp only at hp
  have hx := (abs_le.mp (quarter_xi_cosine_abs_656 hRH (le_refl (0 : ℝ)))).2
  unfold quarterCosineCore656
  dsimp only
  simp only [abs_zero, Real.exp_zero, inv_one] at hp ⊢
  rw [symmetric_profile_value (by norm_num only : (0 : ℝ) < 1)]
  norm_num only [Real.log_one, abs_zero, mul_zero, neg_zero, Real.exp_zero, one_mul,
    quarterAuxProfile656, add_zero]
  norm_num only [neg_zero, zero_div, Real.exp_zero, neg_div] at hp
  linarith only [hp, hx]

/-- Cancel the common Euler tail and expand the principal contour, using
the sharper recovery budget at quarter-square radii through 663/2. -/
theorem quarter_scaled_comparison_upper {p q k : ℕ} [NeZero p] [NeZero q] [NeZero k]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ k}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hk : 2 ≤ k)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r t : ℝ}
    (hr : r ∈ Set.Icc 328 333) (hL : Real.log p + Real.log q + Real.log k = 4 * t)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hpa : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → a n = 1)
    (hpb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → b n = 1)
    (hpc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → c n = 1) (K : Finset ℕ)
    (hK : ∀ n ∈ K, r ^ 2 < (n : ℝ)) (hU : ∀ n ∈ K, Real.log ((n : ℝ) / r ^ 2) ≤ 21 / 8)
    (hpow : ∀ n ∈ K, ∃ p k : ℕ, p.Prime ∧ 2 ≤ k ∧ n = p ^ k) :
    let x := r ^ 2
    let W := fun n ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) x n).re
    let R := (quarterKernel656.transform x⁻¹).re
    4 * (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, W n) - (∑' n, W n) +
        (∑ n ∈ K, 4 * (ArithmeticFunction.vonMangoldt n * quarterWeight656 x n)) +
        (quarterShiftedForward663 a r + quarterShiftedForward663 b r +
          quarterShiftedForward663 c r) +
        (if r ≤ 663 / 2 then 14.55079583 else if r ≤ 332 then 14.54846283 else 14.54795483) ≤
      (3 / 4 + quarterAuxMix663 quarterConductorProfile663) * t + 4 * t * R +
          3 * (centralGammaPair656 (1 : DirichletCharacter ℂ 1) x).re -
        (quarterMainEuler656 a x + quarterMainEuler656 b x + quarterMainEuler656 c x) := by
  intro x W R
  have hr₁ : (1 : ℝ) ≤ r := (by norm_num only : (1 : ℝ) ≤ 328).trans hr.1
  have hx : 1 ≤ x := one_le_pow₀ hr₁
  have hx₀ := zero_lt_one.trans_le hx
  have he := quarter_three_cosine_split_656 ha hb hc (sq_nonneg r) 0 hpa hpb hpc
  rw [hL, quarter_cosine_zero_tail_663 a b c hx, abs_zero] at he
  have h := quarter_scaled_recovered_prefix ha hb hc hp hq hk hG hr hL ht hpa hpb hpc K hK hU hpow
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
  dsimp only [x, W, R] at h he hCa hCb hCc hcond ⊢
  by_cases hb : r ≤ 663 / 2
  · rw [ite_eq_left hb] at h ⊢
    linarith only [h, he, hm, hCa, hCb, hCc, hcond, quarter_mass_constant_656]
  · rw [ite_eq_right hb] at h ⊢
    by_cases hs : r ≤ 332
    · rw [ite_eq_left hs] at h ⊢
      linarith only [h, he, hm, hCa, hCb, hCc, hcond, quarter_mass_constant_656]
    · rw [ite_eq_right hs] at h ⊢
      linarith only [h, he, hm, hCa, hCb, hCc, hcond, quarter_mass_constant_656]

/-- Use the shared principal comparison at the expanded Gaussian radius. -/
theorem quarter_gaussian_comparison_upper {p q k : ℕ} [NeZero p] [NeZero q] [NeZero k]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ k}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hk : 2 ≤ k)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r t : ℝ}
    (hr : r ∈ Set.Icc (663 / 2) 332) (hL : Real.log p + Real.log q + Real.log k = 4 * t)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hpa : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → a n = 1)
    (hpb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → b n = 1)
    (hpc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → c n = 1) (K : Finset ℕ)
    (hK : ∀ n ∈ K, r ^ 2 < (n : ℝ)) (hU : ∀ n ∈ K, Real.log ((n : ℝ) / r ^ 2) ≤ 21 / 8)
    (hpow : ∀ n ∈ K, ∃ p k : ℕ, p.Prime ∧ 2 ≤ k ∧ n = p ^ k) :
    let x := r ^ 2
    let W := fun n ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) x n).re
    let R := (quarterKernel656.transform x⁻¹).re
    4 * (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, W n) - (∑' n, W n) +
        (∑ n ∈ K, 4 * (ArithmeticFunction.vonMangoldt n * quarterWeight656 x n)) +
        (quarterShiftedForward663 a r + quarterShiftedForward663 b r +
          quarterShiftedForward663 c r) +
        14.54846283 ≤
      (3 / 4 + quarterAuxMix663 quarterConductorProfile663) * t + 4 * t * R +
          3 * (centralGammaPair656 (1 : DirichletCharacter ℂ 1) x).re -
        (quarterMainEuler656 a x + quarterMainEuler656 b x + quarterMainEuler656 c x) := by
  intro x W R
  have h :=
    quarter_scaled_comparison_upper ha hb hc hp hq hk hG
      ⟨(by norm_num only : (328 : ℝ) ≤ 663 / 2).trans hr.1, hr.2.trans (by norm_num only)⟩ hL ht hpa
      hpb hpc K hK hU hpow
  dsimp only [x, W, R] at h ⊢
  by_cases hb : r ≤ 663 / 2
  · rw [ite_eq_left hb] at h
    linarith only [h]
  · rw [ite_eq_right hb, ite_eq_left hr.2] at h
    exact h

/-- Cancel the unshifted cosine Euler contribution and keep the main
contour remainders and the principal forward sum. -/
theorem quarter_main_cancel_663 {p q k : ℕ} [NeZero p] [NeZero q] [NeZero k]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ k}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hk : 2 ≤ k)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r : ℝ}
    (hr : r ∈ Set.Icc 328 (663 / 2)) (hL : Real.log p + Real.log q + Real.log k = 4 * r)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hpa : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → a n = 1)
    (hpb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → b n = 1)
    (hpc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → c n = 1) (K : Finset ℕ)
    (hK : ∀ n ∈ K, r ^ 2 < (n : ℝ)) (hU : ∀ n ∈ K, Real.log ((n : ℝ) / r ^ 2) ≤ 21 / 8)
    (hpow : ∀ n ∈ K, ∃ p k : ℕ, p.Prime ∧ 2 ≤ k ∧ n = p ^ k) :
    let W := fun n ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) n).re
    4 * (∑ n ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊, W n) +
        (∑ n ∈ K, 4 * (ArithmeticFunction.vonMangoldt n * quarterWeight656 (r ^ 2) n)) ≤
      (contourRemainder656 a (r ^ 2)).re + (contourRemainder656 b (r ^ 2)).re +
          (contourRemainder656 c (r ^ 2)).re +
          (∑' n, W n) +
          0.71780481 * r -
        1.49393987 -
        0.0219746789 * (663 / 2 - r) := by
  intro W
  have hx : 1 ≤ r ^ 2 := one_le_pow₀ ((by norm_num only : (1 : ℝ) ≤ 328).trans hr.1)
  have h := quarter_main_comparison_663 ha hb hc hp hq hk hG hr hL ht hpa hpb hpc K hK hU hpow
  have he := quarter_three_cosine_split_656 ha hb hc (sq_nonneg r) 0 hpa hpb hpc
  rw [hL, quarter_cosine_zero_tail_663 a b c hx, abs_zero] at he
  dsimp only at h
  dsimp only [W]
  have hm := quarter_cosine_zero_cap_663 hG.riemann r
  norm_num only at hm
  linarith only [h, he, hm]

/-- After removing the main contour remainders, the recovered power
weight is bounded by the principal tail and scalar kernel values. -/
theorem quarter_scalar_comparison_663 {p q k : ℕ} [NeZero p] [NeZero q] [NeZero k]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ k}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hk : 2 ≤ k)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r : ℝ}
    (hr : r ∈ Set.Icc 328 (663 / 2)) (hL : Real.log p + Real.log q + Real.log k = 4 * r)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hpa : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → a n = 1)
    (hpb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → b n = 1)
    (hpc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → c n = 1) (K : Finset ℕ)
    (hK : ∀ n ∈ K, r ^ 2 < (n : ℝ)) (hU : ∀ n ∈ K, Real.log ((n : ℝ) / r ^ 2) ≤ 21 / 8)
    (hpow : ∀ n ∈ K, ∃ p k : ℕ, p.Prime ∧ 2 ≤ k ∧ n = p ^ k) :
    let x := r ^ 2
    let W := fun n ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) x n).re
    let P := fun t : ℝ ↦ (quarterKernel656.function (t : ℂ) * (x : ℂ) ^ (t : ℂ)).re
    (∑ n ∈ K, 4 * (ArithmeticFunction.vonMangoldt n * quarterWeight656 x n)) ≤
      4 * ((∑' n, W n) - ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, W n) +
              4 * r * (quarterKernel656.transform x⁻¹).re -
            3 * P (-1 / 2) -
            3 * P (1 / 2) +
          0.71780481 * r -
        1.49369637 -
        0.0219746789 * (663 / 2 - r) := by
  intro x W P
  have hr₀ : 0 < r := by linarith only [hr.1]
  have hx : 1 ≤ r ^ 2 := one_le_pow₀ ((by norm_num only : (1 : ℝ) ≤ 328).trans hr.1)
  have h := quarter_main_cancel_663 ha hb hc hp hq hk hG hr hL ht hpa hpb hpc K hK hU hpow
  have he : 21 / 8 + -(21 / 8 : ℝ) = 0 := by ring
  have hg :=
    quarter_shifted_forward_diff_656 ha hb hc hG.riemann hr₀ (h := -(21 / 8))
      (by simpa only [he, neg_zero, Real.exp_zero, mul_one] using hx)
  simp only [he, neg_zero, Real.exp_zero, mul_one, hL, Complex.sub_re] at hg
  have hw :
    (quarterKernel656.transform (r ^ 2)⁻¹).re =
      Analysis.rationalPoleProfile 3 (5 / 11) (21 / 16) (r ^ 2)⁻¹ := by
    rw [quarterKernel656,
      LLS.PaperStatements.rationalPole_transform _ _ _ _ (inv_pos.mpr (sq_pos_of_pos hr₀)),
      Complex.ofReal_re]
  rw [← hw] at hg
  have hm :=
    quarter_main_reflect_cap_656 a b c hG.riemann (by linarith only [hr.1] : 322 ≤ r) (B := 103684)
      (by norm_num only) (by norm_num only)
      ((by norm_num only : (103684 : ℝ) ≤ 328 ^ 2).trans
        (pow_le_pow_left₀ (by norm_num only) hr.1 2))
      ht hpa hpb hpc
  have hx' : 1 ≤ r ^ 2 * Real.exp (-(21 / 8 + -(21 / 8 : ℝ))) := by
    simpa only [he, neg_zero, Real.exp_zero, mul_one] using hx
  have hf := quarter_shift_euler_deficit_656 a b c hr₀ (h := -(21 / 8)) hx'
  simp only [he, neg_zero, Real.exp_zero, mul_one] at hf
  rw [hf] at hm
  have ht' := hm.trans (quarter_main_reflect_box_663 ⟨hr.1, hr.2.trans (by norm_num only)⟩)
  have hz := (abs_le.mp (quarter_main_zero_abs_656 hG.riemann hx)).2
  dsimp only at h
  dsimp only [x, W, P]
  rw [Complex.re_tsum
      (LLS.PaperStatements.MellinKernel.summable_summand quarterKernel656
        (1 : DirichletCharacter ℂ 1) (sq_pos_of_pos hr₀))] at hg
  linarith only [h, hg, ht', hz]

end PseudoPrime.PrimeTestBounds.MillerRabin
