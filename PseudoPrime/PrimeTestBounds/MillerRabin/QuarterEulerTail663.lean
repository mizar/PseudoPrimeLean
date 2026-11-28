/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPowerCorrection663
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterForward663
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMass656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterProfileTail663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAuxEuler656

/-! # Common Euler comparison indexed by the unknown support -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem tsum_above_eq {f : ℕ → ℝ} (hf : Summable f) (h₀ : f 0 = 0) (N : ℕ) :
    (∑' n : { n : ℕ // N < n }, f n.val) = (∑' n : ℕ, f n) - ∑ n ∈ Finset.Ioc 0 N, f n := by
  classical
  have he :
    (∑' n : { n : ℕ // n ∉ Finset.Ioc 0 N }, f n.val) = ∑' n : { n : ℕ // N < n }, f n.val := by
    have hc := tsum_subtype {n : ℕ | n ∉ Finset.Ioc 0 N} f
    have ht := tsum_subtype {n : ℕ | N < n} f
    change (∑' n : { n : ℕ // n ∉ Finset.Ioc 0 N }, f n.val) = _ at hc
    change (∑' n : { n : ℕ // N < n }, f n.val) = _ at ht
    rw [hc, ht]
    apply tsum_congr
    intro n
    by_cases hn : n = 0
    · subst n
      simp only [Set.indicator, h₀, ite_self]
    · have hp := Nat.pos_of_ne_zero hn
      simp only [Set.indicator, Set.mem_ofPred, Finset.mem_Ioc, hp, true_and, not_le]
  have hs := hf.sum_add_tsum_compl (s := Finset.Ioc 0 N)
  change
    (∑ n ∈ Finset.Ioc 0 N, f n) + (∑' n : { n : ℕ // n ∉ Finset.Ioc 0 N }, f n.val) =
      ∑' n, f n at hs
  rw [he] at hs
  linarith only [hs]

/-- The common signed Euler series above the tested range retains the
selected prime powers, with the same numerical correction as the prefix-subtracted sum. -/
theorem quarter_recovery_above_663 (hRH : RiemannHypothesis) {r : ℝ}
    (hr : r ∈ Set.Icc 328 (663 / 2)) {p q s : ℕ} (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (ha : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → a n = 1)
    (hb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → b n = 1)
    (hc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → c n = 1) (K : Finset ℕ)
    (hK : ∀ n ∈ K, r ^ 2 < (n : ℝ)) (hU : ∀ n ∈ K, Real.log ((n : ℝ) / r ^ 2) ≤ 21 / 8)
    (hpow : ∀ n ∈ K, ∃ p k : ℕ, p.Prime ∧ 2 ≤ k ∧ n = p ^ k) :
    let d := fun n : ℕ ↦ 3 - ((a n).re + (b n).re + (c n).re)
    (-0.013786 : ℝ) +
        (∑ n ∈ K, 4 * (ArithmeticFunction.vonMangoldt n * quarterWeight656 (r ^ 2) n)) ≤
      ∑' n : { n : ℕ // ⌊r ^ 2⌋₊ < n },
        ArithmeticFunction.vonMangoldt n.val *
          ((4 - d n.val) *
              (if Real.log ((n.val : ℝ) / r ^ 2) ≤ 21 / 8 then quarterWeight656 (r ^ 2) n.val
              else 0) -
            d n.val * quarterDensity663 n.val) := by
  intro d
  have hd (n : ℕ) : d n ∈ Set.Icc 0 4 :=
    ⟨sub_nonneg.mpr (ht n).2, by
      dsimp only [d]; linarith only [(ht n).1]⟩
  rw [tsum_above_eq (common_tail_summable hr.1 d hd)
      (by simp only [ArithmeticFunction.map_zero, zero_mul])]
  exact quarter_recovery_trace_663 hRH hr a b c ht ha hb hc K hK hU hpow

private theorem q_summable :
    Summable
      (fun n : ℕ ↦
        ArithmeticFunction.vonMangoldt n *
          ((n : ℝ) ^ (-(8 / 5) : ℝ) * quarterAuxProfile656 (Real.log n))) := by
  have hm :=
    AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.summable_mangoldt_log (σ := 8 / 5)
      (by norm_num only)
  refine
    (((hm 2).mul_left ((11 / 10 : ℝ) ^ 2 / 8)).add ((hm 1).mul_left (3 * (11 / 10) / 8))).add
        ((hm 0).mul_left (3 / 8)) |>.congr
      ?_
  intro n
  simp only [quarterAuxProfile656, Real.rpow_neg (Nat.cast_nonneg n), pow_zero, pow_one,
    div_eq_mul_inv]
  ring

/-- The signed Euler series splits into the common forward-minus-quadratic
part and the additional mixed cosine tail. All three series converge. -/
theorem quarter_euler_split_above_663 {r : ℝ} (hr : 328 ≤ r) (d : ℕ → ℝ)
    (hd : ∀ n, d n ∈ Set.Icc 0 4) :
    let N := { n : ℕ // ⌊r ^ 2⌋₊ < n }
    let f := fun n : ℕ ↦
      if Real.log ((n : ℝ) / r ^ 2) ≤ 21 / 8 then quarterWeight656 (r ^ 2) n else 0
    let q := fun n : ℕ ↦ (n : ℝ) ^ (-(8 / 5) : ℝ) * quarterAuxProfile656 (Real.log n)
    (∑' n : N,
        ArithmeticFunction.vonMangoldt n.val *
          ((4 - d n.val) * f n.val - d n.val * quarterDensity663 n.val)) =
      (∑' n : N,
          ArithmeticFunction.vonMangoldt n.val * ((4 - d n.val) * f n.val - d n.val * q n.val)) -
        (∑' n : N,
          d n.val * (ArithmeticFunction.vonMangoldt n.val / (n.val : ℝ) ^ (8 / 5 : ℝ)) *
            (quarterProfile663 (Real.log n.val) - quarterAuxProfile656 (Real.log n.val))) := by
  intro N f q
  let g := fun n : ℕ ↦
    ArithmeticFunction.vonMangoldt n * ((4 - d n) * f n - d n * quarterDensity663 n)
  let k := fun n : ℕ ↦ d n * (ArithmeticFunction.vonMangoldt n * (quarterDensity663 n - q n))
  have hg : Summable g := common_tail_summable hr d hd
  have hb :
    Summable (fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * (quarterDensity663 n - q n)) := by
    simpa only [mul_sub] using quarter_profile_summable_663.sub q_summable
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
        (quarterProfile663 (Real.log n.val) - quarterAuxProfile656 (Real.log n.val)) := by
    simp only [k, q, quarterDensity663, Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv]
    ring
  simp only [h₁] at hs
  simp only [h₂] at hs
  change (∑' n : N, g n.val) = _
  linarith only [hs]

/-- Join the three forward inequalities to the recovered prime-power
mass. The mixed cosine tail cancels against the common signed Euler series. -/
theorem quarter_forward_recovered_663 {p q k : ℕ} [NeZero p] [NeZero q] [NeZero k]
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
    let N := { n : ℕ // ⌊r ^ 2⌋₊ < n }
    let f := fun n : ℕ ↦
      if Real.log ((n : ℝ) / r ^ 2) ≤ 21 / 8 then quarterWeight656 (r ^ 2) n else 0
    let Q := fun n : ℕ ↦ (n : ℝ) ^ (-(8 / 5) : ℝ) * quarterAuxProfile656 (Real.log n)
    (∑' n, quarterKernel656.summand a (r ^ 2) n).re +
        (∑' n, quarterKernel656.summand b (r ^ 2) n).re +
        (∑' n, quarterKernel656.summand c (r ^ 2) n).re +
        (quarterShiftedForward663 a r + quarterShiftedForward663 b r +
          quarterShiftedForward663 c r) +
        3.62673593 +
        (∑ n ∈ K, 4 * (ArithmeticFunction.vonMangoldt n * quarterWeight656 (r ^ 2) n)) ≤
      quarterCosineContour656 a 0 + quarterCosineContour656 b 0 + quarterCosineContour656 c 0 +
        ((contourRemainder656 a (r ^ 2)).re + (contourRemainder656 b (r ^ 2)).re +
          (contourRemainder656 c (r ^ 2)).re) +
        quarterAuxMix663 quarterConductorProfile663 * r +
        ∑' n : N,
          ArithmeticFunction.vonMangoldt n.val * ((4 - d n.val) * f n.val - d n.val * Q n.val) := by
  intro d N f Q
  have hd (n : ℕ) : d n ∈ Set.Icc 0 4 :=
    ⟨sub_nonneg.mpr (ht n).2, by
      dsimp only [d]; linarith only [(ht n).1]⟩
  have h := quarter_recovery_above_663 hG.riemann hr a b c ht hpa hpb hpc K hK hU hpow
  dsimp only at h
  have he := quarter_euler_split_above_663 hr.1 d hd
  dsimp only at he
  dsimp only [d] at he
  rw [he] at h
  dsimp only [d, N, f, Q]
  linarith only [h, quarter_three_forward_663 ha hb hc hp hq hk hG hr.1 hL hpa hpb hpc]

private theorem principal_summand_eq {x : ℝ} (hx : 0 < x) (n : ℕ) :
    (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) x n).re =
      ArithmeticFunction.vonMangoldt n *
        (if Real.log ((n : ℝ) / x) ≤ 21 / 8 then quarterWeight656 x n else 0) := by
  by_cases hn : n = 0
  · simp only [hn, LLS.PaperStatements.MellinKernel.summand, ite_true, Complex.zero_re,
      ArithmeticFunction.map_zero, zero_mul]
  have hp := Nat.pos_of_ne_zero hn
  by_cases hs : Real.log ((n : ℝ) / x) ≤ 21 / 8
  · rw [ite_eq_left hs, quarter_summand_656 hx hp hs, mul_comm]
  have hy := div_pos (Nat.cast_pos.mpr hp) hx
  have hz :=
    Analysis.rationalPoleProfile_eq_zero 3 (5 / 11) (21 / 16)
      (by
        rw [show 2 * (21 / 16 : ℝ) = 21 / 8 by norm_num only]
        exact (Real.lt_log_iff_exp_lt hy).mp (lt_of_not_ge hs))
  simp only [ite_eq_right hs, mul_zero, LLS.PaperStatements.MellinKernel.summand, ite_eq_right hn]
  rw [quarterKernel656, LLS.PaperStatements.rationalPole_transform _ _ _ _ hy, hz]
  simp only [Complex.ofReal_zero, mul_zero, Complex.zero_re]

/-- The forward part of the common Euler tail cancels the three principal
deficits and leaves four copies of the tested prefix. -/
theorem quarter_forward_prefix_663 {p q k : ℕ} [NeZero p] [NeZero q] [NeZero k]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ k) {x : ℝ}
    (hx : 0 < x) (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (ha : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ x → a n = 1) (hb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ x → b n = 1)
    (hc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ x → c n = 1) :
    let d := fun n : ℕ ↦ 3 - ((a n).re + (b n).re + (c n).re)
    let W := fun n ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) x n).re
    (∑' n, quarterKernel656.summand a x n).re + (∑' n, quarterKernel656.summand b x n).re +
          (∑' n, quarterKernel656.summand c x n).re +
          (∑' n, W n) -
        (∑' n : { n : ℕ // ⌊x⌋₊ < n }, (4 - d n.val) * W n.val) =
      4 * ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, W n := by
  intro d W
  have hW : Summable W :=
    (Complex.hasSum_re
        (LLS.PaperStatements.MellinKernel.summable_summand quarterKernel656
            (1 : DirichletCharacter ℂ 1) hx).hasSum).summable
  have hdW : Summable (fun n ↦ (4 - d n) * W n) := by
    apply Summable.of_norm_bounded (hW.norm.mul_left 4)
    intro n
    have h := ht n
    have h₀ : 0 ≤ 4 - d n := by
      dsimp only [d]; linarith only [h.1]
    have h₁ : 4 - d n ≤ 4 := by
      dsimp only [d]; linarith only [h.2]
    rw [norm_mul, Real.norm_of_nonneg h₀]
    exact mul_le_mul_of_nonneg_right h₁ (norm_nonneg _)
  rw [tsum_above_eq hdW
      (by simp only [W, principal_summand_eq hx, ArithmeticFunction.map_zero, zero_mul, mul_zero])]
  have hs :
    (∑' n, (4 - d n) * W n) =
      (∑' n, quarterKernel656.summand a x n).re + (∑' n, quarterKernel656.summand b x n).re +
        (∑' n, quarterKernel656.summand c x n).re +
        (∑' n, W n) := by
    have he (n : ℕ) : 4 * W n - (4 - d n) * W n = d n * W n := by ring
    have h := quarter_forward_trace_deficit_656 a b c hx
    change _ = (∑' n, d n * W n) at h
    have hz : (∑' n, d n * W n) = 4 * (∑' n, W n) - (∑' n, (4 - d n) * W n) := by
      simpa only [Pi.sub_apply, he, tsum_mul_left] using (hW.mul_left 4).tsum_sub hdW
    have hWsum :=
      Complex.re_tsum
        (LLS.PaperStatements.MellinKernel.summable_summand quarterKernel656
          (1 : DirichletCharacter ℂ 1) hx)
    change _ = (∑' n, W n) at hWsum
    linarith only [h, hz, hWsum]
  rw [hs]
  have hf : (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (4 - d n) * W n) = 4 * ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, W n := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hn' := (Nat.le_floor_iff hx.le).mp (Finset.mem_Ioc.mp hn).2
    by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
    · simp only [W, principal_summand_eq hx, hΛ, zero_mul, mul_zero]
    simp only [d,
      AnalyticNumberTheory.Arithmetic.character_apply_one_of_mangoldt_ne_zero a ha hn' hΛ,
      AnalyticNumberTheory.Arithmetic.character_apply_one_of_mangoldt_ne_zero b hb hn' hΛ,
      AnalyticNumberTheory.Arithmetic.character_apply_one_of_mangoldt_ne_zero c hc hn' hΛ,
      Complex.one_re]
    ring
  linarith only [hf]

/-- Split the common forward-minus-quadratic tail into the physical
principal summand and the reflected quadratic term. -/
theorem quarter_forward_quadratic_split_663 {x : ℝ} (hx : 0 < x) (d : ℕ → ℝ)
    (hd : ∀ n, d n ∈ Set.Icc 0 4) :
    let N := { n : ℕ // ⌊x⌋₊ < n }
    let Q := fun n : ℕ ↦ (n : ℝ) ^ (-(8 / 5) : ℝ) * quarterAuxProfile656 (Real.log n)
    let W := fun n ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) x n).re
    (∑' n : N,
        ArithmeticFunction.vonMangoldt n.val *
          ((4 - d n.val) *
              (if Real.log ((n.val : ℝ) / x) ≤ 21 / 8 then quarterWeight656 x n.val else 0) -
            d n.val * Q n.val)) =
      (∑' n : N, (4 - d n.val) * W n.val) -
        (∑' n : N, d n.val * (ArithmeticFunction.vonMangoldt n.val * Q n.val)) := by
  intro N Q W
  have hW : Summable W :=
    (Complex.hasSum_re
        (LLS.PaperStatements.MellinKernel.summable_summand quarterKernel656
            (1 : DirichletCharacter ℂ 1) hx).hasSum).summable
  have hb {g : ℕ → ℝ} (hg : Summable g) {v : ℕ → ℝ} (hv : ∀ n, v n ∈ Set.Icc 0 4) :
    Summable (fun n ↦ v n * g n) := by
    apply Summable.of_norm_bounded (hg.norm.mul_left 4)
    intro n
    rw [norm_mul, Real.norm_of_nonneg (hv n).1]
    exact mul_le_mul_of_nonneg_right (hv n).2 (norm_nonneg _)
  have hdW :=
    hb hW (v := fun n ↦ 4 - d n) (fun n ↦ ⟨sub_nonneg.mpr (hd n).2, by linarith only [(hd n).1]⟩)
  have hdQ := hb q_summable hd
  have hs := (hdW.subtype (fun n ↦ ⌊x⌋₊ < n)).tsum_sub (hdQ.subtype (fun n ↦ ⌊x⌋₊ < n))
  refine Eq.trans ?_ hs
  apply tsum_congr
  intro n
  dsimp only [W, Function.comp_apply]
  rw [principal_summand_eq hx]
  ring

/-- The three-character comparison retains both the tested prefix and
the recovered prime powers, with one reflected quadratic term. -/
theorem quarter_recovered_prefix_663 {p q k : ℕ} [NeZero p] [NeZero q] [NeZero k]
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
        (quarterShiftedForward663 a r + quarterShiftedForward663 b r +
          quarterShiftedForward663 c r) +
        3.62673593 +
        (∑ n ∈ K, 4 * (ArithmeticFunction.vonMangoldt n * quarterWeight656 (r ^ 2) n)) +
        (∑' n : { n : ℕ // ⌊r ^ 2⌋₊ < n },
          d n.val * (ArithmeticFunction.vonMangoldt n.val * Q n.val)) ≤
      quarterCosineContour656 a 0 + quarterCosineContour656 b 0 + quarterCosineContour656 c 0 +
        ((contourRemainder656 a (r ^ 2)).re + (contourRemainder656 b (r ^ 2)).re +
          (contourRemainder656 c (r ^ 2)).re) +
        quarterAuxMix663 quarterConductorProfile663 * r +
        (∑' n, W n) := by
  intro d W Q
  have hx : 0 < r ^ 2 := sq_pos_of_pos (by linarith only [hr.1])
  have hd (n : ℕ) : d n ∈ Set.Icc 0 4 :=
    ⟨sub_nonneg.mpr (ht n).2, by
      dsimp only [d]; linarith only [(ht n).1]⟩
  have h := quarter_forward_recovered_663 ha hb hc hp hq hk hG hr hL ht hpa hpb hpc K hK hU hpow
  have he := quarter_forward_quadratic_split_663 hx d hd
  dsimp only at he h
  dsimp only [d] at he
  rw [he] at h
  have hf := quarter_forward_prefix_663 a b c hx ht hpa hpb hpc
  dsimp only [d, W, Q] at hf ⊢
  linarith only [h, hf]

/-- At Gaussian K137 radii, the tested prefix and recovered powers obey
the forward comparison with an independent conductor radius. -/
theorem quarter_scaled_recovered_prefix {p q k : ℕ} [NeZero p] [NeZero q] [NeZero k]
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
    let d := fun n : ℕ ↦ 3 - ((a n).re + (b n).re + (c n).re)
    let W := fun n ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) n).re
    let Q := fun n : ℕ ↦ (n : ℝ) ^ (-(8 / 5) : ℝ) * quarterAuxProfile656 (Real.log n)
    4 * (∑ n ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊, W n) +
        (quarterShiftedForward663 a r + quarterShiftedForward663 b r +
          quarterShiftedForward663 c r) +
        (if r ≤ 663 / 2 then 3.62882893 else if r ≤ 332 then 3.62649593 else 3.62598793) +
        (∑ n ∈ K, 4 * (ArithmeticFunction.vonMangoldt n * quarterWeight656 (r ^ 2) n)) +
        (∑' n : { n : ℕ // ⌊r ^ 2⌋₊ < n },
          d n.val * (ArithmeticFunction.vonMangoldt n.val * Q n.val)) ≤
      quarterCosineContour656 a 0 + quarterCosineContour656 b 0 + quarterCosineContour656 c 0 +
        ((contourRemainder656 a (r ^ 2)).re + (contourRemainder656 b (r ^ 2)).re +
          (contourRemainder656 c (r ^ 2)).re) +
        quarterAuxMix663 quarterConductorProfile663 * t +
        (∑' n, W n) := by
  intro d W Q
  have hr' : (328 : ℝ) ≤ r := hr.1
  have hx : 0 < r ^ 2 := sq_pos_of_pos ((by norm_num only : (0 : ℝ) < 328).trans_le hr')
  have hd (n : ℕ) : d n ∈ Set.Icc 0 4 :=
    ⟨sub_nonneg.mpr (ht n).2, by
      dsimp only [d]; linarith only [(ht n).1]⟩
  let w := fun n : ℕ ↦
    ArithmeticFunction.vonMangoldt n *
      ((4 - d n) * (if Real.log ((n : ℝ) / r ^ 2) ≤ 21 / 8 then quarterWeight656 (r ^ 2) n else 0) -
        d n * quarterDensity663 n)
  have hz : w 0 = 0 := by simp only [w, ArithmeticFunction.map_zero, zero_mul]
  have h :
    (if r ≤ 663 / 2 then -0.011693 else if r ≤ 332 then -0.014026 else -0.014534 : ℝ) +
        (∑ n ∈ K, 4 * (ArithmeticFunction.vonMangoldt n * quarterWeight656 (r ^ 2) n)) ≤
      (∑' n : ℕ, w n) - ∑ n ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊, w n := by
    by_cases hb : r ≤ 663 / 2
    · rw [ite_eq_left hb]
      have hh := quarter_bridge_recovery hG.riemann ⟨hr.1, hb⟩ a b c ht hpa hpb hpc K hK hU hpow
      dsimp only at hh
      change _ ≤ (∑' n : ℕ, w n) - ∑ n ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊, w n at hh
      linarith only [hh]
    · rw [ite_eq_right hb]
      exact
        quarter_recovery_trace_gaussian hG.riemann ⟨le_of_not_ge hb, hr.2⟩ a b c ht hpa hpb hpc K hK
          hU hpow
  change _ ≤ (∑' n : ℕ, w n) - ∑ n ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊, w n at h
  rw [← tsum_above_eq (common_tail_summable hr' d hd) hz] at h
  rw [quarter_euler_split_above_663 hr' d hd, quarter_forward_quadratic_split_663 hx d hd] at h
  have hf := quarter_forward_prefix_663 a b c hx ht hpa hpb hpc
  have hm := quarter_scaled_forward_663 ha hb hc hp hq hk hG hr' hL hpa hpb hpc
  dsimp only [d, W, Q] at h hf ⊢
  by_cases hb : r ≤ 663 / 2
  · rw [ite_eq_left hb] at h ⊢
    linarith only [h, hf, hm]
  · rw [ite_eq_right hb] at h ⊢
    by_cases hs : r ≤ 332
    · rw [ite_eq_left hs] at h ⊢
      linarith only [h, hf, hm]
    · rw [ite_eq_right hs] at h ⊢
      linarith only [h, hf, hm]

/-- The common recovered-prefix comparison on the first Gaussian radii. -/
theorem quarter_gaussian_recovered_prefix {p q k : ℕ} [NeZero p] [NeZero q] [NeZero k]
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
    let d := fun n : ℕ ↦ 3 - ((a n).re + (b n).re + (c n).re)
    let W := fun n ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) n).re
    let Q := fun n : ℕ ↦ (n : ℝ) ^ (-(8 / 5) : ℝ) * quarterAuxProfile656 (Real.log n)
    4 * (∑ n ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊, W n) +
        (quarterShiftedForward663 a r + quarterShiftedForward663 b r +
          quarterShiftedForward663 c r) +
        3.62649593 +
        (∑ n ∈ K, 4 * (ArithmeticFunction.vonMangoldt n * quarterWeight656 (r ^ 2) n)) +
        (∑' n : { n : ℕ // ⌊r ^ 2⌋₊ < n },
          d n.val * (ArithmeticFunction.vonMangoldt n.val * Q n.val)) ≤
      quarterCosineContour656 a 0 + quarterCosineContour656 b 0 + quarterCosineContour656 c 0 +
        ((contourRemainder656 a (r ^ 2)).re + (contourRemainder656 b (r ^ 2)).re +
          (contourRemainder656 c (r ^ 2)).re) +
        quarterAuxMix663 quarterConductorProfile663 * t +
        (∑' n, W n) := by
  intro d W Q
  have h :=
    quarter_scaled_recovered_prefix ha hb hc hp hq hk hG
      ⟨(by norm_num only : (328 : ℝ) ≤ 663 / 2).trans hr.1, hr.2.trans (by norm_num only)⟩ hL ht hpa
      hpb hpc K hK hU hpow
  dsimp only [d, W, Q] at h ⊢
  by_cases hb : r ≤ 663 / 2
  · rw [ite_eq_left hb] at h
    linarith only [h]
  · rw [ite_eq_right hb, ite_eq_left hr.2] at h
    exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
