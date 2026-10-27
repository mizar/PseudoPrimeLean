/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.LocalZeroCounting
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.CompletedGenusZeroSums
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.LocalZeroTuran
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.LocalZeroCountBounds

/-! # Completed L-function local zero power sums and remote tails -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity

/--
Inputs: a completed Dirichlet `L` function, a nearby zero, a local support containment, and a
natural bound for the rectangle multiplicity count.
Claim: the predicate records a fixed-multiple power-sum block with its exponent range and lower
bound.
Role: names the output type used by the rectangle-level zero-detection theorem.
-/
def CompletedLFunctionLocalZeroPowerSumBlockData {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (c : ℂ) (η : ℝ) (ρ : ℂ) (K C : ℕ) : Prop :=
  ∃ s : Finset ℂ,
    (∀ v,
        v ∈ s ↔
          MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball c |80 * η|)
              v ≠
            0) ∧
      ρ ∈ s ∧
      (∀ v ∈ s,
        v ∈ Metric.ball c |80 * η| ∧
          MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball c |80 * η|)
              v ≠
            0) ∧
      ∃
        k ∈
          Finset.range
            (∑ v ∈ s,
              (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                  (Metric.ball c |80 * η|) v).toNat),
        K ≤ K * (k + 1) ∧
          K * (k + 1) ≤ K * C ∧
          (1 /
                (4 *
                  ((∑ v ∈ s,
                        (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                            (Metric.ball c |80 * η|) v).toNat :
                      ℕ) :
                    ℝ))) *
              (1 / (3 * η)) ^ (K * (k + 1)) ≤
            ‖∑ᶠ v,
                ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                        (Metric.ball c |80 * η|) v :
                      ℤ) :
                    ℂ) *
                  (c - v)⁻¹ ^ (K * (k + 1))‖

/--
Inputs: a local fixed-multiple power-sum block for a completed Dirichlet `L`-function.
Claim: some exponent in the block has the same lower bound when its finitely supported sum is
written over the canonical finite divisor support.
Proof: identify the block's support with the finite divisor support and replace the `finsum` by
the corresponding finite sum.
Role: puts the local power-sum lower bound in the form used by the logarithmic-derivative split.
-/
theorem exists_completedLFunction_local_zero_block_on_finite_support {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {η : ℝ} {c ρ : ℂ} (K C : ℕ)
    (hblock : CompletedLFunctionLocalZeroPowerSumBlockData χ c η ρ K C) :
    0 <
        ∑ v ∈ (completedLFunction_local_zero_support_finite χ hχ c (80 * η)).toFinset,
          (MeromorphicOn.divisor χ.completedLFunction (Metric.ball c |80 * η|) v).toNat ∧
      ∃ m : ℕ,
        K ≤ m ∧
          m ≤ K * C ∧
          1 /
                (4 *
                  ((∑ v ∈ (completedLFunction_local_zero_support_finite χ hχ c (80 * η)).toFinset,
                        (MeromorphicOn.divisor χ.completedLFunction (Metric.ball c |80 * η|)
                            v).toNat :
                      ℕ) :
                    ℝ)) *
              (1 / (3 * η)) ^ m ≤
            ‖∑ v ∈ (completedLFunction_local_zero_support_finite χ hχ c (80 * η)).toFinset,
                ((MeromorphicOn.divisor χ.completedLFunction (Metric.ball c |80 * η|) v : ℤ) : ℂ) *
                  (c - v)⁻¹ ^ m‖ := by
  classical
  rcases hblock with ⟨s, hs, hρs, hmem, k, hk, hK, hKC, hlower⟩
  let hfinite := completedLFunction_local_zero_support_finite χ hχ c (80 * η)
  let S := hfinite.toFinset
  have hsS : s = S := by
    ext v
    rw [hs v]
    change
      (MeromorphicOn.divisor χ.completedLFunction (Metric.ball c |80 * η|) v ≠ 0) ↔
        v ∈ hfinite.toFinset
    rw [Set.Finite.mem_toFinset]
    rfl
  let m := K * (k + 1)
  have hsumSupport :
    Function.support
        (fun v : ℂ =>
          ((MeromorphicOn.divisor χ.completedLFunction (Metric.ball c |80 * η|) v : ℤ) : ℂ) *
            (c - v)⁻¹ ^ m) ⊆
      (s : Set ℂ) := by
    intro v hv
    change
      ((MeromorphicOn.divisor χ.completedLFunction (Metric.ball c |80 * η|) v : ℤ) : ℂ) *
          (c - v)⁻¹ ^ m ≠
        0 at hv
    have hdiv : MeromorphicOn.divisor χ.completedLFunction (Metric.ball c |80 * η|) v ≠ 0 := by
      intro hzero
      apply hv
      rw [hzero]
      simp only [Int.cast_zero, zero_mul]
    exact (hs v).2 hdiv
  have hsum :=
    finsum_eq_sum_of_support_subset
      (fun v : ℂ =>
        ((MeromorphicOn.divisor χ.completedLFunction (Metric.ball c |80 * η|) v : ℤ) : ℂ) *
          (c - v)⁻¹ ^ m)
      hsumSupport
  have hlower' := hlower
  rw [hsum, hsS] at hlower'
  have hsumPosS :
    0 < ∑ v ∈ s, (MeromorphicOn.divisor χ.completedLFunction (Metric.ball c |80 * η|) v).toNat :=
    Nat.zero_lt_of_lt (Finset.mem_range.mp hk)
  have hsumPos :
    0 < ∑ v ∈ S, (MeromorphicOn.divisor χ.completedLFunction (Metric.ball c |80 * η|) v).toNat := by
    simpa only [hsS] using hsumPosS
  refine ⟨hsumPos, m, ?_, ?_, ?_⟩
  · dsimp only [m]
    exact hK
  · dsimp only [m]
    exact hKC
  · simpa only [S, hfinite, m] using hlower'

/--
Inputs: a completed Dirichlet `L`-function, a local divisor disk, and a derivative order.
Claim: the local term in the logarithmic-derivative moment is the signed factorial times the
corresponding inverse-distance power sum.
Proof: rewrite the negative integer power as a natural power of the reciprocal, then factor the
constant out of the finite sum.
Role: converts the local power-sum block into the local contribution to the derivative split.
-/
theorem completedLFunction_local_divisor_power_sum_factorization {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {c : ℂ} (R : ℝ) (n : ℕ) :
    (∑ v ∈ (completedLFunction_local_zero_support_finite χ hχ c R).toFinset,
        (MeromorphicOn.divisor χ.completedLFunction (Metric.ball c |R|) v : ℂ) *
          ((-1 : ℂ) ^ n * (n.factorial : ℂ) * (c - v) ^ (-1 - (n : ℕ) : ℤ))) =
      ((-1 : ℂ) ^ n * (n.factorial : ℂ)) *
        ∑ v ∈ (completedLFunction_local_zero_support_finite χ hχ c R).toFinset,
          (MeromorphicOn.divisor χ.completedLFunction (Metric.ball c |R|) v : ℂ) *
            (c - v)⁻¹ ^ (n + 1) := by
  classical
  have hexp : (-1 : ℤ) - (n : ℤ) = Int.negSucc n := by
    rw [Int.negSucc_eq]
    ring
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  rw [show (-1 : ℤ) - (n : ℤ) = Int.negSucc n from hexp, zpow_negSucc, inv_pow]
  ring

/--
Inputs: a primitive completed-function zero close to the center, an admissible rectangle
containing the local divisor support, and the rectangle's localization bound at `1 + it`.

Claim: the uniform zero count gives a natural multiplicity cap together with a fixed-multiple
local power-sum block.

Proof: take the natural ceiling of the uniform rectangle estimate and pass the resulting count
bound to the local fixed-multiple power-sum theorem.

Role: joins local zero detection to the unconditional multiplicity-counting interface.
-/
theorem exists_completedLFunction_local_zero_power_sum_block_of_near_of_rectangle {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1)
    {c : ℂ} {η : ℝ} (hη : 0 < η) (hc : DirichletCharacter.completedLFunction χ c ≠ 0) (ρ : ℂ)
    (hρ :
      MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball c |80 * η|) ρ ≠
        0)
    (hclose : ‖c - ρ‖ ≤ 3 * η) (K : ℕ) (z w : ℂ)
    (hSupport :
      ∀
        v ∈
          (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
              (Metric.ball c |80 * η|)).support,
        v ∈ dirichletCompletedLFunctionRectangleBox z w)
    {θ t : ℝ} (hθ : 0 < θ) (hθle : θ ≤ 1 / 2)
    (hRectangle :
      ∀ u ∈ dirichletCompletedLFunctionRectangleBox z w,
        ‖u - ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ θ / 4) :
    ∃ C : ℕ,
      completedZeroMultiplicityCountInRectangle χ hχ z w ≤ (C : ℝ) ∧
        CompletedLFunctionLocalZeroPowerSumBlockData χ c η ρ K C ∧
        C =
          Nat.ceil
            (completedZeroLocalLogBoundConstant * (1 + θ * Real.log ((q : ℝ) * (|t| + 3)))) := by
  let B := completedZeroLocalLogBoundConstant * (1 + θ * Real.log ((q : ℝ) * (|t| + 3)))
  let C : ℕ := Nat.ceil B
  have hcount :=
    completedZeroMultiplicityCountInRectangle_le_nat_ceil_uniform_local_log_bound hq hχ hp hinv hθ
      hθle z w hRectangle
  have hcount' : completedZeroMultiplicityCountInRectangle χ hχ z w ≤ (C : ℝ) := by
    simpa only [C, B] using hcount
  exact
    ⟨C, hcount',
      exists_completedLFunction_local_zero_power_sum_fixed_multiple_block_of_near χ hχ hη hc ρ hρ
        hclose K z w hSupport C hcount',
      by rfl⟩

/--
Inputs: a primitive completed-function zero within horizontal distance `η` of `1`, a nonzero
center with real part `1 + η`, and a sufficiently small positive scale `η`.
Claim: a natural rectangle multiplicity cap and a fixed-multiple reciprocal-power-sum block exist
for the local divisor ball of radius `80η`, and the cap equals the ceiling of the explicit
uniform local count bound at height `ρ.im`.
Content: the ball fits in the rectangle centered at the chosen center, and every point of that
rectangle lies within `161η` of `1 + i * Im ρ`.
Proof: obtain the zero's divisor membership, use the centered-square support bound, and apply the
rectangle-level theorem with localization parameter `644η`.
Role: connects each near-one zero to a block whose cost is controlled by the uniform local count.
-/
theorem exists_completedLFunction_local_zero_power_sum_block_of_near_one_zero {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1)
    {η : ℝ} (hη : 0 < η) (hηsmall : η ≤ 1 / 1288) {c ρ : ℂ} (hcre : c.re = 1 + η)
    (hcim : c.im = ρ.im) (hρre : |ρ.re - 1| ≤ η)
    (hzero : DirichletCharacter.completedLFunction χ ρ = 0)
    (hc : DirichletCharacter.completedLFunction χ c ≠ 0) (K : ℕ) :
    ∃ C : ℕ,
      completedZeroMultiplicityCountInRectangle χ hχ ⟨c.re - 80 * η, c.im - 80 * η⟩
            ⟨c.re + 80 * η, c.im + 80 * η⟩ ≤
          (C : ℝ) ∧
        CompletedLFunctionLocalZeroPowerSumBlockData χ c η ρ K C ∧
        C =
          Nat.ceil
            (completedZeroLocalLogBoundConstant *
              (1 + 644 * η * Real.log ((q : ℝ) * (|ρ.im| + 3)))) := by
  have hreal : |c.re - ρ.re| ≤ 2 * η := by
    rw [hcre]
    have h := abs_le.mp hρre
    apply abs_le.mpr
    constructor <;> linarith only [h.1, h.2]
  have himag : |c.im - ρ.im| = 0 := by simp only [hcim, sub_self, abs_zero]
  have hdist : ‖c - ρ‖ ≤ 2 * η := by
    calc
      ‖c - ρ‖ ≤ |(c - ρ).re| + |(c - ρ).im| := Complex.norm_le_abs_re_add_abs_im _
      _ = |c.re - ρ.re| + |c.im - ρ.im| := by simp only [Complex.sub_re, Complex.sub_im]
      _ ≤ 2 * η := by simpa only [himag, add_zero] using hreal
  have hclose : ‖c - ρ‖ ≤ 3 * η := by
    have hηnonneg : 0 ≤ η := le_of_lt hη
    nlinarith only [hdist, hηnonneg]
  have hball : ρ ∈ Metric.ball c |80 * η| := by
    apply Metric.mem_ball.mpr
    rw [dist_eq_norm, abs_of_pos (mul_pos (by norm_num) hη)]
    calc
      ‖ρ - c‖ = ‖c - ρ‖ := norm_sub_rev _ _
      _ ≤ 2 * η := hdist
      _ < 80 * η := by nlinarith only [hη]
  have hρ := completedLFunction_zero_mem_local_divisor_support χ hχ hball hzero
  let z : ℂ := ⟨c.re - 80 * η, c.im - 80 * η⟩
  let w : ℂ := ⟨c.re + 80 * η, c.im + 80 * η⟩
  have hSupport :
    ∀
      v ∈
        (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.ball c |80 * η|)).support,
      v ∈ dirichletCompletedLFunctionRectangleBox z w := by
    intro v hv
    have hR : 0 < 80 * η := mul_pos (by norm_num) hη
    have hv'' := hv
    rw [abs_of_pos hR] at hv''
    have hv' :
      v ∈
        (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.ball c (80 * η))).support := by
      exact hv''
    have hsquare := completedLFunction_local_divisor_support_mem_centered_square χ c hR hv'
    simpa only [z, w] using hsquare
  have hθ : 0 < 644 * η := by positivity
  have hθle : 644 * η ≤ 1 / 2 := by
    have := hηsmall
    nlinarith only [this]
  have hRectangle :
    ∀ u ∈ dirichletCompletedLFunctionRectangleBox z w,
      ‖u - ((1 : ℂ) + (ρ.im : ℂ) * Complex.I)‖ ≤ (644 * η) / 4 := by
    intro u hu
    change
      u.re ∈ Set.uIcc (c.re - 80 * η) (c.re + 80 * η) ∧
        u.im ∈ Set.uIcc (c.im - 80 * η) (c.im + 80 * η) at hu
    have hηnonneg : 0 ≤ η := le_of_lt hη
    have hcoords :
      c.re - 80 * η ≤ u.re ∧
        u.re ≤ c.re + 80 * η ∧ c.im - 80 * η ≤ u.im ∧ u.im ≤ c.im + 80 * η := by
      rw [Set.uIcc_of_le (by nlinarith only [hηnonneg]),
        Set.uIcc_of_le (by nlinarith only [hηnonneg])] at hu
      exact ⟨hu.1.1, hu.1.2, hu.2.1, hu.2.2⟩
    have hreal' : |u.re - 1| ≤ 81 * η := by
      have hcoords' := hcoords
      rw [hcre] at hcoords'
      rw [abs_le]
      constructor
      · nlinarith only [hcoords'.1, hηnonneg]
      · nlinarith only [hcoords'.2.1, hηnonneg]
    have himag' : |u.im - ρ.im| ≤ 80 * η := by
      rw [abs_le, ← hcim]
      constructor <;> nlinarith only [hcoords.2.2, hcoords.2.1, hηnonneg]
    calc
      ‖u - ((1 : ℂ) + (ρ.im : ℂ) * Complex.I)‖ ≤
          |(u - ((1 : ℂ) + (ρ.im : ℂ) * Complex.I)).re| +
            |(u - ((1 : ℂ) + (ρ.im : ℂ) * Complex.I)).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ = |u.re - 1| + |u.im - ρ.im| := by
        simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
          Complex.I_im, Complex.one_re, Complex.one_im, mul_zero, mul_one, sub_zero, add_zero,
          zero_add]
      _ ≤ 81 * η + 80 * η := add_le_add hreal' himag'
      _ = (644 * η) / 4 := by ring
  have hηpositive : 0 < η := hη
  exact
    exists_completedLFunction_local_zero_power_sum_block_of_near_of_rectangle hq hχ hp hinv
      hηpositive hc ρ hρ hclose K z w hSupport hθ hθle hRectangle

/--
Inputs: a near-one completed-function zero, a nonzero center at real part `1 + η`, and a small
positive scale.
Claim: a multiplicity-capped fixed-multiple power-sum block exists, and every larger derivative
order has a remote tail bounded by half of the near-zero scale.
Proof: obtain the rectangle count cap, choose a uniform remote-tail threshold from the genus mass
bound, and apply the local block theorem at that threshold.
Role: aligns the local zero signal and the unconditional remote contribution on one order range.
-/
theorem exists_completedLFunction_local_zero_block_with_remote_tail {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1) {η : ℝ}
    (hη : 0 < η) (hηsmall : η ≤ 1 / 1288) {c ρ : ℂ} (hcre : c.re = 1 + η) (hcim : c.im = ρ.im)
    (hρre : |ρ.re - 1| ≤ η) (hzero : DirichletCharacter.completedLFunction χ ρ = 0)
    (hc : DirichletCharacter.completedLFunction χ c ≠ 0) :
    ∃ C K : ℕ,
      2 ≤ K ∧
        completedZeroMultiplicityCountInRectangle χ hχ ⟨c.re - 80 * η, c.im - 80 * η⟩
            ⟨c.re + 80 * η, c.im + 80 * η⟩ ≤
          (C : ℝ) ∧
        CompletedLFunctionLocalZeroPowerSumBlockData χ c η ρ K C ∧
        ∀ k : ℕ,
          K ≤ k →
            ‖∑' v : ℂ,
                  ((if 80 * η ≤ ‖c - v‖ then
                          (MeromorphicOn.divisor χ.completedLFunction Set.univ v : ℝ)
                        else 0 :
                        ℝ) :
                      ℂ) *
                    (if 80 * η ≤ ‖c - v‖ then (c - v)⁻¹ else 0) ^ k‖ ≤
              (1 / (8 * ((C : ℝ) + 1))) * (1 / (3 * η)) ^ (k + 1) := by
  classical
  obtain ⟨C, hcount, _⟩ :=
    exists_completedLFunction_local_zero_power_sum_block_of_near_one_zero hq hχ hp hinv hη hηsmall
      hcre hcim hρre hzero hc 2
  have hreal : |c.re - ρ.re| ≤ 2 * η := by
    rw [hcre]
    have h := abs_le.mp hρre
    apply abs_le.mpr
    constructor <;> linarith only [h.1, h.2]
  have himag : |c.im - ρ.im| = 0 := by simp only [hcim, sub_self, abs_zero]
  have hdist : ‖c - ρ‖ ≤ 2 * η := by
    calc
      ‖c - ρ‖ ≤ |(c - ρ).re| + |(c - ρ).im| := Complex.norm_le_abs_re_add_abs_im _
      _ = |c.re - ρ.re| + |c.im - ρ.im| := by simp only [Complex.sub_re, Complex.sub_im]
      _ ≤ 2 * η := by simpa only [himag, add_zero] using hreal
  have hclose : ‖c - ρ‖ ≤ 3 * η := by
    have hηnonneg : 0 ≤ η := le_of_lt hη
    nlinarith only [hdist, hηnonneg]
  have hball : ρ ∈ Metric.ball c |80 * η| := by
    apply Metric.mem_ball.mpr
    rw [dist_eq_norm, abs_of_pos (mul_pos (by norm_num) hη)]
    calc
      ‖ρ - c‖ = ‖c - ρ‖ := norm_sub_rev _ _
      _ ≤ 2 * η := hdist
      _ < 80 * η := by nlinarith only [hη]
  have hρ := completedLFunction_zero_mem_local_divisor_support χ hχ hball hzero
  let z : ℂ := ⟨c.re - 80 * η, c.im - 80 * η⟩
  let w : ℂ := ⟨c.re + 80 * η, c.im + 80 * η⟩
  have hSupport :
    ∀
      v ∈
        (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.ball c |80 * η|)).support,
      v ∈ dirichletCompletedLFunctionRectangleBox z w := by
    intro v hv
    have hR : 0 < 80 * η := mul_pos (by norm_num) hη
    have hv' := hv
    rw [abs_of_pos hR] at hv'
    have hsquare := completedLFunction_local_divisor_support_mem_centered_square χ c hR hv'
    simpa only [z, w] using hsquare
  have hcenter : c = ((1 + η : ℝ) : ℂ) + Complex.I * ρ.im := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
      exact hcre
    · simp only [Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, zero_mul]
      simpa only [zero_add, one_mul] using hcim
  let S : Set ℂ := {v | 80 * η ≤ ‖c - v‖}
  have hremote : ∀ v ∈ S, 8 * η ≤ ‖(((1 + η : ℝ) : ℂ) + Complex.I * ρ.im) - v‖ := by
    intro v hv
    have hv' : 80 * η ≤ ‖c - v‖ := by simpa only [S, Set.mem_ofPred_eq] using hv
    rw [← hcenter]
    have hηscale : 8 * η ≤ 80 * η := by nlinarith only [hη]
    exact le_trans hηscale hv'
  have hN : 0 < (C : ℝ) + 1 := by positivity
  obtain ⟨A, B, hA, hB, K, _, hK, htail⟩ :=
    exists_k_completed_genus_remote_reciprocal_power_le_uniform_half_near_scale hq hχ hp hinv S hη
      (by nlinarith only [hηsmall]) ρ.im hN 2 hremote
  have hblock :=
    exists_completedLFunction_local_zero_power_sum_fixed_multiple_block_of_near χ hχ hη hc ρ hρ
      hclose K z w hSupport C hcount
  refine ⟨C, K, hK, hcount, hblock, ?_⟩
  intro k hk
  simpa only [hcenter, S, Set.mem_ofPred_eq] using htail k hk

/--
Inputs: a near-one completed-function zero, a nonzero center at real part `1 + η`, and a small
positive scale.
Claim: a multiplicity-capped local power-sum block exists, and its selected order is bounded by an
explicit cutoff formed from the conductor-height inverse-square mass constants.
Proof: obtain the rectangle multiplicity cap, choose a matching-exponent remote threshold from the
global inverse-square mass bound, and apply the local fixed-multiple block theorem at that
threshold.
Role: aligns the local zero signal and remote contribution while preserving a quantitative order
bound for downstream derivative detection.
-/
theorem exists_completedLFunction_local_zero_block_with_remote_tail_matching_scale {q : ℕ}
    [NeZero q] {χ : DirichletCharacter ℂ q} (hq : 2 ≤ q) (hχ : χ ≠ 1) (hp : χ.IsPrimitive)
    (hinv : χ⁻¹ ≠ 1) {η : ℝ} (hη : 0 < η) (hηsmall : η ≤ 1 / 1288) (Kmin : ℕ) (hKmin : 2 ≤ Kmin)
    {c ρ : ℂ} (hcre : c.re = 1 + η) (hcim : c.im = ρ.im) (hρre : |ρ.re - 1| ≤ η)
    (hzero : DirichletCharacter.completedLFunction χ ρ = 0)
    (hc : DirichletCharacter.completedLFunction χ c ≠ 0) :
    ∃ A B : ℝ,
      0 < A ∧
        0 < B ∧
        ∃ C K : ℕ,
          Kmin ≤ K ∧
            K ≤ completedGenusRemoteTailUniformCutoff q η ρ.im ((C : ℝ) + 1) Kmin ∧
            2 ≤ K ∧
            completedZeroMultiplicityCountInRectangle χ hχ ⟨c.re - 80 * η, c.im - 80 * η⟩
                ⟨c.re + 80 * η, c.im + 80 * η⟩ ≤
              (C : ℝ) ∧
            ((∑ v ∈ (completedLFunction_local_zero_support_finite χ hχ c (80 * η)).toFinset,
                    (MeromorphicOn.divisor χ.completedLFunction (Metric.ball c |80 * η|) v).toNat :
                  ℕ) :
                ℝ) ≤
              (C : ℝ) ∧
            CompletedLFunctionLocalZeroPowerSumBlockData χ c η ρ K C ∧
            (∀ k : ℕ,
              K ≤ k →
                ‖∑' v : ℂ,
                      ((if 80 * η ≤ ‖c - v‖ then
                              (MeromorphicOn.divisor χ.completedLFunction Set.univ v : ℝ)
                            else 0 :
                            ℝ) :
                          ℂ) *
                        (if 80 * η ≤ ‖c - v‖ then (c - v)⁻¹ else 0) ^ k‖ ≤
                  (1 / (8 * ((C : ℝ) + 1))) * (1 / (3 * η)) ^ k) ∧
            C =
              Nat.ceil
                (completedZeroLocalLogBoundConstant *
                  (1 + 644 * η * Real.log ((q : ℝ) * (|ρ.im| + 3)))) := by
  classical
  obtain ⟨C, hcount, hblockInfo⟩ :=
    exists_completedLFunction_local_zero_power_sum_block_of_near_one_zero hq hχ hp hinv hη hηsmall
      hcre hcim hρre hzero hc 2
  obtain ⟨_, hCeq⟩ := hblockInfo
  have hreal : |c.re - ρ.re| ≤ 2 * η := by
    rw [hcre]
    have h := abs_le.mp hρre
    apply abs_le.mpr
    constructor <;> linarith only [h.1, h.2]
  have himag : |c.im - ρ.im| = 0 := by simp only [hcim, sub_self, abs_zero]
  have hdist : ‖c - ρ‖ ≤ 2 * η := by
    calc
      ‖c - ρ‖ ≤ |(c - ρ).re| + |(c - ρ).im| := Complex.norm_le_abs_re_add_abs_im _
      _ = |c.re - ρ.re| + |c.im - ρ.im| := by simp only [Complex.sub_re, Complex.sub_im]
      _ ≤ 2 * η := by simpa only [himag, add_zero] using hreal
  have hclose : ‖c - ρ‖ ≤ 3 * η := by
    have hηnonneg : 0 ≤ η := le_of_lt hη
    nlinarith only [hdist, hηnonneg]
  have hball : ρ ∈ Metric.ball c |80 * η| := by
    apply Metric.mem_ball.mpr
    rw [dist_eq_norm, abs_of_pos (mul_pos (by norm_num) hη)]
    calc
      ‖ρ - c‖ = ‖c - ρ‖ := norm_sub_rev _ _
      _ ≤ 2 * η := hdist
      _ < 80 * η := by nlinarith only [hη]
  have hρ := completedLFunction_zero_mem_local_divisor_support χ hχ hball hzero
  let z : ℂ := ⟨c.re - 80 * η, c.im - 80 * η⟩
  let w : ℂ := ⟨c.re + 80 * η, c.im + 80 * η⟩
  have hSupport :
    ∀
      v ∈
        (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.ball c |80 * η|)).support,
      v ∈ dirichletCompletedLFunctionRectangleBox z w := by
    intro v hv
    have hR : 0 < 80 * η := mul_pos (by norm_num) hη
    have hv' := hv
    rw [abs_of_pos hR] at hv'
    have hsquare := completedLFunction_local_divisor_support_mem_centered_square χ c hR hv'
    simpa only [z, w] using hsquare
  have hθ : 0 < 644 * η := by positivity
  have hθle : 644 * η ≤ 1 / 2 := by
    have := hηsmall
    nlinarith only [this]
  have hRectangle :
    ∀ u ∈ dirichletCompletedLFunctionRectangleBox z w,
      ‖u - ((1 : ℂ) + (ρ.im : ℂ) * Complex.I)‖ ≤ (644 * η) / 4 := by
    intro u hu
    change
      u.re ∈ Set.uIcc (c.re - 80 * η) (c.re + 80 * η) ∧
        u.im ∈ Set.uIcc (c.im - 80 * η) (c.im + 80 * η) at hu
    have hηnonneg : 0 ≤ η := le_of_lt hη
    have hcoords :
      c.re - 80 * η ≤ u.re ∧
        u.re ≤ c.re + 80 * η ∧ c.im - 80 * η ≤ u.im ∧ u.im ≤ c.im + 80 * η := by
      rw [Set.uIcc_of_le (by nlinarith only [hηnonneg]),
        Set.uIcc_of_le (by nlinarith only [hηnonneg])] at hu
      exact ⟨hu.1.1, hu.1.2, hu.2.1, hu.2.2⟩
    have hreal' : |u.re - 1| ≤ 81 * η := by
      have hcoords' := hcoords
      rw [hcre] at hcoords'
      rw [abs_le]
      constructor
      · nlinarith only [hcoords'.1, hηnonneg]
      · nlinarith only [hcoords'.2.1, hηnonneg]
    have himag' : |u.im - ρ.im| ≤ 80 * η := by
      rw [abs_le, ← hcim]
      constructor <;> nlinarith only [hcoords.2.2, hcoords.2.1, hηnonneg]
    calc
      ‖u - ((1 : ℂ) + (ρ.im : ℂ) * Complex.I)‖ ≤
          |(u - ((1 : ℂ) + (ρ.im : ℂ) * Complex.I)).re| +
            |(u - ((1 : ℂ) + (ρ.im : ℂ) * Complex.I)).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ = |u.re - 1| + |u.im - ρ.im| := by
        simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
          Complex.I_im, Complex.one_re, Complex.one_im, mul_zero, mul_one, sub_zero, add_zero,
          zero_add]
      _ ≤ 81 * η + 80 * η := add_le_add hreal' himag'
      _ = (644 * η) / 4 := by ring
  have hcenter : c = ((1 + η : ℝ) : ℂ) + Complex.I * ρ.im := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
      exact hcre
    · simp only [Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, zero_mul]
      simpa only [zero_add, one_mul] using hcim
  let S : Set ℂ := {v | 80 * η ≤ ‖c - v‖}
  have hremote : ∀ v ∈ S, 8 * η ≤ ‖(((1 + η : ℝ) : ℂ) + Complex.I * ρ.im) - v‖ := by
    intro v hv
    have hv' : 80 * η ≤ ‖c - v‖ := by simpa only [S, Set.mem_ofPred_eq] using hv
    rw [← hcenter]
    have hηscale : 8 * η ≤ 80 * η := by nlinarith only [hη]
    exact le_trans hηscale hv'
  have hN : 0 < (C : ℝ) + 1 := by positivity
  obtain ⟨A, B, hA, hB, K, hKmin', hKupper, hK, htail⟩ :=
    exists_k_completed_genus_remote_reciprocal_power_le_uniform_matching_scale hq hχ hp hinv S hη
      (by nlinarith only [hηsmall]) ρ.im hN Kmin hKmin hremote
  have hblock :=
    exists_completedLFunction_local_zero_power_sum_fixed_multiple_block_of_near χ hχ hη hc ρ hρ
      hclose K z w hSupport C hcount
  have hlocalMass :=
    completedLFunction_local_divisor_support_multiplicity_le_rectangle_count χ hχ c (80 * η) z w
      hSupport
  have hlocalMass' :
    ((∑ v ∈ (completedLFunction_local_zero_support_finite χ hχ c (80 * η)).toFinset,
            (MeromorphicOn.divisor χ.completedLFunction (Metric.ball c |80 * η|) v).toNat :
          ℕ) :
        ℝ) ≤
      (C : ℝ) := by
    simpa only [Nat.cast_sum] using le_trans hlocalMass hcount
  refine ⟨A, B, hA, hB, C, K, hKmin', hKupper, hK, hcount, hlocalMass', hblock, ?_, hCeq⟩
  intro k hk
  simpa only [hcenter, S, Set.mem_ofPred_eq] using htail k hk

/--
Inputs: a primitive nonprincipal completed Dirichlet `L`-function, a near-one zero, and its
matching-scale local block and remote-tail estimates.
Claim: one exponent simultaneously has a finite local power-sum lower bound and the remote-tail
upper bound, with both sums using the same power.
Proof: convert the local block's finitely supported sum to the canonical divisor support and apply
the remote estimate at the exponent selected by that block.
Role: provides the common-order input for comparing the local zero signal with the remote zeros.
-/
theorem exists_completedLFunction_local_finite_power_sum_and_remote_tail_same_order {q : ℕ}
    [NeZero q] {χ : DirichletCharacter ℂ q} (hq : 2 ≤ q) (hχ : χ ≠ 1) (hp : χ.IsPrimitive)
    (hinv : χ⁻¹ ≠ 1) {η : ℝ} (hη : 0 < η) (hηsmall : η ≤ 1 / 1288) (Kmin : ℕ) (hKmin : 2 ≤ Kmin)
    {c ρ : ℂ} (hcre : c.re = 1 + η) (hcim : c.im = ρ.im) (hρre : |ρ.re - 1| ≤ η)
    (hzero : DirichletCharacter.completedLFunction χ ρ = 0)
    (hc : DirichletCharacter.completedLFunction χ c ≠ 0) :
    ∃ A B : ℝ,
      0 < A ∧
        0 < B ∧
        ∃ C K m : ℕ,
          Kmin ≤ K ∧
            K ≤ completedGenusRemoteTailUniformCutoff q η ρ.im ((C : ℝ) + 1) Kmin ∧
            2 ≤ K ∧
            completedZeroMultiplicityCountInRectangle χ hχ ⟨c.re - 80 * η, c.im - 80 * η⟩
                ⟨c.re + 80 * η, c.im + 80 * η⟩ ≤
              (C : ℝ) ∧
            0 <
              ∑ v ∈ (completedLFunction_local_zero_support_finite χ hχ c (80 * η)).toFinset,
                (MeromorphicOn.divisor χ.completedLFunction (Metric.ball c |80 * η|) v).toNat ∧
            (∑ v ∈ (completedLFunction_local_zero_support_finite χ hχ c (80 * η)).toFinset,
                ((MeromorphicOn.divisor χ.completedLFunction (Metric.ball c |80 * η|) v).toNat :
                  ℝ)) ≤
              (C : ℝ) ∧
            K ≤ m ∧
            m ≤ K * C ∧
            (1 /
                  (4 *
                    ((∑ v ∈ (completedLFunction_local_zero_support_finite χ hχ c (80 * η)).toFinset,
                          (MeromorphicOn.divisor χ.completedLFunction (Metric.ball c |80 * η|)
                              v).toNat :
                        ℕ) :
                      ℝ)) *
                (1 / (3 * η)) ^ m ≤
              ‖∑ v ∈ (completedLFunction_local_zero_support_finite χ hχ c (80 * η)).toFinset,
                  ((MeromorphicOn.divisor χ.completedLFunction (Metric.ball c |80 * η|) v : ℤ) :
                      ℂ) *
                    (c - v)⁻¹ ^ m‖) ∧
            ‖∑' v : ℂ,
                  ((if 80 * η ≤ ‖c - v‖ then
                          (MeromorphicOn.divisor χ.completedLFunction Set.univ v : ℝ)
                        else 0 :
                        ℝ) :
                      ℂ) *
                    (if 80 * η ≤ ‖c - v‖ then (c - v)⁻¹ else 0) ^ m‖ ≤
              (1 / (8 * ((C : ℝ) + 1))) * (1 / (3 * η)) ^ m ∧
            ‖∑' v : ℂ,
                  ((if 80 * η ≤ ‖c - v‖ then
                          (MeromorphicOn.divisor χ.completedLFunction Set.univ v : ℝ)
                        else 0 :
                        ℝ) :
                      ℂ) *
                    (if 80 * η ≤ ‖c - v‖ then (c - v)⁻¹ else 0) ^ m‖ <
              ‖∑ v ∈ (completedLFunction_local_zero_support_finite χ hχ c (80 * η)).toFinset,
                  ((MeromorphicOn.divisor χ.completedLFunction (Metric.ball c |80 * η|) v : ℤ) :
                      ℂ) *
                    (c - v)⁻¹ ^ m‖ ∧
            C =
              Nat.ceil
                (completedZeroLocalLogBoundConstant *
                  (1 + 644 * η * Real.log ((q : ℝ) * (|ρ.im| + 3)))) := by
  obtain ⟨A, B, hA, hB, C, K, hKmin', hKupper, hK, hcount, hlocalMass, hblockTail⟩ :=
    exists_completedLFunction_local_zero_block_with_remote_tail_matching_scale hq hχ hp hinv hη
      hηsmall Kmin hKmin hcre hcim hρre hzero hc
  obtain ⟨hblock, htail, hCeq⟩ := hblockTail
  obtain ⟨hmasspos, m, hmK, hmKC, hlocal⟩ :=
    exists_completedLFunction_local_zero_block_on_finite_support χ hχ K C hblock
  have hmass' :
    (∑ v ∈ (completedLFunction_local_zero_support_finite χ hχ c (80 * η)).toFinset,
        ((MeromorphicOn.divisor χ.completedLFunction (Metric.ball c |80 * η|) v).toNat : ℝ)) ≤
      (C : ℝ) := by
    simpa only [Nat.cast_sum] using hlocalMass
  let M :=
    ∑ v ∈ (completedLFunction_local_zero_support_finite χ hχ c (80 * η)).toFinset,
      (MeromorphicOn.divisor χ.completedLFunction (Metric.ball c |80 * η|) v).toNat
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by simpa only [M] using hmasspos)
  have hMle : (M : ℝ) ≤ (C : ℝ) := by simpa only [M, Nat.cast_sum] using hmass'
  have hdenC : 0 < 8 * ((C : ℝ) + 1) := by positivity
  have hdenM : 0 < 4 * (M : ℝ) := by positivity
  have hcoeff : 1 / (8 * ((C : ℝ) + 1)) < 1 / (4 * (M : ℝ)) := by
    apply (div_lt_div_iff₀ hdenC hdenM).2
    nlinarith only [hMle]
  have hx : 0 < 1 / (3 * η) := by positivity
  have hstrict :
    (1 / (8 * ((C : ℝ) + 1))) * (1 / (3 * η)) ^ m < 1 / (4 * (M : ℝ)) * (1 / (3 * η)) ^ m :=
    mul_lt_mul_of_pos_right hcoeff (pow_pos hx m)
  have hlocal' :
    1 / (4 * (M : ℝ)) * (1 / (3 * η)) ^ m ≤
      ‖∑ v ∈ (completedLFunction_local_zero_support_finite χ hχ c (80 * η)).toFinset,
          ((MeromorphicOn.divisor χ.completedLFunction (Metric.ball c |80 * η|) v : ℤ) : ℂ) *
            (c - v)⁻¹ ^ m‖ := by
    simpa only [M] using hlocal
  have hremote := htail m hmK
  exact
    ⟨A, B, hA, hB, C, K, m, hKmin', hKupper, hK, hcount, hmasspos, hmass', hmK, hmKC, hlocal,
      hremote, lt_of_le_of_lt hremote (lt_of_lt_of_le hstrict hlocal'), hCeq⟩

/--
Inputs: a primitive nonprincipal completed Dirichlet `L`-function, a zero close to `1`, and a
nonzero center immediately to its right.
Claim: some derivative order in the fixed-multiple block has an explicit positive lower bound in
terms of the rectangle multiplicity cap and the local scale.
Proof: combine the local power-sum lower bound and remote-tail upper bound in the finite-complement
identity, then apply the reverse triangle inequality with the factorial coefficient retained.
Role: supplies a quantitative completed logarithmic-derivative detector for later density work.
-/
theorem exists_completedLFunction_iteratedDerivWithin_logDeriv_lower_bound_near_one_zero {q : ℕ}
    [NeZero q] {χ : DirichletCharacter ℂ q} (hq : 2 ≤ q) (hχ : χ ≠ 1) (hp : χ.IsPrimitive)
    (hinv : χ⁻¹ ≠ 1) {η : ℝ} (hη : 0 < η) (hηsmall : η ≤ 1 / 1288) (Kmin : ℕ) (hKmin : 2 ≤ Kmin)
    {c ρ : ℂ} (hcre : c.re = 1 + η) (hcim : c.im = ρ.im) (hρre : |ρ.re - 1| ≤ η)
    (hzero : DirichletCharacter.completedLFunction χ ρ = 0)
    (hc : DirichletCharacter.completedLFunction χ c ≠ 0) :
    ∃ massConstA massConstB : ℝ,
      0 < massConstA ∧
        0 < massConstB ∧
        ∃ C K m n : ℕ,
          Kmin ≤ K ∧
            K ≤ completedGenusRemoteTailUniformCutoff q η ρ.im ((C : ℝ) + 1) Kmin ∧
            2 ≤ K ∧
            completedZeroMultiplicityCountInRectangle χ hχ ⟨c.re - 80 * η, c.im - 80 * η⟩
                ⟨c.re + 80 * η, c.im + 80 * η⟩ ≤
              (C : ℝ) ∧
            0 < n ∧
            n + 1 = m ∧
            K ≤ m ∧
            m ≤ K * C ∧
            (1 / (8 * ((C : ℝ) + 1))) * (1 / (3 * η)) ^ m * (n.factorial : ℝ) ≤
              ‖iteratedDerivWithin n (fun z : ℂ => logDeriv χ.completedLFunction z)
                  {z : ℂ | 1 < z.re} c‖ ∧
            C =
              Nat.ceil
                (completedZeroLocalLogBoundConstant *
                  (1 + 644 * η * Real.log ((q : ℝ) * (|ρ.im| + 3)))) := by
  obtain
    ⟨massConstA, massConstB, hmassConstA, hmassConstB, C, K, m, hKmin', hKupper, hK, hcount,
      hmasspos, hmass, hmK, hmKC, hlocal, hremote, hgap, hCeq⟩ :=
    exists_completedLFunction_local_finite_power_sum_and_remote_tail_same_order hq hχ hp hinv hη
      hηsmall Kmin hKmin hcre hcim hρre hzero hc
  have hmTwo : 2 ≤ m := le_trans hK hmK
  have hmPositive : 0 < m := by omega
  let n := m - 1
  have hn : 0 < n := by
    dsimp only [n]; omega
  have hnm : n + 1 = m := by
    dsimp only [n]; omega
  have hcRight : 1 < c.re := by
    rw [hcre]; linarith only [hη]
  let S := (completedLFunction_local_zero_support_finite χ hχ c (80 * η)).toFinset
  let A : ℂ := (-1 : ℂ) ^ n * (n.factorial : ℂ)
  let L : ℂ :=
    ∑ v ∈ S,
      ((MeromorphicOn.divisor χ.completedLFunction (Metric.ball c |80 * η|) v : ℤ) : ℂ) *
        (c - v)⁻¹ ^ m
  let R : ℂ :=
    ∑' v : ℂ,
      ((if 80 * η ≤ ‖c - v‖ then (MeromorphicOn.divisor χ.completedLFunction Set.univ v : ℝ)
            else 0 :
            ℝ) :
          ℂ) *
        (if 80 * η ≤ ‖c - v‖ then (c - v)⁻¹ else 0) ^ m
  have hsplit :=
    iteratedDerivWithin_logDeriv_eq_local_divisor_sum_add_complement hq hχ hp hinv hcRight (80 * η)
      n hn
  have hlocalFactor :
    (∑ v ∈ S,
        (MeromorphicOn.divisor χ.completedLFunction (Metric.ball c |80 * η|) v : ℂ) *
          ((-1 : ℂ) ^ n * (n.factorial : ℂ) * (c - v) ^ (-1 - (n : ℕ) : ℤ))) =
      A * L := by
    have hfactor :=
      completedLFunction_local_divisor_power_sum_factorization χ hχ (c := c) (80 * η) n
    simpa only [S, A, L, hnm] using hfactor
  have hexp : (-1 : ℤ) - (n : ℤ) = Int.negSucc n := by
    rw [Int.negSucc_eq]
    ring
  have hcomplementFactor :
    (∑' (v : { v : ℂ // v ∉ S }),
        (MeromorphicOn.divisor χ.completedLFunction Set.univ v : ℂ) *
          ((-1 : ℂ) ^ n * (n.factorial : ℂ) * (c - v) ^ (-1 - (n : ℕ) : ℤ))) =
      A *
        ∑' (v : { v : ℂ // v ∉ S }),
          (MeromorphicOn.divisor χ.completedLFunction Set.univ v : ℂ) * (c - v)⁻¹ ^ m := by
    calc
      _ =
          ∑' v : { v : ℂ // v ∉ S },
            A * ((MeromorphicOn.divisor χ.completedLFunction Set.univ v : ℂ) * (c - v)⁻¹ ^ m) :=
        by
        apply tsum_congr
        intro v
        rw [hexp, zpow_negSucc, inv_pow, ← hnm]
        dsimp only [A]
        ring
      _ =
          A *
            ∑' (v : { v : ℂ // v ∉ S }),
              (MeromorphicOn.divisor χ.completedLFunction Set.univ v : ℂ) * (c - v)⁻¹ ^ m :=
        tsum_mul_left
  have hremoteEq := completedLFunction_local_support_complement_eq_remote_power_sum χ hχ c hη m
  have hderiv :
    iteratedDerivWithin n (fun z : ℂ => logDeriv χ.completedLFunction z) {z : ℂ | 1 < z.re} c =
      A * (L + R) := by
    calc
      _ =
          (∑ v ∈ S,
              (MeromorphicOn.divisor χ.completedLFunction (Metric.ball c |80 * η|) v : ℂ) *
                ((-1 : ℂ) ^ n * (n.factorial : ℂ) * (c - v) ^ (-1 - (n : ℕ) : ℤ))) +
            ∑' (v : { v : ℂ // v ∉ S }),
              (MeromorphicOn.divisor χ.completedLFunction Set.univ v : ℂ) *
                ((-1 : ℂ) ^ n * (n.factorial : ℂ) * (c - v) ^ (-1 - (n : ℕ) : ℤ)) :=
        hsplit
      _ = A * L + A * R := by rw [hlocalFactor, hcomplementFactor, hremoteEq]
      _ = A * (L + R) := by ring
  let M := ∑ v ∈ S, (MeromorphicOn.divisor χ.completedLFunction (Metric.ball c |80 * η|) v).toNat
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by simpa only [M, S] using hmasspos)
  have hMle : (M : ℝ) ≤ (C : ℝ) := by simpa only [M, S, Nat.cast_sum] using hmass
  have hdenM : 0 < 4 * (M : ℝ) := by positivity
  have hdenC : 0 < 4 * ((C : ℝ) + 1) := by positivity
  have hcoeff : 1 / (4 * ((C : ℝ) + 1)) ≤ 1 / (4 * (M : ℝ)) := by
    apply (div_le_div_iff₀ hdenC hdenM).2
    nlinarith only [hMle]
  have hx : 0 < 1 / (3 * η) := by positivity
  have hlocal' : (1 / (4 * ((C : ℝ) + 1))) * (1 / (3 * η)) ^ m ≤ ‖L‖ := by
    calc
      _ ≤ (1 / (4 * (M : ℝ))) * (1 / (3 * η)) ^ m :=
        mul_le_mul_of_nonneg_right hcoeff (pow_nonneg (le_of_lt hx) m)
      _ ≤ ‖L‖ := by simpa only [M, S] using hlocal
  have hAnorm : ‖A‖ = (n.factorial : ℝ) := by
    dsimp only [A]
    rw [norm_mul, norm_pow, norm_neg, norm_one, Complex.norm_natCast]
    simp only [one_pow, one_mul]
  let B := (1 / (8 * ((C : ℝ) + 1))) * (1 / (3 * η)) ^ m
  have herror : ‖A * R‖ ≤ (n.factorial : ℝ) * B := by
    rw [norm_mul, hAnorm]
    exact mul_le_mul_of_nonneg_left hremote (by positivity)
  have hdecomp :
    iteratedDerivWithin n (fun z : ℂ => logDeriv χ.completedLFunction z) {z : ℂ | 1 < z.re} c =
      A * L + A * R := by
    rw [hderiv]
    ring
  have hderivLower := norm_derivative_lower_bound_of_zero_sum_decomposition hdecomp hlocal' herror
  have hboundEq :
    B * (n.factorial : ℝ) =
      ((1 / (4 * ((C : ℝ) + 1))) * (1 / (3 * η)) ^ m) * (n.factorial : ℝ) -
        (n.factorial : ℝ) * B := by
    dsimp only [B]
    field_simp [ne_of_gt hη, ne_of_gt (show 0 < (C : ℝ) + 1 by positivity)]; ring
  refine
    ⟨massConstA, massConstB, hmassConstA, hmassConstB, C, K, m, n, hKmin', hKupper, hK, hcount, hn,
      hnm, hmK, hmKC, ?_, hCeq⟩
  calc
    _ = B * (n.factorial : ℝ) := by rfl
    _ =
        ((1 / (4 * ((C : ℝ) + 1))) * (1 / (3 * η)) ^ m) * (n.factorial : ℝ) -
          (n.factorial : ℝ) * B :=
      hboundEq
    _ ≤ _ := hderivLower

/--
Inputs: a primitive nonprincipal completed Dirichlet `L`-function, a zero close to `1`, and a
nonzero center immediately to its right.
Claim: some ordinary iterated derivative of the completed logarithmic derivative has an explicit
positive lower bound, with its order related to the selected power exponent by `n + 1 = m`.
Proof: transfer the half-plane iterated derivative bound to the ordinary derivative using
analyticity of the logarithmic derivative and uniqueness of derivatives on the open half-plane.
Role: exposes the quantitative zero detector in the ordinary derivative form needed by density
estimates.
-/
theorem exists_completedLFunction_iteratedDeriv_logDeriv_lower_bound_near_one_zero {q : ℕ}
    [NeZero q] {χ : DirichletCharacter ℂ q} (hq : 2 ≤ q) (hχ : χ ≠ 1) (hp : χ.IsPrimitive)
    (hinv : χ⁻¹ ≠ 1) {η : ℝ} (hη : 0 < η) (hηsmall : η ≤ 1 / 1288) (Kmin : ℕ) (hKmin : 2 ≤ Kmin)
    {c ρ : ℂ} (hcre : c.re = 1 + η) (hcim : c.im = ρ.im) (hρre : |ρ.re - 1| ≤ η)
    (hzero : DirichletCharacter.completedLFunction χ ρ = 0)
    (hc : DirichletCharacter.completedLFunction χ c ≠ 0) :
    ∃ massConstA massConstB : ℝ,
      0 < massConstA ∧
        0 < massConstB ∧
        ∃ C K m n : ℕ,
          Kmin ≤ K ∧
            K ≤ completedGenusRemoteTailUniformCutoff q η ρ.im ((C : ℝ) + 1) Kmin ∧
            2 ≤ K ∧
            completedZeroMultiplicityCountInRectangle χ hχ ⟨c.re - 80 * η, c.im - 80 * η⟩
                ⟨c.re + 80 * η, c.im + 80 * η⟩ ≤
              (C : ℝ) ∧
            0 < n ∧
            n + 1 = m ∧
            K ≤ m ∧
            m ≤ K * C ∧
            (1 / (8 * ((C : ℝ) + 1))) * (1 / (3 * η)) ^ m * (n.factorial : ℝ) ≤
              ‖iteratedDeriv n (fun z : ℂ => logDeriv χ.completedLFunction z) c‖ ∧
            (η ^ (n + 1) / (n.factorial : ℝ)) *
                ‖iteratedDeriv n (fun z : ℂ => logDeriv χ.completedLFunction z) c‖ ≥
              (1 / (8 * ((C : ℝ) + 1))) * (1 / 3 : ℝ) ^ m ∧
            C =
              Nat.ceil
                (completedZeroLocalLogBoundConstant *
                  (1 + 644 * η * Real.log ((q : ℝ) * (|ρ.im| + 3)))) := by
  obtain
    ⟨massConstA, massConstB, hmassConstA, hmassConstB, C, K, m, n, hKmin', hKupper, hK, hcount, hn,
      hnm, hmK, hmKC, hboundPair⟩ :=
    exists_completedLFunction_iteratedDerivWithin_logDeriv_lower_bound_near_one_zero hq hχ hp hinv
      hη hηsmall Kmin hKmin hcre hcim hρre hzero hc
  obtain ⟨hbound, hCeq⟩ := hboundPair
  let U : Set ℂ := {z : ℂ | 1 < z.re}
  have hcU : c ∈ U := by
    rw [Set.mem_ofPred_eq, hcre]
    linarith only [hη]
  have hopen : IsOpen U := by exact isOpen_lt continuous_const Complex.continuous_re
  have hU : UniqueDiffOn ℂ U := hopen.uniqueDiffOn
  have hlog : AnalyticAt ℂ (fun z : ℂ => logDeriv χ.completedLFunction z) c := by
    rw [logDeriv]
    have hF := (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt c
    exact hF.deriv.div hF hc
  have hcont : ContDiffAt ℂ n (fun z : ℂ => logDeriv χ.completedLFunction z) c := hlog.contDiffAt
  have hderivEq :
    iteratedDerivWithin n (fun z : ℂ => logDeriv χ.completedLFunction z) U c =
      iteratedDeriv n (fun z : ℂ => logDeriv χ.completedLFunction z) c :=
    iteratedDerivWithin_eq_iteratedDeriv hU hcont hcU
  refine
    ⟨massConstA, massConstB, hmassConstA, hmassConstB, C, K, m, n, hKmin', hKupper, hK, hcount, hn,
      hnm, hmK, hmKC, ?_, ?_, hCeq⟩
  · rw [← hderivEq]
    exact hbound
  · have hscale : 0 ≤ η ^ (n + 1) / (n.factorial : ℝ) := by positivity
    have hscaled := mul_le_mul_of_nonneg_left hbound hscale
    have hscaledNorm :
      (η ^ (n + 1) / (n.factorial : ℝ)) *
          ‖iteratedDerivWithin n (fun z : ℂ => logDeriv χ.completedLFunction z) U c‖ ≥
        (1 / (8 * ((C : ℝ) + 1))) * (1 / 3 : ℝ) ^ m := by
      rw [hnm]
      calc
        (1 / (8 * ((C : ℝ) + 1))) * (1 / 3 : ℝ) ^ m =
            (η ^ m / (n.factorial : ℝ)) *
              ((1 / (8 * ((C : ℝ) + 1))) * (1 / (3 * η)) ^ m * (n.factorial : ℝ)) :=
          by
          field_simp [ne_of_gt hη, ne_of_gt (show 0 < (C : ℝ) + 1 by positivity),
            ne_of_gt (Nat.cast_pos.mpr (Nat.factorial_pos n))]
          rw [← mul_pow]
          rw [show η * (1 / (3 * η)) = (1 / 3 : ℝ) by field_simp [ne_of_gt hη]]
        _ ≤
            (η ^ m / (n.factorial : ℝ)) *
              ‖iteratedDerivWithin n (fun z : ℂ => logDeriv χ.completedLFunction z) U c‖ :=
          by
          rw [hnm] at hscaled
          simpa only [U] using hscaled
    rw [← hderivEq]
    exact hscaledNorm

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity
