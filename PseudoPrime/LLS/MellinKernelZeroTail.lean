/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.MellinKernelZeros
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LocalZeroCount
public import PseudoPrime.Analysis.QuadraticDecaySeries

/-!
# Conductor-uniform tails of general Mellin-kernel zero sums

Local zero counts and quadratic kernel decay give summable bounds in integer height bins.
Their conductor coefficient has arbitrarily small tails; logarithmic height errors add
only a fixed constant. Large conductors absorb that constant.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements.MellinKernel

/-- For a nonprincipal character and a positive quadratic kernel-decay constant C, each
absolute divisor-weighted kernel term is at most 3C times its multiplicity divided by the
quadratic denominator of the integer floor of its height. Entire completion makes the
divisor nonnegative, and the floor distance transfers decay to the bin denominator.
This is the pointwise input for local zero-count comparisons. -/
theorem norm_kernelZeroTerm_le_height_bin (K : MellinKernel) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hne : χ ≠ 1) {C : ℝ} (hC : 0 < C)
    (hb : ∀ t : ℝ, ‖K.function (Complex.I * t)‖ ≤ C / (1 + t ^ 2)) (ρ : ℂ) :
    ‖K.kernelZeroTerm χ ρ‖ ≤
      (3 * C / (1 + ((⌊ρ.im⌋ : ℤ) : ℝ) ^ 2)) *
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) := by
  let D := MeromorphicOn.divisor χ.completedLFunction Set.univ ρ
  have ha : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := fun z _ ↦
    (DirichletCharacter.differentiable_completedLFunction hne).analyticAt z
  have hn : (0 : ℝ) ≤ D := by exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg ha ρ
  have hd :=
    Analysis.quadraticDenominator_le_of_dist_le_one (Analysis.abs_sub_int_floor_le_one ρ.im)
  have hx : 0 < 1 + ρ.im ^ 2 := by nlinarith only [sq_nonneg ρ.im]
  have hy : 0 < 1 + ((⌊ρ.im⌋ : ℤ) : ℝ) ^ 2 := by nlinarith only [sq_nonneg (((⌊ρ.im⌋ : ℤ) : ℝ))]
  have hdec : C / (1 + ρ.im ^ 2) ≤ 3 * C / (1 + ((⌊ρ.im⌋ : ℤ) : ℝ) ^ 2) := by
    rw [div_le_div_iff₀ hx hy]
    have hm := mul_le_mul_of_nonneg_left hd hC.le
    nlinarith only [hm]
  change ‖(D : ℂ) * K.function (Complex.I * ρ.im)‖ ≤ _ * (D : ℝ)
  rw [norm_mul, Complex.norm_intCast, abs_of_nonneg hn]
  exact (mul_le_mul_of_nonneg_left ((hb ρ.im).trans hdec) hn).trans_eq (mul_comm _ _)

/-- For a nonprincipal character, the finite absolute kernel sum in one integer height bin
is bounded by its total multiplicity times the bin's quadratic decay coefficient.
Sum the pointwise bound and identify each floor index with the fixed bin.
This separates kernel decay from the local count of completed zeros. -/
theorem sum_norm_kernelZeroTerm_height_bin_le (K : MellinKernel) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hne : χ ≠ 1) {C : ℝ} (hC : 0 < C)
    (hb : ∀ t : ℝ, ‖K.function (Complex.I * t)‖ ≤ C / (1 + t ^ 2)) (S : Finset ℂ) (k : ℤ) :
    ∑ ρ ∈ S.filter (fun ρ ↦ ⌊ρ.im⌋ = k), ‖K.kernelZeroTerm χ ρ‖ ≤
      (3 * C / (1 + (k : ℝ) ^ 2)) *
        ∑ ρ ∈ S.filter (fun ρ ↦ ⌊ρ.im⌋ = k),
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ρ hρ
  have he := (Finset.mem_filter.mp hρ).2
  have h := norm_kernelZeroTerm_le_height_bin K hne hC hb ρ
  rwa [he] at h

/-- Every Mellin kernel admits positive decay and height-error constants such that, for
primitive nonprincipal characters satisfying individual RH at modulus q >= 2, each finite
absolute kernel zero sum is bounded by its occupied integer-bin estimates.
Partition by the floor of the imaginary part, compare kernel terms with multiplicities,
and apply the uniform local zero-count theorem. Both constants are independent of q and chi. -/
theorem exists_uniform_finite_kernelZeroSum_height_bins (K : MellinKernel) :
    ∃ C A : ℝ,
      0 < C ∧
        0 < A ∧
        ∀ (q : ℕ) [NeZero q],
          2 ≤ q →
            ∀ (χ : DirichletCharacter ℂ q),
              AnalyticNumberTheory.GRH.DirichletRiemannHypothesis χ →
                χ.IsPrimitive →
                χ ≠ 1 →
                χ⁻¹ ≠ 1 →
                ∀ S : Finset ℂ,
                  ∑ ρ ∈ S, ‖K.kernelZeroTerm χ ρ‖ ≤
                    ∑ k ∈ S.image (fun ρ ↦ (⌊ρ.im⌋ : ℤ)),
                      (3 * C / (1 + (k : ℝ) ^ 2)) *
                        (Real.log q + 2 * A * (Real.log (4 + |(k : ℝ)|) + 1)) := by
  classical
  obtain ⟨C, hC, hbC⟩ := exists_vertical_decay_bound K
  obtain ⟨A, hA, hbA⟩ :=
    AnalyticNumberTheory.DirichletLFunction.exists_uniform_local_zeroMultiplicity_bound
  refine ⟨C, A, hC, hA, ?_⟩
  intro q _ hq χ hRH hp hne hinv S
  have he :=
    Finset.sum_fiberwise_of_maps_to (s := S) (t := S.image (fun ρ : ℂ ↦ (⌊ρ.im⌋ : ℤ)))
      (fun ρ hρ ↦ Finset.mem_image_of_mem (fun z : ℂ ↦ (⌊z.im⌋ : ℤ)) hρ)
      (fun ρ : ℂ ↦ ‖K.kernelZeroTerm χ ρ‖)
  rw [← he]
  apply Finset.sum_le_sum
  intro k _
  have hz :=
    hbA q hq χ hRH hp hne hinv (k : ℝ) (S.filter (fun ρ ↦ (⌊ρ.im⌋ : ℤ) = k)) (fun ρ hρ ↦ ?_)
  · have hn : 0 ≤ 3 * C / (1 + (k : ℝ) ^ 2) :=
      div_nonneg (mul_nonneg (by norm_num only) hC.le) (by nlinarith only [sq_nonneg (k : ℝ)])
    exact
      (sum_norm_kernelZeroTerm_height_bin_le K hne hC hbC S k).trans
        (mul_le_mul_of_nonneg_left hz hn)
  · have hk := (Finset.mem_filter.mp hρ).2
    rw [← hk]
    exact Analysis.abs_sub_int_floor_le_one ρ.im

/-- For every Mellin kernel and epsilon > 0, a positive height cutoff and positive additive
constant work uniformly for all primitive nonprincipal characters satisfying individual RH.
Every finite zero set above the cutoff has absolute kernel sum at most epsilon log q plus
the additive constant. Choose small inverse-quadratic tails for the conductor coefficient;
the summable logarithmic height weights bound the remaining error.
This prepares the infinite tail estimate needed to approximate kernel mass by compact tests. -/
theorem exists_uniform_finite_kernelZeroSum_tail_le (K : MellinKernel) {ε : ℝ} (hε : 0 < ε) :
    ∃ T B : ℝ,
      0 < T ∧
        0 < B ∧
        ∀ (q : ℕ) [NeZero q],
          2 ≤ q →
            ∀ (χ : DirichletCharacter ℂ q),
              AnalyticNumberTheory.GRH.DirichletRiemannHypothesis χ →
                χ.IsPrimitive →
                χ ≠ 1 →
                χ⁻¹ ≠ 1 →
                ∀ S : Finset ℂ,
                  (∀ ρ ∈ S, T ≤ |ρ.im|) → ∑ ρ ∈ S, ‖K.kernelZeroTerm χ ρ‖ ≤ ε * Real.log q + B := by
  classical
  obtain ⟨C, A, hC, hA, hb⟩ := exists_uniform_finite_kernelZeroSum_height_bins K
  have h3C : 0 < 3 * C := mul_pos (by norm_num only) hC
  obtain ⟨I, hI⟩ := Analysis.exists_int_quadratic_finite_tail_lt (div_pos hε h3C)
  let T : ℝ := 2 + ∑ k ∈ I, |(k : ℝ)|
  let V : ℝ := ∑' k : ℤ, (Real.log (4 + |(k : ℝ)|) + 1) / (1 + (k : ℝ) ^ 2)
  have hV : 0 ≤ V :=
    tsum_nonneg
      (fun k ↦
        div_nonneg
          (add_nonneg (Real.log_nonneg (by linarith only [abs_nonneg (k : ℝ)])) zero_le_one)
          (by nlinarith only [sq_nonneg (k : ℝ)]))
  have hcoef : 0 ≤ 6 * C * A := mul_nonneg (mul_nonneg (by norm_num only) hC.le) hA.le
  have hT : 0 < T := by
    have hn := Finset.sum_nonneg (fun k (_ : k ∈ I) ↦ abs_nonneg (k : ℝ))
    dsimp only [T]
    linarith only [hn]
  refine ⟨T, 6 * C * A * V + 1, hT, by linarith only [mul_nonneg hcoef hV], ?_⟩
  intro q _ hq χ hRH hp hne hinv S hS
  let J := S.image (fun ρ : ℂ ↦ (⌊ρ.im⌋ : ℤ))
  have hdis : Disjoint J I := by
    apply Finset.disjoint_left.mpr
    intro k hk hki
    obtain ⟨ρ, hρ, he⟩ := Finset.mem_image.mp hk
    have hki' : |(k : ℝ)| ≤ ∑ j ∈ I, |(j : ℝ)| :=
      Finset.single_le_sum (fun (j : ℤ) _ ↦ abs_nonneg (j : ℝ)) hki
    have hdelta := Analysis.abs_sub_int_floor_le_one ρ.im
    have hab : |ρ.im| ≤ 1 + |(k : ℝ)| := by
      rw [← he]
      calc
        |ρ.im| = |(ρ.im - (⌊ρ.im⌋ : ℝ)) + (⌊ρ.im⌋ : ℝ)| := congrArg abs (sub_add_cancel _ _).symm
        _ ≤ |ρ.im - (⌊ρ.im⌋ : ℝ)| + |(⌊ρ.im⌋ : ℝ)| := by
          simpa only [Real.norm_eq_abs] using norm_add_le (ρ.im - (⌊ρ.im⌋ : ℝ)) (⌊ρ.im⌋ : ℝ)
        _ ≤ _ := add_le_add hdelta le_rfl
    have hs := hS ρ hρ
    dsimp only [T] at hs
    linarith only [hs, hab, hki']
  have hu := (lt_div_iff₀ h3C).mp (hI J hdis)
  have hv : ∑ k ∈ J, (Real.log (4 + |(k : ℝ)|) + 1) / (1 + (k : ℝ) ^ 2) ≤ V :=
    Analysis.summable_int_logWeighted_quadratic.sum_le_tsum J
      (fun k _ ↦
        div_nonneg
          (add_nonneg (Real.log_nonneg (by linarith only [abs_nonneg (k : ℝ)])) zero_le_one)
          (by nlinarith only [sq_nonneg (k : ℝ)]))
  have hql : 0 ≤ Real.log q :=
    Real.log_nonneg
      (by
        have hr : (2 : ℝ) ≤ q := by exact_mod_cast hq
        linarith only [hr])
  have huq := mul_le_mul_of_nonneg_right hu.le hql
  have hvq := mul_le_mul_of_nonneg_left hv hcoef
  have hsplit :
    ∑ k ∈ J, (3 * C / (1 + (k : ℝ) ^ 2)) * (Real.log q + 2 * A * (Real.log (4 + |(k : ℝ)|) + 1)) =
      3 * C * Real.log q * ∑ k ∈ J, 1 / (1 + (k : ℝ) ^ 2) +
        6 * C * A * ∑ k ∈ J, (Real.log (4 + |(k : ℝ)|) + 1) / (1 + (k : ℝ) ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hfinite := hb q hq χ hRH hp hne hinv S
  change
    ∑ ρ ∈ S, ‖K.kernelZeroTerm χ ρ‖ ≤
      ∑ k ∈ J,
        (3 * C / (1 + (k : ℝ) ^ 2)) *
          (Real.log q + 2 * A * (Real.log (4 + |(k : ℝ)|) + 1)) at hfinite
  rw [hsplit] at hfinite
  nlinarith only [hfinite, huq, hvq]

/-- For a Mellin kernel and epsilon > 0, the full absolute kernel zero sum restricted to
heights above a suitable positive cutoff is at most epsilon log q plus a fixed positive
constant, uniformly over primitive nonprincipal characters with individual RH and q >= 2.
Filter each finite zero set by the cutoff, apply the finite estimate, and pass to the
nonnegative infinite sum. This controls the noncompact part of sharp kernel-mass bounds. -/
theorem exists_uniform_kernelZeroSum_tail_le (K : MellinKernel) {ε : ℝ} (hε : 0 < ε) :
    ∃ T B : ℝ,
      0 < T ∧
        0 < B ∧
        ∀ (q : ℕ) [NeZero q],
          2 ≤ q →
            ∀ (χ : DirichletCharacter ℂ q),
              AnalyticNumberTheory.GRH.DirichletRiemannHypothesis χ →
                χ.IsPrimitive →
                χ ≠ 1 →
                χ⁻¹ ≠ 1 →
                (∑' ρ : ℂ, if T ≤ |ρ.im| then ‖K.kernelZeroTerm χ ρ‖ else 0) ≤
                  ε * Real.log q + B := by
  classical
  obtain ⟨T, B, hT, hB, hb⟩ := exists_uniform_finite_kernelZeroSum_tail_le K hε
  refine ⟨T, B, hT, hB, ?_⟩
  intro q _ hq χ hRH hp hne hinv
  apply Real.tsum_le_of_sum_le (fun ρ ↦ ite_nonneg (norm_nonneg _) le_rfl)
  intro S
  have hs :=
    hb q hq χ hRH hp hne hinv (S.filter (fun ρ ↦ T ≤ |ρ.im|))
      (fun ρ hρ ↦ (Finset.mem_filter.mp hρ).2)
  simpa only [Finset.sum_filter] using hs

/-- For every Mellin kernel and epsilon > 0, a positive height cutoff and a modulus threshold
make the full absolute kernel zero tail at most epsilon log q, uniformly over primitive
nonprincipal characters satisfying individual RH. Use half epsilon in the additive tail
bound and let log q absorb its fixed error constant.
This supplies conductor-uniform small tails for the kernel's integral-mass asymptotics. -/
theorem exists_uniform_kernelZeroSum_tail_le_log (K : MellinKernel) {ε : ℝ} (hε : 0 < ε) :
    ∃ (T : ℝ) (Q : ℕ),
      0 < T ∧
        2 ≤ Q ∧
        ∀ (q : ℕ) [NeZero q],
          Q ≤ q →
            ∀ (χ : DirichletCharacter ℂ q),
              AnalyticNumberTheory.GRH.DirichletRiemannHypothesis χ →
                χ.IsPrimitive →
                χ ≠ 1 →
                χ⁻¹ ≠ 1 →
                (∑' ρ : ℂ, if T ≤ |ρ.im| then ‖K.kernelZeroTerm χ ρ‖ else 0) ≤ ε * Real.log q := by
  classical
  obtain ⟨T, B, hT, _, hb⟩ :=
    exists_uniform_kernelZeroSum_tail_le K (show 0 < ε / 2 by linarith only [hε])
  have hl :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop
      (2 * B / ε)
  obtain ⟨Q, hQ⟩ := Filter.eventually_atTop.mp hl
  refine ⟨T, max 2 Q, hT, Nat.le_max_left _ _, ?_⟩
  intro q _ hq χ hRH hp hne hinv
  have hq2 : 2 ≤ q := (Nat.le_max_left 2 Q).trans hq
  have hqQ : Q ≤ q := (Nat.le_max_right 2 Q).trans hq
  have hlarge := (div_le_iff₀ hε).mp (hQ q hqQ)
  simp only [Function.comp_apply] at hlarge
  have htail := hb q hq2 χ hRH hp hne hinv
  nlinarith only [hlarge, htail]

end PseudoPrime.LLS.PaperStatements.MellinKernel
