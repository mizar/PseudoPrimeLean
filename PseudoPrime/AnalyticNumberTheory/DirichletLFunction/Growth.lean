/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import PseudoPrime.AnalyticNumberTheory.Gamma.GrowthElementary
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.Growth
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.VerticalGrowth

/-!
# Boundedness of partial Dirichlet character sums

This file records the elementary fact that partial sums `∑_{k=1}^n χ(k)` of a nontrivial
Dirichlet character are bounded (uniformly in `n`), by periodicity plus
`MulChar.sum_eq_zero_of_ne_one`. This is the input replacing the linearly-growing `⌊t⌋` term
in the classical zeta Euler-Maclaurin
argument with a bounded one for `L(s, χ)`, `χ` nonprincipal,
letting a single level of Abel summation give a growth bound valid on `Re s > 0` (no sawtooth
refinement needed).
-/

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

namespace PrimitiveLFunctionGrowthInternal

variable {N : ℕ} [NeZero N]

/-- `N` consecutive naturals starting at `a + 1` map bijectively onto `ZMod N`. -/
theorem bijOn_natCast_add_one_add (a : ℕ) :
    Set.BijOn (fun j : ℕ => ((a + 1 + j : ℕ) : ZMod N)) (Finset.range N) Set.univ := by
  refine ⟨fun j _ => Set.mem_univ _, ?_, ?_⟩
  · intro j₁ hj₁ j₂ hj₂ heq
    simp only [Finset.coe_range, Set.mem_Iio] at hj₁ hj₂
    have heq' : ((j₁ : ℕ) : ZMod N) = ((j₂ : ℕ) : ZMod N) := by
      have hcast : ((a + 1 + j₁ : ℕ) : ZMod N) = ((a + 1 + j₂ : ℕ) : ZMod N) := heq
      push_cast at hcast
      linear_combination hcast
    have hmod : j₁ ≡ j₂ [MOD N] := (ZMod.natCast_eq_natCast_iff j₁ j₂ N).mp heq'
    exact Nat.ModEq.eq_of_lt_of_lt hmod hj₁ hj₂
  · intro c _
    refine ⟨(c - (a + 1 : ZMod N)).val, ?_, ?_⟩
    · simp only [Finset.coe_range, Set.mem_Iio]
      exact ZMod.val_lt _
    · change ((a + 1 + (c - (a + 1 : ZMod N)).val : ℕ) : ZMod N) = c
      have hcast :
        ((a + 1 + (c - (a + 1 : ZMod N)).val : ℕ) : ZMod N) =
          (a + 1 : ZMod N) + (((c - (a + 1 : ZMod N)).val : ℕ) : ZMod N) := by
        push_cast; ring
      rw [hcast, ZMod.natCast_rightInverse (c - (a + 1 : ZMod N))]
      ring

/-- Sum over any block of `N` consecutive naturals (indices `a+1, …, a+N`) of a nontrivial
character vanishes. -/
theorem sum_Icc_add_one_add_eq_zero {ψ : DirichletCharacter ℂ N} (hψ : ψ ≠ 1) (a : ℕ) :
    ∑ k ∈ Finset.Icc (a + 1) (a + N), ψ k = 0 := by
  have hIcc : Finset.Icc (a + 1) (a + N) = (Finset.range N).image (fun j => a + 1 + j) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · intro h
      exact ⟨k - (a + 1), by omega, by omega⟩
    · intro h
      obtain ⟨j, hj, hjk⟩ := h
      omega
  rw [hIcc, Finset.sum_image (fun j₁ _ j₂ _ h => by omega)]
  have hbij :=
    PrimitiveLFunctionGrowthInternal.bijOn_natCast_add_one_add
      (N := N) a
  have hreindex :
    ∑ j ∈ Finset.range N, ψ ((a + 1 + j : ℕ)) = ∑ c ∈ (Finset.univ : Finset (ZMod N)), ψ c := by
    apply Finset.sum_nbij (fun j : ℕ => ((a + 1 + j : ℕ) : ZMod N))
    · intro j _; exact Finset.mem_univ _
    · exact hbij.injOn
    · intro c hc
      simpa only [Nat.cast_add, Nat.cast_one, Finset.coe_range, Set.mem_image, Set.mem_Iio] using
        hbij.surjOn (Set.mem_univ c)
    · intro j _; rfl
  rw [hreindex]
  exact MulChar.sum_eq_zero_of_ne_one hψ

/-- Partial character sums are periodic with period `N`. -/
theorem sum_Icc_one_periodic {ψ : DirichletCharacter ℂ N} (hψ : ψ ≠ 1) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 (n + N), ψ k = ∑ k ∈ Finset.Icc 1 n, ψ k := by
  have hunion : Finset.Icc 1 (n + N) = Finset.Icc 1 n ∪ Finset.Icc (n + 1) (n + N) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc 1 n) (Finset.Icc (n + 1) (n + N)) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    simp only [Finset.mem_Icc] at hk1 hk2
    omega
  rw [hunion, Finset.sum_union hdisj,
    PrimitiveLFunctionGrowthInternal.sum_Icc_add_one_add_eq_zero
      hψ n,
    add_zero]

end PrimitiveLFunctionGrowthInternal

/--
Input/assumptions: a nontrivial Dirichlet character `ψ` modulo `N`.
Conclusion: every partial sum `∑_{k=1}^n ψ(k)` has norm at most `N`, uniformly in `n`.
Content: partial sums are periodic with period `N` (blocks of `N` consecutive terms sum to zero,
by `MulChar.sum_eq_zero_of_ne_one` and a bijection between `N` consecutive naturals and `ZMod N`),
so it suffices to bound one period, where the crude termwise bound `‖ψ(k)‖ ≤ 1` already gives
`≤ N`.
Role: is the input replacing the linearly-growing `⌊t⌋` term of the classical zeta
Euler-Maclaurin argument with a bounded one, letting a single level of Abel summation give
an `L(s, ψ)` growth
bound valid on `Re s > 0` for nonprincipal `ψ` (no sawtooth refinement needed, unlike `ζ`).
-/
theorem norm_sum_Icc_one_le {N : ℕ} [NeZero N] {ψ : DirichletCharacter ℂ N} (hψ : ψ ≠ 1) (n : ℕ) :
    ‖∑ k ∈ Finset.Icc 1 n, ψ k‖ ≤ N := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases lt_or_ge n N with hn | hn
    · calc
        ‖∑ k ∈ Finset.Icc 1 n, ψ k‖ ≤ ∑ k ∈ Finset.Icc 1 n, ‖ψ k‖ := norm_sum_le _ _
        _ ≤ ∑ _k ∈ Finset.Icc 1 n, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro k _
          exact DirichletCharacter.norm_le_one ψ k
        _ = (n : ℝ) := by
          simp only [Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul, mul_one]
        _ ≤ N := by exact_mod_cast hn.le
    · have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
      have hm : n - N < n := by omega
      have hmn : n - N + N = n := by omega
      have hperiodic := PrimitiveLFunctionGrowthInternal.sum_Icc_one_periodic hψ (n - N)
      rw [hmn] at hperiodic
      rw [hperiodic]
      exact ih (n - N) hm

/--
Input/assumptions: a Dirichlet character `ψ` modulo `N` with `N > 1`, a nonzero `s`.
Conclusion: the finite Abel-summation identity
`∑_{k=1}^M ψ(k) k^{-s} = A(M) M^{-s} + s ∫_1^M t^{-s-1} A(⌊t⌋) dt`, where
`A(n) := ∑_{k=1}^n ψ(k)`.
Content: apply `sum_mul_eq_sub_integral_mul₀` (Abel summation) to the coefficient sequence `ψ`
and the smooth weight `t ↦ t^{-s}`, mirroring
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.sum_cpow_eq_sub_integral`
(the unweighted zeta identity) with `ψ` in place of
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.oneFromOne`.
Role: the finite identity, the starting point for the `M → ∞` limit
giving `L(s, ψ)`'s Abel/Mellin integral representation on `Re s > 0`, without the `ζ`-style
sawtooth correction (the partial sums `A(n)` are already bounded,
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.norm_sum_Icc_one_le`, unlike
`ζ`'s linearly growing `⌊t⌋`).
-/
theorem sum_charCpow_eq_sub_integral {N : ℕ} [NeZero N] (hN1 : 1 < N) {ψ : DirichletCharacter ℂ N}
    {s : ℂ} (hs0 : s ≠ 0) (M : ℕ) :
    ∑ k ∈ Finset.Icc 1 M, ψ k * (k : ℂ) ^ (-s) =
      (∑ k ∈ Finset.Icc 1 M, ψ k) * (M : ℂ) ^ (-s) +
        s *
          ∫ t in Set.Ioc (1 : ℝ) (M : ℝ), (t : ℂ) ^ (-s - 1) * (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ψ k) := by
  have hψ0 : ψ (0 : ℕ) = 0 := by
    have hcop : ¬Nat.Coprime 0 N := by
      rw [Nat.coprime_zero_left]
      omega
    simpa only [Int.cast_natCast] using
      (DirichletCharacter.apply_eq_zero_iff ψ ((0 : ℕ) : ℤ)).mpr
        (by simpa only [Nat.isCoprime_iff_coprime] using hcop)
  have hf_diff :
    ∀ t ∈ Set.Icc (1 : ℝ) (M : ℝ), DifferentiableAt ℝ (fun y : ℝ => (y : ℂ) ^ (-s)) t := by
    intro t ht
    simp only [Set.mem_Icc] at ht
    exact
      (RiemannZeta.hasDerivAt_cpow_neg hs0
          (by linarith : t ≠ (0 : ℝ))).differentiableAt
  have hf_int :
    MeasureTheory.IntegrableOn (deriv (fun y : ℝ => (y : ℂ) ^ (-s))) (Set.Icc (1 : ℝ) (M : ℝ)) := by
    have hderiv_eq :
      ∀ t ∈ Set.Icc (1 : ℝ) (M : ℝ),
        deriv (fun y : ℝ => (y : ℂ) ^ (-s)) t = -s * (t : ℂ) ^ (-s - 1) := by
      intro t ht
      simp only [Set.mem_Icc] at ht
      exact
        (RiemannZeta.hasDerivAt_cpow_neg hs0
            (by linarith : t ≠ (0 : ℝ))).deriv
    exact
      ((RiemannZeta.continuousOn_deriv_cpow_neg s
              zero_lt_one).congr
          hderiv_eq).integrableOn_Icc
  have hraw := sum_mul_eq_sub_integral_mul₀ (fun k : ℕ => ψ k) hψ0 (M : ℝ) hf_diff hf_int
  rw [Nat.floor_natCast] at hraw
  push_cast at hraw
  have h4 : ∀ n : ℕ, ∑ k ∈ Finset.Icc 0 n, ψ k = ∑ k ∈ Finset.Icc 1 n, ψ k := fun n ↦ by
    rw [← Finset.insert_Icc_add_one_left_eq_Icc n.zero_le, Finset.sum_insert (by aesop), hψ0,
      zero_add, zero_add]
  have hlhs :
    ∑ k ∈ Finset.Icc 0 M, (k : ℂ) ^ (-s) * ψ k = ∑ k ∈ Finset.Icc 1 M, ψ k * (k : ℂ) ^ (-s) := by
    rw [←
      Finset.sum_subset (Finset.Icc_subset_Icc_left (Nat.zero_le 1))
        (fun k hk0M hk1 => by
          simp only [Finset.mem_Icc] at hk0M hk1
          have hk0 : k = 0 := by omega
          rw [hk0, hψ0, mul_zero])]
    apply Finset.sum_congr rfl
    intro k hk
    rw [mul_comm]
  rw [hlhs, h4] at hraw
  have hint_eq :
    ∫ t in Set.Ioc (1 : ℝ) (M : ℝ),
        deriv (fun y : ℝ => (y : ℂ) ^ (-s)) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, ψ k =
      -s * ∫ t in Set.Ioc (1 : ℝ) (M : ℝ), (t : ℂ) ^ (-s - 1) * (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ψ k) := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    simp only [Set.mem_Ioc] at ht
    dsimp only
    rw [h4 ⌊t⌋₊,
      (RiemannZeta.hasDerivAt_cpow_neg hs0
          (by linarith : t ≠ (0 : ℝ))).deriv]
    ring
  rw [hint_eq] at hraw
  linear_combination hraw

/-- Pointwise bound on the Abel/Mellin integrand, for any `s` and `t > 0`: `A` is bounded
(`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.norm_sum_Icc_one_le`), so
`‖t^{-s-1} · A(⌊t⌋)‖ ≤ N · t^{-(Re s + 1)}`. -/
theorem norm_charCpow_mul_partialSum_le {N : ℕ} [NeZero N] {ψ : DirichletCharacter ℂ N} (hψ : ψ ≠ 1)
    {s : ℂ} {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ (-s - 1) * ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ψ k‖ ≤ (N : ℝ) * t ^ (-(s.re + 1)) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
  have h1 : (-s - 1).re = -(s.re + 1) := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    ring
  rw [h1]
  calc
    t ^ (-(s.re + 1)) * ‖∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ψ k‖ ≤ t ^ (-(s.re + 1)) * (N : ℝ) :=
      mul_le_mul_of_nonneg_left
        (norm_sum_Icc_one_le hψ ⌊t⌋₊)
        (Real.rpow_nonneg ht.le _)
    _ = (N : ℝ) * t ^ (-(s.re + 1)) := by ring

/--
Input/assumptions: a nontrivial Dirichlet character `ψ` modulo `N`, and `Re s > 0`.
Conclusion: the Abel/Mellin integrand `t ↦ t^{-s-1} · A(⌊t⌋)`, where
`A(n) := ∑_{k=1}^n ψ(k)`, is integrable on `Set.Ioi 1`.
Content: dominate by `N · t^{-(Re s + 1)}`, itself integrable on `Ioi 1` since `Re s + 1 > 1`
(`integrableOn_Ioi_rpow_of_lt`), using
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.norm_sum_Icc_one_le` for the numerator bound;
mirrors `PseudoPrime.AnalyticNumberTheory.RiemannZeta.integrableOn_cpow_mul_sawtooth_Ioi` with
a bounded partial character sum in place of the bounded sawtooth correction.
Role: the integrability step, needed for the `M → ∞` limit of
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.sum_charCpow_eq_sub_integral` giving
the Abel/Mellin representation of `L(s, ψ)` on `Re s > 0`.
-/
theorem integrableOn_charCpow_mul_partialSum_Ioi {N : ℕ} [NeZero N] {ψ : DirichletCharacter ℂ N}
    (hψ : ψ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    MeasureTheory.IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s - 1) * (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ψ k))
      (Set.Ioi (1 : ℝ)) := by
  have hdom :
    MeasureTheory.IntegrableOn (fun t : ℝ => (N : ℝ) * t ^ (-(s.re + 1))) (Set.Ioi (1 : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul _
  refine MeasureTheory.Integrable.mono' hdom ?_ ?_
  · have hcont : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-s - 1)) (Set.Ioi (1 : ℝ)) := by
      intro y hy
      simp only [Set.mem_Ioi] at hy
      exact
        (Complex.continuousAt_ofReal_cpow_const y (-s - 1)
            (Or.inr (by linarith))).continuousWithinAt
    have h1 :
      MeasureTheory.AEStronglyMeasurable (fun t : ℝ => (t : ℂ) ^ (-s - 1))
        (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) :=
      hcont.aestronglyMeasurable measurableSet_Ioi
    have hmeas : Measurable (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, ψ k) := Measurable.of_discrete
    have h2 :
      MeasureTheory.AEStronglyMeasurable (fun t : ℝ => (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ψ k))
        (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) :=
      (hmeas.comp Nat.measurable_floor).aestronglyMeasurable
    exact h1.mul h2
  · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with t ht
    simp only [Set.mem_Ioi] at ht
    exact
      norm_charCpow_mul_partialSum_le hψ
        (by linarith)

/-! ### Holomorphicity of the Abel/Mellin integral via the Mellin transform

`I(s) := ∫_{Ioi 1} t^{-s-1} · A(⌊t⌋) dt`, where `A(n) := ∑_{k=1}^n ψ(k)`, is (up to the
affine change of variable `w = -s`) the Mellin transform of `A(⌊·⌋)` restricted to `Ioi 1`
(extended by `0` on `(0,1]`). Since `A` is bounded
(`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.norm_sum_Icc_one_le`) and the extension
vanishes near `0`, mathlib's general Mellin-transform holomorphicity criterion applies
directly, with no `Re s` lower bound needed beyond `Re s > 0` — unlike the `ζ` case
no second Euler-Maclaurin layer is required since `A` is
already `O(1)`, not `O(t)`. -/

/-- `A(⌊t⌋)`, extended by `0` on `(0,1]`, viewed as a complex-valued function of `t > 0`. -/
noncomputable def charPartialSumIndicator {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) (t : ℝ) :
    ℂ :=
  if t ≤ 1 then 0 else ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ψ k

theorem measurable_charPartialSumIndicator {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) :
    Measurable (charPartialSumIndicator ψ) := by
  unfold charPartialSumIndicator
  have hmeas : Measurable (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, ψ k) := Measurable.of_discrete
  exact Measurable.ite measurableSet_Iic measurable_const (hmeas.comp Nat.measurable_floor)

theorem norm_charPartialSumIndicator_le {N : ℕ} [NeZero N] {ψ : DirichletCharacter ℂ N} (hψ : ψ ≠ 1)
    (t : ℝ) :
    ‖charPartialSumIndicator ψ t‖ ≤ N := by
  unfold charPartialSumIndicator
  split_ifs with h
  · simp only [norm_zero]; exact Nat.cast_nonneg N
  · exact norm_sum_Icc_one_le hψ ⌊t⌋₊

theorem charPartialSumIndicator_eq_zero_of_le_one {N : ℕ} [NeZero N] {ψ : DirichletCharacter ℂ N}
    {t : ℝ} (ht : t ≤ 1) :
    charPartialSumIndicator ψ t = 0 := by
  unfold charPartialSumIndicator;
  rw [ite_eq_left ht]

theorem charPartialSumIndicator_eq_of_lt {N : ℕ} [NeZero N] {ψ : DirichletCharacter ℂ N} {t : ℝ}
    (ht : 1 < t) :
    charPartialSumIndicator ψ t = ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ψ k := by
  unfold charPartialSumIndicator;
  rw [ite_eq_right (not_le.mpr ht)]

theorem locallyIntegrableOn_charPartialSumIndicator {N : ℕ} [NeZero N] {ψ : DirichletCharacter ℂ N}
    (hψ : ψ ≠ 1) :
    MeasureTheory.LocallyIntegrableOn
      (charPartialSumIndicator ψ)
      (Set.Ioi (0 : ℝ)) := by
  refine (MeasureTheory.locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed).mpr fun K _ hK ↦ ?_
  apply
    MeasureTheory.Integrable.mono'
      (MeasureTheory.integrableOn_const (C := (N : ℝ)) hK.measure_lt_top.ne (by finiteness))
  · exact
      (measurable_charPartialSumIndicator ψ).aestronglyMeasurable.restrict
  · exact
      Filter.Eventually.of_forall fun t =>
        norm_charPartialSumIndicator_le hψ t

theorem isBigO_atTop_charPartialSumIndicator {N : ℕ} [NeZero N] {ψ : DirichletCharacter ℂ N}
    (hψ : ψ ≠ 1) :
    charPartialSumIndicator ψ =O[Filter.atTop]
      fun t : ℝ => t ^ (-(0 : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound (N : ℝ)
  filter_upwards with t
  rw [neg_zero, Real.rpow_zero, norm_one, mul_one]
  exact norm_charPartialSumIndicator_le hψ t

theorem isBigO_nhdsWithin_charPartialSumIndicator {N : ℕ} [NeZero N] {ψ : DirichletCharacter ℂ N}
    (b : ℝ) :
    charPartialSumIndicator
        ψ =O[nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))]
      fun t : ℝ => t ^ (-b) := by
  have hev :
    charPartialSumIndicator ψ =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))]
      0 := by
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num only)),
      self_mem_nhdsWithin] with t ht1 ht2
    exact
      charPartialSumIndicator_eq_zero_of_le_one ht1.le
  exact hev.trans_isBigO (Asymptotics.isBigO_zero (fun t : ℝ => t ^ (-b)) _)

/-- The Abel integral `I(s)`, as the Mellin transform of
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.charPartialSumIndicator ψ`, is
holomorphic in `w` throughout `Re w < 0` (no lower bound: the indicator vanishes identically
near `0`, so the near-zero growth threshold `b` can be taken as negative as needed). -/
theorem differentiableAt_mellin_charPartialSumIndicator {N : ℕ} [NeZero N]
    {ψ : DirichletCharacter ℂ N} (hψ : ψ ≠ 1) {w : ℂ} (hw1 : w.re < 0) :
    DifferentiableAt ℂ
      (mellin (charPartialSumIndicator ψ)) w :=
  mellin_differentiableAt_of_isBigO_rpow
    (locallyIntegrableOn_charPartialSumIndicator hψ)
    (isBigO_atTop_charPartialSumIndicator hψ)
    (by simpa only using hw1)
    (isBigO_nhdsWithin_charPartialSumIndicator (w.re - 1))
    (by linarith)

/-- `mellin (PseudoPrime.AnalyticNumberTheory.DirichletLFunction.charPartialSumIndicator ψ) w`
agrees with the Abel integral `I` at `w = -s`,
provided `Re s > 0` (so the integral is genuinely convergent,
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.integrableOn_charCpow_mul_partialSum_Ioi`). -/
theorem mellin_charPartialSumIndicator_eq {N : ℕ} [NeZero N] {ψ : DirichletCharacter ℂ N}
    (hψ : ψ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    mellin (charPartialSumIndicator ψ) (-s) =
      ∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-s - 1) * ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ψ k := by
  have hint1 :
    MeasureTheory.IntegrableOn
      (fun t : ℝ =>
        (t : ℂ) ^ (-s - 1) •
          charPartialSumIndicator ψ t)
      (Set.Ioc (0 : ℝ) 1) := by
    apply MeasureTheory.integrableOn_zero.congr_fun_ae
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    rw [charPartialSumIndicator_eq_zero_of_le_one
        ht.2,
      smul_zero]
  have hint2 :
    MeasureTheory.IntegrableOn
      (fun t : ℝ =>
        (t : ℂ) ^ (-s - 1) •
          charPartialSumIndicator ψ t)
      (Set.Ioi (1 : ℝ)) := by
    have heq :
      (fun t : ℝ =>
          (t : ℂ) ^ (-s - 1) • charPartialSumIndicator ψ t)
             =ᶠ[MeasureTheory.ae (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ)))]
        (fun t : ℝ => (t : ℂ) ^ (-s - 1) * ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ψ k) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
      simp only [Set.mem_Ioi] at ht
      rw [charPartialSumIndicator_eq_of_lt ht,
        smul_eq_mul]
    rw [MeasureTheory.IntegrableOn, MeasureTheory.integrable_congr heq]
    exact integrableOn_charCpow_mul_partialSum_Ioi hψ hs
  rw [mellin,
    show Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) from by
      ext t; simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
      constructor
      · intro ht; by_cases h : t ≤ 1
        · exact Or.inl ⟨ht, h⟩
        · exact Or.inr (not_le.mp h)
      · rintro (⟨ht, _⟩ | ht)
        · exact ht
        · linarith,
    MeasureTheory.setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hint1 hint2,
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (g := fun _ => (0 : ℂ)) fun t ht => by
      rw [charPartialSumIndicator_eq_zero_of_le_one ht.2, smul_zero], MeasureTheory.integral_zero,
      zero_add]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only [Set.mem_Ioi] at ht
  change
    (t : ℂ) ^ (-s - 1) •
        charPartialSumIndicator ψ t =
      (t : ℂ) ^ (-s - 1) * ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ψ k
  rw [charPartialSumIndicator_eq_of_lt ht, smul_eq_mul]

/-- **the Abel/Mellin identity**: the Abel/Mellin integral `I(s) = ∫_{Ioi 1} t^{-s-1} · A(⌊t⌋) dt`
is holomorphic in `s` throughout `Re s > 0`. -/
theorem differentiableAt_charAbelIntegral {N : ℕ} [NeZero N] {ψ : DirichletCharacter ℂ N}
    (hψ : ψ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ
      (fun s => ∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-s - 1) * ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ψ k) s := by
  have hcomp : DifferentiableAt ℂ (fun s : ℂ => -s) s := by fun_prop
  have hd :
    DifferentiableAt ℂ
      (mellin (charPartialSumIndicator ψ))
      (-s) :=
    differentiableAt_mellin_charPartialSumIndicator
      hψ
      (by
        simp only [Complex.neg_re]; linarith)
  have hcd := hd.comp s hcomp
  have heq :
    (mellin (charPartialSumIndicator ψ) ∘
        fun s : ℂ => -s) =ᶠ[nhds s]
      (fun s => ∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-s - 1) * ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ψ k) := by
    filter_upwards [(Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds
        (show (0 : ℝ) < s.re by linarith : s ∈ Complex.re ⁻¹' Set.Ioi (0 : ℝ))] with
      t ht
    exact
      mellin_charPartialSumIndicator_eq hψ ht
  exact hcd.congr_of_eventuallyEq heq.symm

/-- **the continuation identity**: for `Re s > 1`, `L(s, ψ)` equals `s` times the Abel/Mellin
integral `I(s)`, obtained as the `M → ∞` limit of the finite identity
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.sum_charCpow_eq_sub_integral` (the
`A(M) M^{-s}` boundary term vanishes since `A` is bounded and `M^{-s} → 0`). -/
theorem lFunction_eq_mul_charAbelIntegral {N : ℕ} [NeZero N] (hN1 : 1 < N)
    {ψ : DirichletCharacter ℂ N} (hψ : ψ ≠ 1) {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.LFunction ψ s =
      s * ∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-s - 1) * ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ψ k := by
  have hs0 : s ≠ 0 := fun h => by
    simp only [h, Complex.zero_re] at hs; linarith
  have hsumtail :
    Filter.Tendsto (fun M : ℕ => ∑ k ∈ Finset.Icc 1 M, ψ k * (k : ℂ) ^ (-s)) Filter.atTop
      (nhds (DirichletCharacter.LFunction ψ s)) := by
    rw [DirichletCharacter.LFunction_eq_LSeries ψ hs]
    have hsumm := DirichletCharacter.LSeriesSummable_of_one_lt_re ψ hs
    have hhasSum := hsumm.LSeriesHasSum
    have hcongr :
      ∀ M : ℕ,
        ∑ k ∈ Finset.Icc 1 M, ψ k * (k : ℂ) ^ (-s) =
          ∑ n ∈ Finset.range (M + 1), LSeries.term (fun n => ψ n) s n := by
      intro M
      rw [Nat.range_succ_eq_Icc_zero, ←
        Finset.sum_subset (Finset.Icc_subset_Icc_left (Nat.zero_le 1))
          (fun k hk hk1 => by
            simp only [Finset.mem_Icc] at hk hk1
            have hk0 : k = 0 := by omega
            rw [hk0]; simp only [LSeries.term, ↓reduceIte])]
      exact
        Finset.sum_congr rfl fun k hk => by
          simp only [Finset.mem_Icc] at hk
          rw [LSeries.term_of_ne_zero (by omega : k ≠ 0), Complex.cpow_neg, div_eq_mul_inv]
    simp_rw [hcongr]
    exact hhasSum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
  have hz : Filter.Tendsto (fun M : ℕ => ‖(M : ℂ) ^ (-s)‖) Filter.atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mp
      (RiemannZeta.tendsto_natCast_cpow_atTop_zero (z := -s)
        (by
          simp only [Complex.neg_re]; linarith))
  have hAM :
    Filter.Tendsto (fun M : ℕ => (∑ k ∈ Finset.Icc 1 M, ψ k) * (M : ℂ) ^ (-s)) Filter.atTop
      (nhds 0) := by
    apply squeeze_zero_norm' (a := fun M : ℕ => (N : ℝ) * ‖(M : ℂ) ^ (-s)‖)
    · filter_upwards with M
      rw [norm_mul]
      exact
        mul_le_mul_of_nonneg_right
          (norm_sum_Icc_one_le hψ M)
          (norm_nonneg _)
    · simpa only [mul_zero] using hz.const_mul (N : ℝ)
  have heqIoc :
    (fun M : ℕ =>
        ∫ t in Set.Ioc (1 : ℝ) (M : ℝ),
          (t : ℂ) ^ (-s - 1) * ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ψ k) =ᶠ[Filter.atTop]
      (fun M : ℕ =>
        ∫ t in (1 : ℝ)..(M : ℝ), (t : ℂ) ^ (-s - 1) * ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ψ k) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with M hM
    rw [intervalIntegral.integral_of_le (by exact_mod_cast hM)]
  have hI0 :
    Filter.Tendsto
      (fun M : ℕ => ∫ t in (1 : ℝ)..(M : ℝ), (t : ℂ) ^ (-s - 1) * ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ψ k)
      Filter.atTop
      (nhds (∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-s - 1) * ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ψ k)) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi 1
      (integrableOn_charCpow_mul_partialSum_Ioi hψ (by linarith))
      tendsto_natCast_atTop_atTop
  have hI :
    Filter.Tendsto
      (fun M : ℕ =>
        s * ∫ t in Set.Ioc (1 : ℝ) (M : ℝ), (t : ℂ) ^ (-s - 1) * ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ψ k)
      Filter.atTop
      (nhds (s * ∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-s - 1) * ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ψ k)) :=
    (hI0.congr' heqIoc.symm).const_mul s
  have hraw := hAM.add hI
  rw [zero_add] at hraw
  refine tendsto_nhds_unique hsumtail (hraw.congr' (Filter.Eventually.of_forall fun M => ?_))
  exact (sum_charCpow_eq_sub_integral hN1 hs0 M).symm

/-- **the continuation theorem**: the equality `L(s, ψ) = s · I(s)` extends from `Re s > 1` to
all of `Re s > 0`, via the identity theorem: `LFunction ψ` is entire (`ψ` nontrivial) and
`s ↦ s · I(s)` is analytic on `Re s > 0` by `differentiableAt_charAbelIntegral`,
and they agree on the open, nonempty subset `Re s > 1` by `lFunction_eq_mul_charAbelIntegral`. -/
theorem lFunction_eq_mul_charAbelIntegral_of_zero_lt_re {N : ℕ} [NeZero N] (hN1 : 1 < N)
    {ψ : DirichletCharacter ℂ N} (hψ : ψ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.LFunction ψ s =
      s * ∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-s - 1) * ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ψ k := by
  set U : Set ℂ := {u : ℂ | 0 < u.re} with hU_def
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hlin : IsLinearMap ℝ Complex.re := ⟨Complex.add_re, Complex.smul_re⟩
  have hUconn : IsPreconnected U := (convex_halfSpace_gt hlin 0).isPreconnected
  have hf : AnalyticOnNhd ℂ (DirichletCharacter.LFunction ψ) U :=
    (DirichletCharacter.differentiable_LFunction hψ).differentiableOn.analyticOnNhd hUopen
  have hg :
    AnalyticOnNhd ℂ
      (fun u => u * ∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-u - 1) * ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ψ k)
      U := by
    apply DifferentiableOn.analyticOnNhd _ hUopen
    intro u hu
    exact
      ((by fun_prop : DifferentiableAt ℂ (fun u : ℂ => u) u).mul
          (differentiableAt_charAbelIntegral hψ
            hu)).differentiableWithinAt
  have h0 : (2 : ℂ) ∈ U := by simp only [hU_def, Set.mem_ofPred_eq, Complex.re_ofNat, Nat.ofNat_pos]
  have hfg :
    (DirichletCharacter.LFunction ψ) =ᶠ[nhds (2 : ℂ)]
      (fun u => u * ∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-u - 1) * ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ψ k) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show (1 : ℝ) < (2 : ℂ).re by
          change (1 : ℝ) < 2
          norm_num only)] with
      z hz
    exact
      lFunction_eq_mul_charAbelIntegral hN1 hψ
        hz
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hUconn h0 hfg hs

/-- **the growth bound**: the crude growth bound `|L(s, ψ)| ≤ N |s| / Re s` for `Re s > 0`, obtained
by bounding `I(s)` via
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.norm_charCpow_mul_partialSum_le` and
`∫_1^∞ t^{-σ-1} dt = 1/σ`. -/
theorem norm_lFunction_le {N : ℕ} [NeZero N] (hN1 : 1 < N) {ψ : DirichletCharacter ℂ N} (hψ : ψ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) : ‖DirichletCharacter.LFunction ψ s‖ ≤ (N : ℝ) * ‖s‖ / s.re := by
  rw [lFunction_eq_mul_charAbelIntegral_of_zero_lt_re
      hN1 hψ hs,
    norm_mul]
  have hint : ∫ t in Set.Ioi (1 : ℝ), (N : ℝ) * t ^ (-(s.re + 1)) = (N : ℝ) / s.re := by
    rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) zero_lt_one]
    have h1 : -(s.re + 1) + 1 = -s.re := by ring
    rw [h1, Real.one_rpow, neg_div_neg_eq, mul_one_div]
  have hI :
    ‖∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-s - 1) * ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ψ k‖ ≤
      (N : ℝ) / s.re := by
    rw [← hint]
    refine
      (MeasureTheory.norm_integral_le_integral_norm _).trans
        (MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => norm_nonneg _)
          ((integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul _) ?_)
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with t ht
    simp only [Set.mem_Ioi] at ht
    exact
      norm_charCpow_mul_partialSum_le hψ
        (by linarith)
  calc
    ‖s‖ * ‖∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-s - 1) * ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ψ k‖ ≤
        ‖s‖ * ((N : ℝ) / s.re) :=
      mul_le_mul_of_nonneg_left hI (norm_nonneg _)
    _ = (N : ℝ) * ‖s‖ / s.re := by ring

/-- **the right-half-plane bound**: restricted to `Re s ≥ 1/2`, `norm_lFunction_le` simplifies to
the explicit polynomial growth `|L(s, ψ)| ≤ 2N|s|`. -/
theorem norm_lFunction_le_two_mul {N : ℕ} [NeZero N] (hN1 : 1 < N) {ψ : DirichletCharacter ℂ N}
    (hψ : ψ ≠ 1) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖DirichletCharacter.LFunction ψ s‖ ≤ 2 * (N : ℝ) * ‖s‖ := by
  have hs0 : 0 < s.re := by linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  refine (norm_lFunction_le hN1 hψ hs0).trans ?_
  rw [div_le_iff₀ hs0]
  calc
    (N : ℝ) * ‖s‖ = (N : ℝ) * ‖s‖ * 1 := by ring
    _ ≤ (N : ℝ) * ‖s‖ * (2 * s.re) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hNpos.le (norm_nonneg s))
    _ = 2 * (N : ℝ) * ‖s‖ * s.re := by ring

/-! ### `Complex.Gamma` growth on `Re z ≥ 1/4`

`gammaFactor χ s` is `Gammaℝ s = π^{-s/2}Γ(s/2)` or `Gammaℝ(s+1) = π^{-(s+1)/2}Γ((s+1)/2)`,
whose argument has `Re ≥ 1/4` whenever `Re s ≥ 1/2`. Since
`PseudoPrime.AnalyticNumberTheory.Gamma.log_Gamma_le_of_one_le` in `Gamma.GrowthElementary`
only applies once the argument's real part is `≥ 1` (unlike
`PseudoPrime.AnalyticNumberTheory.RiemannXi.riemannXi`'s own `Γ(s/2+1)`, which is shifted by
exactly `1` for this reason), the bound below
reduces `Γ(z)` to `Γ(z+1)/z` (`Complex.Gamma_add_one`) first. -/

/-- Elementary bound `‖Γ(z)‖ ≤ 4 · exp((‖z‖+1)·log(‖z‖+1))` for `Re z ≥ 1/4`, via
`Γ(z) = Γ(z+1)/z` reducing to the `Re ≥ 1` regime where
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.norm_Gamma_le_Gamma_re` and
`PseudoPrime.AnalyticNumberTheory.Gamma.log_Gamma_le_of_one_le` apply,
and `‖z‖ ≥ Re z ≥ 1/4` making `1/‖z‖ ≤ 4` a crude but
sufficient bound on the extra factor. -/
theorem norm_Gamma_le_of_one_quarter_le_re {z : ℂ} (hz : 1 / 4 ≤ z.re) :
    ‖Complex.Gamma z‖ ≤ 4 * Real.exp ((‖z‖ + 1) * Real.log (‖z‖ + 1)) := by
  have hzre_le_norm : z.re ≤ ‖z‖ := (le_abs_self z.re).trans (Complex.abs_re_le_norm z)
  have hzne : z ≠ 0 := fun h => by
    rw [h, Complex.zero_re] at hz; linarith
  have hznorm_pos : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hzne
  have hz1re : (z + 1).re = z.re + 1 := by simp only [Complex.add_re, Complex.one_re]
  have hz1pos : (0 : ℝ) < (z + 1).re := by
    rw [hz1re]; linarith
  have hz1ge1 : (1 : ℝ) ≤ (z + 1).re := by
    rw [hz1re]; linarith
  have hzinv : (1 : ℝ) / ‖z‖ ≤ 4 := by
    rw [div_le_iff₀ hznorm_pos]; linarith
  have hb : ‖Complex.Gamma (z + 1)‖ ≤ Real.exp ((‖z‖ + 1) * Real.log (‖z‖ + 1)) := by
    have hstep1 : ‖Complex.Gamma (z + 1)‖ ≤ Real.Gamma (z + 1).re :=
      RiemannZeta.norm_Gamma_le_Gamma_re hz1pos
    have hpos : 0 < Real.Gamma (z + 1).re := Real.Gamma_pos_of_pos hz1pos
    have hstep2 : Real.Gamma (z + 1).re ≤ Real.exp ((z + 1).re * Real.log (z + 1).re) := by
      calc
        Real.Gamma (z + 1).re = Real.exp (Real.log (Real.Gamma (z + 1).re)) :=
          (Real.exp_log hpos).symm
        _ ≤ Real.exp ((z + 1).re * Real.log (z + 1).re) :=
          Real.exp_le_exp.mpr (Gamma.log_Gamma_le_of_one_le hz1ge1)
    have hstep3 : (z + 1).re ≤ ‖z‖ + 1 := by
      rw [hz1re]; linarith
    have hstep4 :
      Real.exp ((z + 1).re * Real.log (z + 1).re) ≤ Real.exp ((‖z‖ + 1) * Real.log (‖z‖ + 1)) :=
      Real.exp_le_exp.mpr
        (Gamma.mul_log_mono_of_one_le hz1ge1 hstep3)
    exact hstep1.trans (hstep2.trans hstep4)
  have hGammaEq : Complex.Gamma z = Complex.Gamma (z + 1) / z := by
    rw [eq_div_iff hzne, mul_comm]
    exact (Complex.Gamma_add_one z hzne).symm
  rw [hGammaEq, norm_div, div_eq_mul_one_div]
  calc
    ‖Complex.Gamma (z + 1)‖ * (1 / ‖z‖) ≤ Real.exp ((‖z‖ + 1) * Real.log (‖z‖ + 1)) * 4 :=
      mul_le_mul hb hzinv (by positivity) (Real.exp_pos _).le
    _ = 4 * Real.exp ((‖z‖ + 1) * Real.log (‖z‖ + 1)) := by ring

/-- Growth bound for Deligne's archimedean factor `Gammaℝ w = π^{-w/2}Γ(w/2)` on `Re w ≥ 1/2`:
the `π^{-w/2}` factor is bounded by its value at `Re w = 1/2` (`π ≥ 1`, exponent decreasing),
and `Γ(w/2)` by
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.norm_Gamma_le_of_one_quarter_le_re`
(`Re(w/2) ≥ 1/4`). -/
theorem norm_Gammaℝ_le {w : ℂ} (hw : 1 / 2 ≤ w.re) :
    ‖Complex.Gammaℝ w‖ ≤
      Real.pi ^ (-(1 : ℝ) / 4) * (4 * Real.exp ((‖w‖ + 1) * Real.log (‖w‖ + 1))) := by
  rw [Complex.Gammaℝ_def, norm_mul]
  have hfac1 : ‖(Real.pi : ℂ) ^ (-w / 2)‖ ≤ Real.pi ^ (-(1 : ℝ) / 4) := by
    have heq : ‖(Real.pi : ℂ) ^ (-w / 2)‖ = Real.pi ^ (-w / 2).re :=
      Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos _
    rw [heq]
    have hre_eq : (-w / 2).re = -w.re / 2 := by simp only [Complex.div_ofNat_re, Complex.neg_re]
    rw [hre_eq]
    have hpi1 : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
    exact Real.rpow_le_rpow_of_exponent_le hpi1 (by linarith)
  have hzre : (1 : ℝ) / 4 ≤ (w / 2).re := by
    rw [Complex.div_ofNat_re]
    linarith
  have hfac2 : ‖Complex.Gamma (w / 2)‖ ≤ 4 * Real.exp ((‖w / 2‖ + 1) * Real.log (‖w / 2‖ + 1)) :=
    norm_Gamma_le_of_one_quarter_le_re hzre
  have hnormhalf : ‖w / 2‖ = ‖w‖ / 2 := by rw [norm_div, Complex.norm_two]
  have hmono :
    Real.exp ((‖w / 2‖ + 1) * Real.log (‖w / 2‖ + 1)) ≤
      Real.exp ((‖w‖ + 1) * Real.log (‖w‖ + 1)) := by
    apply Real.exp_le_exp.mpr
    apply
      Gamma.mul_log_mono_of_one_le
        (by linarith [norm_nonneg (w / 2)])
    rw [hnormhalf]; linarith [norm_nonneg w]
  calc
    ‖(Real.pi : ℂ) ^ (-w / 2)‖ * ‖Complex.Gamma (w / 2)‖ ≤
        Real.pi ^ (-(1 : ℝ) / 4) * (4 * Real.exp ((‖w / 2‖ + 1) * Real.log (‖w / 2‖ + 1))) :=
      mul_le_mul hfac1 hfac2 (norm_nonneg _) (Real.rpow_nonneg Real.pi_pos.le _)
    _ ≤ Real.pi ^ (-(1 : ℝ) / 4) * (4 * Real.exp ((‖w‖ + 1) * Real.log (‖w‖ + 1))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmono (by norm_num only))
        (Real.rpow_nonneg Real.pi_pos.le _)

/-- **The gamma-factor bound**: `gammaFactor χ s` is bounded uniformly in the parity of
`χ`, on `Re s ≥ 1/2`. Even case is `norm_Gammaℝ_le` directly; odd case applies it at `s + 1`
(`Re(s+1) ≥ 3/2 ≥ 1/2`) and absorbs `‖s+1‖ ≤ ‖s‖ + 1` into the same envelope shape via
`PseudoPrime.AnalyticNumberTheory.Gamma.mul_log_mono_of_one_le`. -/
theorem norm_gammaFactor_le {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} {s : ℂ}
    (hs : 1 / 2 ≤ s.re) :
    ‖DirichletCharacter.gammaFactor χ s‖ ≤
      Real.pi ^ (-(1 : ℝ) / 4) * (4 * Real.exp ((‖s‖ + 2) * Real.log (‖s‖ + 2))) := by
  rcases χ.even_or_odd with hχ | hχ
  · rw [hχ.gammaFactor_def]
    refine (norm_Gammaℝ_le hs).trans ?_
    have hmono :
      Real.exp ((‖s‖ + 1) * Real.log (‖s‖ + 1)) ≤ Real.exp ((‖s‖ + 2) * Real.log (‖s‖ + 2)) :=
      Real.exp_le_exp.mpr
        (Gamma.mul_log_mono_of_one_le (by linarith [norm_nonneg s])
          (by linarith))
    exact
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmono (by norm_num only))
        (Real.rpow_nonneg Real.pi_pos.le _)
  · rw [hχ.gammaFactor_def]
    have hs1 : 1 / 2 ≤ (s + 1).re := by
      rw [Complex.add_re, Complex.one_re]
      linarith
    refine (norm_Gammaℝ_le hs1).trans ?_
    have hnorm1 : ‖s + 1‖ ≤ ‖s‖ + 1 := by
      calc
        ‖s + 1‖ ≤ ‖s‖ + ‖(1 : ℂ)‖ := norm_add_le s 1
        _ = ‖s‖ + 1 := by norm_num only [norm_one]
    have hmono :
      Real.exp ((‖s + 1‖ + 1) * Real.log (‖s + 1‖ + 1)) ≤
        Real.exp ((‖s‖ + 2) * Real.log (‖s‖ + 2)) :=
      Real.exp_le_exp.mpr
        (Gamma.mul_log_mono_of_one_le
          (by linarith [norm_nonneg (s + 1)]) (by linarith))
    exact
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmono (by norm_num only))
        (Real.rpow_nonneg Real.pi_pos.le _)

/-- **the gamma-factor input**: an explicit order-one growth bound for `completedLFunction χ` on
`Re s ≥ 1/2`, combining `norm_lFunction_le_two_mul` with the Gamma-factor bound
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.norm_gammaFactor_le` via
`completedLFunction χ s = LFunction χ s * gammaFactor χ s`
(`LFunction_eq_completed_div_gammaFactor`, `gammaFactor` nonvanishing on `Re s > 0`
via `Complex.Gammaℝ_ne_zero_of_re_pos`). -/
theorem norm_completedLFunction_le {N : ℕ} [NeZero N] (hN1 : 1 < N) {χ : DirichletCharacter ℂ N}
    (hχ1 : χ ≠ 1) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖DirichletCharacter.completedLFunction χ s‖ ≤
      2 * (N : ℝ) * ‖s‖ *
        (Real.pi ^ (-(1 : ℝ) / 4) * (4 * Real.exp ((‖s‖ + 2) * Real.log (‖s‖ + 2)))) := by
  have hgamma_ne : DirichletCharacter.gammaFactor χ s ≠ 0 := by
    rcases χ.even_or_odd with hχ | hχ
    · rw [hχ.gammaFactor_def]; exact Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
    · rw [hχ.gammaFactor_def]
      apply Complex.Gammaℝ_ne_zero_of_re_pos
      rw [Complex.add_re, Complex.one_re]
      linarith
  have hcompleted_eq :
    DirichletCharacter.completedLFunction χ s =
      DirichletCharacter.LFunction χ s * DirichletCharacter.gammaFactor χ s := by
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inr hN1.ne'),
      div_mul_cancel₀ _ hgamma_ne]
  rw [hcompleted_eq, norm_mul]
  exact
    mul_le_mul
      (norm_lFunction_le_two_mul hN1 hχ1 hs)
      (norm_gammaFactor_le hs) (norm_nonneg _)
      (by positivity)

/-! ### Extending to `Re s < 1/2` via the functional equation

`IsPrimitive.completedLFunction_one_sub` reflects `completedLFunction χ` at `1 - s` to
`completedLFunction χ⁻¹` at `s`, up to the elementary factors `N^{s-1/2}` and `rootNumber χ`.
Only crude (not sharp) bounds on these two factors are needed to keep the growth order-one;
in particular the classical fact `‖rootNumber χ‖ = 1` (via `|gaussSum| = √N`) is not needed.
-/

/-- Crude bound: `‖gaussSum χ stdAddChar‖ ≤ N`, via the triangle inequality and
`‖χ a‖ ≤ 1`, `‖stdAddChar a‖ = 1` (termwise), summed over the `N` elements of `ZMod N`.
-/
theorem norm_gaussSum_stdAddChar_le {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} :
    ‖gaussSum χ (ZMod.stdAddChar (N := N))‖ ≤ (N : ℝ) := by
  rw [gaussSum]
  calc
    ‖∑ a, χ a * ZMod.stdAddChar a‖ ≤ ∑ a : ZMod N, ‖χ a * ZMod.stdAddChar a‖ := norm_sum_le _ _
    _ ≤ ∑ _a : ZMod N, (1 : ℝ) := by
      refine Finset.sum_le_sum fun a _ => ?_
      rw [norm_mul, ZMod.stdAddChar_apply, Circle.norm_coe, mul_one]
      exact DirichletCharacter.norm_le_one χ a
    _ = (N : ℝ) := by
      simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]

/-- Crude bound: `‖rootNumber χ‖ ≤ N` (far from the sharp value `1`, but sufficient to keep
the functional-equation reflection order-one in the growth argument). -/
theorem norm_rootNumber_le {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} :
    ‖DirichletCharacter.rootNumber χ‖ ≤ (N : ℝ) := by
  rw [DirichletCharacter.rootNumber, norm_div, norm_div, norm_pow, Complex.norm_I, one_pow, div_one]
  have hNhalf : (1 : ℝ) ≤ ‖(N : ℂ) ^ (1 / 2 : ℂ)‖ := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) from by
        norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast,
          Complex.ofReal_ofNat, Nat.cast_ofNat],
      Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero (NeZero.ne N))]
    simp only [Complex.ofReal_re]
    exact
      Real.one_le_rpow (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
        (by norm_num only)
  calc
    ‖gaussSum χ (ZMod.stdAddChar (N := N))‖ / ‖(N : ℂ) ^ (1 / 2 : ℂ)‖ ≤
        ‖gaussSum χ (ZMod.stdAddChar (N := N))‖ :=
      div_le_self (norm_nonneg _) hNhalf
    _ ≤ (N : ℝ) := norm_gaussSum_stdAddChar_le

/-- An order-one growth bound for `completedLFunction χ` on `Re s < 1/2`,
`χ` primitive. Reflects `s` to `1 - s` (where `Re(1-s) > 1/2`, so `norm_completedLFunction_le`
applies to `χ⁻¹`) via
`IsPrimitive.completedLFunction_one_sub`, absorbing `N^{1/2-s}` and `rootNumber χ` with the
crude bounds above. -/
theorem norm_completedLFunction_lt_half_le {N : ℕ} [NeZero N] (hN1 : 1 < N)
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hχ1inv : χ⁻¹ ≠ 1) {s : ℂ}
    (hs : s.re < 1 / 2) :
    ‖DirichletCharacter.completedLFunction χ s‖ ≤
      (N : ℝ) ^ (1 / 2 - s.re) * (N : ℝ) *
        (2 * (N : ℝ) * ‖1 - s‖ *
          (Real.pi ^ (-(1 : ℝ) / 4) *
            (4 * Real.exp ((‖1 - s‖ + 2) * Real.log (‖1 - s‖ + 2))))) := by
  have heq :
    DirichletCharacter.completedLFunction χ s =
      (N : ℂ) ^ (1 / 2 - s) * DirichletCharacter.rootNumber χ *
        DirichletCharacter.completedLFunction χ⁻¹ (1 - s) := by
    have h := hprimitive.completedLFunction_one_sub (1 - s)
    rwa [show (1 : ℂ) - (1 - s) = s from by ring,
      show (1 - s : ℂ) - 1 / 2 = 1 / 2 - s from by ring] at h
  have hs1re : 1 / 2 ≤ ((1 : ℂ) - s).re := by
    rw [Complex.sub_re, Complex.one_re]
    linarith
  have hNpow : ‖(N : ℂ) ^ (1 / 2 - s)‖ = (N : ℝ) ^ (1 / 2 - s.re) := by
    rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero (NeZero.ne N))]
    congr 1
    simp only [one_div, Complex.sub_re, Complex.inv_re, Complex.re_ofNat, Complex.normSq_ofNat,
      div_self_mul_self']
  rw [heq, norm_mul, norm_mul]
  exact
    mul_le_mul
      (mul_le_mul hNpow.le norm_rootNumber_le (norm_nonneg _) (by positivity))
      (norm_completedLFunction_le hN1 hχ1inv hs1re)
      (norm_nonneg _) (by positivity)

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
