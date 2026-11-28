/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186EulerTail
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK196ZeroUpper
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131TailWitness
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianCompensationAbel
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighCompensationPartition
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianReflectedAbel
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighNegativeMoment
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighSignCert
public import PseudoPrime.LLS.PaperStatements.ShiftedPoleExplicitFormula
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTwoShiftZeta
public import PseudoPrime.LLS.PaperStatements.GammaReflectedEulerIntegral

import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighKernelData
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighZeroMass
import all PseudoPrime.LLS.PaperStatements.ShiftedPoleKernel
import all PseudoPrime.LLS.PaperStatements.ShiftedPoleArithmetic

/-! # Reduction of the high Gaussian witness to lower zero bounds -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The signed zero contribution of the three Jacobi pair characters for the
chosen kernel and positive real cutoff. This is the quantity compared in H17. -/
noncomputable def gaussianPairZeroScore (K : HighGaussianKernel) (X : ℝ) {p q r : ℕ} [NeZero p]
    [NeZero q] [NeZero r] (hp : Odd p) (hq : Odd q) (hr : Odd r) : ℝ :=
  let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
  let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
  let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr);
  -(∑' ρ : ℂ, K.zeroTerm a X ρ).re - (∑' ρ : ℂ, K.zeroTerm b X ρ).re -
    (∑' ρ : ℂ, K.zeroTerm c X ρ).re

/-- A lower zero comparison at a positive real cutoff for every prime
factorization of a uniform triple when all prime bases through the cutoff pass.
Each branch includes its kernel threshold. -/
def GaussianHighLowerBounds (n : ℕ) (X : ℝ) : Prop :=
  (∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) →
    ∀ p q r : ℕ,
      p.Prime →
        q.Prime →
        r.Prime →
        n = p * q * r →
        ∀ [NeZero p] [NeZero q] [NeZero r],
          ∀ (hp : Odd p) (hq : Odd q) (hr : Odd r),
            (30 ≤ Real.log X ∧
                3 / 8 * Real.log n - 94173 / 1250 + 3 * HighGaussianKernel.k186.xiMass.re +
                    4 * k186TailCost X <
                  gaussianPairZeroScore .k186 X hp hq hr) ∨
              (75 / 2 ≤ Real.log X ∧
                3 / 8 * Real.log n - 543 / 40 + 3 * HighGaussianKernel.k196.xiMass.re <
                  gaussianPairZeroScore .k196 X hp hq hr)

/-- At a positive cutoff, either strict lower bound contradicts the corresponding
K186 or K196 upper bound under passage of all prime bases. -/
theorem gaussian_high_witness_of_bounds {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {X : ℝ} (hX : 0 < X) (hlower : GaussianHighLowerBounds n X) : HasRejectingPrime n X := by
  by_contra h
  have hpass (l : ℕ) (hl : l.Prime) (hle : (l : ℝ) ≤ X) :
    PrimeTest.StrongMillerRabinPass n (l : ZMod n) :=
    Classical.byContradiction (fun hf ↦ h ⟨l, hl, hle, hf⟩)
  obtain ⟨p, q, r, hp, hq, hr, _, _, hprod⟩ := uniformKorselt_ordered_factors hu
  have hpO := Odd.of_dvd_nat ho (show p ∣ n from ⟨q * r, hprod.trans (Nat.mul_assoc _ _ _)⟩)
  have hqO := Odd.of_dvd_nat ho (show q ∣ n from ⟨p * r, hprod.trans (by ac_rfl)⟩)
  have hrO := Odd.of_dvd_nat ho (show r ∣ n from ⟨p * q, hprod.trans (by ac_rfl)⟩)
  let : NeZero n := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt hn)⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  let : NeZero q := ⟨hq.ne_zero⟩
  let : NeZero r := ⟨hr.ne_zero⟩
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  let : Fact r.Prime := ⟨hr⟩
  let : Fact (2 < p) := ⟨lt_of_le_of_ne hp.two_le (hpO.ne_two_of_dvd_nat dvd_rfl).symm⟩
  let : Fact (2 < q) := ⟨lt_of_le_of_ne hq.two_le (hqO.ne_two_of_dvd_nat dvd_rfl).symm⟩
  let : Fact (2 < r) := ⟨lt_of_le_of_ne hr.two_le (hrO.ne_two_of_dvd_nat dvd_rfl).symm⟩
  rcases hlower hpass p q r hp hq hr hprod hpO hqO hrO with ⟨hlog, hlo⟩ | ⟨hlog, hlo⟩
  · rw [gaussianPairZeroScore] at hlo
    exact (not_lt_of_ge (k186_zero_upper hn ho hu hprod hpO hqO hrO hg hX hlog hpass)) hlo
  · rw [gaussianPairZeroScore] at hlo
    exact (not_lt_of_ge (k196_zero_upper hn ho hu hprod hpO hqO hrO hg hX hlog hpass)) hlo

/-- Combine the middle witness and high zero comparisons with the proved
uniform ranges. Then use the quarter bounds for the other composites. -/
theorem gaussian_criterion_of_analytic_bounds {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hmid :
      UniformKorseltTriple n →
        Real.log n ∈ Set.Icc (42410 : ℝ) 7000000 →
        HasRejectingPrime n
          (max 2
            (max ((1 / 4 : ℝ) * Real.log n ^ 2)
              ((9090 / 33659 : ℝ) * Real.log n ^ 2 -
                (64 / 5 : ℝ) * Real.log n * Real.exp (-(Real.log n / 1000000) ^ 2)))))
    (hhigh :
      UniformKorseltTriple n →
        6300000 ≤ Real.log n →
        GaussianHighLowerBounds n ((0.270061456043740 : ℝ) * Real.log n ^ 2)) :
    (∀ p : ℕ,
        p.Prime →
          (p : ℝ) ≤ gaussianWitnessCutoff (Real.log n) →
          PrimeTest.StrongMillerRabinPass n (p : ZMod n)) ↔
      n.Prime := by
  apply gaussian_criterion_of_uniform_witness hn ho hg
  intro hu hL
  apply uniform_gaussian_witness_of_upper hn ho hu hL hg (hmid hu)
  intro hU
  have hp : 0 < Real.log n := (by norm_num only : (0 : ℝ) < 6300000).trans_le hU
  exact
    (gaussian_high_witness_of_bounds hn ho hu hg
          (mul_pos (by norm_num only : (0 : ℝ) < 0.270061456043740) (sq_pos_of_pos hp))
          (hhigh hu hU)).mono
      (le_max_right _ _)

private theorem compensated_trace_lower {t b c : ℝ} (ht : t ∈ Set.Icc (-1) 3) (hc : 0 ≤ c)
    (hn : -b ≤ c) : -b - 4 * c ≤ t * b := by
  by_cases hb : 0 ≤ b
  · have h := mul_le_mul_of_nonneg_right ht.1 hb
    linarith only [h, hc]
  · have h := mul_le_mul_of_nonpos_right ht.2 (le_of_not_ge hb)
    linarith only [h, hn]

/-- Under passage through X, the trace is three at supported prime powers
through X. Beyond X, the signed kernel uses the compensation from H13. -/
theorem gaussian_forward_trace_lower {n p q r : ℕ} [NeZero p] [NeZero q] [NeZero r] [NeZero n]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n) (hprod : n = p * q * r) (hp : Odd p)
    (hq : Odd q) (hr : Odd r) {X : ℝ}
    (hpass : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → PrimeTest.StrongMillerRabinPass n (l : ZMod n))
    (S : Finset ℕ) (B C : ℕ → ℝ) (hc : ∀ m ∈ S, 0 ≤ C m ∧ -B m ≤ C m) :
    (∑ m ∈ S,
        ArithmeticFunction.vonMangoldt m * (if (m : ℝ) ≤ X then 3 * B m else -B m - 4 * C m)) ≤
      ∑ m ∈ S,
        ArithmeticFunction.vonMangoldt m *
          (((NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq) m).re +
              (NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr) m).re +
              (NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr) m).re) *
            B m) := by
  let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
  let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
  let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
  obtain ⟨_, _, _, _, _, _, hsmall⟩ := pair_data_of_uniform_pass hn ho hu hprod hp hq hr X hpass
  apply Finset.sum_le_sum
  intro m hm
  change _ ≤ ArithmeticFunction.vonMangoldt m * (((a m).re + (b m).re + (c m).re) * B m)
  by_cases hΛ : ArithmeticFunction.vonMangoldt m = 0
  · simp only [hΛ, zero_mul, le_refl]
  apply mul_le_mul_of_nonneg_left _ ArithmeticFunction.vonMangoldt_nonneg
  by_cases hcut : (m : ℝ) ≤ X
  · obtain ⟨l, k, hl, hk, rfl⟩ :=
      (isPrimePow_nat_iff m).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ)
    have hlX := (Nat.cast_le.mpr (Nat.le_self_pow hk.ne' l)).trans hcut
    obtain ⟨ha, hb, hcc⟩ := hsmall l hl hlX
    change a l = 1 at ha
    change b l = 1 at hb
    change c l = 1 at hcc
    rw [ite_eq_left hcut]
    simp only [Nat.cast_pow, map_pow, ha, hb, hcc, one_pow, Complex.one_re]
    norm_num only [le_refl]
  · rw [ite_eq_right hcut]
    have hlow : -1 ≤ (a m).re + (b m).re + (c m).re := by
      simpa only [a, b, c, Int.cast_natCast] using
        pair_character_sum_ge_neg_one (m : ℤ) p q r (hp.mul hq) (hp.mul hr) (hq.mul hr)
    have htop : (a m).re + (b m).re + (c m).re ≤ 3 := by
      linarith only [(Complex.re_le_norm (a m)).trans (a.norm_le_one _),
        (Complex.re_le_norm (b m)).trans (b.norm_le_one _),
        (Complex.re_le_norm (c m)).trans (c.norm_le_one _)]
    exact compensated_trace_lower ⟨hlow, htop⟩ (hc m hm).1 (hc m hm).2

private theorem gaussian_forward_tail_charge {n p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    [NeZero n] [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)]
    [Fact (2 < r)] (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n) (hprod : n = p * q * r)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) {X Y : ℝ}
    (hpass : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → PrimeTest.StrongMillerRabinPass n (l : ZMod n))
    (B : ℕ → ℝ) (C : ℝ → ℝ) (hC : ∀ m ∈ Finset.Ioc ⌊X⌋₊ ⌊Y⌋₊, 0 ≤ C m ∧ -B m ≤ C m) {Q : ℝ}
    (hc : (∑ m ∈ Finset.Ioc ⌊X⌋₊ ⌊Y⌋₊, ArithmeticFunction.vonMangoldt m * C m) ≤ Q) :
    let S := Finset.Ioc ⌊X⌋₊ ⌊Y⌋₊
    let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
    let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr);
    -(∑ m ∈ S, ArithmeticFunction.vonMangoldt m * B m) - 4 * Q ≤
      ∑ m ∈ S, ArithmeticFunction.vonMangoldt m * (((a m).re + (b m).re + (c m).re) * B m) := by
  intro S a b c
  calc
    _ ≤
        -(∑ m ∈ S, ArithmeticFunction.vonMangoldt m * B m) -
          4 * (∑ m ∈ S, ArithmeticFunction.vonMangoldt m * C m) :=
      by
      dsimp only [S]
      linarith only [hc]
    _ =
        ∑ m ∈ S,
          ArithmeticFunction.vonMangoldt m * (if (m : ℝ) ≤ X then 3 * B m else -B m - 4 * C m) :=
      by
      rw [← Finset.sum_neg_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro m hm
      rw [ite_eq_right (not_le.mpr (Nat.lt_of_floor_lt (Finset.mem_Ioc.mp hm).1))]
      ring
    _ ≤ _ := gaussian_forward_trace_lower hn ho hu hprod hp hq hr hpass S B (fun m ↦ C m) hC

/-- The forward trace on (X,Y] has a lower bound with the smooth H16
compensation charge. The kernel and its majorant may vary with the cutoff. -/
theorem gaussian_forward_tail_lower {n p q r : ℕ} [NeZero p] [NeZero q] [NeZero r] [NeZero n]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n) (hprod : n = p * q * r) (hp : Odd p)
    (hq : Odd q) (hr : Odd r) (hRH : RiemannHypothesis) {X Y : ℝ} (hX : 1000000 ≤ X) (hXY : X ≤ Y)
    (hpass : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → PrimeTest.StrongMillerRabinPass n (l : ZMod n))
    (B : ℕ → ℝ) (C : ℝ → ℝ) (hC : ∀ m ∈ Finset.Ioc ⌊X⌋₊ ⌊Y⌋₊, 0 ≤ C m ∧ -B m ≤ C m)
    (hd : ∀ t ∈ Set.Icc X Y, DifferentiableAt ℝ C t)
    (hi : MeasureTheory.IntegrableOn (deriv C) (Set.Icc X Y)) (hCX : C X = 0) (hCY : C Y = 0) :
    let S := Finset.Ioc ⌊X⌋₊ ⌊Y⌋₊
    let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
    let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr);
    -(∑ m ∈ S, ArithmeticFunction.vonMangoldt m * B m) -
        4 * ((∫ t in X..Y, C t) + Real.log Y ^ 2 / 24 * (∫ t in X..Y, Real.sqrt t * |deriv C t|)) ≤
      ∑ m ∈ S, ArithmeticFunction.vonMangoldt m * (((a m).re + (b m).re + (c m).re) * B m) := by
  exact
    gaussian_forward_tail_charge hn ho hu hprod hp hq hr hpass B C hC
      (gaussian_compensation_interval hRH hX hXY hd hi hCX hCY)

/-- Bound the high forward trace using the charges of a piecewise compensation profile. -/
theorem gaussian_forward_partition_lower {n p q r : ℕ} [NeZero p] [NeZero q] [NeZero r] [NeZero n]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n) (hprod : n = p * q * r) (hp : Odd p)
    (hq : Odd q) (hr : Odd r) (hRH : RiemannHypothesis) (k : ℕ) (x : ℕ → ℝ) (hx : Monotone x)
    (ha : 1000000 ≤ x 0)
    (hpass : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ x 0 → PrimeTest.StrongMillerRabinPass n (l : ZMod n))
    (B : ℕ → ℝ) (C : ℝ → ℝ) (hC : ∀ m ∈ Finset.Ioc ⌊x 0⌋₊ ⌊x k⌋₊, 0 ≤ C m ∧ -B m ≤ C m)
    (f : ℕ → ℝ → ℝ) (hm : ∀ j < k, ∀ t ∈ Set.Icc (x j) (x (j + 1)), f j t = C t)
    (hd : ∀ j < k, ∀ t ∈ Set.Icc (x j) (x (j + 1)), DifferentiableAt ℝ (f j) t)
    (hi : ∀ j < k, MeasureTheory.IntegrableOn (deriv (f j)) (Set.Icc (x j) (x (j + 1))))
    (h0 : C (x 0) = 0) (hk : C (x k) = 0) :
    let S := Finset.Ioc ⌊x 0⌋₊ ⌊x k⌋₊
    let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
    let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr);
    -(∑ m ∈ S, ArithmeticFunction.vonMangoldt m * B m) -
        4 *
          (∑ j ∈ Finset.range k,
            ((∫ t in x j..x (j + 1), f j t) +
              Real.log (x (j + 1)) ^ 2 / 24 *
                (∫ t in x j..x (j + 1), Real.sqrt t * |deriv (f j) t|))) ≤
      ∑ m ∈ S, ArithmeticFunction.vonMangoldt m * (((a m).re + (b m).re + (c m).re) * B m) := by
  exact
    gaussian_forward_tail_charge hn ho hu hprod hp hq hr hpass B C hC
      (gaussian_compensation_partition hRH k x hx ha C f hm hd hi h0 hk)

/-- Passage through the cutoff gives the signed Euler lower bound for
the three Jacobi pair characters with either high Gaussian kernel. -/
theorem gaussian_high_pair_euler_lower (hRH : RiemannHypothesis) (K : HighGaussianKernel)
    {n p q r : ℕ} [NeZero p] [NeZero q] [NeZero r] [NeZero n] [Fact p.Prime] [Fact q.Prime]
    [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)] (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hprod : n = p * q * r) (hp : Odd p) (hq : Odd q) (hr : Odd r)
    {X : ℝ} (hX : 1000000 ≤ X)
    (hpass : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
    let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
    let v := fun m : ℕ ↦ 5 - Real.log ((m : ℝ) / X)
    let B := fun m : ℕ ↦
      ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-(1 / 2) : ℝ) * Real.exp (-(K.pole : ℝ) * v m) *
        K.realProfile.eval (v m)
    4 * (∑ m ∈ Finset.Ioc 0 ⌊X⌋₊, B m) - (∑ m ∈ Finset.Ioc 0 ⌊X * Real.exp 5⌋₊, B m) -
        4 * highCompensationBound K X ≤
      ∑ m ∈ Finset.Ioc 0 ⌊X * Real.exp 5⌋₊, ((a m).re + (b m).re + (c m).re) * B m := by
  intro a b c v B
  refine high_euler_sum_lower hRH K hX (fun m ↦ (a m).re + (b m).re + (c m).re) ?_ ?_
  · intro m
    constructor
    · simpa only [a, b, c, Int.cast_natCast] using
        pair_character_sum_ge_neg_one (m : ℤ) p q r (hp.mul hq) (hp.mul hr) (hq.mul hr)
    · linarith only [(Complex.re_le_norm (a m)).trans (a.norm_le_one _),
        (Complex.re_le_norm (b m)).trans (b.norm_le_one _),
        (Complex.re_le_norm (c m)).trans (c.norm_le_one _)]
  · intro m hm hΛ
    have hmX :=
      (Nat.le_floor_iff ((by norm_num only : (0 : ℝ) ≤ 1000000).trans hX)).mp
        (Finset.mem_Ioc.mp hm).2
    obtain ⟨_, _, _, _, _, _, hsmall⟩ := pair_data_of_uniform_pass hn ho hu hprod hp hq hr X hpass
    obtain ⟨l, k, hl, hk, rfl⟩ :=
      (isPrimePow_nat_iff m).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ)
    have hlX := (Nat.cast_le.mpr (Nat.le_self_pow hk.ne' l)).trans hmX
    obtain ⟨ha, hb, hc⟩ := hsmall l hl hlX
    change a l = 1 at ha
    change b l = 1 at hb
    change c l = 1 at hc
    simp only [Nat.cast_pow, map_pow, ha, hb, hc, one_pow, Complex.one_re]
    norm_num only

/-- The real part of the arithmetic transform is the signed real-profile
sum used in the compensation inequality. -/
theorem gaussian_high_arithmetic_re (K : HighGaussianKernel) {q : ℕ} (χ : DirichletCharacter ℂ q)
    {X : ℝ} (hX : 0 < X) :
    (∑' m : ℕ,
          ∑ j ∈ Finset.range (2 * K.degree + 1),
            (K.expandedCoeff j : ℂ) *
              (LLS.PaperStatements.shiftedPoleKernel (K.logPower j) K.pole 5
                    ((by decide : 1 ≤ 3).trans (Nat.le_add_left _ _))
                    (high_gaussian_pole_gt K)).summand
                χ X m).re =
      ∑ m ∈ Finset.Ioc 0 ⌊X * Real.exp 5⌋₊,
        let v := 5 - Real.log ((m : ℝ) / X)
        (χ m).re *
          (ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-(1 / 2) : ℝ) *
            Real.exp (-(K.pole : ℝ) * v) *
            K.realProfile.eval v) := by
  rw [high_gaussian_arithmetic K χ hX, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hm₀ : (0 : ℝ) < m := Nat.cast_pos.mpr (Finset.mem_Ioc.mp hm).1
  have hd := div_pos hm₀ hX
  have he :
    (((m : ℝ) / X) * Real.exp (-5)) ^ (K.pole : ℝ) =
      Real.exp (-(K.pole : ℝ) * (5 - Real.log ((m : ℝ) / X))) := by
    rw [Real.rpow_def_of_pos (mul_pos hd (Real.exp_pos _)),
      Real.log_mul hd.ne' (Real.exp_pos _).ne', Real.log_exp]
    congr 1
    ring
  rw [he]
  simp only [← high_real_profile_eval, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, mul_zero, sub_zero, zero_add, Real.rpow_neg hm₀.le,
    ← Real.sqrt_eq_rpow]
  rw [div_eq_mul_inv (ArithmeticFunction.vonMangoldt m)]
  ring

/-- The arithmetic term of the high Gaussian explicit formula for one character. -/
noncomputable def highGaussianArithmetic (K : HighGaussianKernel) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (X : ℝ) : ℂ :=
  ∑' m : ℕ,
    ∑ j ∈ Finset.range (2 * K.degree + 1),
      (K.expandedCoeff j : ℂ) *
        (LLS.PaperStatements.shiftedPoleKernel (K.logPower j) K.pole 5
              ((by decide : 1 ≤ 3).trans (Nat.le_add_left _ _)) (high_gaussian_pole_gt K)).summand
          χ X m

/-- The lower bound under passage controls the sum of the three explicit
formula arithmetic terms, with the unsigned principal difference on the left. -/
theorem gaussian_high_arithmetic_lower (hRH : RiemannHypothesis) (K : HighGaussianKernel)
    {n p q r : ℕ} [NeZero p] [NeZero q] [NeZero r] [NeZero n] [Fact p.Prime] [Fact q.Prime]
    [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)] (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hprod : n = p * q * r) (hp : Odd p) (hq : Odd q) (hr : Odd r)
    {X : ℝ} (hX : 1000000 ≤ X)
    (hpass : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
    let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
    let v := fun m : ℕ ↦ 5 - Real.log ((m : ℝ) / X)
    let B := fun m : ℕ ↦
      ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-(1 / 2) : ℝ) * Real.exp (-(K.pole : ℝ) * v m) *
        K.realProfile.eval (v m)
    4 * (∑ m ∈ Finset.Ioc 0 ⌊X⌋₊, B m) - (∑ m ∈ Finset.Ioc 0 ⌊X * Real.exp 5⌋₊, B m) -
        4 * highCompensationBound K X ≤
      (highGaussianArithmetic K a X).re + (highGaussianArithmetic K b X).re +
        (highGaussianArithmetic K c X).re := by
  intro a b c v B
  have hpos := (by norm_num only : (0 : ℝ) < 1000000).trans_le hX
  have he := gaussian_high_pair_euler_lower hRH K hn ho hu hprod hp hq hr hX hpass
  refine he.trans_eq ?_
  simp only [highGaussianArithmetic, gaussian_high_arithmetic_re K _ hpos, add_mul,
    Finset.sum_add_distrib, a, b, c]

/-- The two contour integrals in the high Gaussian formula, with the
zero contribution accounted for separately in the zero score. -/
noncomputable def highGaussianContourTerms (K : HighGaussianKernel) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (X : ℝ) : ℂ :=
  let H := fun j : ℕ ↦
    LLS.PaperStatements.shiftedPoleKernel (K.logPower j) K.pole 5
      ((by decide : 1 ≤ 3).trans (Nat.le_add_left _ _)) (high_gaussian_pole_gt K)
  let d := min (((K.pole : ℝ) - 1 / 2) / 4) (1 / 8)
  let a := -1 / 2 - d / 2
  let t := 1 / 2 + d / 2
  let W := fun j (z : ℂ) ↦ (H j).function z * (X : ℂ) ^ z
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ v : ℝ,
        ∑ j ∈ Finset.range (2 * K.degree + 1),
          (K.expandedCoeff j : ℂ) *
            (-logDeriv χ.completedLFunction (((a : ℂ) + Complex.I * v) + 1 / 2) *
              W j ((a : ℂ) + Complex.I * v))) +
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ v : ℝ,
        ∑ j ∈ Finset.range (2 * K.degree + 1),
          (K.expandedCoeff j : ℂ) *
            (logDeriv χ.gammaFactor (((t : ℂ) + Complex.I * v) + 1 / 2) *
              W j ((t : ℂ) + Complex.I * v)))

/-- Apply the shifted-pole explicit formula and identify its zero term
with the signed high Gaussian zero summand. -/
theorem high_gaussian_arithmetic_contours (K : HighGaussianKernel) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hq : 2 ≤ q) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {X : ℝ} (hX : 1 ≤ X) :
    highGaussianArithmetic K χ X =
      -(∑' γ : ℂ, K.zeroTerm χ X γ) + highGaussianContourTerms K χ X := by
  have h :=
    LLS.PaperStatements.shiftedPole_polynomial_contours (Finset.range (2 * K.degree + 1)) K.logPower
      (fun j ↦ (K.expandedCoeff j : ℂ)) (fun _ ↦ (by decide : 1 ≤ 3).trans (Nat.le_add_left _ _))
      (b := 5) (high_gaussian_pole_gt K) hX hq hGRH hp hne hinv
  rw [highGaussianArithmetic, high_gaussian_arithmetic K χ (zero_lt_one.trans_le hX)]
  simp only [HighGaussianKernel.profilePoly]
  rw [h]
  dsimp only [HighGaussianKernel.zeroTerm, highGaussianContourTerms]
  simp only [LLS.PaperStatements.shiftedPole_weightedResidue_zero, mul_zero, Finset.sum_const_zero,
    zero_sub]
  ring

/-- The compensated arithmetic lower bound controls the signed zero score
up to the contour terms of the three primitive pair characters. -/
theorem gaussian_high_zero_score_lower
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (K : HighGaussianKernel)
    {n p q r : ℕ} [NeZero p] [NeZero q] [NeZero r] [NeZero n] [Fact p.Prime] [Fact q.Prime]
    [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)] (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hprod : n = p * q * r) (hp : Odd p) (hq : Odd q) (hr : Odd r)
    {X : ℝ} (hX : 1000000 ≤ X)
    (hpass : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
    let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
    let v := fun m : ℕ ↦ 5 - Real.log ((m : ℝ) / X)
    let B := fun m : ℕ ↦
      ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-(1 / 2) : ℝ) * Real.exp (-(K.pole : ℝ) * v m) *
        K.realProfile.eval (v m)
    4 * (∑ m ∈ Finset.Ioc 0 ⌊X⌋₊, B m) - (∑ m ∈ Finset.Ioc 0 ⌊X * Real.exp 5⌋₊, B m) -
        4 * highCompensationBound K X ≤
      gaussianPairZeroScore K X hp hq hr + (highGaussianContourTerms K a X).re +
        (highGaussianContourTerms K b X).re +
        (highGaussianContourTerms K c X).re := by
  intro a b c v B
  obtain ⟨hpq, hpr, hqr, ha, hb, hc, _⟩ := pair_data_of_uniform_pass hn ho hu hprod hp hq hr X hpass
  have h₁ := (by norm_num only : (1 : ℝ) ≤ 1000000).trans hX
  have ea := high_gaussian_arithmetic_contours K hGRH hpq ha.1 ha.2.1 (ha.2.2.1.symm ▸ ha.2.1) h₁
  have eb := high_gaussian_arithmetic_contours K hGRH hpr hb.1 hb.2.1 (hb.2.2.1.symm ▸ hb.2.1) h₁
  have ec := high_gaussian_arithmetic_contours K hGRH hqr hc.1 hc.2.1 (hc.2.2.1.symm ▸ hc.2.1) h₁
  have h := gaussian_high_arithmetic_lower hGRH.riemann K hn ho hu hprod hp hq hr hX hpass
  dsimp only at h
  rw [ea, eb, ec] at h
  simp only [Complex.add_re, Complex.neg_re] at h
  unfold gaussianPairZeroScore
  dsimp only [a, b, c, v, B]
  linarith only [h]

/-- Reassemble the contour integrand into the square kernel before
estimating it. The common logarithmic derivative and cutoff weight factor out. -/
theorem high_gaussian_contour_integrand (K : HighGaussianKernel) (X : ℝ) (z D : ℂ)
    (hz : z + (K.pole : ℂ) ≠ 0) :
    (∑ j ∈ Finset.range (2 * K.degree + 1),
        (K.expandedCoeff j : ℂ) *
          (D *
            ((LLS.PaperStatements.shiftedPoleKernel (K.logPower j) K.pole 5
                    ((by decide : 1 ≤ 3).trans (Nat.le_add_left _ _))
                    (high_gaussian_pole_gt K)).function
                z *
              (X : ℂ) ^ z))) =
      D *
        ((K.normalization : ℂ) * Complex.exp (5 * z) *
            (K.polynomial.eval₂ (Rat.castHom ℂ) (z + (K.pole : ℂ))) ^ 2 /
          (z + (K.pole : ℂ)) ^ (2 * K.degree + 4)) *
        (X : ℂ) ^ z := by
  rw [← high_gaussian_kernel_sum K hz, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  simp only [LLS.PaperStatements.shiftedPoleKernel, div_eq_mul_inv, Complex.ofReal_ratCast]
  norm_num only [Complex.ofReal_ofNat]
  ring

/-- The high Gaussian square transform evaluated at a complex argument. -/
noncomputable def highGaussianSquare (K : HighGaussianKernel) (z : ℂ) : ℂ :=
  (K.normalization : ℂ) * Complex.exp (5 * z) *
      (K.polynomial.eval₂ (Rat.castHom ℂ) (z + (K.pole : ℂ))) ^ 2 /
    (z + (K.pole : ℂ)) ^ (2 * K.degree + 4)

private theorem high_contour_width (K : HighGaussianKernel) :
    min (((K.pole : ℝ) - 1 / 2) / 4) (1 / 8) = 1 / 8 := by
  cases K <;>
    norm_num only [HighGaussianKernel.pole, Rat.cast_div, Rat.cast_ofNat, min_def, ite_false]

private theorem high_contour_away_from_pole (K : HighGaussianKernel) {a : ℝ}
    (ha : -(9 / 16 : ℝ) ≤ a) (v : ℝ) : (a : ℂ) + Complex.I * v + (K.pole : ℂ) ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero, ← Complex.ofReal_ratCast,
    Complex.zero_re] at hr
  have hp : (9 / 16 : ℝ) < K.pole := by
    cases K <;> norm_num only [HighGaussianKernel.pole, Rat.cast_div, Rat.cast_ofNat]
  linarith only [ha, hp, hr]

/-- On the left and right lines of the high explicit formula, the contour
terms are the logarithmic derivatives integrated against the square kernel. -/
theorem high_gaussian_contours_square (K : HighGaussianKernel) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (X : ℝ) :
    let l := fun v : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * v
    let r := fun v : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * v
    let W := fun z : ℂ ↦ highGaussianSquare K z * (X : ℂ) ^ z
    highGaussianContourTerms K χ X =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ v : ℝ, -logDeriv χ.completedLFunction (l v + 1 / 2) * W (l v)) +
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ v : ℝ, logDeriv χ.gammaFactor (r v + 1 / 2) * W (r v)) := by
  intro l r W
  have hl : (-1 / 2 - (1 / 8) / 2 : ℝ) = -9 / 16 := by norm_num only
  have hr : (1 / 2 + (1 / 8) / 2 : ℝ) = 9 / 16 := by norm_num only
  simp only [highGaussianContourTerms, high_contour_width, hl, hr, l, r, W]
  congr 2
  · apply MeasureTheory.integral_congr_ae
    exact
      Filter.Eventually.of_forall
        (fun v ↦ by
          dsimp only
          rw [high_gaussian_contour_integrand K X _ _
              (high_contour_away_from_pole K (a := -9 / 16) (by norm_num only) v),
            highGaussianSquare, mul_assoc])
  · apply MeasureTheory.integral_congr_ae
    exact
      Filter.Eventually.of_forall
        (fun v ↦ by
          dsimp only
          rw [high_gaussian_contour_integrand K X _ _
              (high_contour_away_from_pole K (a := 9 / 16) (by norm_num only) v),
            highGaussianSquare, mul_assoc])

/-- The right-contour gamma integrand is the same for all even characters,
so it is independent of the conductor in the character-minus-xi comparison. -/
theorem high_gaussian_even_gamma {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (he : χ.Even)
    (z : ℂ) : logDeriv χ.gammaFactor z = logDeriv (1 : DirichletCharacter ℂ 1).gammaFactor z := by
  have hg : χ.gammaFactor = (1 : DirichletCharacter ℂ 1).gammaFactor := by
    funext w
    rw [he.gammaFactor_def,
      AnalyticNumberTheory.DirichletLFunction.principal_modulus_one_even.gammaFactor_def]
  rw [hg]

/-- Subtracting the principal contour terms from those of an even
character cancels the right-side gamma integral exactly. -/
theorem high_gaussian_contour_sub_principal {q : ℕ} [NeZero q] (K : HighGaussianKernel)
    (χ : DirichletCharacter ℂ q) (he : χ.Even) (X : ℝ) :
    let l := fun v : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * v
    let W := fun z : ℂ ↦ highGaussianSquare K z * (X : ℂ) ^ z
    let d := ((1 / (2 * Real.pi) : ℝ) : ℂ)
    highGaussianContourTerms K χ X - highGaussianContourTerms K (1 : DirichletCharacter ℂ 1) X =
      d * (∫ v : ℝ, -logDeriv χ.completedLFunction (l v + 1 / 2) * W (l v)) -
        d *
          (∫ v : ℝ,
            -logDeriv (1 : DirichletCharacter ℂ 1).completedLFunction (l v + 1 / 2) * W (l v)) := by
  rw [high_gaussian_contours_square, high_gaussian_contours_square]
  simp only [high_gaussian_even_gamma χ he, add_sub_add_right_eq_sub]

/-- Reflect the high-kernel left contour difference to the line
Re s = 17/16 and preserve integrability of the reflected integrand. -/
theorem high_gaussian_left_reflected (K : HighGaussianKernel) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hn : χ ≠ 1) (hi : χ⁻¹ = χ) (he : χ.Even)
    {X : ℝ} (hX : 0 < X) :
    let l := fun v : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * v
    let w := fun v : ℝ ↦ ((17 / 16 : ℝ) : ℂ) - Complex.I * v
    let W := fun v ↦ highGaussianSquare K (l v) * (X : ℂ) ^ l v
    let A := fun v ↦
      (Complex.log q + logDeriv χ.LFunction (w v) - logDeriv riemannZeta (w v) - 1 / w v -
          1 / (w v - 1)) *
        W v
    ((∫ v : ℝ, -logDeriv χ.completedLFunction (l v + 1 / 2) * W v) -
          (∫ v : ℝ, -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (l v + 1 / 2) * W v) =
        ∫ v : ℝ, A v) ∧
      MeasureTheory.Integrable A ∧
      MeasureTheory.Integrable
        (fun v ↦ -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (l v + 1 / 2) * W v) := by
  intro l w W A
  let H := fun j : ℕ ↦
    LLS.PaperStatements.shiftedPoleKernel (K.logPower j) K.pole 5
      ((by decide : 1 ≤ 3).trans (Nat.le_add_left _ _)) (high_gaussian_pole_gt K)
  have hd (j : ℕ) : (H j).delta = 1 / 8 := by
    rw [LLS.PaperStatements.shiftedPoleKernel_delta, high_contour_width]
  have hline (j : ℕ) : -1 / 2 - (H j).delta < (-9 / 16 : ℝ) := by
    rw [hd]
    norm_num only
  have hInt (D : ℝ → ℂ)
    (hD :
      ∀ j, MeasureTheory.Integrable (fun v : ℝ ↦ D v * ((H j).function (l v) * (X : ℂ) ^ l v))) :
    MeasureTheory.Integrable (fun v ↦ D v * W v) := by
    have hs :=
      MeasureTheory.integrable_finsetSum (Finset.range (2 * K.degree + 1))
        (fun j _ ↦ (hD j).const_mul (K.expandedCoeff j : ℂ))
    refine hs.congr (Filter.Eventually.of_forall (fun v ↦ ?_))
    exact
      (high_gaussian_contour_integrand K X (l v) (D v)
            (high_contour_away_from_pole K (a := -9 / 16) (by norm_num only) v)).trans
        (mul_assoc _ _ _)
  have hχ :=
    hInt (fun v ↦ -logDeriv χ.completedLFunction (l v + 1 / 2))
      (fun j ↦
        LLS.PaperStatements.MellinKernel.integrable_completed_left_line (H j) hp hn (hi.symm ▸ hn)
          (hline j) (by norm_num only) (by norm_num only) hX)
  have hξ :=
    hInt (fun v ↦ -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (l v + 1 / 2))
      (fun j ↦
        LLS.PaperStatements.MellinKernel.integrable_xi_left_line (H j) (hline j) (by norm_num only)
          (by norm_num only) hX)
  have heq (v : ℝ) :
    ((fun t ↦ -logDeriv χ.completedLFunction (l t + 1 / 2) * W t) - fun t ↦
          -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (l t + 1 / 2) * W t)
        v =
      A v := by
    have h := congrArg (fun z : ℂ ↦ z * W v) (twoShift_left_log_difference hp hn hi he v)
    simpa only [Pi.sub_apply, A, l, w, add_mul, neg_mul, sub_neg_eq_add] using h
  refine ⟨?_, (hχ.sub hξ).congr (Filter.Eventually.of_forall heq), hξ⟩
  rw [← MeasureTheory.integral_sub hχ hξ]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall heq)

/-- On either contour line, the square kernel inverts to the finite sum of
shifted-pole profiles at every positive scale, including outside the support. -/
theorem high_gaussian_square_inverse_sum (K : HighGaussianKernel) {c u : ℝ} (hc : -(9 / 16 : ℝ) ≤ c)
    (hc' : c ≤ 9 / 16) (hne : c ≠ -1 / 2) (hu : 0 < u) :
    Analysis.inverseMellin (highGaussianSquare K) c u =
      ∑ j ∈ Finset.range (2 * K.degree + 1),
        (K.expandedCoeff j : ℂ) *
          (LLS.PaperStatements.shiftedPoleKernel (K.logPower j) K.pole 5
                ((by decide : 1 ≤ 3).trans (Nat.le_add_left _ _))
                (high_gaussian_pole_gt K)).transform
            u := by
  let H := fun j : ℕ ↦
    LLS.PaperStatements.shiftedPoleKernel (K.logPower j) K.pole 5
      ((by decide : 1 ≤ 3).trans (Nat.le_add_left _ _)) (high_gaussian_pole_gt K)
  let l := fun t : ℝ ↦ (c : ℂ) + Complex.I * t
  have hp : (9 / 16 : ℝ) < K.pole := by
    cases K <;> norm_num only [HighGaussianKernel.pole, Rat.cast_div, Rat.cast_ofNat]
  have hH (j : ℕ) : Analysis.inverseMellin (H j).function c u = (H j).transform u := by
    rw [LLS.PaperStatements.shiftedPoleKernel_transform _ _ _ _ _ hu]
    exact
      Analysis.inverseMellin_shiftedPole ((by decide : 1 ≤ 3).trans (Nat.le_add_left _ _))
        (by linarith only [hp, hc]) hu 5
  have hi (j : ℕ) :
    MeasureTheory.Integrable
      (fun t : ℝ ↦ (K.expandedCoeff j : ℂ) * ((H j).function (l t) * (u : ℂ) ^ (-(l t)))) := by
    have hd : (H j).delta = 1 / 8 := by
      rw [LLS.PaperStatements.shiftedPoleKernel_delta, high_contour_width]
    have hm :=
      LLS.PaperStatements.MellinKernel.integrable_logWeighted_power_line (H j) (c := c) (x := u⁻¹)
        (F := fun _ ↦ (1 : ℂ)) (A := 1)
        (by
          rw [hd]; linarith only [hc])
        (by
          rw [hd]; linarith only [hc'])
        hne (inv_pos.mpr hu) continuous_const.aestronglyMeasurable
        (fun t ↦ by
          simpa only [norm_one, one_mul, le_add_iff_nonneg_left] using
            Real.log_nonneg (show 1 ≤ 4 + |t| from by linarith only [abs_nonneg t]))
    simpa only [l, one_mul, Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg hu.le,
      Complex.cpow_neg] using hm.const_mul (K.expandedCoeff j : ℂ)
  calc
    _ =
        ∑ j ∈ Finset.range (2 * K.degree + 1),
          (K.expandedCoeff j : ℂ) * Analysis.inverseMellin (H j).function c u :=
      by
      simp only [Analysis.inverseMellin, mul_left_comm (↑(K.expandedCoeff _) : ℂ), ← Finset.mul_sum]
      congr 1
      simp only [← MeasureTheory.integral_const_mul (K.expandedCoeff _ : ℂ)]
      rw [← MeasureTheory.integral_finsetSum _ (fun j _ ↦ hi j)]
      apply MeasureTheory.integral_congr_ae
      exact
        Filter.Eventually.of_forall
          (fun t ↦ by
            have he :=
              high_gaussian_contour_integrand K 1 (l t) 1 (high_contour_away_from_pole K hc t)
            simp only [Complex.ofReal_one, Complex.one_cpow, mul_one, one_mul] at he
            change
              highGaussianSquare K (l t) * (u : ℂ) ^ (-(l t)) =
                ∑ j ∈ Finset.range (2 * K.degree + 1),
                  (K.expandedCoeff j : ℂ) * ((H j).function (l t) * (u : ℂ) ^ (-(l t)))
            simp only [← mul_assoc, ← Finset.sum_mul]
            exact congrArg (· * (u : ℂ) ^ (-(l t))) he.symm)
    _ = _ := by simp only [hH, H]

/-- The inverse Mellin integral of the square transform on the left line
gives the physical profile inside its support. -/
theorem high_gaussian_square_inverse (K : HighGaussianKernel) {u : ℝ} (hu : 0 < u)
    (hu₅ : u ≤ Real.exp 5) :
    Analysis.inverseMellin (highGaussianSquare K) (-9 / 16) u =
      (((u * Real.exp (-5)) ^ (K.pole : ℝ) : ℝ) : ℂ) * K.profilePoly (5 - Real.log u) := by
  rw [high_gaussian_square_inverse_sum K (by norm_num only) (by norm_num only) (by norm_num only)
      hu]
  exact
    LLS.PaperStatements.shiftedPole_transform_sum (Finset.range (2 * K.degree + 1)) K.logPower
      (fun j ↦ (K.expandedCoeff j : ℂ)) (fun _ ↦ (by decide : 1 ≤ 3).trans (Nat.le_add_left _ _))
      (high_gaussian_pole_gt K) hu hu₅

/-- On either contour, the inverse kernel vanishes beyond the modulation cutoff. -/
theorem high_gaussian_square_inverse_zero (K : HighGaussianKernel) {c u : ℝ}
    (hc : -(9 / 16 : ℝ) ≤ c) (hc' : c ≤ 9 / 16) (hne : c ≠ -1 / 2) (hu : Real.exp 5 ≤ u) :
    Analysis.inverseMellin (highGaussianSquare K) c u = 0 := by
  rw [high_gaussian_square_inverse_sum K hc hc' hne ((Real.exp_pos _).trans_le hu)]
  exact
    LLS.PaperStatements.shiftedPole_transform_sum_zero (Finset.range (2 * K.degree + 1)) K.logPower
      (fun j ↦ (K.expandedCoeff j : ℂ)) (fun _ ↦ (by decide : 1 ≤ 3).trans (Nat.le_add_left _ _))
      (high_gaussian_pole_gt K) hu

/-- The constant logarithmic conductor term on the left contour equals
the conductor logarithm times the physical profile at reciprocal scale. -/
theorem high_gaussian_left_conductor (K : HighGaussianKernel) (q : ℕ) {X : ℝ} (hX : 1 ≤ X) :
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ, Complex.log q * (highGaussianSquare K (l t) * (X : ℂ) ^ l t)) =
      Complex.log q * (((X⁻¹ * Real.exp (-5)) ^ (K.pole : ℝ) : ℝ) : ℂ) *
        K.profilePoly (5 - Real.log X⁻¹) := by
  intro l
  have hp := zero_lt_one.trans_le hX
  have hu : X⁻¹ ≤ Real.exp 5 :=
    (inv_le_one_of_one_le₀ hX).trans (Real.one_le_exp (by norm_num only))
  have he := high_gaussian_square_inverse K (inv_pos.mpr hp) hu
  unfold Analysis.inverseMellin at he
  simp only [Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg hp.le, Complex.cpow_neg,
    inv_inv] at he
  rw [MeasureTheory.integral_const_mul, mul_left_comm _ (Complex.log q)]
  dsimp only [l]
  rw [he, mul_assoc]

/-- The real normalized conductor contribution on the left contour. -/
noncomputable def highConductorTerm (K : HighGaussianKernel) (q : ℕ) (X : ℝ) : ℝ :=
  let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
  (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ, Complex.log q * (highGaussianSquare K (l t) * (X : ℂ) ^ l t))).re

/-- Evaluate one real conductor contribution in the translated log coordinate. -/
theorem high_conductor_term_eq (K : HighGaussianKernel) (q : ℕ) {X : ℝ} (hX : 1 ≤ X) :
    highConductorTerm K q X =
      Real.log q * Real.exp (-(K.pole : ℝ) * (5 + Real.log X)) *
        K.realProfile.eval (5 + Real.log X) := by
  unfold highConductorTerm
  dsimp only
  rw [high_gaussian_left_conductor K q hX, Real.log_inv, sub_neg_eq_add, ← high_real_profile_eval, ←
    Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg q), ← Complex.ofReal_mul, ←
    Complex.ofReal_mul, Complex.ofReal_re]
  have hx : 0 < X := zero_lt_one.trans_le hX
  have hpow :
    (X⁻¹ * Real.exp (-5)) ^ (K.pole : ℝ) = Real.exp (-(K.pole : ℝ) * (5 + Real.log X)) := by
    rw [Real.rpow_def_of_pos (mul_pos (inv_pos.mpr hx) (Real.exp_pos _)),
      Real.log_mul (inv_pos.mpr hx).ne' (Real.exp_pos _).ne', Real.log_inv, Real.log_exp]
    congr 1
    ring
  rw [hpow]

/-- The three pair conductors contribute twice the log of the original
uniform triple, with a common physical profile and cutoff multiplier. -/
theorem high_conductor_pair_sum (K : HighGaussianKernel) {p q r n : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hr : 0 < r) (hn : n = p * q * r) {X : ℝ} (hX : 1 ≤ X) :
    highConductorTerm K (p * q) X + highConductorTerm K (p * r) X + highConductorTerm K (q * r) X =
      2 * Real.log n * Real.exp (-(K.pole : ℝ) * (5 + Real.log X)) *
        K.realProfile.eval (5 + Real.log X) := by
  have hp' := (Nat.cast_pos.mpr hp : (0 : ℝ) < p).ne'
  have hq' := (Nat.cast_pos.mpr hq : (0 : ℝ) < q).ne'
  have hr' := (Nat.cast_pos.mpr hr : (0 : ℝ) < r).ne'
  simp only [high_conductor_term_eq _ _ hX, hn, Nat.cast_mul, Real.log_mul hp' hq',
    Real.log_mul hp' hr', Real.log_mul hq' hr', Real.log_mul (mul_ne_zero hp' hq') hr']
  ring

/-- The square kernel times the positive scale factor decays at least
quadratically on either gamma contour. This allows termwise integration
of the digamma reciprocal differences. -/
theorem high_gamma_weight_quadratic (K : HighGaussianKernel) {c X : ℝ} (hc : -(9 / 16 : ℝ) ≤ c)
    (hc' : c ≤ 9 / 16) (hne : c ≠ -1 / 2) (hX : 0 < X) :
    let l := fun t : ℝ ↦ (c : ℂ) + Complex.I * t
    ∃ A : ℝ, ∀ t : ℝ, ‖highGaussianSquare K (l t) * (X : ℂ) ^ l t‖ ≤ A / (1 + t ^ 2) := by
  intro l
  let H := fun j : ℕ ↦
    LLS.PaperStatements.shiftedPoleKernel (K.logPower j) K.pole 5
      ((by decide : 1 ≤ 3).trans (Nat.le_add_left _ _)) (high_gaussian_pole_gt K)
  have hB (j : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, ‖(H j).function (l t)‖ ≤ C / (1 + t ^ 2) := by
    have hd : (H j).delta = 1 / 8 := by
      rw [LLS.PaperStatements.shiftedPoleKernel_delta, high_contour_width]
    exact
      LLS.PaperStatements.MellinKernel.exists_norm_line_le_inverseSquare (H j)
        (by
          rw [hd]; linarith only [hc])
        (by
          rw [hd]; linarith only [hc'])
        hne
  choose C _ hC using hB
  refine
    ⟨(∑ j ∈ Finset.range (2 * K.degree + 1), ‖(K.expandedCoeff j : ℂ)‖ * C j) * X ^ c, fun t ↦ ?_⟩
  have h := high_gaussian_contour_integrand K X (l t) 1 (high_contour_away_from_pole K hc t)
  have he :
    highGaussianSquare K (l t) * (X : ℂ) ^ l t =
      ∑ j ∈ Finset.range (2 * K.degree + 1),
        (K.expandedCoeff j : ℂ) * ((H j).function (l t) * (X : ℂ) ^ l t) := by
    simpa only [H, highGaussianSquare, one_mul] using h.symm
  have hr : (l t).re = c := by
    simp only [l, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  rw [he, Finset.sum_mul, Finset.sum_div]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX, hr]
  calc
    _ ≤ ‖(K.expandedCoeff j : ℂ)‖ * (C j / (1 + t ^ 2) * X ^ c) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hC j t) (Real.rpow_nonneg hX.le _))
        (norm_nonneg _)
    _ = _ := by rw [div_mul_eq_mul_div, ← mul_div_assoc, ← mul_assoc]

private theorem high_square_left_integrable (K : HighGaussianKernel) {X : ℝ} (hX : 0 < X) :
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    MeasureTheory.Integrable (fun t ↦ highGaussianSquare K (l t) * (X : ℂ) ^ l t) := by
  intro l
  let H := fun j : ℕ ↦
    LLS.PaperStatements.shiftedPoleKernel (K.logPower j) K.pole 5
      ((by decide : 1 ≤ 3).trans (Nat.le_add_left _ _)) (high_gaussian_pole_gt K)
  have hi (j : ℕ) :
    MeasureTheory.Integrable
      (fun t : ℝ ↦ (K.expandedCoeff j : ℂ) * ((H j).function (l t) * (X : ℂ) ^ l t)) := by
    have hd : (H j).delta = 1 / 8 := by
      rw [LLS.PaperStatements.shiftedPoleKernel_delta, high_contour_width]
    have hm :=
      LLS.PaperStatements.MellinKernel.integrable_logWeighted_power_line (H j) (c := -9 / 16) (F :=
        fun _ ↦ (1 : ℂ)) (A := 1)
        (by
          rw [hd]; norm_num only)
        (by
          rw [hd]; norm_num only)
        (by norm_num only) hX continuous_const.aestronglyMeasurable
        (fun t ↦ by
          simpa only [norm_one, one_mul, le_add_iff_nonneg_left] using
            Real.log_nonneg (show 1 ≤ 4 + |t| from by linarith only [abs_nonneg t]))
    simpa only [l, one_mul] using hm.const_mul (K.expandedCoeff j : ℂ)
  refine
    (MeasureTheory.integrable_finsetSum (Finset.range (2 * K.degree + 1)) (fun j _ ↦ hi j)).congr ?_
  exact
    Filter.Eventually.of_forall
      (fun t ↦ by
        have h :=
          high_gaussian_contour_integrand K X (l t) 1
            (high_contour_away_from_pole K (a := -9 / 16) (by norm_num only) t)
        simpa only [H, highGaussianSquare, one_mul] using h)

/-- The ordinary reflected logarithmic derivative is integrable against
the high kernel on the left contour. The proof sums the integrated Euler norms. -/
theorem high_reflected_ordinary_integrable (K : HighGaussianKernel) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {X : ℝ} (hX : 0 < X) :
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let r := fun t : ℝ ↦ ((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)
    MeasureTheory.Integrable
      (fun t ↦ -logDeriv χ.LFunction (r t) * (highGaussianSquare K (l t) * (X : ℂ) ^ l t)) := by
  intro l r
  let W := fun t ↦ highGaussianSquare K (l t) * (X : ℂ) ^ l t
  let f := (fun n : ℕ ↦ χ n) * (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ))
  let F := fun (m : ℕ) (t : ℝ) ↦ LSeries.term f (r t) m * W t
  have hs :=
    χ.LSeriesSummable_twist_vonMangoldt
      (show 1 < (((17 / 16 : ℝ) : ℂ)).re by norm_num only [Complex.ofReal_re])
  have hW : MeasureTheory.Integrable W := high_square_left_integrable K hX
  have hF :=
    Analysis.integrable_tsum_of_summable_integral_norm F
      (fun m ↦
        AnalyticNumberTheory.General.integrable_LSeries_term_mul_weight _ (17 / 16) m
          (fun t : ℝ ↦ -t) continuous_neg W hW)
      (AnalyticNumberTheory.General.summable_integral_norm_LSeries_term_mul_weight hs
        (fun t : ℝ ↦ -t) W)
  refine hF.congr (Filter.Eventually.of_forall fun t ↦ ?_)
  dsimp only [F]
  rw [tsum_mul_right]
  change LSeries f (r t) * W t = _
  rw [← LLS.PaperStatements.gamma_reflected_ordinary_eq_euler]

/-- Separate the reflected left contour into its constant conductor,
ordinary character, and principal remainder integrals. -/
theorem high_left_reflected_components (K : HighGaussianKernel) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hn : χ ≠ 1) (hi : χ⁻¹ = χ) (he : χ.Even)
    {X : ℝ} (hX : 0 < X) :
    let l := fun v : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * v
    let w := fun v : ℝ ↦ ((17 / 16 : ℝ) : ℂ) - Complex.I * v
    let W := fun v ↦ highGaussianSquare K (l v) * (X : ℂ) ^ l v
    let P := fun v ↦ (-logDeriv riemannZeta (w v) - 1 / w v - 1 / (w v - 1)) * W v
    ((∫ v : ℝ, -logDeriv χ.completedLFunction (l v + 1 / 2) * W v) -
          (∫ v : ℝ, -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (l v + 1 / 2) * W v) =
        (∫ v : ℝ, Complex.log q * W v) - (∫ v : ℝ, -logDeriv χ.LFunction (w v) * W v) +
          ∫ v : ℝ, P v) ∧
      MeasureTheory.Integrable P := by
  intro l w W P
  let A := fun v ↦
    (Complex.log q + logDeriv χ.LFunction (w v) - logDeriv riemannZeta (w v) - 1 / w v -
        1 / (w v - 1)) *
      W v
  let C := fun v ↦ Complex.log q * W v
  let E := fun v ↦ -logDeriv χ.LFunction (w v) * W v
  have hA := high_gaussian_left_reflected K hp hn hi he hX
  have hC : MeasureTheory.Integrable C := (high_square_left_integrable K hX).const_mul _
  have hE : MeasureTheory.Integrable E := by
    simpa only [E, w, W, l, Complex.ofReal_neg, mul_neg, ← sub_eq_add_neg] using
      high_reflected_ordinary_integrable K χ hX
  have hpoint (v : ℝ) : (A - C + E) v = P v := by
    dsimp only [Pi.add_apply, Pi.sub_apply, A, C, E, P]
    ring
  have hP : MeasureTheory.Integrable P :=
    ((hA.2.1.sub hC).add hE).congr (Filter.Eventually.of_forall hpoint)
  refine ⟨?_, hP⟩
  have hsplit : A = C - E + P := by
    funext v
    change A v = C v - E v + P v
    rw [← hpoint v]
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  change _ = (∫ v : ℝ, C v) - (∫ v : ℝ, E v) + ∫ v : ℝ, P v
  have hformula := hA.1
  change
    (∫ v : ℝ, -logDeriv χ.completedLFunction (l v + 1 / 2) * W v) -
        (∫ v : ℝ, -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (l v + 1 / 2) * W v) =
      (∫ v : ℝ, A v) at hformula
  rw [hformula, hsplit]
  change (∫ v : ℝ, (C - E) v + P v) = _
  rw [MeasureTheory.integral_add (hC.sub hE) hP]
  simp only [Pi.sub_apply, MeasureTheory.integral_sub hC hE]

/-- The real normalized ordinary reflected Euler integral for one character. -/
noncomputable def highReflectedEuler (K : HighGaussianKernel) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (X : ℝ) : ℝ :=
  let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
  let w := fun t : ℝ ↦ ((17 / 16 : ℝ) : ℂ) - Complex.I * t
  (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ, -logDeriv χ.LFunction (w t) * (highGaussianSquare K (l t) * (X : ℂ) ^ l t))).re

/-- The even-character contour contribution that is independent of the
conductor and the ordinary reflected character series. -/
noncomputable def highCommonContour (K : HighGaussianKernel) (X : ℝ) : ℝ :=
  let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
  let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
  let w := fun t : ℝ ↦ ((17 / 16 : ℝ) : ℂ) - Complex.I * t
  let W := fun z : ℂ ↦ highGaussianSquare K z * (X : ℂ) ^ z
  let d := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  (d * (∫ t : ℝ, -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (l t + 1 / 2) * W (l t))).re +
    (d * (∫ t : ℝ, logDeriv (1 : DirichletCharacter ℂ 1).gammaFactor (r t + 1 / 2) * W (r t))).re +
    (d * (∫ t : ℝ, (-logDeriv riemannZeta (w t) - 1 / w t - 1 / (w t - 1)) * W (l t))).re

/-- The common principal contour is exactly the sum of the forward and
reflected gamma-integral contributions. The Xi reflection cancels the two
polar terms and the ordinary zeta logarithmic derivative. -/
theorem high_common_contour_gamma (K : HighGaussianKernel) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hn : χ ≠ 1) (hi : χ⁻¹ = χ) (he : χ.Even)
    {X : ℝ} (hX : 0 < X) :
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
    let w := fun t : ℝ ↦ ((17 / 16 : ℝ) : ℂ) - Complex.I * t
    let W := fun z : ℂ ↦ highGaussianSquare K z * (X : ℂ) ^ z
    let d := ((1 / (2 * Real.pi) : ℝ) : ℂ)
    let γ := (1 : DirichletCharacter ℂ 1).gammaFactor
    highCommonContour K X =
      (d * (∫ t : ℝ, logDeriv γ (r t + 1 / 2) * W (r t))).re +
        (d * (∫ t : ℝ, logDeriv γ (w t) * W (l t))).re := by
  intro l r w W d γ
  let F := fun t : ℝ ↦ -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (l t + 1 / 2) * W (l t)
  let P := fun t : ℝ ↦ (-logDeriv riemannZeta (w t) - 1 / w t - 1 / (w t - 1)) * W (l t)
  let G := fun t : ℝ ↦ logDeriv γ (w t) * W (l t)
  have hF : MeasureTheory.Integrable F := (high_gaussian_left_reflected K hp hn hi he hX).2.2
  have hP : MeasureTheory.Integrable P := (high_left_reflected_components K hp hn hi he hX).2
  have hpoint (t : ℝ) : F t + P t = G t := by
    have hw : (1 : ℝ) < (w t).re := by
      simp only [w, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
      norm_num only
    have harg : l t + 1 / 2 = 1 - w t := by
      dsimp only [l, w]
      norm_num only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_one,
        Complex.ofReal_ofNat]
      ring
    dsimp only [F, P, G, γ]
    rw [harg, AnalyticNumberTheory.RiemannXi.logDeriv_one_sub,
      AnalyticNumberTheory.RiemannXi.logDeriv_eq_poles_gamma_zeta_of_re_gt_one hw]
    ring
  have hsum : (∫ t : ℝ, F t) + ∫ t : ℝ, P t = ∫ t : ℝ, G t := by
    rw [← MeasureTheory.integral_add hF hP]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint)
  have h := congrArg (fun z : ℂ ↦ (d * z).re) hsum
  simp only [mul_add, Complex.add_re] at h
  change
    (d * (∫ t : ℝ, F t)).re + (d * (∫ t : ℝ, logDeriv γ (r t + 1 / 2) * W (r t))).re +
        (d * (∫ t : ℝ, P t)).re =
      _ + (d * (∫ t : ℝ, G t)).re
  linarith only [h]

/-- Reassemble the exact even-character contour formula from the conductor,
ordinary Euler reflection, and common principal contribution. -/
theorem high_contour_components_re (K : HighGaussianKernel) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hn : χ ≠ 1) (hi : χ⁻¹ = χ) (he : χ.Even)
    {X : ℝ} (hX : 0 < X) :
    (highGaussianContourTerms K χ X).re =
      highConductorTerm K q X - highReflectedEuler K χ X + highCommonContour K X := by
  have h :=
    congrArg (fun z : ℂ ↦ ((((1 / (2 * Real.pi) : ℝ) : ℂ) * z)).re)
      (high_left_reflected_components K hp hn hi he hX).1
  rw [high_gaussian_contours_square]
  simp only [highConductorTerm, highReflectedEuler, highCommonContour,
    high_gaussian_even_gamma χ he, mul_add, mul_sub, Complex.add_re, Complex.sub_re] at h ⊢
  linarith only [h]

/-- The three even Jacobi pair contours combine with a single common
principal term and the sum of the three ordinary reflected Euler terms. -/
theorem high_pair_contours_re (K : HighGaussianKernel) {n p q r : ℕ} [NeZero p] [NeZero q]
    [NeZero r] [NeZero n] [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)]
    [Fact (2 < r)] (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n) (hprod : n = p * q * r)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) {X : ℝ} (hX : 1 ≤ X)
    (hpass : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
    let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
    let z := 5 + Real.log X
    (highGaussianContourTerms K a X).re + (highGaussianContourTerms K b X).re +
        (highGaussianContourTerms K c X).re =
      2 * Real.log n * Real.exp (-(K.pole : ℝ) * z) * K.realProfile.eval z -
          (highReflectedEuler K a X + highReflectedEuler K b X + highReflectedEuler K c X) +
        3 * highCommonContour K X := by
  intro a b c z
  obtain ⟨_, _, _, ha, hb, hc, _⟩ := pair_data_of_uniform_pass hn ho hu hprod hp hq hr X hpass
  have ea := high_contour_components_re K ha.1 ha.2.1 ha.2.2.1 ha.2.2.2 (zero_lt_one.trans_le hX)
  have eb := high_contour_components_re K hb.1 hb.2.1 hb.2.2.1 hb.2.2.2 (zero_lt_one.trans_le hX)
  have ec := high_contour_components_re K hc.1 hc.2.1 hc.2.2.1 hc.2.2.2 (zero_lt_one.trans_le hX)
  have hC :=
    high_conductor_pair_sum K (Nat.pos_of_ne_zero (NeZero.ne p)) (Nat.pos_of_ne_zero (NeZero.ne q))
      (Nat.pos_of_ne_zero (NeZero.ne r)) hprod hX
  dsimp only [a, b, c, z]
  linarith only [ea, eb, ec, hC]

/-- Absolute convergence at real part 17/16 permits termwise integration
of the reflected Euler series against the high Gaussian left weight. -/
theorem high_gaussian_reflected_exchange (K : HighGaussianKernel) {q : ℕ}
    (χ : DirichletCharacter ℂ q) {X : ℝ} (hX : 0 < X) :
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let r := fun t : ℝ ↦ ((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)
    let W := fun t ↦ highGaussianSquare K (l t) * (X : ℂ) ^ l t
    let a := (fun n : ℕ ↦ χ n) * (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ))
    (∫ t : ℝ, LSeries a (r t) * W t) = ∑' n : ℕ, ∫ t : ℝ, LSeries.term a (r t) n * W t := by
  intro l r W a
  have hs :=
    χ.LSeriesSummable_twist_vonMangoldt
      (show 1 < (((17 / 16 : ℝ) : ℂ)).re by norm_num only [Complex.ofReal_re])
  exact
    AnalyticNumberTheory.General.integral_LSeries_mul_weight_eq_tsum hs (fun t : ℝ ↦ -t) W
      continuous_neg (high_square_left_integrable K hX)

/-- A positive-index reflected Euler term has inverse Mellin scale
equal to the reciprocal of the product of its index and the cutoff. -/
theorem high_gaussian_reflected_term (K : HighGaussianKernel) (a : ℕ → ℂ) {X : ℝ} (hX : 0 < X)
    {n : ℕ} (hn : n ≠ 0) :
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let r := fun t : ℝ ↦ ((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ, LSeries.term a (r t) n * (highGaussianSquare K (l t) * (X : ℂ) ^ l t)) =
      (a n / (n : ℂ) ^ (1 / 2 : ℂ)) *
        Analysis.inverseMellin (highGaussianSquare K) (-9 / 16) ((n : ℝ) * X)⁻¹ := by
  intro l r
  unfold Analysis.inverseMellin
  rw [mul_left_comm (a n / (n : ℂ) ^ (1 / 2 : ℂ))]
  congr 1
  rw [← MeasureTheory.integral_const_mul (a n / (n : ℂ) ^ (1 / 2 : ℂ))]
  apply MeasureTheory.integral_congr_ae
  exact
    Filter.Eventually.of_forall
      (fun t ↦ by
        have hr : r t = 1 / 2 - l t := by
          dsimp only [r, l]
          norm_num only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_one,
            Complex.ofReal_ofNat]
          ring
        have hnX : 0 < (n : ℝ) * X := mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) hX
        change
          LSeries.term a (r t) n * (highGaussianSquare K (l t) * (X : ℂ) ^ l t) =
            (a n / (n : ℂ) ^ (1 / 2 : ℂ)) *
              (highGaussianSquare K (l t) * ((((n : ℝ) * X)⁻¹ : ℝ) : ℂ) ^ (-(l t)))
        rw [LSeries.term_of_ne_zero hn, hr, Complex.cpow_sub _ _ (Nat.cast_ne_zero.mpr hn)]
        rw [Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg hnX.le, Complex.cpow_neg, inv_inv,
          Complex.ofReal_mul, Complex.ofReal_mul_cpow (Nat.cast_nonneg n) (X : ℂ),
          Complex.ofReal_natCast, div_div_eq_mul_div]
        ring)

/-- The reflected Euler contribution is a Mangoldt series evaluated at
reciprocal scales inside the physical support of the high kernel. -/
theorem high_gaussian_reflected_euler_at_cutoff (K : HighGaussianKernel) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {X : ℝ} (hX : 1 ≤ X) :
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let r := fun t : ℝ ↦ ((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ, -logDeriv χ.LFunction (r t) * (highGaussianSquare K (l t) * (X : ℂ) ^ l t)) =
      ∑' n : ℕ,
        let u := ((n : ℝ) * X)⁻¹
        (χ n * (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ (1 / 2 : ℂ)) *
          ((((u * Real.exp (-5)) ^ (K.pole : ℝ) : ℝ) : ℂ) * K.profilePoly (5 - Real.log u)) := by
  intro l r
  have hp := zero_lt_one.trans_le hX
  simp only [r, LLS.PaperStatements.gamma_reflected_ordinary_eq_euler]
  rw [high_gaussian_reflected_exchange K χ hp, ← tsum_mul_left]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [LSeries.term_zero, zero_mul, MeasureTheory.integral_zero, mul_zero,
      ArithmeticFunction.map_zero, Complex.ofReal_zero, zero_div]
  · have hn₁ : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hn)
    have hnx : 1 ≤ (n : ℝ) * X := one_le_mul_of_one_le_of_one_le hn₁ hX
    have hu : ((n : ℝ) * X)⁻¹ ≤ Real.exp 5 :=
      (inv_le_one_of_one_le₀ hnx).trans (Real.one_le_exp (by norm_num only))
    rw [high_gaussian_reflected_term K _ hp hn,
      high_gaussian_square_inverse K (inv_pos.mpr (zero_lt_one.trans_le hnx)) hu]
    rfl

/-- Rewrite the reflected Euler summand in the log coordinate of H29.
The profile already includes the Gram normalization. -/
theorem high_gaussian_reflected_weight (K : HighGaussianKernel) {q : ℕ} (χ : DirichletCharacter ℂ q)
    {X : ℝ} (hX : 0 < X) (n : ℕ) :
    let u := ((n : ℝ) * X)⁻¹
    (χ n * (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ (1 / 2 : ℂ)) *
        ((((u * Real.exp (-5)) ^ (K.pole : ℝ) : ℝ) : ℂ) * K.profilePoly (5 - Real.log u)) =
      χ n *
        ((ArithmeticFunction.vonMangoldt n * Real.exp (-(K.pole : ℝ) * (5 + Real.log X)) *
              (n : ℝ) ^ (-(K.pole : ℝ) - 1 / 2) *
              K.realProfile.eval (5 + Real.log X + Real.log n) :
            ℝ) :
          ℂ) := by
  intro u
  by_cases hn : n = 0
  · subst n
    simp only [ArithmeticFunction.map_zero, Complex.ofReal_zero, mul_zero, zero_div, zero_mul]
  have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hu : 0 < u := inv_pos.mpr (mul_pos hn₀ hX)
  have hz : 5 - Real.log u = 5 + Real.log X + Real.log n := by
    dsimp only [u]
    rw [Real.log_inv, Real.log_mul hn₀.ne' hX.ne']
    ring
  have he :
    (u * Real.exp (-5)) ^ (K.pole : ℝ) =
      Real.exp (-(K.pole : ℝ) * (5 + Real.log X)) * (n : ℝ) ^ (-(K.pole : ℝ)) := by
    rw [Real.rpow_def_of_pos (mul_pos hu (Real.exp_pos _)),
      Real.log_mul hu.ne' (Real.exp_pos _).ne', Real.log_exp, Real.rpow_def_of_pos hn₀, ←
      Real.exp_add]
    congr 1
    linarith only [congrArg (fun z : ℝ ↦ z * (K.pole : ℝ)) hz]
  have hs : (((n : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) = (n : ℂ) ^ (1 / 2 : ℂ) := by
    simpa only [Complex.ofReal_natCast, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat] using Complex.ofReal_cpow hn₀.le (1 / 2)
  rw [he, hz, ← high_real_profile_eval, Real.rpow_sub hn₀, ← hs]
  simp only [Complex.ofReal_mul, Complex.ofReal_div]
  ring

/-- The reflected integral equals the polynomially weighted Euler sum
used in H29, with the cutoff dependence factored out. -/
theorem high_gaussian_reflected_log_series (K : HighGaussianKernel) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {X : ℝ} (hX : 1 ≤ X) :
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let r := fun t : ℝ ↦ ((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ, -logDeriv χ.LFunction (r t) * (highGaussianSquare K (l t) * (X : ℂ) ^ l t)) =
      ((Real.exp (-(K.pole : ℝ) * (5 + Real.log X))) : ℂ) *
        ∑' n : ℕ,
          χ n *
            ((ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(K.pole : ℝ) - 1 / 2) *
                  K.realProfile.eval (5 + Real.log X + Real.log n) :
                ℝ) :
              ℂ) := by
  intro l r
  rw [high_gaussian_reflected_euler_at_cutoff K χ hX, ← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [high_gaussian_reflected_weight K χ (zero_lt_one.trans_le hX) n]
  simp only [Complex.ofReal_mul]
  ring

/-- Bound the real part of the normalized reflected integral for one character
by the H29 polynomial envelope at the high Gaussian cutoff. -/
theorem high_gaussian_reflected_bound (K : HighGaussianKernel) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {X : ℝ} (hX : 1 ≤ X) :
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let r := fun t : ℝ ↦ ((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)
    let z := 5 + Real.log X
    let σ := (K.pole : ℝ) + 1 / 2
    |(((1 / (2 * Real.pi) : ℝ) : ℂ) *
            (∫ t : ℝ,
              -logDeriv χ.LFunction (r t) * (highGaussianSquare K (l t) * (X : ℂ) ^ l t))).re| ≤
      Real.exp (-(K.pole : ℝ) * z) *
        ∫ t in Set.Ioi (1 : ℝ),
          6 * t ^ (-σ) *
            (σ * |K.realProfile.eval (z + Real.log t)| +
              |K.realProfile.derivative.eval (z + Real.log t)|) := by
  intro l r z σ
  have hσ : 1 < σ := by
    dsimp only [σ]
    linarith only [high_gaussian_pole_gt K]
  rw [high_gaussian_reflected_log_series K χ hX]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, abs_mul,
    abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  rw [show -(K.pole : ℝ) - 1 / 2 = -σ by
      dsimp only [σ]; ring]
  simpa only [mul_assoc] using
    reflected_complex_abel_bound (fun n : ℕ ↦ χ n)
      (fun n ↦ (χ.norm_le_one n).trans (by norm_num only)) K.realProfile hσ z

/-- The three reflected Euler integrals use a single H29 envelope. The
combined coefficient has norm at most three at each prime power. -/
theorem high_gaussian_reflected_triple (K : HighGaussianKernel) {q₁ q₂ q₃ : ℕ} [NeZero q₁]
    [NeZero q₂] [NeZero q₃] (a : DirichletCharacter ℂ q₁) (b : DirichletCharacter ℂ q₂)
    (c : DirichletCharacter ℂ q₃) {X : ℝ} (hX : 1 ≤ X) :
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let r := fun t : ℝ ↦ ((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)
    let J := fun F : ℂ → ℂ ↦
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ, -logDeriv F (r t) * (highGaussianSquare K (l t) * (X : ℂ) ^ l t))
    let z := 5 + Real.log X
    let σ := (K.pole : ℝ) + 1 / 2
    |(J a.LFunction + J b.LFunction + J c.LFunction).re| ≤
      Real.exp (-(K.pole : ℝ) * z) *
        ∫ v in Set.Ioi (0 : ℝ),
          6 * Real.exp (-(σ - 1) * v) *
            (σ * |K.realProfile.eval (z + v)| + |K.realProfile.derivative.eval (z + v)|) := by
  intro l r J z σ
  rw [← reflected_abel_log_coordinate]
  have hσ : 1 < σ := by
    dsimp only [σ]
    linarith only [high_gaussian_pole_gt K]
  have hs (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) :=
    summable_reflected_complex f (fun n ↦ (hf n).trans (by norm_num only)) K.realProfile hσ z
  have ha := hs (fun n ↦ a n) (fun n ↦ a.norm_le_one n)
  have hb := hs (fun n ↦ b n) (fun n ↦ b.norm_le_one n)
  have hc := hs (fun n ↦ c n) (fun n ↦ c.norm_le_one n)
  have habc (n : ℕ) : ‖a n + b n + c n‖ ≤ 3 := by
    linarith only [norm_add_le (a n + b n) (c n), norm_add_le (a n) (b n), a.norm_le_one n,
      b.norm_le_one n, c.norm_le_one n]
  have he : -(K.pole : ℝ) - 1 / 2 = -σ := by
    dsimp only [σ]
    ring
  dsimp only [J]
  rw [high_gaussian_reflected_log_series K a hX, high_gaussian_reflected_log_series K b hX,
    high_gaussian_reflected_log_series K c hX, ← mul_add, ← mul_add, he]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, abs_mul,
    abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  simp only [mul_assoc]
  rw [← Summable.tsum_add ha hb, ← Summable.tsum_add (ha.add hb) hc]
  simpa only [add_mul, Pi.add_apply, mul_assoc] using
    reflected_complex_abel_bound (fun n ↦ a n + b n + c n) habc K.realProfile hσ z

/-- Both high Gaussian profiles have the H28 bound in the translated H29
coordinate. The terminal coefficient sign is supplied by the kernel certificate. -/
theorem high_gaussian_shifted_moment (K : HighGaussianKernel) (j : ℕ) {z : ℝ}
    (hz : (profileCorrectionStart K : ℝ) ≤ z) :
    let P := (Polynomial.derivative^[j]) K.realProfile
    let Q := P.comp (Polynomial.X + Polynomial.C z)
    let s := (K.pole : ℝ) - 1 / 2
    (∫ v in Set.Ioi (0 : ℝ), Real.exp (-s * v) * |P.eval (z + v)|) ≤
      (∑ k ∈ Finset.range (Q.natDegree + 1), Q.coeff k * ((k.factorial : ℝ) / s ^ (k + 1))) +
        2 * Real.exp (s * z) * highNegativeMoment K j := by
  exact high_shifted_moment_le K (high_correction_profile_check K) j hz

/-- The exact signed Laplace moment of the indicated derivative, in the
coordinate translated to the logarithm of the cutoff. -/
noncomputable def highSignedMoment (K : HighGaussianKernel) (j : ℕ) (z : ℝ) : ℝ :=
  let Q := ((Polynomial.derivative^[j]) K.realProfile).comp (Polynomial.X + Polynomial.C z)
  let s := (K.pole : ℝ) - 1 / 2
  ∑ k ∈ Finset.range (Q.natDegree + 1), Q.coeff k * ((k.factorial : ℝ) / s ^ (k + 1))

/-- The upper bound on a translated absolute moment. It adds the signed
polynomial moment and the H28 charge for the same derivative. -/
noncomputable def highMomentUpper (K : HighGaussianKernel) (j : ℕ) (z : ℝ) : ℝ :=
  let s := (K.pole : ℝ) - 1 / 2
  highSignedMoment K j z + 2 * Real.exp (s * z) * highNegativeMoment K j

/-- The integrated H29 envelope is bounded by the two certified H28
moment bounds, with weights σ and one. -/
theorem high_reflected_envelope_le (K : HighGaussianKernel) {z : ℝ}
    (hz : (profileCorrectionStart K : ℝ) ≤ z) :
    let s := (K.pole : ℝ) - 1 / 2
    let σ := (K.pole : ℝ) + 1 / 2
    (∫ v in Set.Ioi (0 : ℝ),
        6 * Real.exp (-s * v) *
          (σ * |K.realProfile.eval (z + v)| + |K.realProfile.derivative.eval (z + v)|)) ≤
      6 * (σ * highMomentUpper K 0 z + highMomentUpper K 1 z) := by
  intro s σ
  let W := fun v : ℝ ↦ Real.exp (-s * v)
  let f := fun v : ℝ ↦ W v * |K.realProfile.eval (z + v)|
  let g := fun v : ℝ ↦ W v * |K.realProfile.derivative.eval (z + v)|
  have hs : 0 < s := sub_pos.mpr (high_gaussian_pole_gt K)
  have hσ : 0 ≤ σ := by
    dsimp only [σ]
    linarith only [high_gaussian_pole_gt K]
  have hf : MeasureTheory.IntegrableOn f (Set.Ioi 0) :=
    integrable_shifted_abs_moment K.realProfile z hs
  have hg : MeasureTheory.IntegrableOn g (Set.Ioi 0) :=
    integrable_shifted_abs_moment K.realProfile.derivative z hs
  have he (v : ℝ) :
    6 * W v * (σ * |K.realProfile.eval (z + v)| + |K.realProfile.derivative.eval (z + v)|) =
      6 * (σ * f v + g v) := by
    dsimp only [f, g]
    ring
  change
    (∫ v in Set.Ioi (0 : ℝ),
        6 * W v * (σ * |K.realProfile.eval (z + v)| + |K.realProfile.derivative.eval (z + v)|)) ≤
      _
  simp only [he, MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_add (hf.const_mul σ) hg, MeasureTheory.integral_const_mul]
  apply mul_le_mul_of_nonneg_left _ (by norm_num only)
  exact
    add_le_add (mul_le_mul_of_nonneg_left (high_gaussian_shifted_moment K 0 hz) hσ)
      (high_gaussian_shifted_moment K 1 hz)

/-- Separate the H29 signed moments from the negative-profile correction.
The correction has exponential rate one half in the translated cutoff. -/
private theorem high_reflected_bound_split (K : HighGaussianKernel) (z : ℝ) :
    let a := (K.pole : ℝ)
    let σ := a + 1 / 2
    Real.exp (-a * z) * (6 * (σ * highMomentUpper K 0 z + highMomentUpper K 1 z)) =
      6 * Real.exp (-a * z) * (σ * highSignedMoment K 0 z + highSignedMoment K 1 z) +
        12 * Real.exp (-z / 2) * (σ * highNegativeMoment K 0 + highNegativeMoment K 1) := by
  intro a σ
  have he : Real.exp (-a * z) * Real.exp ((a - 1 / 2) * z) = Real.exp (-z / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  dsimp only [highMomentUpper]
  change
    _ =
      6 * Real.exp (-a * z) * (σ * highSignedMoment K 0 z + highSignedMoment K 1 z) +
        12 * Real.exp (-z / 2) * (σ * highNegativeMoment K 0 + highNegativeMoment K 1)
  rw [← he]
  ring

/-- H29 for the three reflected character terms, with the H30 reflection
correction separated from the signed polynomial moments. -/
theorem high_reflected_triple_le_moments (K : HighGaussianKernel) {q₁ q₂ q₃ : ℕ} [NeZero q₁]
    [NeZero q₂] [NeZero q₃] (a : DirichletCharacter ℂ q₁) (b : DirichletCharacter ℂ q₂)
    (c : DirichletCharacter ℂ q₃) {X : ℝ} (hX : 1 ≤ X)
    (hz : (profileCorrectionStart K : ℝ) ≤ 5 + Real.log X) :
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let r := fun t : ℝ ↦ ((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)
    let J := fun F : ℂ → ℂ ↦
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ, -logDeriv F (r t) * (highGaussianSquare K (l t) * (X : ℂ) ^ l t))
    let z := 5 + Real.log X
    let σ := (K.pole : ℝ) + 1 / 2
    |(J a.LFunction + J b.LFunction + J c.LFunction).re| ≤
      6 * Real.exp (-(K.pole : ℝ) * z) * (σ * highSignedMoment K 0 z + highSignedMoment K 1 z) +
        12 * Real.exp (-z / 2) * (σ * highNegativeMoment K 0 + highNegativeMoment K 1) := by
  intro l r J z σ
  rw [← high_reflected_bound_split]
  have he : (K.pole : ℝ) + 1 / 2 - 1 = (K.pole : ℝ) - 1 / 2 := by ring
  have habc := high_gaussian_reflected_triple K a b c hX
  refine habc.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _))
  simpa only [he] using high_reflected_envelope_le K hz

/-- The explicit upper bound on the cost of the three reflected Euler terms. -/
noncomputable def highReflectedBudget (K : HighGaussianKernel) (z : ℝ) : ℝ :=
  let a := (K.pole : ℝ)
  let σ := a + 1 / 2
  6 * Real.exp (-a * z) * (σ * highSignedMoment K 0 z + highSignedMoment K 1 z) +
    12 * Real.exp (-z / 2) * (σ * highNegativeMoment K 0 + highNegativeMoment K 1)

/-- The negative of the real Euler sum is bounded by the H29 budget. -/
theorem high_reflected_real_sum_le (K : HighGaussianKernel) {q₁ q₂ q₃ : ℕ} [NeZero q₁] [NeZero q₂]
    [NeZero q₃] (a : DirichletCharacter ℂ q₁) (b : DirichletCharacter ℂ q₂)
    (c : DirichletCharacter ℂ q₃) {X : ℝ} (hX : 1 ≤ X)
    (hz : (profileCorrectionStart K : ℝ) ≤ 5 + Real.log X) :
    -(highReflectedEuler K a X + highReflectedEuler K b X + highReflectedEuler K c X) ≤
      highReflectedBudget K (5 + Real.log X) := by
  have h := high_reflected_triple_le_moments K a b c hX hz
  dsimp only at h
  refine (neg_le_abs _).trans ?_
  simpa only [highReflectedEuler, highReflectedBudget, Complex.add_re, Complex.ofReal_neg, mul_neg,
    sub_eq_add_neg] using h

/-- Under passage through the cutoff, the compensated arithmetic lower
bound controls the zero score with explicit conductor and reflection costs.
The common principal contour remains as one term. -/
theorem gaussian_high_zero_score_costs
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (K : HighGaussianKernel)
    {n p q r : ℕ} [NeZero p] [NeZero q] [NeZero r] [NeZero n] [Fact p.Prime] [Fact q.Prime]
    [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)] (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hprod : n = p * q * r) (hp : Odd p) (hq : Odd q) (hr : Odd r)
    {X : ℝ} (hX : 1000000 ≤ X) (hz : (profileCorrectionStart K : ℝ) ≤ 5 + Real.log X)
    (hpass : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    let z := 5 + Real.log X
    let v := fun m : ℕ ↦ 5 - Real.log ((m : ℝ) / X)
    let B := fun m : ℕ ↦
      ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-(1 / 2) : ℝ) * Real.exp (-(K.pole : ℝ) * v m) *
        K.realProfile.eval (v m)
    4 * (∑ m ∈ Finset.Ioc 0 ⌊X⌋₊, B m) - (∑ m ∈ Finset.Ioc 0 ⌊X * Real.exp 5⌋₊, B m) -
        4 * highCompensationBound K X ≤
      gaussianPairZeroScore K X hp hq hr +
        2 * Real.log n * Real.exp (-(K.pole : ℝ) * z) * K.realProfile.eval z +
        highReflectedBudget K z +
        3 * highCommonContour K X := by
  intro z v B
  have h₁ := (by norm_num only : (1 : ℝ) ≤ 1000000).trans hX
  have ha := gaussian_high_zero_score_lower hGRH K hn ho hu hprod hp hq hr hX hpass
  have hc := high_pair_contours_re K hn ho hu hprod hp hq hr h₁ hpass
  have he :=
    high_reflected_real_sum_le K (NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq))
      (NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr))
      (NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)) h₁ hz
  dsimp only at ha hc
  dsimp only [z, v, B]
  linarith only [ha, hc, he]

/-- Apply the H28 derivative moment bounds to the lower H27 remainder
integral for both high kernels. -/
theorem high_h27_lower_moment_le (K : HighGaussianKernel) {z : ℝ}
    (hz : (profileCorrectionStart K : ℝ) ≤ z) :
    let d := (K.pole : ℝ) - 1 / 2
    let B := K.realProfile
    let D :=
      Polynomial.C (d ^ 2) * B - Polynomial.C (2 * d) * B.derivative + B.derivative.derivative
    (∫ v in Set.Ioi (0 : ℝ), Real.exp (-d * v) * |D.eval (z + v)|) ≤
      d ^ 2 * highMomentUpper K 0 z + 2 * d * highMomentUpper K 1 z + highMomentUpper K 2 z := by
  intro d B D
  have hd : 0 ≤ d := sub_nonneg.mpr (high_gaussian_pole_gt K).le
  refine (high_remainder_moment_triangle K z).trans ?_
  exact
    add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left (high_gaussian_shifted_moment K 0 hz) (sq_nonneg d))
        (mul_le_mul_of_nonneg_left (high_gaussian_shifted_moment K 1 hz)
          (mul_nonneg zero_le_two hd)))
      (high_gaussian_shifted_moment K 2 hz)

/-- The lower H27 charge separates into signed polynomial moments and
the principal contribution to the exponentially decaying H30 correction. -/
theorem high_h27_lower_charge_le (K : HighGaussianKernel) {z : ℝ}
    (hz : (profileCorrectionStart K : ℝ) ≤ z) :
    let a := (K.pole : ℝ)
    let d := a - 1 / 2
    let B := K.realProfile
    let D :=
      Polynomial.C (d ^ 2) * B - Polynomial.C (2 * d) * B.derivative + B.derivative.derivative
    (51 / 10 : ℝ) * Real.exp (-a * z) *
        (∫ v in Set.Ioi (0 : ℝ), Real.exp (-d * v) * |D.eval (z + v)|) ≤
      (51 / 10 : ℝ) * Real.exp (-a * z) *
          (d ^ 2 * highSignedMoment K 0 z + 2 * d * highSignedMoment K 1 z +
            highSignedMoment K 2 z) +
        (51 / 5 : ℝ) * Real.exp (-z / 2) *
          (d ^ 2 * highNegativeMoment K 0 + 2 * d * highNegativeMoment K 1 +
            highNegativeMoment K 2) := by
  intro a d B D
  have h :=
    mul_le_mul_of_nonneg_left (high_h27_lower_moment_le K hz)
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 51 / 10) (Real.exp_nonneg (-a * z)))
  refine h.trans_eq ?_
  have he : Real.exp (-z / 2) = Real.exp (-a * z) * Real.exp (d * z) := by
    rw [← Real.exp_add]
    congr 1
    dsimp only [d]
    ring
  rw [he]
  dsimp only [highMomentUpper, d, a]
  ring

/-- Combined H30 coefficient for the lower principal remainder and the
three reflected characters. The physical profile includes the Gram scale. -/
noncomputable def highH30Charge (K : HighGaussianKernel) : ℝ :=
  let d := (K.pole : ℝ) - 1 / 2
  let σ := (K.pole : ℝ) + 1 / 2
  let J := fun j ↦ highNegativeMoment K j
  51 / 5 * (d ^ 2 * J 0 + 2 * d * J 1 + J 2) + 12 * (σ * J 0 + J 1)

/-- The lower H27 and reflected H29 charges share one H30 correction
after the signed Laplace moments have been extracted. -/
theorem high_principal_reflected_charge_le (K : HighGaussianKernel) {q₁ q₂ q₃ : ℕ} [NeZero q₁]
    [NeZero q₂] [NeZero q₃] (a : DirichletCharacter ℂ q₁) (b : DirichletCharacter ℂ q₂)
    (c : DirichletCharacter ℂ q₃) {X : ℝ} (hX : 1 ≤ X)
    (hz : (profileCorrectionStart K : ℝ) ≤ 5 + Real.log X) :
    let z := 5 + Real.log X
    let d := (K.pole : ℝ) - 1 / 2
    let σ := (K.pole : ℝ) + 1 / 2
    let B := K.realProfile
    let D :=
      Polynomial.C (d ^ 2) * B - Polynomial.C (2 * d) * B.derivative + B.derivative.derivative
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let r := fun t : ℝ ↦ ((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)
    let J := fun F : ℂ → ℂ ↦
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ, -logDeriv F (r t) * (highGaussianSquare K (l t) * (X : ℂ) ^ l t))
    let M := fun j ↦ highSignedMoment K j z
    (51 / 10 : ℝ) * Real.exp (-(K.pole : ℝ) * z) *
          (∫ v in Set.Ioi (0 : ℝ), Real.exp (-d * v) * |D.eval (z + v)|) +
        |(J a.LFunction + J b.LFunction + J c.LFunction).re| ≤
      Real.exp (-(K.pole : ℝ) * z) *
          (51 / 10 * (d ^ 2 * M 0 + 2 * d * M 1 + M 2) + 6 * (σ * M 0 + M 1)) +
        Real.exp (-z / 2) * highH30Charge K := by
  intro z d σ B D l r J M
  refine
    (add_le_add (high_h27_lower_charge_le K hz)
          (high_reflected_triple_le_moments K a b c hX hz)).trans_eq
      ?_
  dsimp only [highH30Charge, M, d, σ, z]
  ring

/-- Upper bounds on the three negative moments bound the common H30
coefficient independently of the partition used for each moment. -/
theorem high_h30_charge_le (K : HighGaussianKernel) {m₀ m₁ m₂ : ℝ}
    (h₀ : highNegativeMoment K 0 ≤ m₀) (h₁ : highNegativeMoment K 1 ≤ m₁)
    (h₂ : highNegativeMoment K 2 ≤ m₂) :
    let d := (K.pole : ℝ) - 1 / 2
    let σ := (K.pole : ℝ) + 1 / 2
    highH30Charge K ≤ 51 / 5 * (d ^ 2 * m₀ + 2 * d * m₁ + m₂) + 12 * (σ * m₀ + m₁) := by
  intro d σ
  have hd : 0 ≤ d := sub_nonneg.mpr (high_gaussian_pole_gt K).le
  have hσ : 0 ≤ σ := by
    dsimp only [σ]
    linarith only [high_gaussian_pole_gt K]
  have hp :=
    add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left h₀ (sq_nonneg d))
        (mul_le_mul_of_nonneg_left h₁ (mul_nonneg zero_le_two hd)))
      h₂
  have hr := add_le_add (mul_le_mul_of_nonneg_left h₀ hσ) h₁
  exact
    add_le_add (mul_le_mul_of_nonneg_left hp (by norm_num only : (0 : ℝ) ≤ 51 / 5))
      (mul_le_mul_of_nonneg_left hr (by norm_num only : (0 : ℝ) ≤ 12))

/-- The original quarter-width sums are one source of numerical H30 bounds. -/
theorem high_h30_charge_le_of_ticks (K : HighGaussianKernel) (m₀ m₁ m₂ : ℤ)
    (h₀ : highNegativeChargeTicks K 0 ≤ m₀) (h₁ : highNegativeChargeTicks K 1 ≤ m₁)
    (h₂ : highNegativeChargeTicks K 2 ≤ m₂) :
    let d := (K.pole : ℝ) - 1 / 2
    let σ := (K.pole : ℝ) + 1 / 2
    highH30Charge K ≤ (51 / 5 * (d ^ 2 * m₀ + 2 * d * m₁ + m₂) + 12 * (σ * m₀ + m₁)) / 10 ^ 6 := by
  intro d σ
  refine
    (high_h30_charge_le K (high_negative_moment_le_of_ticks K h₀)
          (high_negative_moment_le_of_ticks K h₁) (high_negative_moment_le_of_ticks K h₂)).trans_eq
      ?_
  ring

/-- The combined H30 coefficient is nonnegative by nonnegativity of the
three weighted negative moments. -/
theorem high_h30_charge_nonneg (K : HighGaussianKernel) : 0 ≤ highH30Charge K := by
  have hb : (profileCorrectionStart K : ℝ) ≤ (profileCorrectionEnd K : ℝ) := by
    cases K <;>
      norm_num only [profileCorrectionStart, profileCorrectionEnd, Rat.cast_ofNat, Rat.cast_div,
        Int.cast_ofNat]
  have hJ (j : ℕ) : (0 : ℝ) ≤ highNegativeMoment K j :=
    intervalIntegral.integral_nonneg hb
      (fun t _ ↦
        mul_nonneg (Real.exp_nonneg _)
          (le_max_left 0 (-((Polynomial.derivative^[j]) K.realProfile).eval t)))
  have hd := sub_nonneg.mpr (high_gaussian_pole_gt K).le
  have hσ : (0 : ℝ) ≤ (K.pole : ℝ) + 1 / 2 := by linarith only [high_gaussian_pole_gt K]
  dsimp only [highH30Charge]
  exact
    add_nonneg
      (mul_nonneg (by norm_num only)
        (add_nonneg
          (add_nonneg (mul_nonneg (sq_nonneg _) (hJ 0))
            (mul_nonneg (mul_nonneg zero_le_two hd) (hJ 1)))
          (hJ 2)))
      (mul_nonneg (by norm_num only) (add_nonneg (mul_nonneg hσ (hJ 0)) (hJ 1)))

/-- A numerical H30 coefficient bound gives a uniform correction bound
over any cutoff interval starting at z₀. -/
theorem high_h30_charge_on_ray (K : HighGaussianKernel) {z₀ z C : ℝ} (hz : z₀ ≤ z)
    (hC : highH30Charge K ≤ C) : Real.exp (-z / 2) * highH30Charge K ≤ Real.exp (-z₀ / 2) * C := by
  have h :=
    Real.exp_le_exp.mpr
      (div_le_div_of_nonneg_right (neg_le_neg hz) (by norm_num only : (0 : ℝ) ≤ 2))
  exact mul_le_mul h hC (high_h30_charge_nonneg K) (Real.exp_nonneg _)

end PseudoPrime.PrimeTestBounds.MillerRabin
