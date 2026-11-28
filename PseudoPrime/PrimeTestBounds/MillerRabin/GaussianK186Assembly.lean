/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186FarWitness
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186FiniteLoss
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianThroughMiddle

import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186ForwardAbel

/-! # Final Gaussian range assembly using the K186 finite comparison -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A four-term positive Taylor sum, raised to power 61, covers the
right endpoint of the finite K186 comparison. -/
private theorem k186_finite_exp_right : (15600000000000 : ℝ) ≤ Real.exp (61 / 2) := by
  have h : (79 / 48 : ℝ) ≤ Real.exp (1 / 2) := by
    have he := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 1 / 2) 4
    norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero,
      Nat.factorial] at he
    linarith only [he]
  have hc : (15600000000000 : ℚ) ≤ (79 / 48 : ℚ) ^ 61 := by decide +kernel
  rw [show (61 / 2 : ℝ) = (61 : ℕ) * (1 / 2 : ℝ) by norm_num only, Real.exp_natCast_mul]
  exact
    (by
          simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using
            (Rat.cast_le (K := ℝ)).mpr hc :
          (15600000000000 : ℝ) ≤ (79 / 48 : ℝ) ^ 61).trans
      (pow_le_pow_left₀ (by norm_num only) h 61)

/-- The finite part between the verified middle and far ranges lies in
the K186 cutoff-log interval from 30 to 61. -/
theorem k186_finite_cutoff_log {L : ℝ} (hL : 7000000 ≤ L) (hU : L ≤ 30000000000000) :
    Real.log ((gaussianK186FarScale * L) ^ 2) ∈ Set.Icc (30 : ℝ) 61 := by
  have hr : 0 < gaussianK186FarScale := by norm_num only [gaussianK186FarScale]
  have hp := mul_pos hr ((by norm_num only : (0 : ℝ) < 7000000).trans_le hL)
  have hu :=
    (mul_le_mul_of_nonneg_left hU hr.le).trans
      (by norm_num only [gaussianK186FarScale] :
        gaussianK186FarScale * 30000000000000 ≤ (15600000000000 : ℝ))
  have hl := Real.log_le_log hp (hu.trans k186_finite_exp_right)
  rw [Real.log_exp] at hl
  refine ⟨(k186_direct_cutoff_domain hL).2, ?_⟩
  rw [Real.log_pow, Nat.cast_ofNat]
  linarith only [hl]

/-- The scalar comparison required on the remaining finite input range.
The cutoff coordinate extends to 61 to overlap the far witness theorem. -/
def K186FiniteComparison : Prop :=
  ∀ L : ℝ,
    7000000 ≤ L →
      Real.log ((gaussianK186FarScale * L) ^ 2) ∈ Set.Icc (30 : ℝ) 61 →
        let X := (gaussianK186FarScale * L) ^ 2
        3 / 8 * L + k186DirectLoss L X < k186ForwardValue X

/-- Middle, finite high, and far witnesses join for uniform triples at the
final Gaussian cutoff. Only the finite scalar comparison is supplied. -/
theorem uniform_gaussian_of_k186_finite (hfinite : K186FiniteComparison) {n : ℕ} (hn : 1 < n)
    (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 663 ≤ Real.log n) :
    HasRejectingPrime n (gaussianWitnessCutoff (Real.log n)) := by
  by_cases hmid : Real.log n ≤ 7000000
  · exact uniform_gaussian_through_middle hn ho hu hGRH ⟨hL, hmid⟩
  by_cases hfar : 30000000000000 ≤ Real.log n
  · exact uniform_gaussian_far hn ho hu hGRH hfar
  have hlo := le_of_lt (lt_of_not_ge hmid)
  exact
    uniform_k186_of_direct_comparison hn ho hu hGRH hlo
      (hfinite (Real.log n) hlo (k186_finite_cutoff_log hlo (le_of_not_ge hfar)))

/-- Combine the uniform ranges with the established low and nonuniform
cases to obtain the Gaussian primality criterion from the finite comparison. -/
theorem gaussian_criterion_of_k186_finite (hfinite : K186FiniteComparison) {n : ℕ} (hn : 1 < n)
    (ho : Odd n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (∀ p : ℕ,
        p.Prime →
          (p : ℝ) ≤ gaussianWitnessCutoff (Real.log n) →
          PrimeTest.StrongMillerRabinPass n (p : ZMod n)) ↔
      n.Prime := by
  exact
    gaussian_criterion_of_uniform_witness hn ho hGRH
      (fun hu hL ↦ uniform_gaussian_of_k186_finite hfinite hn ho hu hGRH hL)

/-- Cutoff monotonicity transfers the assembled Gaussian result to the
quadratic 027007 criterion. -/
theorem criterion_027007_of_k186_finite (hfinite : K186FiniteComparison) {n : ℕ} (hn : 1 < n)
    (ho : Odd n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (∀ p : ℕ,
        p.Prime →
          (p : ℝ) ≤ max 2 ((9090 / 33659 : ℝ) * Real.log n ^ 2) →
          PrimeTest.StrongMillerRabinPass n (p : ZMod n)) ↔
      n.Prime := by
  exact criterion_027007_of_gaussian ho (gaussian_criterion_of_k186_finite hfinite hn ho hGRH)

/-- A lower estimate for the forward sum under RH can be compared
against the finite loss after the common contour has been absorbed. -/
def K186FiniteBudget : Prop :=
  RiemannHypothesis →
    ∀ L : ℝ,
      7000000 ≤ L →
        Real.log ((gaussianK186FarScale * L) ^ 2) ∈ Set.Icc (30 : ℝ) 61 →
          let X := (gaussianK186FarScale * L) ^ 2
          3 / 8 * L + k186FiniteLoss L (Real.log X) < k186ForwardValue X

/-- A scalar comparison with the finite Abel lower budget suffices
for the actual forward Mangoldt sum under RH. -/
theorem k186_finite_budget_of_abel
    (h :
      RiemannHypothesis →
        ∀ x ∈ Set.Icc (30 : ℝ) 61,
          let L := Real.exp (x / 2) / gaussianK186FarScale
          3 / 8 * L + k186FiniteLoss L x < k186FiniteForward x) :
    K186FiniteBudget := by
  intro hRH L hL hx X
  have hρ : 0 < gaussianK186FarScale := by norm_num only [gaussianK186FarScale]
  have hy : 0 < gaussianK186FarScale * L :=
    mul_pos hρ ((by norm_num only : (0 : ℝ) < 7000000).trans_le hL)
  have hX : 0 < X := pow_pos hy 2
  have hback : Real.exp (Real.log X / 2) / gaussianK186FarScale = L := by
    change Real.exp (Real.log ((gaussianK186FarScale * L) ^ 2) / 2) / _ = _
    rw [Real.log_pow, Nat.cast_ofNat,
      show ∀ t : ℝ, 2 * t / 2 = t by
        intro t; ring,
      Real.exp_log hy, mul_div_cancel_left₀ L hρ.ne']
  have hc := h hRH (Real.log X) hx
  dsimp only at hc
  rw [hback] at hc
  obtain ⟨hi, hv⟩ := k186_comp_cert_caps
  have hf :=
    k186_finite_forward_le hRH ((by norm_num only : (20 : ℝ) ≤ 30).trans hx.1)
      (k186_scaled_comp_of_cap (hi.trans (by norm_num only))) (hv.trans (by norm_num only))
  rw [Real.exp_log hX] at hf
  exact hc.trans_le hf

/-- A single certified square moment removes the Abel residual from all
finite scalar comparisons, leaving a constant cost of six fifths. -/
theorem k186_finite_budget_of_square (hm : k186AbelSquare ≤ 11 / 50)
    (h :
      ∀ x ∈ Set.Icc (30 : ℝ) 61,
        let L := Real.exp (x / 2) / gaussianK186FarScale
        3 / 8 * L + k186FiniteLoss L x <
          0.7216056623106 * Real.exp (x / 2) - 301 / 20000 * x ^ 2 - (x + 5) ^ 2 / 6000 -
            k186ForwardEndpoint (x + 5) -
            6 / 5) :
    K186FiniteBudget := by
  apply k186_finite_budget_of_abel
  intro hRH x hx
  have hr := k186_abel_residual_of_square hRH hx.1 hm
  have hc := h x hx
  dsimp only [k186FiniteForward] at ⊢
  linarith only [hr, hc]

/-- A comparison with the finite budget supplies a uniform witness.
The character used to absorb the contour comes from the assumed passing bases. -/
private theorem uniform_k186_of_finite_budget (hfinite : K186FiniteBudget) {n : ℕ} (hn : 1 < n)
    (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 7000000 ≤ Real.log n)
    (hU : Real.log n ≤ 30000000000000) :
    HasRejectingPrime n (gaussianWitnessCutoff (Real.log n)) := by
  let L := Real.log n
  let X := (gaussianK186FarScale * L) ^ 2
  have hd := k186_direct_cutoff_domain hL
  have hX : 0 < X := (by norm_num only : (0 : ℝ) < 1000000).trans_le hd.1
  have hz : (profileCorrectionStart .k186 : ℝ) ≤ 5 + Real.log X := by
    simp only [profileCorrectionStart, Rat.cast_ofNat]
    exact (show (35 : ℝ) = 5 + 30 by norm_num only) ▸ add_le_add_right hd.2 5
  have hc := hfinite hGRH.riemann L hL (k186_finite_cutoff_log hL hU)
  have hw : HasRejectingPrime n X := by
    apply uniform_gaussian_witness_from_factors hn ho hu
    intro p q r _ _ _ _ _ _ _ _ _ _ hprod hp hq hr
    by_contra h
    have hpass (l : ℕ) (hl : l.Prime) (hle : (l : ℝ) ≤ X) :
      PrimeTest.StrongMillerRabinPass n (l : ZMod n) :=
      Classical.byContradiction (fun hf ↦ h ⟨l, hl, hle, hf⟩)
    obtain ⟨_, _, _, hχ, _, _, _⟩ := pair_data_of_uniform_pass hn ho hu hprod hp hq hr X hpass
    have hb := k186_direct_loss_le_finite hχ.1 hχ.2.1 hχ.2.2.1 hχ.2.2.2 L hX hd.2
    have hf := k186_direct_inequality_of_pass hGRH hn ho hu hprod hp hq hr hd.1 hd.2 hz hpass
    exact (not_lt_of_ge (hf.trans (add_le_add_right hb _))) hc
  exact hw.mono (gaussian_k186_far_cutoff ((by norm_num only : (2000000 : ℝ) ≤ 7000000).trans hL))

/-- Join the middle, finite high and far ranges for a uniform triple
using the finite budget as the scalar comparison. -/
theorem uniform_gaussian_of_finite_budget (hfinite : K186FiniteBudget) {n : ℕ} (hn : 1 < n)
    (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 663 ≤ Real.log n) :
    HasRejectingPrime n (gaussianWitnessCutoff (Real.log n)) := by
  by_cases hm : Real.log n ≤ 7000000
  · exact uniform_gaussian_through_middle hn ho hu hGRH ⟨hL, hm⟩
  by_cases hf : 30000000000000 ≤ Real.log n
  · exact uniform_gaussian_far hn ho hu hGRH hf
  exact
    uniform_k186_of_finite_budget hfinite hn ho hu hGRH (le_of_lt (lt_of_not_ge hm))
      (le_of_not_ge hf)

/-- Combine the uniform witness ranges with the established low and
nonuniform cases to obtain the Gaussian criterion from the finite budget. -/
theorem gaussian_criterion_of_finite_budget (hfinite : K186FiniteBudget) {n : ℕ} (hn : 1 < n)
    (ho : Odd n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (∀ p : ℕ,
        p.Prime →
          (p : ℝ) ≤ gaussianWitnessCutoff (Real.log n) →
          PrimeTest.StrongMillerRabinPass n (p : ZMod n)) ↔
      n.Prime := by
  exact
    gaussian_criterion_of_uniform_witness hn ho hGRH
      (fun hu hL ↦ uniform_gaussian_of_finite_budget hfinite hn ho hu hGRH hL)

/-- Transfer the Gaussian criterion from the finite budget to the
quadratic coefficient 9090/33659. -/
theorem criterion_027007_of_finite_budget (hfinite : K186FiniteBudget) {n : ℕ} (hn : 1 < n)
    (ho : Odd n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (∀ p : ℕ,
        p.Prime →
          (p : ℝ) ≤ max 2 ((9090 / 33659 : ℝ) * Real.log n ^ 2) →
          PrimeTest.StrongMillerRabinPass n (p : ZMod n)) ↔
      n.Prime := by
  exact criterion_027007_of_gaussian ho (gaussian_criterion_of_finite_budget hfinite hn ho hGRH)

end PseudoPrime.PrimeTestBounds.MillerRabin
