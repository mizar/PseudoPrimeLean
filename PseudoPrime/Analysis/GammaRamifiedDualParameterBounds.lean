/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaRamifiedFiniteSupport

/-! # Adjustable ramified dual parameters and exact finite support -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The dual parameter theta/sqrt x, with theta greater than one in
the finite-support estimates. This allows a rational parameter to be chosen
for each scale cell while retaining the actual signed prime costs. -/
noncomputable def gammaRamifiedThetaParameter (θ x : ℝ) : ℝ :=
  θ / Real.sqrt x

/-- The real support cutoff for theta greater than one and x at least one.
The first branch excludes second prime powers from the ramp cutoff; the
second pays the reciprocal Euler tail with (theta-1)/sqrt x. -/
noncomputable def gammaRamifiedThetaCutoff (θ x : ℝ) : ℝ :=
  max (Real.sqrt ((99 / 40 : ℝ) * x)) (1 + (79977719 / 25000000 : ℝ) * Real.sqrt x / (θ - 1))

/-- Odd primes not exceeding the adjustable real cutoff. The floor and
prime filter give a finite set. Positive signed dual excess outside this
set vanishes, independently of the input's prime factorization. -/
noncomputable def gammaRamifiedThetaPrimeSet (θ x : ℝ) : Finset ℕ :=
  (Finset.Icc 3 ⌊gammaRamifiedThetaCutoff θ x⌋₊).filter Nat.Prime

/-- For nonnegative theta, the adjustable dual parameter is nonnegative
at every scale. Divide by the nonnegative square root. This supplies the
sign premise of the input-logarithm dual estimate. -/
theorem gamma_ramified_theta_parameter_nonneg {θ : ℝ} (hθ : 0 ≤ θ) (x : ℝ) :
    0 ≤ gammaRamifiedThetaParameter θ x := by exact div_nonneg hθ (Real.sqrt_nonneg x)

/-- At theta=5/4 the adjustable parameter equals the existing parameter.
Normalize the rational quotient. Existing parameter APIs remain available. -/
theorem gamma_ramified_theta_parameter_five_fourths (x : ℝ) :
    gammaRamifiedThetaParameter (5 / 4) x = gammaRamifiedDualParameter x := by
  dsimp only [gammaRamifiedThetaParameter, gammaRamifiedDualParameter]
  ring

/-- For x at least one and theta greater than one, a prime beyond the
adjustable cutoff has combined count allowance below theta/sqrt x.
The two cutoff branches separately control the Euler tail and ramp count.
This gives a strict tail bound without weakening the retained signed terms. -/
theorem gamma_ramified_cost_lt_theta_dual {p : ℕ} (hp : 1 < p) {θ x : ℝ} (hθ : 1 < θ) (hx : 1 ≤ x)
    (hpbig : gammaRamifiedThetaCutoff θ x < p) :
    gammaRamifiedCombinedCost p x < gammaRamifiedThetaParameter θ x := by
  have hx0 := zero_lt_one.trans_le hx
  have ht0 := Real.sqrt_pos.mpr hx0
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hθ0 : 0 < θ - 1 := sub_pos.mpr hθ
  have hsqrt : Real.sqrt ((99 / 40 : ℝ) * x) < p := (le_max_left _ _).trans_lt hpbig
  have hbig : 1 + (79977719 / 25000000 : ℝ) * Real.sqrt x / (θ - 1) < p :=
    (le_max_right _ _).trans_lt hpbig
  have hcut : (99 / 40 : ℝ) * x < (p : ℝ) ^ 2 := by
    have hs :=
      (sq_lt_sq₀ (Real.sqrt_nonneg ((99 / 40 : ℝ) * x)) (zero_lt_one.trans hpR).le).mpr hsqrt
    rw [Real.sq_sqrt (mul_nonneg (by norm_num only) hx0.le)] at hs
    exact hs
  have he := gamma_prime_euler_cost_le_positive_reciprocal hpR
  have hr := gamma_ramp_count_le_one_of_square_above hp hx hcut
  have hlin : (79977719 / 25000000 : ℝ) * Real.sqrt x / (θ - 1) < (p : ℝ) - 1 := by
    linarith only [hbig]
  have hprod := (div_lt_iff₀ hθ0).mp hlin
  have hd : (79977719 / 25000000 : ℝ) / ((p : ℝ) - 1) < (θ - 1) / Real.sqrt x := by
    apply (div_lt_div_iff₀ (sub_pos.mpr hpR) ht0).mpr
    nlinarith only [hprod]
  have hbound := add_lt_add_of_lt_of_le (he.trans_lt hd) (div_le_div_of_nonneg_right hr ht0.le)
  have heq : (θ - 1) / Real.sqrt x + 1 / Real.sqrt x = θ / Real.sqrt x := by ring
  simpa only [gammaRamifiedCombinedCost, gammaRamifiedThetaParameter, heq] using hbound

/-- Beyond the adjustable cutoff the signed positive dual excess is zero.
Bound the signed allowance by the count allowance and use the strict tail
bound. This permits exact finite support in the numerical certificate. -/
theorem gamma_ramified_theta_signed_excess_eq_zero {p : ℕ} (hp : 1 < p) {θ x : ℝ} (hθ : 1 < θ)
    (hx : 1 ≤ x) (hpbig : gammaRamifiedThetaCutoff θ x < p) :
    max (gammaRamifiedSignedCombinedCost p x - gammaRamifiedThetaParameter θ x) 0 = 0 := by
  exact
    max_eq_right
      (sub_nonpos.mpr
        ((gamma_ramified_signed_cost_le_combined hp (zero_lt_one.trans_le hx)).trans
          (gamma_ramified_cost_lt_theta_dual hp hθ hx hpbig).le))

/-- An odd prime outside the adjustable prime set exceeds its real cutoff.
Use floor monotonicity and nonnegativity of the square-root cutoff branch.
This identifies the strict condition needed to remove each tail term. -/
theorem gamma_odd_prime_gt_theta_cutoff_of_not_mem {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (θ x : ℝ)
    (hnot : p ∉ gammaRamifiedThetaPrimeSet θ x) : gammaRamifiedThetaCutoff θ x < p := by
  have hfloor : ⌊gammaRamifiedThetaCutoff θ x⌋₊ < p := by
    apply lt_of_not_ge
    intro hle
    exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp3, hle⟩, hp⟩)
  have hcut0 : 0 ≤ gammaRamifiedThetaCutoff θ x := (Real.sqrt_nonneg _).trans (le_max_left _ _)
  exact (Nat.floor_lt hcut0).mp hfloor

/-- Any finite odd-prime signed excess sum is at most the adjustable
finite prime sum. Terms outside the set vanish and all retained terms
are nonnegative. This is the factor-independent numerical target. -/
theorem gamma_ramified_theta_signed_excess_le_finite (R : Finset ℕ) (hR : ∀ p ∈ R, p.Prime ∧ 3 ≤ p)
    {θ x : ℝ} (hθ : 1 < θ) (hx : 1 ≤ x) :
    (∑ p ∈ R,
        Real.log p *
          max (gammaRamifiedSignedCombinedCost p x - gammaRamifiedThetaParameter θ x) 0) ≤
      ∑ p ∈ gammaRamifiedThetaPrimeSet θ x,
        Real.log p *
          max (gammaRamifiedSignedCombinedCost p x - gammaRamifiedThetaParameter θ x) 0 := by
  apply gamma_supported_sum_le_finite
  · intro p hp hnot
    rw [gamma_ramified_theta_signed_excess_eq_zero (hR p hp).1.one_lt hθ hx
        (gamma_odd_prime_gt_theta_cutoff_of_not_mem (hR p hp).1 (hR p hp).2 θ x hnot),
      mul_zero]
  · intro p hp
    exact
      mul_nonneg (Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_le))
        (le_max_right _ _)

/-- For odd n, actual zero-valued local losses satisfy an adjustable
input-logarithm budget plus the finite signed excess. The arbitrary
positive-power prefix and the full signed ramp remain at the same scale.
This connects the parameterized support to actual character arithmetic. -/
theorem gamma_actual_odd_ramified_signed_cost_le_theta_dual {n f : ℕ} (hn : Odd n) (R : Finset ℕ)
    (hR : R ⊆ n.primeFactors) (χ : DirichletCharacter ℂ f) (hχ : ∀ p ∈ R, χ p = 0)
    (K : ℕ → Finset ℕ) {θ x : ℝ} (hθ : 1 < θ) (hx : 1 ≤ x) :
    (∑ p ∈ R, gammaActualPrimeLocalCost χ p (K p) x) ≤
      gammaRamifiedThetaParameter θ x * Real.log n +
        ∑ p ∈ gammaRamifiedThetaPrimeSet θ x,
          Real.log p *
            max (gammaRamifiedSignedCombinedCost p x - gammaRamifiedThetaParameter θ x) 0 := by
  have hr :=
    gamma_actual_ramified_signed_cost_le_input_dual_cap hn.pos R hR χ hχ K x
      (gamma_ramified_theta_parameter_nonneg (zero_lt_one.trans hθ).le x)
  have hprime (p : ℕ) (hp : p ∈ R) : p.Prime ∧ 3 ≤ p := by
    have h := Nat.prime_of_mem_primeFactors (hR hp)
    have hpne : p ≠ 2 := by
      intro he
      exact hn.not_two_dvd_nat (he ▸ Nat.dvd_of_mem_primeFactors (hR hp))
    exact ⟨h, Nat.succ_le_iff.mpr (lt_of_le_of_ne h.two_le (Ne.symm hpne))⟩
  exact hr.trans (add_le_add le_rfl (gamma_ramified_theta_signed_excess_le_finite R hprime hθ hx))

/-- At theta=5/4 the adjustable cutoff equals the existing real cutoff
at every scale. The square-root branch is dominated by the reciprocal
Euler branch. This preserves the existing finite prime support exactly. -/
theorem gamma_ramified_theta_cutoff_five_fourths (x : ℝ) :
    gammaRamifiedThetaCutoff (5 / 4) x = 1 + (79977719 / 6250000 : ℝ) * Real.sqrt x := by
  have hcoef : Real.sqrt (99 / 40 : ℝ) ≤ 2 := by
    have h := Real.sqrt_le_sqrt (by norm_num only : (99 / 40 : ℝ) ≤ 4)
    norm_num only [Real.sqrt_eq_iff_mul_self_eq_of_pos] at h
    norm_num only [Real.sqrt_eq_iff_mul_self_eq_of_pos]
    exact h
  have hroot := mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg x)
  rw [← Real.sqrt_mul (by norm_num only : (0 : ℝ) ≤ 99 / 40)] at hroot
  have hs : Real.sqrt ((99 / 40 : ℝ) * x) ≤ 1 + (79977719 / 6250000 : ℝ) * Real.sqrt x := by
    nlinarith only [hroot, Real.sqrt_nonneg x]
  dsimp only [gammaRamifiedThetaCutoff]
  rw [show
      1 + (79977719 / 25000000 : ℝ) * Real.sqrt x / (5 / 4 - 1) =
        1 + (79977719 / 6250000 : ℝ) * Real.sqrt x
      by ring]
  exact max_eq_right hs

/-- At theta=5/4 the adjustable finite prime set equals the existing set.
Substitute the exact cutoff identity. Old finite-support certificates
therefore remain valid without a change of prime range. -/
theorem gamma_ramified_theta_prime_set_five_fourths (x : ℝ) :
    gammaRamifiedThetaPrimeSet (5 / 4) x = gammaRamifiedDualPrimeSet x := by
  dsimp only [gammaRamifiedThetaPrimeSet, gammaRamifiedDualPrimeSet]
  rw [gamma_ramified_theta_cutoff_five_fourths]

/-- For a scale cell with sqrt x at most s and theta at least tau greater
than one, the adjustable cutoff is bounded by a single root envelope.
Use monotonicity of the root product and the positive reciprocal denominator.
This permits one certified prime range to cover the entire scale cell. -/
theorem gamma_ramified_theta_cutoff_le_root_envelope {θ τ x s : ℝ} (hτ : 1 < τ) (hθ : τ ≤ θ)
    (hs : Real.sqrt x ≤ s) :
    gammaRamifiedThetaCutoff θ x ≤
      max (Real.sqrt (99 / 40 : ℝ) * s) (1 + (79977719 / 25000000 : ℝ) * s / (τ - 1)) := by
  have hθ0 : 0 < θ - 1 := sub_pos.mpr (hτ.trans_le hθ)
  have hτ0 : 0 < τ - 1 := sub_pos.mpr hτ
  have hs0 : 0 ≤ s := (Real.sqrt_nonneg x).trans hs
  have hn := mul_le_mul_of_nonneg_left hs (by norm_num only : (0 : ℝ) ≤ 79977719 / 25000000)
  have hd :=
    (div_le_div_of_nonneg_right hn hθ0.le).trans
      (div_le_div_of_nonneg_left (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 79977719 / 25000000) hs0)
        hτ0 (sub_le_sub_right hθ 1))
  have hr := mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg (99 / 40 : ℝ))
  rw [← Real.sqrt_mul (by norm_num only : (0 : ℝ) ≤ 99 / 40)] at hr
  exact max_le_max hr (add_le_add le_rfl hd)

/-- Odd primes up to the real bound C, used as a fixed support for a cell.
The cutoff is independent of the varying scale and parameter.
The filtered natural interval supports finite rational certificates. -/
noncomputable def gammaRamifiedCertificatePrimeSet (C : ℝ) : Finset ℕ :=
  (Finset.Icc 3 ⌊C⌋₊).filter Nat.Prime

/-- A real upper bound C on the adjustable cutoff gives inclusion in the
fixed cell prime set. Transfer the natural-floor inequality and preserve
the odd-prime filter. This is the exact finite-support coverage condition. -/
theorem gamma_ramified_theta_prime_set_subset_certificate {θ x C : ℝ}
    (hC : gammaRamifiedThetaCutoff θ x ≤ C) :
    gammaRamifiedThetaPrimeSet θ x ⊆ gammaRamifiedCertificatePrimeSet C := by
  intro p hp
  obtain ⟨hi, hprime⟩ := Finset.mem_filter.mp hp
  obtain ⟨hp3, hpcut⟩ := Finset.mem_Icc.mp hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp3, hpcut.trans (Nat.floor_mono hC)⟩, hprime⟩

/-- With theta greater than one, x at least one and a certified cutoff
upper bound C, every finite odd-prime signed excess is bounded by the
fixed cell prime sum. Extend the already proved finite support using
nonnegative terms. This is the numerical target for a complete scale cell. -/
theorem gamma_ramified_theta_signed_excess_le_certificate (R : Finset ℕ)
    (hR : ∀ p ∈ R, p.Prime ∧ 3 ≤ p) {θ x C : ℝ} (hθ : 1 < θ) (hx : 1 ≤ x)
    (hC : gammaRamifiedThetaCutoff θ x ≤ C) :
    (∑ p ∈ R,
        Real.log p *
          max (gammaRamifiedSignedCombinedCost p x - gammaRamifiedThetaParameter θ x) 0) ≤
      ∑ p ∈ gammaRamifiedCertificatePrimeSet C,
        Real.log p *
          max (gammaRamifiedSignedCombinedCost p x - gammaRamifiedThetaParameter θ x) 0 := by
  apply (gamma_ramified_theta_signed_excess_le_finite R hR hθ hx).trans
  apply Finset.sum_le_sum_of_subset_of_nonneg (gamma_ramified_theta_prime_set_subset_certificate hC)
  intro p hp hnot
  exact
    mul_nonneg (Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_le))
      (le_max_right _ _)

end PseudoPrime.Analysis
