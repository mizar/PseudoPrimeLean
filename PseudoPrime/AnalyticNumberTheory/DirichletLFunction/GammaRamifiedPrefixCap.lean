/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaPrimeIndexedPrefix
public import PseudoPrime.AnalyticNumberTheory.Gamma.EvenResolventCertificate

/-! # Finite ramified prefix caps retaining nonramified character losses -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- The ramified weight on any finite set is at most its total common weight.
Each nonunit contributes the same nonnegative combined resolvent weight;
units contribute zero. This cap is independent of conductor size and RH. -/
theorem gamma_nonunit_prefix_le_total (q : ℕ) (B : Finset ℕ) :
    (∑ m ∈ B, if Nat.Coprime m q then 0 else Analysis.gammaResolventMangoldtWeight m) ≤
      ∑ m ∈ B, Analysis.gammaResolventMangoldtWeight m := by
  classical
  apply Finset.sum_le_sum
  intro m hm
  by_cases hc : Nat.Coprime m q
  · rw [ite_eq_left hc]
    exact Analysis.gammaResolventMangoldtWeight_nonneg m
  · rw [ite_eq_right hc]

/-- The exact finite prime-power loss at conductor primes is capped by the
whole integer prefix. Use the prime-power bijection before the pointwise cap.
The endpoint convention is m at most floor b, including prime-power endpoints. -/
theorem gamma_ramified_prime_power_prefix_le_total (q : ℕ) {b : ℝ} (hb : 0 ≤ b) :
    (∑ k ∈ Finset.Icc 1 ⌊Real.log b / Real.log 2⌋₊,
        ∑ p ∈ (Finset.Ioc 0 ⌊b ^ (1 / (k : ℝ))⌋₊).filter Nat.Prime,
          if p ∣ q then Analysis.gammaResolventMangoldtWeight (p ^ k) else 0) ≤
      ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m := by
  rw [← gamma_nonunit_prefix_eq_prime_power_sum q hb]
  exact gamma_nonunit_prefix_le_total q (Finset.Ioc 0 ⌊b⌋₊)

/-- Separate the finite character deficit into its exact ramified weight
and its deficit on conductor units. A character is zero at nonunits.
Minus-one values on units remain in the second sum, even after primitivization. -/
theorem gamma_character_prefix_eq_nonunit_add_unit_deficit {q : ℕ} (χ : DirichletCharacter ℂ q)
    (B : Finset ℕ) :
    (∑ m ∈ B, (1 - (χ m).re) * Analysis.gammaResolventMangoldtWeight m) =
      (∑ m ∈ B, if Nat.Coprime m q then 0 else Analysis.gammaResolventMangoldtWeight m) +
        (∑ m ∈ B,
          if Nat.Coprime m q then (1 - (χ m).re) * Analysis.gammaResolventMangoldtWeight m
          else 0) := by
  classical
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hc : Nat.Coprime m q
  · rw [ite_eq_left hc, ite_eq_left hc, zero_add]
  · have hz : χ m = 0 := χ.map_nonunit (fun hu ↦ hc ((ZMod.isUnit_iff_coprime _ _).mp hu))
    rw [ite_eq_right hc, ite_eq_right hc, hz, Complex.zero_re, sub_zero, one_mul, add_zero]

/-- For a primitive even nonprincipal character under individual RH,
cap only the ramified prefix and certify the even Gamma correction.
The remaining conductor-unit deficit is retained explicitly. This gives
the coarse prefix route without assuming that all units have value one. -/
theorem gammaResolvent_zeroMass_le_capped_even_prefix {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (he : χ.Even) (B : Finset ℕ) :
    (∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          Analysis.gammaResolventMajorant ρ.im) ≤
      (11783423 / 25000000 : ℝ) * Real.log q + (-159 / 100 : ℝ) +
            (∑' m : ℕ, Analysis.gammaResolventMangoldtWeight m) -
          (∑ m ∈ B, Analysis.gammaResolventMangoldtWeight m) +
        (∑ m ∈ B,
          if Nat.Coprime m q then (1 - (χ m).re) * Analysis.gammaResolventMangoldtWeight m
          else 0) := by
  have hs := gammaResolvent_zeroMass_le_signed_prefix hq hRH hp hne hinv B
  have hc := gamma_nonunit_prefix_le_total q B
  have hΓ := Gamma.gammaResolvent_even_correction_le
  have heq : χ.gammaFactor = Complex.Gammaℝ := funext he.gammaFactor_def
  rw [heq, gamma_character_prefix_eq_nonunit_add_unit_deficit χ B] at hs
  linarith only [hs, hc, hΓ]

/-- If every conductor unit in the retained finite set has value one,
the capped even zero-mass bound contains no unit deficit. Ramified inputs
are still present through the single prefix cap. This is the coarse scalar
interface for a genuinely unit-one prefix, rather than an assumption about
all original ambient units after primitivization. -/
theorem gammaResolvent_zeroMass_le_capped_even_prefix_of_units_one {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (he : χ.Even) (B : Finset ℕ)
    (hB : ∀ m ∈ B, Nat.Coprime m q → χ m = 1) :
    (∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          Analysis.gammaResolventMajorant ρ.im) ≤
      (11783423 / 25000000 : ℝ) * Real.log q + (-159 / 100 : ℝ) +
          (∑' m : ℕ, Analysis.gammaResolventMangoldtWeight m) -
        (∑ m ∈ B, Analysis.gammaResolventMangoldtWeight m) := by
  classical
  have hs := gammaResolvent_zeroMass_le_capped_even_prefix hq hRH hp hne hinv he B
  have hz :
    (∑ m ∈ B,
        if Nat.Coprime m q then (1 - (χ m).re) * Analysis.gammaResolventMangoldtWeight m else 0) =
      0 := by
    apply Finset.sum_eq_zero
    intro m hm
    by_cases hc : Nat.Coprime m q
    · rw [ite_eq_left hc, hB m hm hc, Complex.one_re, sub_self, zero_mul]
    · rw [ite_eq_right hc]
  simpa only [hz, add_zero] using hs

/-- The whole common-weight prefix has the same exact prime-indexed
decomposition as the character deficit. Mangoldt support restricts to
prime powers before the bijection and finite row interchange. This
provides a single global cap for selected ramified prime prefixes. -/
theorem gamma_weight_prefix_eq_prime_indexed {b : ℝ} (hb : 0 ≤ b) :
    (∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m) =
      ∑ p ∈ gammaPrefixPrimeSet b,
        ∑ k ∈ gammaPrefixPowerIndices b p, Analysis.gammaResolventMangoldtWeight (p ^ (k + 1)) := by
  have he :
    (∑ m ∈ (Finset.Ioc 0 ⌊b⌋₊).filter IsPrimePow, Analysis.gammaResolventMangoldtWeight m) =
      ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro m hm hnot
    have hpow : ¬IsPrimePow m := fun hh ↦ hnot (Finset.mem_filter.mpr ⟨hm, hh⟩)
    simp only [Analysis.gammaResolventMangoldtWeight, ArithmeticFunction.vonMangoldt_apply,
      ite_eq_right hpow, zero_mul]
  rw [← he, Chebyshev.sum_PrimePow_eq_sum_sum _ hb, gamma_positive_exponent_sum_eq_range]
  exact
    gamma_prefix_rows_eq_prime_sums (Finset.range (gammaPrefixExponentCount b))
      (gammaPrefixRowPrimes b) (fun k p ↦ Analysis.gammaResolventMangoldtWeight (p ^ (k + 1)))

/-- Any selected prime bases in the common finite prefix universe
contribute at most the full common-weight prefix. The proof retains
the signed coefficients inside the nonnegative combined weight, rather
than replacing individual coefficients by their absolute values. -/
theorem gamma_selected_prime_prefix_le_total {b : ℝ} (hb : 0 ≤ b) (R : Finset ℕ)
    (hR : R ⊆ gammaPrefixPrimeSet b) :
    (∑ p ∈ R,
        ∑ k ∈ gammaPrefixPowerIndices b p, Analysis.gammaResolventMangoldtWeight (p ^ (k + 1))) ≤
      ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m := by
  rw [gamma_weight_prefix_eq_prime_indexed hb]
  exact
    Finset.sum_le_sum_of_subset_of_nonneg hR
      (fun p hp hnot ↦
        Finset.sum_nonneg (fun k hk ↦ Analysis.gammaResolventMangoldtWeight_nonneg (p ^ (k + 1))))

/-- Any finite selection of prime bases is capped by the total prefix,
even when it includes primes beyond the cutoff. Such primes have empty
retained power sets. Restrict to the common prime universe before applying
the finite partial-sum comparison. -/
theorem gamma_any_prime_prefix_le_total {b : ℝ} (hb : 0 ≤ b) (R : Finset ℕ) :
    (∑ p ∈ R,
        ∑ k ∈ gammaPrefixPowerIndices b p, Analysis.gammaResolventMangoldtWeight (p ^ (k + 1))) ≤
      ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m := by
  classical
  have he :
    (∑ p ∈ R ∩ gammaPrefixPrimeSet b,
        ∑ k ∈ gammaPrefixPowerIndices b p, Analysis.gammaResolventMangoldtWeight (p ^ (k + 1))) =
      ∑ p ∈ R,
        ∑ k ∈ gammaPrefixPowerIndices b p, Analysis.gammaResolventMangoldtWeight (p ^ (k + 1)) := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro p hp hnot
    have hP : p ∉ gammaPrefixPrimeSet b := fun hh ↦ hnot (Finset.mem_inter.mpr ⟨hp, hh⟩)
    rw [gamma_prefix_power_indices_eq_empty hP, Finset.sum_empty]
  rw [← he]
  exact gamma_selected_prime_prefix_le_total hb _ Finset.inter_subset_right

/-- The actual character Euler loss at selected ramified prime bases
is capped once by the common integer prefix. The zero character value
persists at every positive power, so its deficit is exactly the weight.
This applies to the ramified set in the actual local conductor comparison. -/
theorem gamma_selected_ramified_character_prefix_le_total {q : ℕ} (χ : DirichletCharacter ℂ q)
    {b : ℝ} (hb : 0 ≤ b) (R : Finset ℕ) (hR : ∀ p ∈ R, χ p = 0) :
    (∑ p ∈ R,
        ∑ k ∈ gammaPrefixPowerIndices b p,
          (1 - (χ (p ^ (k + 1))).re) * Analysis.gammaResolventMangoldtWeight (p ^ (k + 1))) ≤
      ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m := by
  have he :
    (∑ p ∈ R,
        ∑ k ∈ gammaPrefixPowerIndices b p,
          (1 - (χ (p ^ (k + 1))).re) * Analysis.gammaResolventMangoldtWeight (p ^ (k + 1))) =
      ∑ p ∈ R,
        ∑ k ∈ gammaPrefixPowerIndices b p, Analysis.gammaResolventMangoldtWeight (p ^ (k + 1)) := by
    apply Finset.sum_congr rfl
    intro p hp
    simp only [map_pow, hR p hp, zero_pow (Nat.succ_ne_zero _), Complex.zero_re, sub_zero, one_mul]
  rw [he]
  exact gamma_any_prime_prefix_le_total hb R

/-- For a prime and scale at least one, its log-weighted signed ramified
ramp is at most log((99/40)x)/sqrt x. Combine the cutoff count bound with
log p positivity and cancel the same prime logarithm. -/
theorem gamma_ramified_prime_ramp_le_log_cutoff {p : ℕ} (hp : p.Prime) {x : ℝ} (hx : 1 ≤ x) :
    Real.log p *
        ((∑' k : ℕ, Analysis.exponentialRampLocalCorrection 0 ((p : ℝ) ^ (k + 1) / x) (k + 1)) /
          Real.sqrt x) ≤
      Real.log ((99 / 40 : ℝ) * x) / Real.sqrt x := by
  have hpR : (1 : ℝ) < p := Nat.one_lt_cast.mpr hp.one_lt
  have hl := Real.log_pos hpR
  have ht :=
    (Analysis.gamma_ramp_zero_series_le_count hp.one_lt (zero_lt_one.trans_le hx)).trans
      (div_le_div_of_nonneg_right (Analysis.gamma_ramp_count_le_log hp.one_lt hx)
        (Real.sqrt_nonneg x))
  have hm := mul_le_mul_of_nonneg_left ht hl.le
  convert hm using 1
  field_simp (discharger :=
    first
    | exact hl.ne'
    | exact (Real.sqrt_pos.2 (zero_lt_one.trans_le hx)).ne')

/-- Selected ramified local costs have one shared finite Euler prefix
cap plus a ramp allowance per selected prime. The common nonnegative
weight permits one global cap; the signed ramp is bounded separately.
This is the local input for the coarse analytic tail comparison. -/
theorem gamma_selected_ramified_local_cost_le_prefix_cap {q : ℕ} (χ : DirichletCharacter ℂ q)
    {b x : ℝ} (hb : 0 ≤ b) (hx : 1 ≤ x) (R : Finset ℕ) (hR : ∀ p ∈ R, p.Prime ∧ χ p = 0) :
    (∑ p ∈ R, Analysis.gammaActualPrimeLocalCost χ p (gammaPrefixPowerIndices b p) x) ≤
      (∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m) +
        (R.card : ℝ) * (Real.log ((99 / 40 : ℝ) * x) / Real.sqrt x) := by
  have he := gamma_selected_ramified_character_prefix_le_total χ hb R (fun p hp ↦ (hR p hp).2)
  have hr :
    (∑ p ∈ R,
        Real.log p *
          ((∑' k : ℕ,
              Analysis.exponentialRampLocalCorrection (χ p) ((p : ℝ) ^ (k + 1) / x) (k + 1)) /
            Real.sqrt x)) ≤
      (R.card : ℝ) * (Real.log ((99 / 40 : ℝ) * x) / Real.sqrt x) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro p hp
    rw [(hR p hp).2]
    exact gamma_ramified_prime_ramp_le_log_cutoff (hR p hp).1 hx
  simp only [Analysis.gammaActualPrimeLocalCost, Finset.sum_add_distrib]
  linarith only [he, hr]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
