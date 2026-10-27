/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaDyadicTailBounds
public import PseudoPrime.Analysis.GammaDyadicGridCertificate
public import PseudoPrime.Analysis.GammaDyadicGridCover

/-! # Uniform ramified dyadic budget for the refined Gamma bound -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- On a positive scale interval whose upper endpoint satisfies the explicit
cutoff at power m+1, the actual ramified dyadic series is bounded by the
first m exponential terms at the upper endpoint. Drop the nonpositive tail,
then normalize by the lower endpoint. This avoids logarithmic floor data
in finite rational certificates. -/
theorem gamma_dyadic_ramified_series_le_exp_prefix {x lo hi : ℝ} (hlo : 0 < lo) (hlox : lo ≤ x)
    (hxhi : x ≤ hi) (m : ℕ) (hcut : (99 / 40 : ℝ) * hi ≤ (2 : ℝ) ^ (m + 1)) :
    (∑' k : ℕ, exponentialRampLocalCorrection 0 ((2 : ℝ) ^ (k + 1) / x) (k + 1)) / Real.sqrt x ≤
      (∑ k ∈ Finset.range m, Real.exp (-((2 : ℝ) ^ (k + 1) / hi))) / Real.sqrt lo := by
  have hx : 0 < x := hlo.trans_le hlox
  let u := fun k : ℕ ↦ (2 : ℝ) ^ (k + 1) / x
  have hdiv (k : ℕ) : (2 : ℝ) ^ (k + 1) / hi ≤ u k :=
    div_le_div₀ (pow_nonneg (by norm_num only : (0 : ℝ) ≤ 2) _) le_rfl hx hxhi
  have ht : ∀ k, 99 / 40 ≤ u (k + m) := by
    intro k
    apply (le_div_iff₀ hx).mpr
    have hp : (2 : ℝ) ^ (m + 1) ≤ (2 : ℝ) ^ (k + m + 1) := by
      exact_mod_cast
        Nat.pow_le_pow_right (by norm_num only : 0 < (2 : ℕ))
          (Nat.add_le_add_right (Nat.le_add_left m k) 1)
    exact ((mul_le_mul_of_nonneg_left hxhi (by norm_num only)).trans hcut).trans hp
  have hs :=
    exponentialRampLocalCorrection_tsum_le_prefix (Or.inl rfl) hx u
      (prime_power_div_scale_ge_linear (by norm_num only : 1 < (2 : ℕ)) hx) m ht
  have hb :=
    Finset.sum_le_sum (s := Finset.range m)
      (fun k hk ↦
        (exponentialRampLocalCorrection_zero_le_weight _ (Nat.succ_pos k)).trans
          (((exponentialRampWeight_bounds _).2).trans (Real.exp_le_exp.mpr (neg_le_neg (hdiv k)))))
  have hn : 0 ≤ ∑ k ∈ Finset.range m, Real.exp (-((2 : ℝ) ^ (k + 1) / hi)) :=
    Finset.sum_nonneg (fun k hk ↦ (Real.exp_pos _).le)
  exact
    (div_le_div_of_nonneg_right (hs.trans hb) (Real.sqrt_nonneg x)).trans
      (div_le_div₀ hn le_rfl (Real.sqrt_pos.mpr hlo) (Real.sqrt_le_sqrt hlox))

/-- On each certified grid interval, the actual weighted ramified dyadic
ramp loss is at most 649/10000. The power cutoff drops the signed tail,
the Taylor certificate bounds the finite prefix, and the certified integer
root supplies the normalization. This transfers every rational grid check
to the actual analytic series on its full closed interval. -/
theorem gamma_dyadic_grid_actual_ramp_le (i : ℕ) (hi : i ∈ Finset.range 200) {x : ℝ}
    (hlox : (gammaDyadicGridLower i : ℝ) ≤ x) (hxhi : x ≤ (gammaDyadicGridUpper i : ℝ)) :
    Real.log 2 *
        ((∑' k : ℕ, exponentialRampLocalCorrection 0 ((2 : ℝ) ^ (k + 1) / x) (k + 1)) /
          Real.sqrt x) ≤
      (649 / 10000 : ℝ) := by
  obtain ⟨_, hsquare, hcut, hupper⟩ := gamma_dyadic_grid_checks i hi
  have hloQ : 0 < gammaDyadicGridLower i := by
    dsimp only [gammaDyadicGridLower]
    nlinarith only [(Nat.cast_nonneg i : (0 : ℚ) ≤ i)]
  have hhiQ : 0 < gammaDyadicGridUpper i := by
    dsimp only [gammaDyadicGridUpper]
    nlinarith only [(Nat.cast_nonneg i : (0 : ℚ) ≤ i)]
  have hloR : (0 : ℝ) < gammaDyadicGridLower i := by exact_mod_cast hloQ
  have hcR : (99 / 40 : ℝ) * (gammaDyadicGridUpper i : ℝ) ≤ (2 : ℝ) ^ 17 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hcut
    norm_num only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow] at h
    norm_num only
    exact h
  have hsR : (gammaDyadicGridRoot i : ℝ) ^ 2 ≤ (gammaDyadicGridLower i : ℝ) := by
    exact_mod_cast hsquare
  have hroot := (Real.le_sqrt (Nat.cast_nonneg _) hloR.le).mpr hsR
  have hUR :
    (7 / 10 : ℝ) * (gammaDyadicExpPrefixUpper (gammaDyadicGridUpper i) 16 : ℝ) ≤
      (649 / 10000 : ℝ) * (gammaDyadicGridRoot i : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr hupper
    norm_num only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast] at h
    exact h
  have hp := gamma_dyadic_exp_prefix_upper_valid hhiQ 16
  have hU0 : (0 : ℝ) ≤ gammaDyadicExpPrefixUpper (gammaDyadicGridUpper i) 16 :=
    (Finset.sum_nonneg (fun k hk ↦ (Real.exp_pos _).le)).trans hp
  have hs :=
    (gamma_dyadic_ramified_series_le_exp_prefix hloR hlox hxhi 16 hcR).trans
      (div_le_div_of_nonneg_right hp (Real.sqrt_nonneg _))
  have hw := mul_le_mul_of_nonneg_left hs (Real.log_nonneg (by norm_num only : (1 : ℝ) ≤ 2))
  simp only [← mul_div_assoc] at hw
  have hnum :=
    mul_le_mul_of_nonneg_right (by linarith only [Real.log_two_lt_d9] : Real.log 2 ≤ (7 / 10 : ℝ))
      hU0
  have hfinal :
    Real.log 2 * (gammaDyadicExpPrefixUpper (gammaDyadicGridUpper i) 16 : ℝ) ≤
      (649 / 10000 : ℝ) * Real.sqrt (gammaDyadicGridLower i : ℝ) :=
    (hnum.trans hUR).trans (mul_le_mul_of_nonneg_left hroot (by norm_num only))
  simpa only [mul_div_assoc] using hw.trans ((div_le_iff₀ (Real.sqrt_pos.mpr hloR)).mpr hfinal)

/-- For all scales at least 20000, the actual weighted ramified dyadic
ramp loss is at most 649/10000. The exact grid covers the bounded range,
and the analytic tail bound covers every larger scale. This closes the
ramp certificate over the full scale range required by the refined cutoff. -/
theorem gamma_dyadic_ramified_actual_ramp_le {x : ℝ} (hx : 20000 ≤ x) :
    Real.log 2 *
        ((∑' k : ℕ, exponentialRampLocalCorrection 0 ((2 : ℝ) ^ (k + 1) / x) (k + 1)) /
          Real.sqrt x) ≤
      (649 / 10000 : ℝ) := by
  by_cases hsmall : x < 40000
  · obtain ⟨i, hi, hlo, hhi⟩ := gamma_dyadic_grid_covers hx hsmall
    exact gamma_dyadic_grid_actual_ramp_le i hi hlo hhi
  · exact
      (gamma_dyadic_ramified_actual_ramp_tail_le (le_of_not_gt hsmall)).trans
        (by norm_num only : (1 / 16 : ℝ) ≤ 649 / 10000)

/-- At every scale at least 20000, the actual finite ramified Euler loss
and full signed dyadic ramp loss together are at most three quarters.
Combine the signed Euler certificate 6851/10000 with the uniform ramp
certificate 649/10000. This completes the numerical ramified dyadic budget
required in the even-conductor branch. -/
theorem gamma_dyadic_ramified_actual_cost_le (K : Finset ℕ) {x : ℝ} (hx : 20000 ≤ x) :
    (∑ k ∈ K, gammaResolventMangoldtWeight (2 ^ (k + 1))) +
        Real.log 2 *
          ((∑' k : ℕ, exponentialRampLocalCorrection 0 ((2 : ℝ) ^ (k + 1) / x) (k + 1)) /
            Real.sqrt x) ≤
      (3 / 4 : ℝ) := by
  have he := sum_gammaResolventMangoldtWeight_primePowers_le_cost Nat.prime_two K
  have hc := gamma_dyadic_weighted_euler_bounds.1
  have hr := gamma_dyadic_ramified_actual_ramp_le hx
  norm_num only [Nat.cast_ofNat] at he
  linarith only [he, hc, hr]

/-- At the prescribed refined scale for L>=100 log ten, the actual
ramified dyadic cost is at most three quarters. The proved scale lower
bound removes the independent scale condition from the numerical budget. -/
theorem gamma_refined_dyadic_ramified_actual_cost_le (K : Finset ℕ) {L : ℝ}
    (hL : 100 * Real.log 10 ≤ L) :
    (∑ k ∈ K, gammaResolventMangoldtWeight (2 ^ (k + 1))) +
        Real.log 2 *
          ((∑' k : ℕ,
              exponentialRampLocalCorrection 0 ((2 : ℝ) ^ (k + 1) / gammaRefinedScale L) (k + 1)) /
            Real.sqrt (gammaRefinedScale L)) ≤
      (3 / 4 : ℝ) := by
  exact gamma_dyadic_ramified_actual_cost_le K (gamma_refined_scale_ge_twenty_thousand hL)

/-- A Dirichlet character at an even modulus vanishes at two. Evenness
makes two a divisor, hence a nonunit in the residue ring. This identifies
the actual local character value in the ramified dyadic branch. -/
theorem gamma_even_modulus_character_two_zero {f : ℕ} (χ : DirichletCharacter ℂ f) (hf : Even f) :
    χ 2 = 0 := by
  have hnu : ¬IsUnit ((2 : ℕ) : ZMod f) := by
    simpa only [ZMod.isUnit_iff_coprime, Nat.Prime.coprime_iff_not_dvd Nat.prime_two, not_not] using
      hf.two_dvd
  simpa only [Nat.cast_ofNat] using χ.map_nonunit hnu

/-- For an even-modulus character and every scale at least 20000, the
actual dyadic character Euler correction and signed local ramp series
have total cost at most three quarters. Character vanishing identifies
the ramified local value and every positive power, connecting the numerical
certificate to the actual even-conductor character branch. -/
theorem gamma_even_modulus_actual_dyadic_cost_le {f : ℕ} (χ : DirichletCharacter ℂ f) (hf : Even f)
    (K : Finset ℕ) {x : ℝ} (hx : 20000 ≤ x) :
    (∑ k ∈ K, (1 - (χ (2 ^ (k + 1))).re) * gammaResolventMangoldtWeight (2 ^ (k + 1))) +
        Real.log 2 *
          ((∑' k : ℕ, exponentialRampLocalCorrection (χ 2) ((2 : ℝ) ^ (k + 1) / x) (k + 1)) /
            Real.sqrt x) ≤
      (3 / 4 : ℝ) := by
  have hz := gamma_even_modulus_character_two_zero χ hf
  norm_num only [Nat.cast_pow, Nat.cast_ofNat, map_pow, hz, zero_pow (Nat.succ_ne_zero _),
    Complex.zero_re, sub_zero, one_mul]
  exact gamma_dyadic_ramified_actual_cost_le K hx

/-- At the prescribed refined scale throughout L>=100 log ten, every
even-modulus character has actual dyadic loss at most three quarters.
Use the proved scale lower bound and the actual character cost theorem.
This is the even-conductor interface for the refined witness comparison. -/
theorem gamma_refined_even_modulus_dyadic_cost_le {f : ℕ} (χ : DirichletCharacter ℂ f) (hf : Even f)
    (K : Finset ℕ) {L : ℝ} (hL : 100 * Real.log 10 ≤ L) :
    (∑ k ∈ K, (1 - (χ (2 ^ (k + 1))).re) * gammaResolventMangoldtWeight (2 ^ (k + 1))) +
        Real.log 2 *
          ((∑' k : ℕ,
              exponentialRampLocalCorrection (χ 2) ((2 : ℝ) ^ (k + 1) / gammaRefinedScale L)
                (k + 1)) /
            Real.sqrt (gammaRefinedScale L)) ≤
      (3 / 4 : ℝ) := by
  exact gamma_even_modulus_actual_dyadic_cost_le χ hf K (gamma_refined_scale_ge_twenty_thousand hL)

end PseudoPrime.Analysis
