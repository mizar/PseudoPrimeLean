/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaSmallPrimeCosts
public import PseudoPrime.Analysis.GammaSignedEulerSeries
public import PseudoPrime.Analysis.LogTaylorBounds

/-! # Signed finite Euler intervals and prime-power payload certificates -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The rational lower endpoint for the fixed signed Euler weight.
Use the lower power endpoint for nonnegative coefficients and the upper
endpoint for negative coefficients. Soundness requires certified power intervals. -/
def gammaFiniteEulerLower (r : ℚ → ℚ × ℚ) : ℚ :=
  (gammaResolventCoefficients.map
      (fun ab ↦ ab.2 * (if 0 ≤ ab.2 then (r ab.1).1 else (r ab.1).2))).sum

/-- The rational upper endpoint for the fixed signed Euler weight.
Choose the power endpoint according to the coefficient sign. This retains
the cancellation needed by finite scalar mass certificates. -/
def gammaFiniteEulerUpper (r : ℚ → ℚ × ℚ) : ℚ :=
  (gammaResolventCoefficients.map
      (fun ab ↦ ab.2 * (if 0 ≤ ab.2 then (r ab.1).2 else (r ab.1).1))).sum

/-- A real value in a rational interval gives both signed scalar
bounds. Split by the rational coefficient sign and use order preservation
or reversal under multiplication. This is the node interval interface. -/
theorem signed_rational_node_bounds {b l u : ℚ} {v : ℝ} (hl : (l : ℝ) ≤ v) (hu : v ≤ (u : ℝ)) :
    ((b * (if 0 ≤ b then l else u) : ℚ) : ℝ) ≤ (b : ℝ) * v ∧
      (b : ℝ) * v ≤ ((b * (if 0 ≤ b then u else l) : ℚ) : ℝ) := by
  by_cases hb : 0 ≤ b
  · rw [ite_eq_left hb, ite_eq_left hb, Rat.cast_mul, Rat.cast_mul]
    exact
      ⟨mul_le_mul_of_nonneg_left hl ((Rat.cast_nonneg (K := ℝ)).mpr hb),
        mul_le_mul_of_nonneg_left hu ((Rat.cast_nonneg (K := ℝ)).mpr hb)⟩
  · rw [ite_eq_right hb, ite_eq_right hb, Rat.cast_mul, Rat.cast_mul]
    have hbR : (b : ℝ) ≤ 0 := ((Rat.cast_nonpos (K := ℝ)).mpr (le_of_not_ge hb))
    exact ⟨mul_le_mul_of_nonpos_left hu hbR, mul_le_mul_of_nonpos_left hl hbR⟩

/-- At any real input, rational intervals containing each fixed
node power enclose the actual signed Euler weight. Sum the signed node
bounds and commute the rational cast with the finite list sum. -/
theorem gamma_finite_euler_bounds {m : ℝ} (r : ℚ → ℚ × ℚ)
    (hr :
      ∀ ab ∈ gammaResolventCoefficients,
        ((r ab.1).1 : ℝ) ≤ m ^ (-(1 / 2 + (ab.1 : ℝ))) ∧
          m ^ (-(1 / 2 + (ab.1 : ℝ))) ≤ ((r ab.1).2 : ℝ)) :
    (gammaFiniteEulerLower r : ℝ) ≤ gammaResolventEulerWeight m ∧
      gammaResolventEulerWeight m ≤ (gammaFiniteEulerUpper r : ℝ) := by
  have hl :=
    List.sum_le_sum
      (fun ab hab ↦ (signed_rational_node_bounds (b := ab.2) (hr ab hab).1 (hr ab hab).2).1)
  have hu :=
    List.sum_le_sum
      (fun ab hab ↦ (signed_rational_node_bounds (b := ab.2) (hr ab hab).1 (hr ab hab).2).2)
  norm_num only [gammaFiniteEulerLower, gammaFiniteEulerUpper, Rat.cast_list_sum, List.map_map,
    Function.comp_def]
  exact ⟨hl, hu⟩

/-- For a prime and nonzero exponent, logarithm and Euler-weight
intervals imply rational bounds for the actual Mangoldt weight. Assume the
Euler lower endpoint is nonnegative. Evaluate Mangoldt on the prime power
and apply product monotonicity using the actual Euler-weight positivity. -/
theorem gamma_prime_power_mangoldt_bounds {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) {l u h H : ℚ}
    (hl : (l : ℝ) ≤ Real.log p) (hu : Real.log p ≤ (u : ℝ))
    (hh : (h : ℝ) ≤ gammaResolventEulerWeight (p ^ k : ℕ))
    (hH : gammaResolventEulerWeight (p ^ k : ℕ) ≤ (H : ℝ)) (hh0 : 0 ≤ h) :
    ((l * h : ℚ) : ℝ) ≤ gammaResolventMangoldtWeight (p ^ k) ∧
      gammaResolventMangoldtWeight (p ^ k) ≤ ((u * H : ℚ) : ℝ) := by
  have hm : (1 : ℝ) ≤ (p ^ k : ℕ) :=
    Nat.one_le_cast.mpr (one_le_pow₀ (Nat.one_le_iff_ne_zero.mpr hp.ne_zero))
  have hw := gamma_resolvent_euler_weight_nonneg hm
  have hlog := Real.log_nonneg (Nat.one_le_cast.mpr hp.one_lt.le)
  rw [gammaResolventMangoldtWeight, ArithmeticFunction.vonMangoldt_apply_pow hk,
    ArithmeticFunction.vonMangoldt_apply_prime hp, Rat.cast_mul, Rat.cast_mul]
  exact
    ⟨mul_le_mul hl hh ((Rat.cast_nonneg (K := ℝ)).mpr hh0) hlog,
      mul_le_mul hu hH hw (hlog.trans hu)⟩

/-- A finite set of prime and exponent-minus-one pairs whose image
is exactly the prime-power support through B gives the actual full prefix.
Prime-power uniqueness makes the map injective; Mangoldt vanishing removes
all remaining inputs. This verifies the mathematical meaning of a finite payload. -/
theorem gamma_payload_eq_prefix (B : ℕ) (S : Finset (ℕ × ℕ)) (hP : ∀ pk ∈ S, pk.1.Prime)
    (hcover : S.image (fun pk ↦ pk.1 ^ (pk.2 + 1)) = (Finset.Ioc 0 B).filter IsPrimePow) :
    (∑ m ∈ Finset.Ioc 0 B, gammaResolventMangoldtWeight m) =
      ∑ pk ∈ S, gammaResolventMangoldtWeight (pk.1 ^ (pk.2 + 1)) := by
  classical
  have he :
    (∑ m ∈ (Finset.Ioc 0 B).filter IsPrimePow, gammaResolventMangoldtWeight m) =
      ∑ m ∈ Finset.Ioc 0 B, gammaResolventMangoldtWeight m := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro m hmem hnot
    have hm : ¬IsPrimePow m := fun h ↦ hnot (Finset.mem_filter.mpr ⟨hmem, h⟩)
    rw [gammaResolventMangoldtWeight, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hm, zero_mul]
  rw [← he, ← hcover]
  exact
    Finset.sum_image
      (fun a ha b hb hab ↦
        Prod.ext ((hP a ha).pow_inj (hP b hb) hab).1 ((hP a ha).pow_inj (hP b hb) hab).2)

/-- A prime-power payload with certified exact support and rational
row bounds encloses the full actual finite Euler prefix through B. Reindex
by the proved payload equality and sum the row inequalities. -/
theorem gamma_payload_prefix_bounds (B : ℕ) (S : Finset (ℕ × ℕ)) (hP : ∀ pk ∈ S, pk.1.Prime)
    (hcover : S.image (fun pk ↦ pk.1 ^ (pk.2 + 1)) = (Finset.Ioc 0 B).filter IsPrimePow)
    (lo hi : ℕ × ℕ → ℚ)
    (hr :
      ∀ pk ∈ S,
        (lo pk : ℝ) ≤ gammaResolventMangoldtWeight (pk.1 ^ (pk.2 + 1)) ∧
          gammaResolventMangoldtWeight (pk.1 ^ (pk.2 + 1)) ≤ (hi pk : ℝ)) :
    ((∑ pk ∈ S, lo pk : ℚ) : ℝ) ≤ (∑ m ∈ Finset.Ioc 0 B, gammaResolventMangoldtWeight m) ∧
      (∑ m ∈ Finset.Ioc 0 B, gammaResolventMangoldtWeight m) ≤ ((∑ pk ∈ S, hi pk : ℚ) : ℝ) := by
  rw [gamma_payload_eq_prefix B S hP hcover]
  norm_num only [Rat.cast_sum]
  exact
    ⟨Finset.sum_le_sum (fun pk hpk ↦ (hr pk hpk).1), Finset.sum_le_sum (fun pk hpk ↦ (hr pk hpk).2)⟩

/-- Check a positive rational base and both twentieth-power
inequalities at every fixed Gamma node, including exponent identities and
endpoint nonnegativity. A true result certifies real-power intervals. -/
def gammaFiniteEulerRatioCheck (m : ℚ) (r : ℚ → ℚ × ℚ) : Bool :=
  decide
    (0 < m ∧
      gammaResolventCoefficients.Forall
        (fun ab ↦
          0 ≤ (r ab.1).1 ∧
            0 ≤ (r ab.1).2 ∧
            20 * ab.1 + 10 = (gammaSmallPrimeRatioExponent ab.1 : ℚ) ∧
            (r ab.1).1 ^ 20 * m ^ gammaSmallPrimeRatioExponent ab.1 ≤ 1 ∧
            1 ≤ (r ab.1).2 ^ 20 * m ^ gammaSmallPrimeRatioExponent ab.1))

/-- A successful finite ratio check encloses the real node power
at every fixed Gamma node. Cast the exact rational checks and apply the
proved twentieth-root interval theorem. No numerical oracle is used. -/
theorem gamma_finite_ratio_check_sound {m : ℚ} {r : ℚ → ℚ × ℚ}
    (hc : gammaFiniteEulerRatioCheck m r = true) (ab : ℚ × ℚ)
    (hab : ab ∈ gammaResolventCoefficients) :
    ((r ab.1).1 : ℝ) ≤ (m : ℝ) ^ (-(1 / 2 + (ab.1 : ℝ))) ∧
      (m : ℝ) ^ (-(1 / 2 + (ab.1 : ℝ))) ≤ ((r ab.1).2 : ℝ) := by
  have h := of_decide_eq_true hc
  obtain ⟨hl, hu, he, hlo, hhi⟩ := List.forall_iff_forall_mem.mp h.2 ab hab
  have hlR := (Rat.cast_le (K := ℝ)).mpr hl
  have huR := (Rat.cast_le (K := ℝ)).mpr hu
  have hloR := (Rat.cast_le (K := ℝ)).mpr hlo
  have hhiR := (Rat.cast_le (K := ℝ)).mpr hhi
  have heR := congrArg (fun q : ℚ ↦ (q : ℝ)) he
  norm_num only [Rat.cast_mul, Rat.cast_add, Rat.cast_ofNat, Rat.cast_natCast, Rat.cast_pow,
    Rat.cast_one, Rat.cast_zero] at hlR huR hloR hhiR heR
  have hexp : -(gammaSmallPrimeRatioExponent ab.1 : ℝ) / 20 = -(1 / 2 + (ab.1 : ℝ)) := by
    linarith only [heR]
  simpa only [hexp] using
    gamma_rpow_neg_twentieth_interval ((Rat.cast_pos (K := ℝ)).mpr h.1) hlR huR
      (gammaSmallPrimeRatioExponent ab.1) hloR hhiR

/-- A successful power check bounds the whole actual signed Euler
weight by its rational endpoints. Connect the node certificate to the
signed finite-sum theorem; this is the common row evaluation interface. -/
theorem gamma_finite_ratio_check_euler_bounds {m : ℚ} {r : ℚ → ℚ × ℚ}
    (hc : gammaFiniteEulerRatioCheck m r = true) :
    (gammaFiniteEulerLower r : ℝ) ≤ gammaResolventEulerWeight m ∧
      gammaResolventEulerWeight m ≤ (gammaFiniteEulerUpper r : ℝ) := by
  exact gamma_finite_euler_bounds r (gamma_finite_ratio_check_sound hc)

/-- For a prime-power row, successful power and logarithm checks
and a nonnegative rational Euler lower endpoint certify both actual
Mangoldt-weight bounds. Compose the two check soundness theorems with
the prime-power product bounds for use in finite prefix certificates. -/
theorem gamma_prime_power_row_check_bounds {p k j n : ℕ} (hp : p.Prime) {r : ℚ → ℚ × ℚ} {l u : ℚ}
    (hc : gammaFiniteEulerRatioCheck (p ^ (k + 1) : ℕ) r = true)
    (hl : rationalLogIntervalCheck p j n l u = true) (hh : 0 ≤ gammaFiniteEulerLower r) :
    ((l * gammaFiniteEulerLower r : ℚ) : ℝ) ≤ gammaResolventMangoldtWeight (p ^ (k + 1)) ∧
      gammaResolventMangoldtWeight (p ^ (k + 1)) ≤ ((u * gammaFiniteEulerUpper r : ℚ) : ℝ) := by
  have he := gamma_finite_ratio_check_euler_bounds hc
  have ht := rationalLogIntervalCheck_sound hl
  norm_num only [Rat.cast_natCast] at he ht
  exact gamma_prime_power_mangoldt_bounds hp (Nat.succ_ne_zero k) ht.1 ht.2 he.1 he.2 hh

end PseudoPrime.Analysis
