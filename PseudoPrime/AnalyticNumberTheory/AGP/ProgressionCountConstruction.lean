/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.AGP.P2SeedScale
public import PseudoPrime.AnalyticNumberTheory.AGP.ProgressionCountData

/-! # ProgressionCountConstruction

Construct the finite progression-supply data from uniform Proposition 1.5 counts.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.AGP

/--
Inputs: a positive seed constant, a positive scale `m`, the cubic scale condition `m ^ 3 ≤ z`,
and a lower bound on `c₀ * m` imply a seed factor-count estimate.

Claim: the seed estimate forces the output ratio `T / (4 z m)` to be at least `2 ^ 64`.

Content: the proof cross-multiplies positive denominators and uses `m ^ 3 ≤ z` to compare
the explicit seed lower bound with the threshold.

Role: this supplies the ratio hypothesis required by the fixed-factor P2 comparison.
-/
theorem p2_seed_output_ratio_ge_of_linear_threshold {c₀ : ℝ} {m z T : ℕ} (hc₀ : 0 < c₀) (hm : 1 ≤ m)
    (hz : m ^ 3 ≤ z) (hthreshold : 2 ^ 64 * (160 * Real.log 2) ≤ c₀ * m)
    (hseed :
      (c₀ * (z : ℝ) ^ 2 / (40 * (m : ℝ) * Real.log 2)) / (4 * ((z * m : ℕ) : ℝ)) ≤
        (T : ℝ) / (4 * ((z * m : ℕ) : ℝ))) :
    2 ^ 64 ≤ (T : ℝ) / (4 * ((z * m : ℕ) : ℝ)) := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num only : (1 : ℝ) < 2)
  have hmR : 0 < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num only : 0 < 1) hm)
  have hmpos : 0 < m := Nat.lt_of_lt_of_le (by norm_num only) hm
  have hzR : 0 < (z : ℝ) := by exact_mod_cast (lt_of_lt_of_le (Nat.pow_pos hmpos) hz)
  have hcubeR : (m : ℝ) ^ 3 ≤ (z : ℝ) := by exact_mod_cast hz
  have hfour : 0 < 4 * ((z : ℝ) * (m : ℝ)) :=
    mul_pos (by norm_num only : (0 : ℝ) < 4) (mul_pos hzR hmR)
  have hforty : 0 < 40 * (m : ℝ) * Real.log 2 :=
    mul_pos (mul_pos (by norm_num only : (0 : ℝ) < 40) hmR) hlog2
  have hthresholdM : (2 : ℝ) ^ 64 * (160 * Real.log 2) * (m : ℝ) ^ 2 ≤ c₀ * (m : ℝ) ^ 3 := by
    calc
      (2 : ℝ) ^ 64 * (160 * Real.log 2) * (m : ℝ) ^ 2 ≤ (c₀ * (m : ℝ)) * (m : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hthreshold (sq_nonneg (m : ℝ))
      _ = c₀ * (m : ℝ) ^ 3 := by ring
  have hnum : (2 : ℝ) ^ 64 * (160 * Real.log 2) * (m : ℝ) ^ 2 * (z : ℝ) ≤ c₀ * (z : ℝ) ^ 2 := by
    calc
      (2 : ℝ) ^ 64 * (160 * Real.log 2) * (m : ℝ) ^ 2 * (z : ℝ) ≤ (c₀ * (m : ℝ) ^ 3) * (z : ℝ) :=
        mul_le_mul_of_nonneg_right hthresholdM (le_of_lt hzR)
      _ ≤ (c₀ * (z : ℝ)) * (z : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcubeR (le_of_lt hc₀)) (le_of_lt hzR)
      _ = c₀ * (z : ℝ) ^ 2 := by ring
  have hratioBase :
    (2 : ℝ) ^ 64 ≤
      (c₀ * (z : ℝ) ^ 2 / (40 * (m : ℝ) * Real.log 2)) / (4 * ((z : ℝ) * (m : ℝ))) := by
    apply (le_div_iff₀ hfour).2
    apply (le_div_iff₀ hforty).2
    calc
      (2 : ℝ) ^ 64 * (4 * ((z : ℝ) * (m : ℝ))) * (40 * (m : ℝ) * Real.log 2) =
          (2 : ℝ) ^ 64 * (160 * Real.log 2) * (m : ℝ) ^ 2 * (z : ℝ) :=
        by ring
      _ ≤ c₀ * (z : ℝ) ^ 2 := hnum
  have hseed' :
    (c₀ * (z : ℝ) ^ 2 / (40 * (m : ℝ) * Real.log 2)) / (4 * ((z : ℝ) * (m : ℝ))) ≤
      (T : ℝ) / (4 * ((z : ℝ) * (m : ℝ))) := by
    simpa only [Nat.cast_mul] using hseed
  simpa only [Nat.cast_mul] using le_trans hratioBase hseed'

open PseudoPrime.NumberTheory.PrimeProducts in
/--
Inputs: the seed-start and final Proposition 1.5 thresholds.

Claim: an initial modulus-one uniform count supplies the auxiliary data required by P2 for
every finite positive-base set and every cutoff.

Content: enlarge the seed threshold to cover the finite data, apply the seed constructor, and
transfer its size, factor-count, and ratio bounds through the explicit P2 comparison.

Role: this proves the finite auxiliary-data existence interface from the initial analytic count.
-/
theorem agp_progression_auxiliary_data_exists_of_uniform_count (c₀ : ℝ) (xSeed x₀ : ℕ) :
    AGPProgressionAuxiliaryDataExists c₀ xSeed x₀ := by
  intro hc₀ hcount W C hWpos
  obtain
    ⟨mBase, zBase, hBase10, hBaseCut, hzBase, hcubeBase, hWBase, hmaxBase, hWBaseZ, hmaxBaseZ,
      hcScaleBase, hlinearBase, hparamBase⟩ :=
    exists_p2_seed_common_scale hc₀ (max xSeed x₀) C W
  have hxSeed : xSeed ≤ max xSeed x₀ := le_max_left _ _
  have hxBase : max xSeed x₀ ≤ mBase := hBaseCut
  have hxSeedBase : xSeed ≤ mBase := le_trans hxSeed hxBase
  rcases hcount with ⟨hxSeedTwo, hmodPos, hcoprime, hcountFn⟩
  have hcountBase : ReliableProp15UniformCount c₀ 1 1 mBase := by
    refine ⟨?_, by norm_num only, by norm_num only, ?_⟩
    · exact le_trans (by norm_num only : 2 ≤ 10) hBase10
    · intro L x hx hSquarefree hCoprime
      exact hcountFn L x (le_trans hxSeedBase hx) hSquarefree hCoprime
  obtain ⟨m, z, T, hm10, hmbase, hz, hTdef, hT, hT1024, hscale, hTpow, hdata⟩ :=
    exists_seed_auxiliary_modulus_of_primeProductLE_scale hc₀ mBase hcountBase
  have hbaseToSeed : mBase ≤ m := hmbase
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num only : (1 : ℝ) < 2)
  have hlogden : 0 < 20 * Real.log 2 := mul_pos (by norm_num only : (0 : ℝ) < 20) hlog2
  have hparamSeed : c₀ < 20 * Real.log 2 * (m : ℝ) ^ 4 := by
    have hpowNat : mBase ^ 4 ≤ m ^ 4 := Nat.pow_le_pow_left hbaseToSeed 4
    have hpow : (mBase : ℝ) ^ 4 ≤ (m : ℝ) ^ 4 := by exact_mod_cast hpowNat
    exact lt_of_lt_of_le hparamBase (mul_le_mul_of_nonneg_left hpow (le_of_lt hlogden))
  have hlinearSeed : 2 ^ 64 * (160 * Real.log 2) ≤ c₀ * m := by
    have hmR : (mBase : ℝ) ≤ (m : ℝ) := by exact_mod_cast hbaseToSeed
    have hmul := mul_le_mul_of_nonneg_left hmR (le_of_lt hc₀)
    exact le_trans hlinearBase hmul
  have hcscaleSeed : 1 ≤ c₀ * z := by
    have hzBaseLe : zBase ≤ z := by
      rw [hzBase, hz]
      exact Nat.pow_le_pow_right (by norm_num only : 0 < 2) hbaseToSeed
    have hzBaseLeR : (zBase : ℝ) ≤ (z : ℝ) := by exact_mod_cast hzBaseLe
    have hmul := mul_le_mul_of_nonneg_left hzBaseLeR (le_of_lt hc₀)
    exact le_trans hcScaleBase hmul
  have hcubeSeed : m ^ 3 ≤ z := by simpa only [hz] using powTwo_ge_cube hm10
  have hmleCube : m ≤ m ^ 3 := Nat.le_self_pow (by norm_num only : 3 ≠ 0) m
  have hmlez : m ≤ z := le_trans hmleCube hcubeSeed
  have hWSeed : W.card ≤ z * m := by
    have h1m : 1 ≤ m := le_trans (by norm_num only : 1 ≤ 10) hm10
    have hzge1 : 1 ≤ z := le_trans h1m hmlez
    have hbaseZm : mBase ≤ z * m :=
      le_trans hbaseToSeed (by simpa only [one_mul] using Nat.mul_le_mul_right m hzge1)
    exact le_trans hWBase hbaseZm
  have hTupper : T + 1 ≤ z ^ 3 :=
    p2_seed_count_succ_le_cube_of_parameter_bound hc₀
      (Nat.le_trans (by norm_num only : 1 ≤ 10) hm10) hz hcubeSeed hparamSeed hTdef
  rcases hdata with
    ⟨k, S, L, hk, hkpow, _, hScard, hS, _, _, _, _, _, _, _, _, hfactor, hL, hlambda, hProp15Input,
      hLbound, hLambdaBound, hFactorCount, hLsize, hseedRatio⟩
  let N : ℕ := (primeSetLE z).prod id
  have hpi : 3 * m ≤ Nat.primeCounting z := by
    simpa only [hz] using primeCounting_two_pow_lower hm10
  have hNlower : z ^ 3 ≤ N := by
    calc
      z ^ 3 = (2 ^ m) ^ 3 := by rw [hz]
      _ = 2 ^ (m * 3) := by rw [← pow_mul]
      _ = 2 ^ (3 * m) := by rw [Nat.mul_comm]
      _ ≤ 2 ^ Nat.primeCounting z := Nat.pow_le_pow_right (by norm_num only : 0 < 2) hpi
      _ ≤ N := by
        dsimp [N]
        exact primeProductLE_ge_two_pow_primeCounting z
  have hzpos : 0 < z := Nat.lt_of_lt_of_le (by norm_num only : 0 < 10) (le_trans hm10 hmlez)
  have hNupper : N ≤ z ^ (z + 1) := by
    dsimp [N]
    exact primeProductLE_bound hzpos
  have hzleN : z ≤ N := le_trans (Nat.le_self_pow (by norm_num only : 3 ≠ 0) z) hNlower
  have hNleN5 : N ≤ N ^ 5 := Nat.le_self_pow (by norm_num only : 5 ≠ 0) N
  have hbasecut : max C (W.sup id) ≤ N ^ 5 :=
    le_trans hmaxBase (le_trans hbaseToSeed (le_trans hmlez (le_trans hzleN hNleN5)))
  have hlarge : x₀ ≤ mBase := le_trans (le_max_right xSeed x₀) hxBase
  have hs : 0 < z * m := Nat.mul_pos hzpos (Nat.lt_of_lt_of_le (by norm_num only) hm10)
  have hExponentPos : 0 < 5 * (z * m) := Nat.mul_pos (by norm_num only) hs
  have hqle : N ^ 5 ≤ (N ^ 5) ^ (5 * (z * m)) := Nat.le_self_pow (Nat.ne_of_gt hExponentPos) (N ^ 5)
  have hLargeEnough : x₀ ≤ (N ^ 5) ^ (5 * (z * m)) :=
    le_trans hlarge (le_trans hbaseToSeed (le_trans hmlez (le_trans hzleN (le_trans hNleN5 hqle))))
  have hratio :=
    p2_seed_output_ratio_ge_of_linear_threshold hc₀ (Nat.le_trans (by norm_num only : 1 ≤ 10) hm10)
      hcubeSeed hlinearSeed hseedRatio
  have hscaleP2 : 4 * (z * m) ≤ T + 1 := by simpa only [Nat.mul_assoc] using hscale
  have hSpos : 0 < S.card := by
    rw [hScard]; exact Nat.succ_pos T
  have hSthreshold1024 : primeTailCountThreshold1024 ≤ S.card := by
    rw [hScard]
    exact le_trans hT1024 (Nat.le_succ T)
  have hprimeCount1024 := primeCounting_bound_of_primeTailCountThreshold1024 hSthreshold1024
  have hSprime : ∀ p ∈ S, Nat.Prime p := fun p hp => (hS p hp).1
  have hSseed : ∀ p ∈ S, ∃ d, d ∣ N ∧ p = d * k + 1 := by
    intro p hp
    rcases (hS p hp).2.2 with ⟨d, hdN, _, hpeq⟩
    exact ⟨d, by simpa only [N] using hdN, hpeq⟩
  let L1024 := (S.filter (fun p => 1024 * S.card < p)).prod id
  have hStrongSeedData :=
    seed_prime_tail_auxiliary_modulus_data_of_cutoff S k N 1024 (by norm_num only) hSprime hSseed
      hSpos hprimeCount1024
  have hL1024 : L1024 = (S.filter (fun p => 1024 * S.card < p)).prod id := rfl
  have hzge2 : 2 ≤ z := le_trans (by norm_num only : 2 ≤ 10) (le_trans hm10 hmlez)
  have hNge2 : 2 ≤ N :=
    le_trans hzge2 (le_trans (Nat.le_self_pow (by norm_num only : 3 ≠ 0) z) hNlower)
  have hNfiveLower : z ^ 15 ≤ N ^ 5 := by
    have hpowEq : z ^ 15 = (z ^ 3) ^ 5 := by
      calc
        z ^ 15 = z ^ (3 * 5) := by norm_num only
        _ = (z ^ 3) ^ 5 := by rw [pow_mul]
    calc
      z ^ 15 = (z ^ 3) ^ 5 := hpowEq
      _ ≤ N ^ 5 := Nat.pow_le_pow_left hNlower 5
  have hTpowX : (T + 1) ^ 4 ≤ N ^ 5 := le_trans hTpow hNfiveLower
  rcases hStrongSeedData with ⟨hSqStrong, hpfStrong, hrecipStrong, hlambdaDivStrong, hcardStrong⟩
  have hStrongArithmetic :=
    seed_auxiliary_modulus_arithmetic_bounds_of_cutoff_of_N_le_x 1024 (by norm_num only : 60 ≤ 1024)
      (le_trans hNge2 (Nat.le_self_pow (by norm_num only : 5 ≠ 0) N)) (primeProductLE_pos z) hNleN5
      hk hkpow hScard hTpowX hS hL1024 hSqStrong hpfStrong hrecipStrong hlambdaDivStrong
      hprimeCount1024
  rcases hStrongArithmetic with
    ⟨_, _, hfactorStrong, hLStrong, hlambdaStrong, hProp15Strong, hLboundStrong, hLambdaBoundStrong⟩
  have hFactorCountStrong : (T + 1) / 2 ≤ L1024.primeFactors.card := by
    rw [hpfStrong, ← hScard]
    exact Nat.div_le_of_le_mul hcardStrong
  have hrecipStrongL : (∑ r ∈ L1024.primeFactors, (r : ℝ)⁻¹) ≤ (1 / 1024 : ℝ) := by
    have hdivEq : ((1024 : ℕ) : ℝ)⁻¹ = (1 / 1024 : ℝ) := by norm_num only
    have hsumStrongFilter :
      (∑ p ∈ S.filter (fun p => 1024 * S.card < p), (p : ℝ)⁻¹) ≤ ((1024 : ℕ) : ℝ)⁻¹ := by
      simpa only [hpfStrong] using hrecipStrong
    rw [hL1024, hpfStrong]
    exact le_trans hsumStrongFilter (le_of_eq hdivEq)
  exact
    progressionAuxiliaryData_of_p2_seed_scale hc₀ hm10 hz hNlower hNupper hTupper hWSeed hcscaleSeed
      hratio hLargeEnough hrecipStrongL hLStrong hProp15Strong hbasecut hfactorStrong hlambdaStrong
      hFactorCountStrong hLboundStrong hLambdaBoundStrong hscaleP2

/--
Inputs: a positive source coefficient, a threshold, the uniform count in
reliable, Proposition 1.5, and the existence of auxiliary parameters meeting
the P2 threshold.

Claim: the initial unrestricted count, the final coprime count, and the
auxiliary data using the initial count supply `AGPProgressionCountDataExists`.

Content: choose `k` using the uniform count, pair it with the auxiliary data,
and weaken the strict source count to the non-strict bound stored by the data.

Role: this records the two applications of Proposition 1.5 in reliable, §2:
the modulus-1 count constructs the auxiliary modulus, and the modulus-4
coprime count supplies the final primes.
-/
theorem agp_progression_count_data_exists_of_uniform_count_and_auxiliary (c₀ : ℝ) (hc₀ : 0 < c₀)
    (xSeed x₀ : ℕ) (hseed : ReliableProp15UniformCount c₀ 1 1 xSeed)
    (hcount : ReliableProp15UniformCoprimeCount c₀ x₀)
    (haux : AGPProgressionAuxiliaryDataExists c₀ xSeed x₀) : AGPProgressionCountDataExists := by
  refine ⟨c₀, hc₀, x₀, hcount.1.1, ?_⟩
  intro W C hWpos
  obtain ⟨X, aux, hX, hAuxScale⟩ := haux hc₀ hseed W C hWpos
  obtain ⟨k, hk, hkpow, hcoprime, hProp15⟩ := hcount.2 aux.L aux.x aux.hLargeEnough aux.hProp15Input
  refine
    ⟨X, {
        L := aux.L
        y := reliableProp15DivisorCutoff aux.x
        q := aux.q
        x := aux.x
        k := k
        hL := aux.hL
        hSquarefree := aux.hProp15Input.1
        hLargeEnough := aux.hLargeEnough
        hProp15Input :=
          ⟨aux.hProp15Input.1, aux.hProp15Input.2.1, aux.hProp15Input.2.2.1, aux.hProp15Input.2.2.2,
            rfl, hkpow⟩
        hCq := aux.hCq
        hfactor := aux.hfactor
        hlambda := aux.hlambda
        hk := hk
        hcoprime := hcoprime
        hlower := aux.hlower
        hProp15 := le_of_lt hProp15 }, hX, hAuxScale.1, ?_⟩
  change aux.q ≤ X
  exact hAuxScale.2

/--
Inputs: the initial modulus-one uniform count and the final modulus-four coprime count.

Claim: these two analytic count hypotheses imply `AGPProgressionCountDataExists`.

Content: construct the P2 auxiliary data from the initial count, then apply both
Proposition 1.5 counts through `agp_progression_count_data_exists_of_uniform_count_and_auxiliary`.

Role: this is the direct interface from the analytic count hypotheses to the finite
progression-count data used by the prime-supply construction.
-/
theorem agp_progression_count_data_exists_of_uniform_counts (c₀ : ℝ) (hc₀ : 0 < c₀) (xSeed x₀ : ℕ)
    (hseed : ReliableProp15UniformCount c₀ 1 1 xSeed)
    (hcount : ReliableProp15UniformCoprimeCount c₀ x₀) : AGPProgressionCountDataExists :=
  agp_progression_count_data_exists_of_uniform_count_and_auxiliary c₀ hc₀ xSeed x₀ hseed hcount
    (agp_progression_auxiliary_data_exists_of_uniform_count c₀ xSeed x₀)

/--
Inputs: uniform modulus-one and modulus-four counts at coefficient `c₂`, and
a positive smaller coefficient `c₁ ≤ c₂`.

Claim: the smaller coefficient still supplies
`AGPProgressionCountDataExists`.

Proof: lower both uniform count hypotheses with their monotonicity theorems,
then apply the existing construction at `c₁`.

Role: this lets the count-data construction use a coefficient small enough to
absorb the exceptional-modulus loss.
-/
theorem agp_progression_count_data_exists_of_uniform_counts_at_smaller_coefficient (c₁ c₂ : ℝ)
    (hc₁ : 0 < c₁) (hc : c₁ ≤ c₂) (xSeed x₀ : ℕ) (hseed : ReliableProp15UniformCount c₂ 1 1 xSeed)
    (hcount : ReliableProp15UniformCoprimeCount c₂ x₀) : AGPProgressionCountDataExists := by
  exact
    agp_progression_count_data_exists_of_uniform_counts c₁ hc₁ xSeed x₀
      (reliableProp15UniformCount_mono hc hseed) (reliableProp15UniformCoprimeCount_mono hc hcount)

/--
Inputs: a positive Proposition 1.5 coefficient, a positive finite-average
coefficient, an exceptional-set size, and both uniform count hypotheses.

Claim: there is a positive smaller coefficient satisfying the exceptional-loss
margin, and that coefficient supplies `AGPProgressionCountDataExists`.

Proof: choose the minimum of the source coefficient and `β / (32 * 2^D)`.
Coefficient monotonicity transfers both count hypotheses to this choice, and
the definition of the minimum gives the strict margin.

Role: this completes the finite coefficient-selection step before applying
the fifth-power exceptional-loss construction.
-/
theorem agp_progression_count_data_exists_with_loss_margin (c₂ beta : ℝ) (D : ℕ) (hc₂ : 0 < c₂)
    (hbeta : 0 < beta) (xSeed x₀ : ℕ) (hseed : ReliableProp15UniformCount c₂ 1 1 xSeed)
    (hcount : ReliableProp15UniformCoprimeCount c₂ x₀) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧ 16 * (2 ^ D : ℝ) * c₁ < beta ∧ AGPProgressionCountDataExists := by
  have hA : 0 < (2 ^ D : ℝ) := by exact_mod_cast Nat.pow_pos (by norm_num only : 0 < 2)
  let c₁ : ℝ := min c₂ (beta / (32 * (2 ^ D : ℝ)))
  have hc₁ : 0 < c₁ := by
    dsimp [c₁]
    exact lt_min hc₂ (div_pos hbeta (mul_pos (by norm_num only : (0 : ℝ) < 32) hA))
  have hc₁le : c₁ ≤ c₂ := by
    dsimp [c₁]
    exact min_le_left _ _
  have hscaled : 16 * (2 ^ D : ℝ) * c₁ ≤ beta / 2 := by
    dsimp [c₁]
    calc
      16 * (2 ^ D : ℝ) * min c₂ (beta / (32 * (2 ^ D : ℝ))) ≤
          16 * (2 ^ D : ℝ) * (beta / (32 * (2 ^ D : ℝ))) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _)
          (le_of_lt (mul_pos (by norm_num only : (0 : ℝ) < 16) hA))
      _ = beta / 2 := by
        field_simp [ne_of_gt hA]
        norm_num only
  have hhalf : beta / 2 < beta := by nlinarith only [hbeta]
  refine ⟨c₁, hc₁, hc₁le, lt_of_le_of_lt hscaled hhalf, ?_⟩
  exact
    agp_progression_count_data_exists_of_uniform_counts_at_smaller_coefficient c₁ c₂ hc₁ hc₁le xSeed
      x₀ hseed hcount

end PseudoPrime.AnalyticNumberTheory.AGP
