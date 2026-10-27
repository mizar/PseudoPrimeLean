/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.AGP.P2SeedScale
public import PseudoPrime.AnalyticNumberTheory.AGP.PrimorialSeedCount

/-! # P2 primorial seed bridge -/

set_option maxRecDepth 4096

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.AGP

/--
Inputs: a P2 scale lower bound, a primorial count margin, and a fixed-scale theta supply.

Claim: one P2 scale yields the cutoff, source-count margin, and tail-prime data for the
primorial seed construction.

Proof: choose the P2 exponent above the exceptional-count, theta, finite-base, and modulus
cutoffs; convert the scale output into the primorial hypotheses and apply the tail constructor.

Role: connects the P2 concentration scale to the first-stage primorial seed modulus.
-/
theorem exists_primorial_seed_tail_of_p2_scale {c₀ : ℝ} {J : ℕ} (hc₀ : 0 < c₀) (hJ : 2 ≤ J)
    (W : Finset ℕ) (C D X₀ : ℕ) (hfactor : c₀ * (2 : ℝ) ^ D ≤ 1 / 128)
    (hSupply :
      ∀ Z : ℕ,
        X₀ ≤ Z →
          ∃ E : Finset ℕ,
            E.card ≤ D ∧
              (∀ e ∈ E, 1 < e ∧ ¬e ∣ 4) ∧
              ∀ m d a : ℕ,
                (m = 1 ∨ m = 4) →
                  0 < d →
                  Nat.Coprime d m →
                  1 < d * m →
                  (d * m) ^ J ≤ Z →
                  Nat.Coprime a (d * m) →
                  (∀ e ∈ E, ¬e ∣ d * m) →
                  (((d * Z ^ 3 : ℕ) : ℝ) / (2 * (Nat.totient (d * m) : ℝ))) ≤
                    thetaInProgressionReal ((d * Z ^ 3 : ℕ) : ℝ) (d * m) a) :
    ∃ u X T,
      10 ≤ u ∧
        X = ((PseudoPrime.NumberTheory.PrimeProducts.primeSetLE (2 ^ u)).prod id) ^ J ∧
        X₀ ≤ X ∧
        18000000 ^ 2 ≤ X ∧
        max C (W.sup id) ≤ X ^ 5 ∧
        10 * (J : ℝ) * (((T + 1 : ℕ) : ℝ) + 3) * Real.log ((X ^ 5 : ℕ) : ℝ) *
            ((2 : ℝ) ^ W.card * ((X ^ 5 : ℕ) : ℝ) ^ 2 * ((T + 1 : ℕ) : ℝ) *
                Real.log ((X ^ 5 : ℕ) : ℝ) +
              ((X ^ 5 : ℕ) : ℝ)) <
          c₀ * (2 : ℝ) ^ Nat.floor (((T + 1 : ℕ) : ℝ) / 2) ∧
        T + 1 ≤ (2 ^ u) ^ 3 ∧
        2 * Nat.primeCounting (1024 * (T + 1)) ≤ T + 1 ∧
        ∃ E : Finset ℕ,
          E.card ≤ D ∧
            ∃ k,
              k ∈ positiveCoprimeParameters 1 (X ^ 3) ∧
                ∃ (S : Finset ℕ) (L : ℕ),
                  S.card = T + 1 ∧
                    (∀ p ∈ S,
                      Nat.Prime p ∧
                        p ≤ X ^ 5 ∧
                        ∃ d,
                          d ∣ (PseudoPrime.NumberTheory.PrimeProducts.primeSetLE (2 ^ u)).prod id ∧
                            p = d * k + 1) ∧
                    L = (S.filter (fun p ↦ 1024 * S.card < p)).prod id ∧
                    Squarefree L ∧
                    L.primeFactors = S.filter (fun p ↦ 1024 * S.card < p) ∧
                    (∑ p ∈ (L.primeFactors : Finset ℕ), (p : ℝ)⁻¹) ≤ (1 / 1024 : ℝ) ∧
                    ArithmeticFunction.carmichael L ∣
                      k * (PseudoPrime.NumberTheory.PrimeProducts.primeSetLE (2 ^ u)).prod id ∧
                    S.card ≤ 2 * (S.filter (fun p ↦ 1024 * S.card < p)).card ∧
                    L ≤ (X ^ 5) ^ (T + 1) ∧
                    (∀ r, r ∣ L → Nat.Prime r → r ≤ X ^ 5) ∧
                    ArithmeticFunction.carmichael L ≤ (X ^ 5) ^ 2 ∧
                    2 < L ∧ 3 ≤ ArithmeticFunction.carmichael L := by
  let q₀ := max (D + 1) (max X₀ (max C (max (W.sup id) (18000000 ^ 2))))
  obtain ⟨u, q, t, hu10, hq₀, hq₀u, hq, ht, hthreshold, htail, hseed, hmargin, hbox⟩ :=
    exists_p2_full_divisor_concentration_bound_above_with_seed_margin (J := J) (w := W.card) hc₀
      (lt_of_lt_of_le (by norm_num only : 0 < 2) hJ) q₀
  let N := (PseudoPrime.NumberTheory.PrimeProducts.primeSetLE (2 ^ u)).prod id
  let X := N ^ J
  let T := Nat.floor (c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2))
  have hpi := primeCounting_two_pow_lower hu10
  have hNlower : 2 ^ (3 * u) ≤ N :=
    calc
      2 ^ (3 * u) ≤ 2 ^ Nat.primeCounting (2 ^ u) :=
        Nat.pow_le_pow_right (Nat.le_of_lt Nat.one_lt_two) hpi
      _ ≤ N := PseudoPrime.AnalyticNumberTheory.AGP.primeProductLE_ge_two_pow_primeCounting _
  have hcube := powTwo_ge_cube hu10
  have huCube : u ≤ u ^ 3 := Nat.le_self_pow (Nat.succ_ne_zero 2) u
  have huTwo : u ≤ 2 ^ u := le_trans huCube hcube
  have huThree : u ≤ 3 * u := by
    calc
      u ≤ u * 3 := Nat.le_mul_of_pos_right u (Nat.succ_pos 2)
      _ = 3 * u := Nat.mul_comm u 3
  have hpow : 2 ^ u ≤ 2 ^ (3 * u) := Nat.pow_le_pow_right (Nat.le_of_lt Nat.one_lt_two) huThree
  have huN : u ≤ N := le_trans huTwo (le_trans hpow hNlower)
  have hq₀rest₁ : max X₀ (max C (max (W.sup id) (18000000 ^ 2))) ≤ u :=
    le_trans (le_max_right _ _) hq₀u
  have hq₀rest₂ : max C (max (W.sup id) (18000000 ^ 2)) ≤ u := le_trans (le_max_right _ _) hq₀rest₁
  have hq₀rest₃ : max (W.sup id) (18000000 ^ 2) ≤ u := le_trans (le_max_right _ _) hq₀rest₂
  have hDplus : D + 1 ≤ u := le_trans (le_max_left _ _) hq₀u
  have hX₀u : X₀ ≤ u := le_trans (le_max_left _ _) hq₀rest₁
  have hCu : C ≤ u := le_trans (le_max_left _ _) hq₀rest₂
  have hWsupU : W.sup id ≤ u := le_trans (le_max_left _ _) hq₀rest₃
  have hCWu : max C (W.sup id) ≤ u := max_le hCu hWsupU
  have hHugeu : 18000000 ^ 2 ≤ u := le_trans (le_max_right _ _) hq₀rest₃
  have hD : D < Nat.primeCounting (2 ^ u) :=
    Nat.lt_of_lt_of_le (Nat.lt_of_succ_le hDplus) (le_trans huThree hpi)
  have hNX : N ≤ X := Nat.le_self_pow (Nat.ne_of_gt (lt_of_lt_of_le (Nat.zero_lt_succ 1) hJ)) N
  have hHuge : 18000000 ^ 2 ≤ X := le_trans hHugeu (le_trans huN hNX)
  have hX₀ : X₀ ≤ X := le_trans hX₀u (le_trans huN hNX)
  have hNJ : N ^ J ≤ X := le_rfl
  have hXpow : X ≤ X ^ 5 := Nat.le_self_pow (Nat.succ_ne_zero 4) X
  have hCW : max C (W.sup id) ≤ X ^ 5 := le_trans hCWu (le_trans huN (le_trans hNX hXpow))
  have hqX : q = X ^ 5 :=
    calc
      q = (N ^ 5) ^ J := hq
      _ = (N ^ J) ^ 5 := by
        calc
          (N ^ 5) ^ J = N ^ (5 * J) := (Nat.pow_mul N 5 J).symm
          _ = N ^ (J * 5) := congrArg (fun e : ℕ ↦ N ^ e) (Nat.mul_comm 5 J)
          _ = (N ^ J) ^ 5 := Nat.pow_mul N J 5
      _ = X ^ 5 := rfl
  have htT : t = T + 1 := by simpa only [T] using ht
  have hseedMargin :
    (T : ℝ) <
      reliableProp15Coefficient c₀ 1 (X ^ 5) * ((2 ^ Nat.primeCounting (2 ^ u) : ℕ) : ℝ) := by
    simpa only [T, hqX] using hseed
  have h1024 : 2 * Nat.primeCounting (1024 * (T + 1)) ≤ T + 1 := by simpa only [htT] using htail
  have hpowD : (1 : ℝ) ≤ (2 : ℝ) ^ D := by
    exact_mod_cast Nat.one_le_pow D 2 (by norm_num only : 0 < 2)
  have hc₀small : c₀ ≤ 1 / 128 := by
    calc
      c₀ = c₀ * 1 := by ring
      _ ≤ c₀ * (2 : ℝ) ^ D := mul_le_mul_of_nonneg_left hpowD hc₀.le
      _ ≤ 1 / 128 := hfactor
  have huR : (10 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu10
  have hlog2 : (69 / 100 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hu4 : (1 : ℝ) ≤ (u : ℝ) ^ 4 := one_le_pow₀ (le_trans (by norm_num only : (1 : ℝ) ≤ 10) huR)
  have hlogu : (69 / 100 : ℝ) ≤ Real.log 2 * (u : ℝ) ^ 4 :=
    calc
      69 / 100 = (69 / 100) * 1 := by ring
      _ ≤ Real.log 2 * 1 := mul_le_mul_of_nonneg_right hlog2 (by norm_num only)
      _ ≤ Real.log 2 * (u : ℝ) ^ 4 :=
        mul_le_mul_of_nonneg_left hu4 (le_of_lt (Real.log_pos (by norm_num only)))
  have hparam : c₀ < 20 * Real.log 2 * (u : ℝ) ^ 4 := by
    exact lt_of_le_of_lt hc₀small (by nlinarith only [hlogu])
  have hJpos : 0 < J := lt_of_lt_of_le (by norm_num only : 0 < 2) hJ
  have huOne : 1 ≤ u := le_trans (by norm_num only : 1 ≤ 10) hu10
  have hTcube :=
    p2_full_divisor_seed_count_succ_le_cube (c₀ := c₀) (J := J) (u := u) (z := 2 ^ u) (T := T) hc₀
      hJpos huOne rfl (powTwo_ge_cube hu10) hparam (by simp only [T, Nat.cast_pow, Nat.cast_ofNat])
  refine ⟨u, X, T, hu10, ?_, hX₀, hHuge, hCW, ?_, hTcube, h1024, ?_⟩
  · rfl
  · simpa only [T, hqX, htT, Nat.cast_add, Nat.cast_one] using hbox
  · exact
      exists_primorial_seed_tail_modulus_of_count_margin (2 ^ u) J D X₀ X T c₀ hJ hD hfactor
        hseedMargin hHuge hX₀ hNJ hSupply h1024

/--
Inputs: a P2 scale and its primorial seed-tail construction under fixed-scale theta supply.

Claim: these data yield `AGPProgressionAuxiliaryData` at a larger full-divisor scale.

Proof: first obtain the modulus-four input and size bounds from the cutoff-1024 tail data,
then use the boxed P2 inequality in the full-divisor auxiliary constructor.

Role: connects the primorial seed stage to the progression-count interface.
-/
theorem exists_full_divisor_auxiliary_data_of_p2_primorial_tail {c₀ : ℝ} {J : ℕ} (hc₀ : 0 < c₀)
    (hJ : 2 ≤ J) (W : Finset ℕ) (C D X₀ : ℕ) (hfactor : c₀ * (2 : ℝ) ^ D ≤ 1 / 128)
    (hSupply :
      ∀ Z : ℕ,
        X₀ ≤ Z →
          ∃ E : Finset ℕ,
            E.card ≤ D ∧
              (∀ e ∈ E, 1 < e ∧ ¬e ∣ 4) ∧
              ∀ m d a : ℕ,
                (m = 1 ∨ m = 4) →
                  0 < d →
                  Nat.Coprime d m →
                  1 < d * m →
                  (d * m) ^ J ≤ Z →
                  Nat.Coprime a (d * m) →
                  (∀ e ∈ E, ¬e ∣ d * m) →
                  (((d * Z ^ 3 : ℕ) : ℝ) / (2 * (Nat.totient (d * m) : ℝ))) ≤
                    thetaInProgressionReal ((d * Z ^ 3 : ℕ) : ℝ) (d * m) a) :
    ∃ Y : ℕ,
      ∃ aux : AGPProgressionAuxiliaryData W C c₀ X₀,
        2 ^ 56 ≤ Y ∧ aux.x = Y ^ 5 ∧ aux.q ≤ Y ∧ X₀ ≤ Y ∧ ∀ d, d ∣ aux.L → (4 * d) ^ J ≤ Y := by
  obtain ⟨u, X, T, hu10, hXdef, hX₀, hHuge, hCW, hbox, hTcube, h1024, htail⟩ :=
    exists_primorial_seed_tail_of_p2_scale hc₀ hJ W C D X₀ hfactor hSupply
  rcases htail with
    ⟨E, hEcard, k, hk, S, L, hScard, hS, hL, hSquarefree, hLprimeFactors, hReciprocal,
      hCarmichaelDiv, hTailCard, _hLBoundTail, _hFactorTail, _hCarmichaelUpperTail, hLlarge,
      hCarmichaelLower⟩
  let N := (PseudoPrime.NumberTheory.PrimeProducts.primeSetLE (2 ^ u)).prod id
  let q := X ^ 5
  have hJpos : 0 < J := lt_of_lt_of_le (by norm_num only : 0 < 2) hJ
  have hNpos : 0 < N := PseudoPrime.NumberTheory.PrimeProducts.primeProductLE_pos _
  have hpi := primeCounting_two_pow_lower hu10
  have hNlower : 2 ^ (3 * u) ≤ N :=
    calc
      2 ^ (3 * u) ≤ 2 ^ Nat.primeCounting (2 ^ u) :=
        Nat.pow_le_pow_right (Nat.le_of_lt Nat.one_lt_two) hpi
      _ ≤ N := PseudoPrime.AnalyticNumberTheory.AGP.primeProductLE_ge_two_pow_primeCounting _
  have hNleX : N ≤ X := by
    rw [hXdef]
    dsimp only [N]
    exact Nat.le_self_pow (Nat.ne_of_gt hJpos) _
  have hXpos : 0 < X := lt_of_lt_of_le hNpos hNleX
  have hqpos : 0 < q := Nat.pow_pos hXpos
  have hqTwo : 2 ≤ q := by
    have hNtwo : 2 ≤ N := le_trans (Nat.le_self_pow (by omega : 3 * u ≠ 0) 2) hNlower
    calc
      2 ≤ X := le_trans hNtwo hNleX
      _ ≤ X ^ 5 := Nat.le_self_pow (by norm_num only : 5 ≠ 0) X
      _ = q := rfl
  have hzCube : (2 ^ u) ^ 3 = 2 ^ (3 * u) := by
    calc
      (2 ^ u) ^ 3 = 2 ^ (u * 3) := (Nat.pow_mul 2 u 3).symm
      _ = 2 ^ (3 * u) := congrArg (fun n : ℕ ↦ 2 ^ n) (Nat.mul_comm u 3)
  have hTleX : T + 1 ≤ X := by
    calc
      T + 1 ≤ (2 ^ u) ^ 3 := hTcube
      _ = 2 ^ (3 * u) := hzCube
      _ ≤ N := hNlower
      _ ≤ X := hNleX
  have hTpower : (T + 1) ^ 4 ≤ q := by
    calc
      (T + 1) ^ 4 ≤ X ^ 4 := Nat.pow_le_pow_left hTleX 4
      _ ≤ X ^ 5 := Nat.pow_le_pow_right hXpos (by norm_num only : 4 ≤ 5)
      _ = q := rfl
  have hSArithmetic :
    ∀ p ∈ S,
      Nat.Prime p ∧ p ≤ q ∧ ∃ d, d ∣ N ∧ d ≤ reliableProp15DivisorCutoff q ∧ p = d * k + 1 := by
    intro p hp
    rcases hS p hp with ⟨hpPrime, hpBound, d, hdN, hpEq⟩
    refine ⟨hpPrime, hpBound, d, hdN, ?_, hpEq⟩
    calc
      d ≤ N := Nat.le_of_dvd hNpos hdN
      _ ≤ X := hNleX
      _ ≤ reliableProp15DivisorCutoff q := by
        rw [show q = X ^ 5 by rfl, reliableProp15DivisorCutoff_fifth_power_eq_square X hXpos]
        exact Nat.le_self_pow (by norm_num only : 2 ≠ 0) X
  have hkParts := Finset.mem_filter.mp hk
  have hkInterval := Finset.mem_Icc.mp hkParts.1
  have hkpos : 0 < k := lt_of_lt_of_le (by norm_num only : 0 < 1) hkInterval.1
  have hkpow : k ^ 5 ≤ q ^ 3 := by
    calc
      k ^ 5 ≤ (X ^ 3) ^ 5 := Nat.pow_le_pow_left hkInterval.2 5
      _ = X ^ (3 * 5) := (Nat.pow_mul X 3 5).symm
      _ = X ^ (5 * 3) := congrArg (fun n : ℕ ↦ X ^ n) (by omega)
      _ = (X ^ 5) ^ 3 := Nat.pow_mul X 5 3
      _ = q ^ 3 := rfl
  have hNleq : N ≤ q := le_trans hNleX (Nat.le_self_pow (by norm_num only : 5 ≠ 0) X)
  have h1024' : 2 * Nat.primeCounting (1024 * S.card) ≤ S.card := by simpa only [hScard] using h1024
  have hReciprocal' : (∑ p ∈ L.primeFactors, (p : ℝ)⁻¹) ≤ (1024 : ℝ)⁻¹ := by
    simpa only [one_div, Nat.cast_ofNat] using hReciprocal
  have hTailArithmetic :
    Nat.Coprime L 4 ∧
      L.primeFactors.card ^ 4 ≤ q ∧
      (∀ r, r ∣ L → Nat.Prime r → r ≤ q) ∧
      2 < L ∧
      3 ≤ ArithmeticFunction.carmichael L ∧
      ReliableProp15ModFourInput L q ∧ L ≤ q ^ (T + 1) ∧ ArithmeticFunction.carmichael L ≤ q ^ 2 :=
    @seed_auxiliary_modulus_arithmetic_bounds_of_cutoff_of_N_le_x 1024
      (by norm_num only : 60 ≤ 1024) q N T k S L hqTwo hNpos hNleq hkpos hkpow hScard hTpower
      hSArithmetic hL hSquarefree hLprimeFactors hReciprocal' hCarmichaelDiv h1024'
  rcases hTailArithmetic with
    ⟨_hCoprimeFour, _hFactorCount, hFactorBound, hLlarge', hCarmichaelLower', hProp15Input, hLBound,
      hCarmichaelUpper⟩
  let Y := (4 * q * L) ^ J
  have hYbounds :=
    fullDivisorScale_arithmetic_bounds q L J hqpos (lt_trans (by norm_num only : 0 < 2) hLlarge')
      hJpos
  have hYlarge : X₀ ≤ Y ^ 5 := by
    calc
      X₀ ≤ X := hX₀
      _ ≤ q := by
        dsimp only [q]; exact Nat.le_self_pow (by norm_num only : 5 ≠ 0) X
      _ ≤ Y := hYbounds.1
      _ ≤ Y ^ 5 := Nat.le_self_pow (by norm_num only : 5 ≠ 0) Y
  have hqleY5 : q ≤ Y ^ 5 := le_trans hYbounds.1 (Nat.le_self_pow (by norm_num only : 5 ≠ 0) Y)
  have hqLarge : 2 ^ 56 ≤ q := by
    calc
      2 ^ 56 ≤ (18000000 ^ 2) ^ 5 := by norm_num only
      _ ≤ X ^ 5 := Nat.pow_le_pow_left hHuge 5
      _ = q := rfl
  have hScaleLower : 2 ^ 56 ≤ Y := le_trans hqLarge hYbounds.1
  have hProp15InputY : ReliableProp15ModFourInput L (Y ^ 5) :=
    reliableProp15ModFourInput_mono hProp15Input hqleY5
  let aux : AGPProgressionAuxiliaryData W C c₀ X₀ :=
    progressionAuxiliaryData_of_full_divisor_seed_with_cutoff (R := 1024) hc₀ hqTwo hLlarge'
      (Nat.succ_pos T) hJpos rfl hYlarge hProp15InputY hReciprocal hCW hFactorBound
      hCarmichaelLower' hScard hLprimeFactors hTailCard hLBound hCarmichaelUpper hbox
  refine ⟨Y, aux, hScaleLower, ?_, ?_, ?_, ?_⟩
  · dsimp only [aux, progressionAuxiliaryData_of_full_divisor_seed_with_cutoff]
  · dsimp only [aux, progressionAuxiliaryData_of_full_divisor_seed_with_cutoff]
    exact hYbounds.1
  · calc
      X₀ ≤ X := hX₀
      _ ≤ q := by
        dsimp only [q]; exact Nat.le_self_pow (by norm_num only : 5 ≠ 0) X
      _ ≤ Y := hYbounds.1
  · intro d hd
    dsimp only [aux, progressionAuxiliaryData_of_full_divisor_seed_with_cutoff] at hd ⊢
    exact hYbounds.2.2 d hd

end PseudoPrime.AnalyticNumberTheory.AGP
