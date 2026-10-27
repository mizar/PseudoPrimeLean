/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.AGP.TruncatedSelbergPrimorial

/-! # Coarse progression prime bounds from the finite Selberg sieve -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.AGP

/--
Inputs: a real sieve scale `M ≥ 256`.

Claim: the eighth-root cutoff `z = ⌊M^(1/8)⌋` is positive, lies below the
eighth root, has logarithm at least `log M / 8` after adding one, and satisfies
`z⁴ ≤ M^(1/2)`.

Proof: use the defining floor inequalities, monotonicity of real powers and
logarithms, and the identity `(M^(1/8))⁴ = M^(1/2)`.

Role: supplies the cutoff estimates used to absorb the small-prime count and
the quadratic Selberg remainder.
-/
theorem coarseCutoffBounds {M : ℝ} (hM : 256 ≤ M) :
    let z : ℕ := Nat.floor (Real.rpow M (1 / 8 : ℝ))
    1 ≤ z ∧
      (z : ℝ) ≤ Real.rpow M (1 / 8 : ℝ) ∧
      Real.log M / 8 ≤ Real.log ((z + 1 : ℕ) : ℝ) ∧
      (z : ℝ) ≤ Real.rpow M (1 / 2 : ℝ) ∧ (z : ℝ) ^ 4 ≤ Real.rpow M (1 / 2 : ℝ) := by
  dsimp only
  let z : ℕ := Nat.floor (Real.rpow M (1 / 8 : ℝ))
  have hMpos : 0 < M := by linarith only [hM]
  have hMge1 : (1 : ℝ) ≤ M := le_trans (by norm_num only) hM
  have hrootge1 : (1 : ℝ) ≤ Real.rpow M (1 / 8 : ℝ) := by
    have h :=
      Real.rpow_le_rpow (by norm_num only : (0 : ℝ) ≤ 1) hMge1
        (by norm_num only : (0 : ℝ) ≤ (1 / 8 : ℝ))
    norm_num only at h
    exact h
  refine ⟨Nat.le_floor (by exact_mod_cast hrootge1), ?_, ?_, ?_, ?_⟩
  · exact Nat.floor_le (Real.rpow_nonneg hMpos.le _)
  · have hrootlt : Real.rpow M (1 / 8 : ℝ) < ((z + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.lt_floor_add_one (Real.rpow M (1 / 8 : ℝ))
    have hloglt := Real.log_lt_log (Real.rpow_pos_of_pos hMpos _) hrootlt
    rw [Real.log_rpow hMpos] at hloglt
    linarith only [hloglt]
  · calc
      (z : ℝ) ≤ Real.rpow M (1 / 8 : ℝ) := Nat.floor_le (Real.rpow_nonneg hMpos.le _)
      _ ≤ Real.rpow M (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hMge1 (by norm_num only)
  · have hroot4 : (Real.rpow M (1 / 8 : ℝ)) ^ 4 = Real.rpow M (1 / 2 : ℝ) := by
      calc
        _ = Real.rpow M ((1 / 8 : ℝ) * 4) := (Real.rpow_mul_natCast hMpos.le (1 / 8 : ℝ) 4).symm
        _ = Real.rpow M (1 / 2 : ℝ) := by
          congr 1; norm_num only
    have hzle : (z : ℝ) ≤ Real.rpow M (1 / 8 : ℝ) := Nat.floor_le (Real.rpow_nonneg hMpos.le _)
    have hz2 : (z : ℝ) ^ 2 ≤ (Real.rpow M (1 / 8 : ℝ)) ^ 2 :=
      (sq_le_sq₀ (Nat.cast_nonneg z) (Real.rpow_nonneg hMpos.le _)).2 hzle
    have hz4 : ((z : ℝ) ^ 2) ^ 2 ≤ ((Real.rpow M (1 / 8 : ℝ)) ^ 2) ^ 2 :=
      (sq_le_sq₀ (sq_nonneg (z : ℝ)) (sq_nonneg (Real.rpow M (1 / 8 : ℝ)))).2 hz2
    calc
      (z : ℝ) ^ 4 = ((z : ℝ) ^ 2) ^ 2 := by ring
      _ ≤ ((Real.rpow M (1 / 8 : ℝ)) ^ 2) ^ 2 := hz4
      _ = (Real.rpow M (1 / 8 : ℝ)) ^ 4 := by ring
      _ = Real.rpow M (1 / 2 : ℝ) := hroot4

/--
Inputs: a real scale `M ≥ 256`.

Claim: the sum of the square root scale with its logarithm is absorbed by
`8 M / log M`.

Proof: write `u = √M` and `t = √u`. Then `t ≥ 4`, `log M = 4 log t`, and
`log t ≤ t - 1 ≤ t² / 3`.

Role: absorbs the small-prime count and the quadratic sieve remainder.
-/
theorem coarseSqrtLogAbsorption {M : ℝ} (hM : 256 ≤ M) : 6 * Real.sqrt M ≤ 8 * M / Real.log M := by
  have hMpos : 0 < M := by linarith only [hM]
  have hlogpos : 0 < Real.log M := Real.log_pos (by linarith only [hM])
  let u : ℝ := Real.sqrt M
  let t : ℝ := Real.sqrt u
  have hu16 : 16 ≤ u := by
    dsimp only [u]
    apply (Real.le_sqrt (by norm_num only : (0 : ℝ) ≤ 16) (by linarith only [hM])).2
    nlinarith only [hM]
  have ht4 : 4 ≤ t := by
    dsimp only [t]
    apply (Real.le_sqrt (by norm_num only : (0 : ℝ) ≤ 4) (by linarith only [hu16])).2
    nlinarith only [hu16]
  have huSq : u ^ 2 = M := by
    dsimp only [u]
    exact Real.sq_sqrt hMpos.le
  have htSq : t ^ 2 = u := by
    dsimp only [t]
    exact Real.sq_sqrt (by linarith only [hu16])
  have hlogM : Real.log M = 4 * Real.log t := by
    rw [← huSq, Real.log_pow, ← htSq, Real.log_pow]
    ring
  have hlogt := Real.log_le_sub_one_of_pos (by linarith only [ht4])
  apply (le_div_iff₀ hlogpos).2
  rw [show Real.sqrt M = u by rfl, hlogM, ← huSq]
  have hlogbound : 3 * Real.log t ≤ t ^ 2 := by nlinarith only [ht4, hlogt]
  rw [← htSq]
  have hmul :=
    mul_le_mul_of_nonneg_left hlogbound (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 8) (sq_nonneg t))
  nlinarith only [hmul]

/--
Inputs: a natural cutoff `z` bounded by `√M`, with `z ≥ 1` and `z⁴ ≤ √M`.

Claim: primes through `z` plus the quadratic Selberg remainder contribute at
most `6√M`.

Proof: bound the filtered prime count by the size of `range (z + 1)`, use
`z + 1 ≤ 2z`, and square the bound `z(z + 1) ≤ 2z²`.

Role: isolates the elementary error terms in the coarse progression bound.
-/
theorem coarseCutoffErrorBound {M : ℝ} {z : ℕ} (hz : 1 ≤ z) (hzSqrt : (z : ℝ) ≤ Real.sqrt M)
    (hzFourth : (z : ℝ) ^ 4 ≤ Real.sqrt M) :
    ((Finset.range (z + 1)).filter Nat.Prime).card + ((z : ℝ) * (z + 1 : ℕ)) ^ 2 ≤
      6 * Real.sqrt M := by
  have hzAddNat : z + 1 ≤ 2 * z := by
    calc
      z + 1 ≤ z + z := Nat.add_le_add_left hz z
      _ = 2 * z := (two_mul z).symm
  have hzAdd : ((z + 1 : ℕ) : ℝ) ≤ 2 * (z : ℝ) := by exact_mod_cast hzAddNat
  have hzCast : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hPrimeCount : ((Finset.range (z + 1)).filter Nat.Prime).card ≤ 2 * (z : ℝ) := by
    have hcard := Finset.card_filter_le (Finset.range (z + 1)) Nat.Prime
    have hcardR :
      ((Finset.filter Nat.Prime (Finset.range (z + 1))).card : ℝ) ≤
        ((Finset.range (z + 1)).card : ℝ) := by
      exact_mod_cast hcard
    rw [Finset.card_range] at hcardR
    push_cast at hcardR
    exact le_trans hcardR (by linarith only [hzAdd, hzCast])
  have hPrimeCount' : ((Finset.range (z + 1)).filter Nat.Prime).card ≤ 2 * Real.sqrt M :=
    le_trans hPrimeCount (mul_le_mul_of_nonneg_left hzSqrt (by norm_num only : (0 : ℝ) ≤ 2))
  have hprod : (z : ℝ) * (z + 1 : ℕ) ≤ 2 * (z : ℝ) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hzAdd (Nat.cast_nonneg z)
    convert h using 1
    ring
  have hprodNonneg : 0 ≤ (z : ℝ) * (z + 1 : ℕ) :=
    mul_nonneg (Nat.cast_nonneg z) (Nat.cast_nonneg (z + 1))
  have hrightNonneg : 0 ≤ 2 * (z : ℝ) ^ 2 := mul_nonneg (by norm_num only) (sq_nonneg (z : ℝ))
  have hprodSq : ((z : ℝ) * (z + 1 : ℕ)) ^ 2 ≤ (2 * (z : ℝ) ^ 2) ^ 2 :=
    (sq_le_sq₀ hprodNonneg hrightNonneg).2 hprod
  have herror : ((z : ℝ) * (z + 1 : ℕ)) ^ 2 ≤ 4 * Real.sqrt M := by
    calc
      ((z : ℝ) * (z + 1 : ℕ)) ^ 2 ≤ (2 * (z : ℝ) ^ 2) ^ 2 := hprodSq
      _ = 4 * ((z : ℝ) ^ 4) := by ring
      _ ≤ 4 * Real.sqrt M := mul_le_mul_of_nonneg_left hzFourth (by norm_num only : (0 : ℝ) ≤ 4)
  linarith only [hPrimeCount', herror]

/--
Inputs: a positive modulus `Q`, a sieve modulus coprime to `Q`, and a
squarefree sieve modulus.

Claim: the total mass in the progression sieve through `Y` is at most
`Y / Q + 2`.

Proof: use the exact quotient and incomplete-block formula, then bound the
natural quotient by its real quotient and the final block by one.

Role: bounds the mass multiplying the reciprocal Selberg normalizer.
-/
theorem coarseProgressionSieveMassBound {Y Q a P : ℕ} (hP : Squarefree P) (hQ : 0 < Q) :
    (progressionBoundingSieve Y Q a P hP).totalMass ≤ (Y : ℝ) / (Q : ℝ) + 2 := by
  have hQpos : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hQge1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr hQ)
  have hQinv : 1 / (Q : ℝ) ≤ 1 := (div_le_one hQpos).2 hQge1
  have hcount : (Y + 1) / Q + (if a % Q < (Y + 1) % Q then 1 else 0) ≤ (Y + 1) / Q + 1 := by
    by_cases h : a % Q < (Y + 1) % Q
    · rw [ite_eq_left h]
    · rw [ite_eq_right h]
      exact Nat.le_add_right _ _
  have hdiv : ((Y + 1 : ℕ) : ℝ) / (Q : ℝ) = (Y : ℝ) / (Q : ℝ) + 1 / (Q : ℝ) := by
    push_cast
    ring
  rw [progressionBoundingSieve_totalMass_eq hP hQ]
  calc
    (((Y + 1) / Q + if a % Q < (Y + 1) % Q then 1 else 0 : ℕ) : ℝ) ≤ (((Y + 1) / Q + 1 : ℕ) : ℝ) :=
      by exact_mod_cast hcount
    _ = (((Y + 1) / Q : ℕ) : ℝ) + 1 := by
      push_cast; norm_num only
    _ ≤ ((Y + 1 : ℕ) : ℝ) / (Q : ℝ) + 1 := by
      exact add_le_add_left (Nat.cast_div_le (α := ℝ) (m := Y + 1) (n := Q)) 1
    _ = (Y : ℝ) / (Q : ℝ) + 1 / (Q : ℝ) + 1 := by rw [hdiv]
    _ ≤ (Y : ℝ) / (Q : ℝ) + 2 := by linarith only [hQinv]

/--
Inputs: a positive modulus `Q` and a scale ratio `Y / Q ≥ 256`.

Claim: the number of primes at most `Y` in any residue class modulo `Q` is
at most `32 Y / (φ(Q) log(Y / Q))`.

Proof: apply the explicit finite Selberg sieve with cutoff
`⌊(Y/Q)^(1/8)⌋`. Bound its total mass by the residue-class count, use the
coprime-primorial normalizer lower bound, and absorb the small primes and
quadratic remainder into the remaining coefficient.

Role: supplies an unconditional coarse progression estimate for the AGP
prime-supply argument without assuming Brun–Titchmarsh.
-/
theorem primeCountInProgression_le_thirty_two {Y Q a : ℕ} (hQ : 0 < Q)
    (hscale : (256 : ℝ) ≤ (Y : ℝ) / (Q : ℝ)) :
    (primeCountInProgression Y Q a : ℝ) ≤
      32 * (Y : ℝ) / ((Nat.totient Q : ℝ) * Real.log ((Y : ℝ) / (Q : ℝ))) := by
  let M : ℝ := (Y : ℝ) / (Q : ℝ)
  let z : ℕ := Nat.floor (Real.rpow M (1 / 8 : ℝ))
  let P : ℕ := (PseudoPrime.NumberTheory.PrimeProducts.primeSetLECoprime z Q).prod id
  let G : ℝ := selbergTruncatedTotientSum P z
  have hM : (256 : ℝ) ≤ M := by simpa only [M] using hscale
  have hcut := coarseCutoffBounds hM
  have hPdata := PseudoPrime.NumberTheory.PrimeProducts.primeProductLECoprime_data z Q
  have hP : Squarefree P := by simpa only [P] using hPdata.1
  have hPQ : Nat.Coprime P Q := by
    simpa only [P] using PseudoPrime.NumberTheory.PrimeProducts.primeProductLECoprime_coprime z Q
  have hPsmall : ∀ p : ℕ, Nat.Prime p → p ∣ P → p ≤ z := by
    simpa only [P] using PseudoPrime.NumberTheory.PrimeProducts.primeProductLECoprime_small z Q
  have hz : 1 ≤ z := by simpa only [z] using hcut.1
  have hMpos : 0 < M := by linarith only [hM]
  have hQpos : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hphiPos : 0 < (Nat.totient Q : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hQ
  have hlogMpos : 0 < Real.log M := Real.log_pos (by linarith only [hM])
  have hlogZpos : 0 < Real.log ((z + 1 : ℕ) : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (Nat.lt_succ_of_le hz)
  have hnorm : (Nat.totient Q : ℝ) / (Q : ℝ) * (Real.log ((z + 1 : ℕ) : ℝ) / 2) ≤ G := by
    simpa only [G, P] using
      selbergTruncatedTotientSum_coprime_primorial_ge_totient_ratio_log_div_two z Q hQ hz
  have hGpos : 0 < G := by
    apply lt_of_lt_of_le _ hnorm
    exact mul_pos (div_pos hphiPos hQpos) (div_pos hlogZpos (by norm_num only : (0 : ℝ) < 2))
  have hlogcut : Real.log M / 8 ≤ Real.log ((z + 1 : ℕ) : ℝ) := hcut.2.2.1
  have hnorm' : (Nat.totient Q : ℝ) / (Q : ℝ) * (Real.log M / 16) ≤ G := by
    have hlog : Real.log M / 16 ≤ Real.log ((z + 1 : ℕ) : ℝ) / 2 := by linarith only [hlogcut]
    have hratio : 0 ≤ (Nat.totient Q : ℝ) / (Q : ℝ) := div_nonneg (Nat.cast_nonneg _) hQpos.le
    exact le_trans (mul_le_mul_of_nonneg_left hlog hratio) hnorm
  have hbasePos : 0 < (Nat.totient Q : ℝ) / (Q : ℝ) * (Real.log M / 16) :=
    mul_pos (div_pos hphiPos hQpos) (div_pos hlogMpos (by norm_num only : (0 : ℝ) < 16))
  have hGinv : 1 / G ≤ 16 * (Q : ℝ) / ((Nat.totient Q : ℝ) * Real.log M) := by
    calc
      1 / G ≤ 1 / ((Nat.totient Q : ℝ) / (Q : ℝ) * (Real.log M / 16)) :=
        one_div_le_one_div_of_le hbasePos hnorm'
      _ = 16 * (Q : ℝ) / ((Nat.totient Q : ℝ) * Real.log M) := by
        field_simp [ne_of_gt hQpos, ne_of_gt hphiPos, ne_of_gt hlogMpos]
  have hmass := coarseProgressionSieveMassBound (Y := Y) (Q := Q) (a := a) (P := P) hP hQ
  have hmassBound : (progressionBoundingSieve Y Q a P hP).totalMass ≤ M + 2 := by
    simpa only [M] using hmass
  have hmassSmall : M + 2 ≤ (3 / 2 : ℝ) * M := by nlinarith only [hM]
  have hmain :
    (progressionBoundingSieve Y Q a P hP).totalMass * (1 / G) ≤
      24 * (Y : ℝ) / ((Nat.totient Q : ℝ) * Real.log M) := by
    have hmassNonneg : 0 ≤ (progressionBoundingSieve Y Q a P hP).totalMass := by
      rw [progressionBoundingSieve_totalMass_eq hP hQ]
      exact_mod_cast Nat.zero_le _
    have hfactorNonneg : 0 ≤ 16 * (Q : ℝ) / ((Nat.totient Q : ℝ) * Real.log M) :=
      div_nonneg (mul_nonneg (by norm_num only) (Nat.cast_nonneg Q))
        (le_of_lt (mul_pos hphiPos hlogMpos))
    have hscaleEq : M * (Q : ℝ) = (Y : ℝ) := by
      dsimp only [M]
      field_simp [ne_of_gt hQpos]
    have hnumerator : (M + 2) * (16 * (Q : ℝ)) ≤ 24 * (Y : ℝ) := by
      calc
        (M + 2) * (16 * (Q : ℝ)) ≤ ((3 / 2 : ℝ) * M) * (16 * (Q : ℝ)) :=
          mul_le_mul_of_nonneg_right hmassSmall (mul_nonneg (by norm_num only) (Nat.cast_nonneg Q))
        _ = 24 * (M * (Q : ℝ)) := by ring
        _ = 24 * (Y : ℝ) := by rw [hscaleEq]
    calc
      (progressionBoundingSieve Y Q a P hP).totalMass * (1 / G) ≤
          (progressionBoundingSieve Y Q a P hP).totalMass *
            (16 * (Q : ℝ) / ((Nat.totient Q : ℝ) * Real.log M)) :=
        mul_le_mul_of_nonneg_left hGinv hmassNonneg
      _ ≤ (M + 2) * (16 * (Q : ℝ) / ((Nat.totient Q : ℝ) * Real.log M)) :=
        mul_le_mul_of_nonneg_right hmassBound hfactorNonneg
      _ = ((M + 2) * (16 * (Q : ℝ))) / ((Nat.totient Q : ℝ) * Real.log M) := by ring
      _ ≤ 24 * (Y : ℝ) / ((Nat.totient Q : ℝ) * Real.log M) :=
        div_le_div_of_nonneg_right hnumerator (le_of_lt (mul_pos hphiPos hlogMpos))
  have hzSqrt : (z : ℝ) ≤ Real.sqrt M := by
    calc
      (z : ℝ) ≤ Real.rpow M (1 / 2 : ℝ) := by simpa only [z] using hcut.2.2.2.1
      _ = Real.sqrt M := (Real.sqrt_eq_rpow M).symm
  have hzFourth : (z : ℝ) ^ 4 ≤ Real.sqrt M := by
    calc
      (z : ℝ) ^ 4 ≤ Real.rpow M (1 / 2 : ℝ) := by simpa only [z] using hcut.2.2.2.2
      _ = Real.sqrt M := (Real.sqrt_eq_rpow M).symm
  have hsmallError := coarseCutoffErrorBound hz hzSqrt hzFourth
  have habsorb := coarseSqrtLogAbsorption hM
  have hphiQ : (Nat.totient Q : ℝ) ≤ (Q : ℝ) := by exact_mod_cast Nat.totient_le Q
  have hYphi : M ≤ (Y : ℝ) / (Nat.totient Q : ℝ) := by
    dsimp only [M]
    exact div_le_div_of_nonneg_left (by exact_mod_cast Nat.zero_le Y) hphiPos hphiQ
  have hsmallBound : 6 * Real.sqrt M ≤ 8 * (Y : ℝ) / ((Nat.totient Q : ℝ) * Real.log M) := by
    calc
      6 * Real.sqrt M ≤ 8 * M / Real.log M := habsorb
      _ = 8 * (M / Real.log M) := by ring
      _ ≤ 8 * (((Y : ℝ) / (Nat.totient Q : ℝ)) / Real.log M) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hYphi hlogMpos.le)
          (by norm_num only : (0 : ℝ) ≤ 8)
      _ = 8 * (Y : ℝ) / ((Nat.totient Q : ℝ) * Real.log M) := by
        field_simp [ne_of_gt hphiPos, ne_of_gt hlogMpos]
  have hbase :=
    progressionPrimeCount_le_truncatedOptimal_selberg_explicit_error (Y := Y) (Q := Q) (a := a)
      (z := z) (P := P) hP hQ hPQ hz G rfl hPsmall
  calc
    (primeCountInProgression Y Q a : ℝ) ≤
        ((Finset.range (z + 1)).filter Nat.Prime).card +
          ((progressionBoundingSieve Y Q a P hP).totalMass * (1 / G) +
            ((z : ℝ) * (z + 1 : ℕ)) ^ 2) :=
      hbase
    _ ≤
        ((Finset.range (z + 1)).filter Nat.Prime).card +
          (24 * (Y : ℝ) / ((Nat.totient Q : ℝ) * Real.log M) + ((z : ℝ) * (z + 1 : ℕ)) ^ 2) :=
      by
      have hinner' :
        (progressionBoundingSieve Y Q a P hP).totalMass * (1 / G) + ((z : ℝ) * (z + 1 : ℕ)) ^ 2 ≤
          24 * (Y : ℝ) / ((Nat.totient Q : ℝ) * Real.log M) + ((z : ℝ) * (z + 1 : ℕ)) ^ 2 := by
        calc
          _ =
              ((z : ℝ) * (z + 1 : ℕ)) ^ 2 +
                (progressionBoundingSieve Y Q a P hP).totalMass * (1 / G) :=
            by ring
          _ ≤ ((z : ℝ) * (z + 1 : ℕ)) ^ 2 + 24 * (Y : ℝ) / ((Nat.totient Q : ℝ) * Real.log M) :=
            add_le_add_right hmain _
          _ = _ := by ring
      exact add_le_add_right hinner' _
    _ =
        (((Finset.range (z + 1)).filter Nat.Prime).card + ((z : ℝ) * (z + 1 : ℕ)) ^ 2) +
          24 * (Y : ℝ) / ((Nat.totient Q : ℝ) * Real.log M) :=
      by ring
    _ ≤ 6 * Real.sqrt M + 24 * (Y : ℝ) / ((Nat.totient Q : ℝ) * Real.log M) := by
      exact add_le_add_left hsmallError _
    _ ≤ 32 * (Y : ℝ) / ((Nat.totient Q : ℝ) * Real.log M) := by
      calc
        _ = 24 * (Y : ℝ) / ((Nat.totient Q : ℝ) * Real.log M) + 6 * Real.sqrt M := by ring
        _ ≤
            24 * (Y : ℝ) / ((Nat.totient Q : ℝ) * Real.log M) +
              8 * (Y : ℝ) / ((Nat.totient Q : ℝ) * Real.log M) :=
          add_le_add_right hsmallBound _
        _ = 32 * (Y : ℝ) / ((Nat.totient Q : ℝ) * Real.log M) := by ring

end PseudoPrime.AnalyticNumberTheory.AGP
