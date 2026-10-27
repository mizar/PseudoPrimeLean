/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianMRRelativeNumerics
public import PseudoPrime.Analysis.GaussianMRVariableRelativeNumerics
public import PseudoPrime.LLS.RelativeGaussianSubgroupComparison
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPrincipalWitnessBounds

/-! # Gaussian MR witnesses from relative-loss principal lower bounds -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At log(n) at least 350000, the actual relative-width Gaussian comparison
is impossible for a subgroup of index at least four. The normalized main term
is at least 1827/2500, while lower, principal, and ambient errors total at most
300. Retain the conductor sum until its final bound by (index-1)log(n). -/
theorem gaussian_relative_inequality_contradiction {n : ℕ} [NeZero n] (H : Subgroup (ZMod n)ˣ)
    (hi : 4 ≤ H.index) (hL : 350000 ≤ Real.log n) :
    let x := Analysis.gaussianMRScale (Real.log n)
    ¬(((H.index : ℝ) * (1 - (1 / 2000 : ℝ)) *
              (∫ u in (0 : ℝ)..(21 / 10 : ℝ),
                (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u) -
            Real.exp (1 / 16 : ℝ)) *
          Real.sqrt x ≤
        (161 / 400 : ℝ) * LLS.PaperStatements.subgroupConductorLogSum H +
          (H.index : ℝ) *
            (1 / (10 * (1 / 2000 : ℝ)) +
              ((21 / (10 * (1 / 2000 : ℝ)) + 1839 / 1000) / Real.sqrt x) * Real.exp (1 / 16 : ℝ)) +
          13 +
          ((H.index - 1 : ℕ) : ℝ) * LLS.PaperStatements.gaussianAmbientError n x) := by
  intro x hcmp
  have hiR : (4 : ℝ) ≤ H.index := Nat.cast_le.mpr hi
  have hm : (0 : ℝ) < (H.index : ℝ) - 1 := by linarith only [hiR]
  have hcast : ((H.index - 1 : ℕ) : ℝ) = (H.index : ℝ) - 1 := by
    rw [Nat.cast_sub (le_trans (by decide : 1 ≤ 4) hi), Nat.cast_one]
  rw [hcast] at hcmp
  have hI := LLS.PaperStatements.gaussianGamma_cutoff_gt_target.le
  have hE := Analysis.gaussian_endpoint_exp_le
  have hmain :
    ((H.index : ℝ) - 1) * (1827 / 2500 : ℝ) ≤
      (H.index : ℝ) * (1 - (1 / 2000 : ℝ)) *
          (∫ u in (0 : ℝ)..(21 / 10 : ℝ),
            (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u) -
        Real.exp (1 / 16 : ℝ) := by
    have hw :=
      mul_le_mul_of_nonneg_left hI
        (show 0 ≤ (H.index : ℝ) * (1 - (1 / 2000 : ℝ)) by nlinarith only [hiR])
    nlinarith only [hw, hE, hiR]
  have hleft := mul_le_mul_of_nonneg_right hmain (Real.sqrt_nonneg x)
  have hC :=
    mul_le_mul_of_nonneg_left (LLS.PaperStatements.subgroupConductorLogSum_le H)
      (by norm_num only : (0 : ℝ) ≤ 161 / 400)
  have hB :=
    mul_le_mul_of_nonneg_left (Analysis.gaussianMR_relative_lower_error_le hL)
      (Nat.cast_nonneg H.index)
  have hA :=
    mul_le_mul_of_nonneg_left
      (Analysis.gaussianMR_ambient_error_le_relative hL (le_refl (Real.log n))) hm.le
  have hright :
    (161 / 400 : ℝ) * LLS.PaperStatements.subgroupConductorLogSum H +
        (H.index : ℝ) *
          (1 / (10 * (1 / 2000 : ℝ)) +
            ((21 / (10 * (1 / 2000 : ℝ)) + 1839 / 1000) / Real.sqrt x) * Real.exp (1 / 16 : ℝ)) +
        13 +
        ((H.index : ℝ) - 1) * LLS.PaperStatements.gaussianAmbientError n x ≤
      ((H.index : ℝ) - 1) * ((161 / 400 : ℝ) * Real.log n + 300) := by
    nlinarith only [hC, hB, hA, hiR]
  have hstrict := mul_lt_mul_of_pos_left (Analysis.gaussianMR_relative_main_term_lt hL) hm
  rw [← mul_assoc] at hstrict
  exact (not_lt_of_ge (hleft.trans (hcmp.trans hright))) hstrict

theorem exists_prime_witness_le_gaussian_relative_of_index_ge_four {n : ℕ} [NeZero n]
    (hnOdd : Odd n) (H : Subgroup (ZMod n)ˣ) (hi : 4 ≤ H.index)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 350000 ≤ Real.log n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (16 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  classical
  have hpos : 0 < Real.log n := (by norm_num only : (0 : ℝ) < 350000).trans_le hL
  have hlog := Real.log_le_sub_one_of_pos (Nat.cast_pos.mpr (NeZero.pos n) : (0 : ℝ) < n)
  have hnlarge : 20000 ≤ n := by
    apply Nat.cast_le (α := ℝ).mp
    norm_num only [Nat.cast_ofNat]
    linarith only [hL, hlog]
  by_contra hnone
  let x := Analysis.gaussianMRScale (Real.log n)
  have hx : 4 ≤ x :=
    (by norm_num only : (4 : ℝ) ≤ 3 ^ 16).trans
      (Analysis.gaussianMRScale_ge_three_pow_sixteen_relative hL)
  have hcut : (21 / 10 : ℝ) * x = (16 / 25 : ℝ) * (Real.log n) ^ 2 := by
    dsimp only [x, Analysis.gaussianMRScale]
    ring
  have hpass :
    ∀ r : ℕ,
      r.Prime → (r : ℝ) ≤ (21 / 10 : ℝ) * x → PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
    intro r hr hb
    rw [hcut] at hb
    by_contra hfail
    exact hnone ⟨r, hr, hb, hfail⟩
  have hdiv (p : ℕ) (hp : p.Prime) (hd : p ∣ n) : ⌊(21 / 10 : ℝ) * x⌋₊ < p := by
    apply lt_of_not_ge
    intro hle
    have hb : (p : ℝ) ≤ (21 / 10 : ℝ) * x := (Nat.le_floor_iff' hp.ne_zero).mp hle
    have hn1 : 1 < n := lt_of_lt_of_le (by decide : 1 < 20000) hnlarge
    exact PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn1 hnOdd hp hd (hpass p hp hb)
  have hcmp :=
    LLS.PaperStatements.gaussian_noSmallPrimes_inequality_relative hnlarge H hGRH
      (by norm_num only : (0 : ℝ) < 1 / 2000) (by norm_num only : (1 / 2000 : ℝ) ≤ 1 / 2) hx
      (by norm_num only : (0 : ℝ) ≤ 21 / 10) hdiv
      (fun p hp _ hb ↦ hHpass (p : ZMod n) (hpass p hp hb))
  exact gaussian_relative_inequality_contradiction H hi hL hcmp

/-- The general relative-width Gaussian inequality is incompatible with the
variable-radius budget when the pass-containing subgroup has index at least
four. The proof normalizes the index by `index - 1`, then applies the explicit
ambient-error and coefficient comparison from the analytic estimate. -/
theorem gaussianMRVariable_inequality_contradiction {n : ℕ} [NeZero n] (H : Subgroup (ZMod n)ˣ)
    (hi : 4 ≤ H.index) {L : ℝ} (hL : 4000 ≤ L) (hlog : Real.log n ≤ L)
    (hcmp :
      let r := Analysis.gaussianMRVariableRadius L
      let s := Real.sqrt r
      let h := 1 / (3 * s)
      let I :=
        ∫ u in (0 : ℝ)..(21 / 10 : ℝ),
          (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u
      ((H.index : ℝ) * (1 - h) * I - Real.exp (1 / 16 : ℝ)) * r ≤
        (161 / 400 : ℝ) * LLS.PaperStatements.subgroupConductorLogSum H +
          (H.index : ℝ) *
            (1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / r) * Real.exp (1 / 16 : ℝ)) +
          13 +
          ((H.index - 1 : ℕ) : ℝ) * LLS.PaperStatements.gaussianAmbientError n (r ^ 2)) :
    False := by
  dsimp only at hcmp
  let r := Analysis.gaussianMRVariableRadius L
  let s := Real.sqrt r
  let h := 1 / (3 * s)
  let I :=
    ∫ u in (0 : ℝ)..(21 / 10 : ℝ),
      (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u
  let E := Real.exp (1 / 16 : ℝ)
  let k := (H.index : ℝ)
  let d := k - 1
  have hrL : L / 2 ≤ r := Analysis.gaussianMRVariableRadius_half hL
  have hLpos : 0 < L := by linarith only [hL]
  have hrpos : 0 < r := lt_of_lt_of_le (div_pos hLpos (by norm_num only)) hrL
  have hspos : 0 < s := Real.sqrt_pos.2 hrpos
  have hs20 : 20 ≤ s := by simpa only [r, s] using Analysis.gaussianMRVariableRadius_sqrt_lower hL
  have hRsq : s ^ 2 = r := by
    dsimp only [s]
    exact Real.sq_sqrt hrpos.le
  have hdiv : r / s = s := by
    rw [← hRsq]
    exact (div_eq_iff hspos.ne').2 (by ring)
  have hh : h = 1 / (3 * s) := rfl
  have hh1 : h ≤ 1 / 2 := by
    dsimp only [h]
    have hden : 2 ≤ 3 * s := by nlinarith only [hs20]
    exact one_div_le_one_div_of_le (by norm_num only) hden
  have hk : (4 : ℝ) ≤ k := Nat.cast_le.mpr hi
  have hd : 0 < d := by
    dsimp only [d]; nlinarith only [hk]
  have hd3 : 3 ≤ d := by
    dsimp only [d]; nlinarith only [hk]
  have hkd : k = d + 1 := by
    dsimp only [d]; ring
  have huEq : k / d = 1 + 1 / d := by
    rw [hkd]; field_simp [hd.ne']
  have hv0 : 0 ≤ 1 / d := div_nonneg (by norm_num only) hd.le
  have hv3 : 1 / d ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num only) hd3
  have hI0 : (8147 / 10000 : ℝ) ≤ (81470555 / 100000000 : ℝ) := by norm_num only
  have hI : 8147 / 10000 ≤ I := by
    dsimp only [I]
    exact hI0.trans LLS.PaperStatements.gaussianGamma_cutoff_gt_target.le
  have hE : E ≤ 2129 / 2000 := by
    dsimp only [E]
    exact Analysis.gaussian_endpoint_exp_le
  have hEpos : 0 < E := by
    dsimp only [E]; exact Real.exp_pos _
  have hnorm :=
    Analysis.gaussianMRVariable_normalized_main_lower (u := k / d) (v := 1 / d) (s := s) (I := I)
      (E := E) (h := h) huEq hv0 hv3 hspos hh hh1 hI hE
  have hmul := mul_le_mul_of_nonneg_right hnorm (mul_nonneg hd.le hrpos.le)
  have hleftEq :
    (21943 / 30000 - (4 / 9 * (8147 / 10000)) / s) * (d * r) =
      d * (21943 / 30000 * r - (4 / 9 * (8147 / 10000)) * s) := by
    calc
      _ = d * (21943 / 30000 * r - (4 / 9 * (8147 / 10000)) * (r / s)) := by ring
      _ = _ := by rw [hdiv]
  have hrightEq : (k / d * (1 - h) * I - 1 / d * E) * (d * r) = (k * (1 - h) * I - E) * r := by
    field_simp [hd.ne']
  rw [hleftEq, hrightEq] at hmul
  have hconductor := LLS.PaperStatements.subgroupConductorLogSum_le H
  have hcastSub : ((H.index - 1 : ℕ) : ℝ) = (H.index : ℝ) - 1 := by
    rw [Nat.cast_sub (le_trans (by decide : 1 ≤ 4) hi), Nat.cast_one]
  have hcast : ((H.index - 1 : ℕ) : ℝ) = d := by rw [hcastSub]
  have hcastIndex : (H.index : ℝ) - 1 = d := by dsimp only [d, k]
  have hIndexReal : (4 : ℝ) ≤ (H.index : ℝ) := Nat.cast_le.mpr hi
  have hcondPos : 0 ≤ (H.index : ℝ) - 1 := by nlinarith only [hIndexReal]
  have hconductorL : LLS.PaperStatements.subgroupConductorLogSum H ≤ d * L := by
    calc
      _ ≤ ((H.index : ℝ) - 1) * Real.log n := hconductor
      _ ≤ ((H.index : ℝ) - 1) * L := mul_le_mul_of_nonneg_left hlog hcondPos
      _ = d * L := by rw [hcastIndex]
  have hconductorScaled :=
    mul_le_mul_of_nonneg_left hconductorL (by norm_num only : (0 : ℝ) ≤ 161 / 400)
  have hambient := Analysis.gaussianMRVariable_ambient_error_le hL hlog
  have herror :=
    Analysis.gaussianMRVariable_error_bracket_upper (s := s) (r := r) (h := h) (E := E) hspos
      hRsq.symm hh hE
  let B := 1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / r) * E
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    have h10h : 0 < 10 * h :=
      mul_pos (by norm_num only) (one_div_pos.mpr (mul_pos (by norm_num only) hspos))
    have hNum : 0 < 21 / (10 * h) + 1839 / 1000 :=
      add_pos (div_pos (by norm_num only) h10h) (by norm_num only)
    exact
      add_nonneg (le_of_lt (one_div_pos.mpr h10h))
        (mul_nonneg (div_nonneg hNum.le hrpos.le) hEpos.le)
  have hratio : k ≤ 4 / 3 * d := by
    calc
      k = d + 1 := hkd
      _ ≤ 4 / 3 * d := by nlinarith only [hd3]
  have hBscaled := mul_le_mul_of_nonneg_right hratio hB0
  have hBupper := mul_le_mul_of_nonneg_left herror (le_of_lt hd)
  have hBfinal : k * B ≤ d * ((2 / 5 : ℝ) * s + 44709 / (5000 * s) + 1305077 / (500000 * r)) := by
    calc
      k * B ≤ (4 / 3 * d) * B := hBscaled
      _ = d * (4 / 3 * B) := by ring
      _ ≤ d * ((2 / 5 : ℝ) * s + 44709 / (5000 * s) + 1305077 / (500000 * r)) := hBupper
  have h13 : (13 : ℝ) ≤ d * (13 / 3) := by nlinarith only [hd3]
  have hRhs :
    (161 / 400 : ℝ) * LLS.PaperStatements.subgroupConductorLogSum H + k * B + 13 +
        d * LLS.PaperStatements.gaussianAmbientError n (r ^ 2) ≤
      d *
        ((161 / 400 : ℝ) * L + (2 / 5) * s + 44709 / (5000 * s) + 1305077 / (500000 * r) + 13 / 3 +
          LLS.PaperStatements.gaussianAmbientError n (r ^ 2)) := by
    nlinarith only [hconductorScaled, hBfinal, h13]
  rw [hcast] at hcmp
  have hscaled :
    d * (21943 / 30000 * r - (4 / 9 * (8147 / 10000)) * s) ≤
      d *
        ((161 / 400 : ℝ) * L + (2 / 5) * s + 44709 / (5000 * s) + 1305077 / (500000 * r) + 13 / 3 +
          LLS.PaperStatements.gaussianAmbientError n (r ^ 2)) := by
    have hright := hcmp.trans (by simpa only [B] using hRhs)
    exact hmul.trans (by simpa only [B] using hright)
  have hcancel := le_of_mul_le_mul_left hscaled hd
  have hbudget := Analysis.gaussianMRVariable_comparison_impossible_of_ambient hL hlog
  apply hbudget
  have hineq :
    21943 / 30000 * r ≤
      (161 / 400 : ℝ) * L + (17147 / 22500) * s + 44709 / (5000 * s) + 1305077 / (500000 * r) +
        13 / 3 +
        LLS.PaperStatements.gaussianAmbientError n (r ^ 2) := by
    nlinarith only [hcancel]
  exact hineq

/-- Under GRH, every odd composite log n≥350000 has a prime strong
Miller--Rabin witness at most (16/25)log(n)². The arithmetic pass-containing
subgroup has index at least four; the threshold excludes the exceptional modulus 9.
Apply the actual Gaussian comparison and explicit numerical budget. No additional
subgroup, integral, zero-mass, or error hypothesis remains. -/
theorem exists_prime_witness_le_gaussian_relative {n : ℕ} (hnOdd : Odd n) (hnComposite : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 350000 ≤ Real.log n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (16 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hn0 : n ≠ 0 := by
    intro hz
    rw [hz, Nat.cast_zero, Real.log_zero] at hL
    norm_num only at hL
  have hlog := Real.log_le_sub_one_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0))
  have hnlarge : 20000 ≤ n := by
    apply Nat.cast_le (α := ℝ).mp
    norm_num only [Nat.cast_ofNat]
    linarith only [hL, hlog]
  have hn1 : 1 < n := lt_of_lt_of_le (by decide : 1 < 20000) hnlarge
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn1⟩
  have hn9 : n ≠ 9 := by
    intro h
    rw [h] at hnlarge
    exact (by decide : ¬20000 ≤ 9) hnlarge
  obtain ⟨H, hi, hHpass⟩ :=
    PrimeTest.exists_index_ge_four_subgroup_containing_strongMillerRabinPass hn1 hnOdd hnComposite
      hn9
  exact exists_prime_witness_le_gaussian_relative_of_index_ge_four hnOdd H hi hHpass hGRH hL

/-- Under GRH for odd n with log n≥350000, passage of the canonical strong test
for every prime base at most (16/25)log(n)² is equivalent to primality.
The composite direction uses the explicit relative-loss Gaussian prime witness; the prime
direction restricts the existing log-squared criterion to the smaller cutoff.
The same logarithmic threshold applies to both directions. -/
theorem prime_iff_millerRabin_for_all_primes_le_gaussian_relative {n : ℕ} (hnOdd : Odd n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 350000 ≤ Real.log n) :
    (∀ r : ℕ,
        r.Prime →
          (r : ℝ) ≤ (16 / 25 : ℝ) * (Real.log n) ^ 2 →
          PrimeTest.StrongMillerRabinPass n (r : ZMod n)) ↔
      n.Prime := by
  constructor
  · intro hpass
    by_contra hComposite
    obtain ⟨r, hr, hb, hfail⟩ := exists_prime_witness_le_gaussian_relative hnOdd hComposite hGRH hL
    exact hfail (hpass r hr hb)
  · intro hp r hr hb
    have hn1 : 1 < n := hp.one_lt
    have hcap : (16 / 25 : ℝ) * (Real.log n) ^ 2 ≤ (Real.log n) ^ 2 :=
      mul_le_of_le_one_left (sq_nonneg _) (by norm_num only)
    exact
      (prime_iff_millerRabin_for_all_primes_le_log_sq hGRH hn1 hnOdd).mpr hp r hr (hb.trans hcap)

end PseudoPrime.PrimeTestBounds.MillerRabin
