/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.HighCoefficientSemiprime
public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsHighKernel
public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsSquareBounds

/-! # High-range prime-product budgets for repeated factors -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The floor radius close to `(66143 / 100000) * L`, a positive logarithmic
scale at most `L / 2000`, and the stated floor and ceiling bounds imply that
the paired binomial base exceeds `(7 / 6) * b`. This supports the square
kernel budget with product exponent below `L / u`. -/
theorem highCoeff_square_ratio {L b u : ℝ} {M k : ℕ} (hL : 70000 ≤ L)
    (hb : (66143 / 100000 : ℝ) * L - 1 ≤ b) (hu0 : 0 < u) (hu : u ≤ L / 2000) (hkM : k ≤ M)
    (hM : ((9 / 10 : ℝ) * b ^ 2) / u < (M : ℝ) + 1) (hk : (k : ℝ) < L / u) :
    (7 / 6 : ℝ) * b < 2 * ((M + 1 - k : ℕ) : ℝ) / (k + 1) := by
  have hb0 : 0 < b := by linarith only [hL, hb]
  have hpart : (7 / 6 : ℝ) * (L + u) < (9 / 5 : ℝ) * b - 4 := by linarith only [hL, hb, hu]
  have hmul := mul_lt_mul_of_pos_left hpart hb0
  have hbound : 2 * L ≤ 4 * b := by linarith only [hL, hb]
  have hbase : (7 / 6 : ℝ) * b * (L + u) < 2 * ((9 / 10 : ℝ) * b ^ 2 - L) := by
    nlinarith only [hmul, hbound]
  have hmk : ((M + 1 - k : ℕ) : ℝ) = (M : ℝ) + 1 - k := by
    rw [Nat.cast_sub (hkM.trans (Nat.le_succ M)), Nat.cast_succ]
  have hN : ((9 / 10 : ℝ) * b ^ 2 - L) < ((M + 1 - k : ℕ) : ℝ) * u := by
    have hm := (div_lt_iff₀ hu0).mp hM
    have hkk := (lt_div_iff₀ hu0).mp hk
    nlinarith only [hm, hkk, hmk]
  have hK : ((k : ℝ) + 1) * u < L + u := by
    have hkk := (lt_div_iff₀ hu0).mp hk
    linarith only [hkk]
  have hleft := mul_lt_mul_of_pos_left hK (mul_pos (by norm_num only : (0 : ℝ) < 7 / 6) hb0)
  have hright := mul_lt_mul_of_pos_left hN (show (0 : ℝ) < 2 by norm_num only)
  have hden : 0 < (k : ℝ) + 1 := add_pos_of_nonneg_of_pos (Nat.cast_nonneg k) (by norm_num only)
  apply (lt_div_iff₀ hden).2
  have hv : (7 / 6 : ℝ) * b * ((k : ℝ) + 1) * u < (2 * ((M + 1 - k : ℕ) : ℝ)) * u := by
    nlinarith only [hleft, hbase, hright]
  exact lt_of_mul_lt_mul_right hv hu0.le

/-- For positive `L` and `u`, a multiplier `σ ≥ 1 / 3`, and the stated
quadratic logarithmic margin, the ceiling-minus-one lower bound for `k`
gives a strict paired-count budget above `σ * L / 2`. -/
theorem highCoeff_partial_scalar {L σ u k : ℝ} (hL : 0 < L) (hσ : (1 / 3 : ℝ) ≤ σ) (hu : 0 < u)
    (hm : u ^ 2 + (29 / 25 : ℝ) * u ≤ L / 100) (hk : σ * L / u - 1 ≤ k) :
    σ * L / 2 < k * (u / 2 + 3 / 20) := by
  have hmargin : u ^ 2 + (3 / 10 : ℝ) * u < ((1 / 2 : ℝ) * L) / 5 := by linarith only [hm, hu, hL]
  have hsigma : (2 / 3 : ℝ) ≤ (2 : ℝ) * σ := by linarith only [hσ]
  have hk' : ((2 : ℝ) * σ) * ((1 / 2 : ℝ) * L) / u - 1 ≤ k := by
    convert hk using 1
    ring
  have h :=
    high_kernel_scalar_budget (L := (1 / 2 : ℝ) * L) (σ := (2 : ℝ) * σ)
      (mul_pos (by norm_num only) hL) hsigma hu hmargin hk'
  convert h using 1
  ring

/-- For `L ≥ 70000` and `1 / 3 ≤ σ ≤ 1`, the selected floor radius and
prime supply with exponent `ceil (σ * L / u) - 1` give a paired binomial
count greater than `exp (σ * L / 2)`. The logarithmic error and ratio
estimates hold on the whole half-line without finite input enumeration. -/
theorem highCoeff_partial_selected_count {L σ : ℝ} (hL : 70000 ≤ L) (hσ : (1 / 3 : ℝ) ≤ σ)
    (hσ1 : σ ≤ 1) :
    let b : ℝ := (⌊(66143 / 100000 : ℝ) * L⌋₊ : ℝ)
    let u := 2 * Real.log b
    let M := ⌊((9 / 10 : ℝ) * b ^ 2) / u⌋₊
    let k := ⌈σ * L / u⌉₊ - 1
    Real.exp (σ * L / 2) < (Nat.choose M k : ℝ) := by
  dsimp only
  let b : ℝ := (⌊(66143 / 100000 : ℝ) * L⌋₊ : ℝ)
  let u := 2 * Real.log b
  let M := ⌊((9 / 10 : ℝ) * b ^ 2) / u⌋₊
  let k := ⌈σ * L / u⌉₊ - 1
  let R : ℝ := 2 * ((M + 1 - k : ℕ) : ℝ) / (k + 1)
  have hL0 : 0 < L := by linarith only [hL]
  have hσ0 : 0 < σ := by linarith only [hσ]
  have hσL : σ * L ≤ L := by nlinarith only [mul_nonneg (sub_nonneg.mpr hσ1) hL0.le]
  have hbFloor := Nat.lt_floor_add_one ((66143 / 100000 : ℝ) * L)
  have hb : (66143 / 100000 : ℝ) * L - 1 ≤ b := by
    dsimp only [b]
    linarith only [hbFloor]
  have hb1 : 1 < b := by linarith only [hL, hb]
  have hu : 0 < u := mul_pos (by norm_num only) (Real.log_pos hb1)
  have hm : u ^ 2 + (29 / 25 : ℝ) * u ≤ L / 100 := highCoeff_semiprime_log_margin hL
  have huLin : u ≤ L / 2000 := highCoeff_semiprime_log_linear hL hu.le hm
  have hy : 0 < σ * L / u := div_pos (mul_pos hσ0 hL0) hu
  have hk := ceil_sub_one_bounds hy
  have hquad : σ * L < (9 / 10 : ℝ) * b ^ 2 := by nlinarith only [hL, hb, hσL, sq_nonneg (b - 100)]
  have hkM : k ≤ M := ceil_sub_one_le_floor hy ((div_lt_div_iff_of_pos_right hu).2 hquad)
  have hfloor := Nat.lt_floor_add_one (((9 / 10 : ℝ) * b ^ 2) / u)
  have hkUpper : (k : ℝ) < L / u := hk.2.trans_le ((div_le_div_iff_of_pos_right hu).2 hσL)
  have hratio : (7 / 6 : ℝ) * b < R := highCoeff_square_ratio hL hb hu huLin hkM hfloor hkUpper
  have hpos : 0 < (7 / 6 : ℝ) * b := mul_pos (by norm_num only) (lt_trans (by norm_num only) hb1)
  have hR : 0 < R := hpos.trans hratio
  have hlog := Real.log_lt_log hpos hratio
  rw [Real.log_mul (by norm_num only : (7 / 6 : ℝ) ≠ 0)
      (ne_of_gt (lt_trans (by norm_num only : (0 : ℝ) < 1) hb1))] at hlog
  have hc : Analysis.rationalLogIntervalCheck (7 / 6) 0 12 (151 / 1000) 1 = true := by
    decide +kernel
  have hconst := (Analysis.rationalLogIntervalCheck_sound hc).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hconst
  have hlogR : u / 2 + (3 / 20 : ℝ) < Real.log R := by
    dsimp only [u]
    linarith only [hlog, hconst]
  have hscalar := highCoeff_partial_scalar hL0 hσ hu hm hk.1
  have hkpos : 0 < k := by
    have hku := hk.1
    have hratio : (2 : ℝ) < σ * L / u := by
      apply (lt_div_iff₀ hu).2
      nlinarith only [hL, huLin, mul_nonneg (sub_nonneg.mpr hσ) hL0.le]
    have hkr : (0 : ℝ) < (k : ℝ) := by linarith only [hku, hratio]
    exact_mod_cast hkr
  have hmul := mul_lt_mul_of_pos_left hlogR (Nat.cast_pos.mpr hkpos)
  have hbudget : σ * L / 2 < (k : ℝ) * Real.log R := hscalar.trans hmul
  exact exp_lt_choose_of_paired_budget M k hR hbudget

/-- At scale at least 70000, the full-logarithm exponent gives a paired
binomial count exceeding `exp (L / 2)`. This specializes the uniform
partial-scale count for the prime-power branch. -/
theorem highCoeff_square_selected_count {L : ℝ} (hL : 70000 ≤ L) :
    let b : ℝ := (⌊(66143 / 100000 : ℝ) * L⌋₊ : ℝ)
    let u := 2 * Real.log b
    let M := ⌊((9 / 10 : ℝ) * b ^ 2) / u⌋₊
    let k := ⌈L / u⌉₊ - 1
    Real.exp (L / 2) < (Nat.choose M k : ℝ) := by
  simpa only [one_mul] using
    highCoeff_partial_selected_count (σ := (1 : ℝ)) hL (by norm_num only) (by norm_num only)

/-- For `n = p ^ a` with `a ≥ 2`, a logarithmic product-size bound and a
binomial count with twice its logarithm above `log n` give `B ^ k < p ^ a`
and `p - 1 < choose M k`. These are the local prime-power kernel conditions. -/
theorem highCoeff_primePow_choose {n p B M k a : ℕ} (hp : p.Prime) (hpow : n = p ^ a) (ha : 2 ≤ a)
    (hB : 1 < B) (hsize : (k : ℝ) * Real.log B < Real.log n)
    (hcount : Real.log n < 2 * Real.log (Nat.choose M k : ℝ)) :
    B ^ k < p ^ a ∧ p - 1 < Nat.choose M k := by
  have hpos : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have hnpos : (0 : ℝ) < n := by
    rw [hpow, Nat.cast_pow]
    exact pow_pos hpos _
  have hsize' : Real.log ((B : ℝ) ^ k) < Real.log (n : ℝ) := by
    rw [Real.log_pow]
    exact hsize
  have hlt : (B : ℝ) ^ k < (n : ℝ) :=
    (Real.log_lt_log_iff (pow_pos (Nat.cast_pos.mpr (zero_lt_one.trans hB)) _) hnpos).mp hsize'
  have hpLog : Real.log n = a * Real.log p := by rw [hpow, Nat.cast_pow, Real.log_pow]
  have hpn := Real.log_natCast_nonneg p
  have haReal : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have hplog : 2 * Real.log p ≤ Real.log n := by
    rw [hpLog]
    exact mul_le_mul_of_nonneg_right haReal hpn
  have hcpos : 0 < Nat.choose M k := by
    by_contra h
    have hz : Nat.choose M k = 0 := Nat.eq_zero_of_not_pos h
    rw [hz, Nat.cast_zero, Real.log_zero] at hcount
    linarith only [hcount, hplog, hpn]
  have hclog : Real.log (p : ℝ) < Real.log (Nat.choose M k : ℝ) := by linarith only [hcount, hplog]
  have hpc : (p : ℝ) < (Nat.choose M k : ℝ) :=
    (Real.log_lt_log_iff hpos (Nat.cast_pos.mpr hcpos)).mp hclog
  have hnat : B ^ k < n := by exact_mod_cast hlt
  exact ⟨hpow ▸ hnat, (Nat.sub_le p 1).trans_lt (Nat.cast_lt.mp hpc)⟩

/-- Under RH, an odd prime power `n = p ^ a` with `a ≥ 2` and `log n ≥ 70000`
has a prime MR witness at most `(7 / 16) * log n ^ 2`. The selected prime
products fit below `p ^ a` and outnumber the corresponding Fermat kernel. -/
theorem highCoeff_primePow_witness {n p a : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hp2 : p ≠ 2) (ha : 2 ≤ a) (hpow : n = p ^ a) (hRH : RiemannHypothesis)
    (hL : (70000 : ℝ) ≤ Real.log n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 16 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let L := Real.log n
  let b := ⌊(66143 / 100000 : ℝ) * L⌋₊
  let B := b ^ 2
  let u := 2 * Real.log (b : ℝ)
  let M := ⌊((9 / 10 : ℝ) * (b : ℝ) ^ 2) / u⌋₊
  let k := ⌈L / u⌉₊ - 1
  have hLf : 0 < L := by linarith only [hL]
  have hbFloor := Nat.lt_floor_add_one ((66143 / 100000 : ℝ) * L)
  have hbReal : (56 : ℝ) ≤ b := by
    dsimp only [b]
    linarith only [hL, hbFloor]
  have hb : 56 ≤ b := by exact_mod_cast hbReal
  have hB : 1 < B := by
    dsimp only [B]
    nlinarith only [hb]
  have hb1 : 1 < (b : ℝ) := by linarith only [hbReal]
  have hu : 0 < u := mul_pos (by norm_num only) (Real.log_pos hb1)
  have hy : 0 < L / u := div_pos hLf hu
  have hk := (ceil_sub_one_bounds hy).2
  have hsize : (k : ℝ) * Real.log B < L := by
    have hs := (lt_div_iff₀ hu).mp hk
    dsimp only [B, u] at hs ⊢
    rw [Nat.cast_pow, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    exact hs
  have hpi : M ≤ B.primeCounting := by
    have h := high_square_floor_prime_count hRH hb
    simpa only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] using h
  have he := highCoeff_square_selected_count hL
  have hc : L < 2 * Real.log (Nat.choose M k : ℝ) := by
    have ht := Real.log_lt_log (Real.exp_pos (L / 2)) he
    rw [Real.log_exp] at ht
    linarith only [ht]
  obtain ⟨hs, hc'⟩ := highCoeff_primePow_choose hp hpow ha hB hsize hc
  have hdiv : p ^ a ∣ n := hpow.symm ▸ dvd_refl (p ^ a)
  obtain ⟨r, hr, hbR, hf⟩ :=
    exists_prime_primePow_choose_count hn ho hp hp2 (lt_of_lt_of_le (by norm_num only : 0 < 2) ha)
      hdiv B M k hpi hs hc'
  have hscale : 0 ≤ (66143 / 100000 : ℝ) * L := by linarith only [hL]
  have hfloor := Nat.floor_le hscale
  have hsquare := pow_le_pow_left₀ (Nat.cast_nonneg b) hfloor 2
  have hbound : (B : ℝ) ≤ (7 / 16 : ℝ) * L ^ 2 := by
    dsimp only [B]
    rw [Nat.cast_pow]
    nlinarith only [hsquare]
  exact ⟨r, hr, (Nat.cast_le.mpr hbR).trans hbound, hf⟩

/-- Under RH, suppose an odd `n` has a prime-power divisor `p ^ a` with
`a ≥ 2` and logarithmic size between one third of `log n` and `log n`.
For `log n ≥ 70000`, the partial-scale prime-product count gives a prime
MR witness at most `(7 / 16) * log n ^ 2`. -/
theorem highCoeff_primePow_divisor {n p a : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hp2 : p ≠ 2) (ha : 2 ≤ a) (hdiv : p ^ a ∣ n) (hRH : RiemannHypothesis)
    (hL : (70000 : ℝ) ≤ Real.log n) (hlower : Real.log n / 3 ≤ Real.log (p ^ a : ℕ))
    (hupper : Real.log (p ^ a : ℕ) ≤ Real.log n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 16 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let L := Real.log n
  let σ := Real.log (p ^ a : ℕ) / L
  let b := ⌊(66143 / 100000 : ℝ) * L⌋₊
  let B := b ^ 2
  let u := 2 * Real.log (b : ℝ)
  let M := ⌊((9 / 10 : ℝ) * (b : ℝ) ^ 2) / u⌋₊
  let k := ⌈σ * L / u⌉₊ - 1
  have hLf : 0 < L := by linarith only [hL]
  have hσL : σ * L = Real.log (p ^ a : ℕ) := div_mul_cancel₀ _ hLf.ne'
  have hσ : (1 / 3 : ℝ) ≤ σ := by
    dsimp only [σ]
    apply (le_div_iff₀ hLf).mpr
    linarith only [hlower]
  have hσ1 : σ ≤ 1 := by
    dsimp only [σ]
    apply (div_le_iff₀ hLf).mpr
    linarith only [hupper]
  have hσ0 : 0 < σ := by linarith only [hσ]
  have hbFloor := Nat.lt_floor_add_one ((66143 / 100000 : ℝ) * L)
  have hbReal : (56 : ℝ) ≤ b := by
    dsimp only [b]
    linarith only [hL, hbFloor]
  have hb : 56 ≤ b := by exact_mod_cast hbReal
  have hB : 1 < B := by
    dsimp only [B]
    nlinarith only [hb]
  have hb1 : 1 < (b : ℝ) := by linarith only [hbReal]
  have hu : 0 < u := mul_pos (by norm_num only) (Real.log_pos hb1)
  have hy : 0 < σ * L / u := div_pos (mul_pos hσ0 hLf) hu
  have hk := (ceil_sub_one_bounds hy).2
  have hsize : (k : ℝ) * Real.log B < Real.log (p ^ a : ℕ) := by
    have hs := (lt_div_iff₀ hu).mp hk
    dsimp only [B, u] at hs ⊢
    rw [Nat.cast_pow, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [hs, hσL]
  have hpi : M ≤ B.primeCounting := by
    have h := high_square_floor_prime_count hRH hb
    simpa only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] using h
  have he := highCoeff_partial_selected_count hL hσ hσ1
  have hc : Real.log (p ^ a : ℕ) < 2 * Real.log (Nat.choose M k : ℝ) := by
    have ht := Real.log_lt_log (Real.exp_pos (σ * L / 2)) he
    rw [Real.log_exp] at ht
    linarith only [ht, hσL]
  obtain ⟨hs, hc'⟩ := highCoeff_primePow_choose hp (rfl : p ^ a = p ^ a) ha hB hsize hc
  obtain ⟨r, hr, hbR, hf⟩ :=
    exists_prime_primePow_choose_count hn ho hp hp2 (lt_of_lt_of_le (by norm_num only : 0 < 2) ha)
      hdiv B M k hpi hs hc'
  have hscale : 0 ≤ (66143 / 100000 : ℝ) * L := by linarith only [hL]
  have hfloor := Nat.floor_le hscale
  have hsquare := pow_le_pow_left₀ (Nat.cast_nonneg b) hfloor 2
  have hbound : (B : ℝ) ≤ (7 / 16 : ℝ) * L ^ 2 := by
    dsimp only [B]
    rw [Nat.cast_pow]
    nlinarith only [hsquare]
  exact ⟨r, hr, (Nat.cast_le.mpr hbR).trans hbound, hf⟩

/-- Under GRH, an odd composite `n = p ^ 2 * q` with prime `p` and `q`
has a prime MR witness at most `(7 / 16) * log n ^ 2` for `log n ≥ 70000`.
When `q` is large, use its local kernel; otherwise use the local kernel at
`p ^ 2`. The existing triangular profile covers the far high range. -/
theorem highCoeff_squareTimesPrime_witness {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hp : p.Prime) (hq : q.Prime) (hprod : n = p ^ 2 * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (70000 : ℝ) ≤ Real.log n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 16 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hpsq : 1 < p ^ 2 := by nlinarith only [hp.one_lt]
  have hpdiv : p ∣ n := hprod ▸ dvd_mul_of_dvd_left (dvd_pow_self p (by norm_num only)) q
  have hqdiv : q ∣ n := hprod ▸ dvd_mul_left q (p ^ 2)
  have hp2 : p ≠ 2 := ho.ne_two_of_dvd_nat hpdiv
  have hq2 : q ≠ 2 := ho.ne_two_of_dvd_nat hqdiv
  have hdiv : p ^ 2 ∣ n := hprod ▸ dvd_mul_right (p ^ 2) q
  have hlog : Real.log n = Real.log (p ^ 2 : ℕ) + Real.log q := by
    rw [hprod, Nat.cast_mul,
      Real.log_mul (Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt (zero_lt_one.trans hpsq)))
        (Nat.cast_ne_zero.mpr hq.ne_zero)]
  have hupper : Real.log (p ^ 2 : ℕ) ≤ Real.log n := by
    have hqlog := Real.log_natCast_nonneg q
    linarith only [hlog, hqlog]
  by_cases hqLarge : (66143 / 100000 : ℝ) * Real.log n < Real.log q
  · by_cases hU : Real.log n ≤ 40000000000
    · exact highCoeff_largeCofactor_witness hn ho hpsq hq hq2 hprod hGRH.riemann hL hU hqLarge
    · have ht : triangularP04145.T ≤ Real.log n := by
        change (40000000000 : ℝ) ≤ Real.log n
        exact (lt_of_not_ge hU).le
      obtain ⟨r, hr, hb, hf⟩ := exists_prime_triangularProfile triangularP04145 hn ho hc hGRH ht
      have hbound : triangularP04145.C * Real.log n ^ 2 ≤ (7 / 16 : ℝ) * (Real.log n) ^ 2 := by
        change (4145 / 10000 : ℝ) * Real.log n ^ 2 ≤ (7 / 16 : ℝ) * (Real.log n) ^ 2
        nlinarith only [sq_nonneg (Real.log n)]
      exact ⟨r, hr, hb.trans hbound, hf⟩
  · have hlower : Real.log n / 3 ≤ Real.log (p ^ 2 : ℕ) := by
      have hqsmall := le_of_not_gt hqLarge
      linarith only [hlog, hqsmall, hL]
    exact
      highCoeff_primePow_divisor hn ho hp hp2 (by norm_num only : 2 ≤ 2) hdiv hGRH.riemann hL hlower
        hupper

end PseudoPrime.PrimeTestBounds.MillerRabin
