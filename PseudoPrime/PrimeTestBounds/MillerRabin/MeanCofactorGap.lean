/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.MeanScalarCells

/-! # Large-cofactor witness from an average-logarithm gap

Combine the mean-selected prime products, the explicit Stirling estimate and a scalar
gap. The remaining hypotheses are explicit scale, floor, theta and loss budgets.
-/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For positive `P` and `B`, `τ ≥ 4`, the stated prime-supply rounding bound and
the floor bound for `k` imply `(τ / P) * f - 2 ≤ k`. Clear the positive denominator
and absorb the two floor losses using the displayed rational budget. This supplies the
selected-size hypothesis in the large-cofactor gap criterion. -/
theorem mean_selected_size_lower {τ P B f : ℝ} {M k : ℕ} (hB : 0 < B) (hP : 0 < P) (hτ : 4 ≤ τ)
    (hM : B * f ≤ (M : ℝ) + 1) (hround : 4 * B * f + (τ - 4) ≤ P * B)
    (hk : (τ - 4) * M / (P * B) - 1 ≤ k) : (τ / P) * f - 2 ≤ (k : ℝ) := by
  have hden : 0 < P * B := mul_pos hP hB
  have hm := mul_le_mul_of_nonneg_left hM (show 0 ≤ τ - 4 by linarith only [hτ])
  have hnum : τ * B * f - P * B ≤ (τ - 4) * M := by nlinarith only [hm, hround]
  have hdiv := div_le_div_of_nonneg_right hnum hden.le
  have he : (τ * B * f - P * B) / (P * B) = (τ / P) * f - 1 := by
    rw [sub_div, div_self hden.ne']
    have hx : τ * B * f / (P * B) = (τ / P) * f := by
      rw [show τ * B * f = (τ * f) * B by ring, mul_div_mul_right _ _ hB.ne']
      ring
    rw [hx]
  rw [he] at hdiv
  linarith only [hdiv, hk]

/-- For positive `B` and `P`, nonnegative `f`, and `τ ≥ 4`, the two displayed
size conditions and rounding budget give the five conclusions for the floor-selected
prime supply `M` and subset size `k`. Apply the floor inequalities and the preceding
rounding lemma. These bounds supply the mean and selected-size hypotheses together. -/
theorem mean_floor_parameters {τ P B f : ℝ} (hB : 0 < B) (hP : 0 < P) (hf : 0 ≤ f) (hτ : 4 ≤ τ)
    (hsize : τ - 4 ≤ P * B) (hpos : P * B ≤ (τ - 4) * (⌊B * f⌋₊ : ℝ))
    (hround : 4 * B * f + (τ - 4) ≤ P * B) :
    let M := ⌊B * f⌋₊
    let k := ⌊(τ - 4) * M / (P * B)⌋₊
    1 ≤ k ∧ k ≤ M ∧ (M : ℝ) ≤ B * f ∧ (k : ℝ) * (P * B) ≤ (τ - 4) * M ∧ (τ / P) * f - 2 ≤ k := by
  let M := ⌊B * f⌋₊
  let k := ⌊(τ - 4) * M / (P * B)⌋₊
  have hden : 0 < P * B := mul_pos hP hB
  have hx : 0 ≤ (τ - 4) * M / (P * B) :=
    div_nonneg (mul_nonneg (by linarith only [hτ]) (Nat.cast_nonneg M)) hden.le
  have hMk : 1 ≤ (τ - 4) * M / (P * B) :=
    (le_div_iff₀ hden).mpr (by simpa only [one_mul] using hpos)
  have hk0 : 1 ≤ k := (Nat.le_floor_iff hx).mpr (by simpa only [Nat.cast_one] using hMk)
  have hfM : (M : ℝ) ≤ B * f := Nat.floor_le (mul_nonneg hB.le hf)
  have hfloor : B * f ≤ (M : ℝ) + 1 := (Nat.lt_floor_add_one _).le
  have hkfloor : (k : ℝ) ≤ (τ - 4) * M / (P * B) := Nat.floor_le hx
  have hkupper : (τ - 4) * M / (P * B) ≤ M := by
    apply (div_le_iff₀ hden).mpr
    have h := mul_le_mul_of_nonneg_right hsize (Nat.cast_nonneg M : (0 : ℝ) ≤ M)
    nlinarith only [h]
  have hkM : k ≤ M := Nat.cast_le.mp (hkfloor.trans hkupper)
  have hmean : (k : ℝ) * (P * B) ≤ (τ - 4) * M := (le_div_iff₀ hden).mp hkfloor
  have hkfloorlo : (τ - 4) * M / (P * B) - 1 ≤ k := by
    have h := Nat.lt_floor_add_one ((τ - 4) * M / (P * B))
    linarith only [h]
  have hklo : (τ / P) * f - 2 ≤ (k : ℝ) := mean_selected_size_lower hB hP hτ hfloor hround hkfloorlo
  exact ⟨hk0, hkM, hfM, hmean, hklo⟩

/-- For `n = m * q` with an odd prime `q`, the displayed theta, mean, floor and scalar
gap hypotheses produce a rejecting prime at most `b ^ 2`. The mean bound supplies the
binomial base, the Stirling budget supplies the count, and the local kernel gives the
witness. This is the large-cofactor interface before discharging numerical floor estimates. -/
theorem large_cofactor_of_mean_gap {n m q b M k : ℕ} (hn : 1 < n) (ho : Odd n) (hm : 1 < m)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = m * q) {α P a η : ℝ} (hα : 0 < α) (hP : 1 ≤ P)
    (hb : 2002 ≤ b) (hk : 1 ≤ k) (hkM : k ≤ M) (hL : 0 < Real.log n)
    (hfloor : α * Real.log n ≤ (b : ℝ) + 1) (hmargin : 4 ≤ α * Real.log n)
    (hqL : α * Real.log n < Real.log q) (hθB : a * (b : ℝ) ^ 2 ≤ Chebyshev.theta (b ^ 2 : ℕ))
    (hθ : ∀ t ∈ Set.Icc ((b : ℝ) ^ 2 / 16) ((b : ℝ) ^ 2), η * t ≤ Chebyshev.theta t)
    (hupper : Chebyshev.theta (b ^ 2 : ℕ) ≤ P * (b : ℝ) ^ 2)
    (hM :
      (M : ℝ) ≤ (b : ℝ) ^ 2 * (a / Real.log (b ^ 2 : ℕ) + (15 * η / 16) / Real.log (b ^ 2 : ℕ) ^ 2))
    (hmean : (k : ℝ) * (P * (b : ℝ) ^ 2) ≤ (α * Real.log n - 4) * M)
    (hklo :
      (α / P) * Real.log n * (a / Real.log (b ^ 2 : ℕ) + (15 * η / 16) / Real.log (b ^ 2 : ℕ) ^ 2) -
          2 ≤
        k)
    (hgap :
      (1 - α) * Real.log n + 120 <
        (α / P) *
          (a / 2 + ((999 / 1000) * a + (15 * η / 16) / 2) / Real.log (b ^ 2 : ℕ) +
            ((999 / 1000) * (15 * η / 16)) / Real.log (b ^ 2 : ℕ) ^ 2) *
          Real.log n)
    (hloss :
      Real.log (α * Real.log n) - Real.log 4 + Real.log k / 2 + Real.log (2 * Real.pi) / 2 +
          1 / (12 * (k : ℝ)) +
          2 * (Real.log (b ^ 2 : ℕ) / 2 + 999 / 1000) ≤
        120) :
    ∃ r : ℕ, r.Prime ∧ r ≤ b ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let L := Real.log n
  let u := Real.log (b ^ 2 : ℕ)
  let τ := α * L
  have hb0 : 1 < b := by linarith only [hb]
  have hB1 : 1 < b ^ 2 := by nlinarith only [hb0]
  have hB : 32 ≤ b ^ 2 := by nlinarith only [hb]
  have hu0 : 0 < u := Real.log_pos (Nat.one_lt_cast.mpr hB1)
  have hτ : 0 < τ := mul_pos hα hL
  have hlogb : u = 2 * Real.log (b : ℝ) := by
    dsimp only [u]
    rw [Nat.cast_pow, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  have hP' : (b : ℝ) ^ 2 ≤ P * (b : ℝ) ^ 2 := by
    nlinarith only [mul_nonneg (show 0 ≤ P - 1 by linarith only [hP]) (sq_nonneg (b : ℝ))]
  have hbase :=
    mean_log_choose_base (M := M) (k := k) (τ := τ) (δ := 4) (P := P * (b : ℝ) ^ 2)
      (by exact_mod_cast hb) (Nat.zero_lt_of_lt hk) hkM hfloor (by norm_num only) hP' hmean
  have hbase' : u / 2 + (999 / 1000 : ℝ) ≤ Real.log (((M + 1 - k : ℕ) : ℝ) / k) + 1 := by
    linarith only [hbase, hlogb]
  have hlog : Real.log n = Real.log m + Real.log q := by
    rw [hprod, Nat.cast_mul,
      Real.log_mul (Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt (zero_lt_one.trans hm)))
        (Nat.cast_ne_zero.mpr hq.ne_zero)]
  have hsmall : Real.log m < (1 - α) * L := by
    dsimp only [L]
    linarith only [hlog, hqL]
  have hbudget := mean_log_budget_of_gap hu0 hklo hgap hsmall hloss
  have hc :=
    mean_count_of_log_budget hτ (by norm_num only : (0 : ℝ) < 4) (Nat.zero_lt_of_lt hm)
      (Nat.ne_zero_of_lt (Nat.zero_lt_of_lt hk)) hkM hbase' hbudget
  exact
    large_cofactor_of_theta hn ho hm hq hq2 hprod (b ^ 2) M k τ 4 (P * (b : ℝ) ^ 2) a η hB hk
      (hk.trans hkM) hτ.le (by norm_num only) (by linarith only [hmargin]) hqL.le
      (by simpa only [Nat.cast_pow] using hθB) (by simpa only [Nat.cast_pow] using hθ)
      (by simpa only [Nat.cast_pow] using hupper) (by simpa only [Nat.cast_pow] using hM)
      (by simpa only [Nat.cast_pow] using hmean) hc

/-- For `n = m * q` with an odd prime `q`, the displayed theta and scalar budgets
produce a rejecting prime at most `b ^ 2`, using the two floor-selected parameters.
The floor lemma discharges the prime-supply and mean constraints, and the preceding gap
criterion supplies the witness. This reduces the branch to explicit real inequalities. -/
theorem large_cofactor_of_mean_floors {n m q b : ℕ} (hn : 1 < n) (ho : Odd n) (hm : 1 < m)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = m * q) {α P a η : ℝ} (hα : 0 < α) (hP : 1 ≤ P)
    (hb : 2002 ≤ b) (hL : 0 < Real.log n) (hfloor : α * Real.log n ≤ (b : ℝ) + 1)
    (hmargin : 4 ≤ α * Real.log n) (hqL : α * Real.log n < Real.log q)
    (hθB : a * (b : ℝ) ^ 2 ≤ Chebyshev.theta (b ^ 2 : ℕ))
    (hθ : ∀ t ∈ Set.Icc ((b : ℝ) ^ 2 / 16) ((b : ℝ) ^ 2), η * t ≤ Chebyshev.theta t)
    (hupper : Chebyshev.theta (b ^ 2 : ℕ) ≤ P * (b : ℝ) ^ 2)
    (hf : 0 ≤ a / Real.log (b ^ 2 : ℕ) + (15 * η / 16) / Real.log (b ^ 2 : ℕ) ^ 2)
    (hsize : α * Real.log n - 4 ≤ P * (b : ℝ) ^ 2)
    (hpos :
      P * (b : ℝ) ^ 2 ≤
        (α * Real.log n - 4) *
          (⌊(b : ℝ) ^ 2 * (a / Real.log (b ^ 2 : ℕ) + (15 * η / 16) / Real.log (b ^ 2 : ℕ) ^ 2)⌋₊ :
            ℝ))
    (hround :
      4 * (b : ℝ) ^ 2 * (a / Real.log (b ^ 2 : ℕ) + (15 * η / 16) / Real.log (b ^ 2 : ℕ) ^ 2) +
          (α * Real.log n - 4) ≤
        P * (b : ℝ) ^ 2)
    (hgap :
      (1 - α) * Real.log n + 120 <
        (α / P) *
          (a / 2 + ((999 / 1000) * a + (15 * η / 16) / 2) / Real.log (b ^ 2 : ℕ) +
            ((999 / 1000) * (15 * η / 16)) / Real.log (b ^ 2 : ℕ) ^ 2) *
          Real.log n)
    (hloss :
      let M :=
        ⌊(b : ℝ) ^ 2 * (a / Real.log (b ^ 2 : ℕ) + (15 * η / 16) / Real.log (b ^ 2 : ℕ) ^ 2)⌋₊
      let k := ⌊(α * Real.log n - 4) * M / (P * (b : ℝ) ^ 2)⌋₊
      Real.log (α * Real.log n) - Real.log 4 + Real.log k / 2 + Real.log (2 * Real.pi) / 2 +
          1 / (12 * (k : ℝ)) +
          2 * (Real.log (b ^ 2 : ℕ) / 2 + 999 / 1000) ≤
        120) :
    ∃ r : ℕ, r.Prime ∧ r ≤ b ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let B : ℝ := (b : ℝ) ^ 2
  let f : ℝ := a / Real.log (b ^ 2 : ℕ) + (15 * η / 16) / Real.log (b ^ 2 : ℕ) ^ 2
  let τ := α * Real.log n
  let M := ⌊B * f⌋₊
  let k := ⌊(τ - 4) * M / (P * B)⌋₊
  have hB : 0 < B := pow_pos (Nat.cast_pos.mpr (by linarith only [hb])) 2
  have hp0 : 0 < P := by linarith only [hP]
  have ⟨hk0, hkM, hM, hmean, hklo⟩ := mean_floor_parameters hB hp0 hf hmargin hsize hpos hround
  have he : (τ / P) * f = (α / P) * Real.log n * f := by
    dsimp only [τ]
    ring
  rw [he] at hklo
  exact
    large_cofactor_of_mean_gap hn ho hm hq hq2 hprod hα hP hb hk0 hkM hL hfloor hmargin hqL hθB hθ
      hupper hM hmean hklo hgap hloss

end PseudoPrime.PrimeTestBounds.MillerRabin
