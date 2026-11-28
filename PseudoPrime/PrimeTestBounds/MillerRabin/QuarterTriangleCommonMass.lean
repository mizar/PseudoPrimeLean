/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTriangleIndicator
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrimeWindow600
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrimeWindow626

/-! # Common-sign prime mass in the section 86 triangle window -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For every radius at least 287, each positive integer in the translated window is coprime
to any prime above the fourth power of the radius. -/
theorem triangle_window_gcd_of_large {R : ℝ} (hl : 287 ≤ R) {p b : ℕ} (hp : p.Prime)
    (hlarge : R ^ 4 < p)
    (hb : b ∈ Finset.Ioc ⌊Real.exp (2 * Real.log R)⌋₊ ⌊Real.exp (2 * Real.log R + 5)⌋₊) :
    (b : ℤ).gcd p = 1 := by
  have hpos : 0 < R := by linarith only [hl]
  have he : Real.exp (2 * Real.log R) = R ^ 2 := by
    rw [two_mul, Real.exp_add, Real.exp_log hpos, sq]
  obtain ⟨ha, hc⟩ := Finset.mem_Ioc.mp hb
  have h₁ := (Nat.floor_lt (Real.exp_pos _).le).mp ha
  have h₂ := (Nat.le_floor_iff (Real.exp_pos _).le).mp hc
  rw [Real.exp_add, he, mul_comm] at h₂
  rw [he] at h₁
  have hE := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 5
  rw [← Real.exp_natCast_mul] at hE
  norm_num only [Nat.cast_ofNat, mul_one] at hE
  have hR : Real.exp 5 ≤ R ^ 2 :=
    hE.trans
      ((by norm_num only : (243 : ℝ) ≤ 287 ^ 2).trans (pow_le_pow_left₀ (by norm_num only) hl 2))
  have h₃ := mul_le_mul_of_nonneg_right hR (sq_nonneg R)
  rw [← pow_add] at h₃
  have hbp : b < p := Nat.cast_lt.mp (h₂.trans_lt (h₃.trans_lt hlarge))
  have hb0 : 0 < b := Nat.cast_pos.mp ((sq_pos_of_pos hpos).trans h₁)
  exact (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hb0 hbp)).symm

/-- Every integer in the translated window is coprime to each prime above
the fourth power of the radius in the radius interval from 287 to 313. -/
theorem triangle_window_gcd_313 {R : ℝ} (hl : 287 ≤ R) (_hu : R ≤ 313) {p b : ℕ} (hp : p.Prime)
    (hlarge : R ^ 4 < p)
    (hb : b ∈ Finset.Ioc ⌊Real.exp (2 * Real.log R)⌋₊ ⌊Real.exp (2 * Real.log R + 5)⌋₊) :
    (b : ℤ).gcd p = 1 := by exact triangle_window_gcd_of_large hl hp hlarge hb

/-- Every integer in the translated window is coprime to each prime above
the fourth power of the radius in the radius interval from 287 to 300. -/
theorem triangle_window_gcd_300 {R : ℝ} (hl : 287 ≤ R) (hu : R ≤ 300) {p b : ℕ} (hp : p.Prime)
    (hlarge : R ^ 4 < p)
    (hb : b ∈ Finset.Ioc ⌊Real.exp (2 * Real.log R)⌋₊ ⌊Real.exp (2 * Real.log R + 5)⌋₊) :
    (b : ℤ).gcd p = 1 := by
  exact triangle_window_gcd_313 hl (hu.trans (by norm_num only)) hp hlarge hb

/-- Restrict the wide-window result through radius 300 to section 86. -/
theorem triangle_window_gcd {R : ℝ} (hl : 287 ≤ R) (hu : R ≤ 288) {p b : ℕ} (hp : p.Prime)
    (hlarge : R ^ 4 < p)
    (hb : b ∈ Finset.Ioc ⌊Real.exp (2 * Real.log R)⌋₊ ⌊Real.exp (2 * Real.log R + 5)⌋₊) :
    (b : ℤ).gcd p = 1 := by
  exact triangle_window_gcd_300 hl (hu.trans (by norm_num only)) hp hlarge hb

/-- The normalized character sum in Mellin coordinates equals the signed
window sum with the same shifted triangle weight as the principal lower bound. -/
theorem triangle_signed_weight_sum {k : ℕ} (χ : DirichletCharacter ℂ k) (v : ℝ) :
    let s := Finset.Ioc ⌊Real.exp v⌋₊ ⌊Real.exp (v + 5)⌋₊
    let x := Real.exp (v + 5 / 2)
    (2 / 5) *
        |∑ b ∈ s,
            ArithmeticFunction.vonMangoldt b / Real.sqrt b * (χ (b : ZMod k)).re *
              LLS.PaperStatements.triangularKernelProfile (5 / 4) (b / x)| =
      |∑ b ∈ s,
          shiftedTriangle (5 / 2) (Real.log b - v) / Real.sqrt b *
            ArithmeticFunction.vonMangoldt b *
            (χ (b : ZMod k)).re| := by
  intro s x
  rw [← abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 2 / 5), ← abs_mul, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro b hb
  have hp : 0 < b := (Nat.zero_le _).trans_lt (Finset.mem_Ioc.mp hb).1
  rw [← triangle_profile_shift (Nat.cast_pos.mpr hp) v]
  dsimp only [x]
  ring

/-- Through radius 316, the translated triangle bounds the mass on common Jacobi signs below. -/
theorem triangle_common_mass_316 {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hn : 1 < n) (ho : Odd n) (hs : Squarefree n) (he : n = p * q * r) (hp : Odd p) (hq : Odd q)
    (hr : Odd r) (hk : p - 1 ∣ n - 1) (hj : q - 1 ∣ n - 1) (hm : r - 1 ∣ n - 1)
    (hv : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hw : padicValNat 2 (r - 1) = padicValNat 2 (p - 1))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {R : ℝ} (hR : 287 ≤ R)
    (hU : R ≤ 316) (hL : Real.log n = 2 * R) (hRH : RiemannHypothesis) (hP : R ^ 4 < p)
    (hQ : R ^ 4 < q) (hT : R ^ 4 < r)
    (hb :
      ∀ b : ℕ, b.Prime → b ≤ ⌊Real.exp (5 / 2)⌋₊ → PrimeTest.StrongMillerRabinPass n (b : ZMod n)) :
    let v := 2 * Real.log R
    let s := Finset.Ioc ⌊Real.exp v⌋₊ ⌊Real.exp (v + 5)⌋₊
    let w (b : ℕ) :=
      shiftedTriangle (5 / 2) (Real.log b - v) / Real.sqrt b * ArithmeticFunction.vonMangoldt b
    2343 / 1600 * R + 4197 / 1000 <
      ∑ b ∈ s.filter (fun (b : ℕ) => jacobiSym b p = jacobiSym b q ∧ jacobiSym b q = jacobiSym b r),
        w b := by
  intro v s w
  let S {k : ℕ} (χ : DirichletCharacter ℂ k) := ∑ b ∈ s, w b * (χ (b : ZMod k)).re
  let A := S (NumberTheory.complexJacobiNumeratorCharacter _ (hp.mul hq))
  let B := S (NumberTheory.complexJacobiNumeratorCharacter _ (hp.mul hr))
  let C := S (NumberTheory.complexJacobiNumeratorCharacter _ (hq.mul hr))
  have hf := triangle_triple_window hn ho hs he hp hq hr hk hj hm hv hw hGRH hR hb
  dsimp only at hf
  simp_rw [triangle_signed_weight_sum] at hf
  change |A| + |B| + |C| < _ at hf
  rw [hL] at hf
  have hsum :=
    triangle_pair_indicator_sum hp hq hr s w
      (fun b ht =>
        ⟨triangle_window_gcd_of_large hR (Fact.out : p.Prime) hP ht,
          triangle_window_gcd_of_large hR (Fact.out : q.Prime) hQ ht,
          triangle_window_gcd_of_large hR (Fact.out : r.Prime) hT ht⟩)
  change 4 * _ = (∑ b ∈ s, w b) + A + B + C at hsum
  have hm :=
    if h : R ≤ 313 then triangle_mangoldt_lower_313 hRH hR h
    else triangle_mangoldt_lower_316 hRH (le_of_not_ge h) hU
  have hm0 : 3943 / 400 * R < ∑ b ∈ s, w b :=
    hm.trans_eq (triangle_branch_sum v (fun b => ArithmeticFunction.vonMangoldt b)).symm
  linarith only [hsum, hm0, hf, neg_le_abs A, neg_le_abs B, neg_le_abs C]

/-- In the radius interval [287,300], the finite mass on common Jacobi signs
exceeds the principal lower bound minus the three signed costs, divided by four. -/
theorem triangle_common_mass_313 {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hn : 1 < n) (ho : Odd n) (hs : Squarefree n) (he : n = p * q * r) (hp : Odd p) (hq : Odd q)
    (hr : Odd r) (hk : p - 1 ∣ n - 1) (hj : q - 1 ∣ n - 1) (hm : r - 1 ∣ n - 1)
    (hv : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hw : padicValNat 2 (r - 1) = padicValNat 2 (p - 1))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {R : ℝ} (hR : 287 ≤ R)
    (hU : R ≤ 313) (hL : Real.log n = 2 * R) (hRH : RiemannHypothesis) (hP : R ^ 4 < p)
    (hQ : R ^ 4 < q) (hT : R ^ 4 < r)
    (hb :
      ∀ b : ℕ, b.Prime → b ≤ ⌊Real.exp (5 / 2)⌋₊ → PrimeTest.StrongMillerRabinPass n (b : ZMod n)) :
    let v := 2 * Real.log R
    let s := Finset.Ioc ⌊Real.exp v⌋₊ ⌊Real.exp (v + 5)⌋₊
    let w (b : ℕ) :=
      shiftedTriangle (5 / 2) (Real.log b - v) / Real.sqrt b * ArithmeticFunction.vonMangoldt b
    2343 / 1600 * R + 4197 / 1000 <
      ∑ b ∈ s.filter (fun (b : ℕ) => jacobiSym b p = jacobiSym b q ∧ jacobiSym b q = jacobiSym b r),
        w b := by
  exact
    triangle_common_mass_316 hn ho hs he hp hq hr hk hj hm hv hw hGRH hR
      (hU.trans (by norm_num only)) hL hRH hP hQ hT hb

/-- In the radius interval [287,300], the finite mass on common Jacobi signs
exceeds the principal lower bound minus the three signed costs, divided by four. -/
theorem triangle_common_mass_300 {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hn : 1 < n) (ho : Odd n) (hs : Squarefree n) (he : n = p * q * r) (hp : Odd p) (hq : Odd q)
    (hr : Odd r) (hk : p - 1 ∣ n - 1) (hj : q - 1 ∣ n - 1) (hm : r - 1 ∣ n - 1)
    (hv : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hw : padicValNat 2 (r - 1) = padicValNat 2 (p - 1))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {R : ℝ} (hR : 287 ≤ R)
    (hU : R ≤ 300) (hL : Real.log n = 2 * R) (hRH : RiemannHypothesis) (hP : R ^ 4 < p)
    (hQ : R ^ 4 < q) (hT : R ^ 4 < r)
    (hb :
      ∀ b : ℕ, b.Prime → b ≤ ⌊Real.exp (5 / 2)⌋₊ → PrimeTest.StrongMillerRabinPass n (b : ZMod n)) :
    let v := 2 * Real.log R
    let s := Finset.Ioc ⌊Real.exp v⌋₊ ⌊Real.exp (v + 5)⌋₊
    let w (b : ℕ) :=
      shiftedTriangle (5 / 2) (Real.log b - v) / Real.sqrt b * ArithmeticFunction.vonMangoldt b
    2343 / 1600 * R + 4197 / 1000 <
      ∑ b ∈ s.filter (fun (b : ℕ) => jacobiSym b p = jacobiSym b q ∧ jacobiSym b q = jacobiSym b r),
        w b := by
  exact
    triangle_common_mass_313 hn ho hs he hp hq hr hk hj hm hv hw hGRH hR
      (hU.trans (by norm_num only)) hL hRH hP hQ hT hb

/-- Restrict the wide-window result through radius 300 to section 86. -/
theorem triangle_common_mass_576 {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hn : 1 < n) (ho : Odd n) (hs : Squarefree n) (he : n = p * q * r) (hp : Odd p) (hq : Odd q)
    (hr : Odd r) (hk : p - 1 ∣ n - 1) (hj : q - 1 ∣ n - 1) (hm : r - 1 ∣ n - 1)
    (hv : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hw : padicValNat 2 (r - 1) = padicValNat 2 (p - 1))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {R : ℝ} (hR : 287 ≤ R)
    (hU : R ≤ 288) (hL : Real.log n = 2 * R) (hRH : RiemannHypothesis) (hP : R ^ 4 < p)
    (hQ : R ^ 4 < q) (hT : R ^ 4 < r)
    (hb :
      ∀ b : ℕ, b.Prime → b ≤ ⌊Real.exp (5 / 2)⌋₊ → PrimeTest.StrongMillerRabinPass n (b : ZMod n)) :
    let v := 2 * Real.log R
    let s := Finset.Ioc ⌊Real.exp v⌋₊ ⌊Real.exp (v + 5)⌋₊
    let w (b : ℕ) :=
      shiftedTriangle (5 / 2) (Real.log b - v) / Real.sqrt b * ArithmeticFunction.vonMangoldt b
    2343 / 1600 * R + 4197 / 1000 <
      ∑ b ∈ s.filter (fun (b : ℕ) => jacobiSym b p = jacobiSym b q ∧ jacobiSym b q = jacobiSym b r),
        w b := by
  exact
    triangle_common_mass_300 hn ho hs he hp hq hr hk hj hm hv hw hGRH hR
      (hU.trans (by norm_num only)) hL hRH hP hQ hT hb

/-- Through radius 316, the translated triangle bounds the common-sign prime mass below. -/
theorem triangle_common_prime_mass_316 {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hn : 1 < n) (ho : Odd n) (hs : Squarefree n) (he : n = p * q * r) (hp : Odd p) (hq : Odd q)
    (hr : Odd r) (hk : p - 1 ∣ n - 1) (hj : q - 1 ∣ n - 1) (hm : r - 1 ∣ n - 1)
    (hv : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hw : padicValNat 2 (r - 1) = padicValNat 2 (p - 1))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {R : ℝ} (hR : 287 ≤ R)
    (hU : R ≤ 316) (hL : Real.log n = 2 * R) (hRH : RiemannHypothesis) (hP : R ^ 4 < p)
    (hQ : R ^ 4 < q) (hT : R ^ 4 < r)
    (hb :
      ∀ b : ℕ, b.Prime → b ≤ ⌊Real.exp (5 / 2)⌋₊ → PrimeTest.StrongMillerRabinPass n (b : ZMod n)) :
    let v := 2 * Real.log R
    let s := Finset.Ioc ⌊Real.exp v⌋₊ ⌊Real.exp (v + 5)⌋₊
    let w (b : ℕ) :=
      shiftedTriangle (5 / 2) (Real.log b - v) / Real.sqrt b * ArithmeticFunction.vonMangoldt b
    73 / 50 * R <
      ∑
        b ∈
          s.filter
            (fun (b : ℕ) =>
              (jacobiSym b p = jacobiSym b q ∧ jacobiSym b q = jacobiSym b r) ∧ b.Prime),
        w b := by
  intro v s w
  let good :=
    s.filter (fun (b : ℕ) => jacobiSym b p = jacobiSym b q ∧ jacobiSym b q = jacobiSym b r)
  have ha :=
    triangle_common_mass_316 hn ho hs he hp hq hr hk hj hm hv hw hGRH hR hU hL hRH hP hQ hT hb
  change _ < ∑ b ∈ good, w b at ha
  have hr0 : 0 < R := by linarith only [hR]
  have hx : Real.exp v = R ^ 2 := by
    dsimp only [v]; rw [two_mul, Real.exp_add, Real.exp_log hr0, sq]
  let bad := good.filter (fun b => ¬b.Prime)
  have hmem {b : ℕ} (hh : b ∈ bad) : b ∈ s := (Finset.mem_filter.mp (Finset.mem_filter.mp hh).1).1
  have hbad :=
    triangle_mangoldt_nonprime_316 hR hU bad (fun b hh => (Finset.mem_filter.mp hh).2)
      (fun b => Real.log b - v)
      (fun b hh => hx ▸ (Nat.floor_lt (Real.exp_pos _).le).mp (Finset.mem_Ioc.mp (hmem hh)).1)
      (fun b hh => by
        rw [← hx, mul_comm, ← Real.exp_add]
        exact (Nat.le_floor_iff (Real.exp_pos _).le).mp (Finset.mem_Ioc.mp (hmem hh)).2)
  simp_rw [mul_comm (ArithmeticFunction.vonMangoldt _) _] at hbad
  change (∑ b ∈ bad, w b) < 5 at hbad
  have ht := Finset.sum_filter_add_sum_filter_not good Nat.Prime w
  have heq :=
    Finset.filter_filter (s := s) (p := fun (b : ℕ) =>
      jacobiSym b p = jacobiSym b q ∧ jacobiSym b q = jacobiSym b r) (q := Nat.Prime)
  rw [← heq]
  change _ < ∑ b ∈ good.filter Nat.Prime, w b
  change _ + (∑ b ∈ bad, w b) = _ at ht
  linarith only [ha, hbad, ht, hR]

/-- Removing all nonprime contributions leaves more than 73R/50 in
common-sign primes in the window through radius 300. -/
theorem triangle_common_prime_mass_313 {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hn : 1 < n) (ho : Odd n) (hs : Squarefree n) (he : n = p * q * r) (hp : Odd p) (hq : Odd q)
    (hr : Odd r) (hk : p - 1 ∣ n - 1) (hj : q - 1 ∣ n - 1) (hm : r - 1 ∣ n - 1)
    (hv : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hw : padicValNat 2 (r - 1) = padicValNat 2 (p - 1))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {R : ℝ} (hR : 287 ≤ R)
    (hU : R ≤ 313) (hL : Real.log n = 2 * R) (hRH : RiemannHypothesis) (hP : R ^ 4 < p)
    (hQ : R ^ 4 < q) (hT : R ^ 4 < r)
    (hb :
      ∀ b : ℕ, b.Prime → b ≤ ⌊Real.exp (5 / 2)⌋₊ → PrimeTest.StrongMillerRabinPass n (b : ZMod n)) :
    let v := 2 * Real.log R
    let s := Finset.Ioc ⌊Real.exp v⌋₊ ⌊Real.exp (v + 5)⌋₊
    let w (b : ℕ) :=
      shiftedTriangle (5 / 2) (Real.log b - v) / Real.sqrt b * ArithmeticFunction.vonMangoldt b
    73 / 50 * R <
      ∑
        b ∈
          s.filter
            (fun (b : ℕ) =>
              (jacobiSym b p = jacobiSym b q ∧ jacobiSym b q = jacobiSym b r) ∧ b.Prime),
        w b := by
  exact
    triangle_common_prime_mass_316 hn ho hs he hp hq hr hk hj hm hv hw hGRH hR
      (hU.trans (by norm_num only)) hL hRH hP hQ hT hb

/-- Removing all nonprime contributions leaves more than 73R/50 in
common-sign primes in the window through radius 300. -/
theorem triangle_common_prime_mass_300 {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hn : 1 < n) (ho : Odd n) (hs : Squarefree n) (he : n = p * q * r) (hp : Odd p) (hq : Odd q)
    (hr : Odd r) (hk : p - 1 ∣ n - 1) (hj : q - 1 ∣ n - 1) (hm : r - 1 ∣ n - 1)
    (hv : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hw : padicValNat 2 (r - 1) = padicValNat 2 (p - 1))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {R : ℝ} (hR : 287 ≤ R)
    (hU : R ≤ 300) (hL : Real.log n = 2 * R) (hRH : RiemannHypothesis) (hP : R ^ 4 < p)
    (hQ : R ^ 4 < q) (hT : R ^ 4 < r)
    (hb :
      ∀ b : ℕ, b.Prime → b ≤ ⌊Real.exp (5 / 2)⌋₊ → PrimeTest.StrongMillerRabinPass n (b : ZMod n)) :
    let v := 2 * Real.log R
    let s := Finset.Ioc ⌊Real.exp v⌋₊ ⌊Real.exp (v + 5)⌋₊
    let w (b : ℕ) :=
      shiftedTriangle (5 / 2) (Real.log b - v) / Real.sqrt b * ArithmeticFunction.vonMangoldt b
    73 / 50 * R <
      ∑
        b ∈
          s.filter
            (fun (b : ℕ) =>
              (jacobiSym b p = jacobiSym b q ∧ jacobiSym b q = jacobiSym b r) ∧ b.Prime),
        w b := by
  exact
    triangle_common_prime_mass_313 hn ho hs he hp hq hr hk hj hm hv hw hGRH hR
      (hU.trans (by norm_num only)) hL hRH hP hQ hT hb

/-- Restrict the wide-window result through radius 300 to section 86. -/
theorem triangle_common_prime_mass_576 {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hn : 1 < n) (ho : Odd n) (hs : Squarefree n) (he : n = p * q * r) (hp : Odd p) (hq : Odd q)
    (hr : Odd r) (hk : p - 1 ∣ n - 1) (hj : q - 1 ∣ n - 1) (hm : r - 1 ∣ n - 1)
    (hv : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hw : padicValNat 2 (r - 1) = padicValNat 2 (p - 1))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {R : ℝ} (hR : 287 ≤ R)
    (hU : R ≤ 288) (hL : Real.log n = 2 * R) (hRH : RiemannHypothesis) (hP : R ^ 4 < p)
    (hQ : R ^ 4 < q) (hT : R ^ 4 < r)
    (hb :
      ∀ b : ℕ, b.Prime → b ≤ ⌊Real.exp (5 / 2)⌋₊ → PrimeTest.StrongMillerRabinPass n (b : ZMod n)) :
    let v := 2 * Real.log R
    let s := Finset.Ioc ⌊Real.exp v⌋₊ ⌊Real.exp (v + 5)⌋₊
    let w (b : ℕ) :=
      shiftedTriangle (5 / 2) (Real.log b - v) / Real.sqrt b * ArithmeticFunction.vonMangoldt b
    73 / 50 * R <
      ∑
        b ∈
          s.filter
            (fun (b : ℕ) =>
              (jacobiSym b p = jacobiSym b q ∧ jacobiSym b q = jacobiSym b r) ∧ b.Prime),
        w b := by
  exact
    triangle_common_prime_mass_300 hn ho hs he hp hq hr hk hj hm hv hw hGRH hR
      (hU.trans (by norm_num only)) hL hRH hP hQ hT hb

/-- The actual common-sign primes in the translated window supply a fourfold
Euler saving strictly above 1119/50000 on the log interval [574,576]. -/
theorem common_prime_euler_saving_576 {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hn : 1 < n) (ho : Odd n) (hs : Squarefree n) (he : n = p * q * r) (hp : Odd p) (hq : Odd q)
    (hr : Odd r) (hk : p - 1 ∣ n - 1) (hj : q - 1 ∣ n - 1) (hm : r - 1 ∣ n - 1)
    (hv : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hw : padicValNat 2 (r - 1) = padicValNat 2 (p - 1))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {R : ℝ} (hR : 287 ≤ R)
    (hU : R ≤ 288) (hL : Real.log n = 2 * R) (hRH : RiemannHypothesis) (hP : R ^ 4 < p)
    (hQ : R ^ 4 < q) (hT : R ^ 4 < r)
    (hb :
      ∀ b : ℕ, b.Prime → b ≤ ⌊Real.exp (5 / 2)⌋₊ → PrimeTest.StrongMillerRabinPass n (b : ZMod n)) :
    let v := 2 * Real.log R
    let s := Finset.Ioc ⌊Real.exp v⌋₊ ⌊Real.exp (v + 5)⌋₊
    let good :=
      s.filter
        (fun (b : ℕ) => (jacobiSym b p = jacobiSym b q ∧ jacobiSym b q = jacobiSym b r) ∧ b.Prime)
    1119 / 50000 < 4 * ∑ b ∈ good, Real.log b * quarterEulerWeight570 b := by
  intro v s good
  have hr0 : 0 < R := by linarith only [hR]
  have hx : Real.exp v = R ^ 2 := by
    dsimp only [v]; rw [two_mul, Real.exp_add, Real.exp_log hr0, sq]
  have hm0 :=
    triangle_common_prime_mass_576 hn ho hs he hp hq hr hk hj hm hv hw hGRH hR hU hL hRH hP hQ hT hb
  apply window_euler_saving_576 hR hU good
  · intro b hh
    rw [← hx]
    exact
      ((Nat.floor_lt (Real.exp_pos _).le).mp (Finset.mem_Ioc.mp (Finset.mem_filter.mp hh).1).1).le
  · intro b hh
    have ht := Finset.mem_Ioc.mp (Finset.mem_filter.mp hh).1
    have hbpos : 0 < b := (Nat.zero_le _).trans_lt ht.1
    have hh' :=
      (Real.log_le_iff_le_exp (Nat.cast_pos.mpr hbpos)).mpr
        ((Nat.le_floor_iff (Real.exp_pos _).le).mp ht.2)
    exact sub_le_iff_le_add.mpr (hh'.trans_eq (add_comm v 5))
  · apply hm0.le.trans_eq
    apply Finset.sum_congr rfl
    intro b hh
    have hprime : b.Prime := (Finset.mem_filter.mp hh).2.2
    dsimp only
    rw [ArithmeticFunction.vonMangoldt_apply_prime hprime, mul_comm]

/-- The actual common-sign primes in the translated window supply a fourfold
Euler saving strictly above 1119/50000 on the log interval [574,576]. -/
theorem common_prime_euler_saving_600 {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hn : 1 < n) (ho : Odd n) (hs : Squarefree n) (he : n = p * q * r) (hp : Odd p) (hq : Odd q)
    (hr : Odd r) (hk : p - 1 ∣ n - 1) (hj : q - 1 ∣ n - 1) (hm : r - 1 ∣ n - 1)
    (hv : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hw : padicValNat 2 (r - 1) = padicValNat 2 (p - 1))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {R : ℝ} (hR : 292 ≤ R)
    (hU : R ≤ 300) (hL : Real.log n = 2 * R) (hRH : RiemannHypothesis) (hP : R ^ 4 < p)
    (hQ : R ^ 4 < q) (hT : R ^ 4 < r)
    (hb :
      ∀ b : ℕ, b.Prime → b ≤ ⌊Real.exp (5 / 2)⌋₊ → PrimeTest.StrongMillerRabinPass n (b : ZMod n)) :
    let v := 2 * Real.log R
    let s := Finset.Ioc ⌊Real.exp v⌋₊ ⌊Real.exp (v + 5)⌋₊
    let good :=
      s.filter
        (fun (b : ℕ) => (jacobiSym b p = jacobiSym b q ∧ jacobiSym b q = jacobiSym b r) ∧ b.Prime)
    (if R ≤ 299 then 0.02169 else 0.02179) <
      4 * ∑ b ∈ good, Real.log b * quarterEulerWeight570 b := by
  intro v s good
  have hr0 : 0 < R := by linarith only [hR]
  have hx : Real.exp v = R ^ 2 := by
    dsimp only [v]; rw [two_mul, Real.exp_add, Real.exp_log hr0, sq]
  have hm0 :=
    triangle_common_prime_mass_300 hn ho hs he hp hq hr hk hj hm hv hw hGRH (by linarith only [hR])
      hU hL hRH hP hQ hT hb
  apply window_euler_saving_600 hR hU good
  · intro b hh
    rw [← hx]
    exact
      ((Nat.floor_lt (Real.exp_pos _).le).mp (Finset.mem_Ioc.mp (Finset.mem_filter.mp hh).1).1).le
  · intro b hh
    have ht := Finset.mem_Ioc.mp (Finset.mem_filter.mp hh).1
    have hbpos : 0 < b := (Nat.zero_le _).trans_lt ht.1
    have hh' :=
      (Real.log_le_iff_le_exp (Nat.cast_pos.mpr hbpos)).mpr
        ((Nat.le_floor_iff (Real.exp_pos _).le).mp ht.2)
    exact sub_le_iff_le_add.mpr (hh'.trans_eq (add_comm v 5))
  · apply hm0.le.trans_eq
    apply Finset.sum_congr rfl
    intro b hh
    have hprime : b.Prime := (Finset.mem_filter.mp hh).2.2
    dsimp only
    rw [ArithmeticFunction.vonMangoldt_apply_prime hprime, mul_comm]

/-- On radii 300 through 316, common-sign primes in the translated window supply
an Euler saving strictly above 0.02085. -/
theorem common_prime_euler_saving_to632 {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hn : 1 < n) (ho : Odd n) (hs : Squarefree n) (he : n = p * q * r) (hp : Odd p) (hq : Odd q)
    (hr : Odd r) (hk : p - 1 ∣ n - 1) (hj : q - 1 ∣ n - 1) (hm : r - 1 ∣ n - 1)
    (hv : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hw : padicValNat 2 (r - 1) = padicValNat 2 (p - 1))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {R : ℝ} (hR : 300 ≤ R)
    (hU : R ≤ 316) (hL : Real.log n = 2 * R) (hRH : RiemannHypothesis) (hP : R ^ 4 < p)
    (hQ : R ^ 4 < q) (hT : R ^ 4 < r)
    (hb :
      ∀ b : ℕ, b.Prime → b ≤ ⌊Real.exp (5 / 2)⌋₊ → PrimeTest.StrongMillerRabinPass n (b : ZMod n)) :
    let v := 2 * Real.log R
    let s := Finset.Ioc ⌊Real.exp v⌋₊ ⌊Real.exp (v + 5)⌋₊
    let good :=
      s.filter
        (fun (b : ℕ) => (jacobiSym b p = jacobiSym b q ∧ jacobiSym b q = jacobiSym b r) ∧ b.Prime)
    0.02085 < 4 * ∑ b ∈ good, Real.log b * quarterEulerWeight570 b := by
  intro v s good
  have hr0 : 0 < R := by linarith only [hR]
  have hx : Real.exp v = R ^ 2 := by
    dsimp only [v]; rw [two_mul, Real.exp_add, Real.exp_log hr0, sq]
  have hm0 :=
    triangle_common_prime_mass_316 hn ho hs he hp hq hr hk hj hm hv hw hGRH (by linarith only [hR])
      hU hL hRH hP hQ hT hb
  have hsave :=
    if h : R ≤ 313 then window_euler_saving_626 hR h good
    else window_euler_saving_316 (le_of_not_ge h) hU good
  apply hsave
  · intro b hh
    rw [← hx]
    exact
      ((Nat.floor_lt (Real.exp_pos _).le).mp (Finset.mem_Ioc.mp (Finset.mem_filter.mp hh).1).1).le
  · intro b hh
    have ht := Finset.mem_Ioc.mp (Finset.mem_filter.mp hh).1
    have hbpos : 0 < b := (Nat.zero_le _).trans_lt ht.1
    have hh' :=
      (Real.log_le_iff_le_exp (Nat.cast_pos.mpr hbpos)).mpr
        ((Nat.le_floor_iff (Real.exp_pos _).le).mp ht.2)
    exact sub_le_iff_le_add.mpr (hh'.trans_eq (add_comm v 5))
  · apply hm0.le.trans_eq
    apply Finset.sum_congr rfl
    intro b hh
    have hprime : b.Prime := (Finset.mem_filter.mp hh).2.2
    dsimp only
    rw [ArithmeticFunction.vonMangoldt_apply_prime hprime, mul_comm]

/-- The actual common-sign primes in the translated window supply a fourfold
Euler saving strictly above 0.02085 on the log interval [600,626]. -/
theorem common_prime_euler_saving_626 {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hn : 1 < n) (ho : Odd n) (hs : Squarefree n) (he : n = p * q * r) (hp : Odd p) (hq : Odd q)
    (hr : Odd r) (hk : p - 1 ∣ n - 1) (hj : q - 1 ∣ n - 1) (hm : r - 1 ∣ n - 1)
    (hv : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hw : padicValNat 2 (r - 1) = padicValNat 2 (p - 1))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {R : ℝ} (hR : 300 ≤ R)
    (hU : R ≤ 313) (hL : Real.log n = 2 * R) (hRH : RiemannHypothesis) (hP : R ^ 4 < p)
    (hQ : R ^ 4 < q) (hT : R ^ 4 < r)
    (hb :
      ∀ b : ℕ, b.Prime → b ≤ ⌊Real.exp (5 / 2)⌋₊ → PrimeTest.StrongMillerRabinPass n (b : ZMod n)) :
    let v := 2 * Real.log R
    let s := Finset.Ioc ⌊Real.exp v⌋₊ ⌊Real.exp (v + 5)⌋₊
    let good :=
      s.filter
        (fun (b : ℕ) => (jacobiSym b p = jacobiSym b q ∧ jacobiSym b q = jacobiSym b r) ∧ b.Prime)
    0.02085 < 4 * ∑ b ∈ good, Real.log b * quarterEulerWeight570 b := by
  exact
    common_prime_euler_saving_to632 hn ho hs he hp hq hr hk hj hm hv hw hGRH hR
      (hU.trans (by norm_num only)) hL hRH hP hQ hT hb

end PseudoPrime.PrimeTestBounds.MillerRabin
