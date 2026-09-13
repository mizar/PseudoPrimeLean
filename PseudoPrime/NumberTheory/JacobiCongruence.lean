/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.NumberTheory.Jacobi.Numerator
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.FundamentalDiscriminant
import Mathlib.Tactic

/-! # General bounds and arithmetic certificates -/

namespace PseudoPrime.NumberTheory

/-- The positive discriminant attached to a squarefree odd part. -/
def positiveFundamentalDiscriminant (d : ℕ) : ℕ :=
  if d % 4 = 1 then d else 4 * d

/-- In the odd fundamental-discriminant branch, the positive representative is `d`. -/
theorem positiveFundamentalDiscriminant_eq_self {d : ℕ} (hdmod : d % 4 = 1) :
    positiveFundamentalDiscriminant d = d := by
  simp only [positiveFundamentalDiscriminant, hdmod, ↓reduceIte]

/-- In the other odd branch, the positive representative is `4 * d`. -/
theorem positiveFundamentalDiscriminant_eq_four_mul {d : ℕ} (hdmod : ¬d % 4 = 1) :
    positiveFundamentalDiscriminant d = 4 * d := by
  simp only [positiveFundamentalDiscriminant, hdmod, ↓reduceIte]

/-- In the odd discriminant branch, the fundamental discriminant is no larger than the input. -/
theorem positiveFundamentalDiscriminant_le_of_square_mul {b d : ℕ} (hb : 0 < b)
    (hdmod : d % 4 = 1) : positiveFundamentalDiscriminant d ≤ b ^ 2 * d := by
  rw [positiveFundamentalDiscriminant_eq_self hdmod]
  simpa only [one_mul] using Nat.mul_le_mul_right d (Nat.one_le_pow 2 b hb)

/-- The positive representative is a Mathlib fundamental discriminant. -/
theorem positiveFundamentalDiscriminant_isFundamentalDiscr {d : ℕ} (hdodd : Odd d)
    (hdsq : Squarefree d) : (positiveFundamentalDiscriminant d : ℤ).IsFundamentalDiscr := by
  dsimp [positiveFundamentalDiscriminant]
  split_ifs with hdmod
  · rw [Int.isFundamentalDiscr_iff_squarefree]
    left
    constructor
    · exact_mod_cast hdmod
    · exact Int.squarefree_natCast.mpr hdsq
  · have hdmod' : d % 4 = 3 := by
      rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hdodd) with h | h
      · exact False.elim (hdmod h)
      · exact h
    have hDcast : (↑(4 * d) : ℤ) = 4 * (d : ℤ) := by norm_num only [Nat.cast_mul]
    rw [hDcast, Int.isFundamentalDiscr_four_mul]
    constructor
    · exact Int.squarefree_natCast.mpr hdsq
    · right
      exact_mod_cast hdmod'

/-- A proper divisor of an odd squarefree modulus admits a representative that is
`1` modulo the divisor but has Jacobi value `-1` modulo the full modulus. -/
theorem exists_nat_one_modEq_and_jacobiSym_eq_neg_one {d c : ℕ} (hdodd : Odd d)
    (hdsq : Squarefree d) (hc : c ∣ d) (hnot : ¬d ∣ c) :
    ∃ a : ℕ, a ≡ 1 [MOD c] ∧ jacobiSym a d = -1 := by
  have hd0 : d ≠ 0 := by
    intro hd
    subst d
    exact (Nat.not_odd_iff_even.mpr (by simp only [Even.zero])) hdodd
  have hc0 : c ≠ 0 := by
    intro hc0
    subst c
    exact hd0 (Nat.eq_zero_of_zero_dvd hc)
  let r := d / c
  have hprod : r * c = d := by
    dsimp [r]
    exact Nat.div_mul_cancel hc
  have hcop : r.Coprime c := by
    have h := Nat.coprime_div_gcd_of_squarefree hdsq hc0
    simpa only [Nat.gcd_eq_right hc] using h
  have hrgt : 1 < r := by
    by_contra hle
    have hle' : r ≤ 1 := Nat.le_of_not_gt hle
    rcases (Nat.le_one_iff_eq_zero_or_eq_one.mp hle') with hr0 | hr1
    · have hzero : (0 : ℕ) * c = d := by simpa only [hr0] using hprod
      exact hd0 (by simpa only [zero_mul] using hzero.symm)
    · apply hnot
      rw [← hprod, hr1]
      simp only [one_mul]
      exact dvd_refl c
  have hrodd : Odd r := by
    have hoddprod : Odd (r * c) := by simpa only [hprod] using hdodd
    exact (Nat.odd_mul.mp hoddprod).1
  have hrsq : Squarefree r := Squarefree.squarefree_of_dvd (Nat.div_dvd_of_dvd hc) hdsq
  have hrsns : ¬IsSquare r := by
    rintro ⟨x, hx⟩
    have hxne : x ≠ 1 := by
      intro hx1
      subst x
      have : r = 1 := by simpa only [mul_one] using hx
      exact (Nat.ne_of_gt hrgt) this
    have hpow : Squarefree (x ^ 2) := by simpa only [pow_two, ← hx] using hrsq
    have hiff := Nat.squarefree_pow_iff hxne (by decide : 2 ≠ 0)
    have hbad : (2 : ℕ) = 1 := (hiff.mp hpow).2
    omega
  obtain ⟨b, hb⟩ := exists_nat_neg_one_numerator hrodd hrsns
  let k := Nat.chineseRemainder hcop.symm 1 b
  refine ⟨k, k.prop.1, ?_⟩
  rw [← hprod, Nat.mul_comm r c, jacobiSym.mul_right']
  · have hkc : jacobiSym (k : ℤ) c = 1 := by
      have hkint : (k : ℤ) % c = (1 : ℤ) % c := by exact_mod_cast k.prop.1
      rw [jacobiSym.mod_left' hkint, jacobiSym.one_left]
    have hkr : jacobiSym (k : ℤ) r = -1 := by
      have hkrint : (k : ℤ) % r = (b : ℤ) % r := by exact_mod_cast k.prop.2
      rw [jacobiSym.mod_left' hkrint]
      exact hb
    rw [hkc, hkr]
    norm_num only
  · exact hc0
  · exact Nat.ne_zero_of_lt (Nat.zero_lt_of_lt hrgt)

/-- The CRT representative can be chosen odd, so it is a unit at the level `4 * d`. -/
theorem exists_nat_odd_one_modEq_and_jacobiSym_eq_neg_one {d c : ℕ} (hdodd : Odd d)
    (hdsq : Squarefree d) (hc : c ∣ d) (hnot : ¬d ∣ c) :
    ∃ a : ℕ, Odd a ∧ a ≡ 1 [MOD c] ∧ jacobiSym a d = -1 := by
  obtain ⟨k, hk, hj⟩ := exists_nat_one_modEq_and_jacobiSym_eq_neg_one hdodd hdsq hc hnot
  let a := if Even k then k + d else k
  have haodd : Odd a := by
    dsimp [a]
    split_ifs with hke
    · exact hke.add_odd hdodd
    · exact Nat.not_even_iff_odd.mp hke
  have hamodc : a ≡ k [MOD c] := by
    dsimp [a]
    split_ifs with hke
    · have hz : d ≡ 0 [MOD c] := Dvd.dvd.modEq_zero_nat hc
      simpa only [Nat.add_zero] using Nat.ModEq.add_left k hz
    · exact Nat.ModEq.refl k
  have hamodd : a ≡ k [MOD d] := by
    dsimp [a]
    split_ifs with hke
    · have hz : d ≡ 0 [MOD d] := Nat.modulus_modEq_zero
      simpa only [Nat.add_zero] using Nat.ModEq.add_left k hz
    · exact Nat.ModEq.refl k
  have hac : a ≡ 1 [MOD c] := hamodc.trans hk
  have haj : jacobiSym (a : ℤ) d = jacobiSym (k : ℤ) d := by
    apply jacobiSym.mod_left'
    exact_mod_cast hamodd
  refine ⟨a, haodd, hac, ?_⟩
  rw [haj]
  exact hj

/-- A prime in the same residue class removes the square-factor obstruction: the
representative can additionally be chosen coprime to any positive square factor. -/
theorem exists_nat_odd_one_modEq_and_jacobiSym_eq_neg_one_coprime {d c s : ℕ} (hdodd : Odd d)
    (hdsq : Squarefree d) (hc : c ∣ d) (hnot : ¬d ∣ c) (hs : 0 < s) :
    ∃ a : ℕ, Odd a ∧ a ≡ 1 [MOD c] ∧ jacobiSym a d = -1 ∧ Nat.Coprime a s := by
  obtain ⟨k, hk, hj⟩ := exists_nat_one_modEq_and_jacobiSym_eq_neg_one hdodd hdsq hc hnot
  have hcopd : Nat.Coprime k d := by
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hne
    have hz : jacobiSym (k : ℤ) d = 0 := by
      apply (jacobiSym.eq_zero_iff).mpr
      exact ⟨(Odd.pos hdodd).ne', by simpa only [Int.gcd_natCast_natCast, ne_eq] using hne⟩
    rw [hz] at hj
    norm_num only at hj
  obtain ⟨p, hpgt, hp, hpk⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (max s 2) (Odd.pos hdodd).ne' hcopd
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hpc : p ≡ 1 [MOD c] := by exact (Nat.ModEq.of_dvd hc hpk).trans hk
  have hpjac : jacobiSym (p : ℤ) d = -1 := by
    have hmod : (p : ℤ) % d = (k : ℤ) % d := by exact_mod_cast hpk
    rw [jacobiSym.mod_left' hmod]
    exact hj
  refine ⟨p, hpodd, hpc, hpjac, ?_⟩
  apply hp.coprime_iff_not_dvd.mpr
  intro hps
  have hple : p ≤ s := Nat.le_of_dvd hs hps
  omega

/-- When the odd part of a proper divisor of `4*d` is proper, a prime-AP lift gives
an odd representative that is `1` modulo the full divisor and has Jacobi value `-1`. -/
theorem exists_nat_odd_one_modEq_and_jacobiSym_eq_neg_one_of_dvd_four_mul_coprime {d c s : ℕ}
    (hdodd : Odd d) (hdsq : Squarefree d) (hs : 0 < s) (hc4 : c ∣ 4 * d) (hdnot : ¬d ∣ c) :
    ∃ a : ℕ, Odd a ∧ a ≡ 1 [MOD 4] ∧ a ≡ 1 [MOD c] ∧ jacobiSym a d = -1 ∧ Nat.Coprime a s := by
  let e := Nat.gcd c d
  have hed : e ∣ d := Nat.gcd_dvd_right c d
  have heodd : Odd e := Odd.of_dvd_nat hdodd hed
  have hec : c ∣ 4 * e := by
    have hce : c ∣ e * 4 := by
      exact (dvd_gcd_mul_iff_dvd_mul).mpr (by simpa only [Nat.mul_comm] using hc4)
    simpa only [Nat.mul_comm] using hce
  have hnoted : ¬d ∣ e := by
    intro hde
    exact hdnot (dvd_trans hde (Nat.gcd_dvd_left c d))
  obtain ⟨k, hk, hj⟩ := exists_nat_one_modEq_and_jacobiSym_eq_neg_one hdodd hdsq hed hnoted
  have hcopkd : Nat.Coprime k d := by
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hne
    have hz : jacobiSym (k : ℤ) d = 0 := by
      apply (jacobiSym.eq_zero_iff).mpr
      exact ⟨(Odd.pos hdodd).ne', by simpa only [Int.gcd_natCast_natCast, ne_eq] using hne⟩
    rw [hz] at hj
    norm_num only at hj
  have h4d : Nat.Coprime 4 d := by
    simpa only [pow_two] using Nat.Coprime.mul_left hdodd.coprime_two_left hdodd.coprime_two_left
  let r := Nat.chineseRemainder h4d 1 k
  have hr4 : r ≡ 1 [MOD 4] := r.prop.1
  have hrd : r ≡ k [MOD d] := r.prop.2
  have hcopr4 : Nat.Coprime r 4 := by
    simpa only [Nat.coprime_iff_gcd_eq_one, Nat.gcd_one_left] using hr4.gcd_eq
  have hcoprd : Nat.Coprime r d := by
    rw [Nat.coprime_iff_gcd_eq_one, hrd.gcd_eq]
    exact Nat.coprime_iff_gcd_eq_one.mp hcopkd
  have hcopr4d : Nat.Coprime r (4 * d) := hcopr4.mul_right hcoprd
  obtain ⟨p, hpgt, hp, hpr⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (max (max c s) 2)
      (Nat.mul_ne_zero (by norm_num only) (Odd.pos hdodd).ne') hcopr4d
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hp4 : p ≡ 1 [MOD 4] := (Nat.ModEq.of_dvd (dvd_mul_right 4 d) hpr).trans hr4
  have hpd : p ≡ k [MOD d] := (Nat.ModEq.of_dvd (dvd_mul_left d 4) hpr).trans hrd
  have hpe : p ≡ 1 [MOD e] := (Nat.ModEq.of_dvd hed hpd).trans hk
  have hcop4e : Nat.Coprime 4 e := Nat.Coprime.of_dvd_right hed h4d
  have hpc4e : p ≡ 1 [MOD 4 * e] := by
    apply (Nat.modEq_and_modEq_iff_modEq_mul hcop4e).mp
    exact And.intro hp4 hpe
  have hpc : p ≡ 1 [MOD c] := Nat.ModEq.of_dvd hec hpc4e
  have hpj : jacobiSym (p : ℤ) d = -1 := by
    have hm : (p : ℤ) % d = (k : ℤ) % d := by exact_mod_cast hpd
    rw [jacobiSym.mod_left' hm]
    exact hj
  have hps : Nat.Coprime p s := by
    apply hp.coprime_iff_not_dvd.mpr
    intro hps
    have hple : p ≤ s := Nat.le_of_dvd hs hps
    omega
  exact ⟨p, hpodd, hp4, hpc, hpj, hps⟩

/-- The odd representative for a proper divisor of `4*d`, without an extra coprimality target. -/
theorem exists_nat_odd_one_modEq_and_jacobiSym_eq_neg_one_of_dvd_four_mul {d c : ℕ} (hdodd : Odd d)
    (hdsq : Squarefree d) (hc4 : c ∣ 4 * d) (hdnot : ¬d ∣ c) :
    ∃ a : ℕ, Odd a ∧ a ≡ 1 [MOD 4] ∧ a ≡ 1 [MOD c] ∧ jacobiSym a d = -1 := by
  obtain ⟨a, haodd, ha4, hac, haj, _⟩ :=
    exists_nat_odd_one_modEq_and_jacobiSym_eq_neg_one_of_dvd_four_mul_coprime (s := 1) hdodd hdsq
      (by norm_num only) hc4 hdnot
  exact ⟨a, haodd, ha4, hac, haj⟩

/-- For the remaining proper divisors `d` and `2*d`, the Jacobi value is `1` while
the residue is `3` modulo `4`, so the `χ₄` factor supplies the required sign. -/
theorem exists_nat_odd_one_modEq_and_jacobiSym_eq_one_of_eq_d_or_two_mul {d c s : ℕ} (hdodd : Odd d)
    (hd4 : d % 4 = 3) (hs : 0 < s) (hc : c = d ∨ c = 2 * d) :
    ∃ a : ℕ, Odd a ∧ a ≡ 1 [MOD c] ∧ jacobiSym a d = 1 ∧ a % 4 = 3 ∧ Nat.Coprime a s := by
  rcases hc with hc | hc
  · subst c
    let r := 1 + 2 * d
    have hr4 : r ≡ 3 [MOD 4] := by
      change r % 4 = 3 % 4
      dsimp [r]
      omega
    have hrd : r ≡ 1 [MOD d] := by
      have hz : 2 * d ≡ 0 [MOD d] := Dvd.dvd.modEq_zero_nat ⟨2, by ring⟩
      dsimp [r]
      simpa only [Nat.add_zero] using Nat.ModEq.add_left 1 hz
    have hcopr4 : Nat.Coprime r 4 := by
      rw [Nat.coprime_iff_gcd_eq_one, hr4.gcd_eq]
      norm_num only
    have hcoprd : Nat.Coprime r d := by
      rw [Nat.coprime_iff_gcd_eq_one, hrd.gcd_eq]
      simp only [Nat.gcd_one_left]
    obtain ⟨p, hpgt, hp, hpr⟩ :=
      Nat.forall_exists_prime_gt_and_modEq (max (max d s) 2)
        (Nat.mul_ne_zero (by norm_num only) (Odd.pos hdodd).ne') (hcopr4.mul_right hcoprd)
    have hpodd : Odd p := hp.odd_of_ne_two (by omega)
    have hpd : p ≡ 1 [MOD d] := (Nat.ModEq.of_dvd (⟨4, by ring⟩ : d ∣ 4 * d) hpr).trans hrd
    have hpj : jacobiSym (p : ℤ) d = 1 := by
      have hm : (p : ℤ) % d = (1 : ℤ) % d := by exact_mod_cast hpd
      rw [jacobiSym.mod_left' hm, jacobiSym.one_left]
    have hp4 : p % 4 = 3 := by
      have hpm := Nat.ModEq.of_dvd (⟨d, by ring⟩ : 4 ∣ 4 * d) hpr
      exact_mod_cast hpm.trans hr4
    have hps : Nat.Coprime p s :=
      hp.coprime_iff_not_dvd.mpr
        (by
          intro hps
          have hple : p ≤ s := Nat.le_of_dvd hs hps
          omega)
    exact ⟨p, hpodd, hpd, hpj, hp4, hps⟩
  · subst c
    let r := 1 + 2 * d
    have hr4 : r ≡ 3 [MOD 4] := by
      change r % 4 = 3 % 4
      dsimp [r]
      omega
    have hr2d : r ≡ 1 [MOD 2 * d] := by
      have hz : 2 * d ≡ 0 [MOD 2 * d] := Nat.modulus_modEq_zero
      dsimp [r]
      simpa only [Nat.add_zero] using Nat.ModEq.add_left 1 hz
    have hrd : r ≡ 1 [MOD d] :=
      (Nat.ModEq.of_dvd (⟨2, by ring⟩ : d ∣ 2 * d) hr2d).trans (Nat.ModEq.refl 1)
    have hcopr4 : Nat.Coprime r 4 := by
      rw [Nat.coprime_iff_gcd_eq_one, hr4.gcd_eq]
      norm_num only
    have hcoprd : Nat.Coprime r d := by
      rw [Nat.coprime_iff_gcd_eq_one, hrd.gcd_eq]
      simp only [Nat.gcd_one_left]
    obtain ⟨p, hpgt, hp, hpr⟩ :=
      Nat.forall_exists_prime_gt_and_modEq (max (max (2 * d) s) 2)
        (Nat.mul_ne_zero (by norm_num only) (Odd.pos hdodd).ne') (hcopr4.mul_right hcoprd)
    have hpodd : Odd p := hp.odd_of_ne_two (by omega)
    have hpc : p ≡ 1 [MOD 2 * d] := (Nat.ModEq.of_dvd (⟨2, by ring⟩ : 2 * d ∣ 4 * d) hpr).trans hr2d
    have hpd : p ≡ 1 [MOD d] := Nat.ModEq.of_dvd (⟨2, by ring⟩ : d ∣ 2 * d) hpc
    have hpj : jacobiSym (p : ℤ) d = 1 := by
      have hm : (p : ℤ) % d = (1 : ℤ) % d := by exact_mod_cast hpd
      rw [jacobiSym.mod_left' hm, jacobiSym.one_left]
    have hp4 : p % 4 = 3 := by
      have hpm := Nat.ModEq.of_dvd (⟨d, by ring⟩ : 4 ∣ 4 * d) hpr
      exact_mod_cast hpm.trans hr4
    have hps : Nat.Coprime p s :=
      hp.coprime_iff_not_dvd.mpr
        (by
          intro hps
          have hple : p ≤ s := Nat.le_of_dvd hs hps
          omega)
    exact ⟨p, hpodd, hpc, hpj, hp4, hps⟩

/-- A proper divisor of `4*d` is either missing an odd factor, or is `d` or `2*d`. -/
theorem eq_squarefreePart_or_two_mul_of_dvd_four_mul_of_dvd {d c : ℕ} (hdodd : Odd d)
    (hc4 : c ∣ 4 * d) (hdc : d ∣ c) (hproper : ¬4 * d ∣ c) : c = d ∨ c = 2 * d := by
  have hdpos : 0 < d := Odd.pos hdodd
  obtain ⟨k, hkc⟩ := hdc
  obtain ⟨l, hl⟩ := hc4
  have hkl : k * l = 4 := by
    apply Nat.eq_of_mul_eq_mul_left hdpos
    calc
      d * (k * l) = (d * k) * l := by ring
      _ = c * l := by rw [← hkc]
      _ = 4 * d := hl.symm
      _ = d * 4 := by omega
  have hkdvd : k ∣ 4 := ⟨l, hkl.symm⟩
  have hk_le : k ≤ 4 := Nat.le_of_dvd (by norm_num only) hkdvd
  by_cases hk4 : k = 4
  · subst k
    exfalso
    apply hproper
    refine ⟨1, ?_⟩
    omega
  · have hklt : k < 4 := Nat.lt_of_le_of_ne hk_le hk4
    interval_cases k <;> omega

end PseudoPrime.NumberTheory
