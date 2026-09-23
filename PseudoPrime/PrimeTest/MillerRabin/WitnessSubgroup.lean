/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.PrimeTest.MillerRabin.Decomposition
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.FieldTheory.Finite.Basic

/-!
# Subgroups containing strong Miller–Rabin pass bases
-/

namespace PseudoPrime.PrimeTest

/--
The subgroup of units modulo `n` whose `(n - 1)`st power equals one. Accepted residues belong to
its image; a prime-square divisor makes it proper, providing one branch of the composite theorem.
-/
def fermatSubgroup (n : ℕ) : Subgroup (ZMod n)ˣ where
  carrier := {u | u ^ (n - 1) = 1}
  one_mem' := by simp
  mul_mem' := by
    intro u v hu hv
    change (u * v) ^ (n - 1) = 1
    rw [mul_pow, hu, hv, one_mul]
  inv_mem' := by
    intro u hu
    change u⁻¹ ^ (n - 1) = 1
    rw [inv_pow, hu, inv_one]

/--
Under an admissible decomposition, a passing residue is a unit and its unit representative lies in
the Fermat subgroup. This is the inclusion used by the prime-square and central subgroup results.
-/
theorem strongMillerRabinPass_mem_fermatSubgroup {n s d : ℕ} {x : ZMod n}
    (hn : 1 < n)
    (hdecomp : n - 1 = 2 ^ s * d)
    (hpass : StrongMillerRabinPass n s d x) :
    ∃ u : (ZMod n)ˣ, u ∈ fermatSubgroup n ∧ (u : ZMod n) = x := by
  have hxUnit := strongMillerRabinPass_isUnit hn hdecomp hpass
  refine ⟨hxUnit.unit, ?_, hxUnit.unit_spec⟩
  apply Units.ext
  rw [Units.val_pow_eq_pow_val]
  exact strongMillerRabinPass_pow_decomp hdecomp hpass

/-- The order of `1 + q` modulo `q²` prevents its `(n - 1)`st power from being one. -/
private theorem one_add_prime_pow_ne_one {n q : ℕ}
    (hn : 1 < n)
    (hq : Nat.Prime q)
    (hq2 : q ≠ 2)
    (hqdiv : q ^ 2 ∣ n) :
    (1 + (q : ZMod (q ^ 2))) ^ (n - 1) ≠ 1 := by
  intro hpow
  have horder : orderOf (1 + (q : ZMod (q ^ 2))) = q := by
    rw [ZMod.orderOf_one_add_prime hq hq2 1, pow_one]
  have hqminus : q ∣ n - 1 := by
    rw [← horder]
    exact orderOf_dvd_of_pow_eq_one hpow
  have hqdivn : q ∣ n := dvd_trans ⟨q, by rw [pow_two]⟩ hqdiv
  have hqone := Nat.dvd_sub hqdivn hqminus
  rw [Nat.sub_sub_self (Nat.le_of_lt hn)] at hqone
  exact hq.ne_one (Nat.dvd_one.mp hqone)

/-- Lift a unit whose Fermat power fails modulo `q²` to a unit outside `fermatSubgroup n`. -/
private theorem exists_prime_square_unit_outside {n q : ℕ}
    (hnNeZero : NeZero n) (hqdiv : q ^ 2 ∣ n)
    (b : (ZMod (q ^ 2))ˣ) (hbpow : b ^ (n - 1) ≠ 1) :
    ∃ u : (ZMod n)ˣ, u ∉ fermatSubgroup n := by
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective (hm := hnNeZero) (n := q ^ 2) (m := n) hqdiv b
  have huout : u ∉ fermatSubgroup n := by
    intro huin
    have hpow := congrArg (ZMod.unitsMap hqdiv) huin
    rw [map_pow, map_one, hu] at hpow
    exact hbpow hpow
  exact ⟨u, huout⟩


/--
If a prime square divides `n`, the Fermat subgroup is proper. The proof uses `1 + q` modulo `q²`,
whose order is `q`, then lifts the corresponding unit to modulus `n`. This is the square-factor
case of the central theorem.
-/
theorem fermatSubgroup_ne_top_of_prime_square_dvd {n q : ℕ}
    (hn : 1 < n)
    (hq : Nat.Prime q)
    (hq2 : q ≠ 2)
    (hqdiv : q ^ 2 ∣ n) :
    fermatSubgroup n ≠ ⊤ := by
  have hnNeZero : NeZero n := ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one hn)⟩
  have hcopq : Nat.Coprime (1 + q) q := by
    rw [Nat.coprime_add_self_left]
    exact Nat.coprime_one_left q
  have hcop : Nat.Coprime (1 + q) (q ^ 2) :=
    (Nat.coprime_pow_right_iff (by decide : 0 < 2) (1 + q) q).2 hcopq
  have hbunit : IsUnit ((1 + q : ℕ) : ZMod (q ^ 2)) :=
    (ZMod.isUnit_iff_coprime (1 + q) (q ^ 2)).2 hcop
  have hcast : ((1 + q : ℕ) : ZMod (q ^ 2)) = 1 + (q : ZMod (q ^ 2)) := by
    norm_cast
  let b : (ZMod (q ^ 2))ˣ := hbunit.unit
  have hbase := one_add_prime_pow_ne_one hn hq hq2 hqdiv
  have hbpow : b ^ (n - 1) ≠ 1 := by
    intro hpow
    apply hbase
    have hval : ((b ^ (n - 1) : (ZMod (q ^ 2))ˣ) : ZMod (q ^ 2)) = 1 :=
      congrArg (fun u : (ZMod (q ^ 2))ˣ => (u : ZMod (q ^ 2))) hpow
    rw [Units.val_pow_eq_pow_val, hbunit.unit_spec, hcast] at hval
    exact hval
  obtain ⟨u, huout⟩ := exists_prime_square_unit_outside hnNeZero hqdiv b hbpow
  intro htop
  apply huout
  rw [htop]
  trivial

/-- In a prime field, a negative strong-test power must occur before the two-adic
exponent of `q - 1`. -/
theorem neg_power_index_lt_twoAdicExponent {q t c j d : ℕ} {y : ZMod q}
    (hq : Nat.Prime q)
    (hq2 : q ≠ 2)
    (hdecomp : q - 1 = 2 ^ t * c)
    (hcOdd : Odd c)
    (htj : t ≤ j)
    (hfermat : y ^ (q - 1) = 1)
    (hneg : y ^ (2 ^ j * d) = -1) :
    False := by
  have hqle : 2 ≤ q := hq.two_le
  have hqgt : 2 < q := by omega
  have hexpPow : 2 ^ j = 2 ^ t * 2 ^ (j - t) := by
    calc
      2 ^ j = 2 ^ (t + (j - t)) :=
        congrArg (2 ^ ·) (Nat.add_sub_of_le htj).symm
      _ = 2 ^ t * 2 ^ (j - t) := Nat.pow_add 2 t (j - t)
  have hexp : 2 ^ j * d * c = (q - 1) * (2 ^ (j - t) * d) := by
    rw [hdecomp, hexpPow]
    ring
  have hpowone : (y ^ (2 ^ j * d)) ^ c = 1 := by
    calc
      (y ^ (2 ^ j * d)) ^ c = y ^ (2 ^ j * d * c) :=
        (pow_mul y (2 ^ j * d) c).symm
      _ = y ^ ((q - 1) * (2 ^ (j - t) * d)) :=
        congrArg (fun e : ℕ => y ^ e) hexp
      _ = (y ^ (q - 1)) ^ (2 ^ (j - t) * d) := by rw [pow_mul]
      _ = 1 := by rw [hfermat, one_pow]
  have hsign : (1 : ZMod q) = -1 := by
    calc
      (1 : ZMod q) = (y ^ (2 ^ j * d)) ^ c := hpowone.symm
      _ = (-1) ^ c := congrArg (fun z : ZMod q => z ^ c) hneg
      _ = -1 := hcOdd.neg_one_pow
  exact (@ZMod.neg_one_ne_one q ⟨hqgt⟩).symm hsign

/--
The subgroup of units modulo `n` whose `E`th power equals either sign. It contains all passing
bases when `E = 2^(t - 1) * d` comes from an odd-prime decomposition `q - 1 = 2^t * c` with
`0 < t` and `Odd d`. With two distinct odd prime divisors `q` and `r` of `n`, this specific
subgroup is proper; see `signSubgroup_ne_top_of_distinct_prime_dvd`.
-/
def signSubgroup (n E : ℕ) : Subgroup (ZMod n)ˣ where
  carrier := {u | u ^ E = 1 ∨ u ^ E = -1}
  one_mem' := by
    left
    exact one_pow E
  mul_mem' := by
    intro u v hu hv
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · left
      rw [mul_pow, hu, hv, one_mul]
    · right
      rw [mul_pow, hu, hv, one_mul]
    · right
      rw [mul_pow, hu, hv, mul_one]
    · left
      rw [mul_pow, hu, hv]
      norm_num
  inv_mem' := by
    intro u hu
    rcases hu with hu | hu
    · left
      rw [inv_pow, hu, inv_one]
    · right
      rw [inv_pow, hu]
      simp

/-- Halving an element's even order produces an element of order two. -/
private theorem order_two_of_prime_field_unit {q t : ℕ} (b : (ZMod q)ˣ)
    (hbOrd : orderOf b = 2 ^ t) (ht : 0 < t) :
    orderOf (b ^ (2 ^ (t - 1))) = 2 := by
  have htwoDiv : 2 ∣ orderOf b := by
    rw [hbOrd]
    refine ⟨2 ^ (t - 1), ?_⟩
    calc
      2 ^ t = 2 ^ (t - 1 + 1) := by
        have htEq : t - 1 + 1 = t := Nat.sub_add_cancel (Nat.succ_le_of_lt ht)
        rw [htEq]
      _ = 2 ^ (t - 1) * 2 := Nat.pow_succ 2 (t - 1)
      _ = 2 * 2 ^ (t - 1) := Nat.mul_comm _ _
  have hdivPow : 2 ^ t / 2 = 2 ^ (t - 1) := by
    calc
      2 ^ t / 2 = 2 ^ t / 2 ^ 1 := by rw [pow_one]
      _ = 2 ^ (t - 1) := Nat.pow_div (Nat.succ_le_of_lt ht) (by decide : 0 < 2)
  have hzord : orderOf (b ^ (2 ^ (t - 1))) = 2 := by
    have h := orderOf_pow_orderOf_div (orderOf_pos b).ne' htwoDiv
    rw [hbOrd, hdivPow] at h
    exact h
  exact hzord

/-- Cyclicity of the prime-field unit group gives a unit of order `2^t`. -/
private theorem exists_prime_field_unit_order_two_power {q t c : ℕ}
    (hq : Nat.Prime q) (hq2 : q ≠ 2) (hqdecomp : q - 1 = 2 ^ t * c) :
    ∃ b : (ZMod q)ˣ, orderOf b = 2 ^ t := by
  have : Fact (Nat.Prime q) := ⟨hq⟩
  obtain ⟨g, hg⟩ :=
    (isCyclic_iff_exists_orderOf_eq_natCard).mp (ZMod.isCyclic_units_prime hq)
  rw [Nat.card_eq_fintype_card, @ZMod.card_units q ⟨hq⟩] at hg
  have hcpos : 0 < c := by
    have hqge : 2 ≤ q := hq.two_le
    have hqgt : 2 < q := by omega
    by_contra hcnot
    rw [Nat.eq_zero_of_not_pos hcnot] at hqdecomp
    omega
  have hcdiv : c ∣ 2 ^ t * c := by
    refine ⟨2 ^ t, ?_⟩
    rw [Nat.mul_comm]
  let b : (ZMod q)ˣ := g ^ c
  have hbOrd : orderOf b = 2 ^ t := by
    dsimp [b]
    rw [orderOf_pow, hg, hqdecomp, Nat.gcd_eq_right hcdiv, Nat.mul_comm]
    exact Nat.mul_div_cancel_left (2 ^ t) hcpos
  exact ⟨b, hbOrd⟩

/-- A negative power before level `t` is negative at the last level and positive below it. -/
private theorem negative_power_before_t_gives_sign {n t d j : ℕ} {x : ZMod n}
    (hjt : j < t) (hneg : x ^ (2 ^ j * d) = -1) :
    x ^ (2 ^ (t - 1) * d) = 1 ∨ x ^ (2 ^ (t - 1) * d) = -1 := by
  by_cases hlast : j = t - 1
  · right
    rw [← hlast]
    exact hneg
  · have hjlt : j < t - 1 := by omega
    have hexp : (2 ^ j * d) * 2 ^ (t - 1 - j) = 2 ^ (t - 1) * d := by
      calc
        (2 ^ j * d) * 2 ^ (t - 1 - j) = 2 ^ j * 2 ^ (t - 1 - j) * d := by ring
        _ = 2 ^ (j + (t - 1 - j)) * d := by rw [Nat.pow_add]
        _ = 2 ^ (t - 1) * d := by rw [Nat.add_sub_of_le (by omega)]
    have hpos : 0 < t - 1 - j := Nat.sub_pos_of_lt hjlt
    have heven : Even (2 ^ (t - 1 - j)) :=
      (show Even 2 from ⟨1, by rfl⟩).pow_of_ne_zero (Nat.ne_of_gt hpos)
    left
    calc
      x ^ (2 ^ (t - 1) * d) = (x ^ (2 ^ j * d)) ^ (2 ^ (t - 1 - j)) := by
        rw [← hexp, pow_mul]
      _ = (-1) ^ (2 ^ (t - 1 - j)) := by rw [hneg]
      _ = 1 := heven.neg_one_pow

/--
A prime residue field has a unit whose `2^(t-1) * d` power is negative one. Cyclicity gives an
element of order `2^t`; its half-order power has order two, hence equals `-1`. Oddness of `d`
preserves that sign. The distinct-prime subgroup proof uses this construction.
-/
theorem exists_prime_field_unit_pow_eq_neg_one {q t c d : ℕ}
    (hq : Nat.Prime q)
    (hq2 : q ≠ 2)
    (hqdecomp : q - 1 = 2 ^ t * c)
    (hdOdd : Odd d)
    (ht : 0 < t) :
    ∃ b : (ZMod q)ˣ, b ^ (2 ^ (t - 1) * d) = -1 := by
  have : Fact (Nat.Prime q) := ⟨hq⟩
  obtain ⟨b, hbOrd⟩ := exists_prime_field_unit_order_two_power hq hq2 hqdecomp
  have hzord := order_two_of_prime_field_unit b hbOrd ht
  have hzval : orderOf ((b ^ (2 ^ (t - 1)) : (ZMod q)ˣ) : ZMod q) = 2 := by
    change orderOf (Units.coeHom (ZMod q) (b ^ (2 ^ (t - 1))) : ZMod q) = 2
    rw [orderOf_injective (Units.coeHom (ZMod q)) Units.coeHom_injective]
    exact hzord
  have hzneg : (b ^ (2 ^ (t - 1)) : (ZMod q)ˣ) = -1 := by
    apply Units.ext
    exact (CharP.orderOf_eq_two_iff q hq2).mp hzval
  have hfinal : b ^ (2 ^ (t - 1) * d) = -1 := by
    calc
      b ^ (2 ^ (t - 1) * d) = (b ^ (2 ^ (t - 1))) ^ d := pow_mul _ _ _
      _ = (-1) ^ d := by rw [hzneg]
      _ = -1 := hdOdd.neg_one_pow
  exact ⟨b, hfinal⟩

/--
For an odd prime divisor `q`, every passing base lies in the corresponding sign-power subgroup.
Reduction modulo `q` bounds the negative-power index by `t`; the two possible index ranges then
give the required sign modulo `n`. No comparison between `t` and `s`, or minimum over prime
factors, is needed. This is the inclusion half of the distinct-prime case.
-/
theorem strongMillerRabinPass_mem_signSubgroup {n s d q t c : ℕ} {x : ZMod n}
    (hn : 1 < n)
    (hdecomp : n - 1 = 2 ^ s * d)
    (hpass : StrongMillerRabinPass n s d x)
    (hq : Nat.Prime q)
    (hq2 : q ≠ 2)
    (hqdiv : q ∣ n)
    (hqdecomp : q - 1 = 2 ^ t * c)
    (hcOdd : Odd c) :
    ∃ u : (ZMod n)ˣ, u ∈ signSubgroup n (2 ^ (t - 1) * d) ∧ (u : ZMod n) = x := by
  have hxunit := strongMillerRabinPass_isUnit hn hdecomp hpass
  let u : (ZMod n)ˣ := hxunit.unit
  have huval : (u : ZMod n) = x := hxunit.unit_spec
  let v : (ZMod q)ˣ := ZMod.unitsMap hqdiv u
  let y : ZMod q := v
  let f : ZMod n →+* ZMod q := ZMod.castHom hqdiv (ZMod q)
  have hyfermat : y ^ (q - 1) = 1 := by
    change ((v ^ (q - 1) : (ZMod q)ˣ) : ZMod q) = 1
    exact congrArg (fun z : (ZMod q)ˣ => (z : ZMod q))
      (@ZMod.units_pow_card_sub_one_eq_one q ⟨hq⟩ v)
  refine ⟨u, ?_, huval⟩
  change u ^ (2 ^ (t - 1) * d) = 1 ∨ u ^ (2 ^ (t - 1) * d) = -1
  rcases hpass with hbase | ⟨j, hjs, hneg⟩
  · left
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, huval, Nat.mul_comm, pow_mul, hbase, one_pow]
    rfl
  · have hyneg : y ^ (2 ^ j * d) = -1 := by
      change (v : ZMod q) ^ (2 ^ j * d) = -1
      have hmap := congrArg f hneg
      rw [map_pow, map_neg, map_one] at hmap
      change f x ^ (2 ^ j * d) = -1 at hmap
      rw [ZMod.unitsMap_val, huval]
      rw [← ZMod.castHom_apply (R := ZMod q) (h := hqdiv)]
      exact hmap
    have hjt : j < t := by
      by_contra hnot
      exact neg_power_index_lt_twoAdicExponent hq hq2 hqdecomp hcOdd
        (Nat.le_of_not_gt hnot) hyfermat hyneg
    rcases negative_power_before_t_gives_sign hjt hneg with hpositive | hnegative
    · left
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, huval]
      exact hpositive
    · right
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, huval]
      exact hnegative

/-- A unit whose `E`th power has neither sign witnesses that the sign subgroup is proper. -/
theorem signSubgroup_ne_top_of_outside {n E : ℕ} {u : (ZMod n)ˣ}
    (hone : u ^ E ≠ 1)
    (hneg : u ^ E ≠ -1) :
    signSubgroup n E ≠ ⊤ := by
  intro htop
  have hu : u ∈ signSubgroup n E := by
    rw [htop]
    trivial
  rcases hu with hu | hu
  · exact hone hu
  · exact hneg hu

/-- The CRT residue with coordinates `(b, 1)` has neither sign after the chosen power. -/
private theorem crt_residue_power_ne_sign {q r E : ℕ} (hq : 2 < q) (hr : 2 < r)
    (hcop : Nat.Coprime q r) (b : (ZMod q)ˣ) (hbpow : b ^ E = -1) :
    let e : ZMod (q * r) ≃+* ZMod q × ZMod r := ZMod.chineseRemainder hcop
    let z : ZMod (q * r) := e.symm ((b : ZMod q), 1)
    z ^ E ≠ 1 ∧ z ^ E ≠ -1 := by
  dsimp
  let e : ZMod (q * r) ≃+* ZMod q × ZMod r := ZMod.chineseRemainder hcop
  let z : ZMod (q * r) := e.symm ((b : ZMod q), 1)
  have hez : e z = ((b : ZMod q), (1 : ZMod r)) := e.apply_symm_apply _
  have hcrtPow : e (z ^ E) = (((b ^ E : (ZMod q)ˣ) : ZMod q), (1 : ZMod r)) := by
    rw [map_pow, hez]
    simp
  constructor
  · intro hpow
    have hpair := (hcrtPow.symm.trans (congrArg e hpow)).trans (map_one e)
    have hfirst := congrArg Prod.fst hpair
    have hbval := congrArg (fun a : (ZMod q)ˣ => (a : ZMod q)) hbpow
    rw [Units.val_pow_eq_pow_val] at hbval
    exact (@ZMod.neg_one_ne_one q ⟨hq⟩) (hbval.symm.trans hfirst)
  · intro hpow
    have hpair := (hcrtPow.symm.trans (congrArg e hpow)).trans
      (map_neg e (1 : ZMod (q * r)))
    have hsecond : (1 : ZMod r) = -1 := by simpa using congrArg Prod.snd hpair
    exact (@ZMod.neg_one_ne_one r ⟨hr⟩).symm hsecond

/-- The inverse CRT image of `(b, 1)` is represented by a unit. -/
private theorem crt_residue_isUnit {q r : ℕ} (hcop : Nat.Coprime q r) (b : (ZMod q)ˣ) :
    ∃ v : (ZMod (q * r))ˣ,
      (v : ZMod (q * r)) =
        (ZMod.chineseRemainder hcop).symm ((b : ZMod q), (1 : ZMod r)) := by
  let e : ZMod (q * r) ≃+* ZMod q × ZMod r := ZMod.chineseRemainder hcop
  let z : ZMod (q * r) := e.symm ((b : ZMod q), 1)
  let w : ZMod (q * r) := e.symm ((↑(b⁻¹) : ZMod q), 1)
  have hez : e z = ((b : ZMod q), (1 : ZMod r)) := e.apply_symm_apply _
  have hew : e w = ((↑(b⁻¹) : ZMod q), (1 : ZMod r)) := e.apply_symm_apply _
  have hzw : z * w = 1 := by
    apply e.injective
    rw [map_mul, hez, hew, map_one]
    ext <;> simp
  have hwz : w * z = 1 := by
    calc
      w * z = z * w := mul_comm _ _
      _ = 1 := hzw
  have hzunit : IsUnit z := isUnit_iff_exists.mpr ⟨w, hzw, hwz⟩
  refine ⟨hzunit.unit, ?_⟩
  rw [hzunit.unit_spec]

/-- Lift a unit with neither power sign to modulus `n` while preserving both inequalities. -/
private theorem exists_lift_unit_with_power_ne_sign {n m E : ℕ}
    (hnNeZero : NeZero n) (hdiv : m ∣ n) (v : (ZMod m)ˣ)
    (hone : v ^ E ≠ 1) (hneg : v ^ E ≠ -1) :
    ∃ u : (ZMod n)ˣ, u ^ E ≠ 1 ∧ u ^ E ≠ -1 := by
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective (hm := hnNeZero) (n := m) (m := n) hdiv v
  refine ⟨u, ?_, ?_⟩
  · intro h
    apply hone
    calc
      v ^ E = (ZMod.unitsMap hdiv u) ^ E := by rw [hu]
      _ = ZMod.unitsMap hdiv (u ^ E) := by rw [map_pow]
      _ = 1 := by rw [h, map_one]
  · intro h
    apply hneg
    calc
      v ^ E = (ZMod.unitsMap hdiv u) ^ E := by rw [hu]
      _ = ZMod.unitsMap hdiv (u ^ E) := by rw [map_pow]
      _ = -1 := by
        rw [h, ZMod.unitsMap]
        exact Units.map_neg_one (ZMod.castHom hdiv (ZMod m))

/--
Suppose distinct odd primes `q` and `r` divide `n`, and `q - 1 = 2^t * c` with `0 < t` and odd
`d`. Then the subgroup for `E = 2^(t - 1) * d` is proper. The proof chooses a unit with CRT
coordinates `(b, 1)`, where `b^E = -1`, then lifts it to modulus `n`; the coordinates rule out
both signs. This supplies the distinct-prime case of the central subgroup theorem.
-/
theorem signSubgroup_ne_top_of_distinct_prime_dvd {n q r t c d : ℕ}
    (hn : 1 < n)
    (hq : Nat.Prime q)
    (hr : Nat.Prime r)
    (hq2 : q ≠ 2)
    (hr2 : r ≠ 2)
    (hqr : q ≠ r)
    (hdiv : q * r ∣ n)
    (hqdecomp : q - 1 = 2 ^ t * c)
    (hdOdd : Odd d)
    (ht : 0 < t) :
    signSubgroup n (2 ^ (t - 1) * d) ≠ ⊤ := by
  obtain ⟨b, hbpow⟩ := exists_prime_field_unit_pow_eq_neg_one hq hq2
    hqdecomp hdOdd ht
  have hnotdvd : ¬ q ∣ r := by
    intro hqdivr
    rcases hr.eq_one_or_self_of_dvd q hqdivr with hqone | hqeq
    · exact hq.ne_one hqone
    · exact hqr hqeq
  have hcop : Nat.Coprime q r := hq.coprime_iff_not_dvd.mpr hnotdvd
  let e : ZMod (q * r) ≃+* ZMod q × ZMod r := ZMod.chineseRemainder hcop
  let z : ZMod (q * r) := e.symm ((b : ZMod q), 1)
  have hqle : 2 ≤ q := hq.two_le
  have hqgt : 2 < q := by omega
  have hrle : 2 ≤ r := hr.two_le
  have hrgt : 2 < r := by omega
  have hcoords := crt_residue_power_ne_sign hqgt hrgt hcop b hbpow
  obtain ⟨v, hvval⟩ := crt_residue_isUnit hcop b
  let exponent := 2 ^ (t - 1) * d
  have hone : v ^ exponent ≠ 1 := by
    intro h
    apply hcoords.1
    have hval := congrArg (fun a : (ZMod (q * r))ˣ => (a : ZMod (q * r))) h
    rw [Units.val_pow_eq_pow_val, hvval] at hval
    exact hval
  have hneg : v ^ exponent ≠ -1 := by
    intro h
    apply hcoords.2
    have hval := congrArg (fun a : (ZMod (q * r))ˣ => (a : ZMod (q * r))) h
    rw [Units.val_pow_eq_pow_val, hvval] at hval
    exact hval
  have hnNeZero : NeZero n := ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one hn)⟩
  obtain ⟨u, huone, huneg⟩ :=
    exists_lift_unit_with_power_ne_sign hnNeZero hdiv v hone hneg
  exact signSubgroup_ne_top_of_outside
    huone huneg

end PseudoPrime.PrimeTest
