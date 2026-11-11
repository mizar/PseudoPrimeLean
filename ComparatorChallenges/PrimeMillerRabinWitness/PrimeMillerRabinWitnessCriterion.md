---
marp: true
theme: default
size: 16:9
math: mathjax
paginate: false
title: "Miller–Rabin under GRH: base-nine and 3/11 criteria"
description: "Abbreviated and fully expanded forms of the prime-base Miller–Rabin criterion."
style: |
  section {
    width: 1280px;
    height: 720px;
    box-sizing: border-box;
    display: block;
    padding: 0;
    background: #ffffff;
    color: #172638;
    font-family: Arial, "Noto Sans", sans-serif;
    font-size: 20px;
    line-height: 1.25;
  }
  section::after { display: none; }
  section p { margin: 0; }
  section h1, section h2 { margin: 0; padding: 0; border: 0; }
  section h1 { font-size: 31px; font-weight: 700; letter-spacing: -0.6px; color: #172638; }
  section h2 { font-size: 17px; font-weight: 700; color: #176875; }
  section mjx-container[display="true"] { margin: 0 !important; }
  .topline { position: absolute; left: 0; top: 0; width: 1280px; height: 6px; background: #176875; }
  .heading { position: absolute; left: 38px; right: 38px; top: 24px; }
  .eyebrow { font-size: 11px; font-weight: 700; letter-spacing: 1.8px; color: #597080; margin-bottom: 7px; }
  .subtitle { margin-top: 7px; font-size: 15px; color: #597080; }
  .short {
    position: absolute; left: 38px; top: 120px; width: 1204px; height: 120px;
    box-sizing: border-box; padding: 12px 20px 12px; background: #f2f7f8;
  }
  .short-label { display: flex; align-items: baseline; gap: 20px; margin-bottom: 3px; }
  .short-label p { font-size: 16px; }
  .short-math { font-size: 23px; }
  .left { position: absolute; left: 38px; top: 256px; width: 470px; }
  .right { position: absolute; left: 544px; top: 256px; width: 698px; }
  .divider { position: absolute; left: 520px; top: 256px; width: 1px; height: 400px; background: #dbe4e8; }
  .grh-math { margin-top: 15px; font-size: 21px; }
  .notation { margin-top: 12px; font-size: 14px; line-height: 1.3; color: #435969; }
  .trivial { margin-top: 11px; font-size: 18px; }
  .modulus-one { margin-top: 12px; font-size: 15px; color: #435969; }
  .full-math { margin-top: 15px; font-size: 21px; }
  .decomp-note { margin-top: 14px; font-size: 14px; line-height: 1.3; color: #435969; }
  .proof-note { font-size: 14px; color: #435969; }
  .foot {
    position: absolute; left: 38px; right: 38px; bottom: 22px;
    padding-top: 10px; border-top: 1px solid #dbe4e8;
    display: flex; justify-content: space-between; gap: 24px;
    font-size: 13px; color: #597080;
  }
  .foot code { font-size: 12px; background: none; padding: 0; color: #597080; }
---

<div class="topline"></div>
<div class="heading">
<div class="eyebrow">PSEUDOPRIME · PRIME-BASE PRIMALITY CRITERION</div>

# Miller–Rabin under GRH: $p\le\frac{2}{(\ln 9)^2}(\ln n)^2$

<div class="subtitle">Comparator solution using the library proof</div>
</div>

<div class="short">
<div class="short-label">

## Abbreviated form

Assume GRH; let $n > 1$ be an odd integer.

</div>
<div class="short-math">

$$
\boxed{
\text{every prime }p \le 2(\log_9 n)^2\text{ passes the strong Miller–Rabin conditions for }n \iff n\text{ is prime}.
}
$$

</div>
</div>

<div class="divider"></div>
<div class="left">

## GRH — definition

<div class="grh-math">

$$
\boxed{
\begin{gathered}
\mathrm{GRH} :\Longleftrightarrow\\[3pt]
\forall q\in\mathbb Z_{\ge 1},\quad
\forall\chi\in\mathcal X_{\mathrm{prim}}(q),\quad
\forall z\in\mathbb C,\\[3pt]
\bigl(L(z,\chi)=0 \land z\notin T_\chi\bigr)
\Longrightarrow\mathrm{Re}(z)=\frac12.
\end{gathered}
}
$$

</div>
<div class="notation">

$\mathcal X_{\mathrm{prim}}(q)$: primitive complex Dirichlet characters modulo $q$.<br>
$L(z,\chi)$: Mathlib's complex-valued Dirichlet $L$-function, defined at every $z$.
At the pole $z=1$ for the trivial character, it has a formal complex value;
the GRH statement above does not exclude that point.

</div>
<div class="trivial">

$$
T_\chi:=
\begin{cases}
\lbrace -2,-4,-6,\ldots\rbrace, & q=1,\\[2pt]
\lbrace 0,-2,-4,\ldots\rbrace, & q > 1,\quad \chi(-1)=1,\\[2pt]
\lbrace -1,-3,-5,\ldots\rbrace, & q > 1,\quad \chi(-1)=-1.
\end{cases}
$$

</div>
<div class="modulus-one">

For $q=1$, $L(z,\chi)=\zeta(z)$; thus GRH includes RH.

</div>
</div>

<div class="right">

## Proven theorem — canonical decomposition

<div class="full-math">

$$
\boxed{
\begin{gathered}
\mathrm{GRH},\quad n\in\mathbb Z_{\ge0},\quad n > 1,\quad n\equiv1\pmod2,\\[4pt]
(s,d):=\mathrm{Nat.maxPowDvdDiv}(2,n-1)
\Longrightarrow\\[4pt]
\left[
\begin{gathered}
\left(\forall p\in\mathbb P,\quad
p \le 2(\log_9 n)^2 \Longrightarrow\right.\\[4pt]
\left.\left(
\begin{gathered}
p^d\equiv1\pmod n\\[2pt]
{}\lor \exists j\in\mathbb Z_{\ge0},\quad
j < s \land p^{2^j d}\equiv-1\pmod n
\end{gathered}
\right)\right)
\Longleftrightarrow n\in\mathbb P
\end{gathered}
\right].
\end{gathered}
}
$$

</div>

<div class="decomp-note">

The theorem uses `Nat.maxPowDvdDiv` to choose the canonical decomposition
$n-1=2^s d$ with $d$ odd.

</div>

<div class="proof-note">

`ComparatorChallenges.PrimeMillerRabinWitness.prime_millerRabin_log_nine_criterion`

The proof uses `prime_millerRabin_log_nine_criterion` in
[`LogNineBridge.lean`](../../PseudoPrime/PrimeTestBounds/MillerRabin/LogNineBridge.lean).

</div>

</div>

<div class="foot">

$\mathbb P$: primes. $\ln$: natural logarithm. The odd-part decomposition uniquely determines $s,d$.

</div>

---

<div class="topline"></div>
<div class="heading">
<div class="eyebrow">PSEUDOPRIME · PRIME-BASE PRIMALITY CRITERION</div>

# Miller–Rabin under GRH: $p\le\max\left(2, \frac{3}{11}(\ln n)^2\right)$

<div class="subtitle">Comparator solution using the library proof</div>
</div>

<div class="short">
<div class="short-label">

## Abbreviated form

Assume GRH; let $n > 1$ be an odd integer.

</div>
<div class="short-math">

$$
\boxed{
\text{every prime }p \le \max\left(2, \frac{3}{11}(\ln n)^2\right)\text{ passes the strong Miller–Rabin conditions for }n \iff n\text{ is prime}.
}
$$

</div>
</div>

<div class="divider"></div>
<div class="left">

## GRH — definition

<div class="grh-math">

$$
\boxed{
\begin{gathered}
\mathrm{GRH} :\Longleftrightarrow\\[3pt]
\forall q\in\mathbb Z_{\ge 1},\quad
\forall\chi\in\mathcal X_{\mathrm{prim}}(q),\quad
\forall z\in\mathbb C,\\[3pt]
\bigl(L(z,\chi)=0 \land z\notin T_\chi\bigr)
\Longrightarrow\mathrm{Re}(z)=\frac12.
\end{gathered}
}
$$

</div>
<div class="notation">

$\mathcal X_{\mathrm{prim}}(q)$: primitive complex Dirichlet characters modulo $q$.<br>
$L(z,\chi)$: Mathlib's complex-valued Dirichlet $L$-function, defined at every $z$.
At the pole $z=1$ for the trivial character, it has a formal complex value;
the GRH statement above does not exclude that point.

</div>
<div class="trivial">

$$
T_\chi:=
\begin{cases}
\lbrace -2,-4,-6,\ldots\rbrace, & q=1,\\[2pt]
\lbrace 0,-2,-4,\ldots\rbrace, & q > 1,\quad \chi(-1)=1,\\[2pt]
\lbrace -1,-3,-5,\ldots\rbrace, & q > 1,\quad \chi(-1)=-1.
\end{cases}
$$

</div>
<div class="modulus-one">

For $q=1$, $L(z,\chi)=\zeta(z)$; thus GRH includes RH.

</div>
</div>

<div class="right">

## Proven theorem — canonical decomposition

<div class="full-math">

$$
\boxed{
\begin{gathered}
\mathrm{GRH},\quad n\in\mathbb Z_{\ge0},\quad n > 1,\quad n\equiv1\pmod2,\\[4pt]
(s,d):=\mathrm{Nat.maxPowDvdDiv}(2,n-1)
\Longrightarrow\\[4pt]
\left[
\begin{gathered}
\left(\forall p\in\mathbb P,\quad
p \le \max\left(2, \frac{3}{11}(\ln n)^2\right) \Longrightarrow\right.\\[4pt]
\left.\left(
\begin{gathered}
p^d\equiv1\pmod n\\[2pt]
{}\lor \exists j\in\mathbb Z_{\ge0},\quad
j < s \land p^{2^j d}\equiv-1\pmod n
\end{gathered}
\right)\right)
\Longleftrightarrow n\in\mathbb P
\end{gathered}
\right].
\end{gathered}
}
$$

</div>

<div class="decomp-note">

The theorem uses `Nat.maxPowDvdDiv` to choose the canonical decomposition
$n-1=2^s d$ with $d$ odd.

</div>

<div class="proof-note">

`ComparatorChallenges.PrimeMillerRabinWitness.prime_millerRabin_027_criterion`

The proof uses `prime_millerRabin_027_criterion` in
[`ThreeEleventhsBridge.lean`](../../PseudoPrime/PrimeTestBounds/MillerRabin/ThreeEleventhsBridge.lean),
which derives the criterion from the least rejecting-prime bound.

</div>

</div>

<div class="foot">

$\mathbb P$: primes. $\ln$: natural logarithm. The odd-part decomposition uniquely determines $s,d$.

</div>
