---
marp: true
theme: default
size: 16:9
math: mathjax
paginate: false
title: "Prime quadratic witnesses under GRH"
description: "Two GRH-conditional bounds for odd-prime Jacobi witnesses."
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
<div class="eyebrow">PSEUDOPRIME · PRIME QUADRATIC WITNESSES</div>

# A prime witness with symbol different from one

<div class="subtitle">Comparator solution using the library proof</div>
</div>

<div class="short">
<div class="short-label">

## Abbreviated form

Assume GRH; let $n$ be an odd nonsquare.

</div>
<div class="short-math">

$$
\boxed{\exists\text{ an odd prime }p \le \max\lbrace 5,(\ln n)^2\rbrace \text{ with }\left(\frac{n}{p}\right) \ne 1.}
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

## Full witness bound

<div class="full-math">

$$
\boxed{
\begin{gathered}
\mathrm{GRH} \Longrightarrow
\forall n\in\mathbb Z_{\ge 0},\\[5pt]
\left(n\equiv1\pmod2
\land n\notin\lbrace k^2 : k\in\mathbb Z_{\ge 0}\rbrace\right)
\Longrightarrow\\[8pt]
\exists p\in\mathbb P,\quad p\equiv1\pmod2,\\[5pt]
p \le \max\lbrace 5,(\ln n)^2\rbrace,\\[5pt]
\left(\frac{n}{p}\right) \ne 1.
\end{gathered}
}
$$

</div>
</div>

<div class="foot">

$\mathbb P$: primes. $\ln$: natural logarithm. The symbol denotes the Jacobi symbol.

`ComparatorChallenges.PrimeQuadraticWitness.prime_ne_one_witness_bound`

</div>

---

<div class="topline"></div>
<div class="heading">
<div class="eyebrow">PSEUDOPRIME · PRIME QUADRATIC WITNESSES</div>

# A prime witness with symbol negative one

<div class="subtitle">Comparator solution using the library proof</div>
</div>

<div class="short">
<div class="short-label">

## Abbreviated form

Assume GRH; let $n$ be an odd nonsquare.

</div>
<div class="short-math">

$$
\boxed{\exists\text{ an odd prime }p \le \left(\ln(4n)+\frac{24}{5}\ln\ln(4n)+2\right)^2 \text{ with }\left(\frac{n}{p}\right)=-1.}
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

## Full witness bound

<div class="full-math">

$$
\boxed{
\begin{gathered}
\mathrm{GRH} \Longrightarrow
\forall n\in\mathbb Z_{\ge 0},\\[5pt]
\left(n\equiv1\pmod2
\land n\notin\lbrace k^2 : k\in\mathbb Z_{\ge 0}\rbrace\right)
\Longrightarrow\\[8pt]
\exists p\in\mathbb P,\quad p\equiv1\pmod2,\\[5pt]
p \le \left(\ln(4n)+\frac{24}{5}\ln\ln(4n)+2\right)^2,\\[5pt]
\left(\frac{n}{p}\right) = -1.
\end{gathered}
}
$$

</div>
</div>

<div class="foot">

$\mathbb P$: primes. $\ln$: natural logarithm. The symbol denotes the Jacobi symbol.

`ComparatorChallenges.PrimeQuadraticWitness.prime_neg_one_witness_bound`

</div>
