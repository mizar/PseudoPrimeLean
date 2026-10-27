# LLS 一般指標・真部分群に対する明示的な素数上界

公開モジュール: [LLS.lean](../PseudoPrime/LLS.lean)。名前空間は `PseudoPrime.LLS`。

Lamzouri–Li–Soundararajan の Theorem 1.1 に対応する S1・S2 を扱う。`Statement.lean` では命題を定義し、別の定理で GRH からその命題を証明する。一般指標の解析評価と GRH による証明は LLS 本体にあり、LLS 本体は Extensions を import しない。

原論文の前提・主張と対応するLean定義は [LLSPaperStatements.md](LLSPaperStatements.md) を参照する。一般L関数と二次指標向けの拡張命題は [LLSExtensionStatements.md](LLSExtensionStatements.md) にまとめている。以下では、原式に対応する仕様と、開始点・補正項・損失評価を改良した定理を分けて示す。

## 共通の記号

$$
\begin{gathered}
q\in\mathbb N,\\
\mathbb P=\lbrace p\in\mathbb N\mid p\text{ は素数}\rbrace,\qquad
G_q=(\mathbb Z/q\mathbb Z)^\times,\\
\iota_q:G_q\hookrightarrow\mathbb Z/q\mathbb Z,\qquad
\chi\in\mathrm{DirChar}_{\mathbb C}(q).
\end{gathered}
$$

$\ln$ は自然対数、 $\omega(q)$ は相異なる素因数の個数、 $\Lambda$ はvon Mangoldt関数とする。
$\mathrm{DirChar}_{\mathbb C}(q)$ は法 $q$ の複素Dirichlet指標全体であり、 $\chi\ne1$ は非主指標であることを表す。
素因数和は相異なる素数について取る。
S1の $[p]_q\notin H$ では $p\nmid q$ のもとで単元剰余を用い、
S2の $[p]_q\notin\iota_q(H)$ では剰余環の元を用いる。S2は非単元の素数も許す。

## S1　法を割らない素数証人

### 原式

[Statement.lean](../PseudoPrime/LLS/Statement.lean) の定義に従い、

$$
A(q) = \max\Bigl(0, 2\ln(\ln\mathrel{} q) - \frac{8}{5} - \sum_{p \mid q}\frac{\ln\mathrel{} p}{p - 1}\Bigr),
$$

$$
B(q) = \max\Bigl(0, 2\ln(\ln\mathrel{} q) + 3 +
\frac{2\omega(q)(\ln(\ln\mathrel{} q))^2}{\ln\mathrel{} q} - 2A(q)\Bigr),\qquad
X_1(q) = (\ln\mathrel{} q + B(q))^2
$$

とする。素因数和は相異なる素因数について取る。 $A(q)$ は `llsAuxiliaryTerm`、 $B(q)$ は `llsCorrectionTerm` に対応する。

$$
\mathrm{GRH},\quad q\ge3000,\quad \chi\in\mathrm{DirChar}_{\mathbb C}(q),\quad\chi\ne1
\quad\Longrightarrow\quad
\exists p\in\mathbb P,\quad p\nmid q,\quad\chi(p)\ne1,\quad p\le X_1(q).
$$

$$
\mathrm{GRH},\quad q\ge3000,\quad H\subsetneq G_q
\quad\Longrightarrow\quad
\exists p\in\mathbb P,\quad p\nmid q,\quad[p]_q\notin H,\quad p\le X_1(q).
$$

対応する仕様と証明は次のとおりである。

| 仕様 | 主張 | GRH からの定理 |
|---|---|---|
| `llsTheorem11S1Character` | 非主複素 Dirichlet 指標 $\chi$ に対し、 $p \nmid q$、 $\chi(p) \ne 1$、 $p \le X_1(q)$ を満たす素数 $p$ が存在 | `llsTheorem11S1Character_of_grh` |
| `llsTheorem11S1` | 任意の真部分群 $H < (ℤ/qℤ)^\times$ に対し、法 $q$ を割らず、単元剰余が $H$ の外にあり、 $p \le X_1(q)$ を満たす素数 $p$ が存在 | `llsTheorem11S1_of_grh` |

一般指標版は、指標の二次性も原始性も要求しない。解析では原始指標に移し、導手と法の変更に伴う補正を扱う。`llsTheorem11S1_of_character` は商群の非自明指標を引き戻し、指標版から真部分群版を導く。二つの仕様は対象と結論が異なる。

`exists_least_prime_outside_subgroup_of_grh` はさらに最小素数を与える。最小性の比較対象は、上界内に限定せず `PrimeOutsideSubgroup q H` を満たすすべての素数である。これらの GRH 定理は [Theorem11S1GRH.lean](../PseudoPrime/LLS/Theorem11S1GRH.lean) にある。

### 原式の開始点3への拡張

$$
q\in\mathbb N,\qquad q\ge3,\qquad
G_q=(\mathbb Z/q\mathbb Z)^\times,\qquad
H\subsetneq G_q,\qquad\mathrm{GRH}
\quad\Longrightarrow\quad
\exists p\in\mathbb P,\quad p\nmid q,\quad[p]_q\notin H,\quad p\le X_1(q).
$$

$[p]_q$ は単元剰余を表す。
[Part1FromThree.lean](../PseudoPrime/LLS/Part1FromThree.lean) の
`llsTheorem11S1_from_three_of_grh` は、原式の補正項を変えずにこの結論を与える。
原論文の仕様 `llsTheorem11S1` の前提は変更していない。

$q=3$ の証人は $p=2$、 $q=4$ の証人は $p=3$ である。
$5\le q < 705$ では19以下、 $705\le q < 3000$ では43以下の素数剰余による単数群の生成を、
圧縮した整数証明書からLeanのカーネルで検証した。この有限範囲ではGRHを使わない。
$q\ge3000$ は既存の解析定理へ接続する。

### 補正定数7031/5000・逆数損失31551/20000による改良式

$L=\ln q$、 $u=\ln L$ とし、添字 $\mathrm{prec}$ で精密な逆数損失を使う補助項と半径を表す。

$$
\begin{aligned}
A_{\mathrm{prec}}(q)&=\max\left(0,2u-\frac{31551}{20000}
-\sum_{\substack{p\mid q\\p\text{ prime}}}\frac{\ln p}{p-1}\right),\\
B_{\mathrm{prec}}(q)&=\max\left(0,2u+\frac{7031}{5000}
+\frac{2\omega(q)u^2}{L}-2A_{\mathrm{prec}}(q)\right),\\
R_{\mathrm{prec}}(q)&=L+B_{\mathrm{prec}}(q),\qquad F_{\mathrm{prec}}(q)=R_{\mathrm{prec}}(q)^2.
\end{aligned}
$$

逆数損失を $32873/20800$ から $31551/20000$ に下げると、補助項は同じか大きくなり、
補正項と二乗上界は同じか小さくなる。補正定数 $7031/5000$ は共通である。
この半径比較は [PreciseSavingTheorem11S1.lean](../PseudoPrime/LLS/PreciseSavingTheorem11S1.lean) の
`preciseSavingRadiusRoot_le_retainedSavingRadiusRoot` が証明する。
`max` により上界が一致する場合もある。

### 改良式の真部分群版

$$
\mathrm{GRH},\quad q\ge3,\quad H\subsetneq G_q
\quad\Longrightarrow\quad
\exists p\in\mathbb P,\quad p\nmid q,\quad[p]_q\notin H,\quad p\le F_{\mathrm{prec}}(q).
$$

[PreciseSavingFromThree.lean](../PseudoPrime/LLS/PreciseSavingFromThree.lean) の
`exists_prime_outside_preciseSaving_from_three` がこの主張を証明する。

### 改良式の非主指標版

$$
\begin{gathered}
\mathrm{GRH},\quad q\in\mathbb N,\quad q\ge3,\\
\chi\in\mathrm{DirChar}_{\mathbb C}(q),\quad\chi\ne1
\end{gathered}
$$

$$
\Longrightarrow\quad
\exists p\in\mathbb P,\quad p\nmid q,\quad \chi(p)\ne1,\quad
p\le F_{\mathrm{prec}}(q).
$$

[PreciseSavingFromThree.lean](../PseudoPrime/LLS/PreciseSavingFromThree.lean) の
`exists_prime_character_ne_one_le_preciseSavingRadius_from_three` がこの主張を証明する。
指標の原始性や二次性は仮定しない。両版とも、有限範囲の上限5・19・43が改良半径に収まることを確認し、
既存の証明書を変更せずに使っている。

### 正確な素因数損失を保つ任意半径の条件

この節でも $L=\ln q$、 $u=\ln L$ とし、 $X > 0$ に対して

$$
C_q(X)=\sum_{\substack{1\le m\le X\\\gcd(m,q) > 1}}
\Lambda(m)\ln(X/m).
$$

と定める。補助項 $A_{\mathrm{prec}}(q)$ は改良式の定義を用いる。

$$
\begin{gathered}
\mathrm{GRH},\quad q\in\mathbb N,\quad q\ge3000,\quad \chi\ne1,\quad y\ge L,\\
\chi\in\mathrm{DirChar}_{\mathbb C}(q),\\
2u+\frac{7031}{5000}+\frac{C_q(y^2)}y-2A_{\mathrm{prec}}(q)\le y-L
\end{gathered}
$$

$$
\Longrightarrow\quad
\exists p\in\mathbb P,\quad p\nmid q,\quad \chi(p)\ne1,\quad p\le y^2.
$$

[PreciseSavingTheorem11S1.lean](../PseudoPrime/LLS/PreciseSavingTheorem11S1.lean) の
`exists_prime_character_ne_one_of_precise_exact_factor_root` がこの主張を証明する。
[ExactFactorLossTheorem11S1.lean](../PseudoPrime/LLS/ExactFactorLossTheorem11S1.lean) は、次の費用比較を証明する。

$$
q\ge3000,\quad y\ge L
\quad\Longrightarrow\quad
\frac{C_q(y^2)}y\le
\frac{2\omega(q)u^2}{L}.
$$

共通因子の寄与を素数冪ごとに保持し、従来の相異なる素因数の個数による上界へ緩和しない。
半径条件は $y$ に依存する陰的な条件であり、閉じた新しい半径式はまだ定めていない。

### 係数4/5による大尺度の一様上界

$$
\mathrm{GRH},\quad q\in\mathbb N,\quad q\ge10^{19787},\quad H\subsetneq G_q
$$

$$
\Longrightarrow\quad\exists p\in\mathbb P,\quad
p\nmid q,\quad[p]_q\notin H,\quad p\le\frac45(\ln q)^2.
$$

$$
\mathrm{GRH},\quad q\ge10^{19787},\quad
\chi\in\mathrm{DirChar}_{\mathbb C}(q),\quad\chi\ne1
$$

$$
\Longrightarrow\quad\exists p\in\mathbb P,\quad
p\nmid q,\quad\chi(p)\ne1,\quad p\le\frac45(\ln q)^2.
$$

[GammaUniformTightStart.lean](../PseudoPrime/LLS/GammaUniformTightStart.lean) の
`exists_prime_outside_subgroup_le_gamma_four_fifths_19787` と
`exists_prime_character_ne_one_le_gamma_four_fifths_19787` が対応する。
部分群指数・法の素因数構成の追加条件はない。
符号付きGamma評価と非単元費用を一様に抑え、最小部分群外素数にも接続している。

S1の精密上界は $F_{\mathrm{prec}}(q)\ge L^2$ なので、
$q\ge10^{19787}$ では係数4/5の式が小さい。
$q < 10^{19787}$ では、正確な素因数損失を使う任意半径の条件とは別に、
掲載した明示式の中では $F_{\mathrm{prec}}(q)$ が最小となる。

## S2　非1指標値・部分群の像の外の素数証人

### 原式の仕様と小素因数排除

S2の各節では $L=\ln q$、 $u=\ln L$ とする。
各改良式では、半径根の記号を $R$、その二乗上界の記号を $F$ とし、同じ添字を付けて区別する。

$$
\begin{gathered}
\mathrm{GRH},\quad q\ge3000,\quad H\subsetneq G_q,\\
\forall r\in\mathbb P,\quad r < L^2\Longrightarrow r\nmid q
\end{gathered}
\quad\Longrightarrow\quad
\exists p\in\mathbb P,\quad p\le L^2,\quad[p]_q\notin\iota_q(H).
$$

公開仕様 `llsTheorem11S2` を証明する `llsTheorem11S2_of_grh` は
[Theorem11S2.lean](../PseudoPrime/LLS/Theorem11S2.lean) にある。
小素因数を除外する前提の不等号は狭義であり、証人の上界の不等号は広義である。
結論には $p\nmid q$ が含まれず、上界と等しい素数が非単元となる場合も許す。

証明途中の `exists_prime_not_one_le_log_sq` は、非主指標の値が $1$ でない素数を与える。ここでは値 $0$ も許される。この中間定理自体には小素因数排除の前提がなく、公開 S2 はその結果を用いて元の仕様を満たす。

### 開始点5への拡張と有限区間

開始点を5へ拡張した定理では、 $\iota_q:G_q\hookrightarrow\mathbb Z/q\mathbb Z$ を自然な埋め込みとして、次を証明した。

$$
\begin{gathered}
\mathrm{GRH},\qquad q\in\mathbb N,\qquad q\ge5,\qquad H\subsetneq G_q,\\
\forall r\in\mathbb P,\quad r < (\ln q)^2\Longrightarrow r\nmid q
\end{gathered}
$$

$$
\Longrightarrow\quad
\exists p\in\mathbb P,\quad p\le(\ln q)^2,\quad [p]_q\notin\iota_q(H).
$$

[Part2FromFive.lean](../PseudoPrime/LLS/Part2FromFive.lean) の `llsTheorem11S2_from_five_of_grh` がこの追加定理である。
同ファイルの `exists_prime_outside_part2_finite` は、 $5\le q < 3000$ についてGRHも小素因数排除も使わずに同じ結論を証明する。
$5\le q < 79$ は小さい素因数または群生成のカーネル検証、 $79\le q < 3000$ はPart 1の既存の19・43の生成証明書を用いる。
$q\ge3000$ は上記の解析定理へ接続する。原論文の仕様 `llsTheorem11S2` の前提は変更していない。

### 小素因数排除を仮定しない対数二乗上界

非主指標については、小素因数排除を仮定せずに次が成立する。

$$
\begin{gathered}
\mathrm{GRH},\qquad q\in\mathbb N,\qquad q\ge5,\\
\chi\in\mathrm{DirChar}_{\mathbb C}(q),\qquad \chi\ne1
\end{gathered}
$$

$$
\Longrightarrow\quad \exists p\in\mathbb P,\quad
p\le(\ln q)^2,\qquad \chi(p)\ne1.
$$

[CharacterPart2FromFive.lean](../PseudoPrime/LLS/CharacterPart2FromFive.lean) の
`exists_prime_not_one_le_log_sq_from_five` がこの主張を証明する。
$5\le q < 3000$ では、有限証明を指標の単数群上の核に適用するためGRHも不要である。
$q\ge3000$ では既存の `exists_prime_not_one_le_log_sq` を用いる。
結論は $\chi(p)=0$ を許し、 $p\nmid q$ は主張しない。

同ファイルの `exists_prime_outside_subgroup_image_le_log_sq_from_five` は、
この指標版から次の部分群版を導く。

$$
\mathrm{GRH},\qquad q\ge5,\qquad H\subsetneq G_q
\quad\Longrightarrow\quad
\exists p\in\mathbb P,\quad p\le(\ln q)^2,\quad [p]_q\notin\iota_q(H).
$$

この主張にも小素因数排除の前提は不要である。

### 補正4.5571と開始点5からの解析的証明

$$
R_{4.5571}(q)=L-2u+\frac{45571}{10000},\qquad
F_{4.5571}(q)=R_{4.5571}(q)^2.
$$

$$
\mathrm{GRH},\qquad q\in\mathbb N,\qquad q\ge5,\qquad
H\subsetneq(\mathbb Z/q\mathbb Z)^\times
\quad\Longrightarrow\quad
\exists p\in\mathbb P,\quad p\le F_{4.5571}(q),\quad
[p]_q\notin\iota_q(H).
$$

[FinerPart2FromFive.lean](../PseudoPrime/LLS/FinerPart2FromFive.lean) の
`exists_prime_outside_finerPart2_from_five` がこの主張を証明する。
小素因数排除は仮定せず、非単元の素数も許す。
指標版と全域での解析的証明は次のとおりである。

$$
\begin{gathered}
\mathrm{GRH},\quad q\in\mathbb N,\quad q\ge5,\\
\chi\in\mathrm{DirChar}_{\mathbb C}(q),\quad \chi\ne1
\end{gathered}
$$

$$
\Longrightarrow\quad
\exists p\in\mathbb P,\quad
p\le F_{4.5571}(q),\quad \chi(p)\ne1.
$$

[AnalyticFinerPart2FromFive.lean](../PseudoPrime/LLS/AnalyticFinerPart2FromFive.lean) の
`exists_prime_not_one_le_finerPart2Root_from_five_analytic` がこの主張を証明する。
法の有限検査を使わず、 $5\le q\le500$ は逆数重み付き明示公式だけで、
$q\ge501$ は切断点50以上・対数誤差 $-5/2$ の比較で証明する。
ただし、少数の実定数については、対数を有理数の区間で評価する検証を用いる。
同ファイルの `exists_prime_outside_finerPart2_from_five_analytic` は、
小素因数排除の前提なしで真部分群の像の外の素数を与える。
いずれも非単元を許し、 $p\nmid q$ は主張しない。

$$
q\ge17400\quad\Longrightarrow\quad
F_{4.5571}(q) < (\ln q)^2.
$$

Euler定数の上界 $28861/50000=0.57722$ と零点質量の上界 $231/10000=0.0231$ から、
逆数重み付き和の損失を $31551/20000=1.57755$ 以下へ改善した。
[FinerLLSConstants.lean](../PseudoPrime/AnalyticNumberTheory/RiemannXi/FinerLLSConstants.lean)
がこれらの数値を証明し、
[FinerPart2CutoffBounds.lean](../PseudoPrime/Analysis/FinerPart2CutoffBounds.lean)
が半径と開始点の比較を与える。補正4.558の旧定理も保持している。

### 切断点依存の逆数損失を使う明示半径

前節の半径根 $R_{4.5571}(q)$ を参照根とし、補助関数 $s$ と適応半径を次で定める。添字 $\mathrm{ad}$ は切断点依存の逆数損失を使う評価を表す。

$$
\begin{aligned}
s(t)&=\frac{78861}{50000}+\frac{231}{5000(t-1)}-\frac{16033}{9000t^2}\quad(t > 1),\\
R_{\mathrm{ad}}(q)&=L-2u+\frac{701}{500}+2s(R_{4.5571}(q)),\\
F_{\mathrm{ad}}(q)&=R_{\mathrm{ad}}(q)^2.
\end{aligned}
$$

$$
\begin{gathered}
\mathrm{GRH},\quad q\in\mathbb N,\quad q\ge600,\\
\chi\in\mathrm{DirChar}_{\mathbb C}(q),\quad\chi\ne1
\end{gathered}
$$

$$
\Longrightarrow\quad
\exists p\in\mathbb P,\quad p\le F_{\mathrm{ad}}(q),\quad \chi(p)\ne1.
$$

$$
q\ge600\Longrightarrow F_{\mathrm{ad}}(q) < F_{4.5571}(q),\qquad
q\ge16000\Longrightarrow F_{\mathrm{ad}}(q) < (\ln q)^2.
$$

[AdaptiveReciprocalWitnessBounds.lean](../PseudoPrime/LLS/AdaptiveReciprocalWitnessBounds.lean) の
`exists_prime_not_one_le_adaptivePart2Root` が証人の存在を証明する。
真部分群版も同ファイルにある。非単元を許し、小素因数排除は仮定しない。
半径は陰的な方程式を解かずに評価できる有理式である。

証明では $U_\zeta(X)=\sum_{1\le m\le X}\Lambda(m)m^{-1}(1-m/X)$ とする。
RHの下で次の点ごとの下界を使う。

$$
y > 0,\quad y^2\ge2
\quad\Longrightarrow\quad
U_\zeta(y^2)\ge\ln(y^2)-r(y),\qquad
r(y)=\frac{78861}{50000}+\frac{231}{5000y}-\frac{16033}{9000y^2}.
$$

参照根を $t=R_{4.5571}(q)$ と置く。 $t\ge7$ と $t-1\le y\le t$ に対し、 $r(y)\le s(t) < 31551/20000$ を証明する。
これにより明示根 $R_{\mathrm{ad}}(q)$ が点ごとの損失を使う半径条件を満たす。
Part 1の正確な素因数費用を保持する条件にも、同じ $r(y)$ を接続した。
既存の開始点5の補正式と開始点600の式は、それぞれ独立した定理として公開する。

### 対数補正を保持したGamma上界の非主指標版

$$
L=\ln q,\qquad
F_\Gamma(q)=\frac{99}{40}\left(\frac{500}{821}L+3\right)^2.
$$

$$
\mathrm{GRH},\quad q\in\mathbb N,\quad L\ge300,\quad
\chi\in\mathrm{DirChar}_{\mathbb C}(q),\quad\chi\ne1
\quad\Longrightarrow\quad
\exists p\in\mathbb P,\quad p\le F_\Gamma(q) < L^2,\quad\chi(p)\ne1.
$$

[ClippedAffineWitnessBounds.lean](../PseudoPrime/LLS/ClippedAffineWitnessBounds.lean) の
`exists_prime_ne_one_le_clippedAffine` を共通の上端 $A=q$ に適用する。
値0を含む $\chi(p)\ne1$ を証人条件とする。
平滑Mangoldt和の切断対数補正を共通誤差の評価前に保持し、
補正項と有限切断の境界項を正確に計算する。
主指標の誤差分子から尺度依存の対数費用を除き、認証済みEuler和と解析的な尾部を組み合わせた。
根の加法定数3と解析的適用開始 $L\ge300$ を、連続した半直線上で証明している。

### 対数補正を保持したGamma上界の真部分群版

上の $L=\ln q$、 $F_\Gamma(q)$ を使う。

$$
\mathrm{GRH},\quad q\in\mathbb N,\quad L\ge300,\quad H\subsetneq G_q
\quad\Longrightarrow\quad
\exists p\in\mathbb P,\quad p\le F_\Gamma(q) < L^2,\quad
[p]_q\notin\iota_q(H).
$$

同じファイルの `exists_prime_outside_subgroup_le_clippedAffine` が対応する。
商群の非主指標を引き戻し、上記の指標版から部分群の像の外の素数を得る。
S2と同じく、剰余環の非単元も証人に含む。

### 端点核による上界61の非主指標版

ここでは $L=\ln q$ とする。

$$
\mathrm{GRH},\quad q\in\mathbb N,\quad q\ge3,\quad L\le9,\quad
\chi\in\mathrm{DirChar}_{\mathbb C}(q),\quad\chi\ne1
\quad\Longrightarrow\quad
\exists p\in\mathbb P,\quad p\le61,\quad\chi(p)\ne1.
$$

[FullEndpointEightyOneRange.lean](../PseudoPrime/LLS/FullEndpointEightyOneRange.lean) の
`PaperStatements.exists_prime_ne_one_le_sixty_one_of_log_le_nine` が対応する。
法の有限列挙は使わず、半径8の端点分離式を解析的に抑える。
値0も認め、素数2も候補に含む。

### 端点核による上界61の真部分群版

$$
\mathrm{GRH},\quad q\in\mathbb N,\quad q\ge3,\quad L=\ln q\le9,\quad
H\subsetneq G_q
\quad\Longrightarrow\quad
\exists p\in\mathbb P,\quad p\le61,\quad[p]_q\notin\iota_q(H).
$$

[FullEndpointEightyOneSubgroup.lean](../PseudoPrime/LLS/FullEndpointEightyOneSubgroup.lean) の
`PaperStatements.exists_prime_outside_subgroup_le_sixty_one` が対応する。
商群の非主指標を引き戻し、上の指標版を適用する。剰余環の非単元も証人になる。

### 係数81/100の有界解析区間における非主指標版

$$
\mathrm{GRH},\quad q\in\mathbb N,\quad9\le L=\ln q\le26,\quad
\chi\in\mathrm{DirChar}_{\mathbb C}(q),\quad\chi\ne1
\quad\Longrightarrow\quad
\exists p\in\mathbb P,\quad p\le\frac{81}{100}L^2,\quad\chi(p)\ne1.
$$

`FullEndpointEightyOneRange.lean` の `PaperStatements.exists_prime_ne_one_le_eightyOne_log_sq` が対応する。
正の間隔を0へ近づけた端点式を使い、半径を $(9/10)L$ とする。
対数の凹性による弦の下界と連続区間の多項式正値性で証明した。
法の有限検査や、未知の指標和に関する仮定は残していない。

### 係数81/100の有界解析区間における真部分群版

$$
\mathrm{GRH},\quad q\in\mathbb N,\quad9\le L=\ln q\le26,\quad
H\subsetneq G_q
\quad\Longrightarrow\quad
\exists p\in\mathbb P,\quad p\le\frac{81}{100}L^2,\quad
[p]_q\notin\iota_q(H).
$$

`FullEndpointEightyOneSubgroup.lean` の `PaperStatements.exists_prime_outside_subgroup_le_eightyOne_log_sq` が対応する。
上の非主指標版から商群指標を使って導く。非単元と素数2も証人に含むため、負値の奇素数Jacobi証人へそのまま転用しない。

### 中間尺度での区分線形半径による改良

$L=\ln q$ とし、次の半径を定める。

$$
R_{\mathrm{aff}}(L)=
\begin{cases}
\dfrac{800}{837}\left(L-\dfrac{167}{100}\right), & L\le\dfrac{703}{20},\\
\dfrac{3200}{3309}\left(L-\dfrac{103}{50}\right), & \dfrac{703}{20} < L\le\dfrac{1706}{25},\\
\dfrac{3200}{3259}\left(L-\dfrac{153}{50}\right), & \dfrac{1706}{25} < L\le\dfrac{6671}{50},\\
\dfrac{12800}{12927}\left(L-\dfrac{83}{20}\right), & \dfrac{6671}{50} < L.
\end{cases}
$$

非主指標版の前提と主張は次のとおりである。

$$
\begin{gathered}
\mathrm{GRH},\quad q\in\mathbb N,\quad q>0,\quad
\chi\text{ は法 }q\text{ のDirichlet指標},\quad\chi\ne1,\\
\frac{1339}{50}\le L\le\frac{26269}{100}
\\
\Longrightarrow\quad
\exists p\text{ は素数},\quad p\le R_{\mathrm{aff}}(L)^2,\quad\chi(p)\ne1.
\end{gathered}
$$

真部分群版では、同じGRHと範囲のもとで次が成立する。

$$
H\subsetneq(\mathbb Z/q\mathbb Z)^\times
\quad\Longrightarrow\quad
\exists p\text{ は素数},\quad p\le R_{\mathrm{aff}}(L)^2,\quad
[p]_q\notin\iota_q(H).
$$

対応する定理は
[非主指標版](../PseudoPrime/LLS/MidscaleEndpointRadius.lean) の
`exists_prime_ne_one_le_midscale_radius_sq` と
[真部分群版](../PseudoPrime/LLS/MidscaleEndpointSubgroup.lean) の
`exists_prime_outside_subgroup_le_midscale_radius_sq` である。
素数2と非単元も証人に含む。奇素数の負値Jacobi証人にはそのまま適用しない。

半径は接続点でそれぞれ32、64、128となり、両端では24、256となる。
4区間の四次式を各5個の有理Bernstein係数で認証し、対数の凹性で実際の自然対数へ移した。
法の有限列挙は使わない。
[比較定理](../PseudoPrime/LLS/MidscaleEndpointComparison.lean)
`midscaleEndpointRadius_sq_lt_adaptive_sq` により、区間全体で

$$
\frac{1339}{50}\le L\le\frac{26269}{100}
\quad\Longrightarrow\quad
R_{\mathrm{aff}}(L)^2 < F_{\mathrm{ad}}(q)
$$

が成立する。

### S2で最良となる掲載式の区間

比較対象は、小素因数排除を仮定せず、非単元も許す非1指標値・真部分群の像の外の素数証人とする。
$L=\ln q$ とし、上記の $R_{\mathrm{ad}}(q)$、 $F_{\mathrm{ad}}(q)$、 $F_\Gamma(q)$ を使う。
ここで最良とは、この節の一般S2向け掲載式のうち適用可能な式が最小となることを指す。

| 条件 | 最小となる掲載上界 | 非主指標版の対応定理 |
|---|---|---|
| $5\le q < 600$ | $L^2$ | [`exists_prime_not_one_le_log_sq_from_five`](../PseudoPrime/LLS/CharacterPart2FromFive.lean) |
| $600\le q$、 $L\le9$、 $R_{\mathrm{ad}}(q)\ge L$、 $L^2\le61$ | $L^2$ | [`exists_prime_not_one_le_log_sq_from_five`](../PseudoPrime/LLS/CharacterPart2FromFive.lean) |
| $600\le q$、 $L\le9$、 $R_{\mathrm{ad}}(q) < L$、 $F_{\mathrm{ad}}(q)\le61$ | $F_{\mathrm{ad}}(q)$ | [`exists_prime_not_one_le_adaptivePart2Root`](../PseudoPrime/LLS/AdaptiveReciprocalWitnessBounds.lean) |
| $600\le q$、 $L\le9$、 $61 < L^2$、 $61 < F_{\mathrm{ad}}(q)$ | $61$ | [`PaperStatements.exists_prime_ne_one_le_sixty_one_of_log_le_nine`](../PseudoPrime/LLS/FullEndpointEightyOneRange.lean) |
| $9 < L\le81/4$ | $(64/81)L^2$ | [`PaperStatements.exists_prime_ne_one_le_eightNinths_log_sq`](../PseudoPrime/LLS/FullEndpointEightNinthsRange.lean) |
| $81/4 < L\le26$ | $(81/100)L^2$ | [`PaperStatements.exists_prime_ne_one_le_eightyOne_log_sq`](../PseudoPrime/LLS/FullEndpointEightyOneRange.lean) |
| $26 < L < 1339/50$ または $26269/100 < L < 300$ | $F_{\mathrm{ad}}(q)$ | [`exists_prime_not_one_le_adaptivePart2Root`](../PseudoPrime/LLS/AdaptiveReciprocalWitnessBounds.lean) |
| $1339/50\le L\le26269/100$ | $R_{\mathrm{aff}}(L)^2$ | [`PaperStatements.exists_prime_ne_one_le_midscale_radius_sq`](../PseudoPrime/LLS/MidscaleEndpointRadius.lean) |
| $L\ge300$、 $q < 10^{19787}$ | $F_\Gamma(q)$ | [`exists_prime_ne_one_le_clippedAffine`](../PseudoPrime/LLS/ClippedAffineWitnessBounds.lean) |
| $q\ge10^{19787}$ | $(4/5)L^2$ | [`exists_prime_character_ne_one_le_gamma_four_fifths_19787`](../PseudoPrime/LLS/GammaUniformTightStart.lean) |

$L\le9$ の範囲では、上界61と既存の2式を表の条件で比較する。 $9 < L\le26$ では、
`FullEndpointEightyOneSubgroup.lean` の `PaperStatements.fullEndpoint_eightyOne_lt_adaptive` により
$(81/100)L^2 < F_{\mathrm{ad}}(q)$ が成立し、 $L^2$ よりも小さい。 $L > 26$ では $F_{\mathrm{ad}}(q) < L^2$ である。

$L\ge300$ では `clippedAffine_cutoff_lt_adaptive` により $F_\Gamma(q) < F_{\mathrm{ad}}(q)$ であり、 $F_\Gamma(q) < L^2$ も証明済みである。
また $F_\Gamma(q) > (99/40)(500/821)^2L^2 > (4/5)L^2$ なので、係数4/5の式が適用できる範囲ではその式が小さい。
$q\ge10^{19787}$ では $R_{\mathrm{ad}}(q) > L-2\ln L+4 > (9/10)L$ であり、係数4/5の式が適応半径の二乗より小さい。
根が正なので、 $F_{\mathrm{ad}}(q) < L^2$ と $R_{\mathrm{ad}}(q) < L$ は同値である。
切替条件はこの正確な式の比較で定め、近似した交点を定理の前提には使わない。
補正4.5571の根は適応半径を定める参照根として使う。
独立した上界としては $q < 600$ で $L^2$、 $q\ge600$ で適応半径の二乗より大きい。
補正4.602・4.558の式も最良区間を持たないため、この比較には含めない。
S1は $p\nmid q$ を保証する別の問題であり、このS2の表と比較しない。

## 導手と除外素数費用を分離した構造別上界

この節では $f_\chi$ を $\chi$ の原始導手とし、正整数 $m$ に対して

$$
E(m)=\sum_{\substack{\ell\mid m\\\ell\text{ は素数}}}\ln\ell
=\ln\mathrm{rad}(m)
$$

と置く。 $\mathrm{rad}(m)$ は $m$ の異なる素因数の積である。

正整数 $f$ と実数 $E\ge0$ に対し、

$$
\begin{aligned}
R(f,E)&=\left(\frac{2429}{720}\ln f+\frac{19171}{400}+
\sqrt{\left(\frac{2429}{720}\ln f+\frac{19171}{400}\right)^2+\frac{14}{5}E}\right)^2,\\
T(f,E)&=4\left(\frac{2429}{720}\ln f+\frac{19171}{400}\right)^2+\frac{28}{5}E
\end{aligned}
$$

と定義する。

$$
\begin{gathered}
\mathrm{GRH},\quad q\in\mathbb N,\quad q > 0,\quad\chi\pmod q,\quad\chi\ne1
\\
\Longrightarrow\quad\exists p\text{ は素数},\quad
p\nmid q,\quad\chi(p)\ne1,\quad
p\le R(f_\chi,E(q)).
\end{gathered}
$$

[DirectHadamardConductorBounds.lean](../PseudoPrime/LLS/DirectHadamardConductorBounds.lean) の
`exists_prime_ne_one_le_direct_conductor_root` が対応する。
主指標を $1$ と書く。大きい法を要求する追加の開始点はない。
原始指標の対数重み付き和を二つの尺度で差し引き、素数一次項の除外費用と高い素数冪を分ける。
導手を元の法へ緩和せず、除外費用を $E(q)$ として分離した上界である。

$$
\begin{gathered}
\mathrm{GRH},\quad q\in\mathbb N,\quad q > 0,\quad H\subsetneq(\mathbb Z/q\mathbb Z)^\times,\quad
\chi\ne1,\quad\forall u\in H,\quad\chi(u)=1
\\
\Longrightarrow\quad\exists p\text{ は素数},\quad
p\nmid q,\quad[p]_q\notin H,\quad
p\le R(f_\chi,E(q)).
\end{gathered}
$$

`exists_prime_outside_le_direct_character_conductor` がこの真部分群版を証明する。
小導手の指標を選べる入力では法の対数二乗への依存を弱められる。
また、次の比較も全域でLeanにより証明した。

$$
f\in\mathbb N,\quad f\ge1,\quad E\ge0
\quad\Longrightarrow\quad
R(f,E)\le T(f,E).
$$

任意の探索上限を受け取る比較補題から、二次不等式の大きい根を使って $R$ を導いた。
根の半径の単調性により、従来の半径係数 $287/80$・定数 $4327/80$ を使う式以下となることもLeanで証明した。
[DirectHadamardConductorBounds.lean](../PseudoPrime/LLS/DirectHadamardConductorBounds.lean) で、
指標和を尺度100以上で $((347/180)\ln f+1213/100)\sqrt x$ 以下と評価し、尺度200以上の証人不存在からの比較へ接続した。
原始Hadamard定数の絶対値を、実部の逆数公式から $(11/18)\ln f+29/10$ 以下と直接評価した。
この上界と端点上界 $(2/3)\ln f+9/2$ を別々に使い、Hadamard定数を端点ノルムへ緩める損失を除いた。
根の上界は自動的に200を超えるため、定数枝との最大値は不要である。入力整数の有限証明書は使っていない。
### 偶指標に対する定数の改善

この項では

$$
R_{\mathrm{even}}(f,E)=\left(\frac{2429}{720}\ln f+\frac{17939}{400}+
\sqrt{\left(\frac{2429}{720}\ln f+\frac{17939}{400}\right)^2+\frac{14}{5}E}\right)^2
$$

と置く。

$$
\begin{gathered}
\mathrm{GRH},\quad q\in\mathbb N,\quad q > 0,\quad\chi\pmod q,\quad\chi\ne1,\quad\chi(-1)=1\\
\Longrightarrow\quad\exists p\text{ は素数},\quad
p\nmid q,\quad\chi(p)\ne1,\quad p\le R_{\mathrm{even}}(f_\chi,E(q)).
\end{gathered}
$$

`exists_prime_ne_one_le_even_direct_conductor_root` が対応する。
偶指標では原始Hadamard定数の絶対値を $(11/18)\ln f+21/10$ 以下と評価できる。
一般指標用の加法定数 $19171/400$ より小さい $17939/400$ を使えるのは、この偶性を保持した場合である。

この評価は選んだ指標の導手にも依存するため、法だけで比較する前節の区間表には含めていない。


### 逆数公式の切断点を保持した拡張

逆数和と、その切断点 $x$ によるHadamard上界を次のように定める。
$\Lambda$ はvon Mangoldt関数である。

$$
\begin{aligned}
R_0(x)&=\sum_{1\le a\le x}\frac{\Lambda(a)}a(1-a/x),\\
C_\eta(f,x)&=\frac{\frac12(1-1/x)(\ln f-\ln\pi)-\eta+R_0(x)}{(1-1/\sqrt{x})^2},\\
F_{\eta,c}(f,x)&=\frac{11}{5}\min\left(\frac{11}{18}\ln f+c,C_\eta(f,x)\right)
+\frac12\left(\frac23\ln f+\frac92\right)+\frac14\ln f+\frac72,\\
A_{\eta,c}(f,x)&=\frac74F_{\eta,c}(f,x)+\frac{267}{10},\\
W_{\eta,c}(f,m,x)&=\left(A_{\eta,c}(f,x)+
\sqrt{A_{\eta,c}(f,x)^2+\frac{14}{5}E(m)}\right)^2.
\end{aligned}
$$

ここで $E(m)$ はこの節で定義した除外整数の素因数対数和である。

$$
\begin{gathered}
\mathrm{GRH},\quad q\ge1,\quad\chi\text{ は法 }q\text{ の非主指標},
\quad f=\mathrm{cond}(\chi),\quad x\ge64
\\
\Longrightarrow\quad\exists p\text{ は素数},\quad
p\nmid q,\quad\chi(p)\ne1,\quad p\le W_{1/4,29/10}(f,q,x).
\end{gathered}
$$

さらに $\chi(-1)=1$ なら、同じ結論で $W_{179/200,21/10}(f,q,x)$ を使える。
[VariableReciprocalConductorBounds.lean](../PseudoPrime/LLS/VariableReciprocalConductorBounds.lean) の
`exists_prime_ne_one_le_variable_reciprocal_root` と
`exists_prime_ne_one_le_even_variable_reciprocal_root` が対応する。

この切断点は証人探索上限とは独立に選べる。
固定Hadamard上界との小さい方を使うため、同じ導手・除外費用の従来の根上界以下となる。
偶指標では切断点100でも、指標和の加法定数を $1037/100$ から $25881/2500$ へ下げられることを証明した。
導手と素因数費用に依存するため、全入力一様の最良区間表には含めない。

### 導手依存の切断点による明示上界

$L=\ln f$ とし、次の関数を定義する。 $E(m)$ はこの節で定義した除外費用である。

$$
\begin{aligned}
A_{\mathrm{ad}}(L)&=\frac{707}{240}L+\frac{77}{10}\ln(L+8)+\frac{3557}{80},\\
U_{\mathrm{ad}}(f,m)&=\left(A_{\mathrm{ad}}(\ln f)+
\sqrt{A_{\mathrm{ad}}(\ln f)^2+\frac{14}{5}E(m)}\right)^2.
\end{aligned}
$$

$$
\begin{gathered}
\mathrm{GRH},\quad q\ge1,\quad\chi\text{ は法 }q\text{ の非主指標},
\quad f=\mathrm{cond}(\chi)
\\
\Longrightarrow\quad\exists p\text{ は素数},\quad
p\nmid q,\quad\chi(p)\ne1,\quad p\le U_{\mathrm{ad}}(f,q).
\end{gathered}
$$

[AdaptiveReciprocalConductorBounds.lean](../PseudoPrime/LLS/AdaptiveReciprocalConductorBounds.lean) の
`exists_prime_ne_one_le_adaptive_reciprocal_root` が対応する。
指標が部分群上で自明なら、同じ素数はその部分群の像の外にある。

逆数公式の切断点を $(\ln f+8)^2$ とし、主指標の逆数和を対数で上から評価した。
その結果、原始Hadamard定数の絶対値を $L/2+2\ln(L+8)+2$ 以下と証明した。
偶性や二次性を要求せず、切断点における有限和の計算も不要である。

$$
L\ge100\quad\Longrightarrow\quad
A_{\mathrm{ad}}(L)+\frac{77}{20}\le\frac{2429}{720}L+\frac{17939}{400}.
$$

したがって $\ln f\ge100$ では、同じ導手・除外費用を持つ従来の偶指標用の根上界以下となる。
100は比較を認証した十分条件であり、最小の交点とはしていない。
導手と素因数費用に依存するため、全入力一様の最良区間表には含めない。

### 推奨切断点による明示上界の改良

逆数公式の切断点を $x=\max(8,(\ln f)/2)^2$ と選ぶ。
既存の固定評価との最小値を保持する版に加え、次の明示包絡を証明した。

$$
\begin{aligned}
A_{\mathrm{cut}}(G)&=\frac{707}{240}G+\frac{77}{10}\ln G+\frac{2941}{80},\\
U_{\mathrm{cut}}(G,m)&=\left(A_{\mathrm{cut}}(G)+
\sqrt{A_{\mathrm{cut}}(G)^2+\frac{14}{5}E(m)}\right)^2.
\end{aligned}
$$

$$
\begin{gathered}
\mathrm{GRH},\quad q\ge1,\quad\chi\text{ は法 }q\text{ の非主指標},\quad
G\ge16,\quad\ln\mathrm{cond}(\chi)\le G
\\
\Longrightarrow\quad\exists p\text{ は素数},\quad
p\nmid q,\quad\chi(p)\ne1,\quad p\le U_{\mathrm{cut}}(G,q).
\end{gathered}
$$

[SelectedReciprocalConductorBounds.lean](../PseudoPrime/LLS/SelectedReciprocalConductorBounds.lean) の
`exists_prime_ne_one_le_selected_envelope_root` が対応する。
原始指標では $G\ge16$、 $\ln f\le G$ からHadamard定数の絶対値を $G/2+2\ln G$ 以下と証明した。
実導手が小さい場合も、固定評価による分岐でこの包絡に含める。
半径と根上界は、固定した除外整数に対して $G\ge1$ で単調増加する。

$$
\begin{aligned}
G\ge16&\quad\Longrightarrow\quad
A_{\mathrm{cut}}(G)+\frac{77}{10}\le A_{\mathrm{ad}}(G),\\
G\ge57&\quad\Longrightarrow\quad
A_{\mathrm{cut}}(G)\le\frac{2429}{720}G+\frac{17939}{400}.
\end{aligned}
$$

したがって、新しい明示半径は前段の可変尺度の半径より適用範囲全体で小さく、
$G\ge57$ では直接Hadamard評価の偶指標用の固定半径以下にもなる。
57は認証済みの十分条件であり、交点の最適値とはしていない。
導手と素因数費用に依存するため、全入力一様の最良区間表には含めない。

### 三次核による導手別上界の改良

前節の除外費用 $E(m)$ を用い、

$$
\begin{aligned}
A_3(G)&=\frac{10}{13}G+\frac{63}{2},\\
R_3(G,m)&=\left(A_3(G)+\sqrt{A_3(G)^2+
\frac85G+28+\frac83E(m)}\right)^2
\end{aligned}
$$

と定義する。原始指標版の前提と結論は次のとおりである。

$$
\begin{gathered}
\mathrm{GRH},\quad f\ge2,\quad m\ge1,\quad
\chi\text{ は法 }f\text{ の原始非主指標},\quad \ln f\le G
\\
\Longrightarrow\quad\exists p\text{ は素数},\quad
p\nmid m,\quad\chi(p)\ne1,\quad p\le R_3(G,m).
\end{gathered}
$$

一般の非主指標では導手へ移し、法の素因数を除外する。

$$
\begin{gathered}
\mathrm{GRH},\quad q\ge1,\quad
\chi\text{ は法 }q\text{ の非主指標},\quad \ln\mathrm{cond}(\chi)\le G
\\
\Longrightarrow\quad\exists p\text{ は素数},\quad
p\nmid q,\quad\chi(p)\ne1,\quad p\le R_3(G,q).
\end{gathered}
$$

[TightCubicRadiusComparisons.lean](../PseudoPrime/LLS/TightCubicRadiusComparisons.lean) の
`exists_prime_outside_le_tight_cubic_conductor_radius` と
`exists_prime_ne_one_le_tight_cubic_conductor_radius` が対応する。
前節の $G\ge16$ という条件は、この存在定理には不要である。

$$
G\ge16\quad\Longrightarrow\quad R_3(G,m)\le U_{\mathrm{cut}}(G,m).
$$

定数 $34,33$ の旧半径以下となる比較と、旧半径に対する既存の比較から従う。新しい比較は `tightCubicExclusionRadius_sq_le_previous` で証明した。
導手と除外費用を固定すれば、前節の推奨切断点の包絡を適用範囲全体で置き換えられる。
法だけで比較する全入力一様の最良区間表には含めない。

三次核の指標和では、平方根項の加法定数 $97/130$ と残りの定数 $103729/15000$ を保持した。これにより、半径の加法定数を $34$ から $63/2$、根内の定数を $33$ から $28$ に下げた。新しいGamma評価や零点評価は仮定していない。

さらに、除外素数ごとの指標値を残す費用を用いる。

$$
\begin{aligned}
E_\chi(m)&=\sum_{p\mid m,\ p\text{ は素数}}(1-\Re\chi(p))\ln p,\\
R_{3,\chi}(G,m)&=\left(A_3(G)+\sqrt{A_3(G)^2+
\frac85G+28+\frac43E_\chi(m)}\right)^2.
\end{aligned}
$$

$$
\begin{gathered}
\mathrm{GRH},\quad f\ge2,\quad m\ge1,\quad
\chi\text{ は法 }f\text{ の原始非主指標},\quad\ln f\le G
\\
\Longrightarrow\quad\exists p\text{ は素数},\quad
p\nmid m,\quad\chi(p)\ne1,\quad p\le R_{3,\chi}(G,m).
\end{gathered}
$$

$$
0\le E_\chi(m)\le2E(m),\qquad
G\ge0\quad\Longrightarrow\quad R_{3,\chi}(G,m)\le R_3(G,m).
$$

[TightCubicConductorBounds.lean](../PseudoPrime/LLS/TightCubicConductorBounds.lean) の
`exists_prime_outside_le_tight_cubic_exclusion_radius` は $E_\chi(m)$ の任意の上界を受け取る。
除外素数でも $\chi(p)=1$ なら費用は0となる。
一般の非主指標 $\chi$ には、その原始指標 $\theta$ を用いて
$p\le R_{3,\theta}(G,q)$ を得る。対応する定理は
`exists_prime_ne_one_le_tight_cubic_sensitive_radius` である。

#### 切断点以下の除外費用による三次上界の改良

前項の $A_3(G)$ を用い、切断点 $X$ ごとの費用と上界を

$$
\begin{aligned}
E_\chi(m;X)&=\sum_{\substack{p\mid m,\ p\le X\\p\text{ は素数}}}
(1-\Re\chi(p))\ln p,\\
R_{3,\chi}(G,m;X)&=\left(A_3(G)+\sqrt{A_3(G)^2+
\frac85G+28+\frac43E_\chi(m;X)}\right)^2
\end{aligned}
$$

と定義する。

$$
\begin{gathered}
\mathrm{GRH},\quad f\ge2,\quad m\ge1,\quad
\chi\text{ は法 }f\text{ の原始非主指標},\quad\ln f\le G,\\
R_{3,\chi}(G,m;X)\le X
\\
\Longrightarrow\quad\exists p\text{ は素数},\quad
p\le X,\quad p\nmid m,\quad\chi(p)\ne1.
\end{gathered}
$$

[TruncatedCubicExclusion.lean](../PseudoPrime/LLS/TruncatedCubicExclusion.lean) の
`exists_prime_outside_le_of_truncated_cubic_radius` が対応する。
除外整数を $X$ 以下の素因数の積に置き換えて既存の抽出定理を適用する。
抽出した素数も $X$ 以下なので、元の $m$ を割らないことが従う。
$X$ より大きい除外素数の費用は不要である。

初期上界と反復を

$$
X_0=R_{3,\chi}(G,m),\qquad X_{j+1}=R_{3,\chi}(G,m;X_j)
$$

と定めると、同じ前提のもとで

$$
\begin{gathered}
\forall j\in\mathbb N,\quad X_{j+1}\le X_j,\quad
R_{3,\chi}(G,m;X_j)\le X_j,\\
\forall j\in\mathbb N,\quad\exists p\text{ は素数},\quad
p\le X_j,\quad p\nmid m,\quad\chi(p)\ne1,\\
\exists j_0\in\mathbb N,\quad\forall j\ge j_0,\quad X_j=X_{j_0}.
\end{gathered}
$$

[TruncatedCubicIteration.lean](../PseudoPrime/LLS/TruncatedCubicIteration.lean) の
`truncatedCubicIterate_step_le`、`exists_prime_outside_le_truncatedCubicIterate`、
`truncatedCubicIterate_eventually_constant` が対応する。
費用の単調性から、各反復値は有効な上界を保つ。
費用を決める素因数の部分集合は有限個なので、反復は有限段で一定になる。
この有限性は汎用的な有限集合の議論で証明し、数値証明書は生成していない。
指標と素因数に依存するため、全入力一様の最良区間表には含めない。

#### 平方因子費用を吸収する汎用半径と定数2434/75

実数 $c,G,E$ に対し、

$$
\begin{aligned}
B_c(G)&=\frac{10}{13}G+c,\\
r_c(G,E)&=B_c(G)+\sqrt{B_c(G)^2+\frac83E},\\
\mathcal R(G,E)&=\left(A_3(G)+
\sqrt{A_3(G)^2+\frac85G+28+\frac43E}\right)^2
\end{aligned}
$$

と定める。前節の $A_3(G)=(10/13)G+63/2$ を用いる。

$$
\begin{gathered}
G,E\ge0,\quad c\ge\frac{63}{2},\quad
\frac{44}{15}\le4\left(c-\frac{63}{2}\right)\frac{10}{13},\quad
28\le4\left(c-\frac{63}{2}\right)c
\\
\Longrightarrow\quad
\mathcal R(G,G+2E)\le r_c(G,E)^2.
\end{gathered}
$$

`tightCubicExclusionRadius_le_square_factor_with_constant` は、除外費用の導手項を吸収する定数の条件を明示する。
定数ごとの証明を繰り返さず、この汎用定理を使う。

$$
G,E\ge0\quad\Longrightarrow\quad
\mathcal R(G,G+2E)\le r_{2434/75}(G,E)^2,\qquad
r_{2434/75}(G,E) < r_{65/2}(G,E).
$$

[ParameterizedCubicSquareFactorRadius.lean](../PseudoPrime/LLS/ParameterizedCubicSquareFactorRadius.lean) の
`tightCubicExclusionRadius_le_square_factor2434` と
`cubicSquareFactorRadius2434_lt_tight` が対応する。
$c=2434/75$ では $c-63/2=143/150$ となり、導手係数の条件は等号で成立する。
全ての非負予算で従来の半径を改善するが、導手と平方因子の費用に依存するため、全入力一様の最良区間表には含めない。

#### 三次核の部分群版

$$
\begin{gathered}
\mathrm{GRH},\quad q\ge1,\quad
\chi\in\mathrm{DirChar}_{\mathbb C}(q),\quad\chi\ne1,\quad
\ln\mathrm{cond}(\chi)\le G,
\\
H\le G_q,\quad
\forall u\in H,\quad\chi(\iota_q(u))=1
\\
\Longrightarrow\quad
\exists p\in\mathbb P,\quad
p\nmid q,\quad p\le R_3(G,q),\quad[p]_q\notin H.
\end{gathered}
$$

`LLS.exists_prime_outside_le_tight_cubic_conductor_radius` が対応する。
指標が $H$ 上で自明であることと、素数での指標値が1でないことから部分群の像の外にあることを示す。
$p\nmid q$ を保証するため、結論の $[p]_q$ は単元剰余である。

## 小部分群に対する無条件の指数改善

固定した実数 $\eta,A$ の前提を

$$
0 < \eta < 1,\qquad A > \frac1\eta
$$

とする。このとき、次をGRHなしで証明した。

$$
\begin{gathered}
\exists Q_0=Q_0(\eta,A)\in\mathbb N,\quad
\forall q\in\mathbb N,\quad\forall H\le G_q,\\
q\ge Q_0,\quad q > 1,\quad
\lvert H\rvert\le q^{1-\eta}
\\
\Longrightarrow\quad
\exists p\in\mathbb P,\quad
p\nmid q,\quad[p]_q\notin H,\quad p\le(\ln q)^A.
\end{gathered}
$$

[SmallSubgroupPowerBounds.lean](../PseudoPrime/LLS/SmallSubgroupPowerBounds.lean) の
`eventually_exists_prime_outside_le_log_power_of_small_card` が対応する。
`eventually_exists_least_prime_outside_le_log_power_of_small_card` は、
集合 $\lbrace p\in\mathbb P\mid p\nmid q,\ [p]_q\notin H\rbrace$ の最小元にも同じ上界を与える。
開始点 $Q_0$ は $H$ に依存しないが、具体的な数値はまだ与えていない。

$\eta > 1/2$ なら $1/\eta < A < 2$ を選べるため、指数を $2$ 未満にできる。
この結果は部分群の位数に強い条件を課しており、固定指数の真部分群すべてに適用できるとは限らない。
法だけで比較する既存の数値区間表には含めていない。

証明では $B$ 以下で法を割らない素数のうち相異なる $k$ 個を選んだ積を数える。
積を $q$ 未満に収めれば、すべての候補素数が $H$ に属するとき、その個数は $\lvert H\rvert$ 以下となる。
Chebyshevの素数個数下界から、法の素因数を除いても十分な候補が残ることを示して矛盾を得る。
除外個数には $\omega(q)\le\ln q/\ln2$ を使い、有限証明書は追加していない。

## 共通核の係数が持つ下限

この節の $K$ は [PaperDefinitions.lean](../PseudoPrime/LLS/PaperDefinitions.lean) の
`MellinKernel` の要素とし、$\widetilde K$ をその逆Mellin変換とする。
局所的な記号を次のように定義する。

$$
\begin{aligned}
M_K&=\frac1{2\pi}\int_{\mathbb R}\lvert K(it)\rvert dt,\\
I_K(\lambda)&=\int_0^\lambda\frac{\Re\widetilde K(u)}{\sqrt u}du,\\
E_K&=\Re K(1/2),\\
D_K(h,\lambda)&=hI_K(\lambda)-E_K,\\
c_K(h,\lambda)&=\lambda
\left(\frac{(h-1)M_K}{D_K(h,\lambda)}\right)^2.
\end{aligned}
$$

前提と結論は次のとおりである。

$$
h\in\mathbb N,\quad h\ge2,\quad
\lambda > 0,\quad D_K(h,\lambda) > 0
\quad\Longrightarrow\quad c_K(h,\lambda)\ge\frac14.
$$

[QuarterCoefficient.lean](../PseudoPrime/LLS/MethodBarrier/QuarterCoefficient.lean) の
`ambientMethodCoefficient_ge_one_quarter` が対応する。
$I_K(\lambda)\le E_K$ と $I_K(\lambda)\le2M_K\sqrt\lambda$ を保持し、
$D_K(h,\lambda)\le2(h-1)M_K\sqrt\lambda$ を得て証明する。

`not_eventually_ambientMethodCoefficient_le_log_power_saving` は、
核・指数・切断値を尺度 $L$ に応じて変える場合にも、
この係数を固定した $\varepsilon > 0$ に対する $CL^{-\varepsilon}$ 以下にはできないことを証明する。
対象はこの共通核の係数式である。符号付き位相和など別の解析評価による改善は、この定理の対象に含まれない。

## 解析的評価を支える構成

| ファイル | 役割 |
|---|---|
| [Theorem11S1.lean](../PseudoPrime/LLS/Theorem11S1.lean) | S1 の半径・上下界のインターフェースと、上下界の矛盾から結論を導く構成 |
| [Theorem11S1FullLevel.lean](../PseudoPrime/LLS/Theorem11S1FullLevel.lean) | 一般・二次両経路で使う零点質量のインターフェース、法だけによる上界、数値比較 |
| [Theorem11S1Estimates.lean](../PseudoPrime/LLS/Theorem11S1Estimates.lean) | 一般指標の対数・逆数評価と導手補正から S1 の上界を供給 |
| [Theorem11S1Subgroup.lean](../PseudoPrime/LLS/Theorem11S1Subgroup.lean) | 商群指標の構成、真部分群版と最小素数版 |
| [Numerics.lean](../PseudoPrime/LLS/Numerics.lean) | S1 の実変数評価と厳密な上下界分離 |
| [LogResidueBoundGeneral.lean](../PseudoPrime/AnalyticNumberTheory/RiemannZeta/LogResidueBoundGeneral.lean)・[ReciprocalResidueBoundGeneral.lean](../PseudoPrime/AnalyticNumberTheory/RiemannZeta/ReciprocalResidueBoundGeneral.lean) | RH から Riemann 側の重み付き下界を供給 |
| [PrimitiveLogWeightedBounds.lean](../PseudoPrime/LLS/PrimitiveLogWeightedBounds.lean)・[PrimitiveReciprocalWeightedBounds.lean](../PseudoPrime/LLS/PrimitiveReciprocalWeightedBounds.lean) | 一般原始指標の GRH 上界 |
| [WeightedComparison.lean](../PseudoPrime/LLS/WeightedComparison.lean)・[WeightedComparisonGRH.lean](../PseudoPrime/LLS/WeightedComparisonGRH.lean) | 欠損・零点質量・誤差項を引数に持つ共通比較と GRH 構成 |
| [Theorem11S2SmallPrimeExclusion.lean](../PseudoPrime/LLS/Theorem11S2SmallPrimeExclusion.lean)・[Theorem11S2Numerics.lean](../PseudoPrime/LLS/Theorem11S2Numerics.lean) | 切断範囲内で指標値が1となる性質の移送と S2 の数値分離 |

### 有限区間に台を持つ有理Mellin核

$$
K(s)=\frac1{(s+1/2)(s+3/2)},\qquad
\widetilde K(u)=\sqrt{u}\max(1-u,0)\quad(u > 0).
$$

$$
c > -\frac12,\quad u > 0
\quad\Longrightarrow\quad
\mathrm{inverseMellin}(K,c,u)=\widetilde K(u),
\qquad K(1/2)=\frac12.
$$

$$
x > 0
\quad\Longrightarrow\quad
\sum_{m\ge0}\mathrm{summand}_{K,\chi}(x,m)
=\frac1{\sqrt{x}}\sum_{1\le m\le\lfloor x\rfloor}
\Lambda(m)\chi(m)(1-m/x).
$$

[ReciprocalKernel.lean](../PseudoPrime/LLS/ReciprocalKernel.lean) はすべての適格性条件を証明し、
[ReciprocalKernelArithmetic.lean](../PseudoPrime/LLS/ReciprocalKernelArithmetic.lean) は
この有限和をGRH下の完備L関数の明示公式へ接続する。
[ReciprocalKernelComparison.lean](../PseudoPrime/LLS/ReciprocalKernelComparison.lean) は、
非負Euler級数の初めの有限個の項を残した零点和評価を実際の有限指標和へ渡す。
留数と輪郭積分の明示的な数値評価は別途必要であり、新しい証人開始点を主張するものではない。

## 二次指標・Miller–Rabinへの接続

### PseudoSquareとExtensions

Jacobi記号の負値証人には、法を割らない素数を与えるS1を適用する。非1証人には共通の重み付き比較と二次指標専用の精密評価を使う。これらの証人は対象とする指標値が異なるため、別々の定理として扱う。

二次指標専用の解析結果は [Extensions.lean](../PseudoPrime/LLS/Extensions.lean) が公開する。具体的な前提、上界式、最小奇素数証人と有限最大値への接続、各式が最良となる区間は [PseudoSquare](PseudoSquare.md) を参照する。

### Miller–Rabinの素数底証人

Miller–Rabinでは、合格底を含む真部分群を構成し、S2から得られる部分群の像の外の素数を不合格底へ移す。小素因数を利用する場合の議論と有限区間の証明を組み合わせ、素数底証人の上界へ接続する。

具体的な前提と上界式、Miller–Rabin専用の解析による改良、各式が最良となる区間は [Miller–Rabinの素数判定同値と素数底証人上界](MillerRabinBoundGrh.md) を参照する。

## 利用例

```lean
import PseudoPrime.LLS

#check PseudoPrime.LLS.llsTheorem11S1Character_of_grh
#check PseudoPrime.LLS.llsTheorem11S1_of_grh
#check PseudoPrime.LLS.llsTheorem11S2_of_grh
#check PseudoPrime.LLS.exists_least_prime_outside_subgroup_of_grh
```

[構成全体へ](README.md)
