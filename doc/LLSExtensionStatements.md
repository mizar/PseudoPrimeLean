# LLS拡張の命題と証明

[Extensions/PaperStatements.lean](../PseudoPrime/LLS/Extensions/PaperStatements.lean)に収録した拡張命題を解説する。補助定義は[PaperDefinitions.lean](../PseudoPrime/LLS/Extensions/PaperDefinitions.lean)、公開証明は[PaperProofs.lean](../PseudoPrime/LLS/Extensions/PaperProofs.lean)にある。名前空間は`PseudoPrime.LLS.Extensions`である。論文本体の命題については[LLS原文の命題と証明](LLSPaperStatements.md)を参照する。

各節では前提と主張を述べ、公開証明がある場合は証明の概要も記す。「公開証明はない」は、対応するPropの定義はあるが、PaperProofsにその証明がないことを表す。証明方針を記した場合も、Leanで証明済みであることを意味しない。

## 拡張命題と公開証明

| 用途 | Leanの命題 | 公開証明 |
|---|---|---|
| 補題2.5の一般L関数への拡張 | `lls_propL1_general` | `lls_propL1_general_proof` |
| 平滑化した対数微分公式 | `lls_propL2` | `lls_propL2_proof` |
| 零点質量の評価 | `lls_sumzeros` | `lls_sumzeros_proof` |
| L値と逆数の評価 | `lls_generalL` | なし |
| Q-ne-oneの値0の分岐 | `lls_qNeOne_zero_branch` | `lls_qNeOne_zero_branch_proof` |
| Q-ne-oneの値−1の分岐 | `lls_qNeOne_neg_one_branch` | `lls_qNeOne_neg_one_branch_proof` |
| Q-ne-oneの値1の分岐 | `lls_qNeOne_one_branch` | `lls_qNeOne_one_branch_proof` |

最後の3命題は、Extensionsから外部参照される既存の公開定理の前提と結論をPropとして表したものである。

## 一般L関数の前提と記法

`GeneralLFunction`は、次数 $d$、算術的導手 $q$、ガンマ因子のパラメータ $\kappa_j$、局所根 $\alpha_j(p)$、ディリクレ級数の係数 $\lambda_f(n)$、関数 $L(s,f)$、完備関数 $\xi(s,f)$ を持つ。完備関数は独立した解析接続のデータである。

`IsAdmissible`では $d \ge 1$、 $q \ge 1$、 $\lambda_f(1)=1$、 $\mathrm{Re} \kappa_j \ge 0$ を仮定する。また、各素数 $p$ について $\vert\alpha_j(p)\vert \le 1$ というRamanujan条件を課す。半平面 $\mathrm{Re} s > 1$ では、ディリクレ級数が収束して $L(s,f)$ に一致し、Euler積が収束して同じ値を取る。LeanではEuler因子の複素対数の総和可能性も条件に含める。

完備関数は、ガンマ因子に極のない半平面 $\mathrm{Re} s > 0$ で

$$
\xi(s,f)=q^{s/2}\pi^{-ds/2}
\prod_{j=1}^{d}\Gamma\left(\frac{s+\kappa_j}{2}\right)L(s,f)
$$

を満たす。左半平面を含めた値は整関数としての解析接続で与え、全域化されたガンマ関数の極での値からは定義しない。また、位数1以下の増大条件を満たすと仮定する。具体的には、任意の実数 $r > 1$ に対して $A > 0$ と $R \ge 0$ が存在し、 $\vert s\vert \ge R$ ならば

$$
\vert\xi(s,f)\vert \le \exp(A\vert s\vert^r)
$$

となる。さらに、 $\vert\epsilon\vert=1$ を満たす複素数 $\epsilon$ が存在し、関数等式

$$
\xi(s,f)=\epsilon\overline{\xi(1-\overline{s},f)}
$$

が成り立つ。種数1のHadamard展開に用いるため、位数1以下の増大条件を課している。

解析的導手は次の式で定義する。

$$
C(f)=\frac{q}{\pi^d}\prod_{j=1}^{d}
\left\vert\frac{1+\kappa_j}{2}\right\vert
$$

Iwaniec–Kowalskiの式(5.7)にある $q\prod_j(\vert s+\kappa_j\vert+3)$ とは定義が異なる。

`RiemannHypothesis`は、この関数の完備零点すべての実部が $1/2$ であるという仮定である。全ディリクレ指標に対するGRHを前提としているわけではない。以下、零点 $\rho$ の重複度を $m_f(\rho)$ とし、零点質量を

$$
M_f=\sum_{\xi(\rho,f)=0}\frac{m_f(\rho)}{\vert\rho\vert^2}
$$

と書く。Leanでは重複度を`analyticOrderNatAt`で与え、和を`tsum`で定義する。一般版の最初の3命題では、この和の総和可能性も結論に含める。

対数は自然対数、 $\Lambda$ はフォン・マンゴルト関数、 $\gamma$ はオイラー定数とする。素数冪の係数を

$$
a_f(p^k)=\sum_{j=1}^{d}\alpha_j(p)^k\quad(k \ge 1)
$$

とし、素数冪でない正整数では $a_f(n)=0$ とする。これはディリクレ級数の係数 $\lambda_f(n)$ とは別の係数である。有限和を

$$
\begin{aligned}
V_f(x)&=\sum_{1\le n\le x}\frac{a_f(n)\Lambda(n)}{n},\\
U_f(x)&=\sum_{1\le n\le x}\frac{a_f(n)\Lambda(n)}{n}
\left(1-\frac nx\right),\\
T_f(x)&=\sum_{1\le n\le x}\frac{a_f(n)\Lambda(n)}{n\log n}
\frac{\log(x/n)}{\log x},\\
W_f(x)&=\sum_{1\le n\le x}a_f(n)\Lambda(n)
\left(\frac{1}{n\log n}-\frac{1}{x\log x}\right)
\end{aligned}
$$

とする。順に`reciprocalSum`、`reciprocalWeightedSum`、`logValueSum`、`truncatedValueSum`に対応する。Leanでは1から $\lfloor x\rfloor$ までの有限和を取り、 $n=1$ の項は全域化された除算と $\Lambda(1)=0$ により0となる。

ガンマ因子と導手による端点の寄与を

$$
G_f=\frac12\log\frac{q}{\pi^d}
+\frac12\sum_{j=1}^{d}\mathrm{Re} \psi\left(\frac{1+\kappa_j}{2}\right),
\qquad \psi(z)=\frac{\Gamma'(z)}{\Gamma(z)}
$$

とする。 $G_f$ は`gammaLogDerivativeAtOne`である。

## ディリクレ指標への特殊化

`ofDirichletCharacter`は、法が非零の複素ディリクレ指標を次数1のデータとして表す。局所根と級数係数を指標値、L関数を指標のL関数とし、ガンマ移動量を偶奇に応じて0または1とする。原始非主指標については、以下のように解析的許容性を示す。

Mangoldt関数を掛けた係数が指標値を掛けたものに一致することを証明し、一般版の対数和・平滑化した逆数和・打切り和を原論文の指標和へ結び付けている。また、係数のノルム上界だけを仮定する一般有限和評価から、任意の指標と $x \ge 1$ について $\lVert T_\chi(x)\rVert \le T(x)$ を得る。原始性やGRHは不要である。

ガンマ端点は偶奇別にdigammaの特殊値を計算して、補題2.5の定数と一致することを証明している。完備関数の正規化因子は全平面で正則かつ非零なので、零点と解析的重複度を保つ。個々の原始非主指標のRHを一般版の`RiemannHypothesis`へ移す証明では、関数等式と右半平面の非消滅性によって完備零点の実部が正であることを先に示す。

零点の部分型上の質量は、整関数のdivisorと解析的重複度の対応を使って、指標の完備関数の全平面上の零点和に直す。対象の原始指標のRHから、臨界線上の零点ごとの恒等式をHadamardの総和公式へ適用し、関数等式と逆指標の定数の一致を使って $M_f=2\vert\mathrm{Re}B(\chi)\vert$ を得る。この同定には対象の指標のRHだけを使う。

原始非主指標の次数1データの解析的許容性は、右半平面での級数・Euler積・対数の収束、ガンマ積との一致、完備関数の全正則性、位数が高々1であること、ノルム1の根数を持つ関数等式から従う。成長条件は球上の評価と、任意の $r > 1$ に対する $\log t=o(t^{r-1})$ を使って示す。この段階ではRHを使わない。一般公式の次数1の誤差上界は補題2.5と一致する。

## 補題2.5の一般化 `lls_propL1_general`

前提は、 $f$ が`IsAdmissible`を満たし、その関数について`RiemannHypothesis`が成り立つことである。

主張は、零点質量の和が総和可能で、すべての $x \ge 2$ について実数 $\theta_1,\theta_2$ が存在し、 $\vert\theta_1\vert \le 1$、 $\vert\theta_2\vert \le 1$ と

$$
\log\vert L(1,f)\vert
=\mathrm{Re} T_f(x)+\frac{G_f}{\log x}
-\left(\frac{1}{2\log x}
+\frac{\theta_1}{\sqrt{x}(\log x)^2}\right)M_f
+\frac{2d\theta_2}{x(\log x)^2}
$$

が成り立つことである。二つの係数は独立に選ぶ。最後の項の絶対値は $2d/(x(\log x)^2)$ 以下であり、導手やガンマ移動量に依存しない。

公開証明は`lls_propL1_general_proof`である。実数 $\sigma > 1$ で移動した対数Perron積分を評価し、 $\sigma$ について積分する。完備関数の端点の対数微分から $G_f$ と零点質量の寄与を取り出す。個別RHから $\vert\sigma-\rho\vert \ge \vert\rho\vert$ が従い、零点項を $M_f/(\sqrt{x}(\log x)^2)$ 以下に抑える。ガンマ項では $\mathrm{Re}\kappa_j \ge 0$ を使い、残差を

$$
\frac{d}{x(\log x)^2}\sum_{n=0}^{\infty}\frac{1}{(n+1)^2}
<\frac{2d}{x(\log x)^2}
$$

で抑える。

まず、係数列に対するMellin反転と級数・縦積分の交換により、算術有限和を対数微分の縦積分に直す。移動量について積分すると重み $1/(n\log n)$ が現れ、補題2.5の有限対数和が得られる。

移動した核の原点での留数は $-(L\prime/L)\prime(\sigma)-(L\prime/L)(\sigma)\log x$、零点での留数は $-m_\rho x^{\rho-\sigma}/(\rho-\sigma)^2$ である。個別RHと零点質量の収束から、移動した零点和の収束と移動量方向の可積分性を示し、和と積分を交換する。対数で割った積分のノルムは $M_f/(\sqrt{x}(\log x)^2)$ 以下であり、その実部を絶対値1以下の係数 $\theta_1$ で表す。

零点質量の総和可能性は、位数が高々1という増大条件から大域的な指数上界を作り、Jensen公式による零点数の評価を二進環ごとに足し合わせて示す。中心化したHadamard展開と関数等式から $\mathrm{Re}(\xi\prime/\xi)(1)=M_f/2$ を得る。さらに完備因子の対数微分を差し引くと、 $\mathrm{Re}(L\prime/L)(1)=M_f/2-G_f$ となる。

許容条件と個別RHから、実数半直線上でのL関数の解析性・非消滅性を得る。対数重み付きのDirichlet級数を使って、対数微分とその微分の指数減衰を示す。この減衰から無限遠での消失と可積分性が従い、原点留数を積分するための端点条件がそろう。

ガンマ項は、各シフトの実部が非負であることを使って、移動留数のノルムを $x^{-\sigma}/(m+1)^2$ で抑える。逆二乗級数の総和が2以下なので、級数は絶対収束し、移動量について積分した後も和と積分を交換できる。対数で割った積分のノルムは $2d/(x(\log x)^2)$ 以下となり、その実部を絶対値1以下の係数 $\theta_2$ で表す。

算術有限和を原点・完備零点・ガンマ極の寄与に分解するには、Euler対数級数を微分し、素数冪で再索引付けして対数微分の縦積分を得る。完備関数には中心化Hadamard展開を、ガンマ因子にはdigammaの逆数差級数を使う。零点の重複度を逆数の冪で重み付けした和は、指数が1より大きければ収束する。指数3/2の評価から縦積分の共通の可積分上界を作り、零点和・ガンマ和と積分を交換する。中心化した逆数差の積分と微分を計算することで、各項を留数の形へ直す。

得られた移動公式を実数半直線上で積分し、原点項を端点のL値と対数微分で表す。端点の等式と零点・ガンマ項の上界を代入すると、一般化した補題2.5の結論を得る。積分交換と留数の評価も解析的許容条件と個別RHから導いている。

原始非主指標への特殊化では、自明零点の重複度が1であることから、その留数をガンマ級数の項へ同定する。偶指標の零点0も、移動後は原点以外の留数として含める。偶奇それぞれの級数の積分評価にはRHを使わず、次数1のガンマ誤差の実部を $2\theta_2/(x(\log x)^2)$ と表す。

### 補題2.5への特殊化

原点項の積分は、L関数が1へ収束し、対数微分が0へ収束することと、対数微分およびその微分の可積分性を使って、 $\log\vert L(1)\vert+\mathrm{Re}(L\prime/L)(1)/\log x$ と表す。一般データでは許容条件と個別RHからこれらを示せるので、端点公式のために前提を加える必要はない。

法 $q \ge 3$ の原始指標 $\chi$ に対して、`ofDirichletCharacter`のデータを使う。次数は1、ガンマ移動量は偶指標で0、奇指標で1である。完備関数にはmathlibの解析接続を用い、導手の因子 $q^{s/2}$ と、奇指標の場合の正規化因子 $\sqrt{\pi}$ を掛ける。この零点と重複度は指標の完備L関数のものと一致する。

一般式に、有限和の一致、 $M_f=2\vert\mathrm{Re}B(\chi)\vert$、偶奇別の $G_f$ の値を代入すると、`lls_lemma25`の主張になる。二つの有界係数と最後の項 $2\theta_2/(x(\log x)^2)$ も一致する。

次数1データの解析的許容性、個別RHの移送、零点質量の同定、有限和とガンマ端点の一致を使って、証明済みの一般公式を特殊化する。これにより原論文の補題2.5が従い、公開証明`lls_lemma25_proof`を得る。

零点誤差については、原始非主指標の個別RHから次数1データの零点質量の収束を示し、一般の零点積分評価を適用する。その実部は $2\theta_1\vert\mathrm{Re}B(\chi)\vert/(\sqrt{x}(\log x)^2)$ と表され、係数は $\vert\theta_1\vert \le 1$ を満たす。

### 導手に応じた打切り点

次数 $d$ を固定し、 $C(f)\to\infty$ とすると、`lls_generalL`で使う $x=(\log C(f))^2/(4d^2)$ は最終的に2以上となる。一般式はすべての $x \ge 2$ に適用できるため、関数ごとの評価開始点を選ぶ必要がない。この点で最後の誤差上界は

$$
\frac{8d^3}{(\log C(f))^2
\left(\log\left((\log C(f))^2/(4d^2)\right)\right)^2}
$$

となり、固定次数の関数族について一様に0へ近づく。`lls_generalL`全体の証明には、他の二つの明示公式の誤差の一様性と、最終的な誤差尺度の次数1の場合の整理も必要となる。

## 平滑化した対数微分公式 `lls_propL2`

前提は`IsAdmissible`と、その関数の`RiemannHypothesis`である。

主張は、零点質量の和が総和可能で、実数値関数 $\theta(x)$ と $r(x)$ が存在し、すべての $x \ge 2$ について $\vert\theta(x)\vert \le 1$ と

$$
-\mathrm{Re}\frac{L'}{L}(1,f)
=\mathrm{Re} U_f(x)
+\left(\frac{\theta(x)}{\sqrt{x}}-\frac{1}{2x}\right)M_f+r(x)
$$

が成り立つことである。固定した $f$ について、 $x\to\infty$ のとき

$$
r(x)=O\left(\frac{\log C(f)+d\log x}{x}\right)
$$

を要求する。 $\theta$ と $r$ はこの命題の結論として選ぶ関数であり、追加の前提ではない。

証明ではHadamard展開を中心化し、零点ごとの逆数重みのMellin積分を計算する。重複度を含む零点質量の総和可能性により、積分と零点和を交換できる。個別RHから零点項のノルムは $M_f/\sqrt{x}$ 以下となり、端点の対数微分と組み合わせて積分の実部を

$$
-\frac{M_f}{2}
+\left(\frac{\eta(x)}{\sqrt{x}}-\frac{1}{2x}\right)M_f,
\qquad \vert\eta(x)\vert \le 1
$$

と表せる。普通L関数側では、Mangoldt係数級数の逆数Mellin反転から有限和 $U_f(x)$ を得る。ガンマ因子側では各極の留数を計算し、ガンマ移動量が0で平滑化核の極と重なる場合の寄与を $-\log x/x$ と評価する。

ガンマ留数の和を $T_f(x)$ とすると、剰余は

$$
r_f(x)=\frac{G_f+M_f}{x}+\mathrm{Re} T_f(x)
$$

と書ける。留数の係数は総和可能であり、固定した $f$ に対して $\vert T_f(x)\vert\le B_f(\log x+1)/x$ となる定数 $B_f$ を取れる。次数が正なので、この上界から要求されるBig-O評価を得る。普通L関数の端点公式を使い、 $\theta(x)=-\eta(x)$ と選ぶことで命題全体が従う。

この証明のBig-O定数と閾値は、固定した $f$ に依存してよい。`lls_generalL`に必要な、固定次数の関数族に共通する定数と閾値は別に評価する必要がある。

ガンマ留数和については、移動量に依存しない定数 $B$ による

$$
\vert T_f(x)\vert\le d\frac{\log x+B}{x}
$$

も証明済みである。最初の極では $\vert x^{-\kappa}-1\vert\le\log x\vert\kappa\vert$ を用い、分母の移動量と打ち消す。移動量0では重なる極の公式を使う。残りの極には共通の逆二乗級数の上界があり、全ガンマ因子を足すと上記の一様評価が得られる。ガンマ端点と零点質量を導手と次数で抑える評価も証明済みであり、零点質量の剰余評価へ接続している。

## 零点質量の評価 `lls_sumzeros`

前提は`IsAdmissible`と、その関数の`RiemannHypothesis`である。

主張は、零点質量の和が総和可能で、実数値関数 $r(x)$ が存在し、すべての $x \ge 2$ について

$$
M_f=\log C(f)-2\mathrm{Re} V_f(x)+r(x)
$$

が成り立つことである。固定した $f$ について、 $x\to\infty$ のとき

$$
r(x)=O\left(d+\frac{\log C(f)}{\sqrt{x}}\right)
$$

を要求する。

証明では、完備関数とガンマ因子の逆数Mellin公式から、固定した $f$ に対して $U_f(x)$ が有界であることを示す。また、二つの算術和の差は

$$
V_f(x)-U_f(x)=\frac1x\sum_{n\le x}a_f(n)\Lambda(n)
$$

となる。Ramanujan条件による $\vert a_f(n)\vert\le d$ とChebyshev関数の上界を用いると、この差も有界であり、 $V_f(x)$ の有界性が従う。

そこで $r(x)=M_f-\log C(f)+2\mathrm{Re} V_f(x)$ と選ぶ。この関数は有界で、Big-Oの尺度 $d+\log C(f)/\sqrt{x}$ は正の次数 $d$ に収束するため、要求される評価を満たす。

関数族に一様な評価も証明している。実部が1/2以上の複素引数について、水平な単位区間での対数の差と逆数との差を逆二乗で抑える。その有限和を望遠和に直し、Euler級数と調和数の極限を用いると、digamma実部とノルムの対数との差には普遍定数 $A$ による上界が得られる。各ガンマ因子に適用すると、 $\vert2G_f-\log C(f)\vert\le dA$ となる。

切断点を16に固定して算術有限和を次数で抑え、剰余の上界に現れる零点質量を左辺へ移す。普遍定数 $K$ による

$$
M_f\le\frac{17}{7}\vert\log C(f)\vert+dK
$$

が従い、固定次数の関数族では $M_f=O(\log C(f))$ となる。この上界を剰余へ代入すると、普遍定数 $D$ を用いて、すべての $x > 1$ について

$$
\vert r(x)\vert\le dD+\frac{58}{7}\frac{\vert\log C(f)\vert}{\sqrt{x}}
$$

を得る。定数は個々の関数やガンマ移動量に依存しない。

## L値と逆数の評価 `lls_generalL`

前提は固定した正の次数 $d$ である。その次数の`IsAdmissible`と`RiemannHypothesis`を満たす関数全体を対象とし、解析的導手 $C(f)$ を無限大へ近づける。以下、 $\ell_f=\log\log C(f)$ と書く。

主張は、この関数族上に2つの実数値誤差関数 $e_+(f)$、 $e_-(f)$ が存在し、十分大きな導手について一様に

$$
\vert L(1,f)\vert\le (2e^\gamma)^d
\left(\ell_f^d-
\left(d\log d+d\left(\log2-\frac12\right)+e_+(f)\right)\ell_f^{d-1}\right)
$$

と

$$
\frac{1}{\vert L(1,f)\vert}\le
\left(\frac{12e^\gamma}{\pi^2}\right)^d
\left(\ell_f^d-
\left(d\log d+d\left(\log2-\frac12\right)+e_-(f)\right)\ell_f^{d-1}\right)
$$

が成り立つことである。2つの誤差は独立に選び、それぞれ

$$
e_\pm(f)=o(1),\qquad
e_\pm(f)=O\left(\frac{d^2(\log d)^2}{\log\log C(f)}\right)
\quad(C(f)\to\infty)
$$

を満たす。Leanでは`FixedDegreeFamily d`と`conductorFilter d`を用いる。次数を固定した関数族全体に共通の導手の閾値を要求する。この閾値は個々の関数には依存しない。

公開証明はない。対数公式と平滑化した逆数公式を組み合わせ、切断和を主項とするL値の対数の公式を証明している。零点質量を対数導手へ置き換えた際の誤差は、次数・導手・切断点と実数のMangoldt和で抑えている。切断和の重みの非負性とRamanujan条件による係数評価から、L値とその逆数に共通する指数型の上界も得られる。

下界側では、素数ごとの有限素数冪和を複素多項式とみなし、単位円周上の比較を最大値原理によって閉単位円板へ延長している。これをRamanujan条件を満たす各局所根に適用し、根と素数について足すと、切断和の実部は次数倍の交代素数冪和以上となる。この比較を切断公式に代入し、逆数L値の指数型上界まで接続している。

交代素数冪和の偶数指数を平方指数へ直すと、平方補正は $\log(\pi^2/6)$ から切断誤差を引いた形になる。その誤差を $3/(2\sqrt{x})$ で抑え、逆数L値の上界に $(6/\pi^2)^d$ の係数を取り出している。

切断Mangoldt和は、対数重みのMangoldt和から $\psi(x)/(x\log x)$ を引いたものである。それぞれの誤差が $a$、 $b$ 以下なら、主項 $\log\log x+\gamma-1/\log x$ からの誤差は $a+b/(x\log x)$ 以下となる。この評価をL値と逆数の両方の上界へ接続している。

切断点 $x=(\log C(f))^2/(4d^2)$ について、平方根は $\log C(f)/(2d)$、対数は $2(\log\log C(f)-\log(2d))$ である。固定次数の関数族では、この切断点は一様に100以上となり、無限大へ向かう。上記のL値と逆数の上界を関数族全体へ適用し、先頭の導手項を $2d/\log x$ に直している。平方補正の誤差 $3/(2\sqrt{x})$ がこの関数族上で0へ収束することも証明している。

逆数Mangoldt和を $\log x(1+\log x)$ で抑えると、その和を $\sqrt{x}\log x$ で割った量は0へ収束する。導手切断点で切断誤差全体を逆数・平方根・対数の各尺度に分解し、固定次数の関数族上で一様に0へ収束することを証明している。先頭の導手項と平方補正も含め、十分大きな導手では指数内の誤差を任意の正数以下に抑えられる。上下両側に共通する算術主項と、逆数側の係数 $(6/\pi^2)^d$ を保った評価まで得られる。

切断誤差に $(\log x)^2$ を掛けた量は、固定次数の関数族上で $34d/7$ へ収束する。平方補正の損失を加えても同じ極限となるため、十分大きな導手では共通の誤差を $(34d/7+1)/(\log x)^2$ 以下に抑えられる。これにより、先頭導手項 $2d/\log x$ を残した二次精度の評価を得ている。

対数重みMangoldt和の誤差が $A/(\log x)^2$ 以下、 $\psi(x)$ の誤差が $Bx/(\log x)^2$ 以下となる定量評価を入力すると、上下両側の指数を

$$
d\left(\log\log x+\gamma+\frac{1}{\log x}\right)
+\frac{d(A+B)+34d/7+1}{(\log x)^2}
$$

で抑えられる。これは素数和の定量評価を前提とする補助定理である。

この指数型評価を最終の多項式型評価へ直す部分も証明している。 $t=\log\log C(f)$、 $a=\log(2d)$ と置き、指数化した上界から先頭因子を除いた関数を $F(1/t)$ とする。 $F(0)=1$、 $F'(0)=d(1/2-a)$ を求めると、

$$
t^dF(1/t)=t^d-\left(d\log d+d(\log2-1/2)+e(t)\right)t^{d-1}
$$

となる。ここで $e(t)=t(1-F(1/t))-d(a-1/2)$ である。 $F$ の解析性から二次剰余を評価し、 $e(t)\to0$ と $e(t)=O(1/t)$ を証明している。素数和の定量評価を入力すれば、この恒等式によって主張と同じ先頭因子・一次係数を持つL値と逆数の評価が得られる。次数2以上では $d^2(\log d)^2\ne0$ なので、固定次数の関数族上で要求されるBig-O尺度も満たす。

二つの算術評価は明示的な仮定として残る。これらを入力すると、固定次数での補正のlittle-o評価と逆対数のBig-O評価を適用できる。公開命題が次数1に要求する誤差なしの評価は別途必要である。

次数1では $d^2(\log d)^2=0$ となるため、このBig-O条件は誤差が十分大きな導手で恒等的に0となることを要求する。単に誤差が0へ収束するだけでは、この条件を満たさない。

二次精度の素数和評価を仮定すれば、公開命題は次数1の厳密な上下界と同値になる。十分性では、次数1の二つの誤差を零とし、次数2以上には指数型評価から得た一次補正を使う。必要性では、次数1でBig-O尺度が零になるため二つの誤差が最終的に零になると示し、公開命題の不等式へ代入する。素数和の二つの定量評価と、次数1の誤差項のない上下界が未証明の入力として残る。

## Q-ne-oneの3分岐に共通する前提

法 $q \ne 0$ の非主複素ディリクレ指標 $\chi$ を取り、その導手 $c=\mathrm{cond}(\chi)$ も0でないとする。原始指標`χ.primitiveCharacter`を $\chi_*$ と書く。 $\chi_*$ は偶指標で、全ディリクレ指標に対するGRHを仮定する。ここでは二次指標であることは前提に含まれない。

実数 $y \ge 12$ を取り、

$$
1\le k\le\left\lfloor\frac{\log(y^2)}{\log2}\right\rfloor,
\qquad 0 < p\le\left\lfloor(y^2)^{1/k}\right\rfloor
$$

を満たすすべての奇素数 $p$ について $\chi_*(p)=1$ と仮定する。Leanの前提はこの $k,p$ の範囲を明示している。

さらに、`LLSRiemannWeightedLowerBound`と`LLSRiemannReciprocalLowerBound`を前提に置く。指標因子のない和を

$$
S_\zeta(x)=\sum_{1\le n\le x}\Lambda(n)\log(x/n),\qquad
U_\zeta(x)=\sum_{1\le n\le x}\frac{\Lambda(n)}{n}\left(1-\frac nx\right)
$$

とすると、前者はすべての $x > 1$ について

$$
x-\log(2\pi)\log x-1-2b_\zeta(\sqrt{x}+1)\le S_\zeta(x)
$$

を、後者はすべての $x \ge 2$ について

$$
\log x-\frac85\le U_\zeta(x)
$$

を主張する。 $b_\zeta$ は`RiemannXi.riemannZeroMass`であり、[本体の解説の記法](LLSPaperStatements.md#記法)と同じ定数である。公開定理の型では、これらの下界はGRHと別々の引数として渡す。

## 値0の分岐 `lls_qNeOne_zero_branch`

前提は上の共通条件に加え、 $\chi_*(2)=0$ と

$$
\log c\le y+\log4
$$

である。主張は、これらの前提が同時には成り立たないことであり、Leanでの結論は`False`である。

公開証明は`lls_qNeOne_zero_branch_proof`にある。まず、値0の分岐に対応する重み付き和の上下界を導く。次に、 $y \ge 12$ では共通の上界が下界を下回る数値評価を適用し、矛盾を得る。

## 値−1の分岐 `lls_qNeOne_neg_one_branch`

前提は共通条件に加え、 $\chi_*(2)=-1$ と

$$
\log c\le y
$$

である。主張は、これらの前提から`False`が従うことである。

公開証明は`lls_qNeOne_neg_one_branch_proof`にある。2の冪の寄与を補正した重み付き和について共通の上下界を導き、 $y \ge 12$ での数値的な隔たりから矛盾を得る。

## 値1の分岐 `lls_qNeOne_one_branch`

前提は共通条件に加え、 $\chi_*(2)=1$ と

$$
\log c\le y
$$

である。主張は、これらの前提から`False`が従うことである。

公開証明は`lls_qNeOne_one_branch_proof`にある。重み付き和の実部について共通の上下界を導き、 $y \ge 12$ で上界が下界を下回ることから矛盾を得る。
