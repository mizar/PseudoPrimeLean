# Fibonacci最大添字の高速計算と互除法の燃料

ユークリッド互除法を有限の燃料で実行するとき、初期値そのものを燃料にすれば停止するが、大きな入力では過剰な上界になる。この文書ではFibonacci数から十分な燃料を計算し、その正当性と最悪例を説明する。

## 最大Fibonacci添字

Fibonacci数を $F_0=0,F_1=1,F_{k+2}=F_k+F_{k+1}$ とする。入力 $n$ 以下のFibonacci数の最大添字を

$$
G(n)=\max\lbrace k\in\mathbb{N}\mid F_k\le n\rbrace
$$

と定義する。mathlibの `Nat.greatestFib` に対応し、$F_{G(n)}\le n < F_{G(n)+1}$ を満たす。$F_1=F_2=1$ なので $G(1)=2$、$G(0)=0$ である。

高速実装 `greatestFibBinary` は状態 $(i,F_i,F_{i+1})$ を保持する。二つの有効な状態の添字を加えるには

$$
F_{i+j}=F_iF_{j+1}+(F_{i+1}-F_i)F_j,
$$

$$
F_{i+j+1}=F_{i+1}F_{j+1}+F_iF_j
$$

を使い、添字の倍加には

$$
F_{2i}=F_i(2F_{i+1}-F_i),\qquad
F_{2i+1}=F_i^2+F_{i+1}^2
$$

を使う。自然数の引き算を用いるが、$F_i\le F_{i+1}$ なので有効な状態では切り捨てによる誤差はない。

探索は添字1の状態から始める。現在の値が $n$ 以下なら状態を倍加して再帰し、戻ってきた状態に現在の添字を加えられるか調べる。和の値が $n$ 以下なら加えた状態を、超えるなら再帰結果を返す。現在の値が既に $n$ を超えている場合と燃料ゼロの場合は添字0の状態を返す。

燃料 $f$ と状態 $t$ に対して、$G(n) < t.i 2^f$ の前提があれば、結果 $u$ は有効で

$$
u.i\le G(n) < u.i+t.i
$$

を満たす。初期添字は1なので、この区間から $u.i=G(n)$ が従う。`greatestFibBinaryLoop_spec` が区間仕様、`greatestFibBinary_spec` がmathlibの定義との一致を保証する。

## 実数対数を使わない探索燃料

ここで $\log_2 m$ は自然数の二進対数、すなわち正の $m$ に対する $\lfloor\log_2 m\rfloor$ を表す。Fibonacciの漸化式と単調性から

$$
2^{r+1}\le F_{2r+3}
$$

となる。$r=\log_2(n+1)$ とすれば $n < 2^{r+1}$ なので

$$
G(n) < 2\log_2(n+1)+3
$$

を得る。したがって

$$
f(n)=\log_2\bigl(2\log_2(n+1)+3\bigr)+1
$$

は $G(n) < 2^{f(n)}$ を満たす十分な探索燃料である。これを `greatestFibBinaryFuel` として実装した。再帰の深さは $f(n)$ 以下であり、$n$ の値に対して $O(\log\log(n+1))$ で増える。ただし各更新で多倍長整数を乗算するため、この深さだけが実行時間を表すわけではない。実行時間の比較測定はまだ行っていない。

## 互除法の実行と停止回数

自然数の状態 $(c,m)$ を

$$
\mathrm{step}(c,m)=
\begin{cases}
(c,0)&m=0,\\
(m,c\bmod m)&m>0
\end{cases}
$$

で更新する。`run k c m` はこの更新を $k$ 回行う。第2成分が0になった後は状態を保持する。`stoppingTime c m` は第2成分が初めて0になる回数である。初期状態で $m=0$ なら停止回数も0になる。

各回の剰余は除数より小さいので、燃料 $m$ で必ず停止する。この粗い上界を使って最小停止回数の存在を保証してから、Fibonacciによる上界を証明する。

### 非停止のFibonacci下界

$k$ 回後も第2成分が非零なら

$$
F_{k+2}\le m
$$

が成り立つ。さらに $m < c$ なら $F_{k+3}\le c$ である。`fib_lower` はこの二つを同時に帰納法で証明する。

帰納段階では、次の状態 $(m,c\bmod m)$ に下界を適用する。$m\le c$ と $m>0$ なら、商が1以上なので

$$
m+(c\bmod m)\le c
$$

となる。次の状態の二つの下界を加え、Fibonacciの漸化式を使えば、元の第1成分の下界を得られる。

非停止の下界の対偶により、$m < F_{k+2}$ なら $k$ 回で停止する。この結論は初期状態の $c,m$ の大小を仮定しない。

### 高速に計算する十分な燃料

$$
B(m)=G(m)-1
$$

とする。自然数の差なので $B(0)=0$ である。$m>0$ では最大添字仕様から $m < F_{B(m)+2}$ となり、任意の $c$ に対して

$$
\mathrm{stoppingTime}(c,m)\le B(m)
\le 2\log_2(m+1)+1
$$

を得る。`stepBound` は高速実装の添字から $B(m)$ を計算し、`run_stops_stepBound` が実際の燃料付き実行の停止を保証する。実数対数、黄金比の数値近似、RHやGRHは使わない。

互除法の各更新は最大公約数を保存する。停止時は $\gcd(c',0)=c'$ なので、`gcdBounded` を停止状態の第1成分として定義すると、`gcdBounded_eq` によりすべての自然数入力で `Nat.gcd` と一致する。

### 上界を達成する最悪例

隣接Fibonacci値 $(c,m)=(F_{k+3},F_{k+2})$ から始めると、$k$ 回後の状態は $(2,1)$ となり、その次の1回で停止する。したがって

$$
\mathrm{stoppingTime}(F_{k+3},F_{k+2})
=B(F_{k+2})=k+1
$$

である。`stoppingTime_fib_pair` がこの等式を証明する。$B$ は第2成分だけから決める一様上界として、これらの入力で実際に達成される。

例えば $(233,144)=(F_{13},F_{12})$ の停止回数は11であり、計算燃料も $G(144)-1=12-1=11$ となる。粗い線形燃料144と比べて小さい。整数対数による上界は $2\log_2(145)+1=15$ である。

## Jacobi記号の燃料上界

Jacobi計算では、分子 $a$ の因子2を取り除いて奇数部分 $d$ を作り、相互法則による符号更新後に $(n,a)$ を $(d,n\bmod d)$ へ移す。因子2を除去するため、通常の互除法と状態が一回ずつ一致するとは限らない。

このため、任意の正の $d\le m$ を選んで $(c,m)$ から $(d,c\bmod d)$ へ移る遷移を定義した。`divisionNonstop k c m` は、この遷移を $k$ 回行ってなお第2成分が非零となる列が存在することを表す。0回の場合は $m\ne0$ である。

この一般化でも

$$
\mathrm{divisionNonstop}(k,c,m)\Longrightarrow F_{k+2}\le m
$$

が成り立つ。次の状態の第1成分 $d$ が元の $m$ 以下なので、通常の互除法の帰納証明を適用できる。`divisionNonstop_fib_lower` と `not_divisionNonstop_stepBound` により、除数を縮小しても $B(m)$ 回後まで非停止を続けることはできない。

### 2進付値による一括除去

`ReferenceArithmetic.jacobiNat` は、正の分子ごとに2因子を一括除去する。分子 $a > 0$ に対して

$$
s=\mathrm{padicValNat}(2,a),\qquad
d=\mathrm{divMaxPow}(a,2),\qquad
a=2^s d
$$

と置く。Leanの関数は `padicValNat 2 a` と `Nat.divMaxPow a 2` である。最大の2冪を取り除くため、$d$ は奇数となり、$0 < d \le a$ が成り立つ。1反復で因子2の符号を $s$ 回分まとめて反映し、相互法則の符号を掛けて、次の入力を $(n\bmod d,d)$ とする。

奇数の法 $n$ では、因子2の符号は $n\bmod8$ が3または5なら $-1$、それ以外なら1である。相互法則の符号は $d\bmod4=n\bmod4=3$ のときだけ $-1$ となる。両方を掛けた1反復の符号は `jacobiRoundSign` で定義した。`jacobiNat_eq` は、この一括除去版が `jacobiSym` と一致することを証明する。

### 燃料付き実行の停止と正当性

`jacobiNatBatchedFuel fuel a n` は、上の1反復ごとに燃料を1減らす。分子が0なら燃料を消費せず終了し、法が1なら `some 1`、それ以外なら `some 0` を返す。分子が非零で燃料が0なら `none` を返す。したがって、計算したJacobi値0と燃料枯渇を区別できる。

枯渇した実行は、同じ長さの `divisionNonstop fuel n a` を与える。各反復の除数に奇数部分 $d$ を選べば、$0 < d \le a$ と剰余更新が遷移の条件を満たす。この列をFibonacciの非停止下界へ接続することで、次を証明した。

$$
\mathrm{fuel}\ge B(a)
\quad\Longrightarrow\quad
\mathrm{jacobiNatBatchedFuel}(\mathrm{fuel},a,n)\ne\mathrm{none}
$$

この停止の主張には法の奇数性は要らない。奇数の法では、さらに返り値が `some (jacobiSym (a : ℤ) n)` となる。`jacobiNatBatchedFuel_eq` が十分な燃料での一致を、`jacobiNatBatchedFuel_sound` が任意の燃料で成功した結果の正しさを示す。整数対数だけで予算を決める場合は

$$
B(a)\le 2\lfloor\log_2(a+1)\rfloor+1
$$

を使える。`Nat.log2` は床を取った整数対数であり、実数対数を計算しない。`jacobiNatBatched` は高速に求めた $B(a)$ を自動で割り当てる入口である。

### 符号付き入力と法だけから決まる燃料

`jacobiSignedBatched` は負の分子の符号を反映し、絶対値に対する予算を使う。`jacobiNormalizedBatched` は整数の分子を先に法で正規化する。奇数の法に対して、どちらも元の整数のJacobi記号と一致する。

正規化した分子 $r$ は $0 \le r < n$ なので、$B$ の単調性から、すべての整数の分子に共通して

$$
B(r)\le B(n-1)\le 2\lfloor\log_2 n\rfloor+1
$$

を燃料にできる。`jacobiNormalizedBatchedFuel_eq` は $B(n-1)$ 以上の燃料での一致を、`jacobiNormalizedBatchedFuel_log2` は整数対数の予算での一致を証明する。法1も含み、正規化した分子0の終端で正しく1を返す。

この燃料は、一括除去と相互法則と剰余更新をまとめた反復の回数を数える。`padicValNat` や `Nat.divMaxPow` の内部処理、多倍長整数の除算や乗算の計算量は別に扱う。

### BPSWの実行経路への接続

`jacobiExecutable` は、奇数の法では正規化付きの一括除去を使う。その他の法では `jacobiSym` の既存の定義を使う。`jacobiExecutable_eq` により、すべての整数の分子と自然数の法で `jacobiSym` と一致する。

Wheel30のSelfridge走査では、候補の停止判定と、停止後のパラメータ・因子の分類にこの実行入口を使う。分類に必要な命題は従来の `jacobiSym D n = -1` のまま保持し、`jacobiEqDecidable` が実行結果からその証拠を返す。C++の等号除外に対応する比較用走査にも同じ入口を使う。通常版・強化版のWheel30 Bool、予算付きDecision、段階実行はこの走査を通る。

Selfridge走査の燃料は候補区間の整数の個数を数え、Jacobi内部の燃料は一括除去後の反復を数える。Jacobiの自動予算は十分性を証明済みなので、外側の走査の枯渇と混同しない。古典的な純粋 $-1$ 探索や一般のLucas検査のJacobi評価は今回の置換対象に含めていない。参考実装との回帰照合と性能測定は未実施である。

## 公開モジュール

| モジュール | 内容 |
|---|---|
| [Fibonacci/Greatest.lean](../PseudoPrime/NumberTheory/Fibonacci/Greatest.lean) | 隣接値の状態、二進探索、十分な探索燃料、最大添字との一致 |
| [Fibonacci/Euclid.lean](../PseudoPrime/NumberTheory/Fibonacci/Euclid.lean) | 最小停止回数、Fibonacci燃料、gcdの正当性、最悪例、除数縮小付き遷移 |
| [PrimeTest/JacobiFuel.lean](../PseudoPrime/PrimeTest/JacobiFuel.lean) | 2因子一括除去の燃料付きJacobi、枯渇の排除、自然数・整数入力の正当性 |

Fibonacciと互除法の名前空間は、それぞれ `PseudoPrime.NumberTheory.Fibonacci` と `PseudoPrime.NumberTheory.Euclid` である。Jacobiの実装と定理は `PseudoPrime.PrimeTest.ReferenceArithmetic` に置く。前者は `import PseudoPrime.NumberTheory`、後者は `import PseudoPrime.PrimeTest` で利用できる。`import PseudoPrime` は両方を公開する。
