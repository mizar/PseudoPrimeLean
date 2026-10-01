# LLS — 一般指標・真部分群に対する明示的な素数上界

公開入口: [LLS.lean](../PseudoPrime/LLS.lean)。名前空間は `PseudoPrime.LLS`。

Lamzouri–Li–Soundararajan の Theorem 1.1 に対応する S1・S2 を扱う。 `Statement.lean` にある命題の定義と、GRH からそれを証明する定理を区別する。一般指標の解析評価・GRH による証明は LLS 本体にあり、Extensions を import しない。

## S1: 一般指標版と真部分群版

[Statement.lean](../PseudoPrime/LLS/Statement.lean) の定義に従い、

$$
A(q) = \max\Bigl(0, 2\ln(\ln\mathrel{} q) - \frac{8}{5} - \sum_{p \mid q}\frac{\ln\mathrel{} p}{p - 1}\Bigr),
$$

$$
B(q) = \max\Bigl(0, 2\ln(\ln\mathrel{} q) + 3 +
\frac{2\omega(q)(\ln(\ln\mathrel{} q))^2}{\ln\mathrel{} q} - 2A(q)\Bigr),\qquad
X_1(q) = (\ln\mathrel{} q + B(q))^2
$$

とする。素因数和は異なる素因数についての和。 $A(q)$ は `llsAuxiliaryTerm`、 $B(q)$ は `llsCorrectionTerm` に対応する。

GRH、 $q \ge 3000$ のもとで次が証明されている。

| 仕様 | 主張 | GRH からの定理 |
|---|---|---|
| `llsTheorem11S1Character` | 非自明な複素 Dirichlet 指標 $\chi$ に対し、素数 $p \nmid q$、 $\chi(p) \ne 1$、 $p \le X_1(q)$ が存在 | `llsTheorem11S1Character_of_grh` |
| `llsTheorem11S1` | 任意の真部分群 $H < (\mathbb{Z}/q\mathbb{Z})^\times$ に対し、法 $q$ を割らず、単元剰余が $H$ の外にあり、 $p \le X_1(q)$ を満たす素数 $p$ が存在 | `llsTheorem11S1_of_grh` |

一般指標版は二次性も、元の指標の原始性も要求しない。解析では原始指標へ移り、導手と法変更の補正を処理する。 `llsTheorem11S1_of_character` は、商群の非自明指標を引き戻して指標版から真部分群版を得る。同一結論の別名ではなく、対象と結論が異なる二つの仕様である。

`exists_least_prime_outside_subgroup_of_grh` はさらに最小素数を与える。最小性の比較対象は、上界内に限定せず `PrimeOutsideSubgroup q H` を満たすすべての素数である。これらの GRH 定理は [Theorem11S1GRH.lean](../PseudoPrime/LLS/Theorem11S1GRH.lean) にある。

## S2: 小さい素因数の排除と対数二乗上界

`llsTheorem11S2_of_grh` は [Theorem11S2.lean](../PseudoPrime/LLS/Theorem11S2.lean) にある。公開仕様 `llsTheorem11S2` は、 $q \ge 3000$ と

$$
\text{素数 }r < (\ln\mathrel{} q)^2\Longrightarrow r \nmid q
$$

を前提とし、真部分群 $H$ に対して、 $p \le (\ln\mathrel{} q)^2$ でその剰余が $H$ の像に入らない素数を与える。小素因数を除外する前提の不等号は狭義であり、証人の上界の不等号は広義である。結論には $p \nmid q$ が含まれず、等号端点の非単元も許すため、S1 の単元としての結論とは区別する。

証明途中の `exists_prime_not_one_le_log_sq` は、非自明指標の値が $1$ でない素数を与える。ここでは値 $0$ も許される。この中間定理自体には小素因数排除の前提がなく、公開 S2 はその結果を用いて元の仕様を満たす。

この S2 は [Miller–Rabin の素数判定同値と素数底証人上界](MillerRabinBoundGrh.md) にも使われる。合格底を含む真部分群を無条件に構成し、小素因数があればその底で不合格、なければ S2 で得た部分群の像の外の素数底で不合格とする。有限区間の証明と合わせることで、GRH の下ですべての奇合成数 $n > 1$ を対象とする $p \le (\ln\mathrel{} n)^2$ の上界が得られる。

## 証明を支える構成

| ファイル | 役割 |
|---|---|
| [Theorem11S1.lean](../PseudoPrime/LLS/Theorem11S1.lean) | S1 の半径・上下界 interface と、上下界の矛盾から結論を得る組立て |
| [Theorem11S1FullLevel.lean](../PseudoPrime/LLS/Theorem11S1FullLevel.lean) | 一般・二次両経路で使う零点質量 interface、法だけによる上界、数値比較 |
| [Theorem11S1Estimates.lean](../PseudoPrime/LLS/Theorem11S1Estimates.lean) | 一般指標の対数・逆数評価と導手補正から S1 の上界を供給 |
| [Theorem11S1Subgroup.lean](../PseudoPrime/LLS/Theorem11S1Subgroup.lean) | 商群指標の構成、真部分群版と最小素数版 |
| [Numerics.lean](../PseudoPrime/LLS/Numerics.lean) | S1 の実変数評価と厳密な上下界分離 |
| [RiemannLogResidueBound.lean](../PseudoPrime/LLS/RiemannLogResidueBound.lean)・[RiemannReciprocalResidueBound.lean](../PseudoPrime/LLS/RiemannReciprocalResidueBound.lean) | RH から Riemann 側の重み付き下界を供給 |
| [PrimitiveLogWeightedBounds.lean](../PseudoPrime/LLS/PrimitiveLogWeightedBounds.lean)・[PrimitiveReciprocalWeightedBounds.lean](../PseudoPrime/LLS/PrimitiveReciprocalWeightedBounds.lean) | 一般原始指標の GRH 上界 |
| [WeightedComparison.lean](../PseudoPrime/LLS/WeightedComparison.lean)・[WeightedComparisonGRH.lean](../PseudoPrime/LLS/WeightedComparisonGRH.lean) | 欠損・零点質量・誤差項を引数に持つ共通比較と GRH 構成 |
| [Theorem11S2SmallPrimeExclusion.lean](../PseudoPrime/LLS/Theorem11S2SmallPrimeExclusion.lean)・[Theorem11S2Numerics.lean](../PseudoPrime/LLS/Theorem11S2Numerics.lean) | cutoff 内自明性の移送と S2 の数値分離 |

## PseudoSquare への接続と Extensions

Jacobi 記号が $-1$ となる証人の上界は、一般 S1 を法 $4n$ の Jacobi 指標へ適用して得る。 $p \nmid 4n$ により値 $0$ を排除でき、指標値が $1$ と異なることから Jacobi 値が $-1$ と分かる。

Jacobi 記号が $1$ でない証人の上界は最終 S2 の直接適用ではなく、共通の重み付き比較を利用する。 [Extensions/QNeOneLogWeightedBounds.lean](../PseudoPrime/LLS/Extensions/QNeOneLogWeightedBounds.lean) にある、 $2$ での値が $0$・ $1$・ $-1$ となる三分岐と、偶指標の精密評価が使われる。二次指標専用の解析結果は [Extensions.lean](../PseudoPrime/LLS/Extensions.lean) が別に公開する。

## 利用例

```lean
import PseudoPrime.LLS

#check PseudoPrime.LLS.llsTheorem11S1Character_of_grh
#check PseudoPrime.LLS.llsTheorem11S1_of_grh
#check PseudoPrime.LLS.llsTheorem11S2_of_grh
#check PseudoPrime.LLS.exists_least_prime_outside_subgroup_of_grh
```

[構成全体へ](README.md)
