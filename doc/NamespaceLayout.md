# 名前空間とソース配置

Leanソースの基底名前空間は `PseudoPrime/` を含む親ディレクトリのパスに対応させる。例えば、 `PseudoPrime/Analysis/` の宣言は `PseudoPrime.Analysis` に、 `PseudoPrime/PrimeTestBounds/MillerRabin/` の宣言は `PseudoPrime.PrimeTestBounds.MillerRabin` に配置する。型固有の下位名前空間は、その型を扱うファイル内で使える。

異なる分野の宣言を一つのファイルに混在させない。解析の補助定理とMiller–Rabinへの適用定理が同居する場合は、docstringと証明を含む宣言を分割し、それぞれの名前空間に対応するディレクトリへ移す。配置のみを変更する場合は完全修飾名を保持し、利用側のimportで依存関係を接続する。所属する名前空間も変更する場合は、後述の分離方針に従う。旧import経路を維持するファイルには、転送用の `public import` を置く。

## 一般的な定義・補題の分離

LLSに依存しない一般的な定義・補題は、共通の定義や広い用途を持つものから優先して `PseudoPrime.LLS` から分離し、内容に応じて `PseudoPrime.Analysis`、 `PseudoPrime.NumberTheory`、 `PseudoPrime.AnalyticNumberTheory` などへ配置する。この方針はLLSに限らない。特定の名前空間に固有の概念を必要としないことに加え、実際の共有可能性や分離の必要性も確認して配置を決める。

配置はimportの依存関係だけで判断しない。各宣言の引数、暗黙の引数、型クラス、前提、結論、返り値の型を読み、その名前空間に固有の定義や仮定が必要かを確かめる。 `def` の定義本体や、型の別名・補助定義の展開先も確認する。LLSのファイルからしか使われていないことや、LLSの定理を証明で使っていることだけでは、LLS固有とは判断しない。

各宣言について、前提と主張が数学的に何に依存するかを確認する。前提に現れる対象・条件と、主張に現れる対象・性質が、どの分野の定義や仮定を必要とするかを、補助定義の展開先までたどる。前提・主張の依存と、証明で使う補題への依存を区別し、その宣言が一般の解析・算術だけで述べられるのか、LLSなどの適用先に固有の概念を必要とするのかを確かめて配置を決める。

実数や算術量だけで記述できることは、汎用性の十分条件ではない。核・尺度・係数・誤差予算・開始条件が、どのパラメータの選択に基づくかも確認する。LLSで選んだ核や尺度、定数に特化した評価・数値認証・比較条件は、一般の解析や算術の式だけで書ける場合もLLS側に置く。一部の係数が引数に残っていても、他の尺度や定数がLLSの選択に固定されていれば、それだけで汎用評価とは判断しない。

一般化できることと、共通APIとして切り出す必要性を区別する。仮定する条件の制約や、不等式評価などの用途によって、使える状況・使われ方が限定される宣言ほど、一般化・分離の必要性は低いと判断する。特に、特定の条件の組合せで特定の上界・下界を得る不等式評価は、引数を増やして一般形にできるだけでは共通APIへ切り出す理由にならない。一般的な定義や広く使える基本的な恒等式を優先し、限定的な評価は共通化する必要が確認できた場合に切り出す。仮定や不等式の有無だけで一律に分類せず、実際の適用範囲と再利用の必要性を確認する。

一般の尺度・係数を引数とし、適用先の選択から独立して成り立つ共通評価と、具体的なパラメータを選んだ後の評価を区別する。前者は共通化の必要性を確認して内容に応じた一般の分野へ置き、後者は適用側へ残す。例えば、LLSの尺度 $T = \log q - \log\log q$ と所定の誤差係数を組み合わせた評価はLLS側に置く。引数にパラメータがあることだけで特殊な評価と判断したり、固定した数値を含むことだけで適用先固有と判断したりせず、前提・主張に現れる選択と適用先の関係を確認する。

定義された数学的対象の係数総和などの基本的な恒等式は、その対象を所有する名前空間に置く。固定値が応用で使われるという理由だけで、その恒等式を応用側へ移さない。数値が対象の定義から決まる恒等式と、開始点や許容誤差を選ぶ評価を区別する。

例えば、広く共有できる有限群・指標・積分に関する主張は、LLSへの用途があっても一般の分野へ置く。一方、LLS固有の証人や評価条件を前提とする適用定理はLLS側へ残す。一般的な主張の証明がLLS固有の補題に依存している場合は、必要な補題も分離するか、一般的な証明へ組み替える。移動先からLLSをimportして済ませてはならない。

分離時はdocstring・定義本体・証明を一体で移し、名前空間と配置先を対応させ、参照名とimportを更新する。一般の名前空間へ所属を変更する場合は完全修飾名も変更する。既存APIとの互換性が必要な場合は、旧名前空間側に互換用の宣言を置き、新しい一般の宣言を参照させる。

配置変更は、逆依存を生まない依存先から着手する。変更前に前提・主張・定義本体・証明の依存関係を確認し、移動先が必要とする共通の定義・一般補題を先に分離して検証する。移動先が適用側を参照せずに成立することを確認してから、依存する宣言と利用側を順に変更する。対象の依存経路に既存の逆依存がある場合も、先にその依存を解消する。後で修正することを前提に、一般側から適用側へのimportを残したり追加したりしない。

新規に逆依存を生む変更は禁止する。変更前後の直接・間接の依存経路を比較し、一般側から専用の適用側へ戻る新しい依存が生じていないことを確認する。importの経路だけでなく、宣言・定義本体・証明の参照も対象とする。変更後に新規の逆依存が判明した場合は、当該変更をロールバックする。ビルドの成功やimport件数の減少を理由に例外扱いしない。

逆依存を全て解消した段階で、汎用補題の一般名前空間への移設は一旦凍結する。以後は新規証明を優先し、移設の再開は明示の指示を受けてから行う。凍結までの配置作業も、逆依存の解消と、それに不可欠な依存先・利用側の修正に絞る。

2026年10月31日の配置適用で、一般3領域からLLS・PrimeTestBounds・PseudoSquareへの直接・間接importと、一般側ソースの専用領域への修飾付き参照が0件となったため、この凍結を有効にした。これはソースの依存検査による判断であり、変更後の全体CLIビルドの受入とは区別する。残る計画済みの専用評価の配置と必須のimport修正は、新規逆依存を生まない単位で検証する。

凍結の記録と検査は、作業用レポジトリの `PseudoPrimeWork/20261031_refactor/migration_policy.py` で管理する。再開の明示指示がない限り、一般名前空間へ所有者を変更する配置案は適用しない。同じ名前空間を保つファイル分割や、専用評価を専用領域へ戻す処理と区別する。

全体ビルドは移設中も移設終了後も、関連する変更の統合確認など、必要なタイミングで行う。移設では先に依存範囲と変更案の逆依存を確認し、関連する移設・利用側の接続・対象検証と修正をまとめてから全体ビルドへ進む。移設1件ごとに全体ビルドへ頼る手順を避け、変更範囲・依存関係・検証結果に応じて実行時点を判断する。

必要な依存を外せず逆依存が残る場合は、依存する宣言の配置が適切でないと判断し、配置を見直す。前提・主張に適用先固有の概念が必要なら適用側へ配置し、一般部分と適用部分が混在しているなら宣言を分割する。配置先を先に固定して逆依存を例外扱いせず、前提・主張と証明の依存に合う配置へ改める。

例えば、部分群への剰余の所属、部分群外の適格素数、剰余類内の素数集合は、
群・指標・自然数だけで定義でき、LLSで選んだ核や尺度を必要としない。
これらは `NumberTheory/ResidueSubgroup.lean` に置き、算術的な直交性や素数冪の補題と
ともに共有する。一方、LLSの番号付き定理に固有の係数や補正項は
`LLS/PaperDefinitions.lean` に残す。

MR包絡線で選んだ開始点・局所予算・誤差係数を条件に含む
`TriangularProfile` と具体的な認証値は、
`PrimeTestBounds/MillerRabin/TriangularProfiles.lean` と
`TriangularTunedProfiles.lean` に置く。係数や開始点をフィールドに持っていても、
条件が特定の包絡線の選択に固定されていれば、一般の解析APIとは判断しない。

`GaussianRelativeProfiles.lean` と、その固定尺度を扱う
`GaussianNextTripleNumerics.lean`、 `GaussianRelativeHighNumerics.lean` もMR側に置く。
これらは選択した係数・開始条件とLLSの具体的な誤差評価を組み合わせるため、
実数の不等式として書けることだけでは一般解析側へ配置する理由にならない。

固定した床値・残差・prefix予算を持つ `GaussianLowProfile` と
`GaussianTunedProfile` もMR側に置く。その候補間の順序や切替点を扱う
`GaussianLowSwitches.lean`、 `GaussianTunedOrder.lean`、
`GaussianTunedSwitches.lean` は、型と一緒に依存範囲を確認して移す。
比較の引数が実数でも、固定した候補群を選ぶための評価は適用側の内容として扱う。

一方、`Analysis/GaussianBudgetRoots.lean` の二次根・方程式・単調性は、
任意の実係数に対する共通APIとして複数の候補群で使う。
固定MR係数やLLSの誤差評価を必要としないため、Mathlibだけに依存させる。
具体的な係数を代入する利用側は、その係数や評価の依存を明示する。

固定MR係数を用いるGaussianの根・床値・残差・候補選択もMR側に置く。
係数を残した補助評価でも、LLSの特定の比較式を整理する用途に限られる
`LLS/GaussianRelativeFour.lean` のような宣言はLLS側に残す。
これらを共通の二次根APIと同じファイルや依存層にまとめない。

MR用に係数を固定した近似式の比較は
`PrimeTestBounds/MillerRabin/AffineLogarithmicFitBounds.lean` に置く。
任意係数の近似根や継続条件は `Analysis/AffineLogarithmicTailBounds.lean` に残し、
固定した近似式を実際のMR証人へ移す定理と区別する。

## 名前空間の依存図

図は配置方針に沿う向きのimportを表示し、図に表示しない依存も下表に列挙する。名前空間単位の集計であり、ファイル単位の循環検査や、各宣言の前提・主張・証明の意味上の監査を代替しない。図と表の両方を確認し、一般側から適用側へ戻る依存は、宣言の配置と数学的な依存に照らして個別に見直す。

<!-- namespace-dependencies:start -->
対象はチェックアウト内のLeanソース 2800 ファイル。隠しディレクトリ・ `archive` ・シンボリックリンク以下は走査しない。未追跡ファイルも含む。Mathlibなどの外部依存と同一グループ内の辺は図から除く。

```mermaid
flowchart TD
    N0["PseudoPrime (1)"]
    N1["Analysis (416)"]
    N2["AnalyticNumberTheory (562)"]
    N3["Combinatorics (2)"]
    N4["Data (1)"]
    N5["LLS (960)"]
    N6["NumberTheory (250)"]
    N7["PrimeTest (162)"]
    N8["PrimeTestBounds (283)"]
    N9["PseudoSquare (143)"]
    N10["Tests (16)"]
    N11["Tools (4)"]
    N0 --> N1
    N0 --> N2
    N0 --> N5
    N0 --> N6
    N0 --> N7
    N0 --> N8
    N0 --> N9
    N2 --> N1
    N2 --> N4
    N2 --> N6
    N3 --> N4
    N5 --> N1
    N5 --> N2
    N5 --> N6
    N5 --> N7
    N6 --> N1
    N7 --> N2
    N7 --> N3
    N7 --> N6
    N8 --> N1
    N8 --> N2
    N8 --> N5
    N8 --> N6
    N8 --> N7
    N8 --> N9
    N9 --> N1
    N9 --> N2
    N9 --> N5
    N9 --> N6
    N10 --> N6
    N10 --> N7
    N10 --> N11
    N11 --> N7
```

ノードの括弧内はファイル数。名前は `PseudoPrime.` を省略している。異なるグループ間の直接依存 39 方向のうち、配置方針に沿う 33 方向を表示する。図に表示しない 6 方向は下表にすべて示す。表示する辺はすべて実際のimportに基づく。図から除いた依存がソース上で解消されたことを意味しない。

| 依存元 | 依存先 | import数 |
|---|---|---|
| `Analysis` | `AnalyticNumberTheory` | 27 |
| `Analysis` | `NumberTheory` | 3 |
| `LLS` | `PrimeTestBounds` | 5 |
| `LLS` | `PseudoSquare` | 2 |
| `NumberTheory` | `AnalyticNumberTheory` | 1 |
| `PrimeTest` | `Tests` | 1 |
<!-- namespace-dependencies:end -->

[namespace_dependencies.py](../scripts/namespace_dependencies.py) は、現在のソースから図・件数・省略した依存の表を再生成する。表示方向はスクリプトの `LAYERS` で定める。 `--check` は文書と集計結果の一致だけを検査し、逆依存の解消や配置の妥当性を保証しない。

```powershell
python -X utf8 scripts/namespace_dependencies.py --write
python -X utf8 scripts/namespace_dependencies.py --check
```

## 既存APIを共有する補助ディレクトリ

次のディレクトリ群は共通APIの実装を分野や処理段階で分割している。ディレクトリ名を名前空間へ追加すると既存の型・述語・証人APIを変更するため、以下の基底名前空間を共有する。

| ソースの区分 | 共有する基底名前空間 |
|---|---|
| `PseudoSquare/Bounds`、 `PseudoSquare/Computation` | `PseudoPrime.PseudoSquare` |
| `PrimeTest` 以下のBPSW・EulerJacobi・Lucas・LucasV・MillerRabin・Selfridge・StrongLucasの実装 | `PseudoPrime.PrimeTest` |
| `NumberTheory` 以下のJacobi・JacobiWitness・Kroneckerの実装 | `PseudoPrime.NumberTheory` |
| `AnalyticNumberTheory/NumberField` のDedekind L関数API | `PseudoPrime.AnalyticNumberTheory` |

例外の対象ディレクトリと許可する名前空間は [namespace_layout_policy.json](../scripts/namespace_layout_policy.json) に列挙している。許可は列挙した名前空間に限り、同じ接頭辞を持つ別分野へは広げない。 `PseudoSquare.SmallN` の内部計算も対象ディレクトリと名前空間を個別に指定している。

## 配置の検査

[check_namespace_layout.py](../scripts/check_namespace_layout.py) はコメントと文字列を除き、入れ子の名前空間を解決して宣言の所属を検査する。隠しディレクトリと `archive` 以下は対象外とする。実行用の `main` はモジュール直下に置ける。

```powershell
python -X utf8 scripts/check_namespace_layout.py
python -X utf8 scripts/check_namespace_layout.py --json
```

スクリプトは作業ディレクトリに依存せず、配置違反があれば非ゼロで終了する。検査範囲は宣言の配置であり、定理の型や証明はLeanのビルドとLSP診断で別途確認する。
