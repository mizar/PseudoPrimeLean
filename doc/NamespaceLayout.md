# 名前空間とソース配置

Leanソースの基底名前空間は `PseudoPrime/` を含む親ディレクトリのパスに対応させる。例えば、 `PseudoPrime/Analysis/` の宣言は `PseudoPrime.Analysis` に、 `PseudoPrime/PrimeTestBounds/MillerRabin/` の宣言は `PseudoPrime.PrimeTestBounds.MillerRabin` に配置する。型固有の下位名前空間は、その型を扱うファイル内で使える。

異なる分野の宣言を一つのファイルに混在させない。解析の補助定理とMiller–Rabinへの適用定理が同居する場合は、docstringと証明を含む宣言を分割し、それぞれの名前空間に対応するディレクトリへ移す。配置のみを変更する場合は完全修飾名を保持し、利用側のimportで依存関係を接続する。所属する名前空間も変更する場合は、後述の分離方針に従う。旧import経路を維持するファイルには、転送用の `public import` を置く。

## 一般的な定義・補題の分離

LLSに依存しない一般的な定義・補題は、共通の定義や広い用途を持つものから優先して `PseudoPrime.LLS` から分離し、内容に応じて `PseudoPrime.Analysis`、 `PseudoPrime.NumberTheory`、 `PseudoPrime.AnalyticNumberTheory` などへ配置する。この方針はLLSに限らない。特定の名前空間に固有の概念を必要としないことに加え、実際の共有可能性や分離の必要性も確認して配置を決める。

上流の名前空間へ配置する意義は、その分野の複数の用途で共有できる基盤を提供することにある。ある実装の基盤であることや、依存関係の上流にあることだけを配置の理由にしない。その名前空間の共通基盤として何に再利用できるか、適用先固有の選択から独立してどの役割を果たすかを判断条件に加える。現在の利用箇所が複数あることを必須にはしないが、共通基盤として役立つ用途や役割を具体的に説明できることを確認する。特定の検査方式や適用先の内部実装を支えるだけの定義・補題は、その実装を扱う側に置く。

例えば、 `PseudoPrime.NumberTheory` や `PseudoPrime.AnalyticNumberTheory` には数論や解析的数論の複数の用途に共通する汎用的な基盤を置く。一方、 `(8416299 / 100000000 : ℝ) ≤ Real.exp (-(99 / 40 : ℝ))` のように、特定の証明の内部で選んだ定数に対する数値評価は、その証明を扱う側に置く。実数と指数関数だけで述べられていても、それだけでは一般の解析APIにはならない。このような評価は広く用いられる数学定数の評価や任意の引数に使える評価とは区別する。証明に必要な内部補題を上流へ集めること自体を共通化の成果とせず、上流の名前空間を用途固有の数値評価の置き場にしない。

配置の判断には、更新頻度と再ビルドの波及範囲も含める。用途固有の評価や数値認証を多数のモジュールがimportする上流のファイルへ集めると、定数や評価の調整のたびに、その調整と関係のない下流の証明まで再ビルドが必要になり得る。長時間の再検証が反復作業を妨げ、プロジェクトの継続的な開発を難しくするため、共通化の利点に加えて変更時の費用も確認する。安定した共通の定義・基本補題と、更新の多い用途固有の評価・数値認証を別モジュールに分け、後者の変更が必要な利用側だけに波及する依存関係を作る。名前空間を分けるだけで済ませず、ファイル単位の直接・推移importと集約importも確認する。

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

## 一般名前空間への所有者移設の限定的な許可

一般名前空間への移設凍結は維持する。2026年11月3日の計画では次の4宣言に限り所有者の変更を認める。

- `NumberTheory.choose_power_lower` と `NumberTheory.card_lt_choose_of_power_budget` を `Combinatorics` へ移す。
- `PrimeTestBounds.MillerRabin.card_local_fermat_kernel_prime_pow` と `PrimeTest.local_prime_powerKernel_ne_top_of_not_dvd` を `NumberTheory` へ移す。

利用側のimport修正、同じ名前空間でのファイル分割、MR内部の責務分離と重複解消は、上記の作業に必要な範囲で行う。MRの証人上界、固定係数、有限認証やLLS・GRH固有の評価は一般側へ移さない。新しい一般側から専用領域への直接・推移依存と宣言参照は禁止する。

移設前後の定理の型と利用側を確認し、関連モジュールと全体をビルドする。静的な依存範囲の変化と実測ビルド時間は区別して報告する。対象の作業終了後は列挙した宣言以外の所有者移設を引き続き凍結する。

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

## 改善計画_1の配置計画

今回追加する宣言は次の区分で配置する。これは配置と依存の計画であり、
各ファイルの証明完成や全体ビルドの成功を示すものではない。
ファイルごとの契約と分割理由は
[詳細配置計画](../../PseudoPrimeWork/20261102_Inprovement/round1/PlacementPlan.md) に記録する。
以下のパスはLeanソースルートの `PseudoPrime/` からの相対パスである。

| 対象 | 配置先 | 所有する内容と分割理由 |
|---|---|---|
| 任意の小素数境界による尾評価 | `NumberTheory/SmallPrimeLogTail.lean` | 任意の非零の法の素因数和を、総対数と有限の小素数寄与へ分解する。核・GRH・Jacobi入力に依存せず、法の素因数費用の共通基盤として使う |
| 精密savingの固定認証 | `LLS/PreciseSavingPrime31.lean`、 `PreciseSavingScaleBounds.lean` | 選択した31と定数の認証、因数分解を要しない根の上界。任意境界の尾評価と分ける |
| 負値Jacobiへの移送と累積 | `PseudoSquare/Bounds/PreciseSavingJacobiBounds.lean`、 `PreciseSavingCumulative.lean` | 実際の証人・最小証人、小域31と全自然数の上端を扱う |
| 負値Jacobiの候補選択 | `PseudoSquare/Bounds/PreciseSavingWindowBounds.lean`、 `PreciseSavingEnvelope.lean` | 勝利区間の認証と旧公開候補全体との比較を分け、区間の調整を証人の基盤へ戻さない |
| MRの任意基底履歴 | `PrimeTestBounds/MillerRabin/BaseHistoryBounds.lean` | 小さな再帰と順序保存。現在の役割はMR履歴の構築なので、引数が一般的でもMR側に置く |
| MRのGaussian累積 | `PrimeTestBounds/MillerRabin/GaussianCumulativeBounds.lean`、 `GaussianHistoryCaps.lean` | MRへの具体化・実最小証人・旧履歴比較と、調整するcap・回復条件の認証を分ける |
| MRの改善Gaussian候補 | `PrimeTestBounds/MillerRabin/GaussianTightNumerics.lean`、 `GaussianTightBounds.lean` | 固定予算の認証と実際の証人への接続を分ける |
| MRの公開候補と比較 | `PrimeTestBounds/MillerRabin/NextTunedWitnessEnvelope.lean`、 `NextTunedNormalForm.lean`、 `GaussianTightComparison.lean`、 `GaussianTightCumulativeBounds.lean` | 既存guard内の候補置換、支配された枝の同値整理、厳密比較、累積への移送を分ける |
| 非負全域のMangoldt誤差 | `LLS/RiemannWeightedErrorGlobal.lean` | 核を要求しない既存LLS評価の拡張。任意重みの部分和評価にも使えるが、既存依存を逆転させて一般解析へ移さない |
| 固定K4の二段Abel解析 | `LLS/PaperStatements/RationalPoleDoubleAbelInputs.lean`、 `RationalPoleSecondVariation.lean`、 `RationalPoleDoubleAbel.lean`、 `RationalPolePrincipalSharp.lean` | 選択した核の微分・可積分性・実和の恒等式・主指標誤差。適用開始値やcharacterの数値予算は読み込まない |
| K4の実証人と開始値 | `LLS/PaperStatements/RationalPoleAbelWitness.lean`、 `RationalPoleAbelBudget.lean`、 `RationalPoleAbelEntrance.lean` | 元のcharacter・法の費用を保持した抽出、半直線への移送、3行の開始値認証を分ける |
| K4のJacobi累積と比較 | `PseudoSquare/Bounds/FourPoleAbelBounds.lean`、 `FourPoleAbelComparison.lean` | 実証人・累積と、Q5を含む旧公開最小値との比較を分ける。Q5の調整をAbel上界へ戻さない |
| Selfridgeの利用 | `PrimeTestBounds/Selfridge/PreciseSavingBounds.lean`、 `FourPoleAbelBounds.lean` | Jacobiの上界を停止最大・古典試行回数へ移す。空域と例外27・15は停止規約に従って処理する |
| Selfridgeの最終比較 | `PrimeTestBounds/Selfridge/FourPoleAbelComparison.lean` | Q5・Abelと非1値専用候補の最終最小値を停止・試行へ移す。比較の集約を基礎のAbel停止上界から分ける |

基本名前空間は親ディレクトリに一致させる。
`PseudoSquare/Bounds` だけは下記の既存例外に従い、 `PseudoPrime.PseudoSquare` を使う。
ファイル名を補助名前空間として追加せず、新しい例外も設けない。

一般尾評価からLLS・MR・PseudoSquareへの直接・推移importと宣言参照を追加しない。
固定認証は利用側から参照し、同じ名前空間でも、開始値・窓・capの変更が
安定した定義や恒等式へ戻る依存を作らない。
実装ファイルは必要な個別モジュールをimportし、分野全体の集約ファイルをimportしない。

公開時は `NumberTheory.lean`、 `LLS.lean`、 `PseudoSquare.lean`、
`PrimeTestBounds.lean` から最終の利用側へ到達できることを確認する。
直接importだけでなく、推移importと集約importもファイル単位で監査する。
既存の一般APIの移設は今回の対象に含めない。
命名・行長・配置、単体CLIとLSPを確認し、最終整形後に全体CLIを行う。
波及試験は省略し、静的な依存分析だけで再ビルドの削減や高速化を実証したとは扱わない。

## 名前空間の依存図

図は配置方針に沿う向きのimportを表示し、図に表示しない依存も下表に列挙する。名前空間単位の集計であり、ファイル単位の循環検査や、各宣言の前提・主張・証明の意味上の監査を代替しない。図と表の両方を確認し、一般側から適用側へ戻る依存は、宣言の配置と数学的な依存に照らして個別に見直す。

<!-- namespace-dependencies:start -->
対象はチェックアウト内のLeanソース 2923 ファイル。隠しディレクトリ・ `archive` ・シンボリックリンク以下は走査しない。未追跡ファイルも含む。Mathlibなどの外部依存と同一グループ内の辺は図から除く。

```mermaid
flowchart TD
    N0["PseudoPrime (1)"]
    N1["Analysis (416)"]
    N2["AnalyticNumberTheory (562)"]
    N3["Combinatorics (4)"]
    N4["Data (1)"]
    N5["LLS (994)"]
    N6["NumberTheory (260)"]
    N7["PrimeTest (162)"]
    N8["PrimeTestBounds (345)"]
    N9["PseudoSquare (156)"]
    N10["Tests (18)"]
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
    N5 --> N3
    N5 --> N6
    N5 --> N7
    N6 --> N1
    N6 --> N3
    N7 --> N2
    N7 --> N3
    N7 --> N6
    N8 --> N1
    N8 --> N2
    N8 --> N3
    N8 --> N5
    N8 --> N6
    N8 --> N7
    N8 --> N9
    N9 --> N1
    N9 --> N2
    N9 --> N5
    N9 --> N6
    N10 --> N5
    N10 --> N6
    N10 --> N7
    N10 --> N11
    N11 --> N7
```

ノードの括弧内はファイル数。名前は `PseudoPrime.` を省略している。異なるグループ間の直接依存 43 方向のうち、配置方針に沿う 37 方向を表示する。図に表示しない 6 方向は下表にすべて示す。表示する辺はすべて実際のimportに基づく。図から除いた依存がソース上で解消されたことを意味しない。

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
