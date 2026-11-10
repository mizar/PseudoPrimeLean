# ソース配置と依存

識別子 `PLACE-01`：Leanソースの基底名前空間は `PseudoPrime/` を含む親ディレクトリに対応させる。例えば `PseudoPrime/Analysis/` は `PseudoPrime.Analysis`、 `PseudoPrime/PrimeTestBounds/MillerRabin/` は `PseudoPrime.PrimeTestBounds.MillerRabin` を使う。型固有の下位名前空間はその型を扱うファイル内で使える。

識別子 `PLACE-02`：異なる分野の宣言を同じファイルに混在させない。docstring、定義本体、証明を一体で扱う。同じ名前空間のファイル分割では完全修飾名を保持し、利用側のimportを更新する。旧経路の扱いは [APIと互換性](api-compatibility.md) に従う。

識別子 `PLACE-03`：新規の逆依存を禁止する。直接・推移import、集約import、型・定義本体・証明の参照を確認する。安定した共通APIと更新の多い用途固有の評価・認証をファイル単位で分ける。移設の可否には [一般化と所有者](generality-ownership.md) の方針が優先する。

識別子 `PLACE-04`：一般理論・共通checkerと用途別の数表・認証をファイル単位で分離する。名前空間を分けても、集約importを通じて一般側が用途別の全表に推移依存する場合は分離できていない。各利用側の直接・推移importを確認する。有限認証の役割分担は [有限認証](finite-certificates.md) に従う。

識別子 `PLACE-05`：分類や区間ごとの証明が独立して成立する場合は、それぞれが必要な共通基盤と対応する区間定理に依存する構成を優先する。他の分類の統合定理や、証明に不要な別区間の数表を経由していないか、直接・推移importを確認する。区間の重複は依存関係を整理する妨げとしない。

分類別の累積区間と分類を統合する定理は役割を分ける。細かな区間を全分類で順次統合する必要がなければ、そのためだけの連鎖を設けない。共通基盤を共有するための依存と、証明上不要な依存を区別し、依存図だけで数学的な独立性を判断しない。

識別子 `PLACE-06`：公開する宣言の型や後続の公開APIに必要な依存は `public import` とし、証明内部だけで使う依存は原則として通常の `import` とする。宣言も同様に、内部専用の補助定義・補題は非公開を検討し、意図して提供するAPIは現在の利用箇所がなくても公開を維持する。可視性の変更前後で公開APIと利用側を確認し、型や定義の展開に必要な依存を失わないようにする。

`public import` を通常の `import` に変えても、そのモジュールの直接・推移依存や再ビルドの必要性が自動的になくなるわけではない。再公開の削減とimport経路の除去は別々に確認する。既存APIの変更が必要な場合は [APIと互換性](api-compatibility.md) に従う。

## 共有APIの構造的なディレクトリ

次のディレクトリ群は共通APIの実装を分野や処理段階で分割している。ディレクトリ名を名前空間へ追加すると既存の型・述語・証人APIを変更するため、以下の基底名前空間を共有する。

| ソースの区分 | 共有する基底名前空間 |
|---|---|
| `PseudoSquare/Bounds`、 `PseudoSquare/Computation` | `PseudoPrime.PseudoSquare` |
| `PrimeTest` 以下のBPSW・EulerJacobi・Lucas・LucasV・MillerRabin・Selfridge・StrongLucasの実装 | `PseudoPrime.PrimeTest` |
| `NumberTheory` 以下のJacobi・JacobiWitness・Kroneckerの実装 | `PseudoPrime.NumberTheory` |
| `AnalyticNumberTheory/NumberField` のDedekind L関数API | `PseudoPrime.AnalyticNumberTheory` |

例外の対象ディレクトリと許可する名前空間は [namespace_layout_policy.json](../../../scripts/namespace_layout_policy.json) に列挙している。許可は列挙した名前空間に限り、同じ接頭辞を持つ別分野へは広げない。 `PseudoSquare.SmallN` の内部計算も対象ディレクトリと名前空間を個別に指定している。

## 検査

[check_namespace_layout.py](../../../scripts/check_namespace_layout.py) はコメントと文字列を除き、入れ子の名前空間を解決して宣言の所属を検査する。隠しディレクトリと `archive` 以下は対象外とする。実行用の `main` はモジュール直下に置ける。

```powershell
python -X utf8 scripts/check_namespace_layout.py
python -X utf8 scripts/check_namespace_layout.py --json
```

スクリプトは作業ディレクトリに依存せず、配置違反があれば非ゼロで終了する。検査範囲は宣言の配置であり、定理の型や証明はLeanのビルドとLSP診断で別途確認する。

依存図の生成と限界は [依存図](../generated/namespace-dependencies.md) を参照する。
