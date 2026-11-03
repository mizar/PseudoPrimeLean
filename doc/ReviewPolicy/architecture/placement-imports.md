# ソース配置と依存

識別子 `PLACE-01`：Leanソースの基底名前空間は `PseudoPrime/` を含む親ディレクトリに対応させる。例えば `PseudoPrime/Analysis/` は `PseudoPrime.Analysis`、 `PseudoPrime/PrimeTestBounds/MillerRabin/` は `PseudoPrime.PrimeTestBounds.MillerRabin` を使う。型固有の下位名前空間はその型を扱うファイル内で使える。

識別子 `PLACE-02`：異なる分野の宣言を同じファイルに混在させない。docstring、定義本体、証明を一体で扱う。同じ名前空間のファイル分割では完全修飾名を保持し、利用側のimportを更新する。旧経路の扱いは [APIと互換性](api-compatibility.md) に従う。

識別子 `PLACE-03`：新規の逆依存を禁止する。直接・推移import、集約import、型・定義本体・証明の参照を確認する。安定した共通APIと更新の多い用途固有の評価・認証をファイル単位で分ける。移設の可否には [一般化と所有者](generality-ownership.md) の方針が優先する。

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
