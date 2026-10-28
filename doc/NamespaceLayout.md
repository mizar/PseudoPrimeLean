# 名前空間とソース配置

Leanソースの基底名前空間は `PseudoPrime/` を含む親ディレクトリのパスに対応させる。例えば、 `PseudoPrime/Analysis/` の宣言は `PseudoPrime.Analysis` に、 `PseudoPrime/PrimeTestBounds/MillerRabin/` の宣言は `PseudoPrime.PrimeTestBounds.MillerRabin` に配置する。型固有の下位名前空間は、その型を扱うファイル内で使える。

異なる分野の宣言を一つのファイルに混在させない。解析の補助定理とMiller–Rabinへの適用定理が同居する場合は、docstringと証明を含む宣言を分割し、それぞれの名前空間に対応するディレクトリへ移す。完全修飾名は保持し、利用側のimportで依存関係を接続する。旧import経路を維持するファイルには、転送用の `public import` を置く。

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
