# 名前空間の依存図

図は配置方針に沿う向きのimportを表示し、図に表示しない依存も下表に列挙する。名前空間単位の集計であり、ファイル単位の循環検査や、各宣言の前提・主張・証明の意味上の監査を代替しない。図と表の両方を確認し、一般側から適用側へ戻る依存は、宣言の配置と数学的な依存に照らして個別に見直す。

<!-- namespace-dependencies:start -->
対象はチェックアウト内のLeanソース 2937 ファイル。隠しディレクトリ・ `archive` ・シンボリックリンク以下は走査しない。未追跡ファイルも含む。Mathlibなどの外部依存と同一グループ内の辺は図から除く。

```mermaid
flowchart TD
    N0["ComparatorChallenges (6)"]
    N1["PseudoPrime (1)"]
    N2["Analysis (416)"]
    N3["AnalyticNumberTheory (562)"]
    N4["Combinatorics (4)"]
    N5["Data (1)"]
    N6["LLS (994)"]
    N7["NumberTheory (260)"]
    N8["PrimeTest (162)"]
    N9["PrimeTestBounds (353)"]
    N10["PseudoSquare (156)"]
    N11["Tests (18)"]
    N12["Tools (4)"]
    N0 --> N6
    N0 --> N9
    N0 --> N10
    N1 --> N2
    N1 --> N3
    N1 --> N6
    N1 --> N7
    N1 --> N8
    N1 --> N9
    N1 --> N10
    N3 --> N2
    N3 --> N5
    N3 --> N7
    N4 --> N5
    N6 --> N2
    N6 --> N3
    N6 --> N4
    N6 --> N7
    N6 --> N8
    N7 --> N2
    N7 --> N4
    N8 --> N3
    N8 --> N4
    N8 --> N7
    N9 --> N2
    N9 --> N3
    N9 --> N4
    N9 --> N6
    N9 --> N7
    N9 --> N8
    N9 --> N10
    N10 --> N2
    N10 --> N3
    N10 --> N6
    N10 --> N7
    N11 --> N6
    N11 --> N7
    N11 --> N8
    N11 --> N12
    N12 --> N8
```

ノードの括弧内はファイル数。名前は `PseudoPrime.` を省略している。異なるグループ間の直接依存 46 方向のうち、配置方針に沿う 40 方向を表示する。図に表示しない 6 方向は下表にすべて示す。表示する辺はすべて実際のimportに基づく。図から除いた依存がソース上で解消されたことを意味しない。

| 依存元 | 依存先 | import数 |
|---|---|---|
| `Analysis` | `AnalyticNumberTheory` | 27 |
| `Analysis` | `NumberTheory` | 3 |
| `LLS` | `PrimeTestBounds` | 5 |
| `LLS` | `PseudoSquare` | 2 |
| `NumberTheory` | `AnalyticNumberTheory` | 1 |
| `PrimeTest` | `Tests` | 1 |
<!-- namespace-dependencies:end -->

[namespace_dependencies.py](../../../scripts/namespace_dependencies.py) は、現在のソースから図・件数・省略した依存の表を再生成する。表示方向はスクリプトの `LAYERS` で定める。 `--check` は文書と集計結果の一致だけを検査し、逆依存の解消や配置の妥当性を保証しない。

```powershell
python -X utf8 scripts/namespace_dependencies.py --write
python -X utf8 scripts/namespace_dependencies.py --check
```
