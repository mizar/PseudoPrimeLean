# 比較図の生成

このディレクトリの4本の `plot_*.py` で比較図を生成する。必要なPythonパッケージはNumPyとMatplotlibである。3本の比較図スクリプトは同じディレクトリの描画補助を使い、 `data/` のCSVを入力として読む。この3本は作業ディレクトリに依存せず、既定ではLeanリポジトリの `doc/figures/` にSVGとPNGを出力する。

Leanリポジトリのルートから次を実行する。

```powershell
python -X utf8 scripts/plot_mr_comparison.py
python -X utf8 scripts/plot_qne1_comparison.py
python -X utf8 scripts/plot_qneg1_comparison.py
```

出力先は `--output-dir` で指定できる。 `--max-power` は横軸右端の入力を10の累乗で指定する。負値比較の `--negative-minima` では別の素数別最小入力CSVを指定できる。

凹フィット図はフィット結果JSONと出力先を明示して実行する。JSONには `smaller_regions["100000"]` と `selection_100000` が必要である。

```powershell
python -X utf8 scripts/plot_small_witness_concave.py --results ../PseudoPrimeWork/small_region_concave_fitting/results_3000000.json --output doc/figures
```

## 描画データ

| ファイル | 用途 |
|---|---|
| [mr_records.csv](data/mr_records.csv) | Miller–Rabinの記録点 |
| [non_one_records.csv](data/non_one_records.csv) | 非1証人の記録点 |
| [negative_records.csv](data/negative_records.csv) | 負値証人の記録点 |
| [non_one_prime_minima.csv](data/non_one_prime_minima.csv) | 非1の素数別最小入力 |
| [negative_prime_minima.csv](data/negative_prime_minima.csv) | 負値の素数別最小入力。空欄と行順を保持する。 |
| [negative_results.json](data/negative_results.json) | 負値記録点の範囲と値の照合情報 |

記録点と素数別最小入力は `PseudoPrimeWork/` の探索資料に基づく。負値の更新点は $n < 2^{72}$ の32点を収録し、 `symbol` は $-1$、 `L` は自然対数 $\ln n$ を有効桁数80桁で記す。非1の更新点は $n < 2^{80}$ の49点を収録する。照合用JSONには探索範囲と更新点を保存する。研究側の読み出し・再生成処理もこのディレクトリのデータを参照する。

スクリプト内の数値照合は記録点と描画用の有限標本を検査する。数学的な適用範囲や最小性は、それぞれのLean定理・研究記録の検証範囲に従う。


## 累積上界の追加図

`plot_qne1_comparison.py` は `q_four_pole_high_comparison.svg`・`.png` も生成する。係数777/1000の有限入口と、入口未満を覆う定数項を残した累積候補を区別し、係数4/5の既存候補との最小値を表示する。`plot_qneg1_comparison.py` も同じ共通端点・定数・有理極核の候補を参照する。

`plot_mr_comparison.py` は `mr_cumulative_high_comparison.svg`・`.png` を追加生成する。既存の7プロファイルについて、入口以前の履歴を保持した全域累積上界と点ごとの候補を比較する。表示用の実数補間・有限標本の照合は、全自然数に対するLean証明の代わりにはしない。


`plot_mr_comparison.py` は `mr_endpoint79_guard_comparison.svg` とPNGも生成する。固定79のguard付き候補と既存tuned選択値を比較し、Leanで厳密改善を証明した対数区間12.65以上12.659以下を示す。有限標本の整合確認は、実際の証人・最小値・局所例外に関するLean証明を代替しない。


`plot_mr_comparison.py` は `mr_next_tuned_comparison.svg` とPNGも生成する。固定79と、残差4.185・3.934のGaussian surplus候補を合成した選択値を既存tunedと比較する。Gaussianの厳密比較は選択値の区間定理であり、丸め後の常時厳密改善とは区別する。
