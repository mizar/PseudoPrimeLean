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
