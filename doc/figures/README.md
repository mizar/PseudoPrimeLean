# 証人上界の比較図

図の曲線は各適用域で証明済みの候補を最小化したもの。数値描画や補間をLeanの区間・全域証明の代わりにはしない。

| 図 | 表す上界・比較 | 本文のまとめ | 生成スクリプト |
|---|---|---|---|
| [MR上界](mr_upper_bound_comparison.svg) | 現在のMR包絡線と最小証人記録 | [MR比較グラフ](../MillerRabinBoundGrh.md#比較グラフ) | [plot_mr_comparison.py](../../scripts/plot_mr_comparison.py) |
| [MR全域累積](mr_cumulative_high_comparison.svg) | 高域8候補と前段から縮小した履歴を使う累積上界 $C(N)$ | [MR累積上界](../MillerRabinBoundGrh.md#全域の累積上界) | [plot_mr_comparison.py](../../scripts/plot_mr_comparison.py) |
| [非1値証人](qne1_upper_bound_comparison.svg) | $Q_{\ne1}(B)$ と上界 $U_{\ne1}(B)$ | [PseudoSquare](../PseudoSquare.md#証人別の上界式の適用区間と比較)・[Selfridge](../SelfridgeBoundGrh.md#累積上界の適用区間と図) | [plot_qne1_comparison.py](../../scripts/plot_qne1_comparison.py) |
| [負値証人](qneg1_upper_bound_comparison.svg) | $Q_{-1}(B)$ と上界 $U_{-1}(B)$ | [PseudoSquare](../PseudoSquare.md#証人別の上界式の適用区間と比較)・[Selfridge](../SelfridgeBoundGrh.md#累積上界の適用区間と図) | [plot_qneg1_comparison.py](../../scripts/plot_qneg1_comparison.py) |
| [第四極核の高域累積](q_four_pole_high_comparison.svg) | 短縮した3入口の候補 $F_4(B)$ と係数4/5の候補の最小値 | [PseudoSquareの累積上界](../PseudoSquare.md#累積上界の構成)・[Selfridge](../SelfridgeBoundGrh.md#累積上界の適用区間と図) | [plot_qne1_comparison.py](../../scripts/plot_qne1_comparison.py) |

Selfridgeとの対応は同じ上端 $B$ に含まれる正の奇数・非平方入力上の累積最大で述べる。GRHなしで、非1値系列は $B\ge751$、純粋負値系列は $B\ge399$ から、PseudoSquare・古典Selfridge・Wheel30の対応する最大値が等しい。解析的上界にはGRHを仮定する。小さい上端の例外は [共通前提の表](../PseudoSquare.md#selfridgeと共有する前提と累積最大値) にまとめた。

第四極核は係数 $79/100,39/50,777/1000$ に対し、それぞれ対数尺度の入口
$900000000,14400000000,1440000000000$ を持つ。
累積候補は各行で $c\max\lbrace E,\ln B\rbrace^2$ とし、入口未満の入力も覆う。
[高域のまとめ](../PseudoSquare.md#高域の累積上界) を参照する。
非1値図のinsetは $10^6 < B \le 10^{16384}$ とし、有限上界47の区間を除く。

各SVGと同名のPNGも保存している。
