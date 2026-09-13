# C++・PythonのBPSW参考実装

公開ソースは [examples/bpsw](../examples/bpsw) に置く。

| ファイル | 内容 |
|---|---|
| [baillie_psw_strengthened.py](../examples/bpsw/baillie_psw_strengthened.py) | Pythonの多倍長整数による通常版・強化版BPSW |
| [baillie_psw_strengthened.cpp](../examples/bpsw/baillie_psw_strengthened.cpp) | Boost.Multiprecision `cpp_int` によるC++版 |
| [g++-static.cmd](../examples/bpsw/g++-static.cmd) | MSYS2 MINGW64のGCCを使うstaticビルド |
| [clang++-static.cmd](../examples/bpsw/clang++-static.cmd) | MSYS2 CLANG64のClangを使うstaticビルド |

Lean側の仕様・証明については [PrimeTest](PrimeTest.md) を参照する。

## 公開関数と処理

両言語は次の主要関数を持つ。C++では `bpsw_strengthened` 名前空間に置かれている。

| 関数 | 意味 |
|---|---|
| `isprime_bpsw(n)` | 底2 Strong Miller–RabinとMethod A*によるStrong Lucasの組合せ |
| `isprime_strengthened_bpsw(n)` | 上記にLucas-VとQのEuler条件を加える |
| `lucas_selfridge_scan(n)` | Wheel30候補からJacobi−1または非自明因子を検出 |
| `lucas_params_a(n)`・`lucas_params_a_star(n)` | Method A / A*のP・Qを選ぶ |
| `lucas_uvq_mod(n, p, q, k)` | LucasのU・VとQの冪を法nで評価 |
| `jacobi_symbol(a, n)`・`kronecker_symbol(a, n)` | 整数の記号計算 |

トップレベル2関数は、2を受理し、2未満と2以外の偶数を棄却する。
`true` / `True` はこのテストの受理を意味し、任意精度の整数に対する素数証明書ではない。
下位関数には奇数・正値等の前提があるため、汎用の判定にはトップレベル関数を使う。

Selfridge候補は接頭部 `5,7,9,11,13,15,17,19,23,29` の後、30と互いに素な剰余を使って増加する。
探索時には平方数を先に除外し、`i == n` の候補を飛ばす。
返り値 `(D, -1)` はパラメータ選択成功、`(D, 0)` は因子検出、`(0, 0)` は平方数である。
これはfuel付きの探索APIではない。

## Pythonで実行

Python 3.9以降と標準ライブラリを使用する。外部のPythonパッケージは不要。
以下は公開リポジトリのルートで実行するPowerShell例である。

```powershell
python -c "from examples.bpsw.baillie_psw_strengthened import isprime_bpsw, isprime_strengthened_bpsw; print(isprime_bpsw(7), isprime_strengthened_bpsw(2047))"
```

出力は `True False`。

スクリプトを直接起動した場合は、判定結果を1行ずつ返すCLIではなく、比較集計用のドライバになる。
入力は1行に1個の、3以上の奇数。空行またはEOFで終了する。

```powershell
@('7', '9', '11', '15', '2047') | python examples/bpsw/baillie_psw_strengthened.py
```

出力は `5 3 2 2 2 2 2`。左から入力数、底2 MR、7底MR、13底MR、Strong Lucas、通常BPSW、
強化BPSWの受理数である。7底・13底MRは比較用であり、BPSWの返り値に追加される条件ではない。
両MRリストが受理して強化BPSWが棄却した場合は、集計の前に診断行も出力する。
2・偶数・負数の境界入力を試す場合は、このドライバではなくトップレベル関数を呼ぶ。

## C++をstaticビルドして実行

C++17以降、Boostのヘッダ、MSYS2のMINGW64またはCLANG64ツールチェーンを使用する。
同梱のcmdは `%USERPROFILE%\scoop\apps\msys2\current` 配下を参照し、対応するbinを
ビルドプロセスのPATHに加え、コンパイラに `-static` を渡す。
この配置と異なる環境ではcmd内のMSYS2パスを合わせる。

動的ランタイムDLLの探索による実行への影響を避けるため、Windowsでは次のstaticビルドを使う。

```powershell
New-Item -ItemType Directory -Force .work | Out-Null
.\examples\bpsw\g++-static.cmd -std=c++17 -O2 -Wall -Wextra -pedantic examples/bpsw/baillie_psw_strengthened.cpp -o .work/bpsw-gcc-static.exe
@('7', '9', '11', '15', '2047') | .\.work\bpsw-gcc-static.exe
```

Clangの場合は次の通り。

```powershell
.\examples\bpsw\clang++-static.cmd -std=c++17 -O2 -Wall -Wextra -pedantic examples/bpsw/baillie_psw_strengthened.cpp -o .work/bpsw-clang-static.exe
@('7', '9', '11', '15', '2047') | .\.work\bpsw-clang-static.exe
```

どちらも上記Pythonドライバと同じ列順で集計する。
別のC++プログラムへ組み込む場合は `BPSW_STRENGTHENED_NO_MAIN` を定義するとドライバのmainを除ける。
入力の整数型は `bpsw_strengthened::bigint`。

## Leanとの対応と相違

| 観点 | Leanの公開トップレベル | C++・Python参考実装 |
|---|---|---|
| 通常版 | `bailliePSW` | `isprime_bpsw` |
| 強化版 | `strengthenedBPSW` | `isprime_strengthened_bpsw` |
| 初期処理 | 小入力・偶数・平方数のprecheck | 小入力・偶数を処理し、MRを先行。平方数はLucas側の探索前に処理 |
| パラメータ探索 | 古典候補の昇順、純粋Jacobi−1、fuel `n - 2` | Wheel30、因子検出付き、明示fuelなし |
| 証明 | 無条件の素数受理定理と個別仕様 | 実行用ソース。Leanとのプログラム同値性は未形式化 |

[NumberTheory](NumberTheory.md)の目撃者存在、PrimeTestの候補順序・停止値比較、
[SelfridgeBoundGrh](SelfridgeBoundGrh.md)の定量評価は、関連する数学的な根拠を与える。
ただし、Leanの数学的停止値に関する証明と、これらのC++・Python関数の実行意味論との対応を
一括して証明したという意味ではない。有限の照合結果も、その形式的な同値証明とは区別する。

## 配置時の検証

Python、および両cmdでstaticビルドしたC++版について、`-10 ≤ n ≤ 4096` の通常版・強化版の
結果を独立した試し割りと照合した。また、`(2^127 - 1)^2` と `2(2^127 - 1)` の棄却、
上記集計例の一致を確認した。C++は `-Wall -Wextra -pedantic` で診断なし。

[PrimeTestへ](PrimeTest.md) · [構成全体へ](README.md)
