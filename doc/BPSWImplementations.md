# C++・Python の BPSW 参考実装

公開ソースは [examples/bpsw](../examples/bpsw) に置く。

| ファイル | 内容 |
|---|---|
| [baillie_psw_strengthened.py](../examples/bpsw/baillie_psw_strengthened.py) | Python の多倍長整数による通常版・強化版 BPSW |
| [baillie_psw_strengthened.cpp](../examples/bpsw/baillie_psw_strengthened.cpp) | Boost.Multiprecision `cpp_int` による C++ 版 |
| [g++-static.cmd](../examples/bpsw/g++-static.cmd) | MSYS2 MINGW64 の GCC を使う static ビルド |
| [clang++-static.cmd](../examples/bpsw/clang++-static.cmd) | MSYS2 CLANG64 の Clang を使う static ビルド |

Lean 側の仕様・証明については [PrimeTest](PrimeTest.md) を参照する。

## 公開関数と処理

両言語は次の主要関数を持つ。C++ では `bpsw_strengthened` 名前空間に置かれている。

| 関数 | 意味 |
|---|---|
| `isprime_bpsw(n)` | 底 2 Strong Miller–Rabin と `Method A*` による Strong Lucas の組合せ |
| `isprime_strengthened_bpsw(n)` | 上記に Lucas-V と $Q$ の Euler 条件を加える |
| `lucas_selfridge_scan(n)` | Wheel30 候補から Jacobi 値 $-1$ または非自明因子を検出 |
| `lucas_params_a(n)` ・ `lucas_params_a_star(n)` | Method A / `A*` の $P$ と $Q$ を選ぶ |
| `lucas_uvq_mod(n, p, q, k)` | Lucas の $U$・ $V$ と $Q$ の冪を法 $n$ で評価 |
| `jacobi_symbol(a, n)` ・ `kronecker_symbol(a, n)` | 整数の記号計算 |

トップレベル 2 関数は、2 を受理し、2 未満と 2 以外の偶数を棄却する。 `true` / `True` はこのテストの受理を意味し、任意精度の整数に対する素数証明書ではない。下位関数には奇数・正値等の前提があるため、汎用の判定にはトップレベル関数を使う。

Selfridge 候補は接頭部 $5, 7, 9, 11, 13, 15, 17, 19, 23, 29$ の後、 $30$ と互いに素な剰余を使って増加する。探索時には平方数を先に除外し、 `i == n` の候補を飛ばす。返り値 `(D, -1)` はパラメータ選択成功、 `(D, 0)` は因子検出、 `(0, 0)` は平方数である。これは `fuel` による回数制限を持つ探索 API ではない。

## Python で実行

Python 3.9 以降と標準ライブラリを使用する。外部の Python パッケージは不要。以下は公開リポジトリのルートで実行する PowerShell 例である。

```powershell
python -c "from examples.bpsw.baillie_psw_strengthened import isprime_bpsw, isprime_strengthened_bpsw; print(isprime_bpsw(7), isprime_strengthened_bpsw(2047))"
```

出力は `True False`。

スクリプトを直接起動した場合は、判定結果を 1 行ずつ返す CLI ではなく、比較集計用のドライバになる。各行に 3 以上の奇数を 1 個ずつ入力する。空行または EOF で終了する。

```powershell
@('7', '9', '11', '15', '2047') | python examples/bpsw/baillie_psw_strengthened.py
```

出力は `5 3 2 2 2 2 2`。左から入力数、底 2 MR、7 底 MR、13 底 MR、Strong Lucas、通常 BPSW、強化 BPSW の受理数である。7 底・13 底 MR は比較用であり、BPSW の返り値に追加される条件ではない。両 MR リストが受理して強化 BPSW が棄却した場合は、集計の前に診断行も出力する。 2・偶数・負数の境界入力を試す場合は、このドライバではなくトップレベル関数を呼ぶ。

## C++ を static ビルドして実行

C++17 以降、Boost のヘッダ、MSYS2 の MINGW64 または CLANG64 ツールチェーンを使用する。同梱の cmd は `%USERPROFILE%\scoop\apps\msys2\current` 配下を参照し、対応する bin をビルドプロセスの PATH に加え、コンパイラに `-static` を渡す。この配置と異なる環境では cmd 内の MSYS2 パスを合わせる。

動的ランタイム DLL の探索による実行への影響を避けるため、Windows では次の static ビルドを使う。

```powershell
New-Item -ItemType Directory -Force .work | Out-Null
.\examples\bpsw\g++-static.cmd -std=c++17 -O2 -Wall -Wextra -pedantic examples/bpsw/baillie_psw_strengthened.cpp -o .work/bpsw-gcc-static.exe
@('7', '9', '11', '15', '2047') | .\.work\bpsw-gcc-static.exe
```

Clang の場合は次の通り。

```powershell
.\examples\bpsw\clang++-static.cmd -std=c++17 -O2 -Wall -Wextra -pedantic examples/bpsw/baillie_psw_strengthened.cpp -o .work/bpsw-clang-static.exe
@('7', '9', '11', '15', '2047') | .\.work\bpsw-clang-static.exe
```

どちらも上記 Python ドライバと同じ列順で集計する。別の C++ プログラムへ組み込む場合は `BPSW_STRENGTHENED_NO_MAIN` を定義するとドライバの main を除ける。入力の整数型は `bpsw_strengthened::bigint`。

## Lean との対応と相違

| 観点 | Lean の公開トップレベル | C++・Python 参考実装 |
|---|---|---|
| 通常版 | `bailliePSW` | `isprime_bpsw` |
| 強化版 | `strengthenedBPSW` | `isprime_strengthened_bpsw` |
| 初期処理 | 小入力・偶数・平方数の precheck | 小入力・偶数を処理し、MR を先行。平方数は Lucas 側の探索前に処理 |
| パラメータ探索 | 古典候補の昇順、純粋 Jacobi 値 $-1$、fuel `n - 2` | Wheel30、因子検出付き、明示 fuel なし |
| 証明 | 無条件の素数受理定理と個別仕様 | 実行用ソース。Lean とのプログラム同値性は未形式化 |

[NumberTheory](NumberTheory.md) の証人存在、PrimeTest の候補順序・停止値比較、 [SelfridgeBoundGrh](SelfridgeBoundGrh.md) の定量評価は、関連する数学的な根拠を与える。ただし、Lean の数学的停止値に関する証明と、これらの C++・Python 関数の実行意味論との対応を一括して証明したという意味ではない。有限の照合結果も、その形式的な同値証明とは区別する。

## 配置時の検証

Python 版の区間照合は、公開リポジトリのルートで次の PowerShell コマンドにより再現できる。通常版・強化版を独立した試し割りと比較する。これは Python 版の再現手順であり、以下の C++ 版を含む配置時の検証記録とは区別する。

```powershell
@'
from math import isqrt
from examples.bpsw.baillie_psw_strengthened import isprime_bpsw, isprime_strengthened_bpsw

def trial_prime(n):
    return n >= 2 and all(n % d != 0 for d in range(2, isqrt(n) + 1))

for n in range(-10, 4097):
    expected = trial_prime(n)
    assert isprime_bpsw(n) == expected, ("BPSW", n)
    assert isprime_strengthened_bpsw(n) == expected, ("strengthened BPSW", n)
print("Python: -10 <= n <= 4096 matched trial division")
'@ | python -
```


Python、および両 cmd で static ビルドした C++ 版について、 $-10 \le n \le 4096$ の通常版・強化版の結果を独立した試し割りと照合した。また、 $(2^{127} - 1)^2$ と $2(2^{127} - 1)$ の棄却、上記集計例の一致を確認した。C++ は `-Wall -Wextra -pedantic` で診断なし。

[PrimeTest へ](PrimeTest.md) · [構成全体へ](README.md)
