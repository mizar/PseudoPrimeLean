# 最小奇素数の負値・非1証人の初出と更新点の探索

非平方の正奇数 $3 \le n \le N$ について、Legendre記号 $(n/p)$ が $-1$ となる最小奇素数と、$1$ 以外となる最小奇素数の更新点と、各奇素数が最小証人となる最小入力を求める。分母が候補素数 $p$ であり、素数 $2$ は候補に含めない。負値証人では値 $0$ を飛ばし、非1証人では値 $0$ も証人に含める。平方数と $1$ は除外する。

既定の上限は $N=2^{64}$。`--bits 80`で $N=2^{80}$、`--bits 128`で $N=2^{128}-1$ を指定できる。`--upper`で指定する十進整数上限は $N$ 以下を対象とし、最大値は $2^{128}-1$ である。 $2^k$ は偶数なので、`--bits k`は非平方の正奇数 $n < 2^k$ を調べる指定になる。

## ビルド

必要なものはPython 3.11以降と、C++20・`unsigned __int128`を使えるGCCまたはClangである。Pythonの追加パッケージ、Lean、既存の探索結果、外部の研究用ディレクトリは不要。このフォルダだけをコピーして利用できる。ライセンスは[Apache-2.0](LICENSE)。

### WindowsでScoopから導入する

管理者権限を使わずにPowerShellを起動する。Scoopが未導入の場合は、[公式のインストール手順](https://github.com/ScoopInstaller/Install#installation)に従って次を実行する。導入済みなら省略する。

```powershell
Set-ExecutionPolicy -ExecutionPolicy RemoteSigned -Scope CurrentUser
Invoke-RestMethod -Uri https://get.scoop.sh | Invoke-Expression
```

MSYS2とPythonを導入する。Python 3.11以降が導入済みなら、`scoop install python`は省略できる。MSYS2はScoopの[main bucket](https://github.com/ScoopInstaller/Main/blob/master/bucket/msys2.json)に含まれる。

```powershell
scoop install msys2
scoop install python
msys2
```

MSYS2の初期化が完了してシェルのプロンプトが表示されたら、`exit`を入力してPowerShellへ戻る。このフォルダで、同梱の導入用cmdを実行する。

```powershell
.\install-g++-toolchain.cmd
```

Clangを使う場合は、代わりに`install-clang++-toolchain.cmd`を実行する。こちらはCLANG64の`mingw-w64-clang-x86_64-toolchain`を導入する。

このcmdはMSYS2全体を更新し、MINGW64のツールチェーンとBoostを導入する。確認には既定の回答を使う。基幹部分の更新で処理が終了した場合は、同じcmdを再実行する。詳細はMSYS2の[更新手順](https://www.msys2.org/docs/updating/)と[toolchainパッケージ一覧](https://packages.msys2.org/groups/mingw-w64-x86_64-toolchain)を参照する。探索プログラム自体はBoostを使わない。

導入用cmdとビルド用cmdは、Scoopの標準配置である`%USERPROFILE%\scoop\apps\msys2\current`を使う。別の場所へ導入した場合は、導入用cmdの`BPSW_MSYS2_ROOT`と、ビルド用cmdの`MSYS2_MINGW64`または`MSYS2_CLANG64`を変更する。ビルド用cmd内でコンパイラのPATHを設定するため、PowerShell側でのPATH追加は不要である。

### ビルドコマンド

Windowsでは、このフォルダで次を実行する。

```powershell
.\g++-static.cmd -O3 -std=c++20 -pthread search.cpp -o search.exe
```

Clangでビルドする場合は次を使う。

```powershell
.\clang++-static.cmd -O3 -std=c++20 -pthread search.cpp -o search.exe
```

両方のビルド用cmdは`-static`を付ける。C++の言語規格は呼び出し側で指定する。実行時のツールチェーンのDLLへの依存を避けるため、Windowsではこれらのコマンドを使う。

Linuxでは次でビルドする。

```sh
g++ -O3 -std=c++20 -pthread search.cpp -o search
```

## 実行

まず小さい範囲で動作を確認する。以下のPythonコマンドはWindowsとLinuxで共通である。

```sh
python records.py --upper 1000000 --threads 4 --work-dir small-work
```

両方の証人を既定の $2^{64}$ まで探索する。

```sh
python records.py --threads 8 --work-dir u64-work
```

上限、証人の種類、作業先を指定する例を示す。

```sh
python records.py --bits 80 --threads 8 --work-dir u80-work
python records.py --bits 128 --threads 8 --work-dir u128-work
python records.py --kind non_one --bits 80 --threads 8 --work-dir non-one-u80
python records.py --kind negative --upper 10000000000 --threads 8 --work-dir negative-1e10
python records.py --help
```

`--kind`は`both`、`negative`、`non_one`を選べる。既定は`both`。`--bits`と`--upper`は併用できない。`--bits`は1から128まで指定できる。スレッド数の既定値はCPU数であり、メモリ使用量を抑える場合は明示的に小さくする。`--engine`で実行ファイルの場所、`--chunk-size`でチャンク当たりの目安となる候補数を指定できる。

### エンジンで128-bit上端の区間を調べる

`search.cpp`の実行ファイルは、`--bits 128`または`--upper-exclusive 340282366920938463463374607431768211456`で $n < 2^{128}$ を指定できる。`--lower`は下限を含む指定で、既定値は1である。次は上端付近の257整数に含まれる非平方の正奇数を調べる例である。

```powershell
.\search.exe --bits 128 --lower 340282366920938463463374607431768211199 --threshold 3 --wheel-limit 3 --threads 2 --chunk-size 32 --checkpoint-seconds 0 --work-dir high128-work
```

既定では負値証人を扱い、`--non-one`を加えると非1証人を扱う。出力はチャンクごとの証人別最小入力と件数であり、下限未満の入力を含む累積最大値ではない。`--lower`を使った作業先は、全域の累積最大値を集計する`records.py`とは分ける。

## 出力と再開

作業先の`negative_prime_minima.csv`と`non_one_prime_minima.csv`には、各奇素数を最小証人とする最小の非平方正奇数を`witness,n`の列で、素数の昇順に保存する。負値版は、その素数で初めてLegendre記号が $-1$ となる入力を集める。非1版は、その素数で初めてLegendre記号が $0$ または $-1$ となる入力を集める。最大値を更新しない素数の初出も含む。

表には、その時点で見つかった最大の証人以下の奇素数をすべて載せる。対象範囲内で最小入力が見つからない素数の`n`は空欄にする。空欄は解が存在しないという意味ではない。表に載らない、それより大きい奇素数も対象範囲内では未出現である。

作業先の`negative_records.csv`と`non_one_records.csv`には、初期点を含む更新点を`n,witness`の十進整数で保存する。各CSVの対象範囲は`status.json`の`searches`内にある`covered_inclusive`で確認する。指定上限全体の完了条件は、最上位の`complete`が`true`になることである。

`status.json`の各探索にある`minima_complete`は、`prime_minima.csv`が全素数の最小入力を含むかを示す。通常の新版作業先では`true`である。更新点だけを保存する旧形式から移行した場合は`false`となり、旧範囲内の非更新素数について最小入力が分からない。更新点CSVは旧範囲を含めて正確に保たれる。

探索中の新しい候補を、未完了範囲の確定更新点としてCSVへ追加することはない。各段階の全チャンクが完了した後に、証人別の最小入力を統合してCSVを更新する。探索済み上端を $C$、指定上限を $N$ とすると、次の上端は $U=\min(N,16C,C+2^{64})$ とし、未探索区間 $C < n \le U$ だけを実行する。小さい範囲では16倍ずつ広げるが、1回の追加探索の幅は $2^{64}$ 以下に制限する。この幅は入力整数の区間幅であり、`--chunk-size`の候補数とは別である。

追加区間の下端が $2^{64}$ 以上で、区間幅が $2^{20}$ 以下の場合、エンジンはその区間を直接走査する。これにより、高い下端に短い区間を追加したときに、CRT座標上の空チャンクを順に調べる処理を避ける。

`identity.json`には種類・チャンク設定と、Python・C++ソース・実行ファイルのSHA-256を保存する。指定上限は`status.json`に保存し、同じ作業先で`--upper`や`--bits`を増やせば、確定済みの最小入力と探索範囲を保持して追加探索する。途中のジョブがある場合は、その元の範囲を再開してから追加範囲へ進む。上限の縮小、種類・チャンク設定・未対応のコード変更は拒否する。スレッド数は変更できる。

対応する旧版の作業先も、同じディレクトリで利用できる。探索幅を制限した直前版では、種類・チャンク設定・C++ソース・実行ファイルが一致すれば、保存済みの探索を引き継ぐ。更新点だけを集計する形式1の既知の版では、元の状態を`identity.format1.json`と`status.format1.json`に保存し、旧ジョブを残して`records-v3/`内で探索する。完了済みの上端と更新点を引き継ぐため、追加探索はその直後から始まり、確定済み範囲を再走査しない。この形式には素数別の初出情報がないので、移行後も`minima_complete`は`false`のままである。

例えば、同じ作業先で上限を100万から200万へ広げるには、次の順に実行する。最初の探索を中断した場合も、停止要求を解除した後に2番目のコマンドで再開できる。

```powershell
python records.py --upper 1000000 --chunk-size 65536 --work-dir witness-records-work
python records.py --upper 2000000 --chunk-size 65536 --work-dir witness-records-work
```

中断するには、実行中のジョブのフォルダに空の`stop.request`を作る。ジョブ名は標準出力の種類・しきい値・上限に対応する`negative_t43_u160000`などである。処理中のチャンクが終わると停止する。Ctrl+Cでも停止を要求する。再開時は該当する`stop.request`を削除し、同じPythonコマンドを実行する。結果ログに完全に保存されたチャンクを再利用する。強制終了で保存されなかったチャンクは再計算する。

ジョブごとの`search.log`に進行状況を保存する。`odd/results-0.journal`から`odd/results-15.journal`までの最大16本に、チャンクごとの証人別最小入力と件数を追記する。空のチャンクも完了レコードを残す。結果ファイル数はチャンク数やスレッド数によって増えない。`odd/done.bitmap`は完了状況のキャッシュである。

再開時は結果ログのチェックサムを検証して完了状況を復元し、末尾の書き込み途中のレコードだけを切り捨てて再探索する。完全なレコードの破損や重複を検出した場合は停止する。プロセスの強制終了後も同じコマンドで再開でき、`--threads`は変更できる。OSのキャッシュを含む停電時の永続化までは保証しない。途中ファイルを移動・編集しないこと。

`records.py`による同じ作業先での多重起動はOSのファイルロックで防ぐ。旧版の`chunk-*.csv`は新版の結果ログとして再利用しない。上記の旧版移行ではファイルを残し、`records-v3`以下に新版の結果を保存する。

## 探索方法と検証範囲

最初の1万までは直接走査し、その後は上限を最大16倍ずつ広げる。確定済みの最大証人を $b$ とすると、新しい更新点は、$b$ 以下のすべての奇素数で証人条件を満たさない入力に限られる。負値探索では各指標値が $0$ または $1$、非1探索ではすべて $1$ となる条件を課す。

`search.cpp`は既存の`negative_records_branches.cpp`を基に、CRTの二分割、剰余類のwheel、座標フィルタ、並列チャンク処理を使う。公開用CLIは、負値探索でも値 $0$ の枝を含む全入力を直接対象にする。既存の符号別最小入力表や80-bit候補一覧を再利用しない。各段階では、未出現の最小奇素数をしきい値として候補を列挙し、証人別の最小入力を保存する。既に初出が確定した素数の最小入力は保持する。最大証人より小さい未出現の素数も探索するため、後から現れる非更新点を取りこぼさない。入力順に統合し、証人が狭義に増える点を採用すれば全更新点が得られる。

入力・最小入力・チャンク内の候補件数には128-bit整数を使い、Python側は任意精度整数を使う。CRTの片側座標が64-bitに収まる場合は従来の演算を使い、超える場合は128-bit座標へ切り替える。平方判定、剰余計算、座標からの差の計算も $2^{128}-1$ まで扱う。終了コードだけで完了と判断せず、全ビットの完了・全チャンクのレコードの存在と一意性・各最小入力の証人条件をPython側でも確認する。証人の再計算はEulerの規準による。

128-bit上限の指定と整数処理には対応しているが、計算時間・メモリ・ディスク使用量は探索範囲と証人の種類に依存する。特に負値探索では値 $0$ の候補も残るため、既存の分岐削減を使う専用探索より重くなる場合がある。この公開用プログラムによる64-bit・80-bit・128-bit全域の探索は実施していない。既存資料の完了済み探索とは別の実行記録として扱う。

エンジンのしきい値上限は997。これを超える次の更新点を探索する必要が生じた場合は、未完了のままエラーで停止する。証人値を997で打ち切って完了扱いにすることはない。チャンク幅と総チャンク数は64-bitの管理範囲に制限し、超える指定はエラーとする。完了ビットマップと作業配列を確保できるだけのメモリも必要になる。

## テスト

```sh
python -m unittest discover -s . -v
```

20万までの全件走査との一致、初期の値 $0$ の証人、平方数除外、チャンクの途中再開、不足ファイルの拒否、設定変更時の拒否を確認する。テストの作業記録は`_test`に残す。整数演算のテストは次で実行する。

```powershell
.\g++-static.cmd -O2 -std=c++20 -pthread test_arithmetic.cpp -o test_arithmetic.exe
.\test_arithmetic.exe
```

`test_arithmetic.cpp`は、十進整数の桁あふれ拒否、最大64-bit整数の二乗付近の平方判定、60,000件の剰余計算、128-bit座標のwheelと両証人の計算を検証するために同梱している。Pythonのテストでは $2^{64}$、 $2^{96}$、 $2^{127}$、最大64-bit整数の二乗、および $2^{128}-1$ 付近の小区間を独立な全件走査と比較し、上端付近での途中再開も確認する。Linuxでは`g++ -O2 -std=c++20 -pthread test_arithmetic.cpp -o test_arithmetic`でビルドして実行する。
