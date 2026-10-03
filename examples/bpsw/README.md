# BPSWのC++・Python参考実装

通常版・強化版BPSWに加え、Selfridge Method A/A*、Jacobi/Kronecker記号、Lucas列を実装しています。

- [実行方法・入出力・Leanとの対応](../../doc/BPSWImplementations.md)
- [Lean PrimeTestの仕様と成果](../../doc/PrimeTest.md)
- [公開モジュールの構成](../../doc/README.md)

WindowsでC++版をビルドするには、同梱の `g++-static.cmd` または `clang++-static.cmd` を使います。
実行ファイルの出力先には、公開リポジトリの `.work` などの作業ディレクトリを指定し、ソースと分けて保存します。

## ScoopでMSYS2を導入する

管理者権限を使わずにPowerShellを起動します。Scoopが未導入の場合は、[公式のインストール手順](https://github.com/ScoopInstaller/Install#installation)に従い、次のコマンドを実行します。導入済みなら、この手順は省略します。

```powershell
Set-ExecutionPolicy -ExecutionPolicy RemoteSigned -Scope CurrentUser
Invoke-RestMethod -Uri https://get.scoop.sh | Invoke-Expression
```

続いてMSYS2をインストールし、初回セットアップのために起動します。`msys2`はScoopの[main bucket](https://github.com/ScoopInstaller/Main/blob/master/bucket/msys2.json)に含まれているため、追加のbucketを登録する必要はありません。

```powershell
scoop install msys2
msys2
```

MSYS2の初期化が完了し、シェルのプロンプトが表示されたら、`exit`を入力してPowerShellに戻ります。Scoopの標準配置では `%USERPROFILE%\scoop\apps\msys2\current` に導入されるため、以下のツールチェーン導入用cmdをそのまま使えます。

## Windows用ツールチェーンを導入する

導入用cmdとビルド用cmdは、どちらも `%USERPROFILE%\scoop\apps\msys2\current` のMSYS2を使います。別の場所に導入した場合は、導入用cmdの `BPSW_MSYS2_ROOT` とビルド用cmdのMSYS2パスを、その場所に合わせて変更します。

プロジェクトのルートでPowerShellを開き、使用するコンパイラに対応するコマンドを実行します。

```powershell
# g++: MINGW64 toolchain と Boost
.\examples\bpsw\install-g++-toolchain.cmd

# clang++: CLANG64 toolchain と Boost
.\examples\bpsw\install-clang++-toolchain.cmd
```

各コマンドは `pacman -Syu --needed --noconfirm` でMSYS2全体を更新し、対応するツールチェーンとBoostをインストールします。`--noconfirm`を指定しているため、確認には既定の回答を使い、パッケージグループ内の全パッケージを選択します。手動で回答する必要はありません。

MSYS2の基幹部分の更新で処理が終了した場合は、同じコマンドを再実行して更新とインストールを完了します。

パッケージ名はMSYS2の[MINGW64 toolchain](https://packages.msys2.org/groups/mingw-w64-x86_64-toolchain)・[CLANG64 toolchain](https://packages.msys2.org/groups/mingw-w64-clang-x86_64-toolchain)に対応しています。更新手順の詳細は[Updating MSYS2](https://www.msys2.org/docs/updating/)を参照します。

## C++版をビルドする

ツールチェーンの導入後、`lakefile.toml`のある `PseudoPrime` ディレクトリでPowerShellを開きます。次のコマンドで出力先の `.work` を作成し、C++17・最適化・警告オプションを指定してstaticビルドします。使用するコンパイラに応じて、いずれかを実行します。

### g++（MINGW64）

```powershell
New-Item -ItemType Directory -Force .work | Out-Null
.\examples\bpsw\g++-static.cmd -std=c++17 -O2 -Wall -Wextra -pedantic examples/bpsw/baillie_psw_strengthened.cpp -o .work/bpsw-gcc-static.exe
```

### clang++（CLANG64）

```powershell
New-Item -ItemType Directory -Force .work | Out-Null
.\examples\bpsw\clang++-static.cmd -std=c++17 -O2 -Wall -Wextra -pedantic examples/bpsw/baillie_psw_strengthened.cpp -o .work/bpsw-clang-static.exe
```

ビルド後の実行方法と入出力は[BPSW参考実装の解説](../../doc/BPSWImplementations.md)を参照します。
