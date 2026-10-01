# BPSWのC++・Python参考実装

通常版・強化版BPSW、Selfridge Method A/A*、Jacobi/Kronecker記号、Lucas列の実装。

- [実行方法・入出力・Leanとの対応](../../doc/BPSWImplementations.md)
- [Lean PrimeTestの仕様と成果](../../doc/PrimeTest.md)
- [公開モジュールの構成](../../doc/README.md)

WindowsのC++コンパイルには、同梱の `g++-static.cmd` または `clang++-static.cmd` を使う。
出力先は公開リポジトリの `.work` など、ソースと区別した作業ディレクトリにする。

## Scoop 経由での MSYS2 の導入

管理者として起動していない PowerShell を使用する。Scoop が未導入の場合は、[公式のインストール手順](https://github.com/ScoopInstaller/Install#installation) に従って次を実行する。Scoop が導入済みなら、この手順は省略する。

```powershell
Set-ExecutionPolicy -ExecutionPolicy RemoteSigned -Scope CurrentUser
Invoke-RestMethod -Uri https://get.scoop.sh | Invoke-Expression
```

続いて MSYS2 をインストールし、初回セットアップのために起動する。`msys2` は Scoop の [main bucket](https://github.com/ScoopInstaller/Main/blob/master/bucket/msys2.json) に含まれるため、追加 bucket の登録は不要である。

```powershell
scoop install msys2
msys2
```

MSYS2 の初期化が完了してシェルのプロンプトが表示されたら、`exit` を入力して PowerShell に戻る。Scoop の標準配置では `%USERPROFILE%\scoop\apps\msys2\current` に導入され、以下の toolchain インストール用 cmd をそのまま使用できる。

## Windows 用 toolchain のインストール

既存のビルド用 cmd と同じく、Scoop 配下の `%USERPROFILE%\scoop\apps\msys2\current` にインストール済みの MSYS2 を使用する。異なる配置では、インストール用 cmd の `BPSW_MSYS2_ROOT` とビルド用 cmd の MSYS2 パスを合わせる。

プロジェクトのルートから PowerShell で、必要なコンパイラに対応するコマンドを実行する。

```powershell
# g++: MINGW64 toolchain と Boost
.\examples\bpsw\install-g++-toolchain.cmd

# clang++: CLANG64 toolchain と Boost
.\examples\bpsw\install-clang++-toolchain.cmd
```

各コマンドは `pacman -Syu --needed --noconfirm` により MSYS2 全体を更新し、対応する toolchain と Boost をインストールする。`--noconfirm` により確認には既定の回答を使用し、パッケージグループは全選択となるため、手動の確認応答は不要である。MSYS2 の基幹更新により終了した場合は、同じコマンドを再実行して更新とインストールを完了する。

パッケージ名は MSYS2 の [MINGW64 toolchain](https://packages.msys2.org/groups/mingw-w64-x86_64-toolchain)・[CLANG64 toolchain](https://packages.msys2.org/groups/mingw-w64-clang-x86_64-toolchain) に対応する。更新手順は [Updating MSYS2](https://www.msys2.org/docs/updating/) を参照。

## C++ のビルドコマンド例

toolchain の導入後、`lakefile.toml` のある `PseudoPrime` ディレクトリを作業ディレクトリとして、PowerShell で実行する。出力先の `.work` を作成し、C++17・最適化・警告オプションを指定して static ビルドする。使用するコンパイラに応じて、次のいずれかを実行する。

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

ビルド後の実行方法と入出力は [BPSW 参考実装の解説](../../doc/BPSWImplementations.md) を参照。
