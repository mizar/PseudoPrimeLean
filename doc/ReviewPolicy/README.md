# Lean形式化のレビュー規準

このディレクトリはPseudoPrimeの変更を検討するための規準と手順を管理する。ユーザーの明示的な指示とAGENTS.mdを優先し、未承認の例外で既存の制約を変更しない。宣言の所有者移設は[対象ごとに審査する](architecture/generality-ownership.md)。

各レビューでは[_common.md](_common.md) と担当する規準を読み、変更差分、関係するソース、検証結果を照合する。複数の観点が必要なら同じ変更を各規準で評価する。観点ごとにエージェントを使う場合も、ユーザーや実行環境の委任に関する指示に従う。

| 観点 | 規準 |
|---|---|
| 正しさと前提 | [正しさ](integrity/correctness.md)、[仮定と公理](integrity/assumptions.md) |
| 既存成果と出典 | [再利用](integrity/reuse.md)、[範囲と出典](integrity/scope-attribution.md) |
| 所有者と配置 | [一般化と所有者](architecture/generality-ownership.md)、[ソース配置と依存](architecture/placement-imports.md)、[有限認証](architecture/finite-certificates.md) |
| APIと文書 | [APIと互換性](architecture/api-compatibility.md)、[命名と文書](architecture/naming-documentation.md) |
| 品質と成果 | [証明の品質](quality/proof-quality.md)、[ビルド費用](quality/build-cost.md)、[定量上界](quality/quantitative-bounds.md)、[上界の存続](quality/bound-lifecycle.md) |

[例外管理](exceptions/README.md) は適用範囲と根拠を記録する。[依存図](generated/namespace-dependencies.md) はソースから生成する集計であり、意味上の配置監査を代替しない。

## 名前空間とソース配置

名前空間、宣言の所有者、モジュール配置、import依存、API移設の規準は、このディレクトリで管理する。配置の判断は [一般化と所有者](architecture/generality-ownership.md) と [ソース配置と依存](architecture/placement-imports.md) に従う。移設時のAPIは [APIと互換性](architecture/api-compatibility.md)、依存の確認は [移設手順](exceptions/namespace-migrations.md) を参照する。

## 規準自体の変更

レビュー対象に適用する規準は原則として変更前の確定済みポリシーとする。ポリシー自体の変更は別の変更単位で審査し、未承認の例外で既存の違反を正当化しない。今回の規準移行のように既存規則を整理する場合は、変更点と従来の規則を照合する。

数学的な健全性と公理・依存関係の不変条件を最優先とし、明示的な例外管理、API・一般化・配置方針、証明の実装上の好みの順に扱う。所有者移設は対象ごとに根拠と依存を審査する。上位のユーザー指示と衝突する場合はその指示に従う。
