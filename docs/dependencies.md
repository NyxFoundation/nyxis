# 固定依存の準備

JWT検証には承認済みの lean-jose / jose-libcrypto / lean-libcrypto を使う。
推移依存は lean-json / leancrypto。本体Lakeの依存に含め、OpenSSLバックエンドを使う。
lean-pqも既存と同一リビジョンをこの準備経路で取得する。
Cedarとbatteriesの既存Lake依存は維持する。

```sh
python3 scripts/prepare-dependencies.py
lake build
sh scripts/check-installed-jwt.sh
```

Python 3.12以降、OpenSSL CLI、pkg-config、libcrypto・libpq開発用ファイル、Cコンパイラが必要。
`scripts/dependencies.json`が各依存の上流リビジョンと取得アーカイブのSHA256を固定する。
準備スクリプトはGitコマンドを実行せず、HTTPSで取得・照合したソースを
Git管理外の `.lake/vendor/` に置く。ライセンスと上流のLean/Cソースは維持する。
初回取得後の実行はソース照合のみで、ビルド成果物を保持する。
`.lake/vendor/` を改名・移動した場合は、macOS では実行ファイルに lean-libcrypto の dylib の絶対パスが
埋め込まれるため、`.lake/build/bin` と `.lake/vendor/lean-libcrypto/.lake/build` を消して再ビルドする。
既存ソースや固定情報が一致しなければ上書きせず失敗する。

上流のLake設定では依存を固定キャッシュの相対パスへ変え、toolchainを本体と揃える。
lean-jsonではLean v4.34.1で非推奨になった定理名に対する `linter.deprecated` だけを抑制し、
他の `warningAsError` は維持する。暗号・JOSE解析・証明のコードは変更しない。
上流設定は[lean-jsonの固定リビジョン](https://github.com/paulbutcher/lean-json/blob/c7323a3eb8323fb16ee451de495ff91192453aa5/lakefile.lean)
と[jose-libcryptoの固定リビジョン](https://github.com/paulbutcher/jose-libcrypto/blob/d722d4a55c9dfebffe69dde58d8087ae3c004e09/lakefile.lean)で参照できる。

`checkJwtDependency` は検査専用の実行ファイルで、一時鍵をOpenSSLで生成し、
有効JWT・署名不正・改変sub・期限境界・期限切れ・発行者違い・audience違い・
alg none 2件・未知kid・exp欠落の11件を検査する。
鍵と生成JWTは一時ディレクトリだけに置き、終了時に削除する。
`sh scripts/check-handler-effects.sh` はアプリからの `JoseLibcrypto` 直接importも拒否する。

これは依存の導入検査であり、本体の経路(JWKS の HTTPS 取得・JWT 検証・実 DB)の検査ではない。
本体経路の検査は[ローカル Supabase の検査方法](local-supabase.md)を参照する。
