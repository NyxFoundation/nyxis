# JWT ライブラリの採用前検査

リポジトリ直下で `sh scripts/check-jwt-dependency.sh` を実行する。
Lean/Lake、Python 3.12 以降、HTTPS 接続、OpenSSL CLI、pkg-config の libcrypto、C コンパイラが必要。

`python3 scripts/prepare-dependencies.py` が `.lake/vendor/` に置いた承認済みの lean-jose・jose-libcrypto・
lean-libcrypto(と推移依存 lean-json・leancrypto。リビジョンとアーカイブの SHA256 は `scripts/dependencies.json`
で固定)を、一時領域の使い捨ての Lake プロジェクトから path 依存として使う。現在の `lean-toolchain` でビルドし、
`Backend.libcrypto` を明示して ES256 の署名・JWT 検証を実行する。正常系1件と拒否10件、
本体の `Nyxis.Internal.SupabaseJwt` 検証器の24件と、JWKS更新の13件を検査する。

本体の Lake 設定・manifest・依存キャッシュは変更しない。git は起動しない(起動すれば失敗する)。
終了時に生成したテスト鍵とビルド成果物を削除する。テスト鍵は OpenSSL が毎回生成し、実アプリや Supabase の秘密は使わない。

同じ内部検証器をHTTPへ接続し、固定時計・実時計・実libpq接続失敗も検査する。
`--local-auth` は準備済み `python3 scripts/local-supabase.py --exec` から実行し、ローカルAuthが
マジックリンクで発行したJWT・公開JWKS・実時計・隔離された実DBで4主体を検査する。
JWKS取得はテストのPythonが行う。本体経路(`sample` の HTTPS 取得・検証)の検査は
`scripts/check-sample-jwt-db.py` が担い、この検査は依存とコアの検証器の採用前検査である。内部検証器は設定のissuerとJWKSから鍵を準備し、
ES256・issuer・audience・期限を確認した後で必須・非空・NUL無しの `sub` を返す。
JWT ライブラリの `sub` は Option であり、署名・claim 検証の成功だけで主体を確定してはいけない。

検証ごとに `verifyFresh` が注入された取得処理を呼び、JWKSを準備し直す。取得失敗時に古い鍵を
使わず匿名へ閉じ、時計は取得後に読む。HTTP検査はテスト公開鍵ファイルを毎回読み、同じサーバで
鍵削除・不正文書・kid変更・ファイル不在による匿名化/下書き拒否と復旧の19件を追加する。
これは実ネットワークの鍵ローテーション検査ではない。HTTPS取得処理にはTLS・状態・サイズ・期限の検査が必要。

`--local-postgres` と `--local-auth` は、隔離した検査DBだけに一時トリガーを置き、
作成・編集・削除・管理者付与の各操作で、文の実行中と遅延制約のCOMMIT時に失敗させる。
8件ともHTTPは本文 `backend unavailable` の503で、全アプリケーション行は不変であること、
トリガー除去後の同じリクエストは同じサーバで成功し永続化されることを検査する。
ロールバックで戻らない検査用シーケンスにより、拒否や認証失敗ではなく実際にトリガーへ
到達したことも確認する。通信断などCOMMIT結果が不明な場合の検査や、複数操作ハンドラの
途中失敗の実DB検査は含まない。トリガー・関数・シーケンスは除去し、検査DBも削除する。
