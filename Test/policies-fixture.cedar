// Test/Policy.lean の検査用。nyxis_policies がビルド時に埋め込む値(数・負の数・like のパターン・拡張関数・
// has の連鎖・集合・レコード・if・unless・forbid)が、手書きの抽象構文と一致することを確かめる。
// サンプルアプリのポリシーではない。
@id("fixture-1")
forbid (principal is User, action in [Action::"a"], resource)
unless { context.n >= -1 && principal.name like "a*\*" }
when { if context.tags.contains("x") then context has a.b else ip("10.0.0.1").isIpv4() };

permit (principal == User::"u", action == Action::"b", resource in Post::"p")
when { {k: [1, -2]}.k.containsAll([3]) && context.d != decimal("1.5") };
