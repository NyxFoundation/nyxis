// For the checks in Test/Policy.lean. Confirms that the values nyxis_policies embeds at build time (numbers, negative
// numbers, like patterns, extension functions, has chains, sets, records, if, unless, forbid) match the hand-written
// abstract syntax. Not a policy of any example application.
@id("fixture-1")
forbid (principal is User, action in [Action::"a"], resource)
unless { context.n >= -1 && principal.name like "a*\*" }
when { if context.tags.contains("x") then context has a.b else ip("10.0.0.1").isIpv4() };

permit (principal == User::"u", action == Action::"b", resource in Post::"p")
when { {k: [1, -2]}.k.containsAll([3]) && context.d != decimal("1.5") };
