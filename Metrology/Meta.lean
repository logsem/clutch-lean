module

public import Metrology.Meta.Projections
public import Metrology.Meta.Inspect
public import Metrology.Meta.CheckDef

/-!
Metaprogramming utilities: Expr builders (`Build`), `@[constructors]`/`@[uncurriedProjections]`,
`#inspect`, `#checkdef`. `@[discrete]` (`Meta/Discrete`) is meta-imported separately by the
libraries that use it.
-/

@[expose] public section
