import Nyxis.Build
import Nyxis.Internal.PostgresShape

/-! Internal build-time metadata. Imported only after the application's final audit. -/
namespace Nyxis.Internal.PostgresShapeBuild
open Lean Elab Command

deriving instance ToExpr for PostgresShape.ScalarType
deriving instance ToExpr for PostgresShape.CellType
deriving instance ToExpr for PostgresShape.Attribute

syntax "nyxis_postgres_shape " ident " from " str : command
elab_rules : command
  | `(nyxis_postgres_shape $id:ident from $path:str) => do
    let (file, contents) ← Nyxis.Build.readRelative path "PostgreSQL shape"
    match PostgresShape.compile contents with
    | .error e => throwErrorAt path "nyxis: {file}: {e}"
    | .ok shape =>
      Nyxis.Build.defineValue id (ToExpr.toTypeExpr (α := PostgresShape.Shape))
        (toExpr shape) s!"PostgreSQL shape compiled from {path.getString}."

end Nyxis.Internal.PostgresShapeBuild
