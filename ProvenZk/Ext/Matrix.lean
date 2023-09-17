import Mathlib.Data.Matrix.Basic

namespace Matrix
  def to_vector {t α} (m : Matrix (Fin t) Unit α ) : Vector α t := Vector.ofFn (fun i => m i 0)
end Matrix