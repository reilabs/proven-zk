import Init.Data.Range
import Mathlib

namespace Std
namespace Range

theorem forIn_stopSucc {start d : Nat} {init : α} {f : Nat -> α -> α } :
  Id.run (Range.forIn [start:(start + d.succ)] init (fun i a => ForInStep.yield (f i a))) =
  f (start + d) (Id.run (Range.forIn [start:(start + d)] init (fun i a => ForInStep.yield (f i a)))) := by
  sorry

end Range
end Std