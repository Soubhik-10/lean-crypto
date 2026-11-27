module
public import RustCrypto.Common.OrderedVector
@[expose] public section
namespace RustCrypto.OrderedVector
set_option maxHeartbeats 2000000

theorem flatten_list {α : Type} {n m : Nat} (values : Vector (Vector α n) m) :
    values.flatten.toArray.toList = values.toList.flatMap Vector.toList := by
  simp [Vector.flatten, Vector.toList, List.flatMap_def, Function.comp_def]
  rfl

end RustCrypto.OrderedVector
