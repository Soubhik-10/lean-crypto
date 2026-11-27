module
public import RustCrypto.Common.OrderedVector
@[expose] public section
namespace RustCrypto.OrderedPrefix
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def collect (rows : Vector α n) (encode : α → List β) (count : Nat) : List β :=
  (rows.toList.take count).flatMap encode

theorem prefix_zero (rows : Vector α n) (encode : α → List β) : collect rows encode 0 = [] := by
  simp [collect]

theorem prefix_succ (rows : Vector α n) (encode : α → List β) (count : Nat) (hcount : count < n) :
    collect rows encode (count+1) = collect rows encode count ++ encode (rows[count]'hcount) := by
  unfold collect
  rw [List.take_succ_eq_append_getElem (by simpa using hcount)]
  simp only [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,Vector.getElem_toList]

theorem prefix_length (rows : Vector α n) (encode : α → List β) (size : Nat)
    (hsize : ∀ row, (encode row).length = size) (count : Nat) (hcount : count ≤ n) :
    (collect rows encode count).length = count*size := by
  induction count with
  | zero => simp [collect]
  | succ count ih =>
    rw [prefix_succ rows encode count (by omega),List.length_append,hsize,ih (by omega)]
    simp only [Nat.add_mul,Nat.one_mul]

theorem replace_next (original head row : List α) (offset : Nat) (hhead : head.length = offset) :
    (head ++ original.drop offset).take offset ++ row ++
      (head ++ original.drop offset).drop (offset+row.length) =
      (head ++ row) ++ original.drop (offset+row.length) := by
  have ht : head.take offset = head := List.take_of_length_le (by omega)
  have hd : head.drop (offset+row.length) = [] := List.drop_eq_nil_iff.mpr (by omega)
  simp only [List.take_append,List.drop_append,hhead,ht,hd,Nat.sub_self,List.take_zero,List.append_nil,
    List.nil_append,Nat.add_sub_cancel_left,List.drop_drop,List.append_assoc]

theorem prefix_full (rows : Vector α n) (encode : α → List β) :
    collect rows encode n = rows.toList.flatMap encode := by
  unfold collect
  rw [List.take_of_length_le (by simp)]

end RustCrypto.OrderedPrefix
