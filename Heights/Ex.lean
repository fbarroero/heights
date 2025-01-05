namespace Hidden
inductive List (α : Type u) where
| nil  : List α
| cons : α → List α → List α

namespace List

def append (as bs : List α) : List α :=
  match as with
 | nil       => bs
 | cons a as => cons a (append as bs)

theorem nil_append (as : List α) : append nil as = as := rfl

theorem cons_append (a : α) (as bs : List α) : append (cons a as) bs = cons a (append as bs) :=
 rfl

theorem append_nil (as : List α) : append as nil = as :=
  match as with
  | nil       => rfl
  | cons a as => by rw [cons_append, append_nil]

theorem append_assoc (as bs cs : List α)
        : append (append as bs) cs = append as (append bs cs) :=
  match as with
  | nil       => rfl
  | cons a as => by
    rw [cons_append]
    rw [cons_append]
    rw [cons_append]
    rw [append_assoc]

def length : {α : Type u} → List α → Nat :=
  fun as ↦ match as with
  | nil       => 0
  | cons _ as => 1 + length as

theorem foo : length (append as bs) = length as + length bs :=
  match as with
  | nil       => by rw [nil_append, length, Nat.zero_add]
  | cons a as => by simp only [length, foo, Nat.add_assoc]


end List
end Hidden
