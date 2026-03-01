import Init.Data.List.Basic

abbrev Var := String

def nub (l : List Var) : List Var :=
  match l with
  | [] => []
  | x :: xs =>
    have : (xs.filter (fun y => y != x)).length < (x :: xs).length := by
      calc (xs.filter (fun y => y != x)).length
        _ ≤ xs.length := List.length_filter_le ..
        _ < (x :: xs).length := Nat.lt_succ_self ..
    x :: nub (xs.filter (fun y => y != x))
termination_by l.length
