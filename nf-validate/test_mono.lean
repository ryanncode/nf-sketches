import NfValidate

theorem test_trans (a b c : Int) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  exact Int.le_trans h1 h2
