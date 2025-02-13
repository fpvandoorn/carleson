import Mathlib.Tactic.Linter.Header

/-- error: unknown option 'linter.flexible' -/
#guard_msgs in
set_option linter.flexible true
