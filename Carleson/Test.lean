import Mathlib.Tactic.Linter.Header
import Mathlib.Tactic.Linter.Multigoal
import Mathlib.Tactic.Linter.OldObtain
import Mathlib.Tactic.Linter.RefineLinter
import Mathlib.Tactic.Linter.Style

/-- error: unknown option 'linter.flexible' -/
#guard_msgs in
set_option linter.flexible true
