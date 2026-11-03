/- sql_run < script.sql : the SQL semantics (`Sql.runScript`), printing what the
   driver c/driver.c would print. -/
import Sql

def main : IO Unit := do
  let input ← (← IO.getStdin).readBinToEnd
  let out := Sql.runScript input
  let stdout ← IO.getStdout
  stdout.write out
  stdout.flush
