-- Composed by check.sh after the fresh SentinelRealloc Gen.lean and Scenarios.lean.
def main : IO Unit := SentinelReallocScenarios.run {
  make := fun n => SentinelRealloc.make {} n
  append := fun s c => SentinelRealloc.append {} s c
  resize := fun s n => SentinelRealloc.resize {} s n
  release := fun s => SentinelRealloc.release {} s }
