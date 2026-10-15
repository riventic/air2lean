-- Composed by check.sh after `import ZigLean.Mem.Alloc` and Scenarios.lean.
def main : IO Unit := SentinelReallocScenarios.run SentinelReallocScenarios.model
