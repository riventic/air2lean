def main (args : List String) : IO UInt32 := do
  IO.println s!"usage: air2lean <air-dir> -o <out.lean> --namespace <Ns> (args: {args})"
  return 1
