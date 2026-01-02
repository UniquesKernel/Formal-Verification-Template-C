import AnvilVerification.ffi.CAddition
import AnvilVerification.specs.Addition

def main : IO Unit := do
  IO.println "We successfully called both the native lean and the foreign c version of add!"
  IO.println s!"a = 1 and b = 2 is: add_c = {add_c 1 2}"
  IO.println s!"a = 1 and b = 2 is: add = {add 1 2}"
