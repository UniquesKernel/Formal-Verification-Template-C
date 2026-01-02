import AnvilVerification.ffi.CAddition
import AnvilVerification.ffi.CppMultiplication
import AnvilVerification.specs.Addition
import AnvilVerification.specs.Multiplication

def main : IO Unit := do
  IO.println "We successfully called both the native lean and the foreign c version of add!"
  IO.println s!"a = 1 and b = 2 is: add_c = {add_c 1 2}"
  IO.println s!"a = 1 and b = 2 is: add = {add 1 2}"
  IO.println ""
  IO.println "We successfully called both the native lean and the foreign C++ (extern C) version of multiply!"
  IO.println s!"a = 3 and b = 4 is: multiply_c = {multiply_c 3 4}"
  IO.println s!"a = 3 and b = 4 is: multiply = {multiply 3 4}"
