-- Specification: Define the expected behavior of addition
-- This is the "reference implementation" that describes what addition should do
-- We'll verify that our C implementation (via FFI) matches this specification

-- Simple wrapper around Lean's built-in UInt32 addition operator
-- This serves as our formal specification for what "add" means
def add (a b : UInt32) : UInt32 := a + b
