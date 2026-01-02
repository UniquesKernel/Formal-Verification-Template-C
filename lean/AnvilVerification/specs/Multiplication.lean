-- Specification: Define the expected behavior of multiplication
-- This is the "reference implementation" that describes what multiplication should do
-- We'll verify that our C++ implementation (via FFI) matches this specification

-- Simple wrapper around Lean's built-in UInt32 multiplication operator
-- This serves as our formal specification for what "multiply" means
def multiply (a b : UInt32) : UInt32 := a * b
