-- FFI (Foreign Function Interface) binding to a C function
-- This connects Lean code to external C code, allowing us to call C functions from Lean

-- @[extern "add"] tells Lean to link this to the C function named "add"
-- 'opaque' means we don't provide a Lean implementation - the actual code is in C
-- This declares a function that takes two UInt32 values and returns a UInt32
@[extern "add"]
opaque add_c (a b : UInt32) : UInt32
