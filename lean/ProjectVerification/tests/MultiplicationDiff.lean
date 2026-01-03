-- ============================================================================
-- Differential Testing: C++ Implementation vs Lean Specification
-- ============================================================================
-- This module demonstrates property-based testing using the Plausible library
-- to verify that our C++ implementation (with extern "C") matches the Lean specification.

import ProjectVerification.specs.Multiplication  -- Import our specification
import ProjectVerification.ffi.CppMultiplication -- Import the C++ FFI binding
import Plausible                               -- Property-based testing library (like QuickCheck)

-- ============================================================================
-- Example 1: With Warning Suppression (Common Pattern)
-- ============================================================================
-- The `set_option warn.sorry false` pattern is commonly used to silence warnings
-- when using tactics like `plausible` that may not provide explicit proofs.
-- The section scope ensures the warning suppression only affects this block.

section
  set_option warn.sorry false

  -- Property: The C++ implementation must match the Lean specification
  -- for all UInt32 pairs. The plausible tactic generates 10,000 random
  -- test instances to verify this property.
  example (a b : UInt32) : multiply a b = multiply_c a b := by
    plausible (config := { numInst := 10000 })

end

-- ============================================================================
-- Example 2: Without Section (Direct Usage)
-- ============================================================================
-- You can also use plausible directly without a section, though this may
-- generate warnings. The same property verification applies.

example (a b : UInt32) : multiply a b = multiply_c a b := by
  plausible (config := { numInst := 10000 })
