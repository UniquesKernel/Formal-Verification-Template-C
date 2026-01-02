-- ============================================================================
-- Lean's Proof System & Theorems
-- ============================================================================
-- Lean is a proof assistant that uses dependent type theory as its foundation.
-- In Lean, a theorem is a proposition (statement) paired with a proof that
-- demonstrates the proposition is always true.
--
-- Key concepts:
-- • A proposition (e.g., "a + b = b + a") is a type in Lean's type system
-- • A proof is a term of that type
-- • If we can construct such a term, the proposition is proven
-- • The `by` tactic mode lets us build proofs step-by-step
--
-- Having a theorem means we've formally verified the property holds for ALL
-- possible inputs, not just tested cases. This gives us mathematical certainty.
--
-- ============================================================================
-- Theorems about Addition
-- ============================================================================

-- Import the specification of the addition function we're verifying
import AnvilVerification.specs.Addition

-- Theorem: Addition is commutative (order doesn't matter)
-- This proves that a + b = b + a for any two 32-bit unsigned integers
theorem addition_commutation (a b : UInt32) : add a b = add b a := by
  unfold add                -- Expand the definition of our 'add' function
  rw [UInt32.add_comm]      -- Apply Lean's built-in commutativity proof for UInt32

-- Theorem: Zero is the additive identity
-- This proves that adding 0 to any number returns that number
theorem add_indentity (a : UInt32) : add a 0 = a := by
  unfold add                -- Expand the definition of our 'add' function
  simp                      -- Simplify using Lean's simplifier (handles 0 identity automatically)

-- Theorem: Every number has an additive inverse
-- This proves that a + (-a) = 0 (in modular arithmetic for UInt32)
theorem add_inverse (a : UInt32) : add a (-a) = 0 := by
  unfold add                -- Expand the definition of our 'add' function
  rw [UInt32.add_right_neg] -- Apply the right-inverse property for UInt32

-- Theorem: Addition is associative (grouping doesn't matter)
-- This proves that (a + b) + c = a + (b + c) for any three numbers
theorem add_associativity (a b c : UInt32) : add (add a b) c = add a (add b c) := by
  unfold add                -- Expand the definition of our 'add' function
  rw [UInt32.add_assoc]     -- Apply Lean's built-in associativity proof for UInt32
