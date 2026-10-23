import MetrologyAsm.Keypair

/-! # Executable layout regression for the retained linked keypair input -/

-- This evaluates the assembler; it supplies no kernel theorem about assembly or execution.
/-- info: true -/
#guard_msgs in
#eval MetrologyAsm.keypairAssemblyCheck

#print axioms MetrologyAsm.keypair_stackBound
