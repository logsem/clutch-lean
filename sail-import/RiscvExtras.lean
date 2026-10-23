-- =======================================================================================
--   This Sail RISC-V architecture model, comprising all files and
--   directories except where otherwise noted is subject the BSD
--   two-clause license in the LICENSE file.
--
--   SPDX-License-Identifier: BSD-2-Clause
-- =======================================================================================

import Sail.Sail
import RiscvZkvm.Sail.Defs

open Sail
open ConcurrencyInterfaceV1

def print_bits {n : Nat} (_ : String) (_ : BitVec n) : Unit := ()
def print_string (_ : String) (_ : String) : Unit := ()
def prerr_string (_: String) : Unit := ()
def putchar {T} (_: T ) : Unit := ()
def string_of_int (z : Int) := s!"{z}"

section defs

variable [Arch]

-- Platform definitions
section Effectful

variable {Register : Type} {RegisterType : Register → Type} [DecidableEq Register] [Hashable Register]

def plat_term_write {α} (_ : α) : SailM Unit := .error .Unreachable
def plat_term_read (_ : Unit) : SailM String := .error .Unreachable

-- Reservations
def load_reservation (_ : Arch.pa) (_ : Nat) : SailM Unit := .error .Unreachable
def match_reservation (_ : Arch.pa) : Bool := false
def cancel_reservation (_ : Unit) : SailM Unit := pure ()
def valid_reservation (_ : Unit) : Bool := false

def get_16_random_bits (_ : Unit) : SailM (BitVec 16) := .error .Unreachable
def sys_enable_experimental_extensions (_ : Unit) : Bool := false

end Effectful

-- Floating-point instruction modules are outside this extraction.
-- Termination of currentlyEnabled
instance : SizeOf extension where
  sizeOf := extension.ctorIdx

macro_rules | `(tactic| decreasing_trivial) => `(tactic| decide)
