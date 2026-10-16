module

public import Metrology
public import Mathlib.Basic.Real.Basic

@[expose] public section

/-! # Some tests -/

-- inductive Lit (B Z R  : Type _) where
--
-- @[projections]
-- inductive Expr' (B Z R : Type _) where
-- -- Literals
-- -- | elit (l : Lit B Z R)
-- -- Functions
-- | evar (s : Ident)
-- | erec (f x : Ident) (e : Expr' B Z R)
-- | eapp (e1 e2 : Expr' B Z R)
-- -- -- Operations
-- | ebinop (op : BinOp) (e1 e2 : Expr' B Z R)
-- | econd (e et ef : Expr' B Z R)
-- -- -- Products
-- | epair (e1 e2 : Expr' B Z R)
-- | efst (e : Expr' B Z R)
-- | esnd (e : Expr' B Z R)
-- -- -- Sums
-- | eleft (e : Expr' B Z R)
-- | eright (e : Expr' B Z R)
-- | ecase (e el er : Expr' B Z R)
--
-- /-- info: Expr'.epair.π.{u_1, u_2, u_3} {B : Type u_1} {Z : Type u_2} {R : Type u_3} :
--   Expr' B Z R → Option (Expr' B Z R × Expr' B Z R) -/
-- #guard_msgs in #check Expr'.epair.π
--
-- def test1 : Expr' Bool ℤ ℝ := .elit <| .real (5 : ℝ)
-- def test2 : Expr' Bool ℤ ℝ := .eleft <| .evar "x"
-- example : Expr'.epair.π (.epair test1 test2) = some (test1, test2) := rfl
-- example : Expr'.esnd.π (.epair test1 test2) = none := rfl

@[uncurriedProjections, constructors]
inductive MyDepC' (n : Nat)
| DepC' (depV : Fin n)

/-- info: MyDepC'.DepC'.π {n : ℕ} (x : MyDepC' n) : Option (Fin n) -/
#guard_msgs in #check MyDepC'.DepC'.π

@[uncurriedProjections, constructors]
inductive MyTree where
| nil
| leaf (x : Nat)
| branch (tl tr : MyTree) (v : Nat)

example : (3, 4, 5) = (3, (4, 5)) := rfl

-- Nullary constructors get no `.π`: there is nothing to project, so `mkProjection`
-- skips them (`Metrology/Meta/Projections.lean`). Unary/n-ary ones do:
example : MyTree.leaf.π (.leaf 5) = some 5 := rfl
example : MyTree.leaf.π .nil = none := rfl
example : MyTree.branch.π (.leaf 5) = none := rfl
example : MyTree.branch.π (.branch (.leaf 1) (.leaf 2) 5) = some (MyTree.leaf 1, MyTree.leaf 2, 5) := rfl

@[uncurriedProjections, constructors]
inductive MyEmpty

@[uncurriedProjections, constructors]
inductive MyType (x y : Nat)
| MyV (n : Unit) (w : Fin x)

@[uncurriedProjections, constructors]
inductive MyThing (x : Nat) (y : Fin x)
| MyNothing
| MyV (blah : String) (bleh : Bool)

example : (@MyThing.MyV.π 5 2 <| .MyV "hi" false) = some ("hi", false) := rfl
example : (@MyThing.MyV.π 5 2 <| MyThing.MyNothing) = none := rfl

@[uncurriedProjections, constructors]
inductive MyParamT (n : Sort 0) (α β : Type)
| Val1 (x : α)
| Val2 (y : β)
| Rec (x1 : MyParamT n α β) (v2 : α)

/-- info: MyParamT.Val2.π {n : Prop} {α β : Type} (x : MyParamT n α β) : Option β -/
#guard_msgs in #check MyParamT.Val2.π

@[uncurriedProjections, constructors]
inductive MyTree' (L1 L2 : Type _) where
| nil
| leaf1 (x : L1)
| leaf2 (x : L1) (y : L2)
| branch (tl tr : MyTree' L1 L2) (v : Nat)

-- Automatically define these uncurried constructors (should be easy)
-- If we want to use Function.uncurry, we should reassociate the product back to the foldl direction.
def MyTree'.nil.ctor : Unit → MyTree' L1 L2 := Function.const _ .nil
def MyTree'.leaf1.ctor  : L1 → MyTree' L1 L2 := .leaf1
def MyTree'.leaf2.ctor  : L1 × L2 → MyTree' L1 L2 := Function.uncurry .leaf2
def MyTree'.branch.ctor  : MyTree' L1 L2 × MyTree' L1 L2 × Nat  → MyTree' L1 L2 :=
  -- This is why we need to reassociate
  -- Function.uncurry (Function.uncurry MyTree'.branch)
  fun (x, y, z) => .branch x y z

-- The ctor and π functions should be inverses
-- #check fun {L1 L2 }(x : MyTree' L1 L2) => (MyTree'.branch.π x) |>.map MyTree'.branch.ctor

-- #check MyTree'.leaf1
-- #check Function.uncurry (Function.uncurry MyTree'.branch)

-- def MyTree'.flatten {L1 L2} (ts : MyTree' (Set L1) (Set L2)) : Set (MyTree' L1 L2) :=
--     let π_nil : Set (MyTree' L1 L2) :=
--       MyTree'.nil.π ts |>.map (fun _ => {nil}) |>.getD ∅
--     let π_leaf1 : Set (MyTree' L1 L2):=
--       MyTree'.leaf1.π ts |>.map (fun f1 => sorry) |>.getD ∅
--
--
--     -- let π_leaf1 := MyTree'.leaf1.π go
--     -- let π_leaf2 := MyTree'.leaf2.π go
--     -- let π_branch := MyTree'.branch.π go
--
--     -- If it's none, then return Set.empty
--     -- If it's some, then
--     --     - Apply flatten to all recursive cases
--     --     - Take the singleton set for all non-recursive, non-parameter cases
--     --     - Take the set itself for all parameter cases
--     --     - Define the preimage of (Some (prod. of sets.)) under the projection function
--     -- The preimage is the union of these sets
--     -- Could also do a dummy match on the go arguent
--
--     sorry
--     -- Set.union { nil } <|
--     -- Set.union { leaf1 l | l ∈ Set.univ } <|
--     -- Set.union { leaf1 l | l ∈ Set.univ } <|
--     --           { leaf1 l | l ∈ Set.univ }

def main : IO Unit := return

end
