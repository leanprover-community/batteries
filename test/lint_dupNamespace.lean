import Std.Data.Nat.Basic
import Std.Tactic.Lint

-- internal names should be ignored
theorem Foo.Foo._bar : True := trivial

def Foo := Nat
  deriving Add

namespace Foo

instance : Mul Foo where
  mul := Nat.mul

end Foo

#lint- only dupNamespace
